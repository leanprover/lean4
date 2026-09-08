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
lean_object* lean_uint8_to_nat(uint8_t);
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
extern lean_object* l_ByteArray_empty;
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_tryOpt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_tryOpt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_peekIs(lean_object*, lean_object*);
static const lean_string_object l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2___closed__0 = (const lean_object*)&l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(lean_object*);
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8;
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
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13;
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
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1;
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___boxed(lean_object*);
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid IPv6 address: "};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0_value;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "expected: '"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2_value;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6_value;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8;
static const lean_closure_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9_value;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__15;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected at least one char"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__16 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__16_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__16_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__17 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__17_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid IPv4 address: "};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_value;
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
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15;
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
LEAN_EXPORT uint8_t l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__1(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__1___boxed(lean_object*);
static const lean_closure_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "too many path segments (limit: "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "path too long (limit: "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " bytes)"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "invalid percent encoding in path segment"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__6 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__6_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__6_value)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__7 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__7_value;
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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___boxed(lean_object*);
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
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4;
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
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0(void){
_start:
{
uint32_t v___x_78_; uint8_t v___x_79_; 
v___x_78_ = 43;
v___x_79_ = lean_uint32_to_uint8(v___x_78_);
return v___x_79_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1(void){
_start:
{
uint32_t v___x_80_; uint8_t v___x_81_; 
v___x_80_ = 45;
v___x_81_ = lean_uint32_to_uint8(v___x_80_);
return v___x_81_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2(void){
_start:
{
uint32_t v___x_82_; uint8_t v___x_83_; 
v___x_82_ = 46;
v___x_83_ = lean_uint32_to_uint8(v___x_82_);
return v___x_83_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3(void){
_start:
{
uint32_t v___x_84_; uint8_t v___x_85_; 
v___x_84_ = 65;
v___x_85_ = lean_uint32_to_uint8(v___x_84_);
return v___x_85_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4(void){
_start:
{
uint32_t v___x_86_; uint8_t v___x_87_; 
v___x_86_ = 90;
v___x_87_ = lean_uint32_to_uint8(v___x_86_);
return v___x_87_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5(void){
_start:
{
uint32_t v___x_88_; uint8_t v___x_89_; 
v___x_88_ = 97;
v___x_89_ = lean_uint32_to_uint8(v___x_88_);
return v___x_89_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6(void){
_start:
{
uint32_t v___x_90_; uint8_t v___x_91_; 
v___x_90_ = 122;
v___x_91_ = lean_uint32_to_uint8(v___x_90_);
return v___x_91_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7(void){
_start:
{
uint32_t v___x_92_; uint8_t v___x_93_; 
v___x_92_ = 48;
v___x_93_ = lean_uint32_to_uint8(v___x_92_);
return v___x_93_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8(void){
_start:
{
uint32_t v___x_94_; uint8_t v___x_95_; 
v___x_94_ = 57;
v___x_95_ = lean_uint32_to_uint8(v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0(uint8_t v_c_96_){
_start:
{
uint8_t v___y_98_; uint8_t v___y_99_; uint8_t v___y_100_; uint8_t v___y_102_; uint8_t v___x_119_; uint8_t v___x_120_; 
v___x_119_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_120_ = lean_uint8_dec_le(v___x_119_, v_c_96_);
if (v___x_120_ == 0)
{
goto v___jp_114_;
}
else
{
uint8_t v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_122_ = lean_uint8_dec_le(v_c_96_, v___x_121_);
if (v___x_122_ == 0)
{
goto v___jp_114_;
}
else
{
v___y_102_ = v___x_122_;
goto v___jp_101_;
}
}
v___jp_97_:
{
if (v___y_98_ == 0)
{
if (v___y_99_ == 0)
{
return v___y_100_;
}
else
{
return v___y_99_;
}
}
else
{
if (v___y_99_ == 0)
{
return v___y_98_;
}
else
{
return v___y_99_;
}
}
}
v___jp_101_:
{
uint8_t v___x_103_; uint8_t v___x_104_; uint8_t v___x_105_; uint8_t v___x_106_; 
v___x_103_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_104_ = lean_uint8_dec_eq(v_c_96_, v___x_103_);
v___x_105_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_106_ = lean_uint8_dec_eq(v_c_96_, v___x_105_);
if (v___x_106_ == 0)
{
uint8_t v___x_107_; uint8_t v___x_108_; 
v___x_107_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_108_ = lean_uint8_dec_eq(v_c_96_, v___x_107_);
v___y_98_ = v___x_104_;
v___y_99_ = v___y_102_;
v___y_100_ = v___x_108_;
goto v___jp_97_;
}
else
{
v___y_98_ = v___x_104_;
v___y_99_ = v___y_102_;
v___y_100_ = v___x_106_;
goto v___jp_97_;
}
}
v___jp_109_:
{
uint8_t v___x_110_; uint8_t v___x_111_; 
v___x_110_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_111_ = lean_uint8_dec_le(v___x_110_, v_c_96_);
if (v___x_111_ == 0)
{
v___y_102_ = v___x_111_;
goto v___jp_101_;
}
else
{
uint8_t v___x_112_; uint8_t v___x_113_; 
v___x_112_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_113_ = lean_uint8_dec_le(v_c_96_, v___x_112_);
v___y_102_ = v___x_113_;
goto v___jp_101_;
}
}
v___jp_114_:
{
uint8_t v___x_115_; uint8_t v___x_116_; 
v___x_115_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_116_ = lean_uint8_dec_le(v___x_115_, v_c_96_);
if (v___x_116_ == 0)
{
goto v___jp_109_;
}
else
{
uint8_t v___x_117_; uint8_t v___x_118_; 
v___x_117_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_118_ = lean_uint8_dec_le(v_c_96_, v___x_117_);
if (v___x_118_ == 0)
{
goto v___jp_109_;
}
else
{
v___y_102_ = v___x_118_;
goto v___jp_101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___boxed(lean_object* v_c_123_){
_start:
{
uint8_t v_c_boxed_124_; uint8_t v_res_125_; lean_object* v_r_126_; 
v_c_boxed_124_ = lean_unbox(v_c_123_);
v_res_125_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0(v_c_boxed_124_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(lean_object* v_x_127_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
uint8_t v___x_128_; 
v___x_128_ = 1;
return v___x_128_;
}
else
{
lean_object* v_head_129_; lean_object* v_tail_130_; uint8_t v___y_145_; uint32_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v_head_129_ = lean_ctor_get(v_x_127_, 0);
v_tail_130_ = lean_ctor_get(v_x_127_, 1);
v___x_161_ = lean_unbox_uint32(v_head_129_);
v___x_162_ = lean_uint32_to_nat(v___x_161_);
v___x_163_ = lean_unsigned_to_nat(128u);
v___x_164_ = lean_nat_dec_lt(v___x_162_, v___x_163_);
lean_dec(v___x_162_);
if (v___x_164_ == 0)
{
goto v___jp_131_;
}
else
{
uint32_t v___x_165_; uint32_t v___x_166_; uint8_t v___x_167_; 
v___x_165_ = 48;
v___x_166_ = lean_unbox_uint32(v_head_129_);
v___x_167_ = lean_uint32_dec_le(v___x_165_, v___x_166_);
if (v___x_167_ == 0)
{
goto v___jp_154_;
}
else
{
uint32_t v___x_168_; uint32_t v___x_169_; uint8_t v___x_170_; 
v___x_168_ = 57;
v___x_169_ = lean_unbox_uint32(v_head_129_);
v___x_170_ = lean_uint32_dec_le(v___x_169_, v___x_168_);
if (v___x_170_ == 0)
{
goto v___jp_154_;
}
else
{
v_x_127_ = v_tail_130_;
goto _start;
}
}
}
v___jp_131_:
{
uint32_t v___x_132_; uint32_t v___x_133_; uint8_t v___x_134_; 
v___x_132_ = 43;
v___x_133_ = lean_unbox_uint32(v_head_129_);
v___x_134_ = lean_uint32_dec_eq(v___x_133_, v___x_132_);
if (v___x_134_ == 0)
{
uint32_t v___x_135_; uint32_t v___x_136_; uint8_t v___x_137_; 
v___x_135_ = 45;
v___x_136_ = lean_unbox_uint32(v_head_129_);
v___x_137_ = lean_uint32_dec_eq(v___x_136_, v___x_135_);
if (v___x_137_ == 0)
{
uint32_t v___x_138_; uint32_t v___x_139_; uint8_t v___x_140_; 
v___x_138_ = 46;
v___x_139_ = lean_unbox_uint32(v_head_129_);
v___x_140_ = lean_uint32_dec_eq(v___x_139_, v___x_138_);
if (v___x_140_ == 0)
{
return v___x_140_;
}
else
{
v_x_127_ = v_tail_130_;
goto _start;
}
}
else
{
v_x_127_ = v_tail_130_;
goto _start;
}
}
else
{
v_x_127_ = v_tail_130_;
goto _start;
}
}
v___jp_144_:
{
if (v___y_145_ == 0)
{
uint32_t v___x_146_; uint32_t v___x_147_; uint8_t v___x_148_; 
v___x_146_ = 97;
v___x_147_ = lean_unbox_uint32(v_head_129_);
v___x_148_ = lean_uint32_dec_le(v___x_146_, v___x_147_);
if (v___x_148_ == 0)
{
goto v___jp_131_;
}
else
{
uint32_t v___x_149_; uint32_t v___x_150_; uint8_t v___x_151_; 
v___x_149_ = 122;
v___x_150_ = lean_unbox_uint32(v_head_129_);
v___x_151_ = lean_uint32_dec_le(v___x_150_, v___x_149_);
if (v___x_151_ == 0)
{
goto v___jp_131_;
}
else
{
v_x_127_ = v_tail_130_;
goto _start;
}
}
}
else
{
v_x_127_ = v_tail_130_;
goto _start;
}
}
v___jp_154_:
{
uint32_t v___x_155_; uint32_t v___x_156_; uint8_t v___x_157_; 
v___x_155_ = 65;
v___x_156_ = lean_unbox_uint32(v_head_129_);
v___x_157_ = lean_uint32_dec_le(v___x_155_, v___x_156_);
if (v___x_157_ == 0)
{
v___y_145_ = v___x_157_;
goto v___jp_144_;
}
else
{
uint32_t v___x_158_; uint32_t v___x_159_; uint8_t v___x_160_; 
v___x_158_ = 90;
v___x_159_ = lean_unbox_uint32(v_head_129_);
v___x_160_ = lean_uint32_dec_le(v___x_159_, v___x_158_);
v___y_145_ = v___x_160_;
goto v___jp_144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1___boxed(lean_object* v_x_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(v_x_172_);
lean_dec(v_x_172_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(lean_object* v_s_175_, lean_object* v_p_176_){
_start:
{
uint32_t v___y_178_; lean_object* v___x_183_; uint8_t v_decide_184_; 
v___x_183_ = lean_string_utf8_byte_size(v_s_175_);
v_decide_184_ = lean_nat_dec_eq(v_p_176_, v___x_183_);
if (v_decide_184_ == 0)
{
uint32_t v___x_185_; uint8_t v___y_187_; uint32_t v___x_190_; uint8_t v___x_191_; 
v___x_185_ = lean_string_utf8_get_fast(v_s_175_, v_p_176_);
v___x_190_ = 65;
v___x_191_ = lean_uint32_dec_le(v___x_190_, v___x_185_);
if (v___x_191_ == 0)
{
v___y_187_ = v___x_191_;
goto v___jp_186_;
}
else
{
uint32_t v___x_192_; uint8_t v___x_193_; 
v___x_192_ = 90;
v___x_193_ = lean_uint32_dec_le(v___x_185_, v___x_192_);
v___y_187_ = v___x_193_;
goto v___jp_186_;
}
v___jp_186_:
{
if (v___y_187_ == 0)
{
v___y_178_ = v___x_185_;
goto v___jp_177_;
}
else
{
uint32_t v___x_188_; uint32_t v___x_189_; 
v___x_188_ = 32;
v___x_189_ = lean_uint32_add(v___x_185_, v___x_188_);
v___y_178_ = v___x_189_;
goto v___jp_177_;
}
}
}
else
{
lean_dec(v_p_176_);
return v_s_175_;
}
v___jp_177_:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
lean_inc(v_p_176_);
v___x_179_ = lean_string_utf8_set(v_s_175_, v_p_176_, v___y_178_);
v___x_180_ = l_Char_utf8Size(v___y_178_);
v___x_181_ = lean_nat_add(v_p_176_, v___x_180_);
lean_dec(v___x_180_);
lean_dec(v_p_176_);
v_s_175_ = v___x_179_;
v_p_176_ = v___x_181_;
goto _start;
}
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_203_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6));
v___x_204_ = lean_unsigned_to_nat(46u);
v___x_205_ = lean_unsigned_to_nat(193u);
v___x_206_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5));
v___x_207_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4));
v___x_208_ = l_mkPanicMessageWithDecl(v___x_207_, v___x_206_, v___x_205_, v___x_204_, v___x_203_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(lean_object* v_config_213_, lean_object* v_a_214_){
_start:
{
lean_object* v___y_219_; lean_object* v___y_223_; lean_object* v___y_224_; uint8_t v___y_225_; uint8_t v___y_226_; uint8_t v___y_229_; lean_object* v___y_230_; lean_object* v___y_231_; uint8_t v___y_232_; uint8_t v___y_233_; uint32_t v___y_235_; uint8_t v___y_236_; lean_object* v___y_237_; lean_object* v___y_238_; uint8_t v___y_239_; uint8_t v___y_240_; lean_object* v_maxSchemeLength_245_; lean_object* v___x_246_; uint8_t v___x_247_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_266_; uint8_t v___y_267_; lean_object* v___y_268_; lean_object* v_lower_269_; lean_object* v_upper_270_; lean_object* v___y_283_; lean_object* v___y_284_; uint8_t v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; 
v_maxSchemeLength_245_ = lean_ctor_get(v_config_213_, 0);
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = lean_nat_dec_eq(v_maxSchemeLength_245_, v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v_array_290_; lean_object* v_idx_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v_array_290_ = lean_ctor_get(v_a_214_, 0);
v_idx_291_ = lean_ctor_get(v_a_214_, 1);
v___x_292_ = lean_byte_array_size(v_array_290_);
v___x_293_ = lean_nat_dec_lt(v_idx_291_, v___x_292_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_box(0);
v___x_295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_295_, 0, v_a_214_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
return v___x_295_;
}
else
{
lean_object* v___f_296_; lean_object* v_pos_298_; uint8_t v_res_299_; uint8_t v_c_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v_it_x27_314_; uint8_t v___x_320_; uint8_t v___x_321_; 
v___f_296_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__8));
v_c_311_ = lean_byte_array_fget(v_array_290_, v_idx_291_);
v___x_312_ = lean_unsigned_to_nat(1u);
v___x_313_ = lean_nat_add(v_idx_291_, v___x_312_);
lean_inc_ref(v_array_290_);
v_it_x27_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_314_, 0, v_array_290_);
lean_ctor_set(v_it_x27_314_, 1, v___x_313_);
v___x_320_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_321_ = lean_uint8_dec_le(v___x_320_, v_c_311_);
if (v___x_321_ == 0)
{
goto v___jp_315_;
}
else
{
uint8_t v___x_322_; uint8_t v___x_323_; 
v___x_322_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_323_ = lean_uint8_dec_le(v_c_311_, v___x_322_);
if (v___x_323_ == 0)
{
goto v___jp_315_;
}
else
{
lean_dec_ref(v_a_214_);
v_pos_298_ = v_it_x27_314_;
v_res_299_ = v_c_311_;
goto v___jp_297_;
}
}
v___jp_297_:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v_snd_303_; lean_object* v_fst_304_; lean_object* v_fst_305_; lean_object* v_array_306_; lean_object* v_idx_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_300_ = lean_unsigned_to_nat(1u);
v___x_301_ = lean_nat_sub(v_maxSchemeLength_245_, v___x_300_);
lean_inc_ref(v_pos_298_);
v___x_302_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_296_, v___x_301_, v___x_246_, v_pos_298_);
lean_dec(v___x_301_);
v_snd_303_ = lean_ctor_get(v___x_302_, 1);
lean_inc(v_snd_303_);
v_fst_304_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_fst_304_);
lean_dec_ref(v___x_302_);
v_fst_305_ = lean_ctor_get(v_snd_303_, 0);
lean_inc(v_fst_305_);
lean_dec(v_snd_303_);
v_array_306_ = lean_ctor_get(v_pos_298_, 0);
lean_inc_ref(v_array_306_);
v_idx_307_ = lean_ctor_get(v_pos_298_, 1);
lean_inc(v_idx_307_);
lean_dec_ref(v_pos_298_);
v___x_308_ = lean_nat_add(v_idx_307_, v_fst_304_);
lean_dec(v_fst_304_);
v___x_309_ = lean_byte_array_size(v_array_306_);
v___x_310_ = lean_nat_dec_le(v_idx_307_, v___x_246_);
if (v___x_310_ == 0)
{
v___y_283_ = v___x_309_;
v___y_284_ = v_array_306_;
v___y_285_ = v_res_299_;
v___y_286_ = v_fst_305_;
v___y_287_ = v___x_308_;
v___y_288_ = v_idx_307_;
goto v___jp_282_;
}
else
{
lean_dec(v_idx_307_);
v___y_283_ = v___x_309_;
v___y_284_ = v_array_306_;
v___y_285_ = v_res_299_;
v___y_286_ = v_fst_305_;
v___y_287_ = v___x_308_;
v___y_288_ = v___x_246_;
goto v___jp_282_;
}
}
v___jp_315_:
{
uint8_t v___x_316_; uint8_t v___x_317_; 
v___x_316_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_317_ = lean_uint8_dec_le(v___x_316_, v_c_311_);
if (v___x_317_ == 0)
{
lean_dec_ref_known(v_it_x27_314_, 2);
goto v___jp_215_;
}
else
{
uint8_t v___x_318_; uint8_t v___x_319_; 
v___x_318_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_319_ = lean_uint8_dec_le(v_c_311_, v___x_318_);
if (v___x_319_ == 0)
{
lean_dec_ref_known(v_it_x27_314_, 2);
goto v___jp_215_;
}
else
{
lean_dec_ref(v_a_214_);
v_pos_298_ = v_it_x27_314_;
v_res_299_ = v_c_311_;
goto v___jp_297_;
}
}
}
}
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10));
v___x_325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_325_, 0, v_a_214_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
return v___x_325_;
}
v___jp_215_:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1));
v___x_217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_217_, 0, v_a_214_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
return v___x_217_;
}
v___jp_218_:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3));
v___x_221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_221_, 0, v___y_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
return v___x_221_;
}
v___jp_222_:
{
if (v___y_225_ == 0)
{
lean_dec_ref(v___y_223_);
v___y_219_ = v___y_224_;
goto v___jp_218_;
}
else
{
if (v___y_226_ == 0)
{
lean_dec_ref(v___y_223_);
v___y_219_ = v___y_224_;
goto v___jp_218_;
}
else
{
lean_object* v___x_227_; 
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v___y_224_);
lean_ctor_set(v___x_227_, 1, v___y_223_);
return v___x_227_;
}
}
}
v___jp_228_:
{
if (v___y_229_ == 0)
{
v___y_223_ = v___y_230_;
v___y_224_ = v___y_231_;
v___y_225_ = v___y_232_;
v___y_226_ = v___y_229_;
goto v___jp_222_;
}
else
{
v___y_223_ = v___y_230_;
v___y_224_ = v___y_231_;
v___y_225_ = v___y_232_;
v___y_226_ = v___y_233_;
goto v___jp_222_;
}
}
v___jp_234_:
{
if (v___y_240_ == 0)
{
uint32_t v___x_241_; uint8_t v___x_242_; 
v___x_241_ = 97;
v___x_242_ = lean_uint32_dec_le(v___x_241_, v___y_235_);
if (v___x_242_ == 0)
{
v___y_229_ = v___y_236_;
v___y_230_ = v___y_237_;
v___y_231_ = v___y_238_;
v___y_232_ = v___y_239_;
v___y_233_ = v___x_242_;
goto v___jp_228_;
}
else
{
uint32_t v___x_243_; uint8_t v___x_244_; 
v___x_243_ = 122;
v___x_244_ = lean_uint32_dec_le(v___y_235_, v___x_243_);
v___y_229_ = v___y_236_;
v___y_230_ = v___y_237_;
v___y_231_ = v___y_238_;
v___y_232_ = v___y_239_;
v___y_233_ = v___x_244_;
goto v___jp_228_;
}
}
else
{
v___y_229_ = v___y_236_;
v___y_230_ = v___y_237_;
v___y_231_ = v___y_238_;
v___y_232_ = v___y_239_;
v___y_233_ = v___y_240_;
goto v___jp_228_;
}
}
v___jp_248_:
{
lean_object* v___x_251_; uint8_t v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; lean_object* v___x_255_; 
v___x_251_ = l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___y_250_, v___x_246_);
lean_inc_ref_n(v___x_251_, 2);
v___x_252_ = l_Std_Http_Internal_instDecidableIsLowerCase(v___x_251_);
v___x_253_ = lean_string_data(v___x_251_);
v___x_254_ = l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(v___x_253_);
v___x_255_ = l_List_head_x3f___redArg(v___x_253_);
lean_dec(v___x_253_);
if (lean_obj_tag(v___x_255_) == 0)
{
v___y_229_ = v___x_254_;
v___y_230_ = v___x_251_;
v___y_231_ = v___y_249_;
v___y_232_ = v___x_252_;
v___y_233_ = v___x_247_;
goto v___jp_228_;
}
else
{
lean_object* v_val_256_; uint32_t v___x_257_; uint32_t v___x_258_; uint8_t v___x_259_; 
v_val_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_val_256_);
lean_dec_ref_known(v___x_255_, 1);
v___x_257_ = 65;
v___x_258_ = lean_unbox_uint32(v_val_256_);
v___x_259_ = lean_uint32_dec_le(v___x_257_, v___x_258_);
if (v___x_259_ == 0)
{
uint32_t v___x_260_; 
v___x_260_ = lean_unbox_uint32(v_val_256_);
lean_dec(v_val_256_);
v___y_235_ = v___x_260_;
v___y_236_ = v___x_254_;
v___y_237_ = v___x_251_;
v___y_238_ = v___y_249_;
v___y_239_ = v___x_252_;
v___y_240_ = v___x_259_;
goto v___jp_234_;
}
else
{
uint32_t v___x_261_; uint32_t v___x_262_; uint8_t v___x_263_; uint32_t v___x_264_; 
v___x_261_ = 90;
v___x_262_ = lean_unbox_uint32(v_val_256_);
v___x_263_ = lean_uint32_dec_le(v___x_262_, v___x_261_);
v___x_264_ = lean_unbox_uint32(v_val_256_);
lean_dec(v_val_256_);
v___y_235_ = v___x_264_;
v___y_236_ = v___x_254_;
v___y_237_ = v___x_251_;
v___y_238_ = v___y_249_;
v___y_239_ = v___x_252_;
v___y_240_ = v___x_263_;
goto v___jp_234_;
}
}
}
v___jp_265_:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_271_ = l_ByteArray_toByteSlice(v___y_266_, v_lower_269_, v_upper_270_);
v___x_272_ = l_ByteArray_empty;
v___x_273_ = lean_byte_array_push(v___x_272_, v___y_267_);
v___x_274_ = l_ByteSlice_toByteArray(v___x_271_);
v___x_275_ = lean_byte_array_size(v___x_273_);
v___x_276_ = lean_byte_array_size(v___x_274_);
v___x_277_ = lean_byte_array_copy_slice(v___x_274_, v___x_246_, v___x_273_, v___x_275_, v___x_276_, v___x_247_);
lean_dec_ref(v___x_274_);
v___x_278_ = lean_string_validate_utf8(v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; 
lean_dec_ref(v___x_277_);
v___x_279_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_280_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_279_);
v___y_249_ = v___y_268_;
v___y_250_ = v___x_280_;
goto v___jp_248_;
}
else
{
lean_object* v___x_281_; 
v___x_281_ = lean_string_from_utf8_unchecked(v___x_277_);
v___y_249_ = v___y_268_;
v___y_250_ = v___x_281_;
goto v___jp_248_;
}
}
v___jp_282_:
{
uint8_t v___x_289_; 
v___x_289_ = lean_nat_dec_le(v___y_287_, v___y_283_);
if (v___x_289_ == 0)
{
lean_dec(v___y_287_);
v___y_266_ = v___y_284_;
v___y_267_ = v___y_285_;
v___y_268_ = v___y_286_;
v_lower_269_ = v___y_288_;
v_upper_270_ = v___y_283_;
goto v___jp_265_;
}
else
{
lean_dec(v___y_283_);
v___y_266_ = v___y_284_;
v___y_267_ = v___y_285_;
v___y_268_ = v___y_286_;
v_lower_269_ = v___y_288_;
v_upper_270_ = v___y_287_;
goto v___jp_265_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___boxed(lean_object* v_config_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_326_, v_a_327_);
lean_dec_ref(v_config_326_);
return v_res_328_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(uint8_t v___y_329_){
_start:
{
uint8_t v___x_330_; uint8_t v___x_331_; 
v___x_330_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_331_ = lean_uint8_dec_le(v___x_330_, v___y_329_);
if (v___x_331_ == 0)
{
return v___x_331_;
}
else
{
uint8_t v___x_332_; uint8_t v___x_333_; 
v___x_332_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_333_ = lean_uint8_dec_le(v___y_329_, v___x_332_);
return v___x_333_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0___boxed(lean_object* v___y_334_){
_start:
{
uint8_t v___y_564__boxed_335_; uint8_t v_res_336_; lean_object* v_r_337_; 
v___y_564__boxed_335_ = lean_unbox(v___y_334_);
v_res_336_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(v___y_564__boxed_335_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(lean_object* v_a_341_){
_start:
{
lean_object* v___f_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v_snd_346_; lean_object* v_fst_347_; lean_object* v_fst_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_401_; 
v___f_342_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0));
v___x_343_ = lean_unsigned_to_nat(5u);
v___x_344_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_341_);
v___x_345_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_342_, v___x_343_, v___x_344_, v_a_341_);
v_snd_346_ = lean_ctor_get(v___x_345_, 1);
lean_inc(v_snd_346_);
v_fst_347_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_fst_347_);
lean_dec_ref(v___x_345_);
v_fst_348_ = lean_ctor_get(v_snd_346_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v_snd_346_);
if (v_isSharedCheck_401_ == 0)
{
lean_object* v_unused_402_; 
v_unused_402_ = lean_ctor_get(v_snd_346_, 1);
lean_dec(v_unused_402_);
v___x_350_ = v_snd_346_;
v_isShared_351_ = v_isSharedCheck_401_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_fst_348_);
lean_dec(v_snd_346_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_401_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___y_353_; lean_object* v_array_384_; lean_object* v_idx_385_; lean_object* v_lower_387_; lean_object* v_upper_388_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___y_398_; uint8_t v___x_400_; 
v_array_384_ = lean_ctor_get(v_a_341_, 0);
lean_inc_ref(v_array_384_);
v_idx_385_ = lean_ctor_get(v_a_341_, 1);
lean_inc(v_idx_385_);
lean_dec_ref(v_a_341_);
v___x_395_ = lean_nat_add(v_idx_385_, v_fst_347_);
lean_dec(v_fst_347_);
v___x_396_ = lean_byte_array_size(v_array_384_);
v___x_400_ = lean_nat_dec_le(v_idx_385_, v___x_344_);
if (v___x_400_ == 0)
{
v___y_398_ = v_idx_385_;
goto v___jp_397_;
}
else
{
lean_dec(v_idx_385_);
v___y_398_ = v___x_344_;
goto v___jp_397_;
}
v___jp_352_:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_354_ = lean_string_utf8_byte_size(v___y_353_);
lean_inc_ref(v___y_353_);
v___x_355_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_355_, 0, v___y_353_);
lean_ctor_set(v___x_355_, 1, v___x_344_);
lean_ctor_set(v___x_355_, 2, v___x_354_);
v___x_356_ = l_String_Slice_toNat_x3f(v___x_355_);
lean_dec_ref_known(v___x_355_, 3);
if (lean_obj_tag(v___x_356_) == 1)
{
lean_object* v_val_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_377_; 
lean_dec_ref(v___y_353_);
v_val_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_377_ == 0)
{
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_377_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_val_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_377_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_361_ = lean_unsigned_to_nat(65535u);
v___x_362_ = lean_nat_dec_lt(v___x_361_, v_val_357_);
if (v___x_362_ == 0)
{
uint16_t v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
lean_del_object(v___x_359_);
v___x_363_ = lean_uint16_of_nat(v_val_357_);
lean_dec(v_val_357_);
v___x_364_ = lean_box(v___x_363_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 1, v___x_364_);
v___x_366_ = v___x_350_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_fst_348_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v___x_364_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_368_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1));
v___x_369_ = l_Nat_reprFast(v_val_357_);
v___x_370_ = lean_string_append(v___x_368_, v___x_369_);
lean_dec_ref(v___x_369_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_370_);
v___x_372_ = v___x_359_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_370_);
v___x_372_ = v_reuseFailAlloc_376_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_374_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set_tag(v___x_350_, 1);
lean_ctor_set(v___x_350_, 1, v___x_372_);
v___x_374_ = v___x_350_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_fst_348_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
lean_dec(v___x_356_);
v___x_378_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2));
v___x_379_ = lean_string_append(v___x_378_, v___y_353_);
lean_dec_ref(v___y_353_);
v___x_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
if (v_isShared_351_ == 0)
{
lean_ctor_set_tag(v___x_350_, 1);
lean_ctor_set(v___x_350_, 1, v___x_380_);
v___x_382_ = v___x_350_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_fst_348_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
v___jp_386_:
{
lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_389_ = l_ByteArray_toByteSlice(v_array_384_, v_lower_387_, v_upper_388_);
v___x_390_ = l_ByteSlice_toByteArray(v___x_389_);
v___x_391_ = lean_string_validate_utf8(v___x_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; 
lean_dec_ref(v___x_390_);
v___x_392_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_393_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_392_);
v___y_353_ = v___x_393_;
goto v___jp_352_;
}
else
{
lean_object* v___x_394_; 
v___x_394_ = lean_string_from_utf8_unchecked(v___x_390_);
v___y_353_ = v___x_394_;
goto v___jp_352_;
}
}
v___jp_397_:
{
uint8_t v___x_399_; 
v___x_399_ = lean_nat_dec_le(v___x_395_, v___x_396_);
if (v___x_399_ == 0)
{
lean_dec(v___x_395_);
v_lower_387_ = v___y_398_;
v_upper_388_ = v___x_396_;
goto v___jp_386_;
}
else
{
v_lower_387_ = v___y_398_;
v_upper_388_ = v___x_395_;
goto v___jp_386_;
}
}
}
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0(void){
_start:
{
uint32_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = 37;
v___x_404_ = lean_uint32_to_uint8(v___x_403_);
return v___x_404_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1(void){
_start:
{
uint32_t v___x_405_; uint8_t v___x_406_; 
v___x_405_ = 58;
v___x_406_ = lean_uint32_to_uint8(v___x_405_);
return v___x_406_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2(void){
_start:
{
uint32_t v___x_407_; uint8_t v___x_408_; 
v___x_407_ = 95;
v___x_408_ = lean_uint32_to_uint8(v___x_407_);
return v___x_408_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3(void){
_start:
{
uint32_t v___x_409_; uint8_t v___x_410_; 
v___x_409_ = 126;
v___x_410_ = lean_uint32_to_uint8(v___x_409_);
return v___x_410_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4(void){
_start:
{
uint32_t v___x_411_; uint8_t v___x_412_; 
v___x_411_ = 33;
v___x_412_ = lean_uint32_to_uint8(v___x_411_);
return v___x_412_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5(void){
_start:
{
uint32_t v___x_413_; uint8_t v___x_414_; 
v___x_413_ = 36;
v___x_414_ = lean_uint32_to_uint8(v___x_413_);
return v___x_414_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6(void){
_start:
{
uint32_t v___x_415_; uint8_t v___x_416_; 
v___x_415_ = 38;
v___x_416_ = lean_uint32_to_uint8(v___x_415_);
return v___x_416_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7(void){
_start:
{
uint32_t v___x_417_; uint8_t v___x_418_; 
v___x_417_ = 39;
v___x_418_ = lean_uint32_to_uint8(v___x_417_);
return v___x_418_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8(void){
_start:
{
uint32_t v___x_419_; uint8_t v___x_420_; 
v___x_419_ = 40;
v___x_420_ = lean_uint32_to_uint8(v___x_419_);
return v___x_420_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9(void){
_start:
{
uint32_t v___x_421_; uint8_t v___x_422_; 
v___x_421_ = 41;
v___x_422_ = lean_uint32_to_uint8(v___x_421_);
return v___x_422_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10(void){
_start:
{
uint32_t v___x_423_; uint8_t v___x_424_; 
v___x_423_ = 42;
v___x_424_ = lean_uint32_to_uint8(v___x_423_);
return v___x_424_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11(void){
_start:
{
uint32_t v___x_425_; uint8_t v___x_426_; 
v___x_425_ = 44;
v___x_426_ = lean_uint32_to_uint8(v___x_425_);
return v___x_426_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12(void){
_start:
{
uint32_t v___x_427_; uint8_t v___x_428_; 
v___x_427_ = 59;
v___x_428_ = lean_uint32_to_uint8(v___x_427_);
return v___x_428_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13(void){
_start:
{
uint32_t v___x_429_; uint8_t v___x_430_; 
v___x_429_ = 61;
v___x_430_ = lean_uint32_to_uint8(v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(uint8_t v_x_431_){
_start:
{
uint8_t v___y_433_; uint8_t v___y_434_; uint8_t v___x_437_; uint8_t v___x_438_; uint8_t v___y_440_; uint8_t v___y_472_; uint8_t v___y_478_; uint8_t v___y_484_; 
v___x_437_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_438_ = lean_uint8_dec_eq(v_x_431_, v___x_437_);
if (v___x_438_ == 0)
{
uint8_t v___x_489_; 
v___x_489_ = 1;
v___y_484_ = v___x_489_;
goto v___jp_483_;
}
else
{
uint8_t v___x_490_; 
v___x_490_ = 0;
v___y_484_ = v___x_490_;
goto v___jp_483_;
}
v___jp_432_:
{
if (v___y_434_ == 0)
{
if (v___y_433_ == 0)
{
return v___y_433_;
}
else
{
uint8_t v___x_435_; uint8_t v___x_436_; 
v___x_435_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_436_ = lean_uint8_dec_eq(v_x_431_, v___x_435_);
return v___x_436_;
}
}
else
{
if (v___y_433_ == 0)
{
return v___y_433_;
}
else
{
return v___y_434_;
}
}
}
v___jp_439_:
{
uint8_t v___x_441_; uint8_t v___x_442_; 
v___x_441_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_442_ = lean_uint8_dec_eq(v_x_431_, v___x_441_);
if (v___x_442_ == 0)
{
uint8_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_444_ = lean_uint8_dec_eq(v_x_431_, v___x_443_);
if (v___x_444_ == 0)
{
uint8_t v___x_445_; uint8_t v___x_446_; 
v___x_445_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_446_ = lean_uint8_dec_eq(v_x_431_, v___x_445_);
if (v___x_446_ == 0)
{
uint8_t v___x_447_; uint8_t v___x_448_; 
v___x_447_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_448_ = lean_uint8_dec_eq(v_x_431_, v___x_447_);
if (v___x_448_ == 0)
{
uint8_t v___x_449_; uint8_t v___x_450_; 
v___x_449_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_450_ = lean_uint8_dec_eq(v_x_431_, v___x_449_);
if (v___x_450_ == 0)
{
uint8_t v___x_451_; uint8_t v___x_452_; 
v___x_451_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_452_ = lean_uint8_dec_eq(v_x_431_, v___x_451_);
if (v___x_452_ == 0)
{
uint8_t v___x_453_; uint8_t v___x_454_; 
v___x_453_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_454_ = lean_uint8_dec_eq(v_x_431_, v___x_453_);
if (v___x_454_ == 0)
{
uint8_t v___x_455_; uint8_t v___x_456_; 
v___x_455_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_456_ = lean_uint8_dec_eq(v_x_431_, v___x_455_);
if (v___x_456_ == 0)
{
uint8_t v___x_457_; uint8_t v___x_458_; 
v___x_457_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_458_ = lean_uint8_dec_eq(v_x_431_, v___x_457_);
if (v___x_458_ == 0)
{
uint8_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_460_ = lean_uint8_dec_eq(v_x_431_, v___x_459_);
if (v___x_460_ == 0)
{
uint8_t v___x_461_; uint8_t v___x_462_; 
v___x_461_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_462_ = lean_uint8_dec_eq(v_x_431_, v___x_461_);
if (v___x_462_ == 0)
{
uint8_t v___x_463_; uint8_t v___x_464_; 
v___x_463_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_464_ = lean_uint8_dec_eq(v_x_431_, v___x_463_);
if (v___x_464_ == 0)
{
uint8_t v___x_465_; uint8_t v___x_466_; 
v___x_465_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_466_ = lean_uint8_dec_eq(v_x_431_, v___x_465_);
if (v___x_466_ == 0)
{
uint8_t v___x_467_; uint8_t v___x_468_; 
v___x_467_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_468_ = lean_uint8_dec_eq(v_x_431_, v___x_467_);
if (v___x_468_ == 0)
{
uint8_t v___x_469_; uint8_t v___x_470_; 
v___x_469_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_470_ = lean_uint8_dec_eq(v_x_431_, v___x_469_);
if (v___x_470_ == 0)
{
v___y_433_ = v___y_440_;
v___y_434_ = v___x_438_;
goto v___jp_432_;
}
else
{
v___y_433_ = v___y_440_;
v___y_434_ = v___x_470_;
goto v___jp_432_;
}
}
else
{
v___y_433_ = v___y_440_;
v___y_434_ = v___x_468_;
goto v___jp_432_;
}
}
else
{
v___y_433_ = v___y_440_;
v___y_434_ = v___x_466_;
goto v___jp_432_;
}
}
else
{
v___y_433_ = v___y_440_;
v___y_434_ = v___x_464_;
goto v___jp_432_;
}
}
else
{
v___y_433_ = v___y_440_;
v___y_434_ = v___x_462_;
goto v___jp_432_;
}
}
else
{
v___y_433_ = v___y_440_;
v___y_434_ = v___x_460_;
goto v___jp_432_;
}
}
else
{
v___y_433_ = v___y_440_;
v___y_434_ = v___x_458_;
goto v___jp_432_;
}
}
else
{
v___y_433_ = v___y_440_;
v___y_434_ = v___x_456_;
goto v___jp_432_;
}
}
else
{
v___y_433_ = v___y_440_;
v___y_434_ = v___x_454_;
goto v___jp_432_;
}
}
else
{
v___y_433_ = v___y_440_;
v___y_434_ = v___x_452_;
goto v___jp_432_;
}
}
else
{
v___y_433_ = v___y_440_;
v___y_434_ = v___x_450_;
goto v___jp_432_;
}
}
else
{
v___y_433_ = v___y_440_;
v___y_434_ = v___x_448_;
goto v___jp_432_;
}
}
else
{
v___y_433_ = v___y_440_;
v___y_434_ = v___x_446_;
goto v___jp_432_;
}
}
else
{
v___y_433_ = v___y_440_;
v___y_434_ = v___x_444_;
goto v___jp_432_;
}
}
else
{
v___y_433_ = v___y_440_;
v___y_434_ = v___x_442_;
goto v___jp_432_;
}
}
v___jp_471_:
{
uint8_t v___x_473_; uint8_t v___x_474_; 
v___x_473_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_474_ = lean_uint8_dec_le(v___x_473_, v_x_431_);
if (v___x_474_ == 0)
{
v___y_440_ = v___y_472_;
goto v___jp_439_;
}
else
{
uint8_t v___x_475_; uint8_t v___x_476_; 
v___x_475_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_476_ = lean_uint8_dec_le(v_x_431_, v___x_475_);
if (v___x_476_ == 0)
{
v___y_440_ = v___y_472_;
goto v___jp_439_;
}
else
{
v___y_433_ = v___y_472_;
v___y_434_ = v___x_476_;
goto v___jp_432_;
}
}
}
v___jp_477_:
{
uint8_t v___x_479_; uint8_t v___x_480_; 
v___x_479_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_480_ = lean_uint8_dec_le(v___x_479_, v_x_431_);
if (v___x_480_ == 0)
{
v___y_472_ = v___y_478_;
goto v___jp_471_;
}
else
{
uint8_t v___x_481_; uint8_t v___x_482_; 
v___x_481_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_482_ = lean_uint8_dec_le(v_x_431_, v___x_481_);
if (v___x_482_ == 0)
{
v___y_472_ = v___y_478_;
goto v___jp_471_;
}
else
{
v___y_433_ = v___y_478_;
v___y_434_ = v___x_482_;
goto v___jp_432_;
}
}
}
v___jp_483_:
{
uint8_t v___x_485_; uint8_t v___x_486_; 
v___x_485_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_486_ = lean_uint8_dec_le(v___x_485_, v_x_431_);
if (v___x_486_ == 0)
{
v___y_478_ = v___y_484_;
goto v___jp_477_;
}
else
{
uint8_t v___x_487_; uint8_t v___x_488_; 
v___x_487_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_488_ = lean_uint8_dec_le(v_x_431_, v___x_487_);
if (v___x_488_ == 0)
{
v___y_478_ = v___y_484_;
goto v___jp_477_;
}
else
{
v___y_433_ = v___y_484_;
v___y_434_ = v___x_488_;
goto v___jp_432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___boxed(lean_object* v_x_491_){
_start:
{
uint8_t v_x_boxed_492_; uint8_t v_res_493_; lean_object* v_r_494_; 
v_x_boxed_492_ = lean_unbox(v_x_491_);
v_res_493_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(v_x_boxed_492_);
v_r_494_ = lean_box(v_res_493_);
return v_r_494_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(uint8_t v_x_495_){
_start:
{
uint8_t v___y_497_; uint8_t v___x_543_; uint8_t v___x_544_; 
v___x_543_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_544_ = lean_uint8_dec_le(v___x_543_, v_x_495_);
if (v___x_544_ == 0)
{
goto v___jp_538_;
}
else
{
uint8_t v___x_545_; uint8_t v___x_546_; 
v___x_545_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_546_ = lean_uint8_dec_le(v_x_495_, v___x_545_);
if (v___x_546_ == 0)
{
goto v___jp_538_;
}
else
{
v___y_497_ = v___x_546_;
goto v___jp_496_;
}
}
v___jp_496_:
{
if (v___y_497_ == 0)
{
uint8_t v___x_498_; uint8_t v___x_499_; 
v___x_498_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_499_ = lean_uint8_dec_eq(v_x_495_, v___x_498_);
return v___x_499_;
}
else
{
return v___y_497_;
}
}
v___jp_500_:
{
uint8_t v___x_501_; uint8_t v___x_502_; 
v___x_501_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_502_ = lean_uint8_dec_eq(v_x_495_, v___x_501_);
if (v___x_502_ == 0)
{
uint8_t v___x_503_; uint8_t v___x_504_; 
v___x_503_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_504_ = lean_uint8_dec_eq(v_x_495_, v___x_503_);
if (v___x_504_ == 0)
{
uint8_t v___x_505_; uint8_t v___x_506_; 
v___x_505_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_506_ = lean_uint8_dec_eq(v_x_495_, v___x_505_);
if (v___x_506_ == 0)
{
uint8_t v___x_507_; uint8_t v___x_508_; 
v___x_507_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_508_ = lean_uint8_dec_eq(v_x_495_, v___x_507_);
if (v___x_508_ == 0)
{
uint8_t v___x_509_; uint8_t v___x_510_; 
v___x_509_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_510_ = lean_uint8_dec_eq(v_x_495_, v___x_509_);
if (v___x_510_ == 0)
{
uint8_t v___x_511_; uint8_t v___x_512_; 
v___x_511_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_512_ = lean_uint8_dec_eq(v_x_495_, v___x_511_);
if (v___x_512_ == 0)
{
uint8_t v___x_513_; uint8_t v___x_514_; 
v___x_513_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_514_ = lean_uint8_dec_eq(v_x_495_, v___x_513_);
if (v___x_514_ == 0)
{
uint8_t v___x_515_; uint8_t v___x_516_; 
v___x_515_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_516_ = lean_uint8_dec_eq(v_x_495_, v___x_515_);
if (v___x_516_ == 0)
{
uint8_t v___x_517_; uint8_t v___x_518_; 
v___x_517_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_518_ = lean_uint8_dec_eq(v_x_495_, v___x_517_);
if (v___x_518_ == 0)
{
uint8_t v___x_519_; uint8_t v___x_520_; 
v___x_519_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_520_ = lean_uint8_dec_eq(v_x_495_, v___x_519_);
if (v___x_520_ == 0)
{
uint8_t v___x_521_; uint8_t v___x_522_; 
v___x_521_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_522_ = lean_uint8_dec_eq(v_x_495_, v___x_521_);
if (v___x_522_ == 0)
{
uint8_t v___x_523_; uint8_t v___x_524_; 
v___x_523_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_524_ = lean_uint8_dec_eq(v_x_495_, v___x_523_);
if (v___x_524_ == 0)
{
uint8_t v___x_525_; uint8_t v___x_526_; 
v___x_525_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_526_ = lean_uint8_dec_eq(v_x_495_, v___x_525_);
if (v___x_526_ == 0)
{
uint8_t v___x_527_; uint8_t v___x_528_; 
v___x_527_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_528_ = lean_uint8_dec_eq(v_x_495_, v___x_527_);
if (v___x_528_ == 0)
{
uint8_t v___x_529_; uint8_t v___x_530_; 
v___x_529_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_530_ = lean_uint8_dec_eq(v_x_495_, v___x_529_);
if (v___x_530_ == 0)
{
uint8_t v___x_531_; uint8_t v___x_532_; 
v___x_531_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_532_ = lean_uint8_dec_eq(v_x_495_, v___x_531_);
v___y_497_ = v___x_532_;
goto v___jp_496_;
}
else
{
v___y_497_ = v___x_530_;
goto v___jp_496_;
}
}
else
{
v___y_497_ = v___x_528_;
goto v___jp_496_;
}
}
else
{
v___y_497_ = v___x_526_;
goto v___jp_496_;
}
}
else
{
v___y_497_ = v___x_524_;
goto v___jp_496_;
}
}
else
{
v___y_497_ = v___x_522_;
goto v___jp_496_;
}
}
else
{
v___y_497_ = v___x_520_;
goto v___jp_496_;
}
}
else
{
v___y_497_ = v___x_518_;
goto v___jp_496_;
}
}
else
{
v___y_497_ = v___x_516_;
goto v___jp_496_;
}
}
else
{
v___y_497_ = v___x_514_;
goto v___jp_496_;
}
}
else
{
v___y_497_ = v___x_512_;
goto v___jp_496_;
}
}
else
{
v___y_497_ = v___x_510_;
goto v___jp_496_;
}
}
else
{
v___y_497_ = v___x_508_;
goto v___jp_496_;
}
}
else
{
v___y_497_ = v___x_506_;
goto v___jp_496_;
}
}
else
{
v___y_497_ = v___x_504_;
goto v___jp_496_;
}
}
else
{
v___y_497_ = v___x_502_;
goto v___jp_496_;
}
}
v___jp_533_:
{
uint8_t v___x_534_; uint8_t v___x_535_; 
v___x_534_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_535_ = lean_uint8_dec_le(v___x_534_, v_x_495_);
if (v___x_535_ == 0)
{
goto v___jp_500_;
}
else
{
uint8_t v___x_536_; uint8_t v___x_537_; 
v___x_536_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_537_ = lean_uint8_dec_le(v_x_495_, v___x_536_);
if (v___x_537_ == 0)
{
goto v___jp_500_;
}
else
{
v___y_497_ = v___x_537_;
goto v___jp_496_;
}
}
}
v___jp_538_:
{
uint8_t v___x_539_; uint8_t v___x_540_; 
v___x_539_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_540_ = lean_uint8_dec_le(v___x_539_, v_x_495_);
if (v___x_540_ == 0)
{
goto v___jp_533_;
}
else
{
uint8_t v___x_541_; uint8_t v___x_542_; 
v___x_541_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_542_ = lean_uint8_dec_le(v_x_495_, v___x_541_);
if (v___x_542_ == 0)
{
goto v___jp_533_;
}
else
{
v___y_497_ = v___x_542_;
goto v___jp_496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed(lean_object* v_x_547_){
_start:
{
uint8_t v_x_boxed_548_; uint8_t v_res_549_; lean_object* v_r_550_; 
v_x_boxed_548_ = lean_unbox(v_x_547_);
v_res_549_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(v_x_boxed_548_);
v_r_550_ = lean_box(v_res_549_);
return v_r_550_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(lean_object* v_config_556_, lean_object* v_a_557_){
_start:
{
lean_object* v___y_559_; lean_object* v_userPassEncoded_560_; lean_object* v___y_561_; lean_object* v___y_565_; lean_object* v_pos_566_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v_lower_572_; lean_object* v_upper_573_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v_maxUserInfoLength_587_; lean_object* v___f_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v_snd_591_; lean_object* v_fst_592_; lean_object* v_fst_593_; lean_object* v_array_594_; lean_object* v_idx_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_645_; 
v_maxUserInfoLength_587_ = lean_ctor_get(v_config_556_, 2);
v___f_588_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2));
v___x_589_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_557_);
v___x_590_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_588_, v_maxUserInfoLength_587_, v___x_589_, v_a_557_);
v_snd_591_ = lean_ctor_get(v___x_590_, 1);
lean_inc(v_snd_591_);
v_fst_592_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_fst_592_);
lean_dec_ref(v___x_590_);
v_fst_593_ = lean_ctor_get(v_snd_591_, 0);
lean_inc(v_fst_593_);
lean_dec(v_snd_591_);
v_array_594_ = lean_ctor_get(v_a_557_, 0);
v_idx_595_ = lean_ctor_get(v_a_557_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_a_557_);
if (v_isSharedCheck_645_ == 0)
{
v___x_597_ = v_a_557_;
v_isShared_598_ = v_isSharedCheck_645_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_idx_595_);
lean_inc(v_array_594_);
lean_dec(v_a_557_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_645_;
goto v_resetjp_596_;
}
v___jp_558_:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v___y_559_);
lean_ctor_set(v___x_562_, 1, v_userPassEncoded_560_);
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v___y_561_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
return v___x_563_;
}
v___jp_564_:
{
lean_object* v___x_567_; 
v___x_567_ = lean_box(0);
v___y_559_ = v___y_565_;
v_userPassEncoded_560_ = v___x_567_;
v___y_561_ = v_pos_566_;
goto v___jp_558_;
}
v___jp_568_:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = l_ByteArray_toByteSlice(v___y_570_, v_lower_572_, v_upper_573_);
v___x_575_ = l_ByteSlice_toByteArray(v___x_574_);
v___x_576_ = l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(v___x_575_);
if (lean_obj_tag(v___x_576_) == 1)
{
v___y_559_ = v___y_569_;
v_userPassEncoded_560_ = v___x_576_;
v___y_561_ = v___y_571_;
goto v___jp_558_;
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; 
lean_dec(v___x_576_);
lean_dec_ref(v___y_569_);
v___x_577_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1));
v___x_578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_578_, 0, v___y_571_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
return v___x_578_;
}
}
v___jp_579_:
{
uint8_t v___x_586_; 
v___x_586_ = lean_nat_dec_le(v___y_582_, v___y_584_);
if (v___x_586_ == 0)
{
lean_dec(v___y_582_);
v___y_569_ = v___y_580_;
v___y_570_ = v___y_581_;
v___y_571_ = v___y_583_;
v_lower_572_ = v___y_585_;
v_upper_573_ = v___y_584_;
goto v___jp_568_;
}
else
{
lean_dec(v___y_584_);
v___y_569_ = v___y_580_;
v___y_570_ = v___y_581_;
v___y_571_ = v___y_583_;
v_lower_572_ = v___y_585_;
v_upper_573_ = v___y_582_;
goto v___jp_568_;
}
}
v_resetjp_596_:
{
lean_object* v___f_599_; lean_object* v_lower_601_; lean_object* v_upper_602_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___y_642_; uint8_t v___x_644_; 
v___f_599_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__3));
v___x_639_ = lean_nat_add(v_idx_595_, v_fst_592_);
lean_dec(v_fst_592_);
v___x_640_ = lean_byte_array_size(v_array_594_);
v___x_644_ = lean_nat_dec_le(v_idx_595_, v___x_589_);
if (v___x_644_ == 0)
{
v___y_642_ = v_idx_595_;
goto v___jp_641_;
}
else
{
lean_dec(v_idx_595_);
v___y_642_ = v___x_589_;
goto v___jp_641_;
}
v___jp_600_:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_603_ = l_ByteArray_toByteSlice(v_array_594_, v_lower_601_, v_upper_602_);
v___x_604_ = l_ByteSlice_toByteArray(v___x_603_);
v___x_605_ = l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(v___x_604_);
if (lean_obj_tag(v___x_605_) == 1)
{
lean_object* v_val_606_; lean_object* v_array_607_; lean_object* v_idx_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v_val_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_val_606_);
lean_dec_ref_known(v___x_605_, 1);
v_array_607_ = lean_ctor_get(v_fst_593_, 0);
v_idx_608_ = lean_ctor_get(v_fst_593_, 1);
v___x_609_ = lean_byte_array_size(v_array_607_);
v___x_610_ = lean_nat_dec_lt(v_idx_608_, v___x_609_);
if (v___x_610_ == 0)
{
lean_del_object(v___x_597_);
v___y_565_ = v_val_606_;
v_pos_566_ = v_fst_593_;
goto v___jp_564_;
}
else
{
uint8_t v___x_611_; uint8_t v___x_612_; uint8_t v___x_613_; 
v___x_611_ = lean_byte_array_fget(v_array_607_, v_idx_608_);
v___x_612_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_613_ = lean_uint8_dec_eq(v___x_611_, v___x_612_);
if (v___x_613_ == 0)
{
lean_del_object(v___x_597_);
v___y_565_ = v_val_606_;
v_pos_566_ = v_fst_593_;
goto v___jp_564_;
}
else
{
if (v___x_610_ == 0)
{
lean_object* v___x_614_; lean_object* v___x_616_; 
lean_dec(v_val_606_);
v___x_614_ = lean_box(0);
if (v_isShared_598_ == 0)
{
lean_ctor_set_tag(v___x_597_, 1);
lean_ctor_set(v___x_597_, 1, v___x_614_);
lean_ctor_set(v___x_597_, 0, v_fst_593_);
v___x_616_ = v___x_597_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_fst_593_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
else
{
lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_632_; 
lean_inc(v_idx_608_);
lean_inc_ref(v_array_607_);
lean_del_object(v___x_597_);
v_isSharedCheck_632_ = !lean_is_exclusive(v_fst_593_);
if (v_isSharedCheck_632_ == 0)
{
lean_object* v_unused_633_; lean_object* v_unused_634_; 
v_unused_633_ = lean_ctor_get(v_fst_593_, 1);
lean_dec(v_unused_633_);
v_unused_634_ = lean_ctor_get(v_fst_593_, 0);
lean_dec(v_unused_634_);
v___x_619_ = v_fst_593_;
v_isShared_620_ = v_isSharedCheck_632_;
goto v_resetjp_618_;
}
else
{
lean_dec(v_fst_593_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_632_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_621_ = lean_unsigned_to_nat(1u);
v___x_622_ = lean_nat_add(v_idx_608_, v___x_621_);
lean_dec(v_idx_608_);
lean_inc(v___x_622_);
lean_inc_ref(v_array_607_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v___x_622_);
v___x_624_ = v___x_619_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_array_607_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v___x_622_);
v___x_624_ = v_reuseFailAlloc_631_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_625_; lean_object* v_snd_626_; lean_object* v_fst_627_; lean_object* v_fst_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_625_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_599_, v_maxUserInfoLength_587_, v___x_589_, v___x_624_);
v_snd_626_ = lean_ctor_get(v___x_625_, 1);
lean_inc(v_snd_626_);
v_fst_627_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_fst_627_);
lean_dec_ref(v___x_625_);
v_fst_628_ = lean_ctor_get(v_snd_626_, 0);
lean_inc(v_fst_628_);
lean_dec(v_snd_626_);
v___x_629_ = lean_nat_add(v___x_622_, v_fst_627_);
lean_dec(v_fst_627_);
v___x_630_ = lean_nat_dec_le(v___x_622_, v___x_589_);
if (v___x_630_ == 0)
{
v___y_580_ = v_val_606_;
v___y_581_ = v_array_607_;
v___y_582_ = v___x_629_;
v___y_583_ = v_fst_628_;
v___y_584_ = v___x_609_;
v___y_585_ = v___x_622_;
goto v___jp_579_;
}
else
{
lean_dec(v___x_622_);
v___y_580_ = v_val_606_;
v___y_581_ = v_array_607_;
v___y_582_ = v___x_629_;
v___y_583_ = v_fst_628_;
v___y_584_ = v___x_609_;
v___y_585_ = v___x_589_;
goto v___jp_579_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_635_; lean_object* v___x_637_; 
lean_dec(v___x_605_);
v___x_635_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1));
if (v_isShared_598_ == 0)
{
lean_ctor_set_tag(v___x_597_, 1);
lean_ctor_set(v___x_597_, 1, v___x_635_);
lean_ctor_set(v___x_597_, 0, v_fst_593_);
v___x_637_ = v___x_597_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_fst_593_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
v___jp_641_:
{
uint8_t v___x_643_; 
v___x_643_ = lean_nat_dec_le(v___x_639_, v___x_640_);
if (v___x_643_ == 0)
{
lean_dec(v___x_639_);
v_lower_601_ = v___y_642_;
v_upper_602_ = v___x_640_;
goto v___jp_600_;
}
else
{
v_lower_601_ = v___y_642_;
v_upper_602_ = v___x_639_;
goto v___jp_600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___boxed(lean_object* v_config_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(v_config_646_, v_a_647_);
lean_dec_ref(v_config_646_);
return v_res_648_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0(void){
_start:
{
uint32_t v___x_649_; uint8_t v___x_650_; 
v___x_649_ = 70;
v___x_650_ = lean_uint32_to_uint8(v___x_649_);
return v___x_650_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1(void){
_start:
{
uint32_t v___x_651_; uint8_t v___x_652_; 
v___x_651_ = 102;
v___x_652_ = lean_uint32_to_uint8(v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(uint8_t v_x_653_){
_start:
{
uint8_t v___x_654_; uint8_t v___x_655_; uint8_t v___x_656_; uint8_t v___x_657_; uint8_t v___y_659_; uint8_t v___x_670_; uint8_t v___x_671_; 
v___x_654_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_655_ = lean_uint8_dec_eq(v_x_653_, v___x_654_);
v___x_656_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_657_ = lean_uint8_dec_eq(v_x_653_, v___x_656_);
v___x_670_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_671_ = lean_uint8_dec_le(v___x_670_, v_x_653_);
if (v___x_671_ == 0)
{
goto v___jp_665_;
}
else
{
uint8_t v___x_672_; uint8_t v___x_673_; 
v___x_672_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_673_ = lean_uint8_dec_le(v_x_653_, v___x_672_);
if (v___x_673_ == 0)
{
goto v___jp_665_;
}
else
{
v___y_659_ = v___x_673_;
goto v___jp_658_;
}
}
v___jp_658_:
{
if (v___x_657_ == 0)
{
if (v___x_655_ == 0)
{
return v___y_659_;
}
else
{
return v___x_655_;
}
}
else
{
if (v___x_655_ == 0)
{
return v___x_657_;
}
else
{
return v___x_655_;
}
}
}
v___jp_660_:
{
uint8_t v___x_661_; uint8_t v___x_662_; 
v___x_661_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_662_ = lean_uint8_dec_le(v___x_661_, v_x_653_);
if (v___x_662_ == 0)
{
v___y_659_ = v___x_662_;
goto v___jp_658_;
}
else
{
uint8_t v___x_663_; uint8_t v___x_664_; 
v___x_663_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0);
v___x_664_ = lean_uint8_dec_le(v_x_653_, v___x_663_);
v___y_659_ = v___x_664_;
goto v___jp_658_;
}
}
v___jp_665_:
{
uint8_t v___x_666_; uint8_t v___x_667_; 
v___x_666_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_667_ = lean_uint8_dec_le(v___x_666_, v_x_653_);
if (v___x_667_ == 0)
{
goto v___jp_660_;
}
else
{
uint8_t v___x_668_; uint8_t v___x_669_; 
v___x_668_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1);
v___x_669_ = lean_uint8_dec_le(v_x_653_, v___x_668_);
if (v___x_669_ == 0)
{
goto v___jp_660_;
}
else
{
v___y_659_ = v___x_669_;
goto v___jp_658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___boxed(lean_object* v_x_674_){
_start:
{
uint8_t v_x_boxed_675_; uint8_t v_res_676_; lean_object* v_r_677_; 
v_x_boxed_675_ = lean_unbox(v_x_674_);
v_res_676_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(v_x_boxed_675_);
v_r_677_ = lean_box(v_res_676_);
return v_r_677_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1(void){
_start:
{
uint32_t v___x_679_; uint8_t v___x_680_; 
v___x_679_ = 91;
v___x_680_ = lean_uint32_to_uint8(v___x_679_);
return v___x_680_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3(void){
_start:
{
uint8_t v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1);
v___x_683_ = lean_uint8_to_nat(v___x_682_);
return v___x_683_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3);
v___x_685_ = l_Nat_reprFast(v___x_684_);
return v___x_685_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_686_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4);
v___x_687_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_688_ = lean_string_append(v___x_687_, v___x_686_);
return v___x_688_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_690_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_691_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5);
v___x_692_ = lean_string_append(v___x_691_, v___x_690_);
return v___x_692_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7);
v___x_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
return v___x_694_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10(void){
_start:
{
uint32_t v___x_696_; uint8_t v___x_697_; 
v___x_696_ = 93;
v___x_697_ = lean_uint32_to_uint8(v___x_696_);
return v___x_697_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11(void){
_start:
{
uint8_t v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10);
v___x_699_ = lean_uint8_to_nat(v___x_698_);
return v___x_699_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11);
v___x_701_ = l_Nat_reprFast(v___x_700_);
return v___x_701_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_702_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12);
v___x_703_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_704_ = lean_string_append(v___x_703_, v___x_702_);
return v___x_704_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_705_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_706_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13);
v___x_707_ = lean_string_append(v___x_706_, v___x_705_);
return v___x_707_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__15(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14);
v___x_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(lean_object* v_a_713_){
_start:
{
lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v_array_724_; lean_object* v_idx_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v_array_724_ = lean_ctor_get(v_a_713_, 0);
v_idx_725_ = lean_ctor_get(v_a_713_, 1);
v___x_726_ = lean_byte_array_size(v_array_724_);
v___x_727_ = lean_nat_dec_lt(v_idx_725_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_box(0);
v___x_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_729_, 0, v_a_713_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
return v___x_729_;
}
else
{
uint8_t v___x_730_; uint8_t v_got_731_; uint8_t v___x_732_; 
v___x_730_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1);
v_got_731_ = lean_byte_array_fget(v_array_724_, v_idx_725_);
v___x_732_ = lean_uint8_dec_eq(v_got_731_, v___x_730_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8);
v___x_734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_734_, 0, v_a_713_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
return v___x_734_;
}
else
{
lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_810_; 
lean_inc(v_idx_725_);
lean_inc_ref(v_array_724_);
v_isSharedCheck_810_ = !lean_is_exclusive(v_a_713_);
if (v_isSharedCheck_810_ == 0)
{
lean_object* v_unused_811_; lean_object* v_unused_812_; 
v_unused_811_ = lean_ctor_get(v_a_713_, 1);
lean_dec(v_unused_811_);
v_unused_812_ = lean_ctor_get(v_a_713_, 0);
lean_dec(v_unused_812_);
v___x_736_ = v_a_713_;
v_isShared_737_ = v_isSharedCheck_810_;
goto v_resetjp_735_;
}
else
{
lean_dec(v_a_713_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_810_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___f_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v___f_738_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9));
v___x_739_ = lean_unsigned_to_nat(1u);
v___x_740_ = lean_nat_add(v_idx_725_, v___x_739_);
lean_dec(v_idx_725_);
lean_inc(v___x_740_);
lean_inc_ref(v_array_724_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 1, v___x_740_);
v___x_742_ = v___x_736_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_array_724_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v___x_740_);
v___x_742_ = v_reuseFailAlloc_809_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v_snd_746_; lean_object* v_fst_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_808_; 
v___x_743_ = lean_unsigned_to_nat(256u);
v___x_744_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___x_742_);
v___x_745_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_738_, v___x_743_, v___x_744_, v___x_742_);
v_snd_746_ = lean_ctor_get(v___x_745_, 1);
v_fst_747_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_808_ == 0)
{
v___x_749_ = v___x_745_;
v_isShared_750_ = v_isSharedCheck_808_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_snd_746_);
lean_inc(v_fst_747_);
lean_dec(v___x_745_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_808_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v_fst_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_806_; 
v_fst_751_ = lean_ctor_get(v_snd_746_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v_snd_746_);
if (v_isSharedCheck_806_ == 0)
{
lean_object* v_unused_807_; 
v_unused_807_ = lean_ctor_get(v_snd_746_, 1);
lean_dec(v_unused_807_);
v___x_753_ = v_snd_746_;
v_isShared_754_ = v_isSharedCheck_806_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_fst_751_);
lean_dec(v_snd_746_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_806_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___y_756_; uint8_t v___x_790_; 
v___x_790_ = lean_nat_dec_eq(v_fst_747_, v___x_744_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; lean_object* v___y_793_; uint8_t v___x_801_; 
lean_dec_ref(v___x_742_);
v___x_791_ = lean_nat_add(v___x_740_, v_fst_747_);
lean_dec(v_fst_747_);
v___x_801_ = lean_nat_dec_le(v___x_740_, v___x_744_);
if (v___x_801_ == 0)
{
v___y_793_ = v___x_740_;
goto v___jp_792_;
}
else
{
lean_dec(v___x_740_);
v___y_793_ = v___x_744_;
goto v___jp_792_;
}
v___jp_792_:
{
uint8_t v___x_794_; 
v___x_794_ = lean_nat_dec_le(v___x_791_, v___x_726_);
if (v___x_794_ == 0)
{
lean_object* v___x_796_; 
lean_dec(v___x_791_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v___x_726_);
lean_ctor_set(v___x_749_, 0, v___y_793_);
v___x_796_ = v___x_749_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___y_793_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v___x_726_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
v___y_756_ = v___x_796_;
goto v___jp_755_;
}
}
else
{
lean_object* v___x_799_; 
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v___x_791_);
lean_ctor_set(v___x_749_, 0, v___y_793_);
v___x_799_ = v___x_749_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___y_793_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v___x_791_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
v___y_756_ = v___x_799_;
goto v___jp_755_;
}
}
}
}
else
{
lean_object* v___x_802_; lean_object* v___x_804_; 
lean_del_object(v___x_753_);
lean_dec(v_fst_751_);
lean_dec(v_fst_747_);
lean_dec(v___x_740_);
lean_dec_ref(v_array_724_);
v___x_802_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__17));
if (v_isShared_750_ == 0)
{
lean_ctor_set_tag(v___x_749_, 1);
lean_ctor_set(v___x_749_, 1, v___x_802_);
lean_ctor_set(v___x_749_, 0, v___x_742_);
v___x_804_ = v___x_749_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
v___jp_755_:
{
lean_object* v_array_757_; lean_object* v_idx_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v_array_757_ = lean_ctor_get(v_fst_751_, 0);
v_idx_758_ = lean_ctor_get(v_fst_751_, 1);
v___x_759_ = lean_byte_array_size(v_array_757_);
v___x_760_ = lean_nat_dec_lt(v_idx_758_, v___x_759_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; lean_object* v___x_763_; 
lean_dec_ref(v___y_756_);
lean_dec_ref(v_array_724_);
v___x_761_ = lean_box(0);
if (v_isShared_754_ == 0)
{
lean_ctor_set_tag(v___x_753_, 1);
lean_ctor_set(v___x_753_, 1, v___x_761_);
v___x_763_ = v___x_753_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_fst_751_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
else
{
uint8_t v___x_765_; uint8_t v_got_766_; uint8_t v___x_767_; 
v___x_765_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10);
v_got_766_ = lean_byte_array_fget(v_array_757_, v_idx_758_);
v___x_767_ = lean_uint8_dec_eq(v_got_766_, v___x_765_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_770_; 
lean_dec_ref(v___y_756_);
lean_dec_ref(v_array_724_);
v___x_768_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__15, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__15_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__15);
if (v_isShared_754_ == 0)
{
lean_ctor_set_tag(v___x_753_, 1);
lean_ctor_set(v___x_753_, 1, v___x_768_);
v___x_770_ = v___x_753_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_fst_751_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
else
{
lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_787_; 
lean_inc(v_idx_758_);
lean_inc_ref(v_array_757_);
lean_del_object(v___x_753_);
v_isSharedCheck_787_ = !lean_is_exclusive(v_fst_751_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; lean_object* v_unused_789_; 
v_unused_788_ = lean_ctor_get(v_fst_751_, 1);
lean_dec(v_unused_788_);
v_unused_789_ = lean_ctor_get(v_fst_751_, 0);
lean_dec(v_unused_789_);
v___x_773_ = v_fst_751_;
v_isShared_774_ = v_isSharedCheck_787_;
goto v_resetjp_772_;
}
else
{
lean_dec(v_fst_751_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_787_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_lower_775_; lean_object* v_upper_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_780_; 
v_lower_775_ = lean_ctor_get(v___y_756_, 0);
lean_inc(v_lower_775_);
v_upper_776_ = lean_ctor_get(v___y_756_, 1);
lean_inc(v_upper_776_);
lean_dec_ref(v___y_756_);
v___x_777_ = l_ByteArray_toByteSlice(v_array_724_, v_lower_775_, v_upper_776_);
v___x_778_ = lean_nat_add(v_idx_758_, v___x_739_);
lean_dec(v_idx_758_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v___x_778_);
v___x_780_ = v___x_773_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_array_757_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v___x_778_);
v___x_780_ = v_reuseFailAlloc_786_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; uint8_t v___x_782_; 
v___x_781_ = l_ByteSlice_toByteArray(v___x_777_);
v___x_782_ = lean_string_validate_utf8(v___x_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; 
lean_dec_ref(v___x_781_);
v___x_783_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_784_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_783_);
v___y_715_ = v___x_780_;
v___y_716_ = v___x_784_;
goto v___jp_714_;
}
else
{
lean_object* v___x_785_; 
v___x_785_ = lean_string_from_utf8_unchecked(v___x_781_);
v___y_715_ = v___x_780_;
v___y_716_ = v___x_785_;
goto v___jp_714_;
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
v___jp_714_:
{
lean_object* v___x_717_; 
v___x_717_ = lean_uv_pton_v6(v___y_716_);
if (lean_obj_tag(v___x_717_) == 1)
{
lean_object* v_val_718_; lean_object* v___x_719_; 
lean_dec_ref(v___y_716_);
v_val_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_val_718_);
lean_dec_ref_known(v___x_717_, 1);
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v___y_715_);
lean_ctor_set(v___x_719_, 1, v_val_718_);
return v___x_719_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
lean_dec(v___x_717_);
v___x_720_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0));
v___x_721_ = lean_string_append(v___x_720_, v___y_716_);
lean_dec_ref(v___y_716_);
v___x_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
v___x_723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_723_, 0, v___y_715_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
return v___x_723_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(uint8_t v_x_813_){
_start:
{
uint8_t v___x_814_; uint8_t v___x_815_; uint8_t v___x_816_; uint8_t v___x_817_; 
v___x_814_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_815_ = lean_uint8_dec_eq(v_x_813_, v___x_814_);
v___x_816_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_817_ = lean_uint8_dec_le(v___x_816_, v_x_813_);
if (v___x_817_ == 0)
{
if (v___x_815_ == 0)
{
return v___x_817_;
}
else
{
return v___x_815_;
}
}
else
{
if (v___x_815_ == 0)
{
uint8_t v___x_818_; uint8_t v___x_819_; 
v___x_818_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_819_ = lean_uint8_dec_le(v_x_813_, v___x_818_);
return v___x_819_;
}
else
{
return v___x_815_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0___boxed(lean_object* v_x_820_){
_start:
{
uint8_t v_x_boxed_821_; uint8_t v_res_822_; lean_object* v_r_823_; 
v_x_boxed_821_ = lean_unbox(v_x_820_);
v_res_822_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(v_x_boxed_821_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(lean_object* v_a_826_){
_start:
{
lean_object* v___f_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v_snd_831_; lean_object* v_fst_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_877_; 
v___f_827_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0));
v___x_828_ = lean_unsigned_to_nat(256u);
v___x_829_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_826_);
v___x_830_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_827_, v___x_828_, v___x_829_, v_a_826_);
v_snd_831_ = lean_ctor_get(v___x_830_, 1);
v_fst_832_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_877_ == 0)
{
v___x_834_ = v___x_830_;
v_isShared_835_ = v_isSharedCheck_877_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_snd_831_);
lean_inc(v_fst_832_);
lean_dec(v___x_830_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_877_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v_fst_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_875_; 
v_fst_836_ = lean_ctor_get(v_snd_831_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v_snd_831_);
if (v_isSharedCheck_875_ == 0)
{
lean_object* v_unused_876_; 
v_unused_876_ = lean_ctor_get(v_snd_831_, 1);
lean_dec(v_unused_876_);
v___x_838_ = v_snd_831_;
v_isShared_839_ = v_isSharedCheck_875_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_fst_836_);
lean_dec(v_snd_831_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_875_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___y_841_; uint8_t v___x_853_; 
v___x_853_ = lean_nat_dec_eq(v_fst_832_, v___x_829_);
if (v___x_853_ == 0)
{
lean_object* v_array_854_; lean_object* v_idx_855_; lean_object* v_lower_857_; lean_object* v_upper_858_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___y_868_; uint8_t v___x_870_; 
lean_del_object(v___x_834_);
v_array_854_ = lean_ctor_get(v_a_826_, 0);
lean_inc_ref(v_array_854_);
v_idx_855_ = lean_ctor_get(v_a_826_, 1);
lean_inc(v_idx_855_);
lean_dec_ref(v_a_826_);
v___x_865_ = lean_nat_add(v_idx_855_, v_fst_832_);
lean_dec(v_fst_832_);
v___x_866_ = lean_byte_array_size(v_array_854_);
v___x_870_ = lean_nat_dec_le(v_idx_855_, v___x_829_);
if (v___x_870_ == 0)
{
v___y_868_ = v_idx_855_;
goto v___jp_867_;
}
else
{
lean_dec(v_idx_855_);
v___y_868_ = v___x_829_;
goto v___jp_867_;
}
v___jp_856_:
{
lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_859_ = l_ByteArray_toByteSlice(v_array_854_, v_lower_857_, v_upper_858_);
v___x_860_ = l_ByteSlice_toByteArray(v___x_859_);
v___x_861_ = lean_string_validate_utf8(v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec_ref(v___x_860_);
v___x_862_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7);
v___x_863_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_862_);
v___y_841_ = v___x_863_;
goto v___jp_840_;
}
else
{
lean_object* v___x_864_; 
v___x_864_ = lean_string_from_utf8_unchecked(v___x_860_);
v___y_841_ = v___x_864_;
goto v___jp_840_;
}
}
v___jp_867_:
{
uint8_t v___x_869_; 
v___x_869_ = lean_nat_dec_le(v___x_865_, v___x_866_);
if (v___x_869_ == 0)
{
lean_dec(v___x_865_);
v_lower_857_ = v___y_868_;
v_upper_858_ = v___x_866_;
goto v___jp_856_;
}
else
{
v_lower_857_ = v___y_868_;
v_upper_858_ = v___x_865_;
goto v___jp_856_;
}
}
}
else
{
lean_object* v___x_871_; lean_object* v___x_873_; 
lean_del_object(v___x_838_);
lean_dec(v_fst_836_);
lean_dec(v_fst_832_);
v___x_871_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__17));
if (v_isShared_835_ == 0)
{
lean_ctor_set_tag(v___x_834_, 1);
lean_ctor_set(v___x_834_, 1, v___x_871_);
lean_ctor_set(v___x_834_, 0, v_a_826_);
v___x_873_ = v___x_834_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_826_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
v___jp_840_:
{
lean_object* v___x_842_; 
v___x_842_ = lean_uv_pton_v4(v___y_841_);
if (lean_obj_tag(v___x_842_) == 1)
{
lean_object* v_val_843_; lean_object* v___x_845_; 
lean_dec_ref(v___y_841_);
v_val_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_val_843_);
lean_dec_ref_known(v___x_842_, 1);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v_val_843_);
v___x_845_ = v___x_838_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_fst_836_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_val_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
else
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
lean_dec(v___x_842_);
v___x_847_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1));
v___x_848_ = lean_string_append(v___x_847_, v___y_841_);
lean_dec_ref(v___y_841_);
v___x_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
if (v_isShared_839_ == 0)
{
lean_ctor_set_tag(v___x_838_, 1);
lean_ctor_set(v___x_838_, 1, v___x_849_);
v___x_851_ = v___x_838_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_fst_836_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(lean_object* v_s_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0));
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___boxed(lean_object* v_s_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(v_s_882_);
lean_dec_ref(v_s_882_);
return v_res_883_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(uint8_t v_x_884_){
_start:
{
uint8_t v___y_886_; uint8_t v___x_901_; uint8_t v___x_902_; 
v___x_901_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_902_ = lean_uint8_dec_le(v___x_901_, v_x_884_);
if (v___x_902_ == 0)
{
goto v___jp_896_;
}
else
{
uint8_t v___x_903_; uint8_t v___x_904_; 
v___x_903_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_904_ = lean_uint8_dec_le(v_x_884_, v___x_903_);
if (v___x_904_ == 0)
{
goto v___jp_896_;
}
else
{
v___y_886_ = v___x_904_;
goto v___jp_885_;
}
}
v___jp_885_:
{
uint8_t v___x_887_; uint8_t v___x_888_; 
v___x_887_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_888_ = lean_uint8_dec_eq(v_x_884_, v___x_887_);
if (v___x_888_ == 0)
{
if (v___y_886_ == 0)
{
uint8_t v___x_889_; uint8_t v___x_890_; 
v___x_889_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_890_ = lean_uint8_dec_eq(v_x_884_, v___x_889_);
return v___x_890_;
}
else
{
return v___y_886_;
}
}
else
{
if (v___y_886_ == 0)
{
return v___x_888_;
}
else
{
return v___y_886_;
}
}
}
v___jp_891_:
{
uint8_t v___x_892_; uint8_t v___x_893_; 
v___x_892_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_893_ = lean_uint8_dec_le(v___x_892_, v_x_884_);
if (v___x_893_ == 0)
{
v___y_886_ = v___x_893_;
goto v___jp_885_;
}
else
{
uint8_t v___x_894_; uint8_t v___x_895_; 
v___x_894_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_895_ = lean_uint8_dec_le(v_x_884_, v___x_894_);
v___y_886_ = v___x_895_;
goto v___jp_885_;
}
}
v___jp_896_:
{
uint8_t v___x_897_; uint8_t v___x_898_; 
v___x_897_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_898_ = lean_uint8_dec_le(v___x_897_, v_x_884_);
if (v___x_898_ == 0)
{
goto v___jp_891_;
}
else
{
uint8_t v___x_899_; uint8_t v___x_900_; 
v___x_899_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_900_ = lean_uint8_dec_le(v_x_884_, v___x_899_);
if (v___x_900_ == 0)
{
goto v___jp_891_;
}
else
{
v___y_886_ = v___x_900_;
goto v___jp_885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed(lean_object* v_x_905_){
_start:
{
uint8_t v_x_boxed_906_; uint8_t v_res_907_; lean_object* v_r_908_; 
v_x_boxed_906_ = lean_unbox(v_x_905_);
v_res_907_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(v_x_boxed_906_);
v_r_908_ = lean_box(v_res_907_);
return v_r_908_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1___redArg(lean_object* v___x_909_, lean_object* v_a_910_, uint8_t v_b_911_){
_start:
{
if (lean_obj_tag(v_a_910_) == 0)
{
lean_object* v_currPos_912_; lean_object* v_searcher_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_933_; 
v_currPos_912_ = lean_ctor_get(v_a_910_, 0);
v_searcher_913_ = lean_ctor_get(v_a_910_, 1);
v_isSharedCheck_933_ = !lean_is_exclusive(v_a_910_);
if (v_isSharedCheck_933_ == 0)
{
v___x_915_ = v_a_910_;
v_isShared_916_ = v_isSharedCheck_933_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_searcher_913_);
lean_inc(v_currPos_912_);
lean_dec(v_a_910_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_933_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v_str_917_; lean_object* v_startInclusive_918_; lean_object* v_endExclusive_919_; uint8_t v___x_920_; lean_object* v___x_921_; uint8_t v_decide_922_; 
v_str_917_ = lean_ctor_get(v___x_909_, 0);
v_startInclusive_918_ = lean_ctor_get(v___x_909_, 1);
v_endExclusive_919_ = lean_ctor_get(v___x_909_, 2);
v___x_920_ = 0;
v___x_921_ = lean_nat_sub(v_endExclusive_919_, v_startInclusive_918_);
v_decide_922_ = lean_nat_dec_eq(v_searcher_913_, v___x_921_);
lean_dec(v___x_921_);
if (v_decide_922_ == 0)
{
uint32_t v___x_923_; lean_object* v___x_924_; uint32_t v___x_925_; uint8_t v___x_926_; 
v___x_923_ = 46;
v___x_924_ = lean_nat_add(v_startInclusive_918_, v_searcher_913_);
lean_dec(v_searcher_913_);
v___x_925_ = lean_string_utf8_get_fast(v_str_917_, v___x_924_);
v___x_926_ = lean_uint32_dec_eq(v___x_925_, v___x_923_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_927_ = lean_string_utf8_next_fast(v_str_917_, v___x_924_);
lean_dec(v___x_924_);
v___x_928_ = lean_nat_sub(v___x_927_, v_startInclusive_918_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 1, v___x_928_);
v___x_930_ = v___x_915_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_currPos_912_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v___x_928_);
v___x_930_ = v_reuseFailAlloc_932_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
v_a_910_ = v___x_930_;
goto _start;
}
}
else
{
lean_dec(v___x_924_);
lean_del_object(v___x_915_);
lean_dec(v_currPos_912_);
return v___x_920_;
}
}
else
{
lean_del_object(v___x_915_);
lean_dec(v_searcher_913_);
lean_dec(v_currPos_912_);
return v___x_920_;
}
}
}
else
{
return v_b_911_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1___redArg___boxed(lean_object* v___x_934_, lean_object* v_a_935_, lean_object* v_b_936_){
_start:
{
uint8_t v_b_boxed_937_; uint8_t v_res_938_; lean_object* v_r_939_; 
v_b_boxed_937_ = lean_unbox(v_b_936_);
v_res_938_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1___redArg(v___x_934_, v_a_935_, v_b_boxed_937_);
lean_dec_ref(v___x_934_);
v_r_939_ = lean_box(v_res_938_);
return v_r_939_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(lean_object* v___x_940_, lean_object* v___x_941_, lean_object* v___x_942_, lean_object* v_a_943_, uint8_t v_b_944_){
_start:
{
if (lean_obj_tag(v_a_943_) == 0)
{
lean_object* v_currPos_945_; lean_object* v_searcher_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_966_; 
v_currPos_945_ = lean_ctor_get(v_a_943_, 0);
v_searcher_946_ = lean_ctor_get(v_a_943_, 1);
v_isSharedCheck_966_ = !lean_is_exclusive(v_a_943_);
if (v_isSharedCheck_966_ == 0)
{
v___x_948_ = v_a_943_;
v_isShared_949_ = v_isSharedCheck_966_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_searcher_946_);
lean_inc(v_currPos_945_);
lean_dec(v_a_943_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_966_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v_str_950_; lean_object* v_startInclusive_951_; lean_object* v_endExclusive_952_; uint8_t v___x_953_; lean_object* v___x_954_; uint8_t v_decide_955_; 
v_str_950_ = lean_ctor_get(v___x_941_, 0);
v_startInclusive_951_ = lean_ctor_get(v___x_941_, 1);
v_endExclusive_952_ = lean_ctor_get(v___x_941_, 2);
v___x_953_ = 0;
v___x_954_ = lean_nat_sub(v_endExclusive_952_, v_startInclusive_951_);
v_decide_955_ = lean_nat_dec_eq(v_searcher_946_, v___x_954_);
lean_dec(v___x_954_);
if (v_decide_955_ == 0)
{
lean_object* v___x_956_; uint32_t v___x_957_; uint32_t v___x_958_; uint8_t v___x_959_; 
v___x_956_ = lean_nat_add(v_startInclusive_951_, v_searcher_946_);
lean_dec(v_searcher_946_);
v___x_957_ = lean_string_utf8_get_fast(v_str_950_, v___x_956_);
v___x_958_ = 46;
v___x_959_ = lean_uint32_dec_eq(v___x_957_, v___x_958_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_960_ = lean_string_utf8_next_fast(v_str_950_, v___x_956_);
lean_dec(v___x_956_);
v___x_961_ = lean_nat_sub(v___x_960_, v_startInclusive_951_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v___x_961_);
v___x_963_ = v___x_948_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_currPos_945_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v___x_961_);
v___x_963_ = v_reuseFailAlloc_965_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
uint8_t v___x_964_; 
v___x_964_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1___redArg(v___x_941_, v___x_963_, v_b_944_);
return v___x_964_;
}
}
else
{
lean_dec(v___x_956_);
lean_del_object(v___x_948_);
lean_dec(v_currPos_945_);
return v___x_953_;
}
}
else
{
lean_del_object(v___x_948_);
lean_dec(v_searcher_946_);
lean_dec(v_currPos_945_);
return v___x_953_;
}
}
}
else
{
return v_b_944_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg___boxed(lean_object* v___x_967_, lean_object* v___x_968_, lean_object* v___x_969_, lean_object* v_a_970_, lean_object* v_b_971_){
_start:
{
uint8_t v_b_boxed_972_; uint8_t v_res_973_; lean_object* v_r_974_; 
v_b_boxed_972_ = lean_unbox(v_b_971_);
v_res_973_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_967_, v___x_968_, v___x_969_, v_a_970_, v_b_boxed_972_);
lean_dec(v___x_969_);
lean_dec_ref(v___x_968_);
lean_dec_ref(v___x_967_);
v_r_974_ = lean_box(v_res_973_);
return v_r_974_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___redArg(uint8_t v___x_975_, lean_object* v___x_976_, lean_object* v___x_977_, lean_object* v___x_978_, lean_object* v_a_979_, uint8_t v_b_980_){
_start:
{
lean_object* v_it_982_; lean_object* v_startInclusive_983_; lean_object* v_endExclusive_984_; 
if (lean_obj_tag(v_a_979_) == 0)
{
lean_object* v_currPos_988_; lean_object* v_searcher_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1018_; 
v_currPos_988_ = lean_ctor_get(v_a_979_, 0);
v_searcher_989_ = lean_ctor_get(v_a_979_, 1);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_a_979_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_991_ = v_a_979_;
v_isShared_992_ = v_isSharedCheck_1018_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_searcher_989_);
lean_inc(v_currPos_988_);
lean_dec(v_a_979_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1018_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v_str_993_; lean_object* v_startInclusive_994_; lean_object* v_endExclusive_995_; lean_object* v___x_996_; uint8_t v_decide_997_; 
v_str_993_ = lean_ctor_get(v___x_977_, 0);
v_startInclusive_994_ = lean_ctor_get(v___x_977_, 1);
v_endExclusive_995_ = lean_ctor_get(v___x_977_, 2);
v___x_996_ = lean_nat_sub(v_endExclusive_995_, v_startInclusive_994_);
v_decide_997_ = lean_nat_dec_eq(v_searcher_989_, v___x_996_);
lean_dec(v___x_996_);
if (v_decide_997_ == 0)
{
uint32_t v___x_998_; lean_object* v___x_999_; uint32_t v___x_1000_; uint8_t v___x_1001_; 
v___x_998_ = 46;
v___x_999_ = lean_nat_add(v_startInclusive_994_, v_searcher_989_);
v___x_1000_ = lean_string_utf8_get_fast(v_str_993_, v___x_999_);
v___x_1001_ = lean_uint32_dec_eq(v___x_1000_, v___x_998_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
lean_dec(v_searcher_989_);
v___x_1002_ = lean_string_utf8_next_fast(v_str_993_, v___x_999_);
lean_dec(v___x_999_);
v___x_1003_ = lean_nat_sub(v___x_1002_, v_startInclusive_994_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 1, v___x_1003_);
v___x_1005_ = v___x_991_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_currPos_988_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
v_a_979_ = v___x_1005_;
goto _start;
}
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v_slice_1011_; lean_object* v_nextIt_1013_; 
v___x_1008_ = lean_string_utf8_next_fast(v_str_993_, v___x_999_);
v___x_1009_ = lean_nat_sub(v___x_1008_, v___x_999_);
lean_dec(v___x_999_);
v___x_1010_ = lean_nat_add(v_searcher_989_, v___x_1009_);
lean_dec(v___x_1009_);
v_slice_1011_ = l_String_Slice_subslice_x21(v___x_977_, v_currPos_988_, v_searcher_989_);
lean_inc(v___x_1010_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 1, v___x_1010_);
lean_ctor_set(v___x_991_, 0, v___x_1010_);
v_nextIt_1013_ = v___x_991_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v___x_1010_);
v_nextIt_1013_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v_startInclusive_1014_; lean_object* v_endExclusive_1015_; 
v_startInclusive_1014_ = lean_ctor_get(v_slice_1011_, 0);
lean_inc(v_startInclusive_1014_);
v_endExclusive_1015_ = lean_ctor_get(v_slice_1011_, 1);
lean_inc(v_endExclusive_1015_);
lean_dec_ref(v_slice_1011_);
v_it_982_ = v_nextIt_1013_;
v_startInclusive_983_ = v_startInclusive_1014_;
v_endExclusive_984_ = v_endExclusive_1015_;
goto v___jp_981_;
}
}
}
else
{
lean_object* v___x_1017_; 
lean_del_object(v___x_991_);
lean_dec(v_searcher_989_);
v___x_1017_ = lean_box(1);
lean_inc(v___x_978_);
v_it_982_ = v___x_1017_;
v_startInclusive_983_ = v_currPos_988_;
v_endExclusive_984_ = v___x_978_;
goto v___jp_981_;
}
}
}
else
{
lean_dec(v___x_978_);
return v_b_980_;
}
v___jp_981_:
{
lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_985_ = lean_string_utf8_extract_fast(v___x_976_, v_startInclusive_983_, v_endExclusive_984_);
lean_dec(v_endExclusive_984_);
lean_dec(v_startInclusive_983_);
v___x_986_ = l_Std_Http_URI_isValidDomainLabel(v___x_985_);
if (v___x_986_ == 0)
{
lean_dec(v_it_982_);
lean_dec(v___x_978_);
return v___x_986_;
}
else
{
{
lean_object* _tmp_4 = v_it_982_;
uint8_t _tmp_5 = v___x_975_;
v_a_979_ = _tmp_4;
v_b_980_ = _tmp_5;
}
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___redArg___boxed(lean_object* v___x_1019_, lean_object* v___x_1020_, lean_object* v___x_1021_, lean_object* v___x_1022_, lean_object* v_a_1023_, lean_object* v_b_1024_){
_start:
{
uint8_t v___x_10841__boxed_1025_; uint8_t v_b_boxed_1026_; uint8_t v_res_1027_; lean_object* v_r_1028_; 
v___x_10841__boxed_1025_ = lean_unbox(v___x_1019_);
v_b_boxed_1026_ = lean_unbox(v_b_1024_);
v_res_1027_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___redArg(v___x_10841__boxed_1025_, v___x_1020_, v___x_1021_, v___x_1022_, v_a_1023_, v_b_boxed_1026_);
lean_dec_ref(v___x_1021_);
lean_dec_ref(v___x_1020_);
v_r_1028_ = lean_box(v_res_1027_);
return v_r_1028_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(uint8_t v___x_1029_, lean_object* v___x_1030_, lean_object* v___x_1031_, lean_object* v___x_1032_, lean_object* v_a_1033_, uint8_t v_b_1034_){
_start:
{
lean_object* v_it_1036_; lean_object* v_startInclusive_1037_; lean_object* v_endExclusive_1038_; 
if (lean_obj_tag(v_a_1033_) == 0)
{
lean_object* v_currPos_1042_; lean_object* v_searcher_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1072_; 
v_currPos_1042_ = lean_ctor_get(v_a_1033_, 0);
v_searcher_1043_ = lean_ctor_get(v_a_1033_, 1);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_a_1033_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1045_ = v_a_1033_;
v_isShared_1046_ = v_isSharedCheck_1072_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_searcher_1043_);
lean_inc(v_currPos_1042_);
lean_dec(v_a_1033_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1072_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v_str_1047_; lean_object* v_startInclusive_1048_; lean_object* v_endExclusive_1049_; lean_object* v___x_1050_; uint8_t v_decide_1051_; 
v_str_1047_ = lean_ctor_get(v___x_1031_, 0);
v_startInclusive_1048_ = lean_ctor_get(v___x_1031_, 1);
v_endExclusive_1049_ = lean_ctor_get(v___x_1031_, 2);
v___x_1050_ = lean_nat_sub(v_endExclusive_1049_, v_startInclusive_1048_);
v_decide_1051_ = lean_nat_dec_eq(v_searcher_1043_, v___x_1050_);
lean_dec(v___x_1050_);
if (v_decide_1051_ == 0)
{
lean_object* v___x_1052_; uint32_t v___x_1053_; uint32_t v___x_1054_; uint8_t v___x_1055_; 
v___x_1052_ = lean_nat_add(v_startInclusive_1048_, v_searcher_1043_);
v___x_1053_ = lean_string_utf8_get_fast(v_str_1047_, v___x_1052_);
v___x_1054_ = 46;
v___x_1055_ = lean_uint32_dec_eq(v___x_1053_, v___x_1054_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
lean_dec(v_searcher_1043_);
v___x_1056_ = lean_string_utf8_next_fast(v_str_1047_, v___x_1052_);
lean_dec(v___x_1052_);
v___x_1057_ = lean_nat_sub(v___x_1056_, v_startInclusive_1048_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 1, v___x_1057_);
v___x_1059_ = v___x_1045_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_currPos_1042_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
uint8_t v___x_1060_; 
v___x_1060_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___redArg(v___x_1029_, v___x_1030_, v___x_1031_, v___x_1032_, v___x_1059_, v_b_1034_);
return v___x_1060_;
}
}
else
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v_slice_1065_; lean_object* v_nextIt_1067_; 
v___x_1062_ = lean_string_utf8_next_fast(v_str_1047_, v___x_1052_);
v___x_1063_ = lean_nat_sub(v___x_1062_, v___x_1052_);
lean_dec(v___x_1052_);
v___x_1064_ = lean_nat_add(v_searcher_1043_, v___x_1063_);
lean_dec(v___x_1063_);
v_slice_1065_ = l_String_Slice_subslice_x21(v___x_1031_, v_currPos_1042_, v_searcher_1043_);
lean_inc(v___x_1064_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 1, v___x_1064_);
lean_ctor_set(v___x_1045_, 0, v___x_1064_);
v_nextIt_1067_ = v___x_1045_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v___x_1064_);
v_nextIt_1067_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v_startInclusive_1068_; lean_object* v_endExclusive_1069_; 
v_startInclusive_1068_ = lean_ctor_get(v_slice_1065_, 0);
lean_inc(v_startInclusive_1068_);
v_endExclusive_1069_ = lean_ctor_get(v_slice_1065_, 1);
lean_inc(v_endExclusive_1069_);
lean_dec_ref(v_slice_1065_);
v_it_1036_ = v_nextIt_1067_;
v_startInclusive_1037_ = v_startInclusive_1068_;
v_endExclusive_1038_ = v_endExclusive_1069_;
goto v___jp_1035_;
}
}
}
else
{
lean_object* v___x_1071_; 
lean_del_object(v___x_1045_);
lean_dec(v_searcher_1043_);
v___x_1071_ = lean_box(1);
lean_inc(v___x_1032_);
v_it_1036_ = v___x_1071_;
v_startInclusive_1037_ = v_currPos_1042_;
v_endExclusive_1038_ = v___x_1032_;
goto v___jp_1035_;
}
}
}
else
{
lean_dec(v___x_1032_);
return v_b_1034_;
}
v___jp_1035_:
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = lean_string_utf8_extract_fast(v___x_1030_, v_startInclusive_1037_, v_endExclusive_1038_);
lean_dec(v_endExclusive_1038_);
lean_dec(v_startInclusive_1037_);
v___x_1040_ = l_Std_Http_URI_isValidDomainLabel(v___x_1039_);
if (v___x_1040_ == 0)
{
lean_dec(v_it_1036_);
lean_dec(v___x_1032_);
return v___x_1040_;
}
else
{
uint8_t v___x_1041_; 
v___x_1041_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___redArg(v___x_1029_, v___x_1030_, v___x_1031_, v___x_1032_, v_it_1036_, v___x_1029_);
return v___x_1041_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg___boxed(lean_object* v___x_1073_, lean_object* v___x_1074_, lean_object* v___x_1075_, lean_object* v___x_1076_, lean_object* v_a_1077_, lean_object* v_b_1078_){
_start:
{
uint8_t v___x_10911__boxed_1079_; uint8_t v_b_boxed_1080_; uint8_t v_res_1081_; lean_object* v_r_1082_; 
v___x_10911__boxed_1079_ = lean_unbox(v___x_1073_);
v_b_boxed_1080_ = lean_unbox(v_b_1078_);
v_res_1081_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_10911__boxed_1079_, v___x_1074_, v___x_1075_, v___x_1076_, v_a_1077_, v_b_boxed_1080_);
lean_dec_ref(v___x_1075_);
lean_dec_ref(v___x_1074_);
v_r_1082_ = lean_box(v_res_1081_);
return v_r_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(lean_object* v_config_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v___y_1091_; lean_object* v___y_1092_; uint8_t v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; uint8_t v___y_1102_; uint8_t v___y_1106_; uint8_t v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; uint8_t v___y_1113_; uint8_t v___y_1116_; uint8_t v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; uint8_t v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; uint8_t v___y_1124_; uint8_t v___y_1126_; uint8_t v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; uint8_t v___y_1135_; uint8_t v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v_lower_1145_; lean_object* v_upper_1146_; uint8_t v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v_array_1167_; lean_object* v_idx_1168_; lean_object* v___f_1169_; lean_object* v___y_1171_; lean_object* v_pos_1194_; lean_object* v_pos_1218_; lean_object* v_res_1219_; lean_object* v_pos_1221_; lean_object* v_res_1222_; lean_object* v___x_1230_; uint8_t v___x_1231_; 
v_array_1167_ = lean_ctor_get(v_a_1089_, 0);
v_idx_1168_ = lean_ctor_get(v_a_1089_, 1);
v___f_1169_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3));
v___x_1230_ = lean_byte_array_size(v_array_1167_);
v___x_1231_ = lean_nat_dec_lt(v_idx_1168_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; 
lean_inc(v_idx_1168_);
lean_inc_ref(v_array_1167_);
v___x_1232_ = lean_box(0);
v_pos_1221_ = v_a_1089_;
v_res_1222_ = v___x_1232_;
goto v___jp_1220_;
}
else
{
uint8_t v___x_1233_; uint8_t v___x_1234_; uint8_t v___x_1235_; 
v___x_1233_ = lean_byte_array_fget(v_array_1167_, v_idx_1168_);
v___x_1234_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1);
v___x_1235_ = lean_uint8_dec_eq(v___x_1233_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; 
lean_inc(v_idx_1168_);
lean_inc_ref(v_array_1167_);
v___x_1236_ = lean_box(0);
v_pos_1221_ = v_a_1089_;
v_res_1222_ = v___x_1236_;
goto v___jp_1220_;
}
else
{
lean_object* v___x_1237_; 
v___x_1237_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(v_a_1089_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_pos_1238_; lean_object* v_res_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1247_; 
v_pos_1238_ = lean_ctor_get(v___x_1237_, 0);
v_res_1239_ = lean_ctor_get(v___x_1237_, 1);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1241_ = v___x_1237_;
v_isShared_1242_ = v_isSharedCheck_1247_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_res_1239_);
lean_inc(v_pos_1238_);
lean_dec(v___x_1237_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1247_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; lean_object* v___x_1245_; 
v___x_1243_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1243_, 0, v_res_1239_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 1, v___x_1243_);
v___x_1245_ = v___x_1241_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_pos_1238_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
else
{
lean_object* v_pos_1248_; lean_object* v_err_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
v_pos_1248_ = lean_ctor_get(v___x_1237_, 0);
v_err_1249_ = lean_ctor_get(v___x_1237_, 1);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1237_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_err_1249_);
lean_inc(v_pos_1248_);
lean_dec(v___x_1237_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_pos_1248_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_err_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
}
v___jp_1090_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1093_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0));
v___x_1094_ = lean_string_append(v___x_1093_, v___y_1092_);
lean_dec_ref(v___y_1092_);
v___x_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
v___x_1096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___y_1091_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
return v___x_1096_;
}
v___jp_1097_:
{
if (v___y_1098_ == 0)
{
lean_dec_ref(v___y_1099_);
v___y_1091_ = v___y_1100_;
v___y_1092_ = v___y_1101_;
goto v___jp_1090_;
}
else
{
if (v___y_1102_ == 0)
{
lean_dec_ref(v___y_1099_);
v___y_1091_ = v___y_1100_;
v___y_1092_ = v___y_1101_;
goto v___jp_1090_;
}
else
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_dec_ref(v___y_1101_);
v___x_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1103_, 0, v___y_1099_);
v___x_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___y_1100_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
return v___x_1104_;
}
}
}
v___jp_1105_:
{
uint8_t v___x_1114_; 
v___x_1114_ = lean_nat_dec_eq(v___y_1109_, v___y_1111_);
lean_dec(v___y_1111_);
lean_dec(v___y_1109_);
if (v___x_1114_ == 0)
{
v___y_1098_ = v___y_1113_;
v___y_1099_ = v___y_1108_;
v___y_1100_ = v___y_1110_;
v___y_1101_ = v___y_1112_;
v___y_1102_ = v___y_1106_;
goto v___jp_1097_;
}
else
{
v___y_1098_ = v___y_1113_;
v___y_1099_ = v___y_1108_;
v___y_1100_ = v___y_1110_;
v___y_1101_ = v___y_1112_;
v___y_1102_ = v___y_1107_;
goto v___jp_1097_;
}
}
v___jp_1115_:
{
if (v___y_1120_ == 0)
{
v___y_1106_ = v___y_1116_;
v___y_1107_ = v___y_1117_;
v___y_1108_ = v___y_1118_;
v___y_1109_ = v___y_1119_;
v___y_1110_ = v___y_1121_;
v___y_1111_ = v___y_1122_;
v___y_1112_ = v___y_1123_;
v___y_1113_ = v___y_1120_;
goto v___jp_1105_;
}
else
{
v___y_1106_ = v___y_1116_;
v___y_1107_ = v___y_1117_;
v___y_1108_ = v___y_1118_;
v___y_1109_ = v___y_1119_;
v___y_1110_ = v___y_1121_;
v___y_1111_ = v___y_1122_;
v___y_1112_ = v___y_1123_;
v___y_1113_ = v___y_1124_;
goto v___jp_1105_;
}
}
v___jp_1125_:
{
uint8_t v___x_1136_; 
lean_inc(v___y_1131_);
v___x_1136_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___y_1126_, v___y_1130_, v___y_1128_, v___y_1131_, v___y_1129_, v___y_1126_);
lean_dec_ref(v___y_1128_);
if (v___x_1136_ == 0)
{
v___y_1116_ = v___y_1126_;
v___y_1117_ = v___y_1127_;
v___y_1118_ = v___y_1130_;
v___y_1119_ = v___y_1131_;
v___y_1120_ = v___y_1135_;
v___y_1121_ = v___y_1132_;
v___y_1122_ = v___y_1133_;
v___y_1123_ = v___y_1134_;
v___y_1124_ = v___x_1136_;
goto v___jp_1115_;
}
else
{
lean_object* v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1137_ = lean_string_length(v___y_1130_);
v___x_1138_ = lean_unsigned_to_nat(255u);
v___x_1139_ = lean_nat_dec_le(v___x_1137_, v___x_1138_);
v___y_1116_ = v___y_1126_;
v___y_1117_ = v___y_1127_;
v___y_1118_ = v___y_1130_;
v___y_1119_ = v___y_1131_;
v___y_1120_ = v___y_1135_;
v___y_1121_ = v___y_1132_;
v___y_1122_ = v___y_1133_;
v___y_1123_ = v___y_1134_;
v___y_1124_ = v___x_1139_;
goto v___jp_1115_;
}
}
v___jp_1140_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1147_ = l_ByteArray_toByteSlice(v___y_1142_, v_lower_1145_, v_upper_1146_);
v___x_1148_ = l_ByteSlice_toByteArray(v___x_1147_);
v___x_1149_ = lean_string_validate_utf8(v___x_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_dec_ref(v___x_1148_);
lean_dec(v___y_1144_);
v___x_1150_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2));
v___x_1151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___y_1143_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
return v___x_1151_;
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; 
v___x_1152_ = lean_string_from_utf8_unchecked(v___x_1148_);
lean_inc_n(v___y_1144_, 2);
lean_inc_ref(v___x_1152_);
v___x_1153_ = l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___x_1152_, v___y_1144_);
v___x_1154_ = lean_string_utf8_byte_size(v___x_1153_);
lean_inc_ref(v___x_1153_);
v___x_1155_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___y_1144_);
lean_ctor_set(v___x_1155_, 2, v___x_1154_);
v___x_1156_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(v___x_1155_);
lean_inc(v___x_1156_);
v___x_1157_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_1153_, v___x_1155_, v___x_1154_, v___x_1156_, v___x_1149_);
if (v___x_1157_ == 0)
{
v___y_1126_ = v___x_1149_;
v___y_1127_ = v___y_1141_;
v___y_1128_ = v___x_1155_;
v___y_1129_ = v___x_1156_;
v___y_1130_ = v___x_1153_;
v___y_1131_ = v___x_1154_;
v___y_1132_ = v___y_1143_;
v___y_1133_ = v___y_1144_;
v___y_1134_ = v___x_1152_;
v___y_1135_ = v___x_1149_;
goto v___jp_1125_;
}
else
{
v___y_1126_ = v___x_1149_;
v___y_1127_ = v___y_1141_;
v___y_1128_ = v___x_1155_;
v___y_1129_ = v___x_1156_;
v___y_1130_ = v___x_1153_;
v___y_1131_ = v___x_1154_;
v___y_1132_ = v___y_1143_;
v___y_1133_ = v___y_1144_;
v___y_1134_ = v___x_1152_;
v___y_1135_ = v___y_1141_;
goto v___jp_1125_;
}
}
}
v___jp_1158_:
{
uint8_t v___x_1166_; 
v___x_1166_ = lean_nat_dec_le(v___y_1162_, v___y_1161_);
if (v___x_1166_ == 0)
{
lean_dec(v___y_1162_);
v___y_1141_ = v___y_1159_;
v___y_1142_ = v___y_1160_;
v___y_1143_ = v___y_1163_;
v___y_1144_ = v___y_1164_;
v_lower_1145_ = v___y_1165_;
v_upper_1146_ = v___y_1161_;
goto v___jp_1140_;
}
else
{
lean_dec(v___y_1161_);
v___y_1141_ = v___y_1159_;
v___y_1142_ = v___y_1160_;
v___y_1143_ = v___y_1163_;
v___y_1144_ = v___y_1164_;
v_lower_1145_ = v___y_1165_;
v_upper_1146_ = v___y_1162_;
goto v___jp_1140_;
}
}
v___jp_1170_:
{
lean_object* v_maxHostLength_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v_snd_1175_; lean_object* v_fst_1176_; lean_object* v_fst_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1191_; 
v_maxHostLength_1172_ = lean_ctor_get(v_config_1088_, 1);
v___x_1173_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___y_1171_);
v___x_1174_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1169_, v_maxHostLength_1172_, v___x_1173_, v___y_1171_);
v_snd_1175_ = lean_ctor_get(v___x_1174_, 1);
lean_inc(v_snd_1175_);
v_fst_1176_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_fst_1176_);
lean_dec_ref(v___x_1174_);
v_fst_1177_ = lean_ctor_get(v_snd_1175_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_snd_1175_);
if (v_isSharedCheck_1191_ == 0)
{
lean_object* v_unused_1192_; 
v_unused_1192_ = lean_ctor_get(v_snd_1175_, 1);
lean_dec(v_unused_1192_);
v___x_1179_ = v_snd_1175_;
v_isShared_1180_ = v_isSharedCheck_1191_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_fst_1177_);
lean_dec(v_snd_1175_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1191_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
uint8_t v___x_1181_; 
v___x_1181_ = lean_nat_dec_eq(v_fst_1176_, v___x_1173_);
if (v___x_1181_ == 0)
{
lean_object* v_array_1182_; lean_object* v_idx_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
lean_del_object(v___x_1179_);
v_array_1182_ = lean_ctor_get(v___y_1171_, 0);
lean_inc_ref(v_array_1182_);
v_idx_1183_ = lean_ctor_get(v___y_1171_, 1);
lean_inc(v_idx_1183_);
lean_dec_ref(v___y_1171_);
v___x_1184_ = lean_nat_add(v_idx_1183_, v_fst_1176_);
lean_dec(v_fst_1176_);
v___x_1185_ = lean_byte_array_size(v_array_1182_);
v___x_1186_ = lean_nat_dec_le(v_idx_1183_, v___x_1173_);
if (v___x_1186_ == 0)
{
v___y_1159_ = v___x_1181_;
v___y_1160_ = v_array_1182_;
v___y_1161_ = v___x_1185_;
v___y_1162_ = v___x_1184_;
v___y_1163_ = v_fst_1177_;
v___y_1164_ = v___x_1173_;
v___y_1165_ = v_idx_1183_;
goto v___jp_1158_;
}
else
{
lean_dec(v_idx_1183_);
v___y_1159_ = v___x_1181_;
v___y_1160_ = v_array_1182_;
v___y_1161_ = v___x_1185_;
v___y_1162_ = v___x_1184_;
v___y_1163_ = v_fst_1177_;
v___y_1164_ = v___x_1173_;
v___y_1165_ = v___x_1173_;
goto v___jp_1158_;
}
}
else
{
lean_object* v___x_1187_; lean_object* v___x_1189_; 
lean_dec(v_fst_1177_);
lean_dec(v_fst_1176_);
v___x_1187_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__17));
if (v_isShared_1180_ == 0)
{
lean_ctor_set_tag(v___x_1179_, 1);
lean_ctor_set(v___x_1179_, 1, v___x_1187_);
lean_ctor_set(v___x_1179_, 0, v___y_1171_);
v___x_1189_ = v___x_1179_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___y_1171_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
v___jp_1193_:
{
lean_object* v___x_1195_; 
lean_inc_ref(v_pos_1194_);
v___x_1195_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(v_pos_1194_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_pos_1196_; lean_object* v_res_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1205_; 
lean_dec_ref(v_pos_1194_);
v_pos_1196_ = lean_ctor_get(v___x_1195_, 0);
v_res_1197_ = lean_ctor_get(v___x_1195_, 1);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1199_ = v___x_1195_;
v_isShared_1200_ = v_isSharedCheck_1205_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_res_1197_);
lean_inc(v_pos_1196_);
lean_dec(v___x_1195_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1205_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1201_, 0, v_res_1197_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 1, v___x_1201_);
v___x_1203_ = v___x_1199_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_pos_1196_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
else
{
lean_object* v_err_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1215_; 
v_err_1206_ = lean_ctor_get(v___x_1195_, 1);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; 
v_unused_1216_ = lean_ctor_get(v___x_1195_, 0);
lean_dec(v_unused_1216_);
v___x_1208_ = v___x_1195_;
v_isShared_1209_ = v_isSharedCheck_1215_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_err_1206_);
lean_dec(v___x_1195_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1215_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v_idx_1210_; uint8_t v___x_1211_; 
v_idx_1210_ = lean_ctor_get(v_pos_1194_, 1);
v___x_1211_ = lean_nat_dec_eq(v_idx_1210_, v_idx_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1213_; 
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v_pos_1194_);
v___x_1213_ = v___x_1208_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_pos_1194_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_err_1206_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
else
{
lean_del_object(v___x_1208_);
lean_dec(v_err_1206_);
v___y_1171_ = v_pos_1194_;
goto v___jp_1170_;
}
}
}
}
v___jp_1217_:
{
v___y_1171_ = v_pos_1218_;
goto v___jp_1170_;
}
v___jp_1220_:
{
lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = lean_byte_array_size(v_array_1167_);
v___x_1224_ = lean_nat_dec_lt(v_idx_1168_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_dec(v_idx_1168_);
lean_dec_ref(v_array_1167_);
v_pos_1218_ = v_pos_1221_;
v_res_1219_ = v_res_1222_;
goto v___jp_1217_;
}
else
{
uint8_t v___x_1225_; uint8_t v___x_1226_; uint8_t v___x_1227_; 
v___x_1225_ = lean_byte_array_fget(v_array_1167_, v_idx_1168_);
lean_dec(v_idx_1168_);
lean_dec_ref(v_array_1167_);
v___x_1226_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_1227_ = lean_uint8_dec_le(v___x_1226_, v___x_1225_);
if (v___x_1227_ == 0)
{
v_pos_1218_ = v_pos_1221_;
v_res_1219_ = v_res_1222_;
goto v___jp_1217_;
}
else
{
uint8_t v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_1229_ = lean_uint8_dec_le(v___x_1225_, v___x_1228_);
if (v___x_1229_ == 0)
{
v_pos_1218_ = v_pos_1221_;
v_res_1219_ = v_res_1222_;
goto v___jp_1217_;
}
else
{
v_pos_1194_ = v_pos_1221_;
goto v___jp_1193_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___boxed(lean_object* v_config_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1257_, v_a_1258_);
lean_dec_ref(v_config_1257_);
return v_res_1259_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(lean_object* v___x_1260_, lean_object* v___x_1261_, lean_object* v___x_1262_, lean_object* v_inst_1263_, lean_object* v_R_1264_, lean_object* v_a_1265_, uint8_t v_b_1266_, lean_object* v_c_1267_){
_start:
{
uint8_t v___x_1268_; 
v___x_1268_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_1260_, v___x_1261_, v___x_1262_, v_a_1265_, v_b_1266_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___boxed(lean_object* v___x_1269_, lean_object* v___x_1270_, lean_object* v___x_1271_, lean_object* v_inst_1272_, lean_object* v_R_1273_, lean_object* v_a_1274_, lean_object* v_b_1275_, lean_object* v_c_1276_){
_start:
{
uint8_t v_b_boxed_1277_; uint8_t v_res_1278_; lean_object* v_r_1279_; 
v_b_boxed_1277_ = lean_unbox(v_b_1275_);
v_res_1278_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(v___x_1269_, v___x_1270_, v___x_1271_, v_inst_1272_, v_R_1273_, v_a_1274_, v_b_boxed_1277_, v_c_1276_);
lean_dec(v___x_1271_);
lean_dec_ref(v___x_1270_);
lean_dec_ref(v___x_1269_);
v_r_1279_ = lean_box(v_res_1278_);
return v_r_1279_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(uint8_t v___x_1280_, lean_object* v___x_1281_, lean_object* v___x_1282_, lean_object* v___x_1283_, lean_object* v_inst_1284_, lean_object* v_R_1285_, lean_object* v_a_1286_, uint8_t v_b_1287_, lean_object* v_c_1288_){
_start:
{
uint8_t v___x_1289_; 
v___x_1289_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_1280_, v___x_1281_, v___x_1282_, v___x_1283_, v_a_1286_, v_b_1287_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___boxed(lean_object* v___x_1290_, lean_object* v___x_1291_, lean_object* v___x_1292_, lean_object* v___x_1293_, lean_object* v_inst_1294_, lean_object* v_R_1295_, lean_object* v_a_1296_, lean_object* v_b_1297_, lean_object* v_c_1298_){
_start:
{
uint8_t v___x_11346__boxed_1299_; uint8_t v_b_boxed_1300_; uint8_t v_res_1301_; lean_object* v_r_1302_; 
v___x_11346__boxed_1299_ = lean_unbox(v___x_1290_);
v_b_boxed_1300_ = lean_unbox(v_b_1297_);
v_res_1301_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(v___x_11346__boxed_1299_, v___x_1291_, v___x_1292_, v___x_1293_, v_inst_1294_, v_R_1295_, v_a_1296_, v_b_boxed_1300_, v_c_1298_);
lean_dec_ref(v___x_1292_);
lean_dec_ref(v___x_1291_);
v_r_1302_ = lean_box(v_res_1301_);
return v_r_1302_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1(lean_object* v___x_1303_, lean_object* v___x_1304_, lean_object* v___x_1305_, lean_object* v_inst_1306_, lean_object* v_R_1307_, lean_object* v_a_1308_, uint8_t v_b_1309_, lean_object* v_c_1310_){
_start:
{
uint8_t v___x_1311_; 
v___x_1311_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1___redArg(v___x_1304_, v_a_1308_, v_b_1309_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1___boxed(lean_object* v___x_1312_, lean_object* v___x_1313_, lean_object* v___x_1314_, lean_object* v_inst_1315_, lean_object* v_R_1316_, lean_object* v_a_1317_, lean_object* v_b_1318_, lean_object* v_c_1319_){
_start:
{
uint8_t v_b_boxed_1320_; uint8_t v_res_1321_; lean_object* v_r_1322_; 
v_b_boxed_1320_ = lean_unbox(v_b_1318_);
v_res_1321_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1(v___x_1312_, v___x_1313_, v___x_1314_, v_inst_1315_, v_R_1316_, v_a_1317_, v_b_boxed_1320_, v_c_1319_);
lean_dec(v___x_1314_);
lean_dec_ref(v___x_1313_);
lean_dec_ref(v___x_1312_);
v_r_1322_ = lean_box(v_res_1321_);
return v_r_1322_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3(uint8_t v___x_1323_, lean_object* v___x_1324_, lean_object* v___x_1325_, lean_object* v___x_1326_, lean_object* v_inst_1327_, lean_object* v_R_1328_, lean_object* v_a_1329_, uint8_t v_b_1330_, lean_object* v_c_1331_){
_start:
{
uint8_t v___x_1332_; 
v___x_1332_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___redArg(v___x_1323_, v___x_1324_, v___x_1325_, v___x_1326_, v_a_1329_, v_b_1330_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___boxed(lean_object* v___x_1333_, lean_object* v___x_1334_, lean_object* v___x_1335_, lean_object* v___x_1336_, lean_object* v_inst_1337_, lean_object* v_R_1338_, lean_object* v_a_1339_, lean_object* v_b_1340_, lean_object* v_c_1341_){
_start:
{
uint8_t v___x_11377__boxed_1342_; uint8_t v_b_boxed_1343_; uint8_t v_res_1344_; lean_object* v_r_1345_; 
v___x_11377__boxed_1342_ = lean_unbox(v___x_1333_);
v_b_boxed_1343_ = lean_unbox(v_b_1340_);
v_res_1344_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3(v___x_11377__boxed_1342_, v___x_1334_, v___x_1335_, v___x_1336_, v_inst_1337_, v_R_1338_, v_a_1339_, v_b_boxed_1343_, v_c_1341_);
lean_dec_ref(v___x_1335_);
lean_dec_ref(v___x_1334_);
v_r_1345_ = lean_box(v_res_1344_);
return v_r_1345_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2(void){
_start:
{
uint32_t v___x_1349_; uint8_t v___x_1350_; 
v___x_1349_ = 47;
v___x_1350_ = lean_uint32_to_uint8(v___x_1349_);
return v___x_1350_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3(void){
_start:
{
uint32_t v___x_1351_; uint8_t v___x_1352_; 
v___x_1351_ = 63;
v___x_1352_ = lean_uint32_to_uint8(v___x_1351_);
return v___x_1352_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4(void){
_start:
{
uint32_t v___x_1353_; uint8_t v___x_1354_; 
v___x_1353_ = 35;
v___x_1354_ = lean_uint32_to_uint8(v___x_1353_);
return v___x_1354_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5(void){
_start:
{
uint8_t v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_1356_ = lean_uint8_to_nat(v___x_1355_);
return v___x_1356_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6(void){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5);
v___x_1358_ = l_Nat_reprFast(v___x_1357_);
return v___x_1358_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7(void){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1359_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6);
v___x_1360_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_1361_ = lean_string_append(v___x_1360_, v___x_1359_);
return v___x_1361_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8(void){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1362_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_1363_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7);
v___x_1364_ = lean_string_append(v___x_1363_, v___x_1362_);
return v___x_1364_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9(void){
_start:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8);
v___x_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
return v___x_1366_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10(void){
_start:
{
uint32_t v___x_1367_; uint8_t v___x_1368_; 
v___x_1367_ = 64;
v___x_1368_ = lean_uint32_to_uint8(v___x_1367_);
return v___x_1368_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11(void){
_start:
{
uint8_t v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1370_ = lean_uint8_to_nat(v___x_1369_);
return v___x_1370_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12(void){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11);
v___x_1372_ = l_Nat_reprFast(v___x_1371_);
return v___x_1372_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13(void){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1373_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12);
v___x_1374_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_1375_ = lean_string_append(v___x_1374_, v___x_1373_);
return v___x_1375_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14(void){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1376_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_1377_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13);
v___x_1378_ = lean_string_append(v___x_1377_, v___x_1376_);
return v___x_1378_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15(void){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14);
v___x_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(lean_object* v_config_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v_port_1386_; lean_object* v___y_1387_; lean_object* v___y_1391_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; uint8_t v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; uint8_t v___y_1404_; lean_object* v___y_1406_; uint8_t v_val_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1417_; lean_object* v___y_1418_; uint8_t v___y_1419_; lean_object* v_pos_1420_; lean_object* v_array_1421_; lean_object* v_idx_1422_; lean_object* v_res_1423_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; uint8_t v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v_pos_1438_; lean_object* v_pos_1441_; lean_object* v_res_1442_; lean_object* v_pos_1507_; lean_object* v_res_1508_; lean_object* v_err_1511_; lean_object* v___x_1516_; 
lean_inc_ref(v_a_1382_);
v___x_1516_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(v_config_1381_, v_a_1382_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_pos_1517_; lean_object* v_res_1518_; lean_object* v_array_1519_; lean_object* v_idx_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1536_; 
v_pos_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_pos_1517_);
v_res_1518_ = lean_ctor_get(v___x_1516_, 1);
lean_inc(v_res_1518_);
lean_dec_ref_known(v___x_1516_, 2);
v_array_1519_ = lean_ctor_get(v_pos_1517_, 0);
v_idx_1520_ = lean_ctor_get(v_pos_1517_, 1);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_pos_1517_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1522_ = v_pos_1517_;
v_isShared_1523_ = v_isSharedCheck_1536_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_idx_1520_);
lean_inc(v_array_1519_);
lean_dec(v_pos_1517_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1536_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___x_1524_ = lean_byte_array_size(v_array_1519_);
v___x_1525_ = lean_nat_dec_lt(v_idx_1520_, v___x_1524_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; 
lean_del_object(v___x_1522_);
lean_dec(v_idx_1520_);
lean_dec_ref(v_array_1519_);
lean_dec(v_res_1518_);
v___x_1526_ = lean_box(0);
v_err_1511_ = v___x_1526_;
goto v___jp_1510_;
}
else
{
uint8_t v___x_1527_; uint8_t v_got_1528_; uint8_t v___x_1529_; 
v___x_1527_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v_got_1528_ = lean_byte_array_fget(v_array_1519_, v_idx_1520_);
v___x_1529_ = lean_uint8_dec_eq(v_got_1528_, v___x_1527_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; 
lean_del_object(v___x_1522_);
lean_dec(v_idx_1520_);
lean_dec_ref(v_array_1519_);
lean_dec(v_res_1518_);
v___x_1530_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15);
v_err_1511_ = v___x_1530_;
goto v___jp_1510_;
}
else
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1534_; 
lean_dec_ref(v_a_1382_);
v___x_1531_ = lean_unsigned_to_nat(1u);
v___x_1532_ = lean_nat_add(v_idx_1520_, v___x_1531_);
lean_dec(v_idx_1520_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 1, v___x_1532_);
v___x_1534_ = v___x_1522_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_array_1519_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v___x_1532_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
v_pos_1507_ = v___x_1534_;
v_res_1508_ = v_res_1518_;
goto v___jp_1506_;
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_pos_1537_; lean_object* v_res_1538_; 
lean_dec_ref(v_a_1382_);
v_pos_1537_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_pos_1537_);
v_res_1538_ = lean_ctor_get(v___x_1516_, 1);
lean_inc(v_res_1538_);
lean_dec_ref_known(v___x_1516_, 2);
v_pos_1507_ = v_pos_1537_;
v_res_1508_ = v_res_1538_;
goto v___jp_1506_;
}
else
{
lean_object* v_err_1539_; 
v_err_1539_ = lean_ctor_get(v___x_1516_, 1);
lean_inc(v_err_1539_);
lean_dec_ref_known(v___x_1516_, 2);
v_err_1511_ = v_err_1539_;
goto v___jp_1510_;
}
}
v___jp_1383_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1388_, 0, v___y_1384_);
lean_ctor_set(v___x_1388_, 1, v___y_1385_);
lean_ctor_set(v___x_1388_, 2, v_port_1386_);
v___x_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___y_1387_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
return v___x_1389_;
}
v___jp_1390_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1));
v___x_1393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___y_1391_);
lean_ctor_set(v___x_1393_, 1, v___x_1392_);
return v___x_1393_;
}
v___jp_1394_:
{
lean_object* v___x_1398_; 
v___x_1398_ = lean_box(1);
v___y_1384_ = v___y_1395_;
v___y_1385_ = v___y_1396_;
v_port_1386_ = v___x_1398_;
v___y_1387_ = v___y_1397_;
goto v___jp_1383_;
}
v___jp_1399_:
{
if (v___y_1400_ == 0)
{
if (v___y_1404_ == 0)
{
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
v___y_1391_ = v___y_1403_;
goto v___jp_1390_;
}
else
{
v___y_1395_ = v___y_1401_;
v___y_1396_ = v___y_1402_;
v___y_1397_ = v___y_1403_;
goto v___jp_1394_;
}
}
else
{
v___y_1395_ = v___y_1401_;
v___y_1396_ = v___y_1402_;
v___y_1397_ = v___y_1403_;
goto v___jp_1394_;
}
}
v___jp_1405_:
{
uint8_t v___x_1410_; uint8_t v___x_1411_; uint8_t v___x_1412_; uint8_t v___x_1413_; 
v___x_1410_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_1411_ = lean_uint8_dec_eq(v_val_1407_, v___x_1410_);
v___x_1412_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_1413_ = lean_uint8_dec_eq(v_val_1407_, v___x_1412_);
if (v___x_1413_ == 0)
{
uint8_t v___x_1414_; uint8_t v___x_1415_; 
v___x_1414_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v___x_1415_ = lean_uint8_dec_eq(v_val_1407_, v___x_1414_);
v___y_1400_ = v___x_1411_;
v___y_1401_ = v___y_1406_;
v___y_1402_ = v___y_1408_;
v___y_1403_ = v___y_1409_;
v___y_1404_ = v___x_1415_;
goto v___jp_1399_;
}
else
{
v___y_1400_ = v___x_1411_;
v___y_1401_ = v___y_1406_;
v___y_1402_ = v___y_1408_;
v___y_1403_ = v___y_1409_;
v___y_1404_ = v___x_1413_;
goto v___jp_1399_;
}
}
v___jp_1416_:
{
lean_object* v___x_1424_; uint8_t v___x_1425_; 
v___x_1424_ = lean_byte_array_size(v_array_1421_);
v___x_1425_ = lean_nat_dec_lt(v_idx_1422_, v___x_1424_);
if (v___x_1425_ == 0)
{
lean_dec(v_idx_1422_);
lean_dec_ref(v_array_1421_);
if (v___y_1419_ == 0)
{
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
v___y_1391_ = v_pos_1420_;
goto v___jp_1390_;
}
else
{
v___y_1395_ = v___y_1417_;
v___y_1396_ = v___y_1418_;
v___y_1397_ = v_pos_1420_;
goto v___jp_1394_;
}
}
else
{
uint8_t v___x_1426_; 
v___x_1426_ = lean_byte_array_fget(v_array_1421_, v_idx_1422_);
lean_dec(v_idx_1422_);
lean_dec_ref(v_array_1421_);
v___y_1406_ = v___y_1417_;
v_val_1407_ = v___x_1426_;
v___y_1408_ = v___y_1418_;
v___y_1409_ = v_pos_1420_;
goto v___jp_1405_;
}
}
v___jp_1427_:
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_box(0);
v___y_1417_ = v___y_1430_;
v___y_1418_ = v___y_1431_;
v___y_1419_ = v___y_1432_;
v_pos_1420_ = v___y_1429_;
v_array_1421_ = v___y_1428_;
v_idx_1422_ = v___y_1433_;
v_res_1423_ = v___x_1434_;
goto v___jp_1416_;
}
v___jp_1435_:
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_box(0);
v___y_1384_ = v___y_1436_;
v___y_1385_ = v___y_1437_;
v_port_1386_ = v___x_1439_;
v___y_1387_ = v_pos_1438_;
goto v___jp_1383_;
}
v___jp_1440_:
{
lean_object* v___x_1443_; 
v___x_1443_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1381_, v_pos_1441_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_pos_1444_; lean_object* v_res_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1496_; 
v_pos_1444_ = lean_ctor_get(v___x_1443_, 0);
v_res_1445_ = lean_ctor_get(v___x_1443_, 1);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1447_ = v___x_1443_;
v_isShared_1448_ = v_isSharedCheck_1496_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_res_1445_);
lean_inc(v_pos_1444_);
lean_dec(v___x_1443_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1496_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v_array_1449_; lean_object* v_idx_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v_array_1449_ = lean_ctor_get(v_pos_1444_, 0);
v_idx_1450_ = lean_ctor_get(v_pos_1444_, 1);
v___x_1451_ = lean_byte_array_size(v_array_1449_);
v___x_1452_ = lean_nat_dec_lt(v_idx_1450_, v___x_1451_);
if (v___x_1452_ == 0)
{
lean_del_object(v___x_1447_);
v___y_1436_ = v_res_1442_;
v___y_1437_ = v_res_1445_;
v_pos_1438_ = v_pos_1444_;
goto v___jp_1435_;
}
else
{
uint8_t v___x_1453_; uint8_t v___x_1454_; uint8_t v___x_1455_; 
v___x_1453_ = lean_byte_array_fget(v_array_1449_, v_idx_1450_);
v___x_1454_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_1455_ = lean_uint8_dec_eq(v___x_1453_, v___x_1454_);
if (v___x_1455_ == 0)
{
lean_del_object(v___x_1447_);
v___y_1436_ = v_res_1442_;
v___y_1437_ = v_res_1445_;
v_pos_1438_ = v_pos_1444_;
goto v___jp_1435_;
}
else
{
if (v___x_1455_ == 0)
{
lean_del_object(v___x_1447_);
v___y_1436_ = v_res_1442_;
v___y_1437_ = v_res_1445_;
v_pos_1438_ = v_pos_1444_;
goto v___jp_1435_;
}
else
{
if (v___x_1452_ == 0)
{
lean_object* v___x_1456_; lean_object* v___x_1458_; 
lean_dec(v_res_1445_);
lean_dec(v_res_1442_);
v___x_1456_ = lean_box(0);
if (v_isShared_1448_ == 0)
{
lean_ctor_set_tag(v___x_1447_, 1);
lean_ctor_set(v___x_1447_, 1, v___x_1456_);
v___x_1458_ = v___x_1447_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_pos_1444_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
else
{
if (v___x_1455_ == 0)
{
lean_object* v___x_1460_; lean_object* v___x_1462_; 
lean_dec(v_res_1445_);
lean_dec(v_res_1442_);
v___x_1460_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
if (v_isShared_1448_ == 0)
{
lean_ctor_set_tag(v___x_1447_, 1);
lean_ctor_set(v___x_1447_, 1, v___x_1460_);
v___x_1462_ = v___x_1447_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_pos_1444_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
else
{
lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1493_; 
lean_inc(v_idx_1450_);
lean_inc_ref(v_array_1449_);
lean_del_object(v___x_1447_);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_pos_1444_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; lean_object* v_unused_1495_; 
v_unused_1494_ = lean_ctor_get(v_pos_1444_, 1);
lean_dec(v_unused_1494_);
v_unused_1495_ = lean_ctor_get(v_pos_1444_, 0);
lean_dec(v_unused_1495_);
v___x_1465_ = v_pos_1444_;
v_isShared_1466_ = v_isSharedCheck_1493_;
goto v_resetjp_1464_;
}
else
{
lean_dec(v_pos_1444_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1493_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1467_ = lean_unsigned_to_nat(1u);
v___x_1468_ = lean_nat_add(v_idx_1450_, v___x_1467_);
lean_dec(v_idx_1450_);
lean_inc(v___x_1468_);
lean_inc_ref(v_array_1449_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 1, v___x_1468_);
v___x_1470_ = v___x_1465_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_array_1449_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
uint8_t v___x_1471_; 
v___x_1471_ = lean_nat_dec_lt(v___x_1468_, v___x_1451_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; 
v___x_1472_ = lean_box(0);
v___y_1417_ = v_res_1442_;
v___y_1418_ = v_res_1445_;
v___y_1419_ = v___x_1455_;
v_pos_1420_ = v___x_1470_;
v_array_1421_ = v_array_1449_;
v_idx_1422_ = v___x_1468_;
v_res_1423_ = v___x_1472_;
goto v___jp_1416_;
}
else
{
uint8_t v___x_1473_; uint8_t v___x_1474_; uint8_t v___x_1475_; 
v___x_1473_ = lean_byte_array_fget(v_array_1449_, v___x_1468_);
v___x_1474_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_1475_ = lean_uint8_dec_le(v___x_1474_, v___x_1473_);
if (v___x_1475_ == 0)
{
v___y_1428_ = v_array_1449_;
v___y_1429_ = v___x_1470_;
v___y_1430_ = v_res_1442_;
v___y_1431_ = v_res_1445_;
v___y_1432_ = v___x_1455_;
v___y_1433_ = v___x_1468_;
goto v___jp_1427_;
}
else
{
uint8_t v___x_1476_; uint8_t v___x_1477_; 
v___x_1476_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_1477_ = lean_uint8_dec_le(v___x_1473_, v___x_1476_);
if (v___x_1477_ == 0)
{
v___y_1428_ = v_array_1449_;
v___y_1429_ = v___x_1470_;
v___y_1430_ = v_res_1442_;
v___y_1431_ = v_res_1445_;
v___y_1432_ = v___x_1455_;
v___y_1433_ = v___x_1468_;
goto v___jp_1427_;
}
else
{
lean_object* v___x_1478_; 
lean_dec(v___x_1468_);
lean_dec_ref(v_array_1449_);
v___x_1478_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_1470_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_pos_1479_; lean_object* v_res_1480_; lean_object* v___x_1481_; uint16_t v___x_1482_; 
v_pos_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_pos_1479_);
v_res_1480_ = lean_ctor_get(v___x_1478_, 1);
lean_inc(v_res_1480_);
lean_dec_ref_known(v___x_1478_, 2);
v___x_1481_ = lean_alloc_ctor(2, 0, 2);
v___x_1482_ = lean_unbox(v_res_1480_);
lean_dec(v_res_1480_);
lean_ctor_set_uint16(v___x_1481_, 0, v___x_1482_);
v___y_1384_ = v_res_1442_;
v___y_1385_ = v_res_1445_;
v_port_1386_ = v___x_1481_;
v___y_1387_ = v_pos_1479_;
goto v___jp_1383_;
}
else
{
lean_object* v_pos_1483_; lean_object* v_err_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec(v_res_1445_);
lean_dec(v_res_1442_);
v_pos_1483_ = lean_ctor_get(v___x_1478_, 0);
v_err_1484_ = lean_ctor_get(v___x_1478_, 1);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1478_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_err_1484_);
lean_inc(v_pos_1483_);
lean_dec(v___x_1478_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_pos_1483_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_err_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
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
lean_object* v_pos_1497_; lean_object* v_err_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec(v_res_1442_);
v_pos_1497_ = lean_ctor_get(v___x_1443_, 0);
v_err_1498_ = lean_ctor_get(v___x_1443_, 1);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1443_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_err_1498_);
lean_inc(v_pos_1497_);
lean_dec(v___x_1443_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_pos_1497_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_err_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
v___jp_1506_:
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1509_, 0, v_res_1508_);
v_pos_1441_ = v_pos_1507_;
v_res_1442_ = v___x_1509_;
goto v___jp_1440_;
}
v___jp_1510_:
{
lean_object* v_idx_1512_; uint8_t v___x_1513_; 
v_idx_1512_ = lean_ctor_get(v_a_1382_, 1);
v___x_1513_ = lean_nat_dec_eq(v_idx_1512_, v_idx_1512_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1514_, 0, v_a_1382_);
lean_ctor_set(v___x_1514_, 1, v_err_1511_);
return v___x_1514_;
}
else
{
lean_object* v___x_1515_; 
lean_dec(v_err_1511_);
v___x_1515_ = lean_box(0);
v_pos_1441_ = v_a_1382_;
v_res_1442_ = v___x_1515_;
goto v___jp_1440_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___boxed(lean_object* v_config_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_1540_, v_a_1541_);
lean_dec_ref(v_config_1540_);
return v_res_1542_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(uint8_t v_c_1543_){
_start:
{
uint8_t v___y_1545_; uint8_t v___x_1593_; uint8_t v___x_1594_; 
v___x_1593_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_1594_ = lean_uint8_dec_le(v___x_1593_, v_c_1543_);
if (v___x_1594_ == 0)
{
goto v___jp_1588_;
}
else
{
uint8_t v___x_1595_; uint8_t v___x_1596_; 
v___x_1595_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_1596_ = lean_uint8_dec_le(v_c_1543_, v___x_1595_);
if (v___x_1596_ == 0)
{
goto v___jp_1588_;
}
else
{
v___y_1545_ = v___x_1596_;
goto v___jp_1544_;
}
}
v___jp_1544_:
{
if (v___y_1545_ == 0)
{
uint8_t v___x_1546_; uint8_t v___x_1547_; 
v___x_1546_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1547_ = lean_uint8_dec_eq(v_c_1543_, v___x_1546_);
return v___x_1547_;
}
else
{
return v___y_1545_;
}
}
v___jp_1548_:
{
uint8_t v___x_1549_; uint8_t v___x_1550_; 
v___x_1549_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_1550_ = lean_uint8_dec_eq(v_c_1543_, v___x_1549_);
if (v___x_1550_ == 0)
{
uint8_t v___x_1551_; uint8_t v___x_1552_; 
v___x_1551_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_1552_ = lean_uint8_dec_eq(v_c_1543_, v___x_1551_);
if (v___x_1552_ == 0)
{
uint8_t v___x_1553_; uint8_t v___x_1554_; 
v___x_1553_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_1554_ = lean_uint8_dec_eq(v_c_1543_, v___x_1553_);
if (v___x_1554_ == 0)
{
uint8_t v___x_1555_; uint8_t v___x_1556_; 
v___x_1555_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_1556_ = lean_uint8_dec_eq(v_c_1543_, v___x_1555_);
if (v___x_1556_ == 0)
{
uint8_t v___x_1557_; uint8_t v___x_1558_; 
v___x_1557_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_1558_ = lean_uint8_dec_eq(v_c_1543_, v___x_1557_);
if (v___x_1558_ == 0)
{
uint8_t v___x_1559_; uint8_t v___x_1560_; 
v___x_1559_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_1560_ = lean_uint8_dec_eq(v_c_1543_, v___x_1559_);
if (v___x_1560_ == 0)
{
uint8_t v___x_1561_; uint8_t v___x_1562_; 
v___x_1561_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_1562_ = lean_uint8_dec_eq(v_c_1543_, v___x_1561_);
if (v___x_1562_ == 0)
{
uint8_t v___x_1563_; uint8_t v___x_1564_; 
v___x_1563_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_1564_ = lean_uint8_dec_eq(v_c_1543_, v___x_1563_);
if (v___x_1564_ == 0)
{
uint8_t v___x_1565_; uint8_t v___x_1566_; 
v___x_1565_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_1566_ = lean_uint8_dec_eq(v_c_1543_, v___x_1565_);
if (v___x_1566_ == 0)
{
uint8_t v___x_1567_; uint8_t v___x_1568_; 
v___x_1567_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_1568_ = lean_uint8_dec_eq(v_c_1543_, v___x_1567_);
if (v___x_1568_ == 0)
{
uint8_t v___x_1569_; uint8_t v___x_1570_; 
v___x_1569_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_1570_ = lean_uint8_dec_eq(v_c_1543_, v___x_1569_);
if (v___x_1570_ == 0)
{
uint8_t v___x_1571_; uint8_t v___x_1572_; 
v___x_1571_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_1572_ = lean_uint8_dec_eq(v_c_1543_, v___x_1571_);
if (v___x_1572_ == 0)
{
uint8_t v___x_1573_; uint8_t v___x_1574_; 
v___x_1573_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_1574_ = lean_uint8_dec_eq(v_c_1543_, v___x_1573_);
if (v___x_1574_ == 0)
{
uint8_t v___x_1575_; uint8_t v___x_1576_; 
v___x_1575_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_1576_ = lean_uint8_dec_eq(v_c_1543_, v___x_1575_);
if (v___x_1576_ == 0)
{
uint8_t v___x_1577_; uint8_t v___x_1578_; 
v___x_1577_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_1578_ = lean_uint8_dec_eq(v_c_1543_, v___x_1577_);
if (v___x_1578_ == 0)
{
uint8_t v___x_1579_; uint8_t v___x_1580_; 
v___x_1579_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_1580_ = lean_uint8_dec_eq(v_c_1543_, v___x_1579_);
if (v___x_1580_ == 0)
{
uint8_t v___x_1581_; uint8_t v___x_1582_; 
v___x_1581_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1582_ = lean_uint8_dec_eq(v_c_1543_, v___x_1581_);
v___y_1545_ = v___x_1582_;
goto v___jp_1544_;
}
else
{
v___y_1545_ = v___x_1580_;
goto v___jp_1544_;
}
}
else
{
v___y_1545_ = v___x_1578_;
goto v___jp_1544_;
}
}
else
{
v___y_1545_ = v___x_1576_;
goto v___jp_1544_;
}
}
else
{
v___y_1545_ = v___x_1574_;
goto v___jp_1544_;
}
}
else
{
v___y_1545_ = v___x_1572_;
goto v___jp_1544_;
}
}
else
{
v___y_1545_ = v___x_1570_;
goto v___jp_1544_;
}
}
else
{
v___y_1545_ = v___x_1568_;
goto v___jp_1544_;
}
}
else
{
v___y_1545_ = v___x_1566_;
goto v___jp_1544_;
}
}
else
{
v___y_1545_ = v___x_1564_;
goto v___jp_1544_;
}
}
else
{
v___y_1545_ = v___x_1562_;
goto v___jp_1544_;
}
}
else
{
v___y_1545_ = v___x_1560_;
goto v___jp_1544_;
}
}
else
{
v___y_1545_ = v___x_1558_;
goto v___jp_1544_;
}
}
else
{
v___y_1545_ = v___x_1556_;
goto v___jp_1544_;
}
}
else
{
v___y_1545_ = v___x_1554_;
goto v___jp_1544_;
}
}
else
{
v___y_1545_ = v___x_1552_;
goto v___jp_1544_;
}
}
else
{
v___y_1545_ = v___x_1550_;
goto v___jp_1544_;
}
}
v___jp_1583_:
{
uint8_t v___x_1584_; uint8_t v___x_1585_; 
v___x_1584_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_1585_ = lean_uint8_dec_le(v___x_1584_, v_c_1543_);
if (v___x_1585_ == 0)
{
goto v___jp_1548_;
}
else
{
uint8_t v___x_1586_; uint8_t v___x_1587_; 
v___x_1586_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_1587_ = lean_uint8_dec_le(v_c_1543_, v___x_1586_);
if (v___x_1587_ == 0)
{
goto v___jp_1548_;
}
else
{
v___y_1545_ = v___x_1587_;
goto v___jp_1544_;
}
}
}
v___jp_1588_:
{
uint8_t v___x_1589_; uint8_t v___x_1590_; 
v___x_1589_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_1590_ = lean_uint8_dec_le(v___x_1589_, v_c_1543_);
if (v___x_1590_ == 0)
{
goto v___jp_1583_;
}
else
{
uint8_t v___x_1591_; uint8_t v___x_1592_; 
v___x_1591_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_1592_ = lean_uint8_dec_le(v_c_1543_, v___x_1591_);
if (v___x_1592_ == 0)
{
goto v___jp_1583_;
}
else
{
v___y_1545_ = v___x_1592_;
goto v___jp_1544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0___boxed(lean_object* v_c_1597_){
_start:
{
uint8_t v_c_boxed_1598_; uint8_t v_res_1599_; lean_object* v_r_1600_; 
v_c_boxed_1598_ = lean_unbox(v_c_1597_);
v_res_1599_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(v_c_boxed_1598_);
v_r_1600_ = lean_box(v_res_1599_);
return v_r_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(lean_object* v_config_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v_maxSegmentLength_1604_; lean_object* v___f_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v_snd_1608_; lean_object* v_fst_1609_; lean_object* v_fst_1610_; lean_object* v_array_1611_; lean_object* v_idx_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1629_; 
v_maxSegmentLength_1604_ = lean_ctor_get(v_config_1602_, 3);
v___f_1605_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0));
v___x_1606_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1603_);
v___x_1607_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1605_, v_maxSegmentLength_1604_, v___x_1606_, v_a_1603_);
v_snd_1608_ = lean_ctor_get(v___x_1607_, 1);
lean_inc(v_snd_1608_);
v_fst_1609_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_fst_1609_);
lean_dec_ref(v___x_1607_);
v_fst_1610_ = lean_ctor_get(v_snd_1608_, 0);
lean_inc(v_fst_1610_);
lean_dec(v_snd_1608_);
v_array_1611_ = lean_ctor_get(v_a_1603_, 0);
v_idx_1612_ = lean_ctor_get(v_a_1603_, 1);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_a_1603_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1614_ = v_a_1603_;
v_isShared_1615_ = v_isSharedCheck_1629_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_idx_1612_);
lean_inc(v_array_1611_);
lean_dec(v_a_1603_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1629_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v_lower_1617_; lean_object* v_upper_1618_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___y_1626_; uint8_t v___x_1628_; 
v___x_1623_ = lean_nat_add(v_idx_1612_, v_fst_1609_);
lean_dec(v_fst_1609_);
v___x_1624_ = lean_byte_array_size(v_array_1611_);
v___x_1628_ = lean_nat_dec_le(v_idx_1612_, v___x_1606_);
if (v___x_1628_ == 0)
{
v___y_1626_ = v_idx_1612_;
goto v___jp_1625_;
}
else
{
lean_dec(v_idx_1612_);
v___y_1626_ = v___x_1606_;
goto v___jp_1625_;
}
v___jp_1616_:
{
lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1619_ = l_ByteArray_toByteSlice(v_array_1611_, v_lower_1617_, v_upper_1618_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 1, v___x_1619_);
lean_ctor_set(v___x_1614_, 0, v_fst_1610_);
v___x_1621_ = v___x_1614_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_fst_1610_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
v___jp_1625_:
{
uint8_t v___x_1627_; 
v___x_1627_ = lean_nat_dec_le(v___x_1623_, v___x_1624_);
if (v___x_1627_ == 0)
{
lean_dec(v___x_1623_);
v_lower_1617_ = v___y_1626_;
v_upper_1618_ = v___x_1624_;
goto v___jp_1616_;
}
else
{
v_lower_1617_ = v___y_1626_;
v_upper_1618_ = v___x_1623_;
goto v___jp_1616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___boxed(lean_object* v_config_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1630_, v_a_1631_);
lean_dec_ref(v_config_1630_);
return v_res_1632_;
}
}
LEAN_EXPORT uint8_t l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(uint8_t v_c_1633_){
_start:
{
uint8_t v___x_1634_; uint8_t v___x_1635_; 
v___x_1634_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_1635_ = lean_uint8_dec_eq(v_c_1633_, v___x_1634_);
if (v___x_1635_ == 0)
{
uint8_t v___x_1636_; uint8_t v___x_1637_; 
v___x_1636_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v___x_1637_ = lean_uint8_dec_eq(v_c_1633_, v___x_1636_);
return v___x_1637_;
}
else
{
return v___x_1635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0___boxed(lean_object* v_c_1638_){
_start:
{
uint8_t v_c_boxed_1639_; uint8_t v_res_1640_; lean_object* v_r_1641_; 
v_c_boxed_1639_ = lean_unbox(v_c_1638_);
v_res_1640_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v_c_boxed_1639_);
v_r_1641_ = lean_box(v_res_1640_);
return v_r_1641_;
}
}
LEAN_EXPORT uint8_t l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__1(uint8_t v___y_1642_){
_start:
{
uint8_t v___x_1688_; uint8_t v___x_1689_; 
v___x_1688_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_1689_ = lean_uint8_dec_le(v___x_1688_, v___y_1642_);
if (v___x_1689_ == 0)
{
goto v___jp_1683_;
}
else
{
uint8_t v___x_1690_; uint8_t v___x_1691_; 
v___x_1690_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_1691_ = lean_uint8_dec_le(v___y_1642_, v___x_1690_);
if (v___x_1691_ == 0)
{
goto v___jp_1683_;
}
else
{
return v___x_1691_;
}
}
v___jp_1643_:
{
uint8_t v___x_1644_; uint8_t v___x_1645_; 
v___x_1644_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_1645_ = lean_uint8_dec_eq(v___y_1642_, v___x_1644_);
if (v___x_1645_ == 0)
{
uint8_t v___x_1646_; uint8_t v___x_1647_; 
v___x_1646_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_1647_ = lean_uint8_dec_eq(v___y_1642_, v___x_1646_);
if (v___x_1647_ == 0)
{
uint8_t v___x_1648_; uint8_t v___x_1649_; 
v___x_1648_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_1649_ = lean_uint8_dec_eq(v___y_1642_, v___x_1648_);
if (v___x_1649_ == 0)
{
uint8_t v___x_1650_; uint8_t v___x_1651_; 
v___x_1650_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_1651_ = lean_uint8_dec_eq(v___y_1642_, v___x_1650_);
if (v___x_1651_ == 0)
{
uint8_t v___x_1652_; uint8_t v___x_1653_; 
v___x_1652_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_1653_ = lean_uint8_dec_eq(v___y_1642_, v___x_1652_);
if (v___x_1653_ == 0)
{
uint8_t v___x_1654_; uint8_t v___x_1655_; 
v___x_1654_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_1655_ = lean_uint8_dec_eq(v___y_1642_, v___x_1654_);
if (v___x_1655_ == 0)
{
uint8_t v___x_1656_; uint8_t v___x_1657_; 
v___x_1656_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_1657_ = lean_uint8_dec_eq(v___y_1642_, v___x_1656_);
if (v___x_1657_ == 0)
{
uint8_t v___x_1658_; uint8_t v___x_1659_; 
v___x_1658_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_1659_ = lean_uint8_dec_eq(v___y_1642_, v___x_1658_);
if (v___x_1659_ == 0)
{
uint8_t v___x_1660_; uint8_t v___x_1661_; 
v___x_1660_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_1661_ = lean_uint8_dec_eq(v___y_1642_, v___x_1660_);
if (v___x_1661_ == 0)
{
uint8_t v___x_1662_; uint8_t v___x_1663_; 
v___x_1662_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_1663_ = lean_uint8_dec_eq(v___y_1642_, v___x_1662_);
if (v___x_1663_ == 0)
{
uint8_t v___x_1664_; uint8_t v___x_1665_; 
v___x_1664_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_1665_ = lean_uint8_dec_eq(v___y_1642_, v___x_1664_);
if (v___x_1665_ == 0)
{
uint8_t v___x_1666_; uint8_t v___x_1667_; 
v___x_1666_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_1667_ = lean_uint8_dec_eq(v___y_1642_, v___x_1666_);
if (v___x_1667_ == 0)
{
uint8_t v___x_1668_; uint8_t v___x_1669_; 
v___x_1668_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_1669_ = lean_uint8_dec_eq(v___y_1642_, v___x_1668_);
if (v___x_1669_ == 0)
{
uint8_t v___x_1670_; uint8_t v___x_1671_; 
v___x_1670_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_1671_ = lean_uint8_dec_eq(v___y_1642_, v___x_1670_);
if (v___x_1671_ == 0)
{
uint8_t v___x_1672_; uint8_t v___x_1673_; 
v___x_1672_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_1673_ = lean_uint8_dec_eq(v___y_1642_, v___x_1672_);
if (v___x_1673_ == 0)
{
uint8_t v___x_1674_; uint8_t v___x_1675_; 
v___x_1674_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_1675_ = lean_uint8_dec_eq(v___y_1642_, v___x_1674_);
if (v___x_1675_ == 0)
{
uint8_t v___x_1676_; uint8_t v___x_1677_; 
v___x_1676_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1677_ = lean_uint8_dec_eq(v___y_1642_, v___x_1676_);
return v___x_1677_;
}
else
{
return v___x_1675_;
}
}
else
{
return v___x_1673_;
}
}
else
{
return v___x_1671_;
}
}
else
{
return v___x_1669_;
}
}
else
{
return v___x_1667_;
}
}
else
{
return v___x_1665_;
}
}
else
{
return v___x_1663_;
}
}
else
{
return v___x_1661_;
}
}
else
{
return v___x_1659_;
}
}
else
{
return v___x_1657_;
}
}
else
{
return v___x_1655_;
}
}
else
{
return v___x_1653_;
}
}
else
{
return v___x_1651_;
}
}
else
{
return v___x_1649_;
}
}
else
{
return v___x_1647_;
}
}
else
{
return v___x_1645_;
}
}
v___jp_1678_:
{
uint8_t v___x_1679_; uint8_t v___x_1680_; 
v___x_1679_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_1680_ = lean_uint8_dec_le(v___x_1679_, v___y_1642_);
if (v___x_1680_ == 0)
{
goto v___jp_1643_;
}
else
{
uint8_t v___x_1681_; uint8_t v___x_1682_; 
v___x_1681_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_1682_ = lean_uint8_dec_le(v___y_1642_, v___x_1681_);
if (v___x_1682_ == 0)
{
goto v___jp_1643_;
}
else
{
return v___x_1682_;
}
}
}
v___jp_1683_:
{
uint8_t v___x_1684_; uint8_t v___x_1685_; 
v___x_1684_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_1685_ = lean_uint8_dec_le(v___x_1684_, v___y_1642_);
if (v___x_1685_ == 0)
{
goto v___jp_1678_;
}
else
{
uint8_t v___x_1686_; uint8_t v___x_1687_; 
v___x_1686_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_1687_ = lean_uint8_dec_le(v___y_1642_, v___x_1686_);
if (v___x_1687_ == 0)
{
goto v___jp_1678_;
}
else
{
return v___x_1687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__1___boxed(lean_object* v___y_1692_){
_start:
{
uint8_t v___y_16791__boxed_1693_; uint8_t v_res_1694_; lean_object* v_r_1695_; 
v___y_16791__boxed_1693_ = lean_unbox(v___y_1692_);
v_res_1694_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__1(v___y_16791__boxed_1693_);
v_r_1695_ = lean_box(v_res_1694_);
return v_r_1695_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___f_1697_; lean_object* v___x_1698_; 
v___f_1697_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1698_ = l_Std_Http_URI_EncodedString_empty(v___f_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(lean_object* v_config_1706_, lean_object* v_a_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v_array_1715_; lean_object* v_idx_1716_; lean_object* v_fst_1717_; lean_object* v_snd_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1912_; 
v_array_1715_ = lean_ctor_get(v___y_1708_, 0);
v_idx_1716_ = lean_ctor_get(v___y_1708_, 1);
v_fst_1717_ = lean_ctor_get(v_a_1707_, 0);
v_snd_1718_ = lean_ctor_get(v_a_1707_, 1);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_a_1707_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1720_ = v_a_1707_;
v_isShared_1721_ = v_isSharedCheck_1912_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_snd_1718_);
lean_inc(v_fst_1717_);
lean_dec(v_a_1707_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1912_;
goto v_resetjp_1719_;
}
v___jp_1709_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___y_1710_);
lean_ctor_set(v___x_1713_, 1, v___y_1712_);
v___x_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1714_, 0, v___y_1711_);
lean_ctor_set(v___x_1714_, 1, v___x_1713_);
return v___x_1714_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; uint8_t v___x_1723_; 
v___x_1722_ = lean_byte_array_size(v_array_1715_);
v___x_1723_ = lean_nat_dec_lt(v_idx_1716_, v___x_1722_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1725_; 
lean_dec_ref(v_config_1706_);
if (v_isShared_1721_ == 0)
{
v___x_1725_ = v___x_1720_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_fst_1717_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v_snd_1718_);
v___x_1725_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
lean_object* v___x_1726_; 
v___x_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___y_1708_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
return v___x_1726_;
}
}
else
{
if (v___x_1723_ == 0)
{
lean_object* v___x_1729_; 
lean_dec_ref(v_config_1706_);
if (v_isShared_1721_ == 0)
{
v___x_1729_ = v___x_1720_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_fst_1717_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_snd_1718_);
v___x_1729_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1730_; 
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___y_1708_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
return v___x_1730_;
}
}
else
{
uint8_t v___x_1732_; uint8_t v___x_1733_; 
v___x_1732_ = lean_byte_array_fget(v_array_1715_, v_idx_1716_);
v___x_1733_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1732_);
if (v___x_1733_ == 0)
{
lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; uint8_t v___x_1754_; uint8_t v___y_1849_; uint8_t v___x_1852_; uint8_t v___y_1854_; uint8_t v___y_1856_; uint8_t v___x_1904_; uint8_t v___x_1905_; 
v___x_1754_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_1852_ = lean_uint8_dec_eq(v___x_1732_, v___x_1754_);
v___x_1904_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_1905_ = lean_uint8_dec_le(v___x_1904_, v___x_1732_);
if (v___x_1905_ == 0)
{
goto v___jp_1899_;
}
else
{
uint8_t v___x_1906_; uint8_t v___x_1907_; 
v___x_1906_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_1907_ = lean_uint8_dec_le(v___x_1732_, v___x_1906_);
if (v___x_1907_ == 0)
{
goto v___jp_1899_;
}
else
{
v___y_1856_ = v___x_1907_;
goto v___jp_1855_;
}
}
v___jp_1734_:
{
lean_object* v___x_1739_; uint8_t v___x_1740_; 
v___x_1739_ = lean_array_get_size(v___y_1735_);
v___x_1740_ = lean_nat_dec_le(v___y_1736_, v___x_1739_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1744_; 
lean_dec(v___y_1736_);
v___x_1741_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1);
v___x_1742_ = lean_array_push(v___y_1735_, v___x_1741_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 1, v___y_1737_);
lean_ctor_set(v___x_1720_, 0, v___x_1742_);
v___x_1744_ = v___x_1720_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1742_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v___y_1737_);
v___x_1744_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
v_a_1707_ = v___x_1744_;
v___y_1708_ = v___y_1738_;
goto _start;
}
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1735_);
lean_del_object(v___x_1720_);
lean_dec_ref(v_config_1706_);
v___x_1747_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1748_ = l_Nat_reprFast(v___y_1736_);
v___x_1749_ = lean_string_append(v___x_1747_, v___x_1748_);
lean_dec_ref(v___x_1748_);
v___x_1750_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1751_ = lean_string_append(v___x_1749_, v___x_1750_);
v___x_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
v___x_1753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___y_1738_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
return v___x_1753_;
}
}
v___jp_1755_:
{
lean_object* v_maxPathSegments_1756_; lean_object* v_maxTotalPathLength_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; 
v_maxPathSegments_1756_ = lean_ctor_get(v_config_1706_, 6);
v_maxTotalPathLength_1757_ = lean_ctor_get(v_config_1706_, 7);
v___x_1758_ = lean_array_get_size(v_fst_1717_);
v___x_1759_ = lean_nat_dec_le(v_maxPathSegments_1756_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; 
v___x_1760_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1706_, v___y_1708_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_pos_1761_; lean_object* v_res_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1831_; 
v_pos_1761_ = lean_ctor_get(v___x_1760_, 0);
v_res_1762_ = lean_ctor_get(v___x_1760_, 1);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1764_ = v___x_1760_;
v_isShared_1765_ = v_isSharedCheck_1831_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_res_1762_);
lean_inc(v_pos_1761_);
lean_dec(v___x_1760_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1831_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
lean_inc(v_res_1762_);
v___x_1766_ = l_ByteSlice_toByteArray(v_res_1762_);
v___x_1767_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1766_);
if (lean_obj_tag(v___x_1767_) == 1)
{
lean_object* v_val_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1826_; 
v_val_1768_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1770_ = v___x_1767_;
v_isShared_1771_ = v_isSharedCheck_1826_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_val_1768_);
lean_dec(v___x_1767_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1826_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1772_ = l_ByteSlice_size(v_res_1762_);
lean_dec(v_res_1762_);
v___x_1773_ = lean_nat_add(v_snd_1718_, v___x_1772_);
lean_dec(v___x_1772_);
lean_dec(v_snd_1718_);
v___x_1774_ = lean_nat_dec_lt(v_maxTotalPathLength_1757_, v___x_1773_);
if (v___x_1774_ == 0)
{
lean_object* v_array_1775_; lean_object* v_idx_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; uint8_t v___x_1779_; 
v_array_1775_ = lean_ctor_get(v_pos_1761_, 0);
v_idx_1776_ = lean_ctor_get(v_pos_1761_, 1);
v___x_1777_ = lean_array_push(v_fst_1717_, v_val_1768_);
v___x_1778_ = lean_byte_array_size(v_array_1775_);
v___x_1779_ = lean_nat_dec_lt(v_idx_1776_, v___x_1778_);
if (v___x_1779_ == 0)
{
lean_del_object(v___x_1770_);
lean_del_object(v___x_1764_);
lean_del_object(v___x_1720_);
lean_dec_ref(v_config_1706_);
v___y_1710_ = v___x_1777_;
v___y_1711_ = v_pos_1761_;
v___y_1712_ = v___x_1773_;
goto v___jp_1709_;
}
else
{
uint8_t v___x_1780_; uint8_t v___x_1781_; 
v___x_1780_ = lean_byte_array_fget(v_array_1775_, v_idx_1776_);
v___x_1781_ = lean_uint8_dec_eq(v___x_1780_, v___x_1754_);
if (v___x_1781_ == 0)
{
lean_del_object(v___x_1770_);
lean_del_object(v___x_1764_);
lean_del_object(v___x_1720_);
lean_dec_ref(v_config_1706_);
v___y_1710_ = v___x_1777_;
v___y_1711_ = v_pos_1761_;
v___y_1712_ = v___x_1773_;
goto v___jp_1709_;
}
else
{
lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1782_ = lean_unsigned_to_nat(1u);
v___x_1783_ = lean_nat_add(v___x_1773_, v___x_1782_);
lean_dec(v___x_1773_);
v___x_1784_ = lean_nat_dec_lt(v_maxTotalPathLength_1757_, v___x_1783_);
if (v___x_1784_ == 0)
{
lean_del_object(v___x_1770_);
if (v___x_1779_ == 0)
{
lean_object* v___x_1785_; lean_object* v___x_1787_; 
lean_dec(v___x_1783_);
lean_dec_ref(v___x_1777_);
lean_del_object(v___x_1720_);
lean_dec_ref(v_config_1706_);
v___x_1785_ = lean_box(0);
if (v_isShared_1765_ == 0)
{
lean_ctor_set_tag(v___x_1764_, 1);
lean_ctor_set(v___x_1764_, 1, v___x_1785_);
v___x_1787_ = v___x_1764_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_pos_1761_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
else
{
lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1801_; 
lean_inc(v_idx_1776_);
lean_inc_ref(v_array_1775_);
lean_del_object(v___x_1764_);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_pos_1761_);
if (v_isSharedCheck_1801_ == 0)
{
lean_object* v_unused_1802_; lean_object* v_unused_1803_; 
v_unused_1802_ = lean_ctor_get(v_pos_1761_, 1);
lean_dec(v_unused_1802_);
v_unused_1803_ = lean_ctor_get(v_pos_1761_, 0);
lean_dec(v_unused_1803_);
v___x_1790_ = v_pos_1761_;
v_isShared_1791_ = v_isSharedCheck_1801_;
goto v_resetjp_1789_;
}
else
{
lean_dec(v_pos_1761_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1801_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1792_; lean_object* v___x_1794_; 
v___x_1792_ = lean_nat_add(v_idx_1776_, v___x_1782_);
lean_dec(v_idx_1776_);
lean_inc(v___x_1792_);
lean_inc_ref(v_array_1775_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 1, v___x_1792_);
v___x_1794_ = v___x_1790_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_array_1775_);
lean_ctor_set(v_reuseFailAlloc_1800_, 1, v___x_1792_);
v___x_1794_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
uint8_t v___x_1795_; 
v___x_1795_ = lean_nat_dec_lt(v___x_1792_, v___x_1778_);
if (v___x_1795_ == 0)
{
lean_dec(v___x_1792_);
lean_dec_ref(v_array_1775_);
lean_inc(v_maxPathSegments_1756_);
v___y_1735_ = v___x_1777_;
v___y_1736_ = v_maxPathSegments_1756_;
v___y_1737_ = v___x_1783_;
v___y_1738_ = v___x_1794_;
goto v___jp_1734_;
}
else
{
uint8_t v___x_1796_; uint8_t v___x_1797_; 
v___x_1796_ = lean_byte_array_fget(v_array_1775_, v___x_1792_);
lean_dec(v___x_1792_);
lean_dec_ref(v_array_1775_);
v___x_1797_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1796_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; 
lean_del_object(v___x_1720_);
v___x_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1777_);
lean_ctor_set(v___x_1798_, 1, v___x_1783_);
v_a_1707_ = v___x_1798_;
v___y_1708_ = v___x_1794_;
goto _start;
}
else
{
lean_inc(v_maxPathSegments_1756_);
v___y_1735_ = v___x_1777_;
v___y_1736_ = v_maxPathSegments_1756_;
v___y_1737_ = v___x_1783_;
v___y_1738_ = v___x_1794_;
goto v___jp_1734_;
}
}
}
}
}
}
else
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1810_; 
lean_inc(v_maxTotalPathLength_1757_);
lean_dec(v___x_1783_);
lean_dec_ref(v___x_1777_);
lean_del_object(v___x_1720_);
lean_dec_ref(v_config_1706_);
v___x_1804_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4));
v___x_1805_ = l_Nat_reprFast(v_maxTotalPathLength_1757_);
v___x_1806_ = lean_string_append(v___x_1804_, v___x_1805_);
lean_dec_ref(v___x_1805_);
v___x_1807_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5));
v___x_1808_ = lean_string_append(v___x_1806_, v___x_1807_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v___x_1808_);
v___x_1810_ = v___x_1770_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_object* v___x_1812_; 
if (v_isShared_1765_ == 0)
{
lean_ctor_set_tag(v___x_1764_, 1);
lean_ctor_set(v___x_1764_, 1, v___x_1810_);
v___x_1812_ = v___x_1764_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_pos_1761_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v___x_1810_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
}
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1821_; 
lean_inc(v_maxTotalPathLength_1757_);
lean_dec(v___x_1773_);
lean_dec(v_val_1768_);
lean_del_object(v___x_1720_);
lean_dec(v_fst_1717_);
lean_dec_ref(v_config_1706_);
v___x_1815_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4));
v___x_1816_ = l_Nat_reprFast(v_maxTotalPathLength_1757_);
v___x_1817_ = lean_string_append(v___x_1815_, v___x_1816_);
lean_dec_ref(v___x_1816_);
v___x_1818_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5));
v___x_1819_ = lean_string_append(v___x_1817_, v___x_1818_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v___x_1819_);
v___x_1821_ = v___x_1770_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1823_; 
if (v_isShared_1765_ == 0)
{
lean_ctor_set_tag(v___x_1764_, 1);
lean_ctor_set(v___x_1764_, 1, v___x_1821_);
v___x_1823_ = v___x_1764_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_pos_1761_);
lean_ctor_set(v_reuseFailAlloc_1824_, 1, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
}
else
{
lean_object* v___x_1827_; lean_object* v___x_1829_; 
lean_dec(v___x_1767_);
lean_dec(v_res_1762_);
lean_del_object(v___x_1720_);
lean_dec(v_snd_1718_);
lean_dec(v_fst_1717_);
lean_dec_ref(v_config_1706_);
v___x_1827_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__7));
if (v_isShared_1765_ == 0)
{
lean_ctor_set_tag(v___x_1764_, 1);
lean_ctor_set(v___x_1764_, 1, v___x_1827_);
v___x_1829_ = v___x_1764_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_pos_1761_);
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
}
else
{
lean_object* v_pos_1832_; lean_object* v_err_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
lean_del_object(v___x_1720_);
lean_dec(v_snd_1718_);
lean_dec(v_fst_1717_);
lean_dec_ref(v_config_1706_);
v_pos_1832_ = lean_ctor_get(v___x_1760_, 0);
v_err_1833_ = lean_ctor_get(v___x_1760_, 1);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1760_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_err_1833_);
lean_inc(v_pos_1832_);
lean_dec(v___x_1760_);
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
else
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
lean_inc(v_maxPathSegments_1756_);
lean_del_object(v___x_1720_);
lean_dec(v_snd_1718_);
lean_dec(v_fst_1717_);
lean_dec_ref(v_config_1706_);
v___x_1841_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1842_ = l_Nat_reprFast(v_maxPathSegments_1756_);
v___x_1843_ = lean_string_append(v___x_1841_, v___x_1842_);
lean_dec_ref(v___x_1842_);
v___x_1844_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1845_ = lean_string_append(v___x_1843_, v___x_1844_);
v___x_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
v___x_1847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___y_1708_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
return v___x_1847_;
}
}
v___jp_1848_:
{
if (v___y_1849_ == 0)
{
if (v___x_1723_ == 0)
{
goto v___jp_1755_;
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_del_object(v___x_1720_);
lean_dec_ref(v_config_1706_);
v___x_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1850_, 0, v_fst_1717_);
lean_ctor_set(v___x_1850_, 1, v_snd_1718_);
v___x_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___y_1708_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
return v___x_1851_;
}
}
else
{
goto v___jp_1755_;
}
}
v___jp_1853_:
{
if (v___x_1852_ == 0)
{
v___y_1849_ = v___y_1854_;
goto v___jp_1848_;
}
else
{
v___y_1849_ = v___x_1852_;
goto v___jp_1848_;
}
}
v___jp_1855_:
{
if (v___y_1856_ == 0)
{
uint8_t v___x_1857_; uint8_t v___x_1858_; 
v___x_1857_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1858_ = lean_uint8_dec_eq(v___x_1732_, v___x_1857_);
v___y_1854_ = v___x_1858_;
goto v___jp_1853_;
}
else
{
v___y_1854_ = v___y_1856_;
goto v___jp_1853_;
}
}
v___jp_1859_:
{
uint8_t v___x_1860_; uint8_t v___x_1861_; 
v___x_1860_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_1861_ = lean_uint8_dec_eq(v___x_1732_, v___x_1860_);
if (v___x_1861_ == 0)
{
uint8_t v___x_1862_; uint8_t v___x_1863_; 
v___x_1862_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_1863_ = lean_uint8_dec_eq(v___x_1732_, v___x_1862_);
if (v___x_1863_ == 0)
{
uint8_t v___x_1864_; uint8_t v___x_1865_; 
v___x_1864_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_1865_ = lean_uint8_dec_eq(v___x_1732_, v___x_1864_);
if (v___x_1865_ == 0)
{
uint8_t v___x_1866_; uint8_t v___x_1867_; 
v___x_1866_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_1867_ = lean_uint8_dec_eq(v___x_1732_, v___x_1866_);
if (v___x_1867_ == 0)
{
uint8_t v___x_1868_; uint8_t v___x_1869_; 
v___x_1868_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_1869_ = lean_uint8_dec_eq(v___x_1732_, v___x_1868_);
if (v___x_1869_ == 0)
{
uint8_t v___x_1870_; uint8_t v___x_1871_; 
v___x_1870_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_1871_ = lean_uint8_dec_eq(v___x_1732_, v___x_1870_);
if (v___x_1871_ == 0)
{
uint8_t v___x_1872_; uint8_t v___x_1873_; 
v___x_1872_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_1873_ = lean_uint8_dec_eq(v___x_1732_, v___x_1872_);
if (v___x_1873_ == 0)
{
uint8_t v___x_1874_; uint8_t v___x_1875_; 
v___x_1874_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_1875_ = lean_uint8_dec_eq(v___x_1732_, v___x_1874_);
if (v___x_1875_ == 0)
{
uint8_t v___x_1876_; uint8_t v___x_1877_; 
v___x_1876_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_1877_ = lean_uint8_dec_eq(v___x_1732_, v___x_1876_);
if (v___x_1877_ == 0)
{
uint8_t v___x_1878_; uint8_t v___x_1879_; 
v___x_1878_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_1879_ = lean_uint8_dec_eq(v___x_1732_, v___x_1878_);
if (v___x_1879_ == 0)
{
uint8_t v___x_1880_; uint8_t v___x_1881_; 
v___x_1880_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_1881_ = lean_uint8_dec_eq(v___x_1732_, v___x_1880_);
if (v___x_1881_ == 0)
{
uint8_t v___x_1882_; uint8_t v___x_1883_; 
v___x_1882_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_1883_ = lean_uint8_dec_eq(v___x_1732_, v___x_1882_);
if (v___x_1883_ == 0)
{
uint8_t v___x_1884_; uint8_t v___x_1885_; 
v___x_1884_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_1885_ = lean_uint8_dec_eq(v___x_1732_, v___x_1884_);
if (v___x_1885_ == 0)
{
uint8_t v___x_1886_; uint8_t v___x_1887_; 
v___x_1886_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_1887_ = lean_uint8_dec_eq(v___x_1732_, v___x_1886_);
if (v___x_1887_ == 0)
{
uint8_t v___x_1888_; uint8_t v___x_1889_; 
v___x_1888_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_1889_ = lean_uint8_dec_eq(v___x_1732_, v___x_1888_);
if (v___x_1889_ == 0)
{
uint8_t v___x_1890_; uint8_t v___x_1891_; 
v___x_1890_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_1891_ = lean_uint8_dec_eq(v___x_1732_, v___x_1890_);
if (v___x_1891_ == 0)
{
uint8_t v___x_1892_; uint8_t v___x_1893_; 
v___x_1892_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1893_ = lean_uint8_dec_eq(v___x_1732_, v___x_1892_);
v___y_1856_ = v___x_1893_;
goto v___jp_1855_;
}
else
{
v___y_1856_ = v___x_1891_;
goto v___jp_1855_;
}
}
else
{
v___y_1856_ = v___x_1889_;
goto v___jp_1855_;
}
}
else
{
v___y_1856_ = v___x_1887_;
goto v___jp_1855_;
}
}
else
{
v___y_1856_ = v___x_1885_;
goto v___jp_1855_;
}
}
else
{
v___y_1856_ = v___x_1883_;
goto v___jp_1855_;
}
}
else
{
v___y_1856_ = v___x_1881_;
goto v___jp_1855_;
}
}
else
{
v___y_1856_ = v___x_1879_;
goto v___jp_1855_;
}
}
else
{
v___y_1856_ = v___x_1877_;
goto v___jp_1855_;
}
}
else
{
v___y_1856_ = v___x_1875_;
goto v___jp_1855_;
}
}
else
{
v___y_1856_ = v___x_1873_;
goto v___jp_1855_;
}
}
else
{
v___y_1856_ = v___x_1871_;
goto v___jp_1855_;
}
}
else
{
v___y_1856_ = v___x_1869_;
goto v___jp_1855_;
}
}
else
{
v___y_1856_ = v___x_1867_;
goto v___jp_1855_;
}
}
else
{
v___y_1856_ = v___x_1865_;
goto v___jp_1855_;
}
}
else
{
v___y_1856_ = v___x_1863_;
goto v___jp_1855_;
}
}
else
{
v___y_1856_ = v___x_1861_;
goto v___jp_1855_;
}
}
v___jp_1894_:
{
uint8_t v___x_1895_; uint8_t v___x_1896_; 
v___x_1895_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_1896_ = lean_uint8_dec_le(v___x_1895_, v___x_1732_);
if (v___x_1896_ == 0)
{
goto v___jp_1859_;
}
else
{
uint8_t v___x_1897_; uint8_t v___x_1898_; 
v___x_1897_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_1898_ = lean_uint8_dec_le(v___x_1732_, v___x_1897_);
if (v___x_1898_ == 0)
{
goto v___jp_1859_;
}
else
{
v___y_1856_ = v___x_1898_;
goto v___jp_1855_;
}
}
}
v___jp_1899_:
{
uint8_t v___x_1900_; uint8_t v___x_1901_; 
v___x_1900_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_1901_ = lean_uint8_dec_le(v___x_1900_, v___x_1732_);
if (v___x_1901_ == 0)
{
goto v___jp_1894_;
}
else
{
uint8_t v___x_1902_; uint8_t v___x_1903_; 
v___x_1902_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_1903_ = lean_uint8_dec_le(v___x_1732_, v___x_1902_);
if (v___x_1903_ == 0)
{
goto v___jp_1894_;
}
else
{
v___y_1856_ = v___x_1903_;
goto v___jp_1855_;
}
}
}
}
else
{
lean_object* v___x_1909_; 
lean_dec_ref(v_config_1706_);
if (v_isShared_1721_ == 0)
{
v___x_1909_ = v___x_1720_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_fst_1717_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v_snd_1718_);
v___x_1909_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1910_; 
v___x_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___y_1708_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
return v___x_1910_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(lean_object* v_config_1913_, lean_object* v_a_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v_array_1922_; lean_object* v_idx_1923_; lean_object* v_fst_1924_; lean_object* v_snd_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_2119_; 
v_array_1922_ = lean_ctor_get(v___y_1915_, 0);
v_idx_1923_ = lean_ctor_get(v___y_1915_, 1);
v_fst_1924_ = lean_ctor_get(v_a_1914_, 0);
v_snd_1925_ = lean_ctor_get(v_a_1914_, 1);
v_isSharedCheck_2119_ = !lean_is_exclusive(v_a_1914_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_1927_ = v_a_1914_;
v_isShared_1928_ = v_isSharedCheck_2119_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_snd_1925_);
lean_inc(v_fst_1924_);
lean_dec(v_a_1914_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_2119_;
goto v_resetjp_1926_;
}
v___jp_1916_:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___y_1917_);
lean_ctor_set(v___x_1920_, 1, v___y_1918_);
v___x_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___y_1919_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
return v___x_1921_;
}
v_resetjp_1926_:
{
lean_object* v___x_1929_; uint8_t v___x_1930_; 
v___x_1929_ = lean_byte_array_size(v_array_1922_);
v___x_1930_ = lean_nat_dec_lt(v_idx_1923_, v___x_1929_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1932_; 
lean_dec_ref(v_config_1913_);
if (v_isShared_1928_ == 0)
{
v___x_1932_ = v___x_1927_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_fst_1924_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_snd_1925_);
v___x_1932_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1933_; 
v___x_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___y_1915_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
return v___x_1933_;
}
}
else
{
if (v___x_1930_ == 0)
{
lean_object* v___x_1936_; 
lean_dec_ref(v_config_1913_);
if (v_isShared_1928_ == 0)
{
v___x_1936_ = v___x_1927_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_fst_1924_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_snd_1925_);
v___x_1936_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1937_; 
v___x_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___y_1915_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
return v___x_1937_;
}
}
else
{
uint8_t v___x_1939_; uint8_t v___x_1940_; 
v___x_1939_ = lean_byte_array_fget(v_array_1922_, v_idx_1923_);
v___x_1940_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1939_);
if (v___x_1940_ == 0)
{
lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; uint8_t v___x_1961_; uint8_t v___y_2056_; uint8_t v___x_2059_; uint8_t v___y_2061_; uint8_t v___y_2063_; uint8_t v___x_2111_; uint8_t v___x_2112_; 
v___x_1961_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2059_ = lean_uint8_dec_eq(v___x_1939_, v___x_1961_);
v___x_2111_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_2112_ = lean_uint8_dec_le(v___x_2111_, v___x_1939_);
if (v___x_2112_ == 0)
{
goto v___jp_2106_;
}
else
{
uint8_t v___x_2113_; uint8_t v___x_2114_; 
v___x_2113_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_2114_ = lean_uint8_dec_le(v___x_1939_, v___x_2113_);
if (v___x_2114_ == 0)
{
goto v___jp_2106_;
}
else
{
v___y_2063_ = v___x_2114_;
goto v___jp_2062_;
}
}
v___jp_1941_:
{
lean_object* v___x_1946_; uint8_t v___x_1947_; 
v___x_1946_ = lean_array_get_size(v___y_1945_);
v___x_1947_ = lean_nat_dec_le(v___y_1944_, v___x_1946_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1951_; 
lean_dec(v___y_1944_);
v___x_1948_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1);
v___x_1949_ = lean_array_push(v___y_1945_, v___x_1948_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 1, v___y_1943_);
lean_ctor_set(v___x_1927_, 0, v___x_1949_);
v___x_1951_ = v___x_1927_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1949_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v___y_1943_);
v___x_1951_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
lean_object* v___x_1952_; 
v___x_1952_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1913_, v___x_1951_, v___y_1942_);
return v___x_1952_;
}
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1943_);
lean_del_object(v___x_1927_);
lean_dec_ref(v_config_1913_);
v___x_1954_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1955_ = l_Nat_reprFast(v___y_1944_);
v___x_1956_ = lean_string_append(v___x_1954_, v___x_1955_);
lean_dec_ref(v___x_1955_);
v___x_1957_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1958_ = lean_string_append(v___x_1956_, v___x_1957_);
v___x_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1958_);
v___x_1960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___y_1942_);
lean_ctor_set(v___x_1960_, 1, v___x_1959_);
return v___x_1960_;
}
}
v___jp_1962_:
{
lean_object* v_maxPathSegments_1963_; lean_object* v_maxTotalPathLength_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; 
v_maxPathSegments_1963_ = lean_ctor_get(v_config_1913_, 6);
v_maxTotalPathLength_1964_ = lean_ctor_get(v_config_1913_, 7);
v___x_1965_ = lean_array_get_size(v_fst_1924_);
v___x_1966_ = lean_nat_dec_le(v_maxPathSegments_1963_, v___x_1965_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; 
v___x_1967_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1913_, v___y_1915_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_pos_1968_; lean_object* v_res_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_2038_; 
v_pos_1968_ = lean_ctor_get(v___x_1967_, 0);
v_res_1969_ = lean_ctor_get(v___x_1967_, 1);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_1971_ = v___x_1967_;
v_isShared_1972_ = v_isSharedCheck_2038_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_res_1969_);
lean_inc(v_pos_1968_);
lean_dec(v___x_1967_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_2038_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
lean_inc(v_res_1969_);
v___x_1973_ = l_ByteSlice_toByteArray(v_res_1969_);
v___x_1974_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1973_);
if (lean_obj_tag(v___x_1974_) == 1)
{
lean_object* v_val_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_2033_; 
v_val_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_2033_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_val_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2033_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; 
v___x_1979_ = l_ByteSlice_size(v_res_1969_);
lean_dec(v_res_1969_);
v___x_1980_ = lean_nat_add(v_snd_1925_, v___x_1979_);
lean_dec(v___x_1979_);
lean_dec(v_snd_1925_);
v___x_1981_ = lean_nat_dec_lt(v_maxTotalPathLength_1964_, v___x_1980_);
if (v___x_1981_ == 0)
{
lean_object* v_array_1982_; lean_object* v_idx_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
v_array_1982_ = lean_ctor_get(v_pos_1968_, 0);
v_idx_1983_ = lean_ctor_get(v_pos_1968_, 1);
v___x_1984_ = lean_array_push(v_fst_1924_, v_val_1975_);
v___x_1985_ = lean_byte_array_size(v_array_1982_);
v___x_1986_ = lean_nat_dec_lt(v_idx_1983_, v___x_1985_);
if (v___x_1986_ == 0)
{
lean_del_object(v___x_1977_);
lean_del_object(v___x_1971_);
lean_del_object(v___x_1927_);
lean_dec_ref(v_config_1913_);
v___y_1917_ = v___x_1984_;
v___y_1918_ = v___x_1980_;
v___y_1919_ = v_pos_1968_;
goto v___jp_1916_;
}
else
{
uint8_t v___x_1987_; uint8_t v___x_1988_; 
v___x_1987_ = lean_byte_array_fget(v_array_1982_, v_idx_1983_);
v___x_1988_ = lean_uint8_dec_eq(v___x_1987_, v___x_1961_);
if (v___x_1988_ == 0)
{
lean_del_object(v___x_1977_);
lean_del_object(v___x_1971_);
lean_del_object(v___x_1927_);
lean_dec_ref(v_config_1913_);
v___y_1917_ = v___x_1984_;
v___y_1918_ = v___x_1980_;
v___y_1919_ = v_pos_1968_;
goto v___jp_1916_;
}
else
{
lean_object* v___x_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
v___x_1989_ = lean_unsigned_to_nat(1u);
v___x_1990_ = lean_nat_add(v___x_1980_, v___x_1989_);
lean_dec(v___x_1980_);
v___x_1991_ = lean_nat_dec_lt(v_maxTotalPathLength_1964_, v___x_1990_);
if (v___x_1991_ == 0)
{
lean_del_object(v___x_1977_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1992_; lean_object* v___x_1994_; 
lean_dec(v___x_1990_);
lean_dec_ref(v___x_1984_);
lean_del_object(v___x_1927_);
lean_dec_ref(v_config_1913_);
v___x_1992_ = lean_box(0);
if (v_isShared_1972_ == 0)
{
lean_ctor_set_tag(v___x_1971_, 1);
lean_ctor_set(v___x_1971_, 1, v___x_1992_);
v___x_1994_ = v___x_1971_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_pos_1968_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v___x_1992_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
else
{
lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2008_; 
lean_inc(v_idx_1983_);
lean_inc_ref(v_array_1982_);
lean_del_object(v___x_1971_);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_pos_1968_);
if (v_isSharedCheck_2008_ == 0)
{
lean_object* v_unused_2009_; lean_object* v_unused_2010_; 
v_unused_2009_ = lean_ctor_get(v_pos_1968_, 1);
lean_dec(v_unused_2009_);
v_unused_2010_ = lean_ctor_get(v_pos_1968_, 0);
lean_dec(v_unused_2010_);
v___x_1997_ = v_pos_1968_;
v_isShared_1998_ = v_isSharedCheck_2008_;
goto v_resetjp_1996_;
}
else
{
lean_dec(v_pos_1968_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2008_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v___x_2001_; 
v___x_1999_ = lean_nat_add(v_idx_1983_, v___x_1989_);
lean_dec(v_idx_1983_);
lean_inc(v___x_1999_);
lean_inc_ref(v_array_1982_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 1, v___x_1999_);
v___x_2001_ = v___x_1997_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_array_1982_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
uint8_t v___x_2002_; 
v___x_2002_ = lean_nat_dec_lt(v___x_1999_, v___x_1985_);
if (v___x_2002_ == 0)
{
lean_dec(v___x_1999_);
lean_dec_ref(v_array_1982_);
lean_inc(v_maxPathSegments_1963_);
v___y_1942_ = v___x_2001_;
v___y_1943_ = v___x_1990_;
v___y_1944_ = v_maxPathSegments_1963_;
v___y_1945_ = v___x_1984_;
goto v___jp_1941_;
}
else
{
uint8_t v___x_2003_; uint8_t v___x_2004_; 
v___x_2003_ = lean_byte_array_fget(v_array_1982_, v___x_1999_);
lean_dec(v___x_1999_);
lean_dec_ref(v_array_1982_);
v___x_2004_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_2003_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
lean_del_object(v___x_1927_);
v___x_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___x_1984_);
lean_ctor_set(v___x_2005_, 1, v___x_1990_);
v___x_2006_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1913_, v___x_2005_, v___x_2001_);
return v___x_2006_;
}
else
{
lean_inc(v_maxPathSegments_1963_);
v___y_1942_ = v___x_2001_;
v___y_1943_ = v___x_1990_;
v___y_1944_ = v_maxPathSegments_1963_;
v___y_1945_ = v___x_1984_;
goto v___jp_1941_;
}
}
}
}
}
}
else
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2017_; 
lean_inc(v_maxTotalPathLength_1964_);
lean_dec(v___x_1990_);
lean_dec_ref(v___x_1984_);
lean_del_object(v___x_1927_);
lean_dec_ref(v_config_1913_);
v___x_2011_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4));
v___x_2012_ = l_Nat_reprFast(v_maxTotalPathLength_1964_);
v___x_2013_ = lean_string_append(v___x_2011_, v___x_2012_);
lean_dec_ref(v___x_2012_);
v___x_2014_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5));
v___x_2015_ = lean_string_append(v___x_2013_, v___x_2014_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_2015_);
v___x_2017_ = v___x_1977_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
lean_object* v___x_2019_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set_tag(v___x_1971_, 1);
lean_ctor_set(v___x_1971_, 1, v___x_2017_);
v___x_2019_ = v___x_1971_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_pos_1968_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v___x_2017_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
}
}
else
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2028_; 
lean_inc(v_maxTotalPathLength_1964_);
lean_dec(v___x_1980_);
lean_dec(v_val_1975_);
lean_del_object(v___x_1927_);
lean_dec(v_fst_1924_);
lean_dec_ref(v_config_1913_);
v___x_2022_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4));
v___x_2023_ = l_Nat_reprFast(v_maxTotalPathLength_1964_);
v___x_2024_ = lean_string_append(v___x_2022_, v___x_2023_);
lean_dec_ref(v___x_2023_);
v___x_2025_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5));
v___x_2026_ = lean_string_append(v___x_2024_, v___x_2025_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_2026_);
v___x_2028_ = v___x_1977_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
lean_object* v___x_2030_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set_tag(v___x_1971_, 1);
lean_ctor_set(v___x_1971_, 1, v___x_2028_);
v___x_2030_ = v___x_1971_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_pos_1968_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
}
else
{
lean_object* v___x_2034_; lean_object* v___x_2036_; 
lean_dec(v___x_1974_);
lean_dec(v_res_1969_);
lean_del_object(v___x_1927_);
lean_dec(v_snd_1925_);
lean_dec(v_fst_1924_);
lean_dec_ref(v_config_1913_);
v___x_2034_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__7));
if (v_isShared_1972_ == 0)
{
lean_ctor_set_tag(v___x_1971_, 1);
lean_ctor_set(v___x_1971_, 1, v___x_2034_);
v___x_2036_ = v___x_1971_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_pos_1968_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
else
{
lean_object* v_pos_2039_; lean_object* v_err_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_del_object(v___x_1927_);
lean_dec(v_snd_1925_);
lean_dec(v_fst_1924_);
lean_dec_ref(v_config_1913_);
v_pos_2039_ = lean_ctor_get(v___x_1967_, 0);
v_err_2040_ = lean_ctor_get(v___x_1967_, 1);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_1967_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_err_2040_);
lean_inc(v_pos_2039_);
lean_dec(v___x_1967_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_pos_2039_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_err_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
else
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
lean_inc(v_maxPathSegments_1963_);
lean_del_object(v___x_1927_);
lean_dec(v_snd_1925_);
lean_dec(v_fst_1924_);
lean_dec_ref(v_config_1913_);
v___x_2048_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_2049_ = l_Nat_reprFast(v_maxPathSegments_1963_);
v___x_2050_ = lean_string_append(v___x_2048_, v___x_2049_);
lean_dec_ref(v___x_2049_);
v___x_2051_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_2052_ = lean_string_append(v___x_2050_, v___x_2051_);
v___x_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
v___x_2054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___y_1915_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
return v___x_2054_;
}
}
v___jp_2055_:
{
if (v___y_2056_ == 0)
{
if (v___x_1930_ == 0)
{
goto v___jp_1962_;
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
lean_del_object(v___x_1927_);
lean_dec_ref(v_config_1913_);
v___x_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2057_, 0, v_fst_1924_);
lean_ctor_set(v___x_2057_, 1, v_snd_1925_);
v___x_2058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___y_1915_);
lean_ctor_set(v___x_2058_, 1, v___x_2057_);
return v___x_2058_;
}
}
else
{
goto v___jp_1962_;
}
}
v___jp_2060_:
{
if (v___x_2059_ == 0)
{
v___y_2056_ = v___y_2061_;
goto v___jp_2055_;
}
else
{
v___y_2056_ = v___x_2059_;
goto v___jp_2055_;
}
}
v___jp_2062_:
{
if (v___y_2063_ == 0)
{
uint8_t v___x_2064_; uint8_t v___x_2065_; 
v___x_2064_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_2065_ = lean_uint8_dec_eq(v___x_1939_, v___x_2064_);
v___y_2061_ = v___x_2065_;
goto v___jp_2060_;
}
else
{
v___y_2061_ = v___y_2063_;
goto v___jp_2060_;
}
}
v___jp_2066_:
{
uint8_t v___x_2067_; uint8_t v___x_2068_; 
v___x_2067_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_2068_ = lean_uint8_dec_eq(v___x_1939_, v___x_2067_);
if (v___x_2068_ == 0)
{
uint8_t v___x_2069_; uint8_t v___x_2070_; 
v___x_2069_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_2070_ = lean_uint8_dec_eq(v___x_1939_, v___x_2069_);
if (v___x_2070_ == 0)
{
uint8_t v___x_2071_; uint8_t v___x_2072_; 
v___x_2071_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_2072_ = lean_uint8_dec_eq(v___x_1939_, v___x_2071_);
if (v___x_2072_ == 0)
{
uint8_t v___x_2073_; uint8_t v___x_2074_; 
v___x_2073_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_2074_ = lean_uint8_dec_eq(v___x_1939_, v___x_2073_);
if (v___x_2074_ == 0)
{
uint8_t v___x_2075_; uint8_t v___x_2076_; 
v___x_2075_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_2076_ = lean_uint8_dec_eq(v___x_1939_, v___x_2075_);
if (v___x_2076_ == 0)
{
uint8_t v___x_2077_; uint8_t v___x_2078_; 
v___x_2077_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_2078_ = lean_uint8_dec_eq(v___x_1939_, v___x_2077_);
if (v___x_2078_ == 0)
{
uint8_t v___x_2079_; uint8_t v___x_2080_; 
v___x_2079_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_2080_ = lean_uint8_dec_eq(v___x_1939_, v___x_2079_);
if (v___x_2080_ == 0)
{
uint8_t v___x_2081_; uint8_t v___x_2082_; 
v___x_2081_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_2082_ = lean_uint8_dec_eq(v___x_1939_, v___x_2081_);
if (v___x_2082_ == 0)
{
uint8_t v___x_2083_; uint8_t v___x_2084_; 
v___x_2083_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_2084_ = lean_uint8_dec_eq(v___x_1939_, v___x_2083_);
if (v___x_2084_ == 0)
{
uint8_t v___x_2085_; uint8_t v___x_2086_; 
v___x_2085_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_2086_ = lean_uint8_dec_eq(v___x_1939_, v___x_2085_);
if (v___x_2086_ == 0)
{
uint8_t v___x_2087_; uint8_t v___x_2088_; 
v___x_2087_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_2088_ = lean_uint8_dec_eq(v___x_1939_, v___x_2087_);
if (v___x_2088_ == 0)
{
uint8_t v___x_2089_; uint8_t v___x_2090_; 
v___x_2089_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_2090_ = lean_uint8_dec_eq(v___x_1939_, v___x_2089_);
if (v___x_2090_ == 0)
{
uint8_t v___x_2091_; uint8_t v___x_2092_; 
v___x_2091_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_2092_ = lean_uint8_dec_eq(v___x_1939_, v___x_2091_);
if (v___x_2092_ == 0)
{
uint8_t v___x_2093_; uint8_t v___x_2094_; 
v___x_2093_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_2094_ = lean_uint8_dec_eq(v___x_1939_, v___x_2093_);
if (v___x_2094_ == 0)
{
uint8_t v___x_2095_; uint8_t v___x_2096_; 
v___x_2095_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_2096_ = lean_uint8_dec_eq(v___x_1939_, v___x_2095_);
if (v___x_2096_ == 0)
{
uint8_t v___x_2097_; uint8_t v___x_2098_; 
v___x_2097_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_2098_ = lean_uint8_dec_eq(v___x_1939_, v___x_2097_);
if (v___x_2098_ == 0)
{
uint8_t v___x_2099_; uint8_t v___x_2100_; 
v___x_2099_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_2100_ = lean_uint8_dec_eq(v___x_1939_, v___x_2099_);
v___y_2063_ = v___x_2100_;
goto v___jp_2062_;
}
else
{
v___y_2063_ = v___x_2098_;
goto v___jp_2062_;
}
}
else
{
v___y_2063_ = v___x_2096_;
goto v___jp_2062_;
}
}
else
{
v___y_2063_ = v___x_2094_;
goto v___jp_2062_;
}
}
else
{
v___y_2063_ = v___x_2092_;
goto v___jp_2062_;
}
}
else
{
v___y_2063_ = v___x_2090_;
goto v___jp_2062_;
}
}
else
{
v___y_2063_ = v___x_2088_;
goto v___jp_2062_;
}
}
else
{
v___y_2063_ = v___x_2086_;
goto v___jp_2062_;
}
}
else
{
v___y_2063_ = v___x_2084_;
goto v___jp_2062_;
}
}
else
{
v___y_2063_ = v___x_2082_;
goto v___jp_2062_;
}
}
else
{
v___y_2063_ = v___x_2080_;
goto v___jp_2062_;
}
}
else
{
v___y_2063_ = v___x_2078_;
goto v___jp_2062_;
}
}
else
{
v___y_2063_ = v___x_2076_;
goto v___jp_2062_;
}
}
else
{
v___y_2063_ = v___x_2074_;
goto v___jp_2062_;
}
}
else
{
v___y_2063_ = v___x_2072_;
goto v___jp_2062_;
}
}
else
{
v___y_2063_ = v___x_2070_;
goto v___jp_2062_;
}
}
else
{
v___y_2063_ = v___x_2068_;
goto v___jp_2062_;
}
}
v___jp_2101_:
{
uint8_t v___x_2102_; uint8_t v___x_2103_; 
v___x_2102_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_2103_ = lean_uint8_dec_le(v___x_2102_, v___x_1939_);
if (v___x_2103_ == 0)
{
goto v___jp_2066_;
}
else
{
uint8_t v___x_2104_; uint8_t v___x_2105_; 
v___x_2104_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_2105_ = lean_uint8_dec_le(v___x_1939_, v___x_2104_);
if (v___x_2105_ == 0)
{
goto v___jp_2066_;
}
else
{
v___y_2063_ = v___x_2105_;
goto v___jp_2062_;
}
}
}
v___jp_2106_:
{
uint8_t v___x_2107_; uint8_t v___x_2108_; 
v___x_2107_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_2108_ = lean_uint8_dec_le(v___x_2107_, v___x_1939_);
if (v___x_2108_ == 0)
{
goto v___jp_2101_;
}
else
{
uint8_t v___x_2109_; uint8_t v___x_2110_; 
v___x_2109_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_2110_ = lean_uint8_dec_le(v___x_1939_, v___x_2109_);
if (v___x_2110_ == 0)
{
goto v___jp_2101_;
}
else
{
v___y_2063_ = v___x_2110_;
goto v___jp_2062_;
}
}
}
}
else
{
lean_object* v___x_2116_; 
lean_dec_ref(v_config_1913_);
if (v_isShared_1928_ == 0)
{
v___x_2116_ = v___x_1927_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_fst_1924_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v_snd_1925_);
v___x_2116_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
lean_object* v___x_2117_; 
v___x_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___y_1915_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
return v___x_2117_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath(lean_object* v_config_2131_, uint8_t v_forceAbsolute_2132_, uint8_t v_allowEmpty_2133_, lean_object* v_a_2134_){
_start:
{
lean_object* v___y_2136_; lean_object* v_array_2139_; lean_object* v_idx_2140_; uint8_t v_isAbsolute_2141_; lean_object* v___x_2142_; lean_object* v_segments_2143_; uint8_t v_isAbsolute_2145_; lean_object* v_totalLength_2146_; lean_object* v___y_2147_; lean_object* v___y_2171_; uint8_t v___y_2172_; lean_object* v___y_2176_; uint8_t v___y_2177_; uint8_t v___y_2178_; uint8_t v___y_2180_; lean_object* v_pos_2181_; uint8_t v_res_2182_; uint8_t v___y_2185_; lean_object* v_pos_2186_; uint8_t v_res_2187_; uint8_t v___y_2210_; lean_object* v___y_2211_; uint8_t v___y_2212_; uint8_t v___y_2221_; lean_object* v___y_2222_; uint8_t v___y_2223_; uint8_t v___y_2224_; uint8_t v___y_2228_; uint8_t v___y_2229_; uint8_t v___y_2230_; lean_object* v___y_2231_; uint8_t v___y_2232_; uint8_t v___y_2234_; lean_object* v___y_2235_; uint8_t v___y_2236_; uint8_t v___y_2237_; uint8_t v___y_2240_; lean_object* v_pos_2241_; uint8_t v_res_2242_; lean_object* v_pos_2245_; lean_object* v_array_2246_; lean_object* v_idx_2247_; uint8_t v_res_2248_; uint8_t v___y_2253_; uint8_t v___y_2254_; lean_object* v___x_2255_; uint8_t v___x_2256_; 
v_array_2139_ = lean_ctor_get(v_a_2134_, 0);
lean_inc_ref(v_array_2139_);
v_idx_2140_ = lean_ctor_get(v_a_2134_, 1);
lean_inc(v_idx_2140_);
v_isAbsolute_2141_ = 0;
v___x_2142_ = lean_unsigned_to_nat(0u);
v_segments_2143_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__2));
v___x_2255_ = lean_byte_array_size(v_array_2139_);
v___x_2256_ = lean_nat_dec_lt(v_idx_2140_, v___x_2255_);
if (v___x_2256_ == 0)
{
v_pos_2245_ = v_a_2134_;
v_array_2246_ = v_array_2139_;
v_idx_2247_ = v_idx_2140_;
v_res_2248_ = v_isAbsolute_2141_;
goto v___jp_2244_;
}
else
{
uint8_t v___x_2257_; uint8_t v___y_2259_; uint8_t v___x_2309_; uint8_t v___x_2310_; 
v___x_2257_ = lean_byte_array_fget(v_array_2139_, v_idx_2140_);
v___x_2309_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_2310_ = lean_uint8_dec_le(v___x_2309_, v___x_2257_);
if (v___x_2310_ == 0)
{
goto v___jp_2304_;
}
else
{
uint8_t v___x_2311_; uint8_t v___x_2312_; 
v___x_2311_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_2312_ = lean_uint8_dec_le(v___x_2257_, v___x_2311_);
if (v___x_2312_ == 0)
{
goto v___jp_2304_;
}
else
{
v___y_2259_ = v___x_2312_;
goto v___jp_2258_;
}
}
v___jp_2258_:
{
uint8_t v___x_2260_; uint8_t v___x_2261_; 
v___x_2260_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_2261_ = lean_uint8_dec_eq(v___x_2257_, v___x_2260_);
if (v___x_2261_ == 0)
{
uint8_t v___x_2262_; uint8_t v___x_2263_; 
v___x_2262_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2263_ = lean_uint8_dec_eq(v___x_2257_, v___x_2262_);
v___y_2253_ = v___y_2259_;
v___y_2254_ = v___x_2263_;
goto v___jp_2252_;
}
else
{
v___y_2253_ = v___y_2259_;
v___y_2254_ = v___x_2261_;
goto v___jp_2252_;
}
}
v___jp_2264_:
{
uint8_t v___x_2265_; uint8_t v___x_2266_; 
v___x_2265_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_2266_ = lean_uint8_dec_eq(v___x_2257_, v___x_2265_);
if (v___x_2266_ == 0)
{
uint8_t v___x_2267_; uint8_t v___x_2268_; 
v___x_2267_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_2268_ = lean_uint8_dec_eq(v___x_2257_, v___x_2267_);
if (v___x_2268_ == 0)
{
uint8_t v___x_2269_; uint8_t v___x_2270_; 
v___x_2269_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_2270_ = lean_uint8_dec_eq(v___x_2257_, v___x_2269_);
if (v___x_2270_ == 0)
{
uint8_t v___x_2271_; uint8_t v___x_2272_; 
v___x_2271_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_2272_ = lean_uint8_dec_eq(v___x_2257_, v___x_2271_);
if (v___x_2272_ == 0)
{
uint8_t v___x_2273_; uint8_t v___x_2274_; 
v___x_2273_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_2274_ = lean_uint8_dec_eq(v___x_2257_, v___x_2273_);
if (v___x_2274_ == 0)
{
uint8_t v___x_2275_; uint8_t v___x_2276_; 
v___x_2275_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_2276_ = lean_uint8_dec_eq(v___x_2257_, v___x_2275_);
if (v___x_2276_ == 0)
{
uint8_t v___x_2277_; uint8_t v___x_2278_; 
v___x_2277_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_2278_ = lean_uint8_dec_eq(v___x_2257_, v___x_2277_);
if (v___x_2278_ == 0)
{
uint8_t v___x_2279_; uint8_t v___x_2280_; 
v___x_2279_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_2280_ = lean_uint8_dec_eq(v___x_2257_, v___x_2279_);
if (v___x_2280_ == 0)
{
uint8_t v___x_2281_; uint8_t v___x_2282_; 
v___x_2281_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_2282_ = lean_uint8_dec_eq(v___x_2257_, v___x_2281_);
if (v___x_2282_ == 0)
{
uint8_t v___x_2283_; uint8_t v___x_2284_; 
v___x_2283_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_2284_ = lean_uint8_dec_eq(v___x_2257_, v___x_2283_);
if (v___x_2284_ == 0)
{
uint8_t v___x_2285_; uint8_t v___x_2286_; 
v___x_2285_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_2286_ = lean_uint8_dec_eq(v___x_2257_, v___x_2285_);
if (v___x_2286_ == 0)
{
uint8_t v___x_2287_; uint8_t v___x_2288_; 
v___x_2287_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_2288_ = lean_uint8_dec_eq(v___x_2257_, v___x_2287_);
if (v___x_2288_ == 0)
{
uint8_t v___x_2289_; uint8_t v___x_2290_; 
v___x_2289_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_2290_ = lean_uint8_dec_eq(v___x_2257_, v___x_2289_);
if (v___x_2290_ == 0)
{
uint8_t v___x_2291_; uint8_t v___x_2292_; 
v___x_2291_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_2292_ = lean_uint8_dec_eq(v___x_2257_, v___x_2291_);
if (v___x_2292_ == 0)
{
uint8_t v___x_2293_; uint8_t v___x_2294_; 
v___x_2293_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_2294_ = lean_uint8_dec_eq(v___x_2257_, v___x_2293_);
if (v___x_2294_ == 0)
{
uint8_t v___x_2295_; uint8_t v___x_2296_; 
v___x_2295_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_2296_ = lean_uint8_dec_eq(v___x_2257_, v___x_2295_);
if (v___x_2296_ == 0)
{
uint8_t v___x_2297_; uint8_t v___x_2298_; 
v___x_2297_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_2298_ = lean_uint8_dec_eq(v___x_2257_, v___x_2297_);
v___y_2259_ = v___x_2298_;
goto v___jp_2258_;
}
else
{
v___y_2259_ = v___x_2296_;
goto v___jp_2258_;
}
}
else
{
v___y_2259_ = v___x_2294_;
goto v___jp_2258_;
}
}
else
{
v___y_2259_ = v___x_2292_;
goto v___jp_2258_;
}
}
else
{
v___y_2259_ = v___x_2290_;
goto v___jp_2258_;
}
}
else
{
v___y_2259_ = v___x_2288_;
goto v___jp_2258_;
}
}
else
{
v___y_2259_ = v___x_2286_;
goto v___jp_2258_;
}
}
else
{
v___y_2259_ = v___x_2284_;
goto v___jp_2258_;
}
}
else
{
v___y_2259_ = v___x_2282_;
goto v___jp_2258_;
}
}
else
{
v___y_2259_ = v___x_2280_;
goto v___jp_2258_;
}
}
else
{
v___y_2259_ = v___x_2278_;
goto v___jp_2258_;
}
}
else
{
v___y_2259_ = v___x_2276_;
goto v___jp_2258_;
}
}
else
{
v___y_2259_ = v___x_2274_;
goto v___jp_2258_;
}
}
else
{
v___y_2259_ = v___x_2272_;
goto v___jp_2258_;
}
}
else
{
v___y_2259_ = v___x_2270_;
goto v___jp_2258_;
}
}
else
{
v___y_2259_ = v___x_2268_;
goto v___jp_2258_;
}
}
else
{
v___y_2259_ = v___x_2266_;
goto v___jp_2258_;
}
}
v___jp_2299_:
{
uint8_t v___x_2300_; uint8_t v___x_2301_; 
v___x_2300_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_2301_ = lean_uint8_dec_le(v___x_2300_, v___x_2257_);
if (v___x_2301_ == 0)
{
goto v___jp_2264_;
}
else
{
uint8_t v___x_2302_; uint8_t v___x_2303_; 
v___x_2302_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_2303_ = lean_uint8_dec_le(v___x_2257_, v___x_2302_);
if (v___x_2303_ == 0)
{
goto v___jp_2264_;
}
else
{
v___y_2259_ = v___x_2303_;
goto v___jp_2258_;
}
}
}
v___jp_2304_:
{
uint8_t v___x_2305_; uint8_t v___x_2306_; 
v___x_2305_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_2306_ = lean_uint8_dec_le(v___x_2305_, v___x_2257_);
if (v___x_2306_ == 0)
{
goto v___jp_2299_;
}
else
{
uint8_t v___x_2307_; uint8_t v___x_2308_; 
v___x_2307_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_2308_ = lean_uint8_dec_le(v___x_2257_, v___x_2307_);
if (v___x_2308_ == 0)
{
goto v___jp_2299_;
}
else
{
v___y_2259_ = v___x_2308_;
goto v___jp_2258_;
}
}
}
}
v___jp_2135_:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__1));
v___x_2138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___y_2136_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
return v___x_2138_;
}
v___jp_2144_:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2148_, 0, v_segments_2143_);
lean_ctor_set(v___x_2148_, 1, v_totalLength_2146_);
v___x_2149_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(v_config_2131_, v___x_2148_, v___y_2147_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_res_2150_; lean_object* v_pos_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2160_; 
v_res_2150_ = lean_ctor_get(v___x_2149_, 1);
v_pos_2151_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2153_ = v___x_2149_;
v_isShared_2154_ = v_isSharedCheck_2160_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_res_2150_);
lean_inc(v_pos_2151_);
lean_dec(v___x_2149_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2160_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v_fst_2155_; lean_object* v___x_2156_; lean_object* v___x_2158_; 
v_fst_2155_ = lean_ctor_get(v_res_2150_, 0);
lean_inc(v_fst_2155_);
lean_dec(v_res_2150_);
v___x_2156_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2156_, 0, v_fst_2155_);
lean_ctor_set_uint8(v___x_2156_, sizeof(void*)*1, v_isAbsolute_2145_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 1, v___x_2156_);
v___x_2158_ = v___x_2153_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_pos_2151_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
else
{
lean_object* v_pos_2161_; lean_object* v_err_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
v_pos_2161_ = lean_ctor_get(v___x_2149_, 0);
v_err_2162_ = lean_ctor_get(v___x_2149_, 1);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2149_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_err_2162_);
lean_inc(v_pos_2161_);
lean_dec(v___x_2149_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_pos_2161_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v_err_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
v___jp_2170_:
{
if (v_allowEmpty_2133_ == 0)
{
v___y_2136_ = v___y_2171_;
goto v___jp_2135_;
}
else
{
if (v___y_2172_ == 0)
{
v___y_2136_ = v___y_2171_;
goto v___jp_2135_;
}
else
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__3));
v___x_2174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___y_2171_);
lean_ctor_set(v___x_2174_, 1, v___x_2173_);
return v___x_2174_;
}
}
}
v___jp_2175_:
{
if (v___y_2177_ == 0)
{
v___y_2171_ = v___y_2176_;
v___y_2172_ = v___y_2178_;
goto v___jp_2170_;
}
else
{
v___y_2171_ = v___y_2176_;
v___y_2172_ = v___y_2177_;
goto v___jp_2170_;
}
}
v___jp_2179_:
{
if (v___y_2180_ == 0)
{
uint8_t v___x_2183_; 
v___x_2183_ = 1;
v___y_2176_ = v_pos_2181_;
v___y_2177_ = v_res_2182_;
v___y_2178_ = v___x_2183_;
goto v___jp_2175_;
}
else
{
v___y_2176_ = v_pos_2181_;
v___y_2177_ = v_res_2182_;
v___y_2178_ = v_isAbsolute_2141_;
goto v___jp_2175_;
}
}
v___jp_2184_:
{
if (v_res_2187_ == 0)
{
if (v_forceAbsolute_2132_ == 0)
{
v_isAbsolute_2145_ = v_isAbsolute_2141_;
v_totalLength_2146_ = v___x_2142_;
v___y_2147_ = v_pos_2186_;
goto v___jp_2144_;
}
else
{
lean_object* v_array_2188_; lean_object* v_idx_2189_; lean_object* v___x_2190_; uint8_t v___x_2191_; 
lean_dec_ref(v_config_2131_);
v_array_2188_ = lean_ctor_get(v_pos_2186_, 0);
v_idx_2189_ = lean_ctor_get(v_pos_2186_, 1);
v___x_2190_ = lean_byte_array_size(v_array_2188_);
v___x_2191_ = lean_nat_dec_lt(v_idx_2189_, v___x_2190_);
if (v___x_2191_ == 0)
{
v___y_2180_ = v___y_2185_;
v_pos_2181_ = v_pos_2186_;
v_res_2182_ = v_forceAbsolute_2132_;
goto v___jp_2179_;
}
else
{
v___y_2180_ = v___y_2185_;
v_pos_2181_ = v_pos_2186_;
v_res_2182_ = v_res_2187_;
goto v___jp_2179_;
}
}
}
else
{
lean_object* v_array_2192_; lean_object* v_idx_2193_; lean_object* v___x_2194_; uint8_t v___x_2195_; 
v_array_2192_ = lean_ctor_get(v_pos_2186_, 0);
v_idx_2193_ = lean_ctor_get(v_pos_2186_, 1);
v___x_2194_ = lean_byte_array_size(v_array_2192_);
v___x_2195_ = lean_nat_dec_lt(v_idx_2193_, v___x_2194_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_dec_ref(v_config_2131_);
v___x_2196_ = lean_box(0);
v___x_2197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2197_, 0, v_pos_2186_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
return v___x_2197_;
}
else
{
lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2206_; 
lean_inc(v_idx_2193_);
lean_inc_ref(v_array_2192_);
v_isSharedCheck_2206_ = !lean_is_exclusive(v_pos_2186_);
if (v_isSharedCheck_2206_ == 0)
{
lean_object* v_unused_2207_; lean_object* v_unused_2208_; 
v_unused_2207_ = lean_ctor_get(v_pos_2186_, 1);
lean_dec(v_unused_2207_);
v_unused_2208_ = lean_ctor_get(v_pos_2186_, 0);
lean_dec(v_unused_2208_);
v___x_2199_ = v_pos_2186_;
v_isShared_2200_ = v_isSharedCheck_2206_;
goto v_resetjp_2198_;
}
else
{
lean_dec(v_pos_2186_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2206_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2204_; 
v___x_2201_ = lean_unsigned_to_nat(1u);
v___x_2202_ = lean_nat_add(v_idx_2193_, v___x_2201_);
lean_dec(v_idx_2193_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 1, v___x_2202_);
v___x_2204_ = v___x_2199_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_array_2192_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v___x_2202_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
v_isAbsolute_2145_ = v___x_2195_;
v_totalLength_2146_ = v___x_2201_;
v___y_2147_ = v___x_2204_;
goto v___jp_2144_;
}
}
}
}
}
v___jp_2209_:
{
lean_object* v_array_2213_; lean_object* v_idx_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; 
v_array_2213_ = lean_ctor_get(v___y_2211_, 0);
v_idx_2214_ = lean_ctor_get(v___y_2211_, 1);
v___x_2215_ = lean_byte_array_size(v_array_2213_);
v___x_2216_ = lean_nat_dec_lt(v_idx_2214_, v___x_2215_);
if (v___x_2216_ == 0)
{
v___y_2185_ = v___y_2210_;
v_pos_2186_ = v___y_2211_;
v_res_2187_ = v___y_2212_;
goto v___jp_2184_;
}
else
{
uint8_t v___x_2217_; uint8_t v___x_2218_; uint8_t v___x_2219_; 
v___x_2217_ = lean_byte_array_fget(v_array_2213_, v_idx_2214_);
v___x_2218_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2219_ = lean_uint8_dec_eq(v___x_2217_, v___x_2218_);
if (v___x_2219_ == 0)
{
v___y_2185_ = v___y_2210_;
v_pos_2186_ = v___y_2211_;
v_res_2187_ = v___y_2212_;
goto v___jp_2184_;
}
else
{
v___y_2185_ = v___y_2210_;
v_pos_2186_ = v___y_2211_;
v_res_2187_ = v___x_2219_;
goto v___jp_2184_;
}
}
}
v___jp_2220_:
{
if (v___y_2221_ == 0)
{
v___y_2210_ = v___y_2223_;
v___y_2211_ = v___y_2222_;
v___y_2212_ = v___y_2221_;
goto v___jp_2209_;
}
else
{
if (v___y_2224_ == 0)
{
v___y_2210_ = v___y_2223_;
v___y_2211_ = v___y_2222_;
v___y_2212_ = v___y_2224_;
goto v___jp_2209_;
}
else
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
lean_dec_ref(v_config_2131_);
v___x_2225_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__5));
v___x_2226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2226_, 0, v___y_2222_);
lean_ctor_set(v___x_2226_, 1, v___x_2225_);
return v___x_2226_;
}
}
}
v___jp_2227_:
{
if (v___y_2228_ == 0)
{
v___y_2221_ = v___y_2229_;
v___y_2222_ = v___y_2231_;
v___y_2223_ = v___y_2230_;
v___y_2224_ = v___y_2232_;
goto v___jp_2220_;
}
else
{
v___y_2221_ = v___y_2229_;
v___y_2222_ = v___y_2231_;
v___y_2223_ = v___y_2230_;
v___y_2224_ = v___y_2228_;
goto v___jp_2220_;
}
}
v___jp_2233_:
{
if (v___y_2236_ == 0)
{
uint8_t v___x_2238_; 
v___x_2238_ = 1;
v___y_2228_ = v___y_2234_;
v___y_2229_ = v___y_2237_;
v___y_2230_ = v___y_2236_;
v___y_2231_ = v___y_2235_;
v___y_2232_ = v___x_2238_;
goto v___jp_2227_;
}
else
{
v___y_2228_ = v___y_2234_;
v___y_2229_ = v___y_2237_;
v___y_2230_ = v___y_2236_;
v___y_2231_ = v___y_2235_;
v___y_2232_ = v_isAbsolute_2141_;
goto v___jp_2227_;
}
}
v___jp_2239_:
{
if (v_allowEmpty_2133_ == 0)
{
uint8_t v___x_2243_; 
v___x_2243_ = 1;
v___y_2234_ = v_res_2242_;
v___y_2235_ = v_pos_2241_;
v___y_2236_ = v___y_2240_;
v___y_2237_ = v___x_2243_;
goto v___jp_2233_;
}
else
{
v___y_2234_ = v_res_2242_;
v___y_2235_ = v_pos_2241_;
v___y_2236_ = v___y_2240_;
v___y_2237_ = v_isAbsolute_2141_;
goto v___jp_2233_;
}
}
v___jp_2244_:
{
lean_object* v___x_2249_; uint8_t v___x_2250_; 
v___x_2249_ = lean_byte_array_size(v_array_2246_);
lean_dec_ref(v_array_2246_);
v___x_2250_ = lean_nat_dec_lt(v_idx_2247_, v___x_2249_);
lean_dec(v_idx_2247_);
if (v___x_2250_ == 0)
{
uint8_t v___x_2251_; 
v___x_2251_ = 1;
v___y_2240_ = v_res_2248_;
v_pos_2241_ = v_pos_2245_;
v_res_2242_ = v___x_2251_;
goto v___jp_2239_;
}
else
{
v___y_2240_ = v_res_2248_;
v_pos_2241_ = v_pos_2245_;
v_res_2242_ = v_isAbsolute_2141_;
goto v___jp_2239_;
}
}
v___jp_2252_:
{
if (v___y_2253_ == 0)
{
if (v___y_2254_ == 0)
{
v_pos_2245_ = v_a_2134_;
v_array_2246_ = v_array_2139_;
v_idx_2247_ = v_idx_2140_;
v_res_2248_ = v_isAbsolute_2141_;
goto v___jp_2244_;
}
else
{
v_pos_2245_ = v_a_2134_;
v_array_2246_ = v_array_2139_;
v_idx_2247_ = v_idx_2140_;
v_res_2248_ = v___y_2254_;
goto v___jp_2244_;
}
}
else
{
v_pos_2245_ = v_a_2134_;
v_array_2246_ = v_array_2139_;
v_idx_2247_ = v_idx_2140_;
v_res_2248_ = v___y_2253_;
goto v___jp_2244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath___boxed(lean_object* v_config_2313_, lean_object* v_forceAbsolute_2314_, lean_object* v_allowEmpty_2315_, lean_object* v_a_2316_){
_start:
{
uint8_t v_forceAbsolute_boxed_2317_; uint8_t v_allowEmpty_boxed_2318_; lean_object* v_res_2319_; 
v_forceAbsolute_boxed_2317_ = lean_unbox(v_forceAbsolute_2314_);
v_allowEmpty_boxed_2318_ = lean_unbox(v_allowEmpty_2315_);
v_res_2319_ = l_Std_Http_URI_Parser_parsePath(v_config_2313_, v_forceAbsolute_boxed_2317_, v_allowEmpty_boxed_2318_, v_a_2316_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0(lean_object* v_config_2320_, lean_object* v_inst_2321_, lean_object* v_a_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(v_config_2320_, v_a_2322_, v___y_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(lean_object* v_config_2325_, lean_object* v_inst_2326_, lean_object* v_a_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_2325_, v_a_2327_, v___y_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(lean_object* v_s_2330_){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0));
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___boxed(lean_object* v_s_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(v_s_2332_);
lean_dec_ref(v_s_2332_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(lean_object* v_s_2334_){
_start:
{
lean_object* v___x_2335_; 
v___x_2335_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0));
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___boxed(lean_object* v_s_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v_s_2336_);
lean_dec_ref(v_s_2336_);
return v_res_2337_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(uint8_t v_c_2338_){
_start:
{
uint8_t v___y_2340_; uint8_t v___x_2392_; uint8_t v___x_2393_; 
v___x_2392_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_2393_ = lean_uint8_dec_le(v___x_2392_, v_c_2338_);
if (v___x_2393_ == 0)
{
goto v___jp_2387_;
}
else
{
uint8_t v___x_2394_; uint8_t v___x_2395_; 
v___x_2394_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_2395_ = lean_uint8_dec_le(v_c_2338_, v___x_2394_);
if (v___x_2395_ == 0)
{
goto v___jp_2387_;
}
else
{
v___y_2340_ = v___x_2395_;
goto v___jp_2339_;
}
}
v___jp_2339_:
{
if (v___y_2340_ == 0)
{
uint8_t v___x_2341_; uint8_t v___x_2342_; 
v___x_2341_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_2342_ = lean_uint8_dec_eq(v_c_2338_, v___x_2341_);
return v___x_2342_;
}
else
{
return v___y_2340_;
}
}
v___jp_2343_:
{
uint8_t v___x_2344_; uint8_t v___x_2345_; 
v___x_2344_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_2345_ = lean_uint8_dec_eq(v_c_2338_, v___x_2344_);
if (v___x_2345_ == 0)
{
uint8_t v___x_2346_; uint8_t v___x_2347_; 
v___x_2346_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_2347_ = lean_uint8_dec_eq(v_c_2338_, v___x_2346_);
if (v___x_2347_ == 0)
{
uint8_t v___x_2348_; uint8_t v___x_2349_; 
v___x_2348_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_2349_ = lean_uint8_dec_eq(v_c_2338_, v___x_2348_);
if (v___x_2349_ == 0)
{
uint8_t v___x_2350_; uint8_t v___x_2351_; 
v___x_2350_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_2351_ = lean_uint8_dec_eq(v_c_2338_, v___x_2350_);
if (v___x_2351_ == 0)
{
uint8_t v___x_2352_; uint8_t v___x_2353_; 
v___x_2352_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_2353_ = lean_uint8_dec_eq(v_c_2338_, v___x_2352_);
if (v___x_2353_ == 0)
{
uint8_t v___x_2354_; uint8_t v___x_2355_; 
v___x_2354_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_2355_ = lean_uint8_dec_eq(v_c_2338_, v___x_2354_);
if (v___x_2355_ == 0)
{
uint8_t v___x_2356_; uint8_t v___x_2357_; 
v___x_2356_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_2357_ = lean_uint8_dec_eq(v_c_2338_, v___x_2356_);
if (v___x_2357_ == 0)
{
uint8_t v___x_2358_; uint8_t v___x_2359_; 
v___x_2358_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_2359_ = lean_uint8_dec_eq(v_c_2338_, v___x_2358_);
if (v___x_2359_ == 0)
{
uint8_t v___x_2360_; uint8_t v___x_2361_; 
v___x_2360_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_2361_ = lean_uint8_dec_eq(v_c_2338_, v___x_2360_);
if (v___x_2361_ == 0)
{
uint8_t v___x_2362_; uint8_t v___x_2363_; 
v___x_2362_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_2363_ = lean_uint8_dec_eq(v_c_2338_, v___x_2362_);
if (v___x_2363_ == 0)
{
uint8_t v___x_2364_; uint8_t v___x_2365_; 
v___x_2364_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_2365_ = lean_uint8_dec_eq(v_c_2338_, v___x_2364_);
if (v___x_2365_ == 0)
{
uint8_t v___x_2366_; uint8_t v___x_2367_; 
v___x_2366_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_2367_ = lean_uint8_dec_eq(v_c_2338_, v___x_2366_);
if (v___x_2367_ == 0)
{
uint8_t v___x_2368_; uint8_t v___x_2369_; 
v___x_2368_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_2369_ = lean_uint8_dec_eq(v_c_2338_, v___x_2368_);
if (v___x_2369_ == 0)
{
uint8_t v___x_2370_; uint8_t v___x_2371_; 
v___x_2370_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_2371_ = lean_uint8_dec_eq(v_c_2338_, v___x_2370_);
if (v___x_2371_ == 0)
{
uint8_t v___x_2372_; uint8_t v___x_2373_; 
v___x_2372_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_2373_ = lean_uint8_dec_eq(v_c_2338_, v___x_2372_);
if (v___x_2373_ == 0)
{
uint8_t v___x_2374_; uint8_t v___x_2375_; 
v___x_2374_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_2375_ = lean_uint8_dec_eq(v_c_2338_, v___x_2374_);
if (v___x_2375_ == 0)
{
uint8_t v___x_2376_; uint8_t v___x_2377_; 
v___x_2376_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_2377_ = lean_uint8_dec_eq(v_c_2338_, v___x_2376_);
if (v___x_2377_ == 0)
{
uint8_t v___x_2378_; uint8_t v___x_2379_; 
v___x_2378_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2379_ = lean_uint8_dec_eq(v_c_2338_, v___x_2378_);
if (v___x_2379_ == 0)
{
uint8_t v___x_2380_; uint8_t v___x_2381_; 
v___x_2380_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_2381_ = lean_uint8_dec_eq(v_c_2338_, v___x_2380_);
v___y_2340_ = v___x_2381_;
goto v___jp_2339_;
}
else
{
v___y_2340_ = v___x_2379_;
goto v___jp_2339_;
}
}
else
{
v___y_2340_ = v___x_2377_;
goto v___jp_2339_;
}
}
else
{
v___y_2340_ = v___x_2375_;
goto v___jp_2339_;
}
}
else
{
v___y_2340_ = v___x_2373_;
goto v___jp_2339_;
}
}
else
{
v___y_2340_ = v___x_2371_;
goto v___jp_2339_;
}
}
else
{
v___y_2340_ = v___x_2369_;
goto v___jp_2339_;
}
}
else
{
v___y_2340_ = v___x_2367_;
goto v___jp_2339_;
}
}
else
{
v___y_2340_ = v___x_2365_;
goto v___jp_2339_;
}
}
else
{
v___y_2340_ = v___x_2363_;
goto v___jp_2339_;
}
}
else
{
v___y_2340_ = v___x_2361_;
goto v___jp_2339_;
}
}
else
{
v___y_2340_ = v___x_2359_;
goto v___jp_2339_;
}
}
else
{
v___y_2340_ = v___x_2357_;
goto v___jp_2339_;
}
}
else
{
v___y_2340_ = v___x_2355_;
goto v___jp_2339_;
}
}
else
{
v___y_2340_ = v___x_2353_;
goto v___jp_2339_;
}
}
else
{
v___y_2340_ = v___x_2351_;
goto v___jp_2339_;
}
}
else
{
v___y_2340_ = v___x_2349_;
goto v___jp_2339_;
}
}
else
{
v___y_2340_ = v___x_2347_;
goto v___jp_2339_;
}
}
else
{
v___y_2340_ = v___x_2345_;
goto v___jp_2339_;
}
}
v___jp_2382_:
{
uint8_t v___x_2383_; uint8_t v___x_2384_; 
v___x_2383_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_2384_ = lean_uint8_dec_le(v___x_2383_, v_c_2338_);
if (v___x_2384_ == 0)
{
goto v___jp_2343_;
}
else
{
uint8_t v___x_2385_; uint8_t v___x_2386_; 
v___x_2385_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_2386_ = lean_uint8_dec_le(v_c_2338_, v___x_2385_);
if (v___x_2386_ == 0)
{
goto v___jp_2343_;
}
else
{
v___y_2340_ = v___x_2386_;
goto v___jp_2339_;
}
}
}
v___jp_2387_:
{
uint8_t v___x_2388_; uint8_t v___x_2389_; 
v___x_2388_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_2389_ = lean_uint8_dec_le(v___x_2388_, v_c_2338_);
if (v___x_2389_ == 0)
{
goto v___jp_2382_;
}
else
{
uint8_t v___x_2390_; uint8_t v___x_2391_; 
v___x_2390_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_2391_ = lean_uint8_dec_le(v_c_2338_, v___x_2390_);
if (v___x_2391_ == 0)
{
goto v___jp_2382_;
}
else
{
v___y_2340_ = v___x_2391_;
goto v___jp_2339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed(lean_object* v_c_2396_){
_start:
{
uint8_t v_c_boxed_2397_; uint8_t v_res_2398_; lean_object* v_r_2399_; 
v_c_boxed_2397_ = lean_unbox(v_c_2396_);
v_res_2398_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(v_c_boxed_2397_);
v_r_2399_ = lean_box(v_res_2398_);
return v_r_2399_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(lean_object* v___x_2400_, lean_object* v___x_2401_, lean_object* v_a_2402_, lean_object* v_b_2403_){
_start:
{
lean_object* v_it_2405_; 
if (lean_obj_tag(v_a_2402_) == 0)
{
lean_object* v_currPos_2409_; lean_object* v_searcher_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2436_; 
v_currPos_2409_ = lean_ctor_get(v_a_2402_, 0);
v_searcher_2410_ = lean_ctor_get(v_a_2402_, 1);
v_isSharedCheck_2436_ = !lean_is_exclusive(v_a_2402_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2412_ = v_a_2402_;
v_isShared_2413_ = v_isSharedCheck_2436_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_searcher_2410_);
lean_inc(v_currPos_2409_);
lean_dec(v_a_2402_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2436_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v_str_2414_; lean_object* v_startInclusive_2415_; lean_object* v_endExclusive_2416_; lean_object* v___x_2417_; uint8_t v_decide_2418_; 
v_str_2414_ = lean_ctor_get(v___x_2400_, 0);
v_startInclusive_2415_ = lean_ctor_get(v___x_2400_, 1);
v_endExclusive_2416_ = lean_ctor_get(v___x_2400_, 2);
v___x_2417_ = lean_nat_sub(v_endExclusive_2416_, v_startInclusive_2415_);
v_decide_2418_ = lean_nat_dec_eq(v_searcher_2410_, v___x_2417_);
lean_dec(v___x_2417_);
if (v_decide_2418_ == 0)
{
uint32_t v___x_2419_; lean_object* v___x_2420_; uint32_t v___x_2421_; uint8_t v___x_2422_; 
v___x_2419_ = 38;
v___x_2420_ = lean_nat_add(v_startInclusive_2415_, v_searcher_2410_);
v___x_2421_ = lean_string_utf8_get_fast(v_str_2414_, v___x_2420_);
v___x_2422_ = lean_uint32_dec_eq(v___x_2421_, v___x_2419_);
if (v___x_2422_ == 0)
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2426_; 
lean_dec(v_searcher_2410_);
v___x_2423_ = lean_string_utf8_next_fast(v_str_2414_, v___x_2420_);
lean_dec(v___x_2420_);
v___x_2424_ = lean_nat_sub(v___x_2423_, v_startInclusive_2415_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 1, v___x_2424_);
v___x_2426_ = v___x_2412_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_currPos_2409_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
v_a_2402_ = v___x_2426_;
goto _start;
}
}
else
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v_nextIt_2433_; 
lean_dec(v_currPos_2409_);
v___x_2429_ = lean_string_utf8_next_fast(v_str_2414_, v___x_2420_);
v___x_2430_ = lean_nat_sub(v___x_2429_, v___x_2420_);
lean_dec(v___x_2420_);
v___x_2431_ = lean_nat_add(v_searcher_2410_, v___x_2430_);
lean_dec(v___x_2430_);
lean_dec(v_searcher_2410_);
lean_inc(v___x_2431_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 1, v___x_2431_);
lean_ctor_set(v___x_2412_, 0, v___x_2431_);
v_nextIt_2433_ = v___x_2412_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2434_, 1, v___x_2431_);
v_nextIt_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
v_it_2405_ = v_nextIt_2433_;
goto v___jp_2404_;
}
}
}
else
{
lean_object* v___x_2435_; 
lean_del_object(v___x_2412_);
lean_dec(v_searcher_2410_);
lean_dec(v_currPos_2409_);
v___x_2435_ = lean_box(1);
v_it_2405_ = v___x_2435_;
goto v___jp_2404_;
}
}
}
else
{
return v_b_2403_;
}
v___jp_2404_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2406_ = lean_unsigned_to_nat(1u);
v___x_2407_ = lean_nat_add(v_b_2403_, v___x_2406_);
lean_dec(v_b_2403_);
v_a_2402_ = v_it_2405_;
v_b_2403_ = v___x_2407_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg___boxed(lean_object* v___x_2437_, lean_object* v___x_2438_, lean_object* v_a_2439_, lean_object* v_b_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2437_, v___x_2438_, v_a_2439_, v_b_2440_);
lean_dec(v___x_2438_);
lean_dec_ref(v___x_2437_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(lean_object* v___x_2442_, lean_object* v___x_2443_, lean_object* v___x_2444_, lean_object* v_a_2445_, lean_object* v_b_2446_){
_start:
{
lean_object* v_it_2448_; 
if (lean_obj_tag(v_a_2445_) == 0)
{
lean_object* v_currPos_2452_; lean_object* v_searcher_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2479_; 
v_currPos_2452_ = lean_ctor_get(v_a_2445_, 0);
v_searcher_2453_ = lean_ctor_get(v_a_2445_, 1);
v_isSharedCheck_2479_ = !lean_is_exclusive(v_a_2445_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2455_ = v_a_2445_;
v_isShared_2456_ = v_isSharedCheck_2479_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_searcher_2453_);
lean_inc(v_currPos_2452_);
lean_dec(v_a_2445_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2479_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v_str_2457_; lean_object* v_startInclusive_2458_; lean_object* v_endExclusive_2459_; lean_object* v___x_2460_; uint8_t v_decide_2461_; 
v_str_2457_ = lean_ctor_get(v___x_2443_, 0);
v_startInclusive_2458_ = lean_ctor_get(v___x_2443_, 1);
v_endExclusive_2459_ = lean_ctor_get(v___x_2443_, 2);
v___x_2460_ = lean_nat_sub(v_endExclusive_2459_, v_startInclusive_2458_);
v_decide_2461_ = lean_nat_dec_eq(v_searcher_2453_, v___x_2460_);
lean_dec(v___x_2460_);
if (v_decide_2461_ == 0)
{
lean_object* v___x_2462_; uint32_t v___x_2463_; uint32_t v___x_2464_; uint8_t v___x_2465_; 
v___x_2462_ = lean_nat_add(v_startInclusive_2458_, v_searcher_2453_);
v___x_2463_ = lean_string_utf8_get_fast(v_str_2457_, v___x_2462_);
v___x_2464_ = 38;
v___x_2465_ = lean_uint32_dec_eq(v___x_2463_, v___x_2464_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2469_; 
lean_dec(v_searcher_2453_);
v___x_2466_ = lean_string_utf8_next_fast(v_str_2457_, v___x_2462_);
lean_dec(v___x_2462_);
v___x_2467_ = lean_nat_sub(v___x_2466_, v_startInclusive_2458_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 1, v___x_2467_);
v___x_2469_ = v___x_2455_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_currPos_2452_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v___x_2467_);
v___x_2469_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
lean_object* v___x_2470_; 
v___x_2470_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2443_, v___x_2444_, v___x_2469_, v_b_2446_);
return v___x_2470_;
}
}
else
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v_nextIt_2476_; 
lean_dec(v_currPos_2452_);
v___x_2472_ = lean_string_utf8_next_fast(v_str_2457_, v___x_2462_);
v___x_2473_ = lean_nat_sub(v___x_2472_, v___x_2462_);
lean_dec(v___x_2462_);
v___x_2474_ = lean_nat_add(v_searcher_2453_, v___x_2473_);
lean_dec(v___x_2473_);
lean_dec(v_searcher_2453_);
lean_inc(v___x_2474_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 1, v___x_2474_);
lean_ctor_set(v___x_2455_, 0, v___x_2474_);
v_nextIt_2476_ = v___x_2455_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2474_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v___x_2474_);
v_nextIt_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
v_it_2448_ = v_nextIt_2476_;
goto v___jp_2447_;
}
}
}
else
{
lean_object* v___x_2478_; 
lean_del_object(v___x_2455_);
lean_dec(v_searcher_2453_);
lean_dec(v_currPos_2452_);
v___x_2478_ = lean_box(1);
v_it_2448_ = v___x_2478_;
goto v___jp_2447_;
}
}
}
else
{
return v_b_2446_;
}
v___jp_2447_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2449_ = lean_unsigned_to_nat(1u);
v___x_2450_ = lean_nat_add(v_b_2446_, v___x_2449_);
lean_dec(v_b_2446_);
v___x_2451_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2443_, v___x_2444_, v_it_2448_, v___x_2450_);
return v___x_2451_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg___boxed(lean_object* v___x_2480_, lean_object* v___x_2481_, lean_object* v___x_2482_, lean_object* v_a_2483_, lean_object* v_b_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2480_, v___x_2481_, v___x_2482_, v_a_2483_, v_b_2484_);
lean_dec(v___x_2482_);
lean_dec_ref(v___x_2481_);
lean_dec_ref(v___x_2480_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(lean_object* v_out_2486_, lean_object* v_a_2487_, lean_object* v_b_2488_){
_start:
{
if (lean_obj_tag(v_a_2487_) == 0)
{
lean_object* v_currPos_2489_; lean_object* v_searcher_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2529_; 
v_currPos_2489_ = lean_ctor_get(v_a_2487_, 0);
v_searcher_2490_ = lean_ctor_get(v_a_2487_, 1);
v_isSharedCheck_2529_ = !lean_is_exclusive(v_a_2487_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2492_ = v_a_2487_;
v_isShared_2493_ = v_isSharedCheck_2529_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_searcher_2490_);
lean_inc(v_currPos_2489_);
lean_dec(v_a_2487_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2529_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v_str_2494_; lean_object* v_startInclusive_2495_; lean_object* v_endExclusive_2496_; lean_object* v_it_2498_; lean_object* v_startInclusive_2499_; lean_object* v_endExclusive_2500_; lean_object* v___x_2507_; uint8_t v_decide_2508_; 
v_str_2494_ = lean_ctor_get(v_out_2486_, 0);
v_startInclusive_2495_ = lean_ctor_get(v_out_2486_, 1);
v_endExclusive_2496_ = lean_ctor_get(v_out_2486_, 2);
v___x_2507_ = lean_nat_sub(v_endExclusive_2496_, v_startInclusive_2495_);
v_decide_2508_ = lean_nat_dec_eq(v_searcher_2490_, v___x_2507_);
if (v_decide_2508_ == 0)
{
uint32_t v___x_2509_; lean_object* v___x_2510_; uint32_t v___x_2511_; uint8_t v___x_2512_; 
lean_dec(v___x_2507_);
v___x_2509_ = 61;
v___x_2510_ = lean_nat_add(v_startInclusive_2495_, v_searcher_2490_);
v___x_2511_ = lean_string_utf8_get_fast(v_str_2494_, v___x_2510_);
v___x_2512_ = lean_uint32_dec_eq(v___x_2511_, v___x_2509_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2516_; 
lean_dec(v_searcher_2490_);
v___x_2513_ = lean_string_utf8_next_fast(v_str_2494_, v___x_2510_);
lean_dec(v___x_2510_);
v___x_2514_ = lean_nat_sub(v___x_2513_, v_startInclusive_2495_);
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 1, v___x_2514_);
v___x_2516_ = v___x_2492_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_currPos_2489_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
v_a_2487_ = v___x_2516_;
goto _start;
}
}
else
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v_slice_2522_; lean_object* v_nextIt_2524_; 
v___x_2519_ = lean_string_utf8_next_fast(v_str_2494_, v___x_2510_);
v___x_2520_ = lean_nat_sub(v___x_2519_, v___x_2510_);
lean_dec(v___x_2510_);
v___x_2521_ = lean_nat_add(v_searcher_2490_, v___x_2520_);
lean_dec(v___x_2520_);
v_slice_2522_ = l_String_Slice_subslice_x21(v_out_2486_, v_currPos_2489_, v_searcher_2490_);
lean_inc(v___x_2521_);
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 1, v___x_2521_);
lean_ctor_set(v___x_2492_, 0, v___x_2521_);
v_nextIt_2524_ = v___x_2492_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v___x_2521_);
lean_ctor_set(v_reuseFailAlloc_2527_, 1, v___x_2521_);
v_nextIt_2524_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
lean_object* v_startInclusive_2525_; lean_object* v_endExclusive_2526_; 
v_startInclusive_2525_ = lean_ctor_get(v_slice_2522_, 0);
lean_inc(v_startInclusive_2525_);
v_endExclusive_2526_ = lean_ctor_get(v_slice_2522_, 1);
lean_inc(v_endExclusive_2526_);
lean_dec_ref(v_slice_2522_);
v_it_2498_ = v_nextIt_2524_;
v_startInclusive_2499_ = v_startInclusive_2525_;
v_endExclusive_2500_ = v_endExclusive_2526_;
goto v___jp_2497_;
}
}
}
else
{
lean_object* v___x_2528_; 
lean_del_object(v___x_2492_);
lean_dec(v_searcher_2490_);
v___x_2528_ = lean_box(1);
v_it_2498_ = v___x_2528_;
v_startInclusive_2499_ = v_currPos_2489_;
v_endExclusive_2500_ = v___x_2507_;
goto v___jp_2497_;
}
v___jp_2497_:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2501_ = lean_nat_add(v_startInclusive_2495_, v_startInclusive_2499_);
lean_dec(v_startInclusive_2499_);
v___x_2502_ = lean_nat_add(v_startInclusive_2495_, v_endExclusive_2500_);
lean_dec(v_endExclusive_2500_);
lean_inc_ref(v_str_2494_);
v___x_2503_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2503_, 0, v_str_2494_);
lean_ctor_set(v___x_2503_, 1, v___x_2501_);
lean_ctor_set(v___x_2503_, 2, v___x_2502_);
v___x_2504_ = l_String_Slice_toString(v___x_2503_);
lean_dec_ref_known(v___x_2503_, 3);
v___x_2505_ = lean_array_push(v_b_2488_, v___x_2504_);
v_a_2487_ = v_it_2498_;
v_b_2488_ = v___x_2505_;
goto _start;
}
}
}
else
{
return v_b_2488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg___boxed(lean_object* v_out_2530_, lean_object* v_a_2531_, lean_object* v_b_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2530_, v_a_2531_, v_b_2532_);
lean_dec_ref(v_out_2530_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(lean_object* v___x_2537_, lean_object* v___x_2538_, lean_object* v___x_2539_, lean_object* v_a_2540_, lean_object* v_b_2541_){
_start:
{
lean_object* v_it_2543_; lean_object* v_startInclusive_2544_; lean_object* v_endExclusive_2545_; 
if (lean_obj_tag(v_a_2540_) == 0)
{
lean_object* v_currPos_2570_; lean_object* v_searcher_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2600_; 
v_currPos_2570_ = lean_ctor_get(v_a_2540_, 0);
v_searcher_2571_ = lean_ctor_get(v_a_2540_, 1);
v_isSharedCheck_2600_ = !lean_is_exclusive(v_a_2540_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2573_ = v_a_2540_;
v_isShared_2574_ = v_isSharedCheck_2600_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_searcher_2571_);
lean_inc(v_currPos_2570_);
lean_dec(v_a_2540_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2600_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v_str_2575_; lean_object* v_startInclusive_2576_; lean_object* v_endExclusive_2577_; lean_object* v___x_2578_; uint8_t v_decide_2579_; 
v_str_2575_ = lean_ctor_get(v___x_2538_, 0);
v_startInclusive_2576_ = lean_ctor_get(v___x_2538_, 1);
v_endExclusive_2577_ = lean_ctor_get(v___x_2538_, 2);
v___x_2578_ = lean_nat_sub(v_endExclusive_2577_, v_startInclusive_2576_);
v_decide_2579_ = lean_nat_dec_eq(v_searcher_2571_, v___x_2578_);
lean_dec(v___x_2578_);
if (v_decide_2579_ == 0)
{
uint32_t v___x_2580_; lean_object* v___x_2581_; uint32_t v___x_2582_; uint8_t v___x_2583_; 
v___x_2580_ = 38;
v___x_2581_ = lean_nat_add(v_startInclusive_2576_, v_searcher_2571_);
v___x_2582_ = lean_string_utf8_get_fast(v_str_2575_, v___x_2581_);
v___x_2583_ = lean_uint32_dec_eq(v___x_2582_, v___x_2580_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2587_; 
lean_dec(v_searcher_2571_);
v___x_2584_ = lean_string_utf8_next_fast(v_str_2575_, v___x_2581_);
lean_dec(v___x_2581_);
v___x_2585_ = lean_nat_sub(v___x_2584_, v_startInclusive_2576_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 1, v___x_2585_);
v___x_2587_ = v___x_2573_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_currPos_2570_);
lean_ctor_set(v_reuseFailAlloc_2589_, 1, v___x_2585_);
v___x_2587_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
v_a_2540_ = v___x_2587_;
goto _start;
}
}
else
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v_slice_2593_; lean_object* v_nextIt_2595_; 
v___x_2590_ = lean_string_utf8_next_fast(v_str_2575_, v___x_2581_);
v___x_2591_ = lean_nat_sub(v___x_2590_, v___x_2581_);
lean_dec(v___x_2581_);
v___x_2592_ = lean_nat_add(v_searcher_2571_, v___x_2591_);
lean_dec(v___x_2591_);
v_slice_2593_ = l_String_Slice_subslice_x21(v___x_2538_, v_currPos_2570_, v_searcher_2571_);
lean_inc(v___x_2592_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 1, v___x_2592_);
lean_ctor_set(v___x_2573_, 0, v___x_2592_);
v_nextIt_2595_ = v___x_2573_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2592_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v___x_2592_);
v_nextIt_2595_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
lean_object* v_startInclusive_2596_; lean_object* v_endExclusive_2597_; 
v_startInclusive_2596_ = lean_ctor_get(v_slice_2593_, 0);
lean_inc(v_startInclusive_2596_);
v_endExclusive_2597_ = lean_ctor_get(v_slice_2593_, 1);
lean_inc(v_endExclusive_2597_);
lean_dec_ref(v_slice_2593_);
v_it_2543_ = v_nextIt_2595_;
v_startInclusive_2544_ = v_startInclusive_2596_;
v_endExclusive_2545_ = v_endExclusive_2597_;
goto v___jp_2542_;
}
}
}
else
{
lean_object* v___x_2599_; 
lean_del_object(v___x_2573_);
lean_dec(v_searcher_2571_);
v___x_2599_ = lean_box(1);
lean_inc(v___x_2539_);
v_it_2543_ = v___x_2599_;
v_startInclusive_2544_ = v_currPos_2570_;
v_endExclusive_2545_ = v___x_2539_;
goto v___jp_2542_;
}
}
}
else
{
lean_object* v___x_2601_; 
lean_dec(v___x_2539_);
lean_dec_ref(v___x_2537_);
v___x_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2601_, 0, v_b_2541_);
return v___x_2601_;
}
v___jp_2542_:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
lean_inc_ref(v___x_2537_);
v___x_2546_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2537_);
lean_ctor_set(v___x_2546_, 1, v_startInclusive_2544_);
lean_ctor_set(v___x_2546_, 2, v_endExclusive_2545_);
v___x_2547_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v___x_2546_);
v___x_2548_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2549_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2546_, v___x_2547_, v___x_2548_);
lean_dec_ref_known(v___x_2546_, 3);
v___x_2550_ = lean_array_to_list(v___x_2549_);
if (lean_obj_tag(v___x_2550_) == 0)
{
v_a_2540_ = v_it_2543_;
goto _start;
}
else
{
lean_object* v_tail_2552_; 
v_tail_2552_ = lean_ctor_get(v___x_2550_, 1);
lean_inc(v_tail_2552_);
if (lean_obj_tag(v_tail_2552_) == 0)
{
lean_object* v_head_2553_; lean_object* v___x_2554_; 
v_head_2553_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_head_2553_);
lean_dec_ref_known(v___x_2550_, 2);
v___x_2554_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2553_);
lean_dec(v_head_2553_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v___x_2555_; 
lean_dec(v_it_2543_);
lean_dec_ref(v_b_2541_);
lean_dec(v___x_2539_);
lean_dec_ref(v___x_2537_);
v___x_2555_ = lean_box(0);
return v___x_2555_;
}
else
{
lean_object* v_val_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v_val_2556_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_val_2556_);
lean_dec_ref_known(v___x_2554_, 1);
v___x_2557_ = lean_box(0);
v___x_2558_ = l_Std_Http_URI_Query_insertEncoded(v_b_2541_, v_val_2556_, v___x_2557_);
v_a_2540_ = v_it_2543_;
v_b_2541_ = v___x_2558_;
goto _start;
}
}
else
{
lean_object* v_head_2560_; lean_object* v___x_2561_; 
v_head_2560_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_head_2560_);
lean_dec_ref_known(v___x_2550_, 2);
v___x_2561_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2560_);
lean_dec(v_head_2560_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v___x_2562_; 
lean_dec(v_tail_2552_);
lean_dec(v_it_2543_);
lean_dec_ref(v_b_2541_);
lean_dec(v___x_2539_);
lean_dec_ref(v___x_2537_);
v___x_2562_ = lean_box(0);
return v___x_2562_;
}
else
{
lean_object* v_val_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v_val_2563_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_val_2563_);
lean_dec_ref_known(v___x_2561_, 1);
v___x_2564_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2565_ = l_String_intercalate(v___x_2564_, v_tail_2552_);
v___x_2566_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2565_);
lean_dec_ref(v___x_2565_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v___x_2567_; 
lean_dec(v_val_2563_);
lean_dec(v_it_2543_);
lean_dec_ref(v_b_2541_);
lean_dec(v___x_2539_);
lean_dec_ref(v___x_2537_);
v___x_2567_ = lean_box(0);
return v___x_2567_;
}
else
{
lean_object* v___x_2568_; 
v___x_2568_ = l_Std_Http_URI_Query_insertEncoded(v_b_2541_, v_val_2563_, v___x_2566_);
v_a_2540_ = v_it_2543_;
v_b_2541_ = v___x_2568_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___boxed(lean_object* v___x_2602_, lean_object* v___x_2603_, lean_object* v___x_2604_, lean_object* v_a_2605_, lean_object* v_b_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2602_, v___x_2603_, v___x_2604_, v_a_2605_, v_b_2606_);
lean_dec_ref(v___x_2603_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(lean_object* v___x_2608_, lean_object* v___x_2609_, lean_object* v___x_2610_, lean_object* v_a_2611_, lean_object* v_b_2612_){
_start:
{
lean_object* v_it_2614_; lean_object* v_startInclusive_2615_; lean_object* v_endExclusive_2616_; 
if (lean_obj_tag(v_a_2611_) == 0)
{
lean_object* v_currPos_2641_; lean_object* v_searcher_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2671_; 
v_currPos_2641_ = lean_ctor_get(v_a_2611_, 0);
v_searcher_2642_ = lean_ctor_get(v_a_2611_, 1);
v_isSharedCheck_2671_ = !lean_is_exclusive(v_a_2611_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2644_ = v_a_2611_;
v_isShared_2645_ = v_isSharedCheck_2671_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_searcher_2642_);
lean_inc(v_currPos_2641_);
lean_dec(v_a_2611_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2671_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v_str_2646_; lean_object* v_startInclusive_2647_; lean_object* v_endExclusive_2648_; lean_object* v___x_2649_; uint8_t v_decide_2650_; 
v_str_2646_ = lean_ctor_get(v___x_2609_, 0);
v_startInclusive_2647_ = lean_ctor_get(v___x_2609_, 1);
v_endExclusive_2648_ = lean_ctor_get(v___x_2609_, 2);
v___x_2649_ = lean_nat_sub(v_endExclusive_2648_, v_startInclusive_2647_);
v_decide_2650_ = lean_nat_dec_eq(v_searcher_2642_, v___x_2649_);
lean_dec(v___x_2649_);
if (v_decide_2650_ == 0)
{
lean_object* v___x_2651_; uint32_t v___x_2652_; uint32_t v___x_2653_; uint8_t v___x_2654_; 
v___x_2651_ = lean_nat_add(v_startInclusive_2647_, v_searcher_2642_);
v___x_2652_ = lean_string_utf8_get_fast(v_str_2646_, v___x_2651_);
v___x_2653_ = 38;
v___x_2654_ = lean_uint32_dec_eq(v___x_2652_, v___x_2653_);
if (v___x_2654_ == 0)
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2658_; 
lean_dec(v_searcher_2642_);
v___x_2655_ = lean_string_utf8_next_fast(v_str_2646_, v___x_2651_);
lean_dec(v___x_2651_);
v___x_2656_ = lean_nat_sub(v___x_2655_, v_startInclusive_2647_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 1, v___x_2656_);
v___x_2658_ = v___x_2644_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_currPos_2641_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v___x_2656_);
v___x_2658_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
lean_object* v___x_2659_; 
v___x_2659_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2608_, v___x_2609_, v___x_2610_, v___x_2658_, v_b_2612_);
return v___x_2659_;
}
}
else
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v_slice_2664_; lean_object* v_nextIt_2666_; 
v___x_2661_ = lean_string_utf8_next_fast(v_str_2646_, v___x_2651_);
v___x_2662_ = lean_nat_sub(v___x_2661_, v___x_2651_);
lean_dec(v___x_2651_);
v___x_2663_ = lean_nat_add(v_searcher_2642_, v___x_2662_);
lean_dec(v___x_2662_);
v_slice_2664_ = l_String_Slice_subslice_x21(v___x_2609_, v_currPos_2641_, v_searcher_2642_);
lean_inc(v___x_2663_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 1, v___x_2663_);
lean_ctor_set(v___x_2644_, 0, v___x_2663_);
v_nextIt_2666_ = v___x_2644_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2663_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v___x_2663_);
v_nextIt_2666_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
lean_object* v_startInclusive_2667_; lean_object* v_endExclusive_2668_; 
v_startInclusive_2667_ = lean_ctor_get(v_slice_2664_, 0);
lean_inc(v_startInclusive_2667_);
v_endExclusive_2668_ = lean_ctor_get(v_slice_2664_, 1);
lean_inc(v_endExclusive_2668_);
lean_dec_ref(v_slice_2664_);
v_it_2614_ = v_nextIt_2666_;
v_startInclusive_2615_ = v_startInclusive_2667_;
v_endExclusive_2616_ = v_endExclusive_2668_;
goto v___jp_2613_;
}
}
}
else
{
lean_object* v___x_2670_; 
lean_del_object(v___x_2644_);
lean_dec(v_searcher_2642_);
v___x_2670_ = lean_box(1);
lean_inc(v___x_2610_);
v_it_2614_ = v___x_2670_;
v_startInclusive_2615_ = v_currPos_2641_;
v_endExclusive_2616_ = v___x_2610_;
goto v___jp_2613_;
}
}
}
else
{
lean_object* v___x_2672_; 
lean_dec(v___x_2610_);
lean_dec_ref(v___x_2608_);
v___x_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2672_, 0, v_b_2612_);
return v___x_2672_;
}
v___jp_2613_:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
lean_inc_ref(v___x_2608_);
v___x_2617_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2608_);
lean_ctor_set(v___x_2617_, 1, v_startInclusive_2615_);
lean_ctor_set(v___x_2617_, 2, v_endExclusive_2616_);
v___x_2618_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v___x_2617_);
v___x_2619_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2620_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2617_, v___x_2618_, v___x_2619_);
lean_dec_ref_known(v___x_2617_, 3);
v___x_2621_ = lean_array_to_list(v___x_2620_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v___x_2622_; 
v___x_2622_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2608_, v___x_2609_, v___x_2610_, v_it_2614_, v_b_2612_);
return v___x_2622_;
}
else
{
lean_object* v_tail_2623_; 
v_tail_2623_ = lean_ctor_get(v___x_2621_, 1);
lean_inc(v_tail_2623_);
if (lean_obj_tag(v_tail_2623_) == 0)
{
lean_object* v_head_2624_; lean_object* v___x_2625_; 
v_head_2624_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_head_2624_);
lean_dec_ref_known(v___x_2621_, 2);
v___x_2625_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2624_);
lean_dec(v_head_2624_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v___x_2626_; 
lean_dec(v_it_2614_);
lean_dec_ref(v_b_2612_);
lean_dec(v___x_2610_);
lean_dec_ref(v___x_2608_);
v___x_2626_ = lean_box(0);
return v___x_2626_;
}
else
{
lean_object* v_val_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v_val_2627_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_val_2627_);
lean_dec_ref_known(v___x_2625_, 1);
v___x_2628_ = lean_box(0);
v___x_2629_ = l_Std_Http_URI_Query_insertEncoded(v_b_2612_, v_val_2627_, v___x_2628_);
v___x_2630_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2608_, v___x_2609_, v___x_2610_, v_it_2614_, v___x_2629_);
return v___x_2630_;
}
}
else
{
lean_object* v_head_2631_; lean_object* v___x_2632_; 
v_head_2631_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_head_2631_);
lean_dec_ref_known(v___x_2621_, 2);
v___x_2632_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2631_);
lean_dec(v_head_2631_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v___x_2633_; 
lean_dec(v_tail_2623_);
lean_dec(v_it_2614_);
lean_dec_ref(v_b_2612_);
lean_dec(v___x_2610_);
lean_dec_ref(v___x_2608_);
v___x_2633_ = lean_box(0);
return v___x_2633_;
}
else
{
lean_object* v_val_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v_val_2634_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_val_2634_);
lean_dec_ref_known(v___x_2632_, 1);
v___x_2635_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2636_ = l_String_intercalate(v___x_2635_, v_tail_2623_);
v___x_2637_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2636_);
lean_dec_ref(v___x_2636_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v___x_2638_; 
lean_dec(v_val_2634_);
lean_dec(v_it_2614_);
lean_dec_ref(v_b_2612_);
lean_dec(v___x_2610_);
lean_dec_ref(v___x_2608_);
v___x_2638_ = lean_box(0);
return v___x_2638_;
}
else
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2639_ = l_Std_Http_URI_Query_insertEncoded(v_b_2612_, v_val_2634_, v___x_2637_);
v___x_2640_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2608_, v___x_2609_, v___x_2610_, v_it_2614_, v___x_2639_);
return v___x_2640_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg___boxed(lean_object* v___x_2673_, lean_object* v___x_2674_, lean_object* v___x_2675_, lean_object* v_a_2676_, lean_object* v_b_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2673_, v___x_2674_, v___x_2675_, v_a_2676_, v_b_2677_);
lean_dec_ref(v___x_2674_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(lean_object* v_config_2684_, lean_object* v_a_2685_){
_start:
{
lean_object* v_maxQueryLength_2686_; lean_object* v_maxQueryParams_2687_; lean_object* v___f_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v_snd_2691_; lean_object* v_fst_2692_; lean_object* v_fst_2693_; lean_object* v_array_2694_; lean_object* v_idx_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2745_; 
v_maxQueryLength_2686_ = lean_ctor_get(v_config_2684_, 4);
lean_inc(v_maxQueryLength_2686_);
v_maxQueryParams_2687_ = lean_ctor_get(v_config_2684_, 8);
lean_inc(v_maxQueryParams_2687_);
lean_dec_ref(v_config_2684_);
v___f_2688_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2689_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2685_);
v___x_2690_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2688_, v_maxQueryLength_2686_, v___x_2689_, v_a_2685_);
lean_dec(v_maxQueryLength_2686_);
v_snd_2691_ = lean_ctor_get(v___x_2690_, 1);
lean_inc(v_snd_2691_);
v_fst_2692_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_fst_2692_);
lean_dec_ref(v___x_2690_);
v_fst_2693_ = lean_ctor_get(v_snd_2691_, 0);
lean_inc(v_fst_2693_);
lean_dec(v_snd_2691_);
v_array_2694_ = lean_ctor_get(v_a_2685_, 0);
v_idx_2695_ = lean_ctor_get(v_a_2685_, 1);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_a_2685_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2697_ = v_a_2685_;
v_isShared_2698_ = v_isSharedCheck_2745_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_idx_2695_);
lean_inc(v_array_2694_);
lean_dec(v_a_2685_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2745_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v_lower_2700_; lean_object* v_upper_2701_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___y_2742_; uint8_t v___x_2744_; 
v___x_2739_ = lean_nat_add(v_idx_2695_, v_fst_2692_);
lean_dec(v_fst_2692_);
v___x_2740_ = lean_byte_array_size(v_array_2694_);
v___x_2744_ = lean_nat_dec_le(v_idx_2695_, v___x_2689_);
if (v___x_2744_ == 0)
{
v___y_2742_ = v_idx_2695_;
goto v___jp_2741_;
}
else
{
lean_dec(v_idx_2695_);
v___y_2742_ = v___x_2689_;
goto v___jp_2741_;
}
v___jp_2699_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; uint8_t v___x_2704_; 
v___x_2702_ = l_ByteArray_toByteSlice(v_array_2694_, v_lower_2700_, v_upper_2701_);
v___x_2703_ = l_ByteSlice_toByteArray(v___x_2702_);
v___x_2704_ = lean_string_validate_utf8(v___x_2703_);
if (v___x_2704_ == 0)
{
lean_object* v___x_2705_; lean_object* v___x_2707_; 
lean_dec_ref(v___x_2703_);
lean_dec(v_maxQueryParams_2687_);
v___x_2705_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2698_ == 0)
{
lean_ctor_set_tag(v___x_2697_, 1);
lean_ctor_set(v___x_2697_, 1, v___x_2705_);
lean_ctor_set(v___x_2697_, 0, v_fst_2693_);
v___x_2707_ = v___x_2697_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_fst_2693_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v___x_2705_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
else
{
lean_object* v___x_2709_; lean_object* v___x_2710_; uint8_t v___x_2711_; 
v___x_2709_ = lean_string_from_utf8_unchecked(v___x_2703_);
v___x_2710_ = lean_string_utf8_byte_size(v___x_2709_);
v___x_2711_ = lean_nat_dec_eq(v___x_2710_, v___x_2689_);
if (v___x_2711_ == 0)
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; uint8_t v___x_2715_; 
lean_inc_ref(v___x_2709_);
v___x_2712_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2709_);
lean_ctor_set(v___x_2712_, 1, v___x_2689_);
lean_ctor_set(v___x_2712_, 2, v___x_2710_);
v___x_2713_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(v___x_2712_);
lean_inc(v___x_2713_);
v___x_2714_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2709_, v___x_2712_, v___x_2710_, v___x_2713_, v___x_2689_);
v___x_2715_ = lean_nat_dec_lt(v_maxQueryParams_2687_, v___x_2714_);
lean_dec(v___x_2714_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
lean_dec(v_maxQueryParams_2687_);
v___x_2716_ = l_Std_Http_URI_Query_empty;
v___x_2717_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2709_, v___x_2712_, v___x_2710_, v___x_2713_, v___x_2716_);
lean_dec_ref_known(v___x_2712_, 3);
if (lean_obj_tag(v___x_2717_) == 1)
{
lean_object* v_val_2718_; lean_object* v___x_2720_; 
v_val_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_val_2718_);
lean_dec_ref_known(v___x_2717_, 1);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 1, v_val_2718_);
lean_ctor_set(v___x_2697_, 0, v_fst_2693_);
v___x_2720_ = v___x_2697_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_fst_2693_);
lean_ctor_set(v_reuseFailAlloc_2721_, 1, v_val_2718_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
else
{
lean_object* v___x_2722_; lean_object* v___x_2724_; 
lean_dec(v___x_2717_);
v___x_2722_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2698_ == 0)
{
lean_ctor_set_tag(v___x_2697_, 1);
lean_ctor_set(v___x_2697_, 1, v___x_2722_);
lean_ctor_set(v___x_2697_, 0, v_fst_2693_);
v___x_2724_ = v___x_2697_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_fst_2693_);
lean_ctor_set(v_reuseFailAlloc_2725_, 1, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
else
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2733_; 
lean_dec(v___x_2713_);
lean_dec_ref_known(v___x_2712_, 3);
lean_dec_ref(v___x_2709_);
v___x_2726_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3));
v___x_2727_ = l_Nat_reprFast(v_maxQueryParams_2687_);
v___x_2728_ = lean_string_append(v___x_2726_, v___x_2727_);
lean_dec_ref(v___x_2727_);
v___x_2729_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_2730_ = lean_string_append(v___x_2728_, v___x_2729_);
v___x_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2730_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set_tag(v___x_2697_, 1);
lean_ctor_set(v___x_2697_, 1, v___x_2731_);
lean_ctor_set(v___x_2697_, 0, v_fst_2693_);
v___x_2733_ = v___x_2697_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_fst_2693_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v___x_2731_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
else
{
lean_object* v___x_2735_; lean_object* v___x_2737_; 
lean_dec_ref(v___x_2709_);
lean_dec(v_maxQueryParams_2687_);
v___x_2735_ = l_Std_Http_URI_Query_empty;
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 1, v___x_2735_);
lean_ctor_set(v___x_2697_, 0, v_fst_2693_);
v___x_2737_ = v___x_2697_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_fst_2693_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v___x_2735_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
v___jp_2741_:
{
uint8_t v___x_2743_; 
v___x_2743_ = lean_nat_dec_le(v___x_2739_, v___x_2740_);
if (v___x_2743_ == 0)
{
lean_dec(v___x_2739_);
v_lower_2700_ = v___y_2742_;
v_upper_2701_ = v___x_2740_;
goto v___jp_2699_;
}
else
{
v_lower_2700_ = v___y_2742_;
v_upper_2701_ = v___x_2739_;
goto v___jp_2699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(lean_object* v___x_2746_, lean_object* v___x_2747_, lean_object* v___x_2748_, lean_object* v_inst_2749_, lean_object* v_R_2750_, lean_object* v_a_2751_, lean_object* v_b_2752_, lean_object* v_c_2753_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2746_, v___x_2747_, v___x_2748_, v_a_2751_, v_b_2752_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___boxed(lean_object* v___x_2755_, lean_object* v___x_2756_, lean_object* v___x_2757_, lean_object* v_inst_2758_, lean_object* v_R_2759_, lean_object* v_a_2760_, lean_object* v_b_2761_, lean_object* v_c_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(v___x_2755_, v___x_2756_, v___x_2757_, v_inst_2758_, v_R_2759_, v_a_2760_, v_b_2761_, v_c_2762_);
lean_dec(v___x_2757_);
lean_dec_ref(v___x_2756_);
lean_dec_ref(v___x_2755_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(lean_object* v_out_2764_, lean_object* v_inst_2765_, lean_object* v_R_2766_, lean_object* v_a_2767_, lean_object* v_b_2768_){
_start:
{
lean_object* v___x_2769_; 
v___x_2769_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2764_, v_a_2767_, v_b_2768_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___boxed(lean_object* v_out_2770_, lean_object* v_inst_2771_, lean_object* v_R_2772_, lean_object* v_a_2773_, lean_object* v_b_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(v_out_2770_, v_inst_2771_, v_R_2772_, v_a_2773_, v_b_2774_);
lean_dec_ref(v_out_2770_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(lean_object* v___x_2776_, lean_object* v___x_2777_, lean_object* v___x_2778_, lean_object* v_inst_2779_, lean_object* v_R_2780_, lean_object* v_a_2781_, lean_object* v_b_2782_, lean_object* v_c_2783_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2776_, v___x_2777_, v___x_2778_, v_a_2781_, v_b_2782_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___boxed(lean_object* v___x_2785_, lean_object* v___x_2786_, lean_object* v___x_2787_, lean_object* v_inst_2788_, lean_object* v_R_2789_, lean_object* v_a_2790_, lean_object* v_b_2791_, lean_object* v_c_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(v___x_2785_, v___x_2786_, v___x_2787_, v_inst_2788_, v_R_2789_, v_a_2790_, v_b_2791_, v_c_2792_);
lean_dec_ref(v___x_2786_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(lean_object* v___x_2794_, lean_object* v___x_2795_, lean_object* v___x_2796_, lean_object* v_inst_2797_, lean_object* v_R_2798_, lean_object* v_a_2799_, lean_object* v_b_2800_, lean_object* v_c_2801_){
_start:
{
lean_object* v___x_2802_; 
v___x_2802_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2795_, v___x_2796_, v_a_2799_, v_b_2800_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___boxed(lean_object* v___x_2803_, lean_object* v___x_2804_, lean_object* v___x_2805_, lean_object* v_inst_2806_, lean_object* v_R_2807_, lean_object* v_a_2808_, lean_object* v_b_2809_, lean_object* v_c_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(v___x_2803_, v___x_2804_, v___x_2805_, v_inst_2806_, v_R_2807_, v_a_2808_, v_b_2809_, v_c_2810_);
lean_dec(v___x_2805_);
lean_dec_ref(v___x_2804_);
lean_dec_ref(v___x_2803_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(lean_object* v___x_2812_, lean_object* v___x_2813_, lean_object* v___x_2814_, lean_object* v_inst_2815_, lean_object* v_R_2816_, lean_object* v_a_2817_, lean_object* v_b_2818_, lean_object* v_c_2819_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2812_, v___x_2813_, v___x_2814_, v_a_2817_, v_b_2818_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___boxed(lean_object* v___x_2821_, lean_object* v___x_2822_, lean_object* v___x_2823_, lean_object* v_inst_2824_, lean_object* v_R_2825_, lean_object* v_a_2826_, lean_object* v_b_2827_, lean_object* v_c_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(v___x_2821_, v___x_2822_, v___x_2823_, v_inst_2824_, v_R_2825_, v_a_2826_, v_b_2827_, v_c_2828_);
lean_dec_ref(v___x_2822_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(lean_object* v_config_2833_, lean_object* v_a_2834_){
_start:
{
lean_object* v_maxFragmentLength_2835_; lean_object* v___f_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v_snd_2839_; lean_object* v_fst_2840_; lean_object* v_fst_2841_; lean_object* v_array_2842_; lean_object* v_idx_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2867_; 
v_maxFragmentLength_2835_ = lean_ctor_get(v_config_2833_, 5);
v___f_2836_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2837_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2834_);
v___x_2838_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2836_, v_maxFragmentLength_2835_, v___x_2837_, v_a_2834_);
v_snd_2839_ = lean_ctor_get(v___x_2838_, 1);
lean_inc(v_snd_2839_);
v_fst_2840_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_fst_2840_);
lean_dec_ref(v___x_2838_);
v_fst_2841_ = lean_ctor_get(v_snd_2839_, 0);
lean_inc(v_fst_2841_);
lean_dec(v_snd_2839_);
v_array_2842_ = lean_ctor_get(v_a_2834_, 0);
v_idx_2843_ = lean_ctor_get(v_a_2834_, 1);
v_isSharedCheck_2867_ = !lean_is_exclusive(v_a_2834_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2845_ = v_a_2834_;
v_isShared_2846_ = v_isSharedCheck_2867_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_idx_2843_);
lean_inc(v_array_2842_);
lean_dec(v_a_2834_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2867_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v_lower_2848_; lean_object* v_upper_2849_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___y_2864_; uint8_t v___x_2866_; 
v___x_2861_ = lean_nat_add(v_idx_2843_, v_fst_2840_);
lean_dec(v_fst_2840_);
v___x_2862_ = lean_byte_array_size(v_array_2842_);
v___x_2866_ = lean_nat_dec_le(v_idx_2843_, v___x_2837_);
if (v___x_2866_ == 0)
{
v___y_2864_ = v_idx_2843_;
goto v___jp_2863_;
}
else
{
lean_dec(v_idx_2843_);
v___y_2864_ = v___x_2837_;
goto v___jp_2863_;
}
v___jp_2847_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2850_ = l_ByteArray_toByteSlice(v_array_2842_, v_lower_2848_, v_upper_2849_);
v___x_2851_ = l_ByteSlice_toByteArray(v___x_2850_);
v___x_2852_ = l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(v___x_2851_);
if (lean_obj_tag(v___x_2852_) == 1)
{
lean_object* v_val_2853_; lean_object* v___x_2855_; 
v_val_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_val_2853_);
lean_dec_ref_known(v___x_2852_, 1);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 1, v_val_2853_);
lean_ctor_set(v___x_2845_, 0, v_fst_2841_);
v___x_2855_ = v___x_2845_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_fst_2841_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_val_2853_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
else
{
lean_object* v___x_2857_; lean_object* v___x_2859_; 
lean_dec(v___x_2852_);
v___x_2857_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1));
if (v_isShared_2846_ == 0)
{
lean_ctor_set_tag(v___x_2845_, 1);
lean_ctor_set(v___x_2845_, 1, v___x_2857_);
lean_ctor_set(v___x_2845_, 0, v_fst_2841_);
v___x_2859_ = v___x_2845_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_fst_2841_);
lean_ctor_set(v_reuseFailAlloc_2860_, 1, v___x_2857_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
v___jp_2863_:
{
uint8_t v___x_2865_; 
v___x_2865_ = lean_nat_dec_le(v___x_2861_, v___x_2862_);
if (v___x_2865_ == 0)
{
lean_dec(v___x_2861_);
v_lower_2848_ = v___y_2864_;
v_upper_2849_ = v___x_2862_;
goto v___jp_2847_;
}
else
{
v_lower_2848_ = v___y_2864_;
v_upper_2849_ = v___x_2861_;
goto v___jp_2847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___boxed(lean_object* v_config_2868_, lean_object* v_a_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2868_, v_a_2869_);
lean_dec_ref(v_config_2868_);
return v_res_2870_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1(void){
_start:
{
lean_object* v___x_2872_; lean_object* v_utf8_2873_; 
v___x_2872_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0));
v_utf8_2873_ = lean_string_to_utf8(v___x_2872_);
return v_utf8_2873_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(lean_object* v_config_2874_, lean_object* v_a_2875_){
_start:
{
uint8_t v___y_2877_; lean_object* v_pos_2878_; lean_object* v_res_2879_; uint8_t v___y_2901_; lean_object* v___y_2902_; lean_object* v_err_2903_; lean_object* v_pos_2909_; lean_object* v_utf8_2917_; lean_object* v___x_2918_; 
v_utf8_2917_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_2875_);
v___x_2918_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_2917_, v_a_2875_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v_pos_2919_; 
lean_dec_ref(v_a_2875_);
v_pos_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc(v_pos_2919_);
lean_dec_ref_known(v___x_2918_, 2);
v_pos_2909_ = v_pos_2919_;
goto v___jp_2908_;
}
else
{
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v_pos_2920_; 
lean_dec_ref(v_a_2875_);
v_pos_2920_ = lean_ctor_get(v___x_2918_, 0);
lean_inc(v_pos_2920_);
lean_dec_ref_known(v___x_2918_, 2);
v_pos_2909_ = v_pos_2920_;
goto v___jp_2908_;
}
else
{
lean_object* v_err_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2952_; 
v_err_2921_ = lean_ctor_get(v___x_2918_, 1);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2952_ == 0)
{
lean_object* v_unused_2953_; 
v_unused_2953_ = lean_ctor_get(v___x_2918_, 0);
lean_dec(v_unused_2953_);
v___x_2923_ = v___x_2918_;
v_isShared_2924_ = v_isSharedCheck_2952_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_err_2921_);
lean_dec(v___x_2918_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2952_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v_idx_2925_; uint8_t v___x_2926_; 
v_idx_2925_ = lean_ctor_get(v_a_2875_, 1);
v___x_2926_ = lean_nat_dec_eq(v_idx_2925_, v_idx_2925_);
if (v___x_2926_ == 0)
{
lean_object* v___x_2928_; 
lean_dec_ref(v_config_2874_);
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 0, v_a_2875_);
v___x_2928_ = v___x_2923_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2875_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v_err_2921_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
else
{
uint8_t v___x_2930_; lean_object* v___x_2931_; 
lean_del_object(v___x_2923_);
lean_dec(v_err_2921_);
v___x_2930_ = 0;
v___x_2931_ = l_Std_Http_URI_Parser_parsePath(v_config_2874_, v___x_2930_, v___x_2926_, v_a_2875_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_pos_2932_; lean_object* v_res_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2942_; 
v_pos_2932_ = lean_ctor_get(v___x_2931_, 0);
v_res_2933_ = lean_ctor_get(v___x_2931_, 1);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2935_ = v___x_2931_;
v_isShared_2936_ = v_isSharedCheck_2942_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_res_2933_);
lean_inc(v_pos_2932_);
lean_dec(v___x_2931_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2942_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2940_; 
v___x_2937_ = lean_box(0);
v___x_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
lean_ctor_set(v___x_2938_, 1, v_res_2933_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 1, v___x_2938_);
v___x_2940_ = v___x_2935_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_pos_2932_);
lean_ctor_set(v_reuseFailAlloc_2941_, 1, v___x_2938_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
else
{
lean_object* v_pos_2943_; lean_object* v_err_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2951_; 
v_pos_2943_ = lean_ctor_get(v___x_2931_, 0);
v_err_2944_ = lean_ctor_get(v___x_2931_, 1);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2946_ = v___x_2931_;
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_err_2944_);
lean_inc(v_pos_2943_);
lean_dec(v___x_2931_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_pos_2943_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v_err_2944_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
}
}
}
v___jp_2876_:
{
lean_object* v___x_2880_; 
v___x_2880_ = l_Std_Http_URI_Parser_parsePath(v_config_2874_, v___y_2877_, v___y_2877_, v_pos_2878_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_pos_2881_; lean_object* v_res_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2890_; 
v_pos_2881_ = lean_ctor_get(v___x_2880_, 0);
v_res_2882_ = lean_ctor_get(v___x_2880_, 1);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2884_ = v___x_2880_;
v_isShared_2885_ = v_isSharedCheck_2890_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_res_2882_);
lean_inc(v_pos_2881_);
lean_dec(v___x_2880_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2890_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2886_; lean_object* v___x_2888_; 
v___x_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2886_, 0, v_res_2879_);
lean_ctor_set(v___x_2886_, 1, v_res_2882_);
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 1, v___x_2886_);
v___x_2888_ = v___x_2884_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_pos_2881_);
lean_ctor_set(v_reuseFailAlloc_2889_, 1, v___x_2886_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
else
{
lean_object* v_pos_2891_; lean_object* v_err_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
lean_dec(v_res_2879_);
v_pos_2891_ = lean_ctor_get(v___x_2880_, 0);
v_err_2892_ = lean_ctor_get(v___x_2880_, 1);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2880_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_err_2892_);
lean_inc(v_pos_2891_);
lean_dec(v___x_2880_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_pos_2891_);
lean_ctor_set(v_reuseFailAlloc_2898_, 1, v_err_2892_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
v___jp_2900_:
{
lean_object* v_idx_2904_; uint8_t v___x_2905_; 
v_idx_2904_ = lean_ctor_get(v___y_2902_, 1);
v___x_2905_ = lean_nat_dec_eq(v_idx_2904_, v_idx_2904_);
if (v___x_2905_ == 0)
{
lean_object* v___x_2906_; 
lean_dec_ref(v_config_2874_);
v___x_2906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___y_2902_);
lean_ctor_set(v___x_2906_, 1, v_err_2903_);
return v___x_2906_;
}
else
{
lean_object* v___x_2907_; 
lean_dec(v_err_2903_);
v___x_2907_ = lean_box(0);
v___y_2877_ = v___y_2901_;
v_pos_2878_ = v___y_2902_;
v_res_2879_ = v___x_2907_;
goto v___jp_2876_;
}
}
v___jp_2908_:
{
uint8_t v___x_2910_; lean_object* v___x_2911_; 
v___x_2910_ = 1;
lean_inc_ref(v_pos_2909_);
v___x_2911_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_2874_, v_pos_2909_);
if (lean_obj_tag(v___x_2911_) == 0)
{
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_pos_2912_; lean_object* v_res_2913_; lean_object* v___x_2914_; 
lean_dec_ref(v_pos_2909_);
v_pos_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_pos_2912_);
v_res_2913_ = lean_ctor_get(v___x_2911_, 1);
lean_inc(v_res_2913_);
lean_dec_ref_known(v___x_2911_, 2);
v___x_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2914_, 0, v_res_2913_);
v___y_2877_ = v___x_2910_;
v_pos_2878_ = v_pos_2912_;
v_res_2879_ = v___x_2914_;
goto v___jp_2876_;
}
else
{
lean_object* v_err_2915_; 
v_err_2915_ = lean_ctor_get(v___x_2911_, 1);
lean_inc(v_err_2915_);
lean_dec_ref_known(v___x_2911_, 2);
v___y_2901_ = v___x_2910_;
v___y_2902_ = v_pos_2909_;
v_err_2903_ = v_err_2915_;
goto v___jp_2900_;
}
}
else
{
lean_object* v_err_2916_; 
v_err_2916_ = lean_ctor_get(v___x_2911_, 1);
lean_inc(v_err_2916_);
lean_dec_ref_known(v___x_2911_, 2);
v___y_2901_ = v___x_2910_;
v___y_2902_ = v_pos_2909_;
v_err_2903_ = v_err_2916_;
goto v___jp_2900_;
}
}
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__0(void){
_start:
{
uint8_t v___x_2954_; lean_object* v___x_2955_; 
v___x_2954_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v___x_2955_ = lean_uint8_to_nat(v___x_2954_);
return v___x_2955_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__1(void){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__0, &l_Std_Http_URI_Parser_parseURI___closed__0_once, _init_l_Std_Http_URI_Parser_parseURI___closed__0);
v___x_2957_ = l_Nat_reprFast(v___x_2956_);
return v___x_2957_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__2(void){
_start:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2958_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__1, &l_Std_Http_URI_Parser_parseURI___closed__1_once, _init_l_Std_Http_URI_Parser_parseURI___closed__1);
v___x_2959_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_2960_ = lean_string_append(v___x_2959_, v___x_2958_);
return v___x_2960_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__3(void){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2961_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_2962_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__2, &l_Std_Http_URI_Parser_parseURI___closed__2_once, _init_l_Std_Http_URI_Parser_parseURI___closed__2);
v___x_2963_ = lean_string_append(v___x_2962_, v___x_2961_);
return v___x_2963_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__4(void){
_start:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2964_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__3, &l_Std_Http_URI_Parser_parseURI___closed__3_once, _init_l_Std_Http_URI_Parser_parseURI___closed__3);
v___x_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
return v___x_2965_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__7(void){
_start:
{
uint8_t v___x_2969_; lean_object* v___x_2970_; 
v___x_2969_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_2970_ = lean_uint8_to_nat(v___x_2969_);
return v___x_2970_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__8(void){
_start:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2971_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__7, &l_Std_Http_URI_Parser_parseURI___closed__7_once, _init_l_Std_Http_URI_Parser_parseURI___closed__7);
v___x_2972_ = l_Nat_reprFast(v___x_2971_);
return v___x_2972_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__9(void){
_start:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2973_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__8, &l_Std_Http_URI_Parser_parseURI___closed__8_once, _init_l_Std_Http_URI_Parser_parseURI___closed__8);
v___x_2974_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_2975_ = lean_string_append(v___x_2974_, v___x_2973_);
return v___x_2975_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__10(void){
_start:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2976_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_2977_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__9, &l_Std_Http_URI_Parser_parseURI___closed__9_once, _init_l_Std_Http_URI_Parser_parseURI___closed__9);
v___x_2978_ = lean_string_append(v___x_2977_, v___x_2976_);
return v___x_2978_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__11(void){
_start:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2979_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__10, &l_Std_Http_URI_Parser_parseURI___closed__10_once, _init_l_Std_Http_URI_Parser_parseURI___closed__10);
v___x_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURI(lean_object* v_config_2981_, lean_object* v_a_2982_){
_start:
{
lean_object* v___x_2983_; 
v___x_2983_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_2981_, v_a_2982_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_pos_2984_; lean_object* v_res_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3116_; 
v_pos_2984_ = lean_ctor_get(v___x_2983_, 0);
v_res_2985_ = lean_ctor_get(v___x_2983_, 1);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_2987_ = v___x_2983_;
v_isShared_2988_ = v_isSharedCheck_3116_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_res_2985_);
lean_inc(v_pos_2984_);
lean_dec(v___x_2983_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3116_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v_array_2989_; lean_object* v_idx_2990_; lean_object* v___x_2991_; uint8_t v___x_2992_; 
v_array_2989_ = lean_ctor_get(v_pos_2984_, 0);
v_idx_2990_ = lean_ctor_get(v_pos_2984_, 1);
v___x_2991_ = lean_byte_array_size(v_array_2989_);
v___x_2992_ = lean_nat_dec_lt(v_idx_2990_, v___x_2991_);
if (v___x_2992_ == 0)
{
lean_object* v___x_2993_; lean_object* v___x_2995_; 
lean_dec(v_res_2985_);
lean_dec_ref(v_config_2981_);
v___x_2993_ = lean_box(0);
if (v_isShared_2988_ == 0)
{
lean_ctor_set_tag(v___x_2987_, 1);
lean_ctor_set(v___x_2987_, 1, v___x_2993_);
v___x_2995_ = v___x_2987_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_pos_2984_);
lean_ctor_set(v_reuseFailAlloc_2996_, 1, v___x_2993_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
else
{
uint8_t v___x_2997_; uint8_t v_got_2998_; uint8_t v___x_2999_; 
v___x_2997_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v_got_2998_ = lean_byte_array_fget(v_array_2989_, v_idx_2990_);
v___x_2999_ = lean_uint8_dec_eq(v_got_2998_, v___x_2997_);
if (v___x_2999_ == 0)
{
lean_object* v___x_3000_; lean_object* v___x_3002_; 
lean_dec(v_res_2985_);
lean_dec_ref(v_config_2981_);
v___x_3000_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
if (v_isShared_2988_ == 0)
{
lean_ctor_set_tag(v___x_2987_, 1);
lean_ctor_set(v___x_2987_, 1, v___x_3000_);
v___x_3002_ = v___x_2987_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_pos_2984_);
lean_ctor_set(v_reuseFailAlloc_3003_, 1, v___x_3000_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
else
{
lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3113_; 
lean_inc(v_idx_2990_);
lean_inc_ref(v_array_2989_);
v_isSharedCheck_3113_ = !lean_is_exclusive(v_pos_2984_);
if (v_isSharedCheck_3113_ == 0)
{
lean_object* v_unused_3114_; lean_object* v_unused_3115_; 
v_unused_3114_ = lean_ctor_get(v_pos_2984_, 1);
lean_dec(v_unused_3114_);
v_unused_3115_ = lean_ctor_get(v_pos_2984_, 0);
lean_dec(v_unused_3115_);
v___x_3005_ = v_pos_2984_;
v_isShared_3006_ = v_isSharedCheck_3113_;
goto v_resetjp_3004_;
}
else
{
lean_dec(v_pos_2984_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3113_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3010_; 
v___x_3007_ = lean_unsigned_to_nat(1u);
v___x_3008_ = lean_nat_add(v_idx_2990_, v___x_3007_);
lean_dec(v_idx_2990_);
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 1, v___x_3008_);
v___x_3010_ = v___x_3005_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_array_2989_);
lean_ctor_set(v_reuseFailAlloc_3112_, 1, v___x_3008_);
v___x_3010_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
lean_object* v___x_3011_; 
lean_inc_ref(v_config_2981_);
v___x_3011_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2981_, v___x_3010_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_res_3012_; lean_object* v_pos_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3102_; 
v_res_3012_ = lean_ctor_get(v___x_3011_, 1);
v_pos_3013_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3015_ = v___x_3011_;
v_isShared_3016_ = v_isSharedCheck_3102_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_res_3012_);
lean_inc(v_pos_3013_);
lean_dec(v___x_3011_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3102_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v_fst_3017_; lean_object* v_snd_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3101_; 
v_fst_3017_ = lean_ctor_get(v_res_3012_, 0);
v_snd_3018_ = lean_ctor_get(v_res_3012_, 1);
v_isSharedCheck_3101_ = !lean_is_exclusive(v_res_3012_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3020_ = v_res_3012_;
v_isShared_3021_ = v_isSharedCheck_3101_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_snd_3018_);
lean_inc(v_fst_3017_);
lean_dec(v_res_3012_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3101_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___y_3023_; lean_object* v_pos_3024_; lean_object* v_res_3025_; lean_object* v_idx_3031_; lean_object* v___y_3032_; lean_object* v_pos_3033_; lean_object* v_err_3034_; lean_object* v_pos_3042_; lean_object* v_array_3043_; lean_object* v_idx_3044_; lean_object* v_res_3045_; lean_object* v_array_3064_; lean_object* v_idx_3065_; lean_object* v_pos_3067_; lean_object* v_array_3068_; lean_object* v_idx_3069_; lean_object* v_err_3070_; lean_object* v___x_3074_; uint8_t v___x_3075_; 
v_array_3064_ = lean_ctor_get(v_pos_3013_, 0);
lean_inc_ref(v_array_3064_);
v_idx_3065_ = lean_ctor_get(v_pos_3013_, 1);
lean_inc(v_idx_3065_);
v___x_3074_ = lean_byte_array_size(v_array_3064_);
v___x_3075_ = lean_nat_dec_lt(v_idx_3065_, v___x_3074_);
if (v___x_3075_ == 0)
{
lean_object* v___x_3076_; 
v___x_3076_ = lean_box(0);
lean_inc(v_idx_3065_);
v_pos_3067_ = v_pos_3013_;
v_array_3068_ = v_array_3064_;
v_idx_3069_ = v_idx_3065_;
v_err_3070_ = v___x_3076_;
goto v___jp_3066_;
}
else
{
uint8_t v___x_3077_; uint8_t v_got_3078_; uint8_t v___x_3079_; 
v___x_3077_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3078_ = lean_byte_array_fget(v_array_3064_, v_idx_3065_);
v___x_3079_ = lean_uint8_dec_eq(v_got_3078_, v___x_3077_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; 
v___x_3080_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3065_);
v_pos_3067_ = v_pos_3013_;
v_array_3068_ = v_array_3064_;
v_idx_3069_ = v_idx_3065_;
v_err_3070_ = v___x_3080_;
goto v___jp_3066_;
}
else
{
lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3098_; 
v_isSharedCheck_3098_ = !lean_is_exclusive(v_pos_3013_);
if (v_isSharedCheck_3098_ == 0)
{
lean_object* v_unused_3099_; lean_object* v_unused_3100_; 
v_unused_3099_ = lean_ctor_get(v_pos_3013_, 1);
lean_dec(v_unused_3099_);
v_unused_3100_ = lean_ctor_get(v_pos_3013_, 0);
lean_dec(v_unused_3100_);
v___x_3082_ = v_pos_3013_;
v_isShared_3083_ = v_isSharedCheck_3098_;
goto v_resetjp_3081_;
}
else
{
lean_dec(v_pos_3013_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3098_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3084_; lean_object* v___x_3086_; 
v___x_3084_ = lean_nat_add(v_idx_3065_, v___x_3007_);
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 1, v___x_3084_);
v___x_3086_ = v___x_3082_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_array_3064_);
lean_ctor_set(v_reuseFailAlloc_3097_, 1, v___x_3084_);
v___x_3086_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
lean_object* v___x_3087_; 
lean_inc_ref(v_config_2981_);
v___x_3087_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2981_, v___x_3086_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v_pos_3088_; lean_object* v_res_3089_; lean_object* v_array_3090_; lean_object* v_idx_3091_; lean_object* v___x_3092_; 
lean_dec(v_idx_3065_);
v_pos_3088_ = lean_ctor_get(v___x_3087_, 0);
lean_inc(v_pos_3088_);
v_res_3089_ = lean_ctor_get(v___x_3087_, 1);
lean_inc(v_res_3089_);
lean_dec_ref_known(v___x_3087_, 2);
v_array_3090_ = lean_ctor_get(v_pos_3088_, 0);
lean_inc_ref(v_array_3090_);
v_idx_3091_ = lean_ctor_get(v_pos_3088_, 1);
lean_inc(v_idx_3091_);
v___x_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3092_, 0, v_res_3089_);
v_pos_3042_ = v_pos_3088_;
v_array_3043_ = v_array_3090_;
v_idx_3044_ = v_idx_3091_;
v_res_3045_ = v___x_3092_;
goto v___jp_3041_;
}
else
{
lean_object* v_pos_3093_; lean_object* v_err_3094_; lean_object* v_array_3095_; lean_object* v_idx_3096_; 
v_pos_3093_ = lean_ctor_get(v___x_3087_, 0);
lean_inc(v_pos_3093_);
v_err_3094_ = lean_ctor_get(v___x_3087_, 1);
lean_inc(v_err_3094_);
lean_dec_ref_known(v___x_3087_, 2);
v_array_3095_ = lean_ctor_get(v_pos_3093_, 0);
lean_inc_ref(v_array_3095_);
v_idx_3096_ = lean_ctor_get(v_pos_3093_, 1);
lean_inc(v_idx_3096_);
v_pos_3067_ = v_pos_3093_;
v_array_3068_ = v_array_3095_;
v_idx_3069_ = v_idx_3096_;
v_err_3070_ = v_err_3094_;
goto v___jp_3066_;
}
}
}
}
}
v___jp_3022_:
{
lean_object* v___x_3026_; lean_object* v___x_3028_; 
v___x_3026_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3026_, 0, v_res_2985_);
lean_ctor_set(v___x_3026_, 1, v_fst_3017_);
lean_ctor_set(v___x_3026_, 2, v_snd_3018_);
lean_ctor_set(v___x_3026_, 3, v___y_3023_);
lean_ctor_set(v___x_3026_, 4, v_res_3025_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 1, v___x_3026_);
lean_ctor_set(v___x_3015_, 0, v_pos_3024_);
v___x_3028_ = v___x_3015_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_pos_3024_);
lean_ctor_set(v_reuseFailAlloc_3029_, 1, v___x_3026_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
v___jp_3030_:
{
lean_object* v_idx_3035_; uint8_t v___x_3036_; 
v_idx_3035_ = lean_ctor_get(v_pos_3033_, 1);
v___x_3036_ = lean_nat_dec_eq(v_idx_3031_, v_idx_3035_);
lean_dec(v_idx_3031_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3038_; 
lean_dec(v___y_3032_);
lean_dec(v_snd_3018_);
lean_dec(v_fst_3017_);
lean_del_object(v___x_3015_);
lean_dec(v_res_2985_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set_tag(v___x_2987_, 1);
lean_ctor_set(v___x_2987_, 1, v_err_3034_);
lean_ctor_set(v___x_2987_, 0, v_pos_3033_);
v___x_3038_ = v___x_2987_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_pos_3033_);
lean_ctor_set(v_reuseFailAlloc_3039_, 1, v_err_3034_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
else
{
lean_object* v___x_3040_; 
lean_dec(v_err_3034_);
lean_del_object(v___x_2987_);
v___x_3040_ = lean_box(0);
v___y_3023_ = v___y_3032_;
v_pos_3024_ = v_pos_3033_;
v_res_3025_ = v___x_3040_;
goto v___jp_3022_;
}
}
v___jp_3041_:
{
lean_object* v___x_3046_; uint8_t v___x_3047_; 
v___x_3046_ = lean_byte_array_size(v_array_3043_);
v___x_3047_ = lean_nat_dec_lt(v_idx_3044_, v___x_3046_);
if (v___x_3047_ == 0)
{
lean_object* v___x_3048_; 
lean_dec_ref(v_array_3043_);
lean_del_object(v___x_3020_);
lean_dec_ref(v_config_2981_);
v___x_3048_ = lean_box(0);
v_idx_3031_ = v_idx_3044_;
v___y_3032_ = v_res_3045_;
v_pos_3033_ = v_pos_3042_;
v_err_3034_ = v___x_3048_;
goto v___jp_3030_;
}
else
{
uint8_t v___x_3049_; uint8_t v_got_3050_; uint8_t v___x_3051_; 
v___x_3049_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v_got_3050_ = lean_byte_array_fget(v_array_3043_, v_idx_3044_);
v___x_3051_ = lean_uint8_dec_eq(v_got_3050_, v___x_3049_);
if (v___x_3051_ == 0)
{
lean_object* v___x_3052_; 
lean_dec_ref(v_array_3043_);
lean_del_object(v___x_3020_);
lean_dec_ref(v_config_2981_);
v___x_3052_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__4, &l_Std_Http_URI_Parser_parseURI___closed__4_once, _init_l_Std_Http_URI_Parser_parseURI___closed__4);
v_idx_3031_ = v_idx_3044_;
v___y_3032_ = v_res_3045_;
v_pos_3033_ = v_pos_3042_;
v_err_3034_ = v___x_3052_;
goto v___jp_3030_;
}
else
{
lean_object* v___x_3053_; lean_object* v___x_3055_; 
lean_dec_ref(v_pos_3042_);
v___x_3053_ = lean_nat_add(v_idx_3044_, v___x_3007_);
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 1, v___x_3053_);
lean_ctor_set(v___x_3020_, 0, v_array_3043_);
v___x_3055_ = v___x_3020_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_array_3043_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v___x_3053_);
v___x_3055_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
lean_object* v___x_3056_; 
v___x_3056_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2981_, v___x_3055_);
lean_dec_ref(v_config_2981_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_pos_3057_; lean_object* v_res_3058_; lean_object* v___x_3059_; 
v_pos_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_pos_3057_);
v_res_3058_ = lean_ctor_get(v___x_3056_, 1);
lean_inc(v_res_3058_);
lean_dec_ref_known(v___x_3056_, 2);
v___x_3059_ = l_Std_Http_URI_EncodedFragment_decode(v_res_3058_);
lean_dec(v_res_3058_);
if (lean_obj_tag(v___x_3059_) == 1)
{
lean_dec(v_idx_3044_);
lean_del_object(v___x_2987_);
v___y_3023_ = v_res_3045_;
v_pos_3024_ = v_pos_3057_;
v_res_3025_ = v___x_3059_;
goto v___jp_3022_;
}
else
{
lean_object* v___x_3060_; 
lean_dec(v___x_3059_);
v___x_3060_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__6));
v_idx_3031_ = v_idx_3044_;
v___y_3032_ = v_res_3045_;
v_pos_3033_ = v_pos_3057_;
v_err_3034_ = v___x_3060_;
goto v___jp_3030_;
}
}
else
{
lean_object* v_pos_3061_; lean_object* v_err_3062_; 
v_pos_3061_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_pos_3061_);
v_err_3062_ = lean_ctor_get(v___x_3056_, 1);
lean_inc(v_err_3062_);
lean_dec_ref_known(v___x_3056_, 2);
v_idx_3031_ = v_idx_3044_;
v___y_3032_ = v_res_3045_;
v_pos_3033_ = v_pos_3061_;
v_err_3034_ = v_err_3062_;
goto v___jp_3030_;
}
}
}
}
}
v___jp_3066_:
{
uint8_t v___x_3071_; 
v___x_3071_ = lean_nat_dec_eq(v_idx_3065_, v_idx_3069_);
lean_dec(v_idx_3065_);
if (v___x_3071_ == 0)
{
lean_object* v___x_3072_; 
lean_dec(v_idx_3069_);
lean_dec_ref(v_array_3068_);
lean_del_object(v___x_3020_);
lean_dec(v_snd_3018_);
lean_dec(v_fst_3017_);
lean_del_object(v___x_3015_);
lean_del_object(v___x_2987_);
lean_dec(v_res_2985_);
lean_dec_ref(v_config_2981_);
v___x_3072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3072_, 0, v_pos_3067_);
lean_ctor_set(v___x_3072_, 1, v_err_3070_);
return v___x_3072_;
}
else
{
lean_object* v___x_3073_; 
lean_dec(v_err_3070_);
v___x_3073_ = lean_box(0);
v_pos_3042_ = v_pos_3067_;
v_array_3043_ = v_array_3068_;
v_idx_3044_ = v_idx_3069_;
v_res_3045_ = v___x_3073_;
goto v___jp_3041_;
}
}
}
}
}
else
{
lean_object* v_pos_3103_; lean_object* v_err_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_del_object(v___x_2987_);
lean_dec(v_res_2985_);
lean_dec_ref(v_config_2981_);
v_pos_3103_ = lean_ctor_get(v___x_3011_, 0);
v_err_3104_ = lean_ctor_get(v___x_3011_, 1);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3011_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_err_3104_);
lean_inc(v_pos_3103_);
lean_dec(v___x_3011_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_pos_3103_);
lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_err_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
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
lean_object* v_pos_3117_; lean_object* v_err_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_dec_ref(v_config_2981_);
v_pos_3117_ = lean_ctor_get(v___x_2983_, 0);
v_err_3118_ = lean_ctor_get(v___x_2983_, 1);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_2983_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_err_3118_);
lean_inc(v_pos_3117_);
lean_dec(v___x_2983_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_pos_3117_);
lean_ctor_set(v_reuseFailAlloc_3124_, 1, v_err_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0(void){
_start:
{
uint8_t v___x_3126_; lean_object* v___x_3127_; 
v___x_3126_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_3127_ = lean_uint8_to_nat(v___x_3126_);
return v___x_3127_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1(void){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0);
v___x_3129_ = l_Nat_reprFast(v___x_3128_);
return v___x_3129_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2(void){
_start:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3130_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1);
v___x_3131_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_3132_ = lean_string_append(v___x_3131_, v___x_3130_);
return v___x_3132_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3(void){
_start:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3133_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_3134_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2);
v___x_3135_ = lean_string_append(v___x_3134_, v___x_3133_);
return v___x_3135_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4(void){
_start:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3136_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3);
v___x_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(lean_object* v_a_3138_){
_start:
{
lean_object* v_array_3139_; lean_object* v_idx_3140_; lean_object* v___x_3141_; uint8_t v___x_3142_; 
v_array_3139_ = lean_ctor_get(v_a_3138_, 0);
v_idx_3140_ = lean_ctor_get(v_a_3138_, 1);
v___x_3141_ = lean_byte_array_size(v_array_3139_);
v___x_3142_ = lean_nat_dec_lt(v_idx_3140_, v___x_3141_);
if (v___x_3142_ == 0)
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3143_ = lean_box(0);
v___x_3144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3144_, 0, v_a_3138_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
return v___x_3144_;
}
else
{
uint8_t v___x_3145_; uint8_t v_got_3146_; uint8_t v___x_3147_; 
v___x_3145_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v_got_3146_ = lean_byte_array_fget(v_array_3139_, v_idx_3140_);
v___x_3147_ = lean_uint8_dec_eq(v_got_3146_, v___x_3145_);
if (v___x_3147_ == 0)
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3148_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4);
v___x_3149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3149_, 0, v_a_3138_);
lean_ctor_set(v___x_3149_, 1, v___x_3148_);
return v___x_3149_;
}
else
{
lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3160_; 
lean_inc(v_idx_3140_);
lean_inc_ref(v_array_3139_);
v_isSharedCheck_3160_ = !lean_is_exclusive(v_a_3138_);
if (v_isSharedCheck_3160_ == 0)
{
lean_object* v_unused_3161_; lean_object* v_unused_3162_; 
v_unused_3161_ = lean_ctor_get(v_a_3138_, 1);
lean_dec(v_unused_3161_);
v_unused_3162_ = lean_ctor_get(v_a_3138_, 0);
lean_dec(v_unused_3162_);
v___x_3151_ = v_a_3138_;
v_isShared_3152_ = v_isSharedCheck_3160_;
goto v_resetjp_3150_;
}
else
{
lean_dec(v_a_3138_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3160_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3156_; 
v___x_3153_ = lean_unsigned_to_nat(1u);
v___x_3154_ = lean_nat_add(v_idx_3140_, v___x_3153_);
lean_dec(v_idx_3140_);
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 1, v___x_3154_);
v___x_3156_ = v___x_3151_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_array_3139_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v___x_3154_);
v___x_3156_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = lean_box(3);
v___x_3158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3156_);
lean_ctor_set(v___x_3158_, 1, v___x_3157_);
return v___x_3158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(lean_object* v_config_3166_, lean_object* v_a_3167_){
_start:
{
lean_object* v_array_3171_; lean_object* v_idx_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; 
v_array_3171_ = lean_ctor_get(v_a_3167_, 0);
v_idx_3172_ = lean_ctor_get(v_a_3167_, 1);
v___x_3173_ = lean_byte_array_size(v_array_3171_);
v___x_3174_ = lean_nat_dec_lt(v_idx_3172_, v___x_3173_);
if (v___x_3174_ == 0)
{
lean_dec_ref(v_config_3166_);
goto v___jp_3168_;
}
else
{
uint8_t v___x_3175_; uint8_t v___x_3176_; uint8_t v___x_3177_; 
v___x_3175_ = lean_byte_array_fget(v_array_3171_, v_idx_3172_);
v___x_3176_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_3177_ = lean_uint8_dec_eq(v___x_3175_, v___x_3176_);
if (v___x_3177_ == 0)
{
lean_dec_ref(v_config_3166_);
goto v___jp_3168_;
}
else
{
lean_object* v___x_3178_; 
lean_inc_ref(v_a_3167_);
lean_inc_ref(v_config_3166_);
v___x_3178_ = l_Std_Http_URI_Parser_parsePath(v_config_3166_, v___x_3177_, v___x_3177_, v_a_3167_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v_pos_3179_; lean_object* v_res_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3225_; 
v_pos_3179_ = lean_ctor_get(v___x_3178_, 0);
v_res_3180_ = lean_ctor_get(v___x_3178_, 1);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3182_ = v___x_3178_;
v_isShared_3183_ = v_isSharedCheck_3225_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_res_3180_);
lean_inc(v_pos_3179_);
lean_dec(v___x_3178_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3225_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v_pos_3185_; lean_object* v_res_3186_; lean_object* v_array_3191_; lean_object* v_idx_3192_; lean_object* v_pos_3194_; lean_object* v_idx_3195_; lean_object* v_err_3196_; lean_object* v___x_3200_; uint8_t v___x_3201_; 
v_array_3191_ = lean_ctor_get(v_pos_3179_, 0);
v_idx_3192_ = lean_ctor_get(v_pos_3179_, 1);
lean_inc(v_idx_3192_);
v___x_3200_ = lean_byte_array_size(v_array_3191_);
v___x_3201_ = lean_nat_dec_lt(v_idx_3192_, v___x_3200_);
if (v___x_3201_ == 0)
{
lean_object* v___x_3202_; 
lean_dec_ref(v_config_3166_);
v___x_3202_ = lean_box(0);
lean_inc(v_idx_3192_);
v_pos_3194_ = v_pos_3179_;
v_idx_3195_ = v_idx_3192_;
v_err_3196_ = v___x_3202_;
goto v___jp_3193_;
}
else
{
uint8_t v___x_3203_; uint8_t v_got_3204_; uint8_t v___x_3205_; 
v___x_3203_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3204_ = lean_byte_array_fget(v_array_3191_, v_idx_3192_);
v___x_3205_ = lean_uint8_dec_eq(v_got_3204_, v___x_3203_);
if (v___x_3205_ == 0)
{
lean_object* v___x_3206_; 
lean_dec_ref(v_config_3166_);
v___x_3206_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3192_);
v_pos_3194_ = v_pos_3179_;
v_idx_3195_ = v_idx_3192_;
v_err_3196_ = v___x_3206_;
goto v___jp_3193_;
}
else
{
lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3222_; 
lean_inc_ref(v_array_3191_);
v_isSharedCheck_3222_ = !lean_is_exclusive(v_pos_3179_);
if (v_isSharedCheck_3222_ == 0)
{
lean_object* v_unused_3223_; lean_object* v_unused_3224_; 
v_unused_3223_ = lean_ctor_get(v_pos_3179_, 1);
lean_dec(v_unused_3223_);
v_unused_3224_ = lean_ctor_get(v_pos_3179_, 0);
lean_dec(v_unused_3224_);
v___x_3208_ = v_pos_3179_;
v_isShared_3209_ = v_isSharedCheck_3222_;
goto v_resetjp_3207_;
}
else
{
lean_dec(v_pos_3179_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3222_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3213_; 
v___x_3210_ = lean_unsigned_to_nat(1u);
v___x_3211_ = lean_nat_add(v_idx_3192_, v___x_3210_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 1, v___x_3211_);
v___x_3213_ = v___x_3208_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_array_3191_);
lean_ctor_set(v_reuseFailAlloc_3221_, 1, v___x_3211_);
v___x_3213_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
lean_object* v___x_3214_; 
v___x_3214_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3166_, v___x_3213_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v_pos_3215_; lean_object* v_res_3216_; lean_object* v___x_3217_; 
lean_dec(v_idx_3192_);
lean_dec_ref(v_a_3167_);
v_pos_3215_ = lean_ctor_get(v___x_3214_, 0);
lean_inc(v_pos_3215_);
v_res_3216_ = lean_ctor_get(v___x_3214_, 1);
lean_inc(v_res_3216_);
lean_dec_ref_known(v___x_3214_, 2);
v___x_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3217_, 0, v_res_3216_);
v_pos_3185_ = v_pos_3215_;
v_res_3186_ = v___x_3217_;
goto v___jp_3184_;
}
else
{
lean_object* v_pos_3218_; lean_object* v_err_3219_; lean_object* v_idx_3220_; 
v_pos_3218_ = lean_ctor_get(v___x_3214_, 0);
lean_inc(v_pos_3218_);
v_err_3219_ = lean_ctor_get(v___x_3214_, 1);
lean_inc(v_err_3219_);
lean_dec_ref_known(v___x_3214_, 2);
v_idx_3220_ = lean_ctor_get(v_pos_3218_, 1);
lean_inc(v_idx_3220_);
v_pos_3194_ = v_pos_3218_;
v_idx_3195_ = v_idx_3220_;
v_err_3196_ = v_err_3219_;
goto v___jp_3193_;
}
}
}
}
}
v___jp_3184_:
{
lean_object* v___x_3187_; lean_object* v___x_3189_; 
v___x_3187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3187_, 0, v_res_3180_);
lean_ctor_set(v___x_3187_, 1, v_res_3186_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 1, v___x_3187_);
lean_ctor_set(v___x_3182_, 0, v_pos_3185_);
v___x_3189_ = v___x_3182_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_pos_3185_);
lean_ctor_set(v_reuseFailAlloc_3190_, 1, v___x_3187_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
v___jp_3193_:
{
uint8_t v___x_3197_; 
v___x_3197_ = lean_nat_dec_eq(v_idx_3192_, v_idx_3195_);
lean_dec(v_idx_3195_);
lean_dec(v_idx_3192_);
if (v___x_3197_ == 0)
{
lean_object* v___x_3198_; 
lean_dec_ref(v_pos_3194_);
lean_del_object(v___x_3182_);
lean_dec(v_res_3180_);
v___x_3198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3198_, 0, v_a_3167_);
lean_ctor_set(v___x_3198_, 1, v_err_3196_);
return v___x_3198_;
}
else
{
lean_object* v___x_3199_; 
lean_dec(v_err_3196_);
lean_dec_ref(v_a_3167_);
v___x_3199_ = lean_box(0);
v_pos_3185_ = v_pos_3194_;
v_res_3186_ = v___x_3199_;
goto v___jp_3184_;
}
}
}
}
else
{
lean_object* v_err_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
lean_dec_ref(v_config_3166_);
v_err_3226_ = lean_ctor_get(v___x_3178_, 1);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3233_ == 0)
{
lean_object* v_unused_3234_; 
v_unused_3234_ = lean_ctor_get(v___x_3178_, 0);
lean_dec(v_unused_3234_);
v___x_3228_ = v___x_3178_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_err_3226_);
lean_dec(v___x_3178_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v_a_3167_);
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3167_);
lean_ctor_set(v_reuseFailAlloc_3232_, 1, v_err_3226_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
}
v___jp_3168_:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3169_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1));
v___x_3170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3170_, 0, v_a_3167_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
return v___x_3170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(lean_object* v_config_3235_, lean_object* v_scheme_3236_, lean_object* v_a_3237_){
_start:
{
lean_object* v_array_3238_; lean_object* v_idx_3239_; lean_object* v___x_3240_; uint8_t v___x_3241_; 
v_array_3238_ = lean_ctor_get(v_a_3237_, 0);
v_idx_3239_ = lean_ctor_get(v_a_3237_, 1);
v___x_3240_ = lean_byte_array_size(v_array_3238_);
v___x_3241_ = lean_nat_dec_lt(v_idx_3239_, v___x_3240_);
if (v___x_3241_ == 0)
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
lean_dec_ref(v_scheme_3236_);
lean_dec_ref(v_config_3235_);
v___x_3242_ = lean_box(0);
v___x_3243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3243_, 0, v_a_3237_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
return v___x_3243_;
}
else
{
uint8_t v___x_3244_; uint8_t v_got_3245_; uint8_t v___x_3246_; 
v___x_3244_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v_got_3245_ = lean_byte_array_fget(v_array_3238_, v_idx_3239_);
v___x_3246_ = lean_uint8_dec_eq(v_got_3245_, v___x_3244_);
if (v___x_3246_ == 0)
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
lean_dec_ref(v_scheme_3236_);
lean_dec_ref(v_config_3235_);
v___x_3247_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
v___x_3248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3248_, 0, v_a_3237_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
return v___x_3248_;
}
else
{
lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3323_; 
lean_inc(v_idx_3239_);
lean_inc_ref(v_array_3238_);
v_isSharedCheck_3323_ = !lean_is_exclusive(v_a_3237_);
if (v_isSharedCheck_3323_ == 0)
{
lean_object* v_unused_3324_; lean_object* v_unused_3325_; 
v_unused_3324_ = lean_ctor_get(v_a_3237_, 1);
lean_dec(v_unused_3324_);
v_unused_3325_ = lean_ctor_get(v_a_3237_, 0);
lean_dec(v_unused_3325_);
v___x_3250_ = v_a_3237_;
v_isShared_3251_ = v_isSharedCheck_3323_;
goto v_resetjp_3249_;
}
else
{
lean_dec(v_a_3237_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3323_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3255_; 
v___x_3252_ = lean_unsigned_to_nat(1u);
v___x_3253_ = lean_nat_add(v_idx_3239_, v___x_3252_);
lean_dec(v_idx_3239_);
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 1, v___x_3253_);
v___x_3255_ = v___x_3250_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_array_3238_);
lean_ctor_set(v_reuseFailAlloc_3322_, 1, v___x_3253_);
v___x_3255_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
lean_object* v___x_3256_; 
lean_inc_ref(v_config_3235_);
v___x_3256_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3235_, v___x_3255_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_res_3257_; lean_object* v_pos_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3312_; 
v_res_3257_ = lean_ctor_get(v___x_3256_, 1);
v_pos_3258_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3260_ = v___x_3256_;
v_isShared_3261_ = v_isSharedCheck_3312_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_res_3257_);
lean_inc(v_pos_3258_);
lean_dec(v___x_3256_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3312_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v_fst_3262_; lean_object* v_snd_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3311_; 
v_fst_3262_ = lean_ctor_get(v_res_3257_, 0);
v_snd_3263_ = lean_ctor_get(v_res_3257_, 1);
v_isSharedCheck_3311_ = !lean_is_exclusive(v_res_3257_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3265_ = v_res_3257_;
v_isShared_3266_ = v_isSharedCheck_3311_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_snd_3263_);
lean_inc(v_fst_3262_);
lean_dec(v_res_3257_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3311_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v_pos_3268_; lean_object* v_res_3269_; lean_object* v_array_3276_; lean_object* v_idx_3277_; lean_object* v_pos_3279_; lean_object* v_idx_3280_; lean_object* v_err_3281_; lean_object* v___x_3287_; uint8_t v___x_3288_; 
v_array_3276_ = lean_ctor_get(v_pos_3258_, 0);
v_idx_3277_ = lean_ctor_get(v_pos_3258_, 1);
lean_inc(v_idx_3277_);
v___x_3287_ = lean_byte_array_size(v_array_3276_);
v___x_3288_ = lean_nat_dec_lt(v_idx_3277_, v___x_3287_);
if (v___x_3288_ == 0)
{
lean_object* v___x_3289_; 
lean_dec_ref(v_config_3235_);
v___x_3289_ = lean_box(0);
lean_inc(v_idx_3277_);
v_pos_3279_ = v_pos_3258_;
v_idx_3280_ = v_idx_3277_;
v_err_3281_ = v___x_3289_;
goto v___jp_3278_;
}
else
{
uint8_t v___x_3290_; uint8_t v_got_3291_; uint8_t v___x_3292_; 
v___x_3290_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3291_ = lean_byte_array_fget(v_array_3276_, v_idx_3277_);
v___x_3292_ = lean_uint8_dec_eq(v_got_3291_, v___x_3290_);
if (v___x_3292_ == 0)
{
lean_object* v___x_3293_; 
lean_dec_ref(v_config_3235_);
v___x_3293_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3277_);
v_pos_3279_ = v_pos_3258_;
v_idx_3280_ = v_idx_3277_;
v_err_3281_ = v___x_3293_;
goto v___jp_3278_;
}
else
{
lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3308_; 
lean_inc_ref(v_array_3276_);
v_isSharedCheck_3308_ = !lean_is_exclusive(v_pos_3258_);
if (v_isSharedCheck_3308_ == 0)
{
lean_object* v_unused_3309_; lean_object* v_unused_3310_; 
v_unused_3309_ = lean_ctor_get(v_pos_3258_, 1);
lean_dec(v_unused_3309_);
v_unused_3310_ = lean_ctor_get(v_pos_3258_, 0);
lean_dec(v_unused_3310_);
v___x_3295_ = v_pos_3258_;
v_isShared_3296_ = v_isSharedCheck_3308_;
goto v_resetjp_3294_;
}
else
{
lean_dec(v_pos_3258_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3308_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3297_; lean_object* v___x_3299_; 
v___x_3297_ = lean_nat_add(v_idx_3277_, v___x_3252_);
if (v_isShared_3296_ == 0)
{
lean_ctor_set(v___x_3295_, 1, v___x_3297_);
v___x_3299_ = v___x_3295_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_array_3276_);
lean_ctor_set(v_reuseFailAlloc_3307_, 1, v___x_3297_);
v___x_3299_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
lean_object* v___x_3300_; 
v___x_3300_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3235_, v___x_3299_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v_pos_3301_; lean_object* v_res_3302_; lean_object* v___x_3303_; 
lean_dec(v_idx_3277_);
lean_del_object(v___x_3265_);
v_pos_3301_ = lean_ctor_get(v___x_3300_, 0);
lean_inc(v_pos_3301_);
v_res_3302_ = lean_ctor_get(v___x_3300_, 1);
lean_inc(v_res_3302_);
lean_dec_ref_known(v___x_3300_, 2);
v___x_3303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3303_, 0, v_res_3302_);
v_pos_3268_ = v_pos_3301_;
v_res_3269_ = v___x_3303_;
goto v___jp_3267_;
}
else
{
lean_object* v_pos_3304_; lean_object* v_err_3305_; lean_object* v_idx_3306_; 
v_pos_3304_ = lean_ctor_get(v___x_3300_, 0);
lean_inc(v_pos_3304_);
v_err_3305_ = lean_ctor_get(v___x_3300_, 1);
lean_inc(v_err_3305_);
lean_dec_ref_known(v___x_3300_, 2);
v_idx_3306_ = lean_ctor_get(v_pos_3304_, 1);
lean_inc(v_idx_3306_);
v_pos_3279_ = v_pos_3304_;
v_idx_3280_ = v_idx_3306_;
v_err_3281_ = v_err_3305_;
goto v___jp_3278_;
}
}
}
}
}
v___jp_3267_:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3274_; 
v___x_3270_ = lean_box(0);
v___x_3271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3271_, 0, v_scheme_3236_);
lean_ctor_set(v___x_3271_, 1, v_fst_3262_);
lean_ctor_set(v___x_3271_, 2, v_snd_3263_);
lean_ctor_set(v___x_3271_, 3, v_res_3269_);
lean_ctor_set(v___x_3271_, 4, v___x_3270_);
v___x_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3271_);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 1, v___x_3272_);
lean_ctor_set(v___x_3260_, 0, v_pos_3268_);
v___x_3274_ = v___x_3260_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_pos_3268_);
lean_ctor_set(v_reuseFailAlloc_3275_, 1, v___x_3272_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
v___jp_3278_:
{
uint8_t v___x_3282_; 
v___x_3282_ = lean_nat_dec_eq(v_idx_3277_, v_idx_3280_);
lean_dec(v_idx_3280_);
lean_dec(v_idx_3277_);
if (v___x_3282_ == 0)
{
lean_object* v___x_3284_; 
lean_dec(v_snd_3263_);
lean_dec(v_fst_3262_);
lean_del_object(v___x_3260_);
lean_dec_ref(v_scheme_3236_);
if (v_isShared_3266_ == 0)
{
lean_ctor_set_tag(v___x_3265_, 1);
lean_ctor_set(v___x_3265_, 1, v_err_3281_);
lean_ctor_set(v___x_3265_, 0, v_pos_3279_);
v___x_3284_ = v___x_3265_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_pos_3279_);
lean_ctor_set(v_reuseFailAlloc_3285_, 1, v_err_3281_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
else
{
lean_object* v___x_3286_; 
lean_dec(v_err_3281_);
lean_del_object(v___x_3265_);
v___x_3286_ = lean_box(0);
v_pos_3268_ = v_pos_3279_;
v_res_3269_ = v___x_3286_;
goto v___jp_3267_;
}
}
}
}
}
else
{
lean_object* v_pos_3313_; lean_object* v_err_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3321_; 
lean_dec_ref(v_scheme_3236_);
lean_dec_ref(v_config_3235_);
v_pos_3313_ = lean_ctor_get(v___x_3256_, 0);
v_err_3314_ = lean_ctor_get(v___x_3256_, 1);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3316_ = v___x_3256_;
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_err_3314_);
lean_inc(v_pos_3313_);
lean_dec(v___x_3256_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3319_; 
if (v_isShared_3317_ == 0)
{
v___x_3319_ = v___x_3316_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_pos_3313_);
lean_ctor_set(v_reuseFailAlloc_3320_, 1, v_err_3314_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(lean_object* v_config_3334_, lean_object* v_a_3335_){
_start:
{
lean_object* v___x_3339_; 
lean_inc_ref(v_a_3335_);
v___x_3339_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3334_, v_a_3335_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v_pos_3340_; lean_object* v_res_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3437_; 
v_pos_3340_ = lean_ctor_get(v___x_3339_, 0);
v_res_3341_ = lean_ctor_get(v___x_3339_, 1);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3343_ = v___x_3339_;
v_isShared_3344_ = v_isSharedCheck_3437_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_res_3341_);
lean_inc(v_pos_3340_);
lean_dec(v___x_3339_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3437_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v_pos_3348_; lean_object* v_res_3349_; lean_object* v_idx_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v_pos_3360_; lean_object* v_idx_3361_; lean_object* v_err_3362_; lean_object* v___x_3431_; uint8_t v___x_3432_; 
v___x_3431_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2));
v___x_3432_ = lean_string_dec_eq(v_res_3341_, v___x_3431_);
if (v___x_3432_ == 0)
{
lean_object* v___x_3433_; uint8_t v___x_3434_; 
v___x_3433_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3));
v___x_3434_ = lean_string_dec_eq(v_res_3341_, v___x_3433_);
if (v___x_3434_ == 0)
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
lean_del_object(v___x_3343_);
lean_dec(v_res_3341_);
lean_dec(v_pos_3340_);
lean_dec_ref(v_config_3334_);
v___x_3435_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5));
v___x_3436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3436_, 0, v_a_3335_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
return v___x_3436_;
}
else
{
goto v___jp_3366_;
}
}
else
{
goto v___jp_3366_;
}
v___jp_3345_:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3354_; 
v___x_3350_ = lean_box(0);
v___x_3351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3351_, 0, v_res_3341_);
lean_ctor_set(v___x_3351_, 1, v___y_3346_);
lean_ctor_set(v___x_3351_, 2, v___y_3347_);
lean_ctor_set(v___x_3351_, 3, v_res_3349_);
lean_ctor_set(v___x_3351_, 4, v___x_3350_);
v___x_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3351_);
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 1, v___x_3352_);
lean_ctor_set(v___x_3343_, 0, v_pos_3348_);
v___x_3354_ = v___x_3343_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_pos_3348_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v___x_3352_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
v___jp_3356_:
{
uint8_t v___x_3363_; 
v___x_3363_ = lean_nat_dec_eq(v_idx_3357_, v_idx_3361_);
lean_dec(v_idx_3361_);
lean_dec(v_idx_3357_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; 
lean_dec_ref(v_pos_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_del_object(v___x_3343_);
lean_dec(v_res_3341_);
v___x_3364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3364_, 0, v_a_3335_);
lean_ctor_set(v___x_3364_, 1, v_err_3362_);
return v___x_3364_;
}
else
{
lean_object* v___x_3365_; 
lean_dec(v_err_3362_);
lean_dec_ref(v_a_3335_);
v___x_3365_ = lean_box(0);
v___y_3346_ = v___y_3358_;
v___y_3347_ = v___y_3359_;
v_pos_3348_ = v_pos_3360_;
v_res_3349_ = v___x_3365_;
goto v___jp_3345_;
}
}
v___jp_3366_:
{
lean_object* v_array_3367_; lean_object* v_idx_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3430_; 
v_array_3367_ = lean_ctor_get(v_pos_3340_, 0);
v_idx_3368_ = lean_ctor_get(v_pos_3340_, 1);
v_isSharedCheck_3430_ = !lean_is_exclusive(v_pos_3340_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3370_ = v_pos_3340_;
v_isShared_3371_ = v_isSharedCheck_3430_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_idx_3368_);
lean_inc(v_array_3367_);
lean_dec(v_pos_3340_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3430_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3372_; uint8_t v___x_3373_; 
v___x_3372_ = lean_byte_array_size(v_array_3367_);
v___x_3373_ = lean_nat_dec_lt(v_idx_3368_, v___x_3372_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
lean_del_object(v___x_3370_);
lean_dec(v_idx_3368_);
lean_dec_ref(v_array_3367_);
lean_del_object(v___x_3343_);
lean_dec(v_res_3341_);
lean_dec_ref(v_config_3334_);
v___x_3374_ = lean_box(0);
v___x_3375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3375_, 0, v_a_3335_);
lean_ctor_set(v___x_3375_, 1, v___x_3374_);
return v___x_3375_;
}
else
{
uint8_t v___x_3376_; uint8_t v_got_3377_; uint8_t v___x_3378_; 
v___x_3376_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v_got_3377_ = lean_byte_array_fget(v_array_3367_, v_idx_3368_);
v___x_3378_ = lean_uint8_dec_eq(v_got_3377_, v___x_3376_);
if (v___x_3378_ == 0)
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
lean_del_object(v___x_3370_);
lean_dec(v_idx_3368_);
lean_dec_ref(v_array_3367_);
lean_del_object(v___x_3343_);
lean_dec(v_res_3341_);
lean_dec_ref(v_config_3334_);
v___x_3379_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
v___x_3380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3380_, 0, v_a_3335_);
lean_ctor_set(v___x_3380_, 1, v___x_3379_);
return v___x_3380_;
}
else
{
lean_object* v___x_3381_; lean_object* v___x_3382_; uint8_t v___x_3383_; 
v___x_3381_ = lean_unsigned_to_nat(1u);
v___x_3382_ = lean_nat_add(v_idx_3368_, v___x_3381_);
lean_dec(v_idx_3368_);
v___x_3383_ = lean_nat_dec_lt(v___x_3382_, v___x_3372_);
if (v___x_3383_ == 0)
{
lean_dec(v___x_3382_);
lean_del_object(v___x_3370_);
lean_dec_ref(v_array_3367_);
lean_del_object(v___x_3343_);
lean_dec(v_res_3341_);
lean_dec_ref(v_config_3334_);
goto v___jp_3336_;
}
else
{
uint8_t v___x_3384_; uint8_t v___x_3385_; uint8_t v___x_3386_; 
v___x_3384_ = lean_byte_array_fget(v_array_3367_, v___x_3382_);
v___x_3385_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_3386_ = lean_uint8_dec_eq(v___x_3384_, v___x_3385_);
if (v___x_3386_ == 0)
{
lean_dec(v___x_3382_);
lean_del_object(v___x_3370_);
lean_dec_ref(v_array_3367_);
lean_del_object(v___x_3343_);
lean_dec(v_res_3341_);
lean_dec_ref(v_config_3334_);
goto v___jp_3336_;
}
else
{
lean_object* v___x_3388_; 
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 1, v___x_3382_);
v___x_3388_ = v___x_3370_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_array_3367_);
lean_ctor_set(v_reuseFailAlloc_3429_, 1, v___x_3382_);
v___x_3388_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
lean_object* v___x_3389_; 
lean_inc_ref(v_config_3334_);
v___x_3389_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3334_, v___x_3388_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v_res_3390_; lean_object* v_pos_3391_; lean_object* v_fst_3392_; lean_object* v_snd_3393_; lean_object* v_array_3394_; lean_object* v_idx_3395_; lean_object* v___x_3396_; uint8_t v___x_3397_; 
v_res_3390_ = lean_ctor_get(v___x_3389_, 1);
lean_inc(v_res_3390_);
v_pos_3391_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_pos_3391_);
lean_dec_ref_known(v___x_3389_, 2);
v_fst_3392_ = lean_ctor_get(v_res_3390_, 0);
lean_inc(v_fst_3392_);
v_snd_3393_ = lean_ctor_get(v_res_3390_, 1);
lean_inc(v_snd_3393_);
lean_dec(v_res_3390_);
v_array_3394_ = lean_ctor_get(v_pos_3391_, 0);
v_idx_3395_ = lean_ctor_get(v_pos_3391_, 1);
lean_inc(v_idx_3395_);
v___x_3396_ = lean_byte_array_size(v_array_3394_);
v___x_3397_ = lean_nat_dec_lt(v_idx_3395_, v___x_3396_);
if (v___x_3397_ == 0)
{
lean_object* v___x_3398_; 
lean_dec_ref(v_config_3334_);
v___x_3398_ = lean_box(0);
lean_inc(v_idx_3395_);
v_idx_3357_ = v_idx_3395_;
v___y_3358_ = v_fst_3392_;
v___y_3359_ = v_snd_3393_;
v_pos_3360_ = v_pos_3391_;
v_idx_3361_ = v_idx_3395_;
v_err_3362_ = v___x_3398_;
goto v___jp_3356_;
}
else
{
uint8_t v___x_3399_; uint8_t v_got_3400_; uint8_t v___x_3401_; 
v___x_3399_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3400_ = lean_byte_array_fget(v_array_3394_, v_idx_3395_);
v___x_3401_ = lean_uint8_dec_eq(v_got_3400_, v___x_3399_);
if (v___x_3401_ == 0)
{
lean_object* v___x_3402_; 
lean_dec_ref(v_config_3334_);
v___x_3402_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3395_);
v_idx_3357_ = v_idx_3395_;
v___y_3358_ = v_fst_3392_;
v___y_3359_ = v_snd_3393_;
v_pos_3360_ = v_pos_3391_;
v_idx_3361_ = v_idx_3395_;
v_err_3362_ = v___x_3402_;
goto v___jp_3356_;
}
else
{
lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3417_; 
lean_inc_ref(v_array_3394_);
v_isSharedCheck_3417_ = !lean_is_exclusive(v_pos_3391_);
if (v_isSharedCheck_3417_ == 0)
{
lean_object* v_unused_3418_; lean_object* v_unused_3419_; 
v_unused_3418_ = lean_ctor_get(v_pos_3391_, 1);
lean_dec(v_unused_3418_);
v_unused_3419_ = lean_ctor_get(v_pos_3391_, 0);
lean_dec(v_unused_3419_);
v___x_3404_ = v_pos_3391_;
v_isShared_3405_ = v_isSharedCheck_3417_;
goto v_resetjp_3403_;
}
else
{
lean_dec(v_pos_3391_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3417_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3406_; lean_object* v___x_3408_; 
v___x_3406_ = lean_nat_add(v_idx_3395_, v___x_3381_);
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 1, v___x_3406_);
v___x_3408_ = v___x_3404_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_array_3394_);
lean_ctor_set(v_reuseFailAlloc_3416_, 1, v___x_3406_);
v___x_3408_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
lean_object* v___x_3409_; 
v___x_3409_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3334_, v___x_3408_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_pos_3410_; lean_object* v_res_3411_; lean_object* v___x_3412_; 
lean_dec(v_idx_3395_);
lean_dec_ref(v_a_3335_);
v_pos_3410_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_pos_3410_);
v_res_3411_ = lean_ctor_get(v___x_3409_, 1);
lean_inc(v_res_3411_);
lean_dec_ref_known(v___x_3409_, 2);
v___x_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3412_, 0, v_res_3411_);
v___y_3346_ = v_fst_3392_;
v___y_3347_ = v_snd_3393_;
v_pos_3348_ = v_pos_3410_;
v_res_3349_ = v___x_3412_;
goto v___jp_3345_;
}
else
{
lean_object* v_pos_3413_; lean_object* v_err_3414_; lean_object* v_idx_3415_; 
v_pos_3413_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_pos_3413_);
v_err_3414_ = lean_ctor_get(v___x_3409_, 1);
lean_inc(v_err_3414_);
lean_dec_ref_known(v___x_3409_, 2);
v_idx_3415_ = lean_ctor_get(v_pos_3413_, 1);
lean_inc(v_idx_3415_);
v_idx_3357_ = v_idx_3395_;
v___y_3358_ = v_fst_3392_;
v___y_3359_ = v_snd_3393_;
v_pos_3360_ = v_pos_3413_;
v_idx_3361_ = v_idx_3415_;
v_err_3362_ = v_err_3414_;
goto v___jp_3356_;
}
}
}
}
}
}
else
{
lean_object* v_err_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3427_; 
lean_del_object(v___x_3343_);
lean_dec(v_res_3341_);
lean_dec_ref(v_config_3334_);
v_err_3420_ = lean_ctor_get(v___x_3389_, 1);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3427_ == 0)
{
lean_object* v_unused_3428_; 
v_unused_3428_ = lean_ctor_get(v___x_3389_, 0);
lean_dec(v_unused_3428_);
v___x_3422_ = v___x_3389_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_err_3420_);
lean_dec(v___x_3389_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 0, v_a_3335_);
v___x_3425_ = v___x_3422_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3335_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v_err_3420_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
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
lean_object* v_err_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
lean_dec_ref(v_config_3334_);
v_err_3438_ = lean_ctor_get(v___x_3339_, 1);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3445_ == 0)
{
lean_object* v_unused_3446_; 
v_unused_3446_ = lean_ctor_get(v___x_3339_, 0);
lean_dec(v_unused_3446_);
v___x_3440_ = v___x_3339_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_err_3438_);
lean_dec(v___x_3339_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 0, v_a_3335_);
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3335_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v_err_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
v___jp_3336_:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3337_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1));
v___x_3338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3338_, 0, v_a_3335_);
lean_ctor_set(v___x_3338_, 1, v___x_3337_);
return v___x_3338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(lean_object* v_config_3447_, lean_object* v_a_3448_){
_start:
{
lean_object* v___x_3449_; 
lean_inc_ref(v_a_3448_);
v___x_3449_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3447_, v_a_3448_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_pos_3450_; lean_object* v_res_3451_; lean_object* v___x_3452_; 
v_pos_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_pos_3450_);
v_res_3451_ = lean_ctor_get(v___x_3449_, 1);
lean_inc(v_res_3451_);
lean_dec_ref_known(v___x_3449_, 2);
v___x_3452_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(v_config_3447_, v_res_3451_, v_pos_3450_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_dec_ref(v_a_3448_);
return v___x_3452_;
}
else
{
lean_object* v_err_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
v_err_3453_ = lean_ctor_get(v___x_3452_, 1);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3460_ == 0)
{
lean_object* v_unused_3461_; 
v_unused_3461_ = lean_ctor_get(v___x_3452_, 0);
lean_dec(v_unused_3461_);
v___x_3455_ = v___x_3452_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_err_3453_);
lean_dec(v___x_3452_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 0, v_a_3448_);
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3448_);
lean_ctor_set(v_reuseFailAlloc_3459_, 1, v_err_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
else
{
lean_object* v_err_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3469_; 
lean_dec_ref(v_config_3447_);
v_err_3462_ = lean_ctor_get(v___x_3449_, 1);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3469_ == 0)
{
lean_object* v_unused_3470_; 
v_unused_3470_ = lean_ctor_get(v___x_3449_, 0);
lean_dec(v_unused_3470_);
v___x_3464_ = v___x_3449_;
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_err_3462_);
lean_dec(v___x_3449_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3467_; 
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 0, v_a_3448_);
v___x_3467_ = v___x_3464_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3448_);
lean_ctor_set(v_reuseFailAlloc_3468_, 1, v_err_3462_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(lean_object* v_config_3471_, lean_object* v_a_3472_){
_start:
{
lean_object* v___x_3473_; 
lean_inc_ref(v_a_3472_);
v___x_3473_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3471_, v_a_3472_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_pos_3474_; lean_object* v_res_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3527_; 
v_pos_3474_ = lean_ctor_get(v___x_3473_, 0);
v_res_3475_ = lean_ctor_get(v___x_3473_, 1);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3477_ = v___x_3473_;
v_isShared_3478_ = v_isSharedCheck_3527_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_res_3475_);
lean_inc(v_pos_3474_);
lean_dec(v___x_3473_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3527_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v_array_3479_; lean_object* v_idx_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3526_; 
v_array_3479_ = lean_ctor_get(v_pos_3474_, 0);
v_idx_3480_ = lean_ctor_get(v_pos_3474_, 1);
v_isSharedCheck_3526_ = !lean_is_exclusive(v_pos_3474_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3482_ = v_pos_3474_;
v_isShared_3483_ = v_isSharedCheck_3526_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_idx_3480_);
lean_inc(v_array_3479_);
lean_dec(v_pos_3474_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3526_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3484_; uint8_t v___x_3485_; 
v___x_3484_ = lean_byte_array_size(v_array_3479_);
v___x_3485_ = lean_nat_dec_lt(v_idx_3480_, v___x_3484_);
if (v___x_3485_ == 0)
{
lean_object* v___x_3486_; lean_object* v___x_3488_; 
lean_del_object(v___x_3482_);
lean_dec(v_idx_3480_);
lean_dec_ref(v_array_3479_);
lean_dec(v_res_3475_);
v___x_3486_ = lean_box(0);
if (v_isShared_3478_ == 0)
{
lean_ctor_set_tag(v___x_3477_, 1);
lean_ctor_set(v___x_3477_, 1, v___x_3486_);
lean_ctor_set(v___x_3477_, 0, v_a_3472_);
v___x_3488_ = v___x_3477_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3472_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v___x_3486_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
else
{
uint8_t v___x_3490_; uint8_t v_got_3491_; uint8_t v___x_3492_; 
v___x_3490_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v_got_3491_ = lean_byte_array_fget(v_array_3479_, v_idx_3480_);
v___x_3492_ = lean_uint8_dec_eq(v_got_3491_, v___x_3490_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3493_; lean_object* v___x_3495_; 
lean_del_object(v___x_3482_);
lean_dec(v_idx_3480_);
lean_dec_ref(v_array_3479_);
lean_dec(v_res_3475_);
v___x_3493_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
if (v_isShared_3478_ == 0)
{
lean_ctor_set_tag(v___x_3477_, 1);
lean_ctor_set(v___x_3477_, 1, v___x_3493_);
lean_ctor_set(v___x_3477_, 0, v_a_3472_);
v___x_3495_ = v___x_3477_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3472_);
lean_ctor_set(v_reuseFailAlloc_3496_, 1, v___x_3493_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
else
{
lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3500_; 
lean_del_object(v___x_3477_);
v___x_3497_ = lean_unsigned_to_nat(1u);
v___x_3498_ = lean_nat_add(v_idx_3480_, v___x_3497_);
lean_dec(v_idx_3480_);
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 1, v___x_3498_);
v___x_3500_ = v___x_3482_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_array_3479_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v___x_3498_);
v___x_3500_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
lean_object* v___x_3501_; 
v___x_3501_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_3500_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_pos_3502_; lean_object* v_res_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3515_; 
lean_dec_ref(v_a_3472_);
v_pos_3502_ = lean_ctor_get(v___x_3501_, 0);
v_res_3503_ = lean_ctor_get(v___x_3501_, 1);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3505_ = v___x_3501_;
v_isShared_3506_ = v_isSharedCheck_3515_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_res_3503_);
lean_inc(v_pos_3502_);
lean_dec(v___x_3501_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3515_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; uint16_t v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3513_; 
v___x_3507_ = lean_box(0);
v___x_3508_ = lean_alloc_ctor(2, 0, 2);
v___x_3509_ = lean_unbox(v_res_3503_);
lean_dec(v_res_3503_);
lean_ctor_set_uint16(v___x_3508_, 0, v___x_3509_);
v___x_3510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3507_);
lean_ctor_set(v___x_3510_, 1, v_res_3475_);
lean_ctor_set(v___x_3510_, 2, v___x_3508_);
v___x_3511_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3510_);
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 1, v___x_3511_);
v___x_3513_ = v___x_3505_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_pos_3502_);
lean_ctor_set(v_reuseFailAlloc_3514_, 1, v___x_3511_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
else
{
lean_object* v_err_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3523_; 
lean_dec(v_res_3475_);
v_err_3516_ = lean_ctor_get(v___x_3501_, 1);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3523_ == 0)
{
lean_object* v_unused_3524_; 
v_unused_3524_ = lean_ctor_get(v___x_3501_, 0);
lean_dec(v_unused_3524_);
v___x_3518_ = v___x_3501_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_err_3516_);
lean_dec(v___x_3501_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v_a_3472_);
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3472_);
lean_ctor_set(v_reuseFailAlloc_3522_, 1, v_err_3516_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
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
lean_object* v_err_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
v_err_3528_ = lean_ctor_get(v___x_3473_, 1);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3535_ == 0)
{
lean_object* v_unused_3536_; 
v_unused_3536_ = lean_ctor_get(v___x_3473_, 0);
lean_dec(v_unused_3536_);
v___x_3530_ = v___x_3473_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_err_3528_);
lean_dec(v___x_3473_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 0, v_a_3472_);
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3472_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v_err_3528_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority___boxed(lean_object* v_config_3537_, lean_object* v_a_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3537_, v_a_3538_);
lean_dec_ref(v_config_3537_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object* v_config_3540_, lean_object* v_a_3541_){
_start:
{
lean_object* v___x_3542_; 
lean_inc_ref(v_a_3541_);
v___x_3542_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(v_a_3541_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_dec_ref(v_a_3541_);
lean_dec_ref(v_config_3540_);
return v___x_3542_;
}
else
{
lean_object* v_pos_3543_; lean_object* v_idx_3544_; lean_object* v_idx_3545_; uint8_t v___x_3546_; 
v_pos_3543_ = lean_ctor_get(v___x_3542_, 0);
lean_inc(v_pos_3543_);
v_idx_3544_ = lean_ctor_get(v_a_3541_, 1);
lean_inc(v_idx_3544_);
lean_dec_ref(v_a_3541_);
v_idx_3545_ = lean_ctor_get(v_pos_3543_, 1);
lean_inc(v_idx_3545_);
v___x_3546_ = lean_nat_dec_eq(v_idx_3544_, v_idx_3545_);
lean_dec(v_idx_3544_);
if (v___x_3546_ == 0)
{
lean_dec(v_idx_3545_);
lean_dec(v_pos_3543_);
lean_dec_ref(v_config_3540_);
return v___x_3542_;
}
else
{
lean_object* v___x_3547_; 
lean_dec_ref_known(v___x_3542_, 2);
lean_inc_ref(v_config_3540_);
v___x_3547_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(v_config_3540_, v_pos_3543_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_dec(v_idx_3545_);
lean_dec_ref(v_config_3540_);
return v___x_3547_;
}
else
{
lean_object* v_pos_3548_; lean_object* v_idx_3549_; uint8_t v___x_3550_; 
v_pos_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_pos_3548_);
v_idx_3549_ = lean_ctor_get(v_pos_3548_, 1);
lean_inc(v_idx_3549_);
v___x_3550_ = lean_nat_dec_eq(v_idx_3545_, v_idx_3549_);
lean_dec(v_idx_3545_);
if (v___x_3550_ == 0)
{
lean_dec(v_idx_3549_);
lean_dec(v_pos_3548_);
lean_dec_ref(v_config_3540_);
return v___x_3547_;
}
else
{
lean_object* v___x_3551_; 
lean_dec_ref_known(v___x_3547_, 2);
lean_inc_ref(v_config_3540_);
v___x_3551_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(v_config_3540_, v_pos_3548_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_dec(v_idx_3549_);
lean_dec_ref(v_config_3540_);
return v___x_3551_;
}
else
{
lean_object* v_pos_3552_; lean_object* v_idx_3553_; uint8_t v___x_3554_; 
v_pos_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_pos_3552_);
v_idx_3553_ = lean_ctor_get(v_pos_3552_, 1);
lean_inc(v_idx_3553_);
v___x_3554_ = lean_nat_dec_eq(v_idx_3549_, v_idx_3553_);
lean_dec(v_idx_3549_);
if (v___x_3554_ == 0)
{
lean_dec(v_idx_3553_);
lean_dec(v_pos_3552_);
lean_dec_ref(v_config_3540_);
return v___x_3551_;
}
else
{
lean_object* v___x_3555_; 
lean_dec_ref_known(v___x_3551_, 2);
v___x_3555_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3540_, v_pos_3552_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_dec(v_idx_3553_);
lean_dec_ref(v_config_3540_);
return v___x_3555_;
}
else
{
lean_object* v_pos_3556_; lean_object* v_idx_3557_; uint8_t v___x_3558_; 
v_pos_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_pos_3556_);
v_idx_3557_ = lean_ctor_get(v_pos_3556_, 1);
v___x_3558_ = lean_nat_dec_eq(v_idx_3553_, v_idx_3557_);
lean_dec(v_idx_3553_);
if (v___x_3558_ == 0)
{
lean_dec(v_pos_3556_);
lean_dec_ref(v_config_3540_);
return v___x_3555_;
}
else
{
lean_object* v___x_3559_; 
lean_dec_ref_known(v___x_3555_, 2);
v___x_3559_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(v_config_3540_, v_pos_3556_);
return v___x_3559_;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(lean_object* v_config_3563_, lean_object* v_a_3564_){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_3563_, v_a_3564_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_object* v_pos_3566_; lean_object* v_res_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3580_; 
v_pos_3566_ = lean_ctor_get(v___x_3565_, 0);
v_res_3567_ = lean_ctor_get(v___x_3565_, 1);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3569_ = v___x_3565_;
v_isShared_3570_ = v_isSharedCheck_3580_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_res_3567_);
lean_inc(v_pos_3566_);
lean_dec(v___x_3565_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3580_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3571_; 
v___x_3571_ = l_Std_Http_URI_EncodedFragment_decode(v_res_3567_);
lean_dec(v_res_3567_);
if (lean_obj_tag(v___x_3571_) == 1)
{
lean_object* v_val_3572_; lean_object* v___x_3574_; 
v_val_3572_ = lean_ctor_get(v___x_3571_, 0);
lean_inc(v_val_3572_);
lean_dec_ref_known(v___x_3571_, 1);
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 1, v_val_3572_);
v___x_3574_ = v___x_3569_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_pos_3566_);
lean_ctor_set(v_reuseFailAlloc_3575_, 1, v_val_3572_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
else
{
lean_object* v___x_3576_; lean_object* v___x_3578_; 
lean_dec(v___x_3571_);
v___x_3576_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___closed__1));
if (v_isShared_3570_ == 0)
{
lean_ctor_set_tag(v___x_3569_, 1);
lean_ctor_set(v___x_3569_, 1, v___x_3576_);
v___x_3578_ = v___x_3569_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_pos_3566_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v___x_3576_);
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
else
{
lean_object* v_pos_3581_; lean_object* v_err_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3589_; 
v_pos_3581_ = lean_ctor_get(v___x_3565_, 0);
v_err_3582_ = lean_ctor_get(v___x_3565_, 1);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3584_ = v___x_3565_;
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_err_3582_);
lean_inc(v_pos_3581_);
lean_dec(v___x_3565_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_pos_3581_);
lean_ctor_set(v_reuseFailAlloc_3588_, 1, v_err_3582_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___boxed(lean_object* v_config_3590_, lean_object* v_a_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3590_, v_a_3591_);
lean_dec_ref(v_config_3590_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_uri(lean_object* v_config_3593_, lean_object* v_a_3594_){
_start:
{
lean_object* v___x_3595_; 
lean_inc_ref(v_a_3594_);
v___x_3595_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3593_, v_a_3594_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v_pos_3596_; lean_object* v_res_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3726_; 
v_pos_3596_ = lean_ctor_get(v___x_3595_, 0);
v_res_3597_ = lean_ctor_get(v___x_3595_, 1);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3599_ = v___x_3595_;
v_isShared_3600_ = v_isSharedCheck_3726_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_res_3597_);
lean_inc(v_pos_3596_);
lean_dec(v___x_3595_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3726_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v_array_3601_; lean_object* v_idx_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3725_; 
v_array_3601_ = lean_ctor_get(v_pos_3596_, 0);
v_idx_3602_ = lean_ctor_get(v_pos_3596_, 1);
v_isSharedCheck_3725_ = !lean_is_exclusive(v_pos_3596_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3604_ = v_pos_3596_;
v_isShared_3605_ = v_isSharedCheck_3725_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_idx_3602_);
lean_inc(v_array_3601_);
lean_dec(v_pos_3596_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3725_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3606_; uint8_t v___x_3607_; 
v___x_3606_ = lean_byte_array_size(v_array_3601_);
v___x_3607_ = lean_nat_dec_lt(v_idx_3602_, v___x_3606_);
if (v___x_3607_ == 0)
{
lean_object* v___x_3608_; lean_object* v___x_3610_; 
lean_del_object(v___x_3604_);
lean_dec(v_idx_3602_);
lean_dec_ref(v_array_3601_);
lean_dec(v_res_3597_);
lean_dec_ref(v_config_3593_);
v___x_3608_ = lean_box(0);
if (v_isShared_3600_ == 0)
{
lean_ctor_set_tag(v___x_3599_, 1);
lean_ctor_set(v___x_3599_, 1, v___x_3608_);
lean_ctor_set(v___x_3599_, 0, v_a_3594_);
v___x_3610_ = v___x_3599_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_a_3594_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v___x_3608_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
else
{
uint8_t v___x_3612_; uint8_t v_got_3613_; uint8_t v___x_3614_; 
v___x_3612_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v_got_3613_ = lean_byte_array_fget(v_array_3601_, v_idx_3602_);
v___x_3614_ = lean_uint8_dec_eq(v_got_3613_, v___x_3612_);
if (v___x_3614_ == 0)
{
lean_object* v___x_3615_; lean_object* v___x_3617_; 
lean_del_object(v___x_3604_);
lean_dec(v_idx_3602_);
lean_dec_ref(v_array_3601_);
lean_dec(v_res_3597_);
lean_dec_ref(v_config_3593_);
v___x_3615_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
if (v_isShared_3600_ == 0)
{
lean_ctor_set_tag(v___x_3599_, 1);
lean_ctor_set(v___x_3599_, 1, v___x_3615_);
lean_ctor_set(v___x_3599_, 0, v_a_3594_);
v___x_3617_ = v___x_3599_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3594_);
lean_ctor_set(v_reuseFailAlloc_3618_, 1, v___x_3615_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
else
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3622_; 
v___x_3619_ = lean_unsigned_to_nat(1u);
v___x_3620_ = lean_nat_add(v_idx_3602_, v___x_3619_);
lean_dec(v_idx_3602_);
if (v_isShared_3605_ == 0)
{
lean_ctor_set(v___x_3604_, 1, v___x_3620_);
v___x_3622_ = v___x_3604_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_array_3601_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v___x_3620_);
v___x_3622_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
lean_object* v___x_3623_; 
lean_inc_ref(v_config_3593_);
v___x_3623_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3593_, v___x_3622_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_res_3624_; lean_object* v_pos_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3714_; 
v_res_3624_ = lean_ctor_get(v___x_3623_, 1);
v_pos_3625_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3627_ = v___x_3623_;
v_isShared_3628_ = v_isSharedCheck_3714_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_res_3624_);
lean_inc(v_pos_3625_);
lean_dec(v___x_3623_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3714_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v_fst_3629_; lean_object* v_snd_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3713_; 
v_fst_3629_ = lean_ctor_get(v_res_3624_, 0);
v_snd_3630_ = lean_ctor_get(v_res_3624_, 1);
v_isSharedCheck_3713_ = !lean_is_exclusive(v_res_3624_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3632_ = v_res_3624_;
v_isShared_3633_ = v_isSharedCheck_3713_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_snd_3630_);
lean_inc(v_fst_3629_);
lean_dec(v_res_3624_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3713_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___y_3635_; lean_object* v_pos_3636_; lean_object* v_res_3637_; lean_object* v_idx_3644_; lean_object* v___y_3645_; lean_object* v_pos_3646_; lean_object* v_err_3647_; lean_object* v_pos_3655_; lean_object* v_array_3656_; lean_object* v_idx_3657_; lean_object* v_res_3658_; lean_object* v_array_3676_; lean_object* v_idx_3677_; lean_object* v_pos_3679_; lean_object* v_array_3680_; lean_object* v_idx_3681_; lean_object* v_err_3682_; lean_object* v___x_3686_; uint8_t v___x_3687_; 
v_array_3676_ = lean_ctor_get(v_pos_3625_, 0);
lean_inc_ref(v_array_3676_);
v_idx_3677_ = lean_ctor_get(v_pos_3625_, 1);
lean_inc(v_idx_3677_);
v___x_3686_ = lean_byte_array_size(v_array_3676_);
v___x_3687_ = lean_nat_dec_lt(v_idx_3677_, v___x_3686_);
if (v___x_3687_ == 0)
{
lean_object* v___x_3688_; 
v___x_3688_ = lean_box(0);
lean_inc(v_idx_3677_);
v_pos_3679_ = v_pos_3625_;
v_array_3680_ = v_array_3676_;
v_idx_3681_ = v_idx_3677_;
v_err_3682_ = v___x_3688_;
goto v___jp_3678_;
}
else
{
uint8_t v___x_3689_; uint8_t v_got_3690_; uint8_t v___x_3691_; 
v___x_3689_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3690_ = lean_byte_array_fget(v_array_3676_, v_idx_3677_);
v___x_3691_ = lean_uint8_dec_eq(v_got_3690_, v___x_3689_);
if (v___x_3691_ == 0)
{
lean_object* v___x_3692_; 
v___x_3692_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3677_);
v_pos_3679_ = v_pos_3625_;
v_array_3680_ = v_array_3676_;
v_idx_3681_ = v_idx_3677_;
v_err_3682_ = v___x_3692_;
goto v___jp_3678_;
}
else
{
lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3710_; 
v_isSharedCheck_3710_ = !lean_is_exclusive(v_pos_3625_);
if (v_isSharedCheck_3710_ == 0)
{
lean_object* v_unused_3711_; lean_object* v_unused_3712_; 
v_unused_3711_ = lean_ctor_get(v_pos_3625_, 1);
lean_dec(v_unused_3711_);
v_unused_3712_ = lean_ctor_get(v_pos_3625_, 0);
lean_dec(v_unused_3712_);
v___x_3694_ = v_pos_3625_;
v_isShared_3695_ = v_isSharedCheck_3710_;
goto v_resetjp_3693_;
}
else
{
lean_dec(v_pos_3625_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3710_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3696_; lean_object* v___x_3698_; 
v___x_3696_ = lean_nat_add(v_idx_3677_, v___x_3619_);
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 1, v___x_3696_);
v___x_3698_ = v___x_3694_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_array_3676_);
lean_ctor_set(v_reuseFailAlloc_3709_, 1, v___x_3696_);
v___x_3698_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
lean_object* v___x_3699_; 
lean_inc_ref(v_config_3593_);
v___x_3699_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3593_, v___x_3698_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_object* v_pos_3700_; lean_object* v_res_3701_; lean_object* v_array_3702_; lean_object* v_idx_3703_; lean_object* v___x_3704_; 
lean_dec(v_idx_3677_);
v_pos_3700_ = lean_ctor_get(v___x_3699_, 0);
lean_inc(v_pos_3700_);
v_res_3701_ = lean_ctor_get(v___x_3699_, 1);
lean_inc(v_res_3701_);
lean_dec_ref_known(v___x_3699_, 2);
v_array_3702_ = lean_ctor_get(v_pos_3700_, 0);
lean_inc_ref(v_array_3702_);
v_idx_3703_ = lean_ctor_get(v_pos_3700_, 1);
lean_inc(v_idx_3703_);
v___x_3704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3704_, 0, v_res_3701_);
v_pos_3655_ = v_pos_3700_;
v_array_3656_ = v_array_3702_;
v_idx_3657_ = v_idx_3703_;
v_res_3658_ = v___x_3704_;
goto v___jp_3654_;
}
else
{
lean_object* v_pos_3705_; lean_object* v_err_3706_; lean_object* v_array_3707_; lean_object* v_idx_3708_; 
v_pos_3705_ = lean_ctor_get(v___x_3699_, 0);
lean_inc(v_pos_3705_);
v_err_3706_ = lean_ctor_get(v___x_3699_, 1);
lean_inc(v_err_3706_);
lean_dec_ref_known(v___x_3699_, 2);
v_array_3707_ = lean_ctor_get(v_pos_3705_, 0);
lean_inc_ref(v_array_3707_);
v_idx_3708_ = lean_ctor_get(v_pos_3705_, 1);
lean_inc(v_idx_3708_);
v_pos_3679_ = v_pos_3705_;
v_array_3680_ = v_array_3707_;
v_idx_3681_ = v_idx_3708_;
v_err_3682_ = v_err_3706_;
goto v___jp_3678_;
}
}
}
}
}
v___jp_3634_:
{
lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3641_; 
v___x_3638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3638_, 0, v_res_3597_);
lean_ctor_set(v___x_3638_, 1, v_fst_3629_);
lean_ctor_set(v___x_3638_, 2, v_snd_3630_);
lean_ctor_set(v___x_3638_, 3, v___y_3635_);
lean_ctor_set(v___x_3638_, 4, v_res_3637_);
v___x_3639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3639_, 0, v___x_3638_);
if (v_isShared_3628_ == 0)
{
lean_ctor_set(v___x_3627_, 1, v___x_3639_);
lean_ctor_set(v___x_3627_, 0, v_pos_3636_);
v___x_3641_ = v___x_3627_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_pos_3636_);
lean_ctor_set(v_reuseFailAlloc_3642_, 1, v___x_3639_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
v___jp_3643_:
{
lean_object* v_idx_3648_; uint8_t v___x_3649_; 
v_idx_3648_ = lean_ctor_get(v_pos_3646_, 1);
v___x_3649_ = lean_nat_dec_eq(v_idx_3644_, v_idx_3648_);
lean_dec(v_idx_3644_);
if (v___x_3649_ == 0)
{
lean_object* v___x_3651_; 
lean_dec_ref(v_pos_3646_);
lean_dec(v___y_3645_);
lean_dec(v_snd_3630_);
lean_dec(v_fst_3629_);
lean_del_object(v___x_3627_);
lean_dec(v_res_3597_);
if (v_isShared_3600_ == 0)
{
lean_ctor_set_tag(v___x_3599_, 1);
lean_ctor_set(v___x_3599_, 1, v_err_3647_);
lean_ctor_set(v___x_3599_, 0, v_a_3594_);
v___x_3651_ = v___x_3599_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3594_);
lean_ctor_set(v_reuseFailAlloc_3652_, 1, v_err_3647_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
else
{
lean_object* v___x_3653_; 
lean_dec(v_err_3647_);
lean_del_object(v___x_3599_);
lean_dec_ref(v_a_3594_);
v___x_3653_ = lean_box(0);
v___y_3635_ = v___y_3645_;
v_pos_3636_ = v_pos_3646_;
v_res_3637_ = v___x_3653_;
goto v___jp_3634_;
}
}
v___jp_3654_:
{
lean_object* v___x_3659_; uint8_t v___x_3660_; 
v___x_3659_ = lean_byte_array_size(v_array_3656_);
v___x_3660_ = lean_nat_dec_lt(v_idx_3657_, v___x_3659_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; 
lean_dec_ref(v_array_3656_);
lean_del_object(v___x_3632_);
lean_dec_ref(v_config_3593_);
v___x_3661_ = lean_box(0);
v_idx_3644_ = v_idx_3657_;
v___y_3645_ = v_res_3658_;
v_pos_3646_ = v_pos_3655_;
v_err_3647_ = v___x_3661_;
goto v___jp_3643_;
}
else
{
uint8_t v___x_3662_; uint8_t v_got_3663_; uint8_t v___x_3664_; 
v___x_3662_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v_got_3663_ = lean_byte_array_fget(v_array_3656_, v_idx_3657_);
v___x_3664_ = lean_uint8_dec_eq(v_got_3663_, v___x_3662_);
if (v___x_3664_ == 0)
{
lean_object* v___x_3665_; 
lean_dec_ref(v_array_3656_);
lean_del_object(v___x_3632_);
lean_dec_ref(v_config_3593_);
v___x_3665_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__4, &l_Std_Http_URI_Parser_parseURI___closed__4_once, _init_l_Std_Http_URI_Parser_parseURI___closed__4);
v_idx_3644_ = v_idx_3657_;
v___y_3645_ = v_res_3658_;
v_pos_3646_ = v_pos_3655_;
v_err_3647_ = v___x_3665_;
goto v___jp_3643_;
}
else
{
lean_object* v___x_3666_; lean_object* v___x_3668_; 
lean_dec_ref(v_pos_3655_);
v___x_3666_ = lean_nat_add(v_idx_3657_, v___x_3619_);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 1, v___x_3666_);
lean_ctor_set(v___x_3632_, 0, v_array_3656_);
v___x_3668_ = v___x_3632_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_array_3656_);
lean_ctor_set(v_reuseFailAlloc_3675_, 1, v___x_3666_);
v___x_3668_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
lean_object* v___x_3669_; 
v___x_3669_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3593_, v___x_3668_);
lean_dec_ref(v_config_3593_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_pos_3670_; lean_object* v_res_3671_; lean_object* v___x_3672_; 
lean_dec(v_idx_3657_);
lean_del_object(v___x_3599_);
lean_dec_ref(v_a_3594_);
v_pos_3670_ = lean_ctor_get(v___x_3669_, 0);
lean_inc(v_pos_3670_);
v_res_3671_ = lean_ctor_get(v___x_3669_, 1);
lean_inc(v_res_3671_);
lean_dec_ref_known(v___x_3669_, 2);
v___x_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3672_, 0, v_res_3671_);
v___y_3635_ = v_res_3658_;
v_pos_3636_ = v_pos_3670_;
v_res_3637_ = v___x_3672_;
goto v___jp_3634_;
}
else
{
lean_object* v_pos_3673_; lean_object* v_err_3674_; 
v_pos_3673_ = lean_ctor_get(v___x_3669_, 0);
lean_inc(v_pos_3673_);
v_err_3674_ = lean_ctor_get(v___x_3669_, 1);
lean_inc(v_err_3674_);
lean_dec_ref_known(v___x_3669_, 2);
v_idx_3644_ = v_idx_3657_;
v___y_3645_ = v_res_3658_;
v_pos_3646_ = v_pos_3673_;
v_err_3647_ = v_err_3674_;
goto v___jp_3643_;
}
}
}
}
}
v___jp_3678_:
{
uint8_t v___x_3683_; 
v___x_3683_ = lean_nat_dec_eq(v_idx_3677_, v_idx_3681_);
lean_dec(v_idx_3677_);
if (v___x_3683_ == 0)
{
lean_object* v___x_3684_; 
lean_dec(v_idx_3681_);
lean_dec_ref(v_array_3680_);
lean_dec_ref(v_pos_3679_);
lean_del_object(v___x_3632_);
lean_dec(v_snd_3630_);
lean_dec(v_fst_3629_);
lean_del_object(v___x_3627_);
lean_del_object(v___x_3599_);
lean_dec(v_res_3597_);
lean_dec_ref(v_config_3593_);
v___x_3684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3684_, 0, v_a_3594_);
lean_ctor_set(v___x_3684_, 1, v_err_3682_);
return v___x_3684_;
}
else
{
lean_object* v___x_3685_; 
lean_dec(v_err_3682_);
v___x_3685_ = lean_box(0);
v_pos_3655_ = v_pos_3679_;
v_array_3656_ = v_array_3680_;
v_idx_3657_ = v_idx_3681_;
v_res_3658_ = v___x_3685_;
goto v___jp_3654_;
}
}
}
}
}
else
{
lean_object* v_err_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
lean_del_object(v___x_3599_);
lean_dec(v_res_3597_);
lean_dec_ref(v_config_3593_);
v_err_3715_ = lean_ctor_get(v___x_3623_, 1);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3722_ == 0)
{
lean_object* v_unused_3723_; 
v_unused_3723_ = lean_ctor_get(v___x_3623_, 0);
lean_dec(v_unused_3723_);
v___x_3717_ = v___x_3623_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_err_3715_);
lean_dec(v___x_3623_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 0, v_a_3594_);
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_a_3594_);
lean_ctor_set(v_reuseFailAlloc_3721_, 1, v_err_3715_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
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
lean_object* v_err_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
lean_dec_ref(v_config_3593_);
v_err_3727_ = lean_ctor_get(v___x_3595_, 1);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3734_ == 0)
{
lean_object* v_unused_3735_; 
v_unused_3735_ = lean_ctor_get(v___x_3595_, 0);
lean_dec(v_unused_3735_);
v___x_3729_ = v___x_3595_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_err_3727_);
lean_dec(v___x_3595_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 0, v_a_3594_);
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3594_);
lean_ctor_set(v_reuseFailAlloc_3733_, 1, v_err_3727_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withAuthority(lean_object* v_config_3736_, lean_object* v_a_3737_){
_start:
{
lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v_pos_3742_; lean_object* v_res_3743_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v_idx_3750_; lean_object* v___y_3751_; lean_object* v_pos_3752_; lean_object* v_err_3753_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v_pos_3769_; lean_object* v_array_3770_; lean_object* v_idx_3771_; lean_object* v_res_3772_; lean_object* v_idx_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v_pos_3793_; lean_object* v_array_3794_; lean_object* v_idx_3795_; lean_object* v_err_3796_; lean_object* v_pos_3801_; lean_object* v_utf8_3857_; lean_object* v___x_3858_; 
v_utf8_3857_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_3737_);
v___x_3858_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_3857_, v_a_3737_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v_pos_3859_; 
v_pos_3859_ = lean_ctor_get(v___x_3858_, 0);
lean_inc(v_pos_3859_);
lean_dec_ref_known(v___x_3858_, 2);
v_pos_3801_ = v_pos_3859_;
goto v___jp_3800_;
}
else
{
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v_pos_3860_; 
v_pos_3860_ = lean_ctor_get(v___x_3858_, 0);
lean_inc(v_pos_3860_);
lean_dec_ref_known(v___x_3858_, 2);
v_pos_3801_ = v_pos_3860_;
goto v___jp_3800_;
}
else
{
lean_object* v_err_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3868_; 
lean_dec_ref(v_config_3736_);
v_err_3861_ = lean_ctor_get(v___x_3858_, 1);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3868_ == 0)
{
lean_object* v_unused_3869_; 
v_unused_3869_ = lean_ctor_get(v___x_3858_, 0);
lean_dec(v_unused_3869_);
v___x_3863_ = v___x_3858_;
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_err_3861_);
lean_dec(v___x_3858_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v_a_3737_);
v___x_3866_ = v___x_3863_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3737_);
lean_ctor_set(v_reuseFailAlloc_3867_, 1, v_err_3861_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
}
v___jp_3738_:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
v___x_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3744_, 0, v___y_3739_);
v___x_3745_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3744_);
lean_ctor_set(v___x_3745_, 1, v___y_3740_);
lean_ctor_set(v___x_3745_, 2, v___y_3741_);
lean_ctor_set(v___x_3745_, 3, v_res_3743_);
v___x_3746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3746_, 0, v_pos_3742_);
lean_ctor_set(v___x_3746_, 1, v___x_3745_);
return v___x_3746_;
}
v___jp_3747_:
{
lean_object* v_idx_3754_; uint8_t v___x_3755_; 
v_idx_3754_ = lean_ctor_get(v_pos_3752_, 1);
v___x_3755_ = lean_nat_dec_eq(v_idx_3750_, v_idx_3754_);
lean_dec(v_idx_3750_);
if (v___x_3755_ == 0)
{
lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3749_);
lean_dec_ref(v___y_3748_);
v_isSharedCheck_3762_ = !lean_is_exclusive(v_pos_3752_);
if (v_isSharedCheck_3762_ == 0)
{
lean_object* v_unused_3763_; lean_object* v_unused_3764_; 
v_unused_3763_ = lean_ctor_get(v_pos_3752_, 1);
lean_dec(v_unused_3763_);
v_unused_3764_ = lean_ctor_get(v_pos_3752_, 0);
lean_dec(v_unused_3764_);
v___x_3757_ = v_pos_3752_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_dec(v_pos_3752_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
lean_ctor_set_tag(v___x_3757_, 1);
lean_ctor_set(v___x_3757_, 1, v_err_3753_);
lean_ctor_set(v___x_3757_, 0, v_a_3737_);
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3737_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v_err_3753_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
else
{
lean_object* v___x_3765_; 
lean_dec(v_err_3753_);
lean_dec_ref(v_a_3737_);
v___x_3765_ = lean_box(0);
v___y_3739_ = v___y_3748_;
v___y_3740_ = v___y_3749_;
v___y_3741_ = v___y_3751_;
v_pos_3742_ = v_pos_3752_;
v_res_3743_ = v___x_3765_;
goto v___jp_3738_;
}
}
v___jp_3766_:
{
lean_object* v___x_3773_; uint8_t v___x_3774_; 
v___x_3773_ = lean_byte_array_size(v_array_3770_);
v___x_3774_ = lean_nat_dec_lt(v_idx_3771_, v___x_3773_);
if (v___x_3774_ == 0)
{
lean_object* v___x_3775_; 
lean_dec_ref(v_array_3770_);
lean_dec_ref(v_config_3736_);
v___x_3775_ = lean_box(0);
v___y_3748_ = v___y_3767_;
v___y_3749_ = v___y_3768_;
v_idx_3750_ = v_idx_3771_;
v___y_3751_ = v_res_3772_;
v_pos_3752_ = v_pos_3769_;
v_err_3753_ = v___x_3775_;
goto v___jp_3747_;
}
else
{
uint8_t v___x_3776_; uint8_t v_got_3777_; uint8_t v___x_3778_; 
v___x_3776_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v_got_3777_ = lean_byte_array_fget(v_array_3770_, v_idx_3771_);
v___x_3778_ = lean_uint8_dec_eq(v_got_3777_, v___x_3776_);
if (v___x_3778_ == 0)
{
lean_object* v___x_3779_; 
lean_dec_ref(v_array_3770_);
lean_dec_ref(v_config_3736_);
v___x_3779_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__4, &l_Std_Http_URI_Parser_parseURI___closed__4_once, _init_l_Std_Http_URI_Parser_parseURI___closed__4);
v___y_3748_ = v___y_3767_;
v___y_3749_ = v___y_3768_;
v_idx_3750_ = v_idx_3771_;
v___y_3751_ = v_res_3772_;
v_pos_3752_ = v_pos_3769_;
v_err_3753_ = v___x_3779_;
goto v___jp_3747_;
}
else
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
lean_dec_ref(v_pos_3769_);
v___x_3780_ = lean_unsigned_to_nat(1u);
v___x_3781_ = lean_nat_add(v_idx_3771_, v___x_3780_);
v___x_3782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3782_, 0, v_array_3770_);
lean_ctor_set(v___x_3782_, 1, v___x_3781_);
v___x_3783_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3736_, v___x_3782_);
lean_dec_ref(v_config_3736_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v_pos_3784_; lean_object* v_res_3785_; lean_object* v___x_3786_; 
lean_dec(v_idx_3771_);
lean_dec_ref(v_a_3737_);
v_pos_3784_ = lean_ctor_get(v___x_3783_, 0);
lean_inc(v_pos_3784_);
v_res_3785_ = lean_ctor_get(v___x_3783_, 1);
lean_inc(v_res_3785_);
lean_dec_ref_known(v___x_3783_, 2);
v___x_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3786_, 0, v_res_3785_);
v___y_3739_ = v___y_3767_;
v___y_3740_ = v___y_3768_;
v___y_3741_ = v_res_3772_;
v_pos_3742_ = v_pos_3784_;
v_res_3743_ = v___x_3786_;
goto v___jp_3738_;
}
else
{
lean_object* v_pos_3787_; lean_object* v_err_3788_; 
v_pos_3787_ = lean_ctor_get(v___x_3783_, 0);
lean_inc(v_pos_3787_);
v_err_3788_ = lean_ctor_get(v___x_3783_, 1);
lean_inc(v_err_3788_);
lean_dec_ref_known(v___x_3783_, 2);
v___y_3748_ = v___y_3767_;
v___y_3749_ = v___y_3768_;
v_idx_3750_ = v_idx_3771_;
v___y_3751_ = v_res_3772_;
v_pos_3752_ = v_pos_3787_;
v_err_3753_ = v_err_3788_;
goto v___jp_3747_;
}
}
}
}
v___jp_3789_:
{
uint8_t v___x_3797_; 
v___x_3797_ = lean_nat_dec_eq(v_idx_3790_, v_idx_3795_);
lean_dec(v_idx_3790_);
if (v___x_3797_ == 0)
{
lean_object* v___x_3798_; 
lean_dec(v_idx_3795_);
lean_dec_ref(v_array_3794_);
lean_dec_ref(v_pos_3793_);
lean_dec_ref(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec_ref(v_config_3736_);
v___x_3798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3798_, 0, v_a_3737_);
lean_ctor_set(v___x_3798_, 1, v_err_3796_);
return v___x_3798_;
}
else
{
lean_object* v___x_3799_; 
lean_dec(v_err_3796_);
v___x_3799_ = lean_box(0);
v___y_3767_ = v___y_3791_;
v___y_3768_ = v___y_3792_;
v_pos_3769_ = v_pos_3793_;
v_array_3770_ = v_array_3794_;
v_idx_3771_ = v_idx_3795_;
v_res_3772_ = v___x_3799_;
goto v___jp_3766_;
}
}
v___jp_3800_:
{
lean_object* v___x_3802_; 
v___x_3802_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_3736_, v_pos_3801_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_pos_3803_; lean_object* v_res_3804_; uint8_t v___x_3805_; lean_object* v___x_3806_; 
v_pos_3803_ = lean_ctor_get(v___x_3802_, 0);
lean_inc(v_pos_3803_);
v_res_3804_ = lean_ctor_get(v___x_3802_, 1);
lean_inc(v_res_3804_);
lean_dec_ref_known(v___x_3802_, 2);
v___x_3805_ = 1;
lean_inc_ref(v_config_3736_);
v___x_3806_ = l_Std_Http_URI_Parser_parsePath(v_config_3736_, v___x_3805_, v___x_3805_, v_pos_3803_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_pos_3807_; lean_object* v_res_3808_; lean_object* v_array_3809_; lean_object* v_idx_3810_; lean_object* v___x_3811_; uint8_t v___x_3812_; 
v_pos_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_pos_3807_);
v_res_3808_ = lean_ctor_get(v___x_3806_, 1);
lean_inc(v_res_3808_);
lean_dec_ref_known(v___x_3806_, 2);
v_array_3809_ = lean_ctor_get(v_pos_3807_, 0);
lean_inc_ref(v_array_3809_);
v_idx_3810_ = lean_ctor_get(v_pos_3807_, 1);
lean_inc(v_idx_3810_);
v___x_3811_ = lean_byte_array_size(v_array_3809_);
v___x_3812_ = lean_nat_dec_lt(v_idx_3810_, v___x_3811_);
if (v___x_3812_ == 0)
{
lean_object* v___x_3813_; 
v___x_3813_ = lean_box(0);
lean_inc(v_idx_3810_);
v_idx_3790_ = v_idx_3810_;
v___y_3791_ = v_res_3804_;
v___y_3792_ = v_res_3808_;
v_pos_3793_ = v_pos_3807_;
v_array_3794_ = v_array_3809_;
v_idx_3795_ = v_idx_3810_;
v_err_3796_ = v___x_3813_;
goto v___jp_3789_;
}
else
{
uint8_t v___x_3814_; uint8_t v_got_3815_; uint8_t v___x_3816_; 
v___x_3814_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3815_ = lean_byte_array_fget(v_array_3809_, v_idx_3810_);
v___x_3816_ = lean_uint8_dec_eq(v_got_3815_, v___x_3814_);
if (v___x_3816_ == 0)
{
lean_object* v___x_3817_; 
v___x_3817_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3810_);
v_idx_3790_ = v_idx_3810_;
v___y_3791_ = v_res_3804_;
v___y_3792_ = v_res_3808_;
v_pos_3793_ = v_pos_3807_;
v_array_3794_ = v_array_3809_;
v_idx_3795_ = v_idx_3810_;
v_err_3796_ = v___x_3817_;
goto v___jp_3789_;
}
else
{
lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3836_; 
v_isSharedCheck_3836_ = !lean_is_exclusive(v_pos_3807_);
if (v_isSharedCheck_3836_ == 0)
{
lean_object* v_unused_3837_; lean_object* v_unused_3838_; 
v_unused_3837_ = lean_ctor_get(v_pos_3807_, 1);
lean_dec(v_unused_3837_);
v_unused_3838_ = lean_ctor_get(v_pos_3807_, 0);
lean_dec(v_unused_3838_);
v___x_3819_ = v_pos_3807_;
v_isShared_3820_ = v_isSharedCheck_3836_;
goto v_resetjp_3818_;
}
else
{
lean_dec(v_pos_3807_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3836_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3824_; 
v___x_3821_ = lean_unsigned_to_nat(1u);
v___x_3822_ = lean_nat_add(v_idx_3810_, v___x_3821_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 1, v___x_3822_);
v___x_3824_ = v___x_3819_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_array_3809_);
lean_ctor_set(v_reuseFailAlloc_3835_, 1, v___x_3822_);
v___x_3824_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
lean_object* v___x_3825_; 
lean_inc_ref(v_config_3736_);
v___x_3825_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3736_, v___x_3824_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v_pos_3826_; lean_object* v_res_3827_; lean_object* v_array_3828_; lean_object* v_idx_3829_; lean_object* v___x_3830_; 
lean_dec(v_idx_3810_);
v_pos_3826_ = lean_ctor_get(v___x_3825_, 0);
lean_inc(v_pos_3826_);
v_res_3827_ = lean_ctor_get(v___x_3825_, 1);
lean_inc(v_res_3827_);
lean_dec_ref_known(v___x_3825_, 2);
v_array_3828_ = lean_ctor_get(v_pos_3826_, 0);
lean_inc_ref(v_array_3828_);
v_idx_3829_ = lean_ctor_get(v_pos_3826_, 1);
lean_inc(v_idx_3829_);
v___x_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3830_, 0, v_res_3827_);
v___y_3767_ = v_res_3804_;
v___y_3768_ = v_res_3808_;
v_pos_3769_ = v_pos_3826_;
v_array_3770_ = v_array_3828_;
v_idx_3771_ = v_idx_3829_;
v_res_3772_ = v___x_3830_;
goto v___jp_3766_;
}
else
{
lean_object* v_pos_3831_; lean_object* v_err_3832_; lean_object* v_array_3833_; lean_object* v_idx_3834_; 
v_pos_3831_ = lean_ctor_get(v___x_3825_, 0);
lean_inc(v_pos_3831_);
v_err_3832_ = lean_ctor_get(v___x_3825_, 1);
lean_inc(v_err_3832_);
lean_dec_ref_known(v___x_3825_, 2);
v_array_3833_ = lean_ctor_get(v_pos_3831_, 0);
lean_inc_ref(v_array_3833_);
v_idx_3834_ = lean_ctor_get(v_pos_3831_, 1);
lean_inc(v_idx_3834_);
v_idx_3790_ = v_idx_3810_;
v___y_3791_ = v_res_3804_;
v___y_3792_ = v_res_3808_;
v_pos_3793_ = v_pos_3831_;
v_array_3794_ = v_array_3833_;
v_idx_3795_ = v_idx_3834_;
v_err_3796_ = v_err_3832_;
goto v___jp_3789_;
}
}
}
}
}
}
else
{
lean_object* v_err_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3846_; 
lean_dec(v_res_3804_);
lean_dec_ref(v_config_3736_);
v_err_3839_ = lean_ctor_get(v___x_3806_, 1);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3846_ == 0)
{
lean_object* v_unused_3847_; 
v_unused_3847_ = lean_ctor_get(v___x_3806_, 0);
lean_dec(v_unused_3847_);
v___x_3841_ = v___x_3806_;
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_err_3839_);
lean_dec(v___x_3806_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3844_; 
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 0, v_a_3737_);
v___x_3844_ = v___x_3841_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_a_3737_);
lean_ctor_set(v_reuseFailAlloc_3845_, 1, v_err_3839_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
}
}
else
{
lean_object* v_err_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3855_; 
lean_dec_ref(v_config_3736_);
v_err_3848_ = lean_ctor_get(v___x_3802_, 1);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3855_ == 0)
{
lean_object* v_unused_3856_; 
v_unused_3856_ = lean_ctor_get(v___x_3802_, 0);
lean_dec(v_unused_3856_);
v___x_3850_ = v___x_3802_;
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_err_3848_);
lean_dec(v___x_3802_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3853_; 
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 0, v_a_3737_);
v___x_3853_ = v___x_3850_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3737_);
lean_ctor_set(v_reuseFailAlloc_3854_, 1, v_err_3848_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath(lean_object* v_config_3870_, lean_object* v_a_3871_){
_start:
{
uint8_t v___x_3872_; uint8_t v___x_3873_; lean_object* v___x_3874_; 
v___x_3872_ = 0;
v___x_3873_ = 1;
lean_inc_ref(v_config_3870_);
v___x_3874_ = l_Std_Http_URI_Parser_parsePath(v_config_3870_, v___x_3872_, v___x_3873_, v_a_3871_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_pos_3875_; lean_object* v_res_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3957_; 
v_pos_3875_ = lean_ctor_get(v___x_3874_, 0);
v_res_3876_ = lean_ctor_get(v___x_3874_, 1);
v_isSharedCheck_3957_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3957_ == 0)
{
v___x_3878_ = v___x_3874_;
v_isShared_3879_ = v_isSharedCheck_3957_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_res_3876_);
lean_inc(v_pos_3875_);
lean_dec(v___x_3874_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3957_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___y_3881_; lean_object* v_pos_3882_; lean_object* v_res_3883_; lean_object* v_idx_3890_; lean_object* v___y_3891_; lean_object* v_pos_3892_; lean_object* v_err_3893_; lean_object* v_pos_3899_; lean_object* v_array_3900_; lean_object* v_idx_3901_; lean_object* v_res_3902_; lean_object* v_array_3919_; lean_object* v_idx_3920_; lean_object* v_pos_3922_; lean_object* v_array_3923_; lean_object* v_idx_3924_; lean_object* v_err_3925_; lean_object* v___x_3929_; uint8_t v___x_3930_; 
v_array_3919_ = lean_ctor_get(v_pos_3875_, 0);
lean_inc_ref(v_array_3919_);
v_idx_3920_ = lean_ctor_get(v_pos_3875_, 1);
lean_inc(v_idx_3920_);
v___x_3929_ = lean_byte_array_size(v_array_3919_);
v___x_3930_ = lean_nat_dec_lt(v_idx_3920_, v___x_3929_);
if (v___x_3930_ == 0)
{
lean_object* v___x_3931_; 
v___x_3931_ = lean_box(0);
lean_inc(v_idx_3920_);
v_pos_3922_ = v_pos_3875_;
v_array_3923_ = v_array_3919_;
v_idx_3924_ = v_idx_3920_;
v_err_3925_ = v___x_3931_;
goto v___jp_3921_;
}
else
{
uint8_t v___x_3932_; uint8_t v_got_3933_; uint8_t v___x_3934_; 
v___x_3932_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3933_ = lean_byte_array_fget(v_array_3919_, v_idx_3920_);
v___x_3934_ = lean_uint8_dec_eq(v_got_3933_, v___x_3932_);
if (v___x_3934_ == 0)
{
lean_object* v___x_3935_; 
v___x_3935_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3920_);
v_pos_3922_ = v_pos_3875_;
v_array_3923_ = v_array_3919_;
v_idx_3924_ = v_idx_3920_;
v_err_3925_ = v___x_3935_;
goto v___jp_3921_;
}
else
{
lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3954_; 
v_isSharedCheck_3954_ = !lean_is_exclusive(v_pos_3875_);
if (v_isSharedCheck_3954_ == 0)
{
lean_object* v_unused_3955_; lean_object* v_unused_3956_; 
v_unused_3955_ = lean_ctor_get(v_pos_3875_, 1);
lean_dec(v_unused_3955_);
v_unused_3956_ = lean_ctor_get(v_pos_3875_, 0);
lean_dec(v_unused_3956_);
v___x_3937_ = v_pos_3875_;
v_isShared_3938_ = v_isSharedCheck_3954_;
goto v_resetjp_3936_;
}
else
{
lean_dec(v_pos_3875_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3954_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3942_; 
v___x_3939_ = lean_unsigned_to_nat(1u);
v___x_3940_ = lean_nat_add(v_idx_3920_, v___x_3939_);
if (v_isShared_3938_ == 0)
{
lean_ctor_set(v___x_3937_, 1, v___x_3940_);
v___x_3942_ = v___x_3937_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_array_3919_);
lean_ctor_set(v_reuseFailAlloc_3953_, 1, v___x_3940_);
v___x_3942_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
lean_object* v___x_3943_; 
lean_inc_ref(v_config_3870_);
v___x_3943_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3870_, v___x_3942_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_pos_3944_; lean_object* v_res_3945_; lean_object* v_array_3946_; lean_object* v_idx_3947_; lean_object* v___x_3948_; 
lean_dec(v_idx_3920_);
v_pos_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_pos_3944_);
v_res_3945_ = lean_ctor_get(v___x_3943_, 1);
lean_inc(v_res_3945_);
lean_dec_ref_known(v___x_3943_, 2);
v_array_3946_ = lean_ctor_get(v_pos_3944_, 0);
lean_inc_ref(v_array_3946_);
v_idx_3947_ = lean_ctor_get(v_pos_3944_, 1);
lean_inc(v_idx_3947_);
v___x_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3948_, 0, v_res_3945_);
v_pos_3899_ = v_pos_3944_;
v_array_3900_ = v_array_3946_;
v_idx_3901_ = v_idx_3947_;
v_res_3902_ = v___x_3948_;
goto v___jp_3898_;
}
else
{
lean_object* v_pos_3949_; lean_object* v_err_3950_; lean_object* v_array_3951_; lean_object* v_idx_3952_; 
v_pos_3949_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_pos_3949_);
v_err_3950_ = lean_ctor_get(v___x_3943_, 1);
lean_inc(v_err_3950_);
lean_dec_ref_known(v___x_3943_, 2);
v_array_3951_ = lean_ctor_get(v_pos_3949_, 0);
lean_inc_ref(v_array_3951_);
v_idx_3952_ = lean_ctor_get(v_pos_3949_, 1);
lean_inc(v_idx_3952_);
v_pos_3922_ = v_pos_3949_;
v_array_3923_ = v_array_3951_;
v_idx_3924_ = v_idx_3952_;
v_err_3925_ = v_err_3950_;
goto v___jp_3921_;
}
}
}
}
}
v___jp_3880_:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3887_; 
v___x_3884_ = lean_box(0);
v___x_3885_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3884_);
lean_ctor_set(v___x_3885_, 1, v_res_3876_);
lean_ctor_set(v___x_3885_, 2, v___y_3881_);
lean_ctor_set(v___x_3885_, 3, v_res_3883_);
if (v_isShared_3879_ == 0)
{
lean_ctor_set(v___x_3878_, 1, v___x_3885_);
lean_ctor_set(v___x_3878_, 0, v_pos_3882_);
v___x_3887_ = v___x_3878_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_pos_3882_);
lean_ctor_set(v_reuseFailAlloc_3888_, 1, v___x_3885_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
v___jp_3889_:
{
lean_object* v_idx_3894_; uint8_t v___x_3895_; 
v_idx_3894_ = lean_ctor_get(v_pos_3892_, 1);
v___x_3895_ = lean_nat_dec_eq(v_idx_3890_, v_idx_3894_);
lean_dec(v_idx_3890_);
if (v___x_3895_ == 0)
{
lean_object* v___x_3896_; 
lean_dec(v___y_3891_);
lean_del_object(v___x_3878_);
lean_dec(v_res_3876_);
v___x_3896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3896_, 0, v_pos_3892_);
lean_ctor_set(v___x_3896_, 1, v_err_3893_);
return v___x_3896_;
}
else
{
lean_object* v___x_3897_; 
lean_dec(v_err_3893_);
v___x_3897_ = lean_box(0);
v___y_3881_ = v___y_3891_;
v_pos_3882_ = v_pos_3892_;
v_res_3883_ = v___x_3897_;
goto v___jp_3880_;
}
}
v___jp_3898_:
{
lean_object* v___x_3903_; uint8_t v___x_3904_; 
v___x_3903_ = lean_byte_array_size(v_array_3900_);
v___x_3904_ = lean_nat_dec_lt(v_idx_3901_, v___x_3903_);
if (v___x_3904_ == 0)
{
lean_object* v___x_3905_; 
lean_dec_ref(v_array_3900_);
lean_dec_ref(v_config_3870_);
v___x_3905_ = lean_box(0);
v_idx_3890_ = v_idx_3901_;
v___y_3891_ = v_res_3902_;
v_pos_3892_ = v_pos_3899_;
v_err_3893_ = v___x_3905_;
goto v___jp_3889_;
}
else
{
uint8_t v___x_3906_; uint8_t v_got_3907_; uint8_t v___x_3908_; 
v___x_3906_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v_got_3907_ = lean_byte_array_fget(v_array_3900_, v_idx_3901_);
v___x_3908_ = lean_uint8_dec_eq(v_got_3907_, v___x_3906_);
if (v___x_3908_ == 0)
{
lean_object* v___x_3909_; 
lean_dec_ref(v_array_3900_);
lean_dec_ref(v_config_3870_);
v___x_3909_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__4, &l_Std_Http_URI_Parser_parseURI___closed__4_once, _init_l_Std_Http_URI_Parser_parseURI___closed__4);
v_idx_3890_ = v_idx_3901_;
v___y_3891_ = v_res_3902_;
v_pos_3892_ = v_pos_3899_;
v_err_3893_ = v___x_3909_;
goto v___jp_3889_;
}
else
{
lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
lean_dec_ref(v_pos_3899_);
v___x_3910_ = lean_unsigned_to_nat(1u);
v___x_3911_ = lean_nat_add(v_idx_3901_, v___x_3910_);
v___x_3912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3912_, 0, v_array_3900_);
lean_ctor_set(v___x_3912_, 1, v___x_3911_);
v___x_3913_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3870_, v___x_3912_);
lean_dec_ref(v_config_3870_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_pos_3914_; lean_object* v_res_3915_; lean_object* v___x_3916_; 
lean_dec(v_idx_3901_);
v_pos_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_pos_3914_);
v_res_3915_ = lean_ctor_get(v___x_3913_, 1);
lean_inc(v_res_3915_);
lean_dec_ref_known(v___x_3913_, 2);
v___x_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3916_, 0, v_res_3915_);
v___y_3881_ = v_res_3902_;
v_pos_3882_ = v_pos_3914_;
v_res_3883_ = v___x_3916_;
goto v___jp_3880_;
}
else
{
lean_object* v_pos_3917_; lean_object* v_err_3918_; 
v_pos_3917_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_pos_3917_);
v_err_3918_ = lean_ctor_get(v___x_3913_, 1);
lean_inc(v_err_3918_);
lean_dec_ref_known(v___x_3913_, 2);
v_idx_3890_ = v_idx_3901_;
v___y_3891_ = v_res_3902_;
v_pos_3892_ = v_pos_3917_;
v_err_3893_ = v_err_3918_;
goto v___jp_3889_;
}
}
}
}
v___jp_3921_:
{
uint8_t v___x_3926_; 
v___x_3926_ = lean_nat_dec_eq(v_idx_3920_, v_idx_3924_);
lean_dec(v_idx_3920_);
if (v___x_3926_ == 0)
{
lean_object* v___x_3927_; 
lean_dec(v_idx_3924_);
lean_dec_ref(v_array_3923_);
lean_del_object(v___x_3878_);
lean_dec(v_res_3876_);
lean_dec_ref(v_config_3870_);
v___x_3927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3927_, 0, v_pos_3922_);
lean_ctor_set(v___x_3927_, 1, v_err_3925_);
return v___x_3927_;
}
else
{
lean_object* v___x_3928_; 
lean_dec(v_err_3925_);
v___x_3928_ = lean_box(0);
v_pos_3899_ = v_pos_3922_;
v_array_3900_ = v_array_3923_;
v_idx_3901_ = v_idx_3924_;
v_res_3902_ = v___x_3928_;
goto v___jp_3898_;
}
}
}
}
else
{
lean_object* v_pos_3958_; lean_object* v_err_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3966_; 
lean_dec_ref(v_config_3870_);
v_pos_3958_ = lean_ctor_get(v___x_3874_, 0);
v_err_3959_ = lean_ctor_get(v___x_3874_, 1);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3961_ = v___x_3874_;
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_err_3959_);
lean_inc(v_pos_3958_);
lean_dec(v___x_3874_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3964_; 
if (v_isShared_3962_ == 0)
{
v___x_3964_ = v___x_3961_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_pos_3958_);
lean_ctor_set(v_reuseFailAlloc_3965_, 1, v_err_3959_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_relative(lean_object* v_config_3967_, lean_object* v_a_3968_){
_start:
{
lean_object* v___y_3970_; lean_object* v___x_3990_; 
lean_inc_ref(v_a_3968_);
lean_inc_ref(v_config_3967_);
v___x_3990_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withAuthority(v_config_3967_, v_a_3968_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_dec_ref(v_a_3968_);
lean_dec_ref(v_config_3967_);
v___y_3970_ = v___x_3990_;
goto v___jp_3969_;
}
else
{
lean_object* v_pos_3991_; lean_object* v_idx_3992_; lean_object* v_idx_3993_; uint8_t v___x_3994_; 
v_pos_3991_ = lean_ctor_get(v___x_3990_, 0);
lean_inc(v_pos_3991_);
v_idx_3992_ = lean_ctor_get(v_a_3968_, 1);
lean_inc(v_idx_3992_);
lean_dec_ref(v_a_3968_);
v_idx_3993_ = lean_ctor_get(v_pos_3991_, 1);
v___x_3994_ = lean_nat_dec_eq(v_idx_3992_, v_idx_3993_);
lean_dec(v_idx_3992_);
if (v___x_3994_ == 0)
{
lean_dec(v_pos_3991_);
lean_dec_ref(v_config_3967_);
v___y_3970_ = v___x_3990_;
goto v___jp_3969_;
}
else
{
lean_object* v___x_3995_; 
lean_dec_ref_known(v___x_3990_, 2);
v___x_3995_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath(v_config_3967_, v_pos_3991_);
v___y_3970_ = v___x_3995_;
goto v___jp_3969_;
}
}
v___jp_3969_:
{
if (lean_obj_tag(v___y_3970_) == 0)
{
lean_object* v_pos_3971_; lean_object* v_res_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3980_; 
v_pos_3971_ = lean_ctor_get(v___y_3970_, 0);
v_res_3972_ = lean_ctor_get(v___y_3970_, 1);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___y_3970_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3974_ = v___y_3970_;
v_isShared_3975_ = v_isSharedCheck_3980_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_res_3972_);
lean_inc(v_pos_3971_);
lean_dec(v___y_3970_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3980_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3976_; lean_object* v___x_3978_; 
v___x_3976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3976_, 0, v_res_3972_);
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 1, v___x_3976_);
v___x_3978_ = v___x_3974_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_pos_3971_);
lean_ctor_set(v_reuseFailAlloc_3979_, 1, v___x_3976_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
else
{
lean_object* v_pos_3981_; lean_object* v_err_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
v_pos_3981_ = lean_ctor_get(v___y_3970_, 0);
v_err_3982_ = lean_ctor_get(v___y_3970_, 1);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___y_3970_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___y_3970_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_err_3982_);
lean_inc(v_pos_3981_);
lean_dec(v___y_3970_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_pos_3981_);
lean_ctor_set(v_reuseFailAlloc_3988_, 1, v_err_3982_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURIReference(lean_object* v_config_3996_, lean_object* v_a_3997_){
_start:
{
lean_object* v___y_3999_; lean_object* v_pos_4000_; lean_object* v___x_4005_; 
lean_inc_ref(v_a_3997_);
lean_inc_ref(v_config_3996_);
v___x_4005_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_uri(v_config_3996_, v_a_3997_);
if (lean_obj_tag(v___x_4005_) == 0)
{
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_dec_ref(v_a_3997_);
lean_dec_ref(v_config_3996_);
return v___x_4005_;
}
else
{
lean_object* v_pos_4006_; 
v_pos_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc(v_pos_4006_);
v___y_3999_ = v___x_4005_;
v_pos_4000_ = v_pos_4006_;
goto v___jp_3998_;
}
}
else
{
lean_object* v_err_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4014_; 
v_err_4007_ = lean_ctor_get(v___x_4005_, 1);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4014_ == 0)
{
lean_object* v_unused_4015_; 
v_unused_4015_ = lean_ctor_get(v___x_4005_, 0);
lean_dec(v_unused_4015_);
v___x_4009_ = v___x_4005_;
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_err_4007_);
lean_dec(v___x_4005_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
lean_inc_ref(v_a_3997_);
if (v_isShared_4010_ == 0)
{
lean_ctor_set(v___x_4009_, 0, v_a_3997_);
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_3997_);
lean_ctor_set(v_reuseFailAlloc_4013_, 1, v_err_4007_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
lean_inc_ref(v_a_3997_);
v___y_3999_ = v___x_4012_;
v_pos_4000_ = v_a_3997_;
goto v___jp_3998_;
}
}
}
v___jp_3998_:
{
lean_object* v_idx_4001_; lean_object* v_idx_4002_; uint8_t v___x_4003_; 
v_idx_4001_ = lean_ctor_get(v_a_3997_, 1);
lean_inc(v_idx_4001_);
lean_dec_ref(v_a_3997_);
v_idx_4002_ = lean_ctor_get(v_pos_4000_, 1);
v___x_4003_ = lean_nat_dec_eq(v_idx_4001_, v_idx_4002_);
lean_dec(v_idx_4001_);
if (v___x_4003_ == 0)
{
lean_dec_ref(v_pos_4000_);
lean_dec_ref(v_config_3996_);
return v___y_3999_;
}
else
{
lean_object* v___x_4004_; 
lean_dec_ref(v___y_3999_);
v___x_4004_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_relative(v_config_3996_, v_pos_4000_);
return v___x_4004_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader(lean_object* v_config_4022_, lean_object* v_a_4023_){
_start:
{
lean_object* v___x_4024_; 
v___x_4024_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_4022_, v_a_4023_);
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_object* v_pos_4025_; lean_object* v_res_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4099_; 
v_pos_4025_ = lean_ctor_get(v___x_4024_, 0);
v_res_4026_ = lean_ctor_get(v___x_4024_, 1);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4028_ = v___x_4024_;
v_isShared_4029_ = v_isSharedCheck_4099_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_res_4026_);
lean_inc(v_pos_4025_);
lean_dec(v___x_4024_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4099_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v_port_4031_; lean_object* v___y_4032_; lean_object* v_pos_4046_; lean_object* v_pos_4049_; lean_object* v_array_4050_; lean_object* v_idx_4051_; lean_object* v_array_4057_; lean_object* v_idx_4058_; lean_object* v___x_4059_; uint8_t v___x_4060_; 
v_array_4057_ = lean_ctor_get(v_pos_4025_, 0);
v_idx_4058_ = lean_ctor_get(v_pos_4025_, 1);
v___x_4059_ = lean_byte_array_size(v_array_4057_);
v___x_4060_ = lean_nat_dec_lt(v_idx_4058_, v___x_4059_);
if (v___x_4060_ == 0)
{
v_pos_4046_ = v_pos_4025_;
goto v___jp_4045_;
}
else
{
uint8_t v___x_4061_; uint8_t v___x_4062_; uint8_t v___x_4063_; 
v___x_4061_ = lean_byte_array_fget(v_array_4057_, v_idx_4058_);
v___x_4062_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_4063_ = lean_uint8_dec_eq(v___x_4061_, v___x_4062_);
if (v___x_4063_ == 0)
{
v_pos_4046_ = v_pos_4025_;
goto v___jp_4045_;
}
else
{
if (v___x_4060_ == 0)
{
lean_object* v___x_4064_; lean_object* v___x_4065_; 
lean_del_object(v___x_4028_);
lean_dec(v_res_4026_);
v___x_4064_ = lean_box(0);
v___x_4065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4065_, 0, v_pos_4025_);
lean_ctor_set(v___x_4065_, 1, v___x_4064_);
return v___x_4065_;
}
else
{
if (v___x_4063_ == 0)
{
lean_object* v___x_4066_; lean_object* v___x_4067_; 
lean_del_object(v___x_4028_);
lean_dec(v_res_4026_);
v___x_4066_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
v___x_4067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4067_, 0, v_pos_4025_);
lean_ctor_set(v___x_4067_, 1, v___x_4066_);
return v___x_4067_;
}
else
{
lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4096_; 
lean_inc(v_idx_4058_);
lean_inc_ref(v_array_4057_);
v_isSharedCheck_4096_ = !lean_is_exclusive(v_pos_4025_);
if (v_isSharedCheck_4096_ == 0)
{
lean_object* v_unused_4097_; lean_object* v_unused_4098_; 
v_unused_4097_ = lean_ctor_get(v_pos_4025_, 1);
lean_dec(v_unused_4097_);
v_unused_4098_ = lean_ctor_get(v_pos_4025_, 0);
lean_dec(v_unused_4098_);
v___x_4069_ = v_pos_4025_;
v_isShared_4070_ = v_isSharedCheck_4096_;
goto v_resetjp_4068_;
}
else
{
lean_dec(v_pos_4025_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4096_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4074_; 
v___x_4071_ = lean_unsigned_to_nat(1u);
v___x_4072_ = lean_nat_add(v_idx_4058_, v___x_4071_);
lean_dec(v_idx_4058_);
lean_inc(v___x_4072_);
lean_inc_ref(v_array_4057_);
if (v_isShared_4070_ == 0)
{
lean_ctor_set(v___x_4069_, 1, v___x_4072_);
v___x_4074_ = v___x_4069_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_array_4057_);
lean_ctor_set(v_reuseFailAlloc_4095_, 1, v___x_4072_);
v___x_4074_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
uint8_t v___x_4075_; 
v___x_4075_ = lean_nat_dec_lt(v___x_4072_, v___x_4059_);
if (v___x_4075_ == 0)
{
v_pos_4049_ = v___x_4074_;
v_array_4050_ = v_array_4057_;
v_idx_4051_ = v___x_4072_;
goto v___jp_4048_;
}
else
{
uint8_t v___x_4076_; uint8_t v___x_4077_; uint8_t v___x_4078_; 
v___x_4076_ = lean_byte_array_fget(v_array_4057_, v___x_4072_);
v___x_4077_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_4078_ = lean_uint8_dec_le(v___x_4077_, v___x_4076_);
if (v___x_4078_ == 0)
{
v_pos_4049_ = v___x_4074_;
v_array_4050_ = v_array_4057_;
v_idx_4051_ = v___x_4072_;
goto v___jp_4048_;
}
else
{
uint8_t v___x_4079_; uint8_t v___x_4080_; 
v___x_4079_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_4080_ = lean_uint8_dec_le(v___x_4076_, v___x_4079_);
if (v___x_4080_ == 0)
{
v_pos_4049_ = v___x_4074_;
v_array_4050_ = v_array_4057_;
v_idx_4051_ = v___x_4072_;
goto v___jp_4048_;
}
else
{
lean_object* v___x_4081_; 
lean_dec(v___x_4072_);
lean_dec_ref(v_array_4057_);
v___x_4081_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_4074_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v_pos_4082_; lean_object* v_res_4083_; lean_object* v___x_4084_; uint16_t v___x_4085_; 
v_pos_4082_ = lean_ctor_get(v___x_4081_, 0);
lean_inc(v_pos_4082_);
v_res_4083_ = lean_ctor_get(v___x_4081_, 1);
lean_inc(v_res_4083_);
lean_dec_ref_known(v___x_4081_, 2);
v___x_4084_ = lean_alloc_ctor(2, 0, 2);
v___x_4085_ = lean_unbox(v_res_4083_);
lean_dec(v_res_4083_);
lean_ctor_set_uint16(v___x_4084_, 0, v___x_4085_);
v_port_4031_ = v___x_4084_;
v___y_4032_ = v_pos_4082_;
goto v___jp_4030_;
}
else
{
lean_object* v_pos_4086_; lean_object* v_err_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4094_; 
lean_del_object(v___x_4028_);
lean_dec(v_res_4026_);
v_pos_4086_ = lean_ctor_get(v___x_4081_, 0);
v_err_4087_ = lean_ctor_get(v___x_4081_, 1);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4089_ = v___x_4081_;
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_err_4087_);
lean_inc(v_pos_4086_);
lean_dec(v___x_4081_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4092_; 
if (v_isShared_4090_ == 0)
{
v___x_4092_ = v___x_4089_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_pos_4086_);
lean_ctor_set(v_reuseFailAlloc_4093_, 1, v_err_4087_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
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
v___jp_4030_:
{
lean_object* v_array_4033_; lean_object* v_idx_4034_; lean_object* v___x_4035_; uint8_t v___x_4036_; 
v_array_4033_ = lean_ctor_get(v___y_4032_, 0);
v_idx_4034_ = lean_ctor_get(v___y_4032_, 1);
v___x_4035_ = lean_byte_array_size(v_array_4033_);
v___x_4036_ = lean_nat_dec_lt(v_idx_4034_, v___x_4035_);
if (v___x_4036_ == 0)
{
lean_object* v___x_4037_; lean_object* v___x_4039_; 
v___x_4037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4037_, 0, v_res_4026_);
lean_ctor_set(v___x_4037_, 1, v_port_4031_);
if (v_isShared_4029_ == 0)
{
lean_ctor_set(v___x_4028_, 1, v___x_4037_);
lean_ctor_set(v___x_4028_, 0, v___y_4032_);
v___x_4039_ = v___x_4028_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___y_4032_);
lean_ctor_set(v_reuseFailAlloc_4040_, 1, v___x_4037_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
else
{
lean_object* v___x_4041_; lean_object* v___x_4043_; 
lean_dec(v_port_4031_);
lean_dec(v_res_4026_);
v___x_4041_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__1));
if (v_isShared_4029_ == 0)
{
lean_ctor_set_tag(v___x_4028_, 1);
lean_ctor_set(v___x_4028_, 1, v___x_4041_);
lean_ctor_set(v___x_4028_, 0, v___y_4032_);
v___x_4043_ = v___x_4028_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v___y_4032_);
lean_ctor_set(v_reuseFailAlloc_4044_, 1, v___x_4041_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
v___jp_4045_:
{
lean_object* v___x_4047_; 
v___x_4047_ = lean_box(0);
v_port_4031_ = v___x_4047_;
v___y_4032_ = v_pos_4046_;
goto v___jp_4030_;
}
v___jp_4048_:
{
lean_object* v___x_4052_; uint8_t v___x_4053_; 
v___x_4052_ = lean_byte_array_size(v_array_4050_);
lean_dec_ref(v_array_4050_);
v___x_4053_ = lean_nat_dec_lt(v_idx_4051_, v___x_4052_);
lean_dec(v_idx_4051_);
if (v___x_4053_ == 0)
{
lean_object* v___x_4054_; 
v___x_4054_ = lean_box(1);
v_port_4031_ = v___x_4054_;
v___y_4032_ = v_pos_4049_;
goto v___jp_4030_;
}
else
{
lean_object* v___x_4055_; lean_object* v___x_4056_; 
lean_del_object(v___x_4028_);
lean_dec(v_res_4026_);
v___x_4055_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__3));
v___x_4056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4056_, 0, v_pos_4049_);
lean_ctor_set(v___x_4056_, 1, v___x_4055_);
return v___x_4056_;
}
}
}
}
else
{
lean_object* v_pos_4100_; lean_object* v_err_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4108_; 
v_pos_4100_ = lean_ctor_get(v___x_4024_, 0);
v_err_4101_ = lean_ctor_get(v___x_4024_, 1);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4103_ = v___x_4024_;
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_err_4101_);
lean_inc(v_pos_4100_);
lean_dec(v___x_4024_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_pos_4100_);
lean_ctor_set(v_reuseFailAlloc_4107_, 1, v_err_4101_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader___boxed(lean_object* v_config_4109_, lean_object* v_a_4110_){
_start:
{
lean_object* v_res_4111_; 
v_res_4111_ = l_Std_Http_URI_Parser_parseHostHeader(v_config_4109_, v_a_4110_);
lean_dec_ref(v_config_4109_);
return v_res_4111_;
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
