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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Http_URI_isValidDomainLabel(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* lean_uv_pton_v4(lean_object*);
lean_object* lean_uv_pton_v6(lean_object*);
lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
extern lean_object* l_Std_Http_URI_Query_empty;
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f(lean_object*);
lean_object* l_Std_Http_URI_Query_insertEncoded(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
uint8_t l_Std_Http_Internal_instDecidableIsLowerCase(lean_object*);
lean_object* lean_string_data(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_List_head_x3f___redArg(lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(lean_object*);
lean_object* l_Std_Http_URI_EncodedFragment_decode(lean_object*);
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
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "invalid scheme"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__0 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__0_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Init.Data.String.Basic"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__2 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__2_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "String.fromUTF8!"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid UTF-8 string"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4_value;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5;
static const lean_closure_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "condition not satisfied"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_value)}};
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
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1;
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13;
static lean_once_cell_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected at least one char"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__15 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__15_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__15_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__16 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__16_value;
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
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "not http absolute uri"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2_value;
static const lean_ctor_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2_value)}};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "http"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__4 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__4_value;
static const lean_string_object l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "https"};
static const lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5 = (const lean_object*)&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority___boxed(lean_object*, lean_object*);
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
uint8_t v___y_98_; uint8_t v___y_106_; uint8_t v___y_112_; uint8_t v___x_117_; uint8_t v___x_118_; 
v___x_117_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_118_ = lean_uint8_dec_le(v___x_117_, v_c_96_);
if (v___x_118_ == 0)
{
v___y_112_ = v___x_118_;
goto v___jp_111_;
}
else
{
uint8_t v___x_119_; uint8_t v___x_120_; 
v___x_119_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_120_ = lean_uint8_dec_le(v_c_96_, v___x_119_);
v___y_112_ = v___x_120_;
goto v___jp_111_;
}
v___jp_97_:
{
if (v___y_98_ == 0)
{
uint8_t v___x_99_; uint8_t v___x_100_; 
v___x_99_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_100_ = lean_uint8_dec_eq(v_c_96_, v___x_99_);
if (v___x_100_ == 0)
{
uint8_t v___x_101_; uint8_t v___x_102_; 
v___x_101_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_102_ = lean_uint8_dec_eq(v_c_96_, v___x_101_);
if (v___x_102_ == 0)
{
uint8_t v___x_103_; uint8_t v___x_104_; 
v___x_103_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_104_ = lean_uint8_dec_eq(v_c_96_, v___x_103_);
if (v___x_104_ == 0)
{
return v___y_98_;
}
else
{
return v___x_104_;
}
}
else
{
return v___x_102_;
}
}
else
{
return v___x_100_;
}
}
else
{
return v___y_98_;
}
}
v___jp_105_:
{
if (v___y_106_ == 0)
{
uint8_t v___x_107_; uint8_t v___x_108_; 
v___x_107_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_108_ = lean_uint8_dec_le(v___x_107_, v_c_96_);
if (v___x_108_ == 0)
{
v___y_98_ = v___x_108_;
goto v___jp_97_;
}
else
{
uint8_t v___x_109_; uint8_t v___x_110_; 
v___x_109_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_110_ = lean_uint8_dec_le(v_c_96_, v___x_109_);
v___y_98_ = v___x_110_;
goto v___jp_97_;
}
}
else
{
return v___y_106_;
}
}
v___jp_111_:
{
if (v___y_112_ == 0)
{
uint8_t v___x_113_; uint8_t v___x_114_; 
v___x_113_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_114_ = lean_uint8_dec_le(v___x_113_, v_c_96_);
if (v___x_114_ == 0)
{
v___y_106_ = v___x_114_;
goto v___jp_105_;
}
else
{
uint8_t v___x_115_; uint8_t v___x_116_; 
v___x_115_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_116_ = lean_uint8_dec_le(v_c_96_, v___x_115_);
v___y_106_ = v___x_116_;
goto v___jp_105_;
}
}
else
{
return v___y_112_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___boxed(lean_object* v_c_121_){
_start:
{
uint8_t v_c_boxed_122_; uint8_t v_res_123_; lean_object* v_r_124_; 
v_c_boxed_122_ = lean_unbox(v_c_121_);
v_res_123_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0(v_c_boxed_122_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(lean_object* v_x_125_){
_start:
{
if (lean_obj_tag(v_x_125_) == 0)
{
uint8_t v___x_126_; 
v___x_126_ = 1;
return v___x_126_;
}
else
{
lean_object* v_head_127_; lean_object* v_tail_128_; uint8_t v___y_130_; uint32_t v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; uint8_t v___y_156_; 
v_head_127_ = lean_ctor_get(v_x_125_, 0);
v_tail_128_ = lean_ctor_get(v_x_125_, 1);
v___x_151_ = lean_unbox_uint32(v_head_127_);
v___x_152_ = lean_uint32_to_nat(v___x_151_);
v___x_153_ = lean_unsigned_to_nat(128u);
v___x_154_ = lean_nat_dec_lt(v___x_152_, v___x_153_);
lean_dec(v___x_152_);
if (v___x_154_ == 0)
{
v___y_130_ = v___x_154_;
goto v___jp_129_;
}
else
{
uint32_t v___x_164_; uint32_t v___x_165_; uint8_t v___x_166_; 
v___x_164_ = 48;
v___x_165_ = lean_unbox_uint32(v_head_127_);
v___x_166_ = lean_uint32_dec_le(v___x_164_, v___x_165_);
if (v___x_166_ == 0)
{
v___y_156_ = v___x_166_;
goto v___jp_155_;
}
else
{
uint32_t v___x_167_; uint32_t v___x_168_; uint8_t v___x_169_; 
v___x_167_ = 57;
v___x_168_ = lean_unbox_uint32(v_head_127_);
v___x_169_ = lean_uint32_dec_le(v___x_168_, v___x_167_);
v___y_156_ = v___x_169_;
goto v___jp_155_;
}
}
v___jp_129_:
{
if (v___y_130_ == 0)
{
uint32_t v___x_131_; uint32_t v___x_132_; uint8_t v___x_133_; 
v___x_131_ = 43;
v___x_132_ = lean_unbox_uint32(v_head_127_);
v___x_133_ = lean_uint32_dec_eq(v___x_132_, v___x_131_);
if (v___x_133_ == 0)
{
uint32_t v___x_134_; uint32_t v___x_135_; uint8_t v___x_136_; 
v___x_134_ = 45;
v___x_135_ = lean_unbox_uint32(v_head_127_);
v___x_136_ = lean_uint32_dec_eq(v___x_135_, v___x_134_);
if (v___x_136_ == 0)
{
uint32_t v___x_137_; uint32_t v___x_138_; uint8_t v___x_139_; 
v___x_137_ = 46;
v___x_138_ = lean_unbox_uint32(v_head_127_);
v___x_139_ = lean_uint32_dec_eq(v___x_138_, v___x_137_);
if (v___x_139_ == 0)
{
return v___y_130_;
}
else
{
v_x_125_ = v_tail_128_;
goto _start;
}
}
else
{
v_x_125_ = v_tail_128_;
goto _start;
}
}
else
{
v_x_125_ = v_tail_128_;
goto _start;
}
}
else
{
v_x_125_ = v_tail_128_;
goto _start;
}
}
v___jp_144_:
{
uint32_t v___x_145_; uint32_t v___x_146_; uint8_t v___x_147_; 
v___x_145_ = 97;
v___x_146_ = lean_unbox_uint32(v_head_127_);
v___x_147_ = lean_uint32_dec_le(v___x_145_, v___x_146_);
if (v___x_147_ == 0)
{
v___y_130_ = v___x_147_;
goto v___jp_129_;
}
else
{
uint32_t v___x_148_; uint32_t v___x_149_; uint8_t v___x_150_; 
v___x_148_ = 122;
v___x_149_ = lean_unbox_uint32(v_head_127_);
v___x_150_ = lean_uint32_dec_le(v___x_149_, v___x_148_);
v___y_130_ = v___x_150_;
goto v___jp_129_;
}
}
v___jp_155_:
{
if (v___y_156_ == 0)
{
uint32_t v___x_157_; uint32_t v___x_158_; uint8_t v___x_159_; 
v___x_157_ = 65;
v___x_158_ = lean_unbox_uint32(v_head_127_);
v___x_159_ = lean_uint32_dec_le(v___x_157_, v___x_158_);
if (v___x_159_ == 0)
{
goto v___jp_144_;
}
else
{
uint32_t v___x_160_; uint32_t v___x_161_; uint8_t v___x_162_; 
v___x_160_ = 90;
v___x_161_ = lean_unbox_uint32(v_head_127_);
v___x_162_ = lean_uint32_dec_le(v___x_161_, v___x_160_);
if (v___x_162_ == 0)
{
goto v___jp_144_;
}
else
{
v___y_130_ = v___x_154_;
goto v___jp_129_;
}
}
}
else
{
v_x_125_ = v_tail_128_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1___boxed(lean_object* v_x_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(v_x_170_);
lean_dec(v_x_170_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(lean_object* v_s_173_, lean_object* v_p_174_){
_start:
{
uint32_t v___y_176_; lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = lean_string_utf8_byte_size(v_s_173_);
v___x_182_ = lean_nat_dec_eq(v_p_174_, v___x_181_);
if (v___x_182_ == 0)
{
uint32_t v___x_183_; uint32_t v___x_184_; uint8_t v___x_185_; 
v___x_183_ = lean_string_utf8_get_fast(v_s_173_, v_p_174_);
v___x_184_ = 65;
v___x_185_ = lean_uint32_dec_le(v___x_184_, v___x_183_);
if (v___x_185_ == 0)
{
v___y_176_ = v___x_183_;
goto v___jp_175_;
}
else
{
uint32_t v___x_186_; uint8_t v___x_187_; 
v___x_186_ = 90;
v___x_187_ = lean_uint32_dec_le(v___x_183_, v___x_186_);
if (v___x_187_ == 0)
{
v___y_176_ = v___x_183_;
goto v___jp_175_;
}
else
{
uint32_t v___x_188_; uint32_t v___x_189_; 
v___x_188_ = 32;
v___x_189_ = lean_uint32_add(v___x_183_, v___x_188_);
v___y_176_ = v___x_189_;
goto v___jp_175_;
}
}
}
else
{
lean_dec(v_p_174_);
return v_s_173_;
}
v___jp_175_:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
lean_inc(v_p_174_);
v___x_177_ = lean_string_utf8_set(v_s_173_, v_p_174_, v___y_176_);
v___x_178_ = l_Char_utf8Size(v___y_176_);
v___x_179_ = lean_nat_add(v_p_174_, v___x_178_);
lean_dec(v___x_178_);
lean_dec(v_p_174_);
v_s_173_ = v___x_177_;
v_p_174_ = v___x_179_;
goto _start;
}
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_196_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4));
v___x_197_ = lean_unsigned_to_nat(46u);
v___x_198_ = lean_unsigned_to_nat(193u);
v___x_199_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3));
v___x_200_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__2));
v___x_201_ = l_mkPanicMessageWithDecl(v___x_200_, v___x_199_, v___x_198_, v___x_197_, v___x_196_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(lean_object* v_config_209_, lean_object* v_a_210_){
_start:
{
lean_object* v___y_212_; lean_object* v___y_216_; lean_object* v___y_217_; uint8_t v_val_218_; uint32_t v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; lean_object* v___y_229_; lean_object* v___y_230_; lean_object* v___y_231_; lean_object* v_maxSchemeLength_246_; lean_object* v___x_247_; uint8_t v___x_248_; lean_object* v___y_250_; uint8_t v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; lean_object* v_lower_254_; lean_object* v_upper_255_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; uint8_t v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; 
v_maxSchemeLength_246_ = lean_ctor_get(v_config_209_, 0);
v___x_247_ = lean_unsigned_to_nat(0u);
v___x_248_ = lean_nat_dec_eq(v_maxSchemeLength_246_, v___x_247_);
if (v___x_248_ == 0)
{
lean_object* v_array_276_; lean_object* v_idx_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v_array_276_ = lean_ctor_get(v_a_210_, 0);
v_idx_277_ = lean_ctor_get(v_a_210_, 1);
v___x_278_ = lean_byte_array_size(v_array_276_);
v___x_279_ = lean_nat_dec_lt(v_idx_277_, v___x_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_box(0);
v___x_281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_281_, 0, v_a_210_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
return v___x_281_;
}
else
{
lean_object* v___f_282_; lean_object* v_pos_284_; uint8_t v_res_285_; uint8_t v_c_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v_it_x27_300_; uint8_t v___y_302_; uint8_t v___y_306_; uint8_t v___x_311_; uint8_t v___x_312_; 
v___f_282_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6));
v_c_297_ = lean_byte_array_fget(v_array_276_, v_idx_277_);
v___x_298_ = lean_unsigned_to_nat(1u);
v___x_299_ = lean_nat_add(v_idx_277_, v___x_298_);
lean_inc_ref(v_array_276_);
v_it_x27_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_300_, 0, v_array_276_);
lean_ctor_set(v_it_x27_300_, 1, v___x_299_);
v___x_311_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_312_ = lean_uint8_dec_le(v___x_311_, v_c_297_);
if (v___x_312_ == 0)
{
v___y_306_ = v___x_312_;
goto v___jp_305_;
}
else
{
uint8_t v___x_313_; uint8_t v___x_314_; 
v___x_313_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_314_ = lean_uint8_dec_le(v_c_297_, v___x_313_);
v___y_306_ = v___x_314_;
goto v___jp_305_;
}
v___jp_283_:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v_snd_289_; lean_object* v_fst_290_; lean_object* v_fst_291_; lean_object* v_array_292_; lean_object* v_idx_293_; lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = lean_nat_sub(v_maxSchemeLength_246_, v___x_286_);
lean_inc_ref(v_pos_284_);
v___x_288_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_282_, v___x_287_, v___x_247_, v_pos_284_);
lean_dec(v___x_287_);
v_snd_289_ = lean_ctor_get(v___x_288_, 1);
lean_inc(v_snd_289_);
v_fst_290_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_fst_290_);
lean_dec_ref(v___x_288_);
v_fst_291_ = lean_ctor_get(v_snd_289_, 0);
lean_inc(v_fst_291_);
lean_dec(v_snd_289_);
v_array_292_ = lean_ctor_get(v_pos_284_, 0);
lean_inc_ref(v_array_292_);
v_idx_293_ = lean_ctor_get(v_pos_284_, 1);
lean_inc(v_idx_293_);
lean_dec_ref(v_pos_284_);
v___x_294_ = lean_nat_add(v_idx_293_, v_fst_290_);
lean_dec(v_fst_290_);
v___x_295_ = lean_byte_array_size(v_array_292_);
v___x_296_ = lean_nat_dec_le(v_idx_293_, v___x_247_);
if (v___x_296_ == 0)
{
v___y_268_ = v___x_295_;
v___y_269_ = v_array_292_;
v___y_270_ = v___x_294_;
v___y_271_ = v_res_285_;
v___y_272_ = v___x_247_;
v___y_273_ = v_fst_291_;
v___y_274_ = v_idx_293_;
goto v___jp_267_;
}
else
{
lean_dec(v_idx_293_);
v___y_268_ = v___x_295_;
v___y_269_ = v_array_292_;
v___y_270_ = v___x_294_;
v___y_271_ = v_res_285_;
v___y_272_ = v___x_247_;
v___y_273_ = v_fst_291_;
v___y_274_ = v___x_247_;
goto v___jp_267_;
}
}
v___jp_301_:
{
if (v___y_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
lean_dec_ref_known(v_it_x27_300_, 2);
v___x_303_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__8));
v___x_304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_304_, 0, v_a_210_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
return v___x_304_;
}
else
{
lean_dec_ref(v_a_210_);
v_pos_284_ = v_it_x27_300_;
v_res_285_ = v_c_297_;
goto v___jp_283_;
}
}
v___jp_305_:
{
if (v___y_306_ == 0)
{
uint8_t v___x_307_; uint8_t v___x_308_; 
v___x_307_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_308_ = lean_uint8_dec_le(v___x_307_, v_c_297_);
if (v___x_308_ == 0)
{
v___y_302_ = v___x_308_;
goto v___jp_301_;
}
else
{
uint8_t v___x_309_; uint8_t v___x_310_; 
v___x_309_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_310_ = lean_uint8_dec_le(v_c_297_, v___x_309_);
v___y_302_ = v___x_310_;
goto v___jp_301_;
}
}
else
{
lean_dec_ref(v_a_210_);
v_pos_284_ = v_it_x27_300_;
v_res_285_ = v_c_297_;
goto v___jp_283_;
}
}
}
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10));
v___x_316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_316_, 0, v_a_210_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
return v___x_316_;
}
v___jp_211_:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1));
v___x_214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_214_, 0, v___y_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
return v___x_214_;
}
v___jp_215_:
{
if (v_val_218_ == 0)
{
lean_dec_ref(v___y_216_);
v___y_212_ = v___y_217_;
goto v___jp_211_;
}
else
{
lean_object* v___x_219_; 
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v___y_217_);
lean_ctor_set(v___x_219_, 1, v___y_216_);
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
v___jp_228_:
{
lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_232_ = l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___y_231_, v___y_230_);
lean_inc_ref(v___x_232_);
v___x_233_ = l_Std_Http_Internal_instDecidableIsLowerCase(v___x_232_);
if (v___x_233_ == 0)
{
lean_dec_ref(v___x_232_);
v___y_212_ = v___y_229_;
goto v___jp_211_;
}
else
{
lean_object* v___x_234_; uint8_t v___x_235_; 
lean_inc_ref(v___x_232_);
v___x_234_ = lean_string_data(v___x_232_);
v___x_235_ = l_List_all___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(v___x_234_);
if (v___x_235_ == 0)
{
lean_dec(v___x_234_);
lean_dec_ref(v___x_232_);
v___y_212_ = v___y_229_;
goto v___jp_211_;
}
else
{
lean_object* v___x_236_; 
v___x_236_ = l_List_head_x3f___redArg(v___x_234_);
lean_dec(v___x_234_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_dec_ref(v___x_232_);
v___y_212_ = v___y_229_;
goto v___jp_211_;
}
else
{
lean_object* v_val_237_; uint32_t v___x_238_; uint32_t v___x_239_; uint8_t v___x_240_; 
v_val_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_val_237_);
lean_dec_ref_known(v___x_236_, 1);
v___x_238_ = 65;
v___x_239_ = lean_unbox_uint32(v_val_237_);
v___x_240_ = lean_uint32_dec_le(v___x_238_, v___x_239_);
if (v___x_240_ == 0)
{
uint32_t v___x_241_; 
v___x_241_ = lean_unbox_uint32(v_val_237_);
lean_dec(v_val_237_);
v___y_221_ = v___x_241_;
v___y_222_ = v___x_232_;
v___y_223_ = v___y_229_;
goto v___jp_220_;
}
else
{
uint32_t v___x_242_; uint32_t v___x_243_; uint8_t v___x_244_; 
v___x_242_ = 90;
v___x_243_ = lean_unbox_uint32(v_val_237_);
v___x_244_ = lean_uint32_dec_le(v___x_243_, v___x_242_);
if (v___x_244_ == 0)
{
uint32_t v___x_245_; 
v___x_245_ = lean_unbox_uint32(v_val_237_);
lean_dec(v_val_237_);
v___y_221_ = v___x_245_;
v___y_222_ = v___x_232_;
v___y_223_ = v___y_229_;
goto v___jp_220_;
}
else
{
lean_dec(v_val_237_);
v___y_216_ = v___x_232_;
v___y_217_ = v___y_229_;
v_val_218_ = v___x_235_;
goto v___jp_215_;
}
}
}
}
}
}
v___jp_249_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_256_ = l_ByteArray_toByteSlice(v___y_250_, v_lower_254_, v_upper_255_);
v___x_257_ = l_ByteArray_empty;
v___x_258_ = lean_byte_array_push(v___x_257_, v___y_251_);
v___x_259_ = l_ByteSlice_toByteArray(v___x_256_);
v___x_260_ = lean_byte_array_size(v___x_258_);
v___x_261_ = lean_byte_array_size(v___x_259_);
lean_inc(v___y_253_);
v___x_262_ = lean_byte_array_copy_slice(v___x_259_, v___y_253_, v___x_258_, v___x_260_, v___x_261_, v___x_248_);
lean_dec_ref(v___x_259_);
v___x_263_ = lean_string_validate_utf8(v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec_ref(v___x_262_);
v___x_264_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5);
v___x_265_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_264_);
v___y_229_ = v___y_252_;
v___y_230_ = v___y_253_;
v___y_231_ = v___x_265_;
goto v___jp_228_;
}
else
{
lean_object* v___x_266_; 
v___x_266_ = lean_string_from_utf8_unchecked(v___x_262_);
v___y_229_ = v___y_252_;
v___y_230_ = v___y_253_;
v___y_231_ = v___x_266_;
goto v___jp_228_;
}
}
v___jp_267_:
{
uint8_t v___x_275_; 
v___x_275_ = lean_nat_dec_le(v___y_270_, v___y_268_);
if (v___x_275_ == 0)
{
lean_dec(v___y_270_);
v___y_250_ = v___y_269_;
v___y_251_ = v___y_271_;
v___y_252_ = v___y_273_;
v___y_253_ = v___y_272_;
v_lower_254_ = v___y_274_;
v_upper_255_ = v___y_268_;
goto v___jp_249_;
}
else
{
lean_dec(v___y_268_);
v___y_250_ = v___y_269_;
v___y_251_ = v___y_271_;
v___y_252_ = v___y_273_;
v___y_253_ = v___y_272_;
v_lower_254_ = v___y_274_;
v_upper_255_ = v___y_270_;
goto v___jp_249_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___boxed(lean_object* v_config_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_317_, v_a_318_);
lean_dec_ref(v_config_317_);
return v_res_319_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(uint8_t v___y_320_){
_start:
{
uint8_t v___x_321_; uint8_t v___x_322_; 
v___x_321_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_322_ = lean_uint8_dec_le(v___x_321_, v___y_320_);
if (v___x_322_ == 0)
{
return v___x_322_;
}
else
{
uint8_t v___x_323_; uint8_t v___x_324_; 
v___x_323_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_324_ = lean_uint8_dec_le(v___y_320_, v___x_323_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0___boxed(lean_object* v___y_325_){
_start:
{
uint8_t v___y_582__boxed_326_; uint8_t v_res_327_; lean_object* v_r_328_; 
v___y_582__boxed_326_ = lean_unbox(v___y_325_);
v_res_327_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(v___y_582__boxed_326_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(lean_object* v_a_332_){
_start:
{
lean_object* v___f_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v_snd_337_; lean_object* v_fst_338_; lean_object* v_fst_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_392_; 
v___f_333_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0));
v___x_334_ = lean_unsigned_to_nat(5u);
v___x_335_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_332_);
v___x_336_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_333_, v___x_334_, v___x_335_, v_a_332_);
v_snd_337_ = lean_ctor_get(v___x_336_, 1);
lean_inc(v_snd_337_);
v_fst_338_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_fst_338_);
lean_dec_ref(v___x_336_);
v_fst_339_ = lean_ctor_get(v_snd_337_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v_snd_337_);
if (v_isSharedCheck_392_ == 0)
{
lean_object* v_unused_393_; 
v_unused_393_ = lean_ctor_get(v_snd_337_, 1);
lean_dec(v_unused_393_);
v___x_341_ = v_snd_337_;
v_isShared_342_ = v_isSharedCheck_392_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_fst_339_);
lean_dec(v_snd_337_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_392_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___y_344_; lean_object* v_array_375_; lean_object* v_idx_376_; lean_object* v_lower_378_; lean_object* v_upper_379_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___y_389_; uint8_t v___x_391_; 
v_array_375_ = lean_ctor_get(v_a_332_, 0);
lean_inc_ref(v_array_375_);
v_idx_376_ = lean_ctor_get(v_a_332_, 1);
lean_inc(v_idx_376_);
lean_dec_ref(v_a_332_);
v___x_386_ = lean_nat_add(v_idx_376_, v_fst_338_);
lean_dec(v_fst_338_);
v___x_387_ = lean_byte_array_size(v_array_375_);
v___x_391_ = lean_nat_dec_le(v_idx_376_, v___x_335_);
if (v___x_391_ == 0)
{
v___y_389_ = v_idx_376_;
goto v___jp_388_;
}
else
{
lean_dec(v_idx_376_);
v___y_389_ = v___x_335_;
goto v___jp_388_;
}
v___jp_343_:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = lean_string_utf8_byte_size(v___y_344_);
lean_inc_ref(v___y_344_);
v___x_346_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_346_, 0, v___y_344_);
lean_ctor_set(v___x_346_, 1, v___x_335_);
lean_ctor_set(v___x_346_, 2, v___x_345_);
v___x_347_ = l_String_Slice_toNat_x3f(v___x_346_);
lean_dec_ref_known(v___x_346_, 3);
if (lean_obj_tag(v___x_347_) == 1)
{
lean_object* v_val_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_368_; 
lean_dec_ref(v___y_344_);
v_val_348_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_368_ == 0)
{
v___x_350_ = v___x_347_;
v_isShared_351_ = v_isSharedCheck_368_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_val_348_);
lean_dec(v___x_347_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_368_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = lean_unsigned_to_nat(65535u);
v___x_353_ = lean_nat_dec_lt(v___x_352_, v_val_348_);
if (v___x_353_ == 0)
{
uint16_t v___x_354_; lean_object* v___x_355_; lean_object* v___x_357_; 
lean_del_object(v___x_350_);
v___x_354_ = lean_uint16_of_nat(v_val_348_);
lean_dec(v_val_348_);
v___x_355_ = lean_box(v___x_354_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 1, v___x_355_);
v___x_357_ = v___x_341_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_fst_339_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_359_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1));
v___x_360_ = l_Nat_reprFast(v_val_348_);
v___x_361_ = lean_string_append(v___x_359_, v___x_360_);
lean_dec_ref(v___x_360_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_361_);
v___x_363_ = v___x_350_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_367_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_365_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set_tag(v___x_341_, 1);
lean_ctor_set(v___x_341_, 1, v___x_363_);
v___x_365_ = v___x_341_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_fst_339_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
else
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
lean_dec(v___x_347_);
v___x_369_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2));
v___x_370_ = lean_string_append(v___x_369_, v___y_344_);
lean_dec_ref(v___y_344_);
v___x_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
if (v_isShared_342_ == 0)
{
lean_ctor_set_tag(v___x_341_, 1);
lean_ctor_set(v___x_341_, 1, v___x_371_);
v___x_373_ = v___x_341_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_fst_339_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
v___jp_377_:
{
lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_380_ = l_ByteArray_toByteSlice(v_array_375_, v_lower_378_, v_upper_379_);
v___x_381_ = l_ByteSlice_toByteArray(v___x_380_);
v___x_382_ = lean_string_validate_utf8(v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_384_; 
lean_dec_ref(v___x_381_);
v___x_383_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5);
v___x_384_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_383_);
v___y_344_ = v___x_384_;
goto v___jp_343_;
}
else
{
lean_object* v___x_385_; 
v___x_385_ = lean_string_from_utf8_unchecked(v___x_381_);
v___y_344_ = v___x_385_;
goto v___jp_343_;
}
}
v___jp_388_:
{
uint8_t v___x_390_; 
v___x_390_ = lean_nat_dec_le(v___x_386_, v___x_387_);
if (v___x_390_ == 0)
{
lean_dec(v___x_386_);
v_lower_378_ = v___y_389_;
v_upper_379_ = v___x_387_;
goto v___jp_377_;
}
else
{
v_lower_378_ = v___y_389_;
v_upper_379_ = v___x_386_;
goto v___jp_377_;
}
}
}
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0(void){
_start:
{
uint32_t v___x_394_; uint8_t v___x_395_; 
v___x_394_ = 58;
v___x_395_ = lean_uint32_to_uint8(v___x_394_);
return v___x_395_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1(void){
_start:
{
uint32_t v___x_396_; uint8_t v___x_397_; 
v___x_396_ = 37;
v___x_397_ = lean_uint32_to_uint8(v___x_396_);
return v___x_397_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2(void){
_start:
{
uint32_t v___x_398_; uint8_t v___x_399_; 
v___x_398_ = 38;
v___x_399_ = lean_uint32_to_uint8(v___x_398_);
return v___x_399_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3(void){
_start:
{
uint32_t v___x_400_; uint8_t v___x_401_; 
v___x_400_ = 39;
v___x_401_ = lean_uint32_to_uint8(v___x_400_);
return v___x_401_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4(void){
_start:
{
uint32_t v___x_402_; uint8_t v___x_403_; 
v___x_402_ = 40;
v___x_403_ = lean_uint32_to_uint8(v___x_402_);
return v___x_403_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5(void){
_start:
{
uint32_t v___x_404_; uint8_t v___x_405_; 
v___x_404_ = 41;
v___x_405_ = lean_uint32_to_uint8(v___x_404_);
return v___x_405_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6(void){
_start:
{
uint32_t v___x_406_; uint8_t v___x_407_; 
v___x_406_ = 42;
v___x_407_ = lean_uint32_to_uint8(v___x_406_);
return v___x_407_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7(void){
_start:
{
uint32_t v___x_408_; uint8_t v___x_409_; 
v___x_408_ = 44;
v___x_409_ = lean_uint32_to_uint8(v___x_408_);
return v___x_409_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8(void){
_start:
{
uint32_t v___x_410_; uint8_t v___x_411_; 
v___x_410_ = 59;
v___x_411_ = lean_uint32_to_uint8(v___x_410_);
return v___x_411_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9(void){
_start:
{
uint32_t v___x_412_; uint8_t v___x_413_; 
v___x_412_ = 61;
v___x_413_ = lean_uint32_to_uint8(v___x_412_);
return v___x_413_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10(void){
_start:
{
uint32_t v___x_414_; uint8_t v___x_415_; 
v___x_414_ = 33;
v___x_415_ = lean_uint32_to_uint8(v___x_414_);
return v___x_415_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11(void){
_start:
{
uint32_t v___x_416_; uint8_t v___x_417_; 
v___x_416_ = 36;
v___x_417_ = lean_uint32_to_uint8(v___x_416_);
return v___x_417_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12(void){
_start:
{
uint32_t v___x_418_; uint8_t v___x_419_; 
v___x_418_ = 95;
v___x_419_ = lean_uint32_to_uint8(v___x_418_);
return v___x_419_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13(void){
_start:
{
uint32_t v___x_420_; uint8_t v___x_421_; 
v___x_420_ = 126;
v___x_421_ = lean_uint32_to_uint8(v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(uint8_t v_x_422_){
_start:
{
uint8_t v___y_424_; uint8_t v___y_430_; uint8_t v___y_450_; uint8_t v___y_456_; uint8_t v___y_462_; uint8_t v___y_468_; uint8_t v___y_474_; uint8_t v___x_479_; uint8_t v___x_480_; 
v___x_479_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_480_ = lean_uint8_dec_eq(v_x_422_, v___x_479_);
if (v___x_480_ == 0)
{
uint8_t v___x_481_; uint8_t v___x_482_; 
v___x_481_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_482_ = lean_uint8_dec_le(v___x_481_, v_x_422_);
if (v___x_482_ == 0)
{
v___y_474_ = v___x_482_;
goto v___jp_473_;
}
else
{
uint8_t v___x_483_; uint8_t v___x_484_; 
v___x_483_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_484_ = lean_uint8_dec_le(v_x_422_, v___x_483_);
v___y_474_ = v___x_484_;
goto v___jp_473_;
}
}
else
{
uint8_t v___x_485_; 
v___x_485_ = 0;
return v___x_485_;
}
v___jp_423_:
{
if (v___y_424_ == 0)
{
uint8_t v___x_425_; uint8_t v___x_426_; 
v___x_425_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_426_ = lean_uint8_dec_eq(v_x_422_, v___x_425_);
if (v___x_426_ == 0)
{
uint8_t v___x_427_; uint8_t v___x_428_; 
v___x_427_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_428_ = lean_uint8_dec_eq(v_x_422_, v___x_427_);
if (v___x_428_ == 0)
{
return v___x_426_;
}
else
{
return v___x_428_;
}
}
else
{
return v___x_426_;
}
}
else
{
return v___y_424_;
}
}
v___jp_429_:
{
if (v___y_430_ == 0)
{
uint8_t v___x_431_; uint8_t v___x_432_; 
v___x_431_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_432_ = lean_uint8_dec_eq(v_x_422_, v___x_431_);
if (v___x_432_ == 0)
{
uint8_t v___x_433_; uint8_t v___x_434_; 
v___x_433_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_434_ = lean_uint8_dec_eq(v_x_422_, v___x_433_);
if (v___x_434_ == 0)
{
uint8_t v___x_435_; uint8_t v___x_436_; 
v___x_435_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_436_ = lean_uint8_dec_eq(v_x_422_, v___x_435_);
if (v___x_436_ == 0)
{
uint8_t v___x_437_; uint8_t v___x_438_; 
v___x_437_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_438_ = lean_uint8_dec_eq(v_x_422_, v___x_437_);
if (v___x_438_ == 0)
{
uint8_t v___x_439_; uint8_t v___x_440_; 
v___x_439_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_440_ = lean_uint8_dec_eq(v_x_422_, v___x_439_);
if (v___x_440_ == 0)
{
uint8_t v___x_441_; uint8_t v___x_442_; 
v___x_441_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_442_ = lean_uint8_dec_eq(v_x_422_, v___x_441_);
if (v___x_442_ == 0)
{
uint8_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_444_ = lean_uint8_dec_eq(v_x_422_, v___x_443_);
if (v___x_444_ == 0)
{
uint8_t v___x_445_; uint8_t v___x_446_; 
v___x_445_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_446_ = lean_uint8_dec_eq(v_x_422_, v___x_445_);
if (v___x_446_ == 0)
{
uint8_t v___x_447_; uint8_t v___x_448_; 
v___x_447_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_448_ = lean_uint8_dec_eq(v_x_422_, v___x_447_);
v___y_424_ = v___x_448_;
goto v___jp_423_;
}
else
{
v___y_424_ = v___x_446_;
goto v___jp_423_;
}
}
else
{
v___y_424_ = v___x_444_;
goto v___jp_423_;
}
}
else
{
v___y_424_ = v___x_442_;
goto v___jp_423_;
}
}
else
{
v___y_424_ = v___x_440_;
goto v___jp_423_;
}
}
else
{
v___y_424_ = v___x_438_;
goto v___jp_423_;
}
}
else
{
v___y_424_ = v___x_436_;
goto v___jp_423_;
}
}
else
{
v___y_424_ = v___x_434_;
goto v___jp_423_;
}
}
else
{
v___y_424_ = v___x_432_;
goto v___jp_423_;
}
}
else
{
return v___y_430_;
}
}
v___jp_449_:
{
if (v___y_450_ == 0)
{
uint8_t v___x_451_; uint8_t v___x_452_; 
v___x_451_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_452_ = lean_uint8_dec_eq(v_x_422_, v___x_451_);
if (v___x_452_ == 0)
{
uint8_t v___x_453_; uint8_t v___x_454_; 
v___x_453_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_454_ = lean_uint8_dec_eq(v_x_422_, v___x_453_);
v___y_430_ = v___x_454_;
goto v___jp_429_;
}
else
{
v___y_430_ = v___x_452_;
goto v___jp_429_;
}
}
else
{
return v___y_450_;
}
}
v___jp_455_:
{
if (v___y_456_ == 0)
{
uint8_t v___x_457_; uint8_t v___x_458_; 
v___x_457_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_458_ = lean_uint8_dec_eq(v_x_422_, v___x_457_);
if (v___x_458_ == 0)
{
uint8_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_460_ = lean_uint8_dec_eq(v_x_422_, v___x_459_);
v___y_450_ = v___x_460_;
goto v___jp_449_;
}
else
{
v___y_450_ = v___x_458_;
goto v___jp_449_;
}
}
else
{
return v___y_456_;
}
}
v___jp_461_:
{
if (v___y_462_ == 0)
{
uint8_t v___x_463_; uint8_t v___x_464_; 
v___x_463_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_464_ = lean_uint8_dec_eq(v_x_422_, v___x_463_);
if (v___x_464_ == 0)
{
uint8_t v___x_465_; uint8_t v___x_466_; 
v___x_465_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_466_ = lean_uint8_dec_eq(v_x_422_, v___x_465_);
v___y_456_ = v___x_466_;
goto v___jp_455_;
}
else
{
v___y_456_ = v___x_464_;
goto v___jp_455_;
}
}
else
{
return v___y_462_;
}
}
v___jp_467_:
{
if (v___y_468_ == 0)
{
uint8_t v___x_469_; uint8_t v___x_470_; 
v___x_469_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_470_ = lean_uint8_dec_le(v___x_469_, v_x_422_);
if (v___x_470_ == 0)
{
v___y_462_ = v___x_470_;
goto v___jp_461_;
}
else
{
uint8_t v___x_471_; uint8_t v___x_472_; 
v___x_471_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_472_ = lean_uint8_dec_le(v_x_422_, v___x_471_);
v___y_462_ = v___x_472_;
goto v___jp_461_;
}
}
else
{
return v___y_468_;
}
}
v___jp_473_:
{
if (v___y_474_ == 0)
{
uint8_t v___x_475_; uint8_t v___x_476_; 
v___x_475_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_476_ = lean_uint8_dec_le(v___x_475_, v_x_422_);
if (v___x_476_ == 0)
{
v___y_468_ = v___x_476_;
goto v___jp_467_;
}
else
{
uint8_t v___x_477_; uint8_t v___x_478_; 
v___x_477_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_478_ = lean_uint8_dec_le(v_x_422_, v___x_477_);
v___y_468_ = v___x_478_;
goto v___jp_467_;
}
}
else
{
return v___y_474_;
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
uint8_t v___y_494_; uint8_t v___y_499_; uint8_t v___y_519_; uint8_t v___y_525_; uint8_t v___y_531_; uint8_t v___y_537_; uint8_t v___y_543_; uint8_t v___x_548_; uint8_t v___x_549_; 
v___x_548_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_549_ = lean_uint8_dec_le(v___x_548_, v_x_492_);
if (v___x_549_ == 0)
{
v___y_543_ = v___x_549_;
goto v___jp_542_;
}
else
{
uint8_t v___x_550_; uint8_t v___x_551_; 
v___x_550_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_551_ = lean_uint8_dec_le(v_x_492_, v___x_550_);
v___y_543_ = v___x_551_;
goto v___jp_542_;
}
v___jp_493_:
{
if (v___y_494_ == 0)
{
uint8_t v___x_495_; 
v___x_495_ = lean_uint8_dec_eq(v_x_492_, v___x_490_);
if (v___x_495_ == 0)
{
uint8_t v___x_496_; uint8_t v___x_497_; 
v___x_496_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_497_ = lean_uint8_dec_eq(v_x_492_, v___x_496_);
if (v___x_497_ == 0)
{
return v___x_495_;
}
else
{
return v___x_491_;
}
}
else
{
return v___x_495_;
}
}
else
{
return v___y_494_;
}
}
v___jp_498_:
{
if (v___y_499_ == 0)
{
uint8_t v___x_500_; uint8_t v___x_501_; 
v___x_500_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_501_ = lean_uint8_dec_eq(v_x_492_, v___x_500_);
if (v___x_501_ == 0)
{
uint8_t v___x_502_; uint8_t v___x_503_; 
v___x_502_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_503_ = lean_uint8_dec_eq(v_x_492_, v___x_502_);
if (v___x_503_ == 0)
{
uint8_t v___x_504_; uint8_t v___x_505_; 
v___x_504_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_505_ = lean_uint8_dec_eq(v_x_492_, v___x_504_);
if (v___x_505_ == 0)
{
uint8_t v___x_506_; uint8_t v___x_507_; 
v___x_506_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_507_ = lean_uint8_dec_eq(v_x_492_, v___x_506_);
if (v___x_507_ == 0)
{
uint8_t v___x_508_; uint8_t v___x_509_; 
v___x_508_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_509_ = lean_uint8_dec_eq(v_x_492_, v___x_508_);
if (v___x_509_ == 0)
{
uint8_t v___x_510_; uint8_t v___x_511_; 
v___x_510_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_511_ = lean_uint8_dec_eq(v_x_492_, v___x_510_);
if (v___x_511_ == 0)
{
uint8_t v___x_512_; uint8_t v___x_513_; 
v___x_512_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_513_ = lean_uint8_dec_eq(v_x_492_, v___x_512_);
if (v___x_513_ == 0)
{
uint8_t v___x_514_; uint8_t v___x_515_; 
v___x_514_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_515_ = lean_uint8_dec_eq(v_x_492_, v___x_514_);
if (v___x_515_ == 0)
{
uint8_t v___x_516_; uint8_t v___x_517_; 
v___x_516_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_517_ = lean_uint8_dec_eq(v_x_492_, v___x_516_);
v___y_494_ = v___x_517_;
goto v___jp_493_;
}
else
{
v___y_494_ = v___x_515_;
goto v___jp_493_;
}
}
else
{
v___y_494_ = v___x_513_;
goto v___jp_493_;
}
}
else
{
v___y_494_ = v___x_511_;
goto v___jp_493_;
}
}
else
{
v___y_494_ = v___x_509_;
goto v___jp_493_;
}
}
else
{
v___y_494_ = v___x_507_;
goto v___jp_493_;
}
}
else
{
v___y_494_ = v___x_505_;
goto v___jp_493_;
}
}
else
{
v___y_494_ = v___x_503_;
goto v___jp_493_;
}
}
else
{
v___y_494_ = v___x_501_;
goto v___jp_493_;
}
}
else
{
return v___y_499_;
}
}
v___jp_518_:
{
if (v___y_519_ == 0)
{
uint8_t v___x_520_; uint8_t v___x_521_; 
v___x_520_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_521_ = lean_uint8_dec_eq(v_x_492_, v___x_520_);
if (v___x_521_ == 0)
{
uint8_t v___x_522_; uint8_t v___x_523_; 
v___x_522_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_523_ = lean_uint8_dec_eq(v_x_492_, v___x_522_);
v___y_499_ = v___x_523_;
goto v___jp_498_;
}
else
{
v___y_499_ = v___x_521_;
goto v___jp_498_;
}
}
else
{
return v___y_519_;
}
}
v___jp_524_:
{
if (v___y_525_ == 0)
{
uint8_t v___x_526_; uint8_t v___x_527_; 
v___x_526_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_527_ = lean_uint8_dec_eq(v_x_492_, v___x_526_);
if (v___x_527_ == 0)
{
uint8_t v___x_528_; uint8_t v___x_529_; 
v___x_528_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_529_ = lean_uint8_dec_eq(v_x_492_, v___x_528_);
v___y_519_ = v___x_529_;
goto v___jp_518_;
}
else
{
v___y_519_ = v___x_527_;
goto v___jp_518_;
}
}
else
{
return v___y_525_;
}
}
v___jp_530_:
{
if (v___y_531_ == 0)
{
uint8_t v___x_532_; uint8_t v___x_533_; 
v___x_532_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_533_ = lean_uint8_dec_eq(v_x_492_, v___x_532_);
if (v___x_533_ == 0)
{
uint8_t v___x_534_; uint8_t v___x_535_; 
v___x_534_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_535_ = lean_uint8_dec_eq(v_x_492_, v___x_534_);
v___y_525_ = v___x_535_;
goto v___jp_524_;
}
else
{
v___y_525_ = v___x_533_;
goto v___jp_524_;
}
}
else
{
return v___y_531_;
}
}
v___jp_536_:
{
if (v___y_537_ == 0)
{
uint8_t v___x_538_; uint8_t v___x_539_; 
v___x_538_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_539_ = lean_uint8_dec_le(v___x_538_, v_x_492_);
if (v___x_539_ == 0)
{
v___y_531_ = v___x_539_;
goto v___jp_530_;
}
else
{
uint8_t v___x_540_; uint8_t v___x_541_; 
v___x_540_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_541_ = lean_uint8_dec_le(v_x_492_, v___x_540_);
v___y_531_ = v___x_541_;
goto v___jp_530_;
}
}
else
{
return v___y_537_;
}
}
v___jp_542_:
{
if (v___y_543_ == 0)
{
uint8_t v___x_544_; uint8_t v___x_545_; 
v___x_544_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_545_ = lean_uint8_dec_le(v___x_544_, v_x_492_);
if (v___x_545_ == 0)
{
v___y_537_ = v___x_545_;
goto v___jp_536_;
}
else
{
uint8_t v___x_546_; uint8_t v___x_547_; 
v___x_546_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_547_ = lean_uint8_dec_le(v_x_492_, v___x_546_);
v___y_537_ = v___x_547_;
goto v___jp_536_;
}
}
else
{
return v___y_543_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed(lean_object* v___x_552_, lean_object* v___x_553_, lean_object* v_x_554_){
_start:
{
uint8_t v___x_4665__boxed_555_; uint8_t v___x_4666__boxed_556_; uint8_t v_x_boxed_557_; uint8_t v_res_558_; lean_object* v_r_559_; 
v___x_4665__boxed_555_ = lean_unbox(v___x_552_);
v___x_4666__boxed_556_ = lean_unbox(v___x_553_);
v_x_boxed_557_ = lean_unbox(v_x_554_);
v_res_558_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(v___x_4665__boxed_555_, v___x_4666__boxed_556_, v_x_boxed_557_);
v_r_559_ = lean_box(v_res_558_);
return v_r_559_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(lean_object* v_config_564_, lean_object* v_a_565_){
_start:
{
lean_object* v___y_567_; lean_object* v_userPassEncoded_568_; lean_object* v___y_569_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v_lower_576_; lean_object* v_upper_577_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_592_; lean_object* v_pos_593_; lean_object* v_maxUserInfoLength_595_; lean_object* v___f_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v_snd_599_; lean_object* v_fst_600_; lean_object* v_fst_601_; lean_object* v_array_602_; lean_object* v_idx_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_655_; 
v_maxUserInfoLength_595_ = lean_ctor_get(v_config_564_, 2);
v___f_596_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2));
v___x_597_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_565_);
v___x_598_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_596_, v_maxUserInfoLength_595_, v___x_597_, v_a_565_);
v_snd_599_ = lean_ctor_get(v___x_598_, 1);
lean_inc(v_snd_599_);
v_fst_600_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_fst_600_);
lean_dec_ref(v___x_598_);
v_fst_601_ = lean_ctor_get(v_snd_599_, 0);
lean_inc(v_fst_601_);
lean_dec(v_snd_599_);
v_array_602_ = lean_ctor_get(v_a_565_, 0);
v_idx_603_ = lean_ctor_get(v_a_565_, 1);
v_isSharedCheck_655_ = !lean_is_exclusive(v_a_565_);
if (v_isSharedCheck_655_ == 0)
{
v___x_605_ = v_a_565_;
v_isShared_606_ = v_isSharedCheck_655_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_idx_603_);
lean_inc(v_array_602_);
lean_dec(v_a_565_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_655_;
goto v_resetjp_604_;
}
v___jp_566_:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v___y_567_);
lean_ctor_set(v___x_570_, 1, v_userPassEncoded_568_);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v___y_569_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
return v___x_571_;
}
v___jp_572_:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = l_ByteArray_toByteSlice(v___y_574_, v_lower_576_, v_upper_577_);
v___x_579_ = l_ByteSlice_toByteArray(v___x_578_);
v___x_580_ = l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(v___x_579_);
if (lean_obj_tag(v___x_580_) == 1)
{
v___y_567_ = v___y_575_;
v_userPassEncoded_568_ = v___x_580_;
v___y_569_ = v___y_573_;
goto v___jp_566_;
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; 
lean_dec(v___x_580_);
lean_dec_ref(v___y_575_);
v___x_581_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1));
v___x_582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_582_, 0, v___y_573_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
return v___x_582_;
}
}
v___jp_583_:
{
uint8_t v___x_590_; 
v___x_590_ = lean_nat_dec_le(v___y_585_, v___y_588_);
if (v___x_590_ == 0)
{
lean_dec(v___y_585_);
v___y_573_ = v___y_584_;
v___y_574_ = v___y_586_;
v___y_575_ = v___y_587_;
v_lower_576_ = v___y_589_;
v_upper_577_ = v___y_588_;
goto v___jp_572_;
}
else
{
lean_dec(v___y_588_);
v___y_573_ = v___y_584_;
v___y_574_ = v___y_586_;
v___y_575_ = v___y_587_;
v_lower_576_ = v___y_589_;
v_upper_577_ = v___y_585_;
goto v___jp_572_;
}
}
v___jp_591_:
{
lean_object* v___x_594_; 
v___x_594_ = lean_box(0);
v___y_567_ = v___y_592_;
v_userPassEncoded_568_ = v___x_594_;
v___y_569_ = v_pos_593_;
goto v___jp_566_;
}
v_resetjp_604_:
{
lean_object* v_lower_608_; lean_object* v_upper_609_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___y_652_; uint8_t v___x_654_; 
v___x_649_ = lean_nat_add(v_idx_603_, v_fst_600_);
lean_dec(v_fst_600_);
v___x_650_ = lean_byte_array_size(v_array_602_);
v___x_654_ = lean_nat_dec_le(v_idx_603_, v___x_597_);
if (v___x_654_ == 0)
{
v___y_652_ = v_idx_603_;
goto v___jp_651_;
}
else
{
lean_dec(v_idx_603_);
v___y_652_ = v___x_597_;
goto v___jp_651_;
}
v___jp_607_:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = l_ByteArray_toByteSlice(v_array_602_, v_lower_608_, v_upper_609_);
v___x_611_ = l_ByteSlice_toByteArray(v___x_610_);
v___x_612_ = l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(v___x_611_);
if (lean_obj_tag(v___x_612_) == 1)
{
lean_object* v_val_613_; lean_object* v_array_614_; lean_object* v_idx_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v_val_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_val_613_);
lean_dec_ref_known(v___x_612_, 1);
v_array_614_ = lean_ctor_get(v_fst_601_, 0);
v_idx_615_ = lean_ctor_get(v_fst_601_, 1);
v___x_616_ = lean_byte_array_size(v_array_614_);
v___x_617_ = lean_nat_dec_lt(v_idx_615_, v___x_616_);
if (v___x_617_ == 0)
{
lean_del_object(v___x_605_);
v___y_592_ = v_val_613_;
v_pos_593_ = v_fst_601_;
goto v___jp_591_;
}
else
{
uint8_t v___x_618_; uint8_t v___x_619_; uint8_t v___x_620_; 
v___x_618_ = lean_byte_array_fget(v_array_614_, v_idx_615_);
v___x_619_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_620_ = lean_uint8_dec_eq(v___x_618_, v___x_619_);
if (v___x_620_ == 0)
{
lean_del_object(v___x_605_);
v___y_592_ = v_val_613_;
v_pos_593_ = v_fst_601_;
goto v___jp_591_;
}
else
{
if (v___x_620_ == 0)
{
lean_del_object(v___x_605_);
v___y_592_ = v_val_613_;
v_pos_593_ = v_fst_601_;
goto v___jp_591_;
}
else
{
if (v___x_617_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_623_; 
lean_dec(v_val_613_);
v___x_621_ = lean_box(0);
if (v_isShared_606_ == 0)
{
lean_ctor_set_tag(v___x_605_, 1);
lean_ctor_set(v___x_605_, 1, v___x_621_);
lean_ctor_set(v___x_605_, 0, v_fst_601_);
v___x_623_ = v___x_605_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_fst_601_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
else
{
lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_642_; 
lean_inc(v_idx_615_);
lean_inc_ref(v_array_614_);
lean_del_object(v___x_605_);
v_isSharedCheck_642_ = !lean_is_exclusive(v_fst_601_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; lean_object* v_unused_644_; 
v_unused_643_ = lean_ctor_get(v_fst_601_, 1);
lean_dec(v_unused_643_);
v_unused_644_ = lean_ctor_get(v_fst_601_, 0);
lean_dec(v_unused_644_);
v___x_626_ = v_fst_601_;
v_isShared_627_ = v_isSharedCheck_642_;
goto v_resetjp_625_;
}
else
{
lean_dec(v_fst_601_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_642_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___f_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_628_ = lean_box(v___x_619_);
v___x_629_ = lean_box(v___x_617_);
v___f_630_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed), 3, 2);
lean_closure_set(v___f_630_, 0, v___x_628_);
lean_closure_set(v___f_630_, 1, v___x_629_);
v___x_631_ = lean_unsigned_to_nat(1u);
v___x_632_ = lean_nat_add(v_idx_615_, v___x_631_);
lean_dec(v_idx_615_);
lean_inc(v___x_632_);
lean_inc_ref(v_array_614_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v___x_632_);
v___x_634_ = v___x_626_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_array_614_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v___x_632_);
v___x_634_ = v_reuseFailAlloc_641_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_635_; lean_object* v_snd_636_; lean_object* v_fst_637_; lean_object* v_fst_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_635_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_630_, v_maxUserInfoLength_595_, v___x_597_, v___x_634_);
v_snd_636_ = lean_ctor_get(v___x_635_, 1);
lean_inc(v_snd_636_);
v_fst_637_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_fst_637_);
lean_dec_ref(v___x_635_);
v_fst_638_ = lean_ctor_get(v_snd_636_, 0);
lean_inc(v_fst_638_);
lean_dec(v_snd_636_);
v___x_639_ = lean_nat_add(v___x_632_, v_fst_637_);
lean_dec(v_fst_637_);
v___x_640_ = lean_nat_dec_le(v___x_632_, v___x_597_);
if (v___x_640_ == 0)
{
v___y_584_ = v_fst_638_;
v___y_585_ = v___x_639_;
v___y_586_ = v_array_614_;
v___y_587_ = v_val_613_;
v___y_588_ = v___x_616_;
v___y_589_ = v___x_632_;
goto v___jp_583_;
}
else
{
lean_dec(v___x_632_);
v___y_584_ = v_fst_638_;
v___y_585_ = v___x_639_;
v___y_586_ = v_array_614_;
v___y_587_ = v_val_613_;
v___y_588_ = v___x_616_;
v___y_589_ = v___x_597_;
goto v___jp_583_;
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
lean_object* v___x_645_; lean_object* v___x_647_; 
lean_dec(v___x_612_);
v___x_645_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1));
if (v_isShared_606_ == 0)
{
lean_ctor_set_tag(v___x_605_, 1);
lean_ctor_set(v___x_605_, 1, v___x_645_);
lean_ctor_set(v___x_605_, 0, v_fst_601_);
v___x_647_ = v___x_605_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_fst_601_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
v___jp_651_:
{
uint8_t v___x_653_; 
v___x_653_ = lean_nat_dec_le(v___x_649_, v___x_650_);
if (v___x_653_ == 0)
{
lean_dec(v___x_649_);
v_lower_608_ = v___y_652_;
v_upper_609_ = v___x_650_;
goto v___jp_607_;
}
else
{
v_lower_608_ = v___y_652_;
v_upper_609_ = v___x_649_;
goto v___jp_607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___boxed(lean_object* v_config_656_, lean_object* v_a_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(v_config_656_, v_a_657_);
lean_dec_ref(v_config_656_);
return v_res_658_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0(void){
_start:
{
uint32_t v___x_659_; uint8_t v___x_660_; 
v___x_659_ = 70;
v___x_660_ = lean_uint32_to_uint8(v___x_659_);
return v___x_660_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1(void){
_start:
{
uint32_t v___x_661_; uint8_t v___x_662_; 
v___x_661_ = 102;
v___x_662_ = lean_uint32_to_uint8(v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(uint8_t v___x_663_, uint8_t v_x_664_){
_start:
{
uint8_t v___y_666_; uint8_t v___y_672_; uint8_t v___x_677_; uint8_t v___x_678_; 
v___x_677_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_678_ = lean_uint8_dec_eq(v_x_664_, v___x_677_);
if (v___x_678_ == 0)
{
uint8_t v___x_679_; uint8_t v___x_680_; 
v___x_679_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_680_ = lean_uint8_dec_eq(v_x_664_, v___x_679_);
if (v___x_680_ == 0)
{
uint8_t v___x_681_; uint8_t v___x_682_; 
v___x_681_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_682_ = lean_uint8_dec_le(v___x_681_, v_x_664_);
if (v___x_682_ == 0)
{
v___y_672_ = v___x_682_;
goto v___jp_671_;
}
else
{
uint8_t v___x_683_; uint8_t v___x_684_; 
v___x_683_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_684_ = lean_uint8_dec_le(v_x_664_, v___x_683_);
v___y_672_ = v___x_684_;
goto v___jp_671_;
}
}
else
{
return v___x_663_;
}
}
else
{
return v___x_663_;
}
v___jp_665_:
{
if (v___y_666_ == 0)
{
uint8_t v___x_667_; uint8_t v___x_668_; 
v___x_667_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_668_ = lean_uint8_dec_le(v___x_667_, v_x_664_);
if (v___x_668_ == 0)
{
if (v___x_668_ == 0)
{
return v___x_668_;
}
else
{
return v___x_663_;
}
}
else
{
uint8_t v___x_669_; uint8_t v___x_670_; 
v___x_669_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0);
v___x_670_ = lean_uint8_dec_le(v_x_664_, v___x_669_);
if (v___x_670_ == 0)
{
return v___x_670_;
}
else
{
return v___x_663_;
}
}
}
else
{
return v___x_663_;
}
}
v___jp_671_:
{
if (v___y_672_ == 0)
{
uint8_t v___x_673_; uint8_t v___x_674_; 
v___x_673_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_674_ = lean_uint8_dec_le(v___x_673_, v_x_664_);
if (v___x_674_ == 0)
{
v___y_666_ = v___x_674_;
goto v___jp_665_;
}
else
{
uint8_t v___x_675_; uint8_t v___x_676_; 
v___x_675_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1);
v___x_676_ = lean_uint8_dec_le(v_x_664_, v___x_675_);
v___y_666_ = v___x_676_;
goto v___jp_665_;
}
}
else
{
return v___x_663_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___boxed(lean_object* v___x_685_, lean_object* v_x_686_){
_start:
{
uint8_t v___x_1493__boxed_687_; uint8_t v_x_boxed_688_; uint8_t v_res_689_; lean_object* v_r_690_; 
v___x_1493__boxed_687_ = lean_unbox(v___x_685_);
v_x_boxed_688_ = lean_unbox(v_x_686_);
v_res_689_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(v___x_1493__boxed_687_, v_x_boxed_688_);
v_r_690_ = lean_box(v_res_689_);
return v_r_690_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1(void){
_start:
{
uint32_t v___x_692_; uint8_t v___x_693_; 
v___x_692_ = 91;
v___x_693_ = lean_uint32_to_uint8(v___x_692_);
return v___x_693_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3(void){
_start:
{
uint8_t v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1);
v___x_696_ = lean_uint8_to_nat(v___x_695_);
return v___x_696_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3);
v___x_698_ = l_Nat_reprFast(v___x_697_);
return v___x_698_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_699_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4);
v___x_700_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_701_ = lean_string_append(v___x_700_, v___x_699_);
return v___x_701_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_703_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_704_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5);
v___x_705_ = lean_string_append(v___x_704_, v___x_703_);
return v___x_705_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7);
v___x_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
return v___x_707_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9(void){
_start:
{
uint32_t v___x_708_; uint8_t v___x_709_; 
v___x_708_ = 93;
v___x_709_ = lean_uint32_to_uint8(v___x_708_);
return v___x_709_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10(void){
_start:
{
uint8_t v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9);
v___x_711_ = lean_uint8_to_nat(v___x_710_);
return v___x_711_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10);
v___x_713_ = l_Nat_reprFast(v___x_712_);
return v___x_713_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_714_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11);
v___x_715_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_716_ = lean_string_append(v___x_715_, v___x_714_);
return v___x_716_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_717_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_718_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12);
v___x_719_ = lean_string_append(v___x_718_, v___x_717_);
return v___x_719_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13);
v___x_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(lean_object* v_a_725_){
_start:
{
lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v_array_736_; lean_object* v_idx_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v_array_736_ = lean_ctor_get(v_a_725_, 0);
v_idx_737_ = lean_ctor_get(v_a_725_, 1);
v___x_738_ = lean_byte_array_size(v_array_736_);
v___x_739_ = lean_nat_dec_lt(v_idx_737_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_box(0);
v___x_741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_741_, 0, v_a_725_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
return v___x_741_;
}
else
{
uint8_t v___x_742_; uint8_t v_got_743_; uint8_t v___x_744_; 
v___x_742_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1);
v_got_743_ = lean_byte_array_fget(v_array_736_, v_idx_737_);
v___x_744_ = lean_uint8_dec_eq(v_got_743_, v___x_742_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8);
v___x_746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_746_, 0, v_a_725_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
return v___x_746_;
}
else
{
lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_823_; 
lean_inc(v_idx_737_);
lean_inc_ref(v_array_736_);
v_isSharedCheck_823_ = !lean_is_exclusive(v_a_725_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; lean_object* v_unused_825_; 
v_unused_824_ = lean_ctor_get(v_a_725_, 1);
lean_dec(v_unused_824_);
v_unused_825_ = lean_ctor_get(v_a_725_, 0);
lean_dec(v_unused_825_);
v___x_748_ = v_a_725_;
v_isShared_749_ = v_isSharedCheck_823_;
goto v_resetjp_747_;
}
else
{
lean_dec(v_a_725_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_823_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___f_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_750_ = lean_box(v___x_739_);
v___f_751_ = lean_alloc_closure((void*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___boxed), 2, 1);
lean_closure_set(v___f_751_, 0, v___x_750_);
v___x_752_ = lean_unsigned_to_nat(1u);
v___x_753_ = lean_nat_add(v_idx_737_, v___x_752_);
lean_dec(v_idx_737_);
lean_inc(v___x_753_);
lean_inc_ref(v_array_736_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v___x_753_);
v___x_755_ = v___x_748_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_array_736_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v___x_753_);
v___x_755_ = v_reuseFailAlloc_822_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v_snd_759_; lean_object* v_fst_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_821_; 
v___x_756_ = lean_unsigned_to_nat(256u);
v___x_757_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___x_755_);
v___x_758_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_751_, v___x_756_, v___x_757_, v___x_755_);
v_snd_759_ = lean_ctor_get(v___x_758_, 1);
v_fst_760_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_821_ == 0)
{
v___x_762_ = v___x_758_;
v_isShared_763_ = v_isSharedCheck_821_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_snd_759_);
lean_inc(v_fst_760_);
lean_dec(v___x_758_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_821_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v_fst_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_819_; 
v_fst_764_ = lean_ctor_get(v_snd_759_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v_snd_759_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v_snd_759_, 1);
lean_dec(v_unused_820_);
v___x_766_ = v_snd_759_;
v_isShared_767_ = v_isSharedCheck_819_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_fst_764_);
lean_dec(v_snd_759_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_819_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___y_769_; uint8_t v___x_803_; 
v___x_803_ = lean_nat_dec_eq(v_fst_760_, v___x_757_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; lean_object* v___y_806_; uint8_t v___x_814_; 
lean_dec_ref(v___x_755_);
v___x_804_ = lean_nat_add(v___x_753_, v_fst_760_);
lean_dec(v_fst_760_);
v___x_814_ = lean_nat_dec_le(v___x_753_, v___x_757_);
if (v___x_814_ == 0)
{
v___y_806_ = v___x_753_;
goto v___jp_805_;
}
else
{
lean_dec(v___x_753_);
v___y_806_ = v___x_757_;
goto v___jp_805_;
}
v___jp_805_:
{
uint8_t v___x_807_; 
v___x_807_ = lean_nat_dec_le(v___x_804_, v___x_738_);
if (v___x_807_ == 0)
{
lean_object* v___x_809_; 
lean_dec(v___x_804_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 1, v___x_738_);
lean_ctor_set(v___x_762_, 0, v___y_806_);
v___x_809_ = v___x_762_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___y_806_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v___x_738_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
v___y_769_ = v___x_809_;
goto v___jp_768_;
}
}
else
{
lean_object* v___x_812_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 1, v___x_804_);
lean_ctor_set(v___x_762_, 0, v___y_806_);
v___x_812_ = v___x_762_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___y_806_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___x_804_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
v___y_769_ = v___x_812_;
goto v___jp_768_;
}
}
}
}
else
{
lean_object* v___x_815_; lean_object* v___x_817_; 
lean_del_object(v___x_766_);
lean_dec(v_fst_764_);
lean_dec(v_fst_760_);
lean_dec(v___x_753_);
lean_dec_ref(v_array_736_);
v___x_815_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__16));
if (v_isShared_763_ == 0)
{
lean_ctor_set_tag(v___x_762_, 1);
lean_ctor_set(v___x_762_, 1, v___x_815_);
lean_ctor_set(v___x_762_, 0, v___x_755_);
v___x_817_ = v___x_762_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
v___jp_768_:
{
lean_object* v_array_770_; lean_object* v_idx_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v_array_770_ = lean_ctor_get(v_fst_764_, 0);
v_idx_771_ = lean_ctor_get(v_fst_764_, 1);
v___x_772_ = lean_byte_array_size(v_array_770_);
v___x_773_ = lean_nat_dec_lt(v_idx_771_, v___x_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_776_; 
lean_dec_ref(v___y_769_);
lean_dec_ref(v_array_736_);
v___x_774_ = lean_box(0);
if (v_isShared_767_ == 0)
{
lean_ctor_set_tag(v___x_766_, 1);
lean_ctor_set(v___x_766_, 1, v___x_774_);
v___x_776_ = v___x_766_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_fst_764_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
else
{
uint8_t v___x_778_; uint8_t v_got_779_; uint8_t v___x_780_; 
v___x_778_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9);
v_got_779_ = lean_byte_array_fget(v_array_770_, v_idx_771_);
v___x_780_ = lean_uint8_dec_eq(v_got_779_, v___x_778_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; lean_object* v___x_783_; 
lean_dec_ref(v___y_769_);
lean_dec_ref(v_array_736_);
v___x_781_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14);
if (v_isShared_767_ == 0)
{
lean_ctor_set_tag(v___x_766_, 1);
lean_ctor_set(v___x_766_, 1, v___x_781_);
v___x_783_ = v___x_766_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_fst_764_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
else
{
lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_800_; 
lean_inc(v_idx_771_);
lean_inc_ref(v_array_770_);
lean_del_object(v___x_766_);
v_isSharedCheck_800_ = !lean_is_exclusive(v_fst_764_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; lean_object* v_unused_802_; 
v_unused_801_ = lean_ctor_get(v_fst_764_, 1);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v_fst_764_, 0);
lean_dec(v_unused_802_);
v___x_786_ = v_fst_764_;
v_isShared_787_ = v_isSharedCheck_800_;
goto v_resetjp_785_;
}
else
{
lean_dec(v_fst_764_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_800_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v_lower_788_; lean_object* v_upper_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_793_; 
v_lower_788_ = lean_ctor_get(v___y_769_, 0);
lean_inc(v_lower_788_);
v_upper_789_ = lean_ctor_get(v___y_769_, 1);
lean_inc(v_upper_789_);
lean_dec_ref(v___y_769_);
v___x_790_ = l_ByteArray_toByteSlice(v_array_736_, v_lower_788_, v_upper_789_);
v___x_791_ = lean_nat_add(v_idx_771_, v___x_752_);
lean_dec(v_idx_771_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 1, v___x_791_);
v___x_793_ = v___x_786_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_array_770_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_791_);
v___x_793_ = v_reuseFailAlloc_799_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = l_ByteSlice_toByteArray(v___x_790_);
v___x_795_ = lean_string_validate_utf8(v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; 
lean_dec_ref(v___x_794_);
v___x_796_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5);
v___x_797_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_796_);
v___y_727_ = v___x_793_;
v___y_728_ = v___x_797_;
goto v___jp_726_;
}
else
{
lean_object* v___x_798_; 
v___x_798_ = lean_string_from_utf8_unchecked(v___x_794_);
v___y_727_ = v___x_793_;
v___y_728_ = v___x_798_;
goto v___jp_726_;
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
v___jp_726_:
{
lean_object* v___x_729_; 
v___x_729_ = lean_uv_pton_v6(v___y_728_);
if (lean_obj_tag(v___x_729_) == 1)
{
lean_object* v_val_730_; lean_object* v___x_731_; 
lean_dec_ref(v___y_728_);
v_val_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_val_730_);
lean_dec_ref_known(v___x_729_, 1);
v___x_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_731_, 0, v___y_727_);
lean_ctor_set(v___x_731_, 1, v_val_730_);
return v___x_731_;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
lean_dec(v___x_729_);
v___x_732_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0));
v___x_733_ = lean_string_append(v___x_732_, v___y_728_);
lean_dec_ref(v___y_728_);
v___x_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
v___x_735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_735_, 0, v___y_727_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
return v___x_735_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(uint8_t v_x_826_){
_start:
{
uint8_t v___x_827_; uint8_t v___x_828_; 
v___x_827_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_828_ = lean_uint8_dec_eq(v_x_826_, v___x_827_);
if (v___x_828_ == 0)
{
uint8_t v___x_829_; uint8_t v___x_830_; 
v___x_829_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_830_ = lean_uint8_dec_le(v___x_829_, v_x_826_);
if (v___x_830_ == 0)
{
return v___x_830_;
}
else
{
uint8_t v___x_831_; uint8_t v___x_832_; 
v___x_831_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_832_ = lean_uint8_dec_le(v_x_826_, v___x_831_);
return v___x_832_;
}
}
else
{
return v___x_828_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0___boxed(lean_object* v_x_833_){
_start:
{
uint8_t v_x_boxed_834_; uint8_t v_res_835_; lean_object* v_r_836_; 
v_x_boxed_834_ = lean_unbox(v_x_833_);
v_res_835_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(v_x_boxed_834_);
v_r_836_ = lean_box(v_res_835_);
return v_r_836_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(lean_object* v_a_839_){
_start:
{
lean_object* v___f_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v_snd_844_; lean_object* v_fst_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_890_; 
v___f_840_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0));
v___x_841_ = lean_unsigned_to_nat(256u);
v___x_842_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_839_);
v___x_843_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_840_, v___x_841_, v___x_842_, v_a_839_);
v_snd_844_ = lean_ctor_get(v___x_843_, 1);
v_fst_845_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_890_ == 0)
{
v___x_847_ = v___x_843_;
v_isShared_848_ = v_isSharedCheck_890_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_snd_844_);
lean_inc(v_fst_845_);
lean_dec(v___x_843_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_890_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v_fst_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_888_; 
v_fst_849_ = lean_ctor_get(v_snd_844_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v_snd_844_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; 
v_unused_889_ = lean_ctor_get(v_snd_844_, 1);
lean_dec(v_unused_889_);
v___x_851_ = v_snd_844_;
v_isShared_852_ = v_isSharedCheck_888_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_fst_849_);
lean_dec(v_snd_844_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_888_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___y_854_; uint8_t v___x_866_; 
v___x_866_ = lean_nat_dec_eq(v_fst_845_, v___x_842_);
if (v___x_866_ == 0)
{
lean_object* v_array_867_; lean_object* v_idx_868_; lean_object* v_lower_870_; lean_object* v_upper_871_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___y_881_; uint8_t v___x_883_; 
lean_del_object(v___x_847_);
v_array_867_ = lean_ctor_get(v_a_839_, 0);
lean_inc_ref(v_array_867_);
v_idx_868_ = lean_ctor_get(v_a_839_, 1);
lean_inc(v_idx_868_);
lean_dec_ref(v_a_839_);
v___x_878_ = lean_nat_add(v_idx_868_, v_fst_845_);
lean_dec(v_fst_845_);
v___x_879_ = lean_byte_array_size(v_array_867_);
v___x_883_ = lean_nat_dec_le(v_idx_868_, v___x_842_);
if (v___x_883_ == 0)
{
v___y_881_ = v_idx_868_;
goto v___jp_880_;
}
else
{
lean_dec(v_idx_868_);
v___y_881_ = v___x_842_;
goto v___jp_880_;
}
v___jp_869_:
{
lean_object* v___x_872_; lean_object* v___x_873_; uint8_t v___x_874_; 
v___x_872_ = l_ByteArray_toByteSlice(v_array_867_, v_lower_870_, v_upper_871_);
v___x_873_ = l_ByteSlice_toByteArray(v___x_872_);
v___x_874_ = lean_string_validate_utf8(v___x_873_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; 
lean_dec_ref(v___x_873_);
v___x_875_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5);
v___x_876_ = l_panic___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_875_);
v___y_854_ = v___x_876_;
goto v___jp_853_;
}
else
{
lean_object* v___x_877_; 
v___x_877_ = lean_string_from_utf8_unchecked(v___x_873_);
v___y_854_ = v___x_877_;
goto v___jp_853_;
}
}
v___jp_880_:
{
uint8_t v___x_882_; 
v___x_882_ = lean_nat_dec_le(v___x_878_, v___x_879_);
if (v___x_882_ == 0)
{
lean_dec(v___x_878_);
v_lower_870_ = v___y_881_;
v_upper_871_ = v___x_879_;
goto v___jp_869_;
}
else
{
v_lower_870_ = v___y_881_;
v_upper_871_ = v___x_878_;
goto v___jp_869_;
}
}
}
else
{
lean_object* v___x_884_; lean_object* v___x_886_; 
lean_del_object(v___x_851_);
lean_dec(v_fst_849_);
lean_dec(v_fst_845_);
v___x_884_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__16));
if (v_isShared_848_ == 0)
{
lean_ctor_set_tag(v___x_847_, 1);
lean_ctor_set(v___x_847_, 1, v___x_884_);
lean_ctor_set(v___x_847_, 0, v_a_839_);
v___x_886_ = v___x_847_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_839_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
v___jp_853_:
{
lean_object* v___x_855_; 
v___x_855_ = lean_uv_pton_v4(v___y_854_);
if (lean_obj_tag(v___x_855_) == 1)
{
lean_object* v_val_856_; lean_object* v___x_858_; 
lean_dec_ref(v___y_854_);
v_val_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_val_856_);
lean_dec_ref_known(v___x_855_, 1);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 1, v_val_856_);
v___x_858_ = v___x_851_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_fst_849_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_val_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
else
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
lean_dec(v___x_855_);
v___x_860_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1));
v___x_861_ = lean_string_append(v___x_860_, v___y_854_);
lean_dec_ref(v___y_854_);
v___x_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
if (v_isShared_852_ == 0)
{
lean_ctor_set_tag(v___x_851_, 1);
lean_ctor_set(v___x_851_, 1, v___x_862_);
v___x_864_ = v___x_851_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_fst_849_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v___x_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(lean_object* v_s_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0));
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___boxed(lean_object* v_s_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(v_s_895_);
lean_dec_ref(v_s_895_);
return v_res_896_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(uint8_t v_x_897_){
_start:
{
uint8_t v___y_899_; uint8_t v___y_905_; uint8_t v___y_911_; uint8_t v___x_916_; uint8_t v___x_917_; 
v___x_916_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_917_ = lean_uint8_dec_le(v___x_916_, v_x_897_);
if (v___x_917_ == 0)
{
v___y_911_ = v___x_917_;
goto v___jp_910_;
}
else
{
uint8_t v___x_918_; uint8_t v___x_919_; 
v___x_918_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_919_ = lean_uint8_dec_le(v_x_897_, v___x_918_);
v___y_911_ = v___x_919_;
goto v___jp_910_;
}
v___jp_898_:
{
if (v___y_899_ == 0)
{
uint8_t v___x_900_; uint8_t v___x_901_; 
v___x_900_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_901_ = lean_uint8_dec_eq(v_x_897_, v___x_900_);
if (v___x_901_ == 0)
{
uint8_t v___x_902_; uint8_t v___x_903_; 
v___x_902_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_903_ = lean_uint8_dec_eq(v_x_897_, v___x_902_);
if (v___x_903_ == 0)
{
return v___y_899_;
}
else
{
return v___x_903_;
}
}
else
{
return v___x_901_;
}
}
else
{
return v___y_899_;
}
}
v___jp_904_:
{
if (v___y_905_ == 0)
{
uint8_t v___x_906_; uint8_t v___x_907_; 
v___x_906_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_907_ = lean_uint8_dec_le(v___x_906_, v_x_897_);
if (v___x_907_ == 0)
{
v___y_899_ = v___x_907_;
goto v___jp_898_;
}
else
{
uint8_t v___x_908_; uint8_t v___x_909_; 
v___x_908_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_909_ = lean_uint8_dec_le(v_x_897_, v___x_908_);
v___y_899_ = v___x_909_;
goto v___jp_898_;
}
}
else
{
return v___y_905_;
}
}
v___jp_910_:
{
if (v___y_911_ == 0)
{
uint8_t v___x_912_; uint8_t v___x_913_; 
v___x_912_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_913_ = lean_uint8_dec_le(v___x_912_, v_x_897_);
if (v___x_913_ == 0)
{
v___y_905_ = v___x_913_;
goto v___jp_904_;
}
else
{
uint8_t v___x_914_; uint8_t v___x_915_; 
v___x_914_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_915_ = lean_uint8_dec_le(v_x_897_, v___x_914_);
v___y_905_ = v___x_915_;
goto v___jp_904_;
}
}
else
{
return v___y_911_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed(lean_object* v_x_920_){
_start:
{
uint8_t v_x_boxed_921_; uint8_t v_res_922_; lean_object* v_r_923_; 
v_x_boxed_921_ = lean_unbox(v_x_920_);
v_res_922_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(v_x_boxed_921_);
v_r_923_ = lean_box(v_res_922_);
return v_r_923_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(lean_object* v___x_924_, lean_object* v___x_925_, lean_object* v___x_926_, lean_object* v_a_927_, uint8_t v_b_928_){
_start:
{
if (lean_obj_tag(v_a_927_) == 0)
{
lean_object* v_currPos_929_; lean_object* v_searcher_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_964_; 
v_currPos_929_ = lean_ctor_get(v_a_927_, 0);
v_searcher_930_ = lean_ctor_get(v_a_927_, 1);
v_isSharedCheck_964_ = !lean_is_exclusive(v_a_927_);
if (v_isSharedCheck_964_ == 0)
{
v___x_932_ = v_a_927_;
v_isShared_933_ = v_isSharedCheck_964_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_searcher_930_);
lean_inc(v_currPos_929_);
lean_dec(v_a_927_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_964_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v_startInclusive_934_; lean_object* v_endExclusive_935_; uint8_t v___x_936_; lean_object* v_it_938_; lean_object* v_startInclusive_939_; lean_object* v_endExclusive_940_; lean_object* v___x_944_; uint8_t v___x_945_; 
v_startInclusive_934_ = lean_ctor_get(v___x_925_, 1);
v_endExclusive_935_ = lean_ctor_get(v___x_925_, 2);
v___x_936_ = 1;
v___x_944_ = lean_nat_sub(v_endExclusive_935_, v_startInclusive_934_);
v___x_945_ = lean_nat_dec_eq(v_searcher_930_, v___x_944_);
lean_dec(v___x_944_);
if (v___x_945_ == 0)
{
uint32_t v___x_946_; uint32_t v___x_947_; uint8_t v___x_948_; 
v___x_946_ = 46;
v___x_947_ = lean_string_utf8_get_fast(v___x_924_, v_searcher_930_);
v___x_948_ = lean_uint32_dec_eq(v___x_947_, v___x_946_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_949_ = lean_string_utf8_next_fast(v___x_924_, v_searcher_930_);
lean_dec(v_searcher_930_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 1, v___x_949_);
v___x_951_ = v___x_932_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_currPos_929_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v___x_949_);
v___x_951_ = v_reuseFailAlloc_953_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
v_a_927_ = v___x_951_;
goto _start;
}
}
else
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v_slice_957_; lean_object* v_nextIt_959_; 
v___x_954_ = lean_string_utf8_next_fast(v___x_924_, v_searcher_930_);
v___x_955_ = lean_nat_sub(v___x_954_, v_searcher_930_);
v___x_956_ = lean_nat_add(v_searcher_930_, v___x_955_);
lean_dec(v___x_955_);
v_slice_957_ = l_String_Slice_subslice_x21(v___x_925_, v_currPos_929_, v_searcher_930_);
lean_inc(v___x_956_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 1, v___x_956_);
lean_ctor_set(v___x_932_, 0, v___x_956_);
v_nextIt_959_ = v___x_932_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_956_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v___x_956_);
v_nextIt_959_ = v_reuseFailAlloc_962_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
lean_object* v_startInclusive_960_; lean_object* v_endExclusive_961_; 
v_startInclusive_960_ = lean_ctor_get(v_slice_957_, 0);
lean_inc(v_startInclusive_960_);
v_endExclusive_961_ = lean_ctor_get(v_slice_957_, 1);
lean_inc(v_endExclusive_961_);
lean_dec_ref(v_slice_957_);
v_it_938_ = v_nextIt_959_;
v_startInclusive_939_ = v_startInclusive_960_;
v_endExclusive_940_ = v_endExclusive_961_;
goto v___jp_937_;
}
}
}
else
{
lean_object* v___x_963_; 
lean_del_object(v___x_932_);
lean_dec(v_searcher_930_);
v___x_963_ = lean_box(1);
lean_inc(v___x_926_);
v_it_938_ = v___x_963_;
v_startInclusive_939_ = v_currPos_929_;
v_endExclusive_940_ = v___x_926_;
goto v___jp_937_;
}
v___jp_937_:
{
lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_941_ = lean_string_utf8_extract(v___x_924_, v_startInclusive_939_, v_endExclusive_940_);
lean_dec(v_endExclusive_940_);
lean_dec(v_startInclusive_939_);
v___x_942_ = l_Std_Http_URI_isValidDomainLabel(v___x_941_);
if (v___x_942_ == 0)
{
lean_dec(v_it_938_);
lean_dec(v___x_926_);
return v___x_942_;
}
else
{
v_a_927_ = v_it_938_;
v_b_928_ = v___x_936_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_926_);
return v_b_928_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg___boxed(lean_object* v___x_965_, lean_object* v___x_966_, lean_object* v___x_967_, lean_object* v_a_968_, lean_object* v_b_969_){
_start:
{
uint8_t v_b_boxed_970_; uint8_t v_res_971_; lean_object* v_r_972_; 
v_b_boxed_970_ = lean_unbox(v_b_969_);
v_res_971_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_965_, v___x_966_, v___x_967_, v_a_968_, v_b_boxed_970_);
lean_dec_ref(v___x_966_);
lean_dec_ref(v___x_965_);
v_r_972_ = lean_box(v_res_971_);
return v_r_972_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(lean_object* v___x_973_, lean_object* v___x_974_, lean_object* v_a_975_, uint8_t v_b_976_){
_start:
{
if (lean_obj_tag(v_a_975_) == 0)
{
lean_object* v_currPos_977_; lean_object* v_searcher_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_995_; 
v_currPos_977_ = lean_ctor_get(v_a_975_, 0);
v_searcher_978_ = lean_ctor_get(v_a_975_, 1);
v_isSharedCheck_995_ = !lean_is_exclusive(v_a_975_);
if (v_isSharedCheck_995_ == 0)
{
v___x_980_ = v_a_975_;
v_isShared_981_ = v_isSharedCheck_995_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_searcher_978_);
lean_inc(v_currPos_977_);
lean_dec(v_a_975_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_995_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v_startInclusive_982_; lean_object* v_endExclusive_983_; uint8_t v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v_startInclusive_982_ = lean_ctor_get(v___x_974_, 1);
v_endExclusive_983_ = lean_ctor_get(v___x_974_, 2);
v___x_984_ = 0;
v___x_985_ = lean_nat_sub(v_endExclusive_983_, v_startInclusive_982_);
v___x_986_ = lean_nat_dec_eq(v_searcher_978_, v___x_985_);
lean_dec(v___x_985_);
if (v___x_986_ == 0)
{
uint32_t v___x_987_; uint32_t v___x_988_; uint8_t v___x_989_; 
v___x_987_ = 46;
v___x_988_ = lean_string_utf8_get_fast(v___x_973_, v_searcher_978_);
v___x_989_ = lean_uint32_dec_eq(v___x_988_, v___x_987_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_990_ = lean_string_utf8_next_fast(v___x_973_, v_searcher_978_);
lean_dec(v_searcher_978_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 1, v___x_990_);
v___x_992_ = v___x_980_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_currPos_977_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v___x_990_);
v___x_992_ = v_reuseFailAlloc_994_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
v_a_975_ = v___x_992_;
goto _start;
}
}
else
{
lean_del_object(v___x_980_);
lean_dec(v_searcher_978_);
lean_dec(v_currPos_977_);
return v___x_984_;
}
}
else
{
lean_del_object(v___x_980_);
lean_dec(v_searcher_978_);
lean_dec(v_currPos_977_);
return v___x_984_;
}
}
}
else
{
return v_b_976_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg___boxed(lean_object* v___x_996_, lean_object* v___x_997_, lean_object* v_a_998_, lean_object* v_b_999_){
_start:
{
uint8_t v_b_boxed_1000_; uint8_t v_res_1001_; lean_object* v_r_1002_; 
v_b_boxed_1000_ = lean_unbox(v_b_999_);
v_res_1001_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_996_, v___x_997_, v_a_998_, v_b_boxed_1000_);
lean_dec_ref(v___x_997_);
lean_dec_ref(v___x_996_);
v_r_1002_ = lean_box(v_res_1001_);
return v_r_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(lean_object* v_config_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; uint8_t v___y_1021_; lean_object* v___y_1025_; lean_object* v___y_1026_; uint8_t v___y_1027_; lean_object* v___y_1028_; uint8_t v___y_1029_; lean_object* v___y_1030_; uint8_t v___y_1031_; lean_object* v___y_1041_; lean_object* v___y_1042_; uint8_t v___y_1043_; lean_object* v___y_1044_; lean_object* v_lower_1045_; lean_object* v_upper_1046_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; uint8_t v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v_array_1067_; lean_object* v_idx_1068_; lean_object* v___f_1069_; lean_object* v___y_1071_; lean_object* v_pos_1094_; lean_object* v_pos_1118_; lean_object* v_res_1119_; lean_object* v___y_1121_; lean_object* v___y_1122_; uint8_t v___y_1123_; lean_object* v_pos_1125_; lean_object* v_res_1126_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v_array_1067_ = lean_ctor_get(v_a_1009_, 0);
v_idx_1068_ = lean_ctor_get(v_a_1009_, 1);
v___f_1069_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3));
v___x_1134_ = lean_byte_array_size(v_array_1067_);
v___x_1135_ = lean_nat_dec_lt(v_idx_1068_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; 
lean_inc(v_idx_1068_);
lean_inc_ref(v_array_1067_);
v___x_1136_ = lean_box(0);
v_pos_1125_ = v_a_1009_;
v_res_1126_ = v___x_1136_;
goto v___jp_1124_;
}
else
{
uint8_t v___x_1137_; uint8_t v___x_1138_; uint8_t v___x_1139_; 
v___x_1137_ = lean_byte_array_fget(v_array_1067_, v_idx_1068_);
v___x_1138_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1);
v___x_1139_ = lean_uint8_dec_eq(v___x_1137_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; 
lean_inc(v_idx_1068_);
lean_inc_ref(v_array_1067_);
v___x_1140_ = lean_box(0);
v_pos_1125_ = v_a_1009_;
v_res_1126_ = v___x_1140_;
goto v___jp_1124_;
}
else
{
lean_object* v___x_1141_; 
v___x_1141_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(v_a_1009_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_pos_1142_; lean_object* v_res_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1151_; 
v_pos_1142_ = lean_ctor_get(v___x_1141_, 0);
v_res_1143_ = lean_ctor_get(v___x_1141_, 1);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1145_ = v___x_1141_;
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_res_1143_);
lean_inc(v_pos_1142_);
lean_dec(v___x_1141_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1147_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1147_, 0, v_res_1143_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v___x_1147_);
v___x_1149_ = v___x_1145_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_pos_1142_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
else
{
lean_object* v_pos_1152_; lean_object* v_err_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
v_pos_1152_ = lean_ctor_get(v___x_1141_, 0);
v_err_1153_ = lean_ctor_get(v___x_1141_, 1);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1141_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_err_1153_);
lean_inc(v_pos_1152_);
lean_dec(v___x_1141_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_pos_1152_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_err_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
v___jp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1013_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0));
v___x_1014_ = lean_string_append(v___x_1013_, v___y_1012_);
lean_dec_ref(v___y_1012_);
v___x_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
v___x_1016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___y_1011_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
return v___x_1016_;
}
v___jp_1017_:
{
if (v___y_1021_ == 0)
{
lean_dec_ref(v___y_1018_);
v___y_1011_ = v___y_1019_;
v___y_1012_ = v___y_1020_;
goto v___jp_1010_;
}
else
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
lean_dec_ref(v___y_1020_);
v___x_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___y_1018_);
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___y_1019_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
return v___x_1023_;
}
}
v___jp_1024_:
{
if (v___y_1031_ == 0)
{
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
v___y_1011_ = v___y_1028_;
v___y_1012_ = v___y_1030_;
goto v___jp_1010_;
}
else
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_1032_ = lean_string_utf8_byte_size(v___y_1025_);
lean_inc(v___y_1026_);
lean_inc_ref(v___y_1025_);
v___x_1033_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1033_, 0, v___y_1025_);
lean_ctor_set(v___x_1033_, 1, v___y_1026_);
lean_ctor_set(v___x_1033_, 2, v___x_1032_);
v___x_1034_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(v___x_1033_);
v___x_1035_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___y_1025_, v___x_1033_, v___x_1032_, v___x_1034_, v___y_1031_);
lean_dec_ref_known(v___x_1033_, 3);
if (v___x_1035_ == 0)
{
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
v___y_1011_ = v___y_1028_;
v___y_1012_ = v___y_1030_;
goto v___jp_1010_;
}
else
{
lean_object* v___x_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; 
v___x_1036_ = lean_string_length(v___y_1025_);
v___x_1037_ = lean_unsigned_to_nat(255u);
v___x_1038_ = lean_nat_dec_le(v___x_1036_, v___x_1037_);
if (v___x_1038_ == 0)
{
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
v___y_1011_ = v___y_1028_;
v___y_1012_ = v___y_1030_;
goto v___jp_1010_;
}
else
{
uint8_t v___x_1039_; 
v___x_1039_ = lean_nat_dec_eq(v___x_1032_, v___y_1026_);
lean_dec(v___y_1026_);
if (v___x_1039_ == 0)
{
v___y_1018_ = v___y_1025_;
v___y_1019_ = v___y_1028_;
v___y_1020_ = v___y_1030_;
v___y_1021_ = v___y_1029_;
goto v___jp_1017_;
}
else
{
v___y_1018_ = v___y_1025_;
v___y_1019_ = v___y_1028_;
v___y_1020_ = v___y_1030_;
v___y_1021_ = v___y_1027_;
goto v___jp_1017_;
}
}
}
}
}
v___jp_1040_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1047_ = l_ByteArray_toByteSlice(v___y_1042_, v_lower_1045_, v_upper_1046_);
v___x_1048_ = l_ByteSlice_toByteArray(v___x_1047_);
v___x_1049_ = lean_string_validate_utf8(v___x_1048_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
lean_dec_ref(v___x_1048_);
lean_dec(v___y_1041_);
v___x_1050_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2));
v___x_1051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___y_1044_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
return v___x_1051_;
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; uint8_t v___x_1057_; 
v___x_1052_ = lean_string_from_utf8_unchecked(v___x_1048_);
lean_inc_n(v___y_1041_, 2);
lean_inc_ref(v___x_1052_);
v___x_1053_ = l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___x_1052_, v___y_1041_);
v___x_1054_ = lean_string_utf8_byte_size(v___x_1053_);
lean_inc_ref(v___x_1053_);
v___x_1055_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set(v___x_1055_, 1, v___y_1041_);
lean_ctor_set(v___x_1055_, 2, v___x_1054_);
v___x_1056_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(v___x_1055_);
v___x_1057_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_1053_, v___x_1055_, v___x_1056_, v___x_1049_);
lean_dec_ref_known(v___x_1055_, 3);
if (v___x_1057_ == 0)
{
v___y_1025_ = v___x_1053_;
v___y_1026_ = v___y_1041_;
v___y_1027_ = v___y_1043_;
v___y_1028_ = v___y_1044_;
v___y_1029_ = v___x_1049_;
v___y_1030_ = v___x_1052_;
v___y_1031_ = v___x_1049_;
goto v___jp_1024_;
}
else
{
v___y_1025_ = v___x_1053_;
v___y_1026_ = v___y_1041_;
v___y_1027_ = v___y_1043_;
v___y_1028_ = v___y_1044_;
v___y_1029_ = v___x_1049_;
v___y_1030_ = v___x_1052_;
v___y_1031_ = v___y_1043_;
goto v___jp_1024_;
}
}
}
v___jp_1058_:
{
uint8_t v___x_1066_; 
v___x_1066_ = lean_nat_dec_le(v___y_1059_, v___y_1062_);
if (v___x_1066_ == 0)
{
lean_dec(v___y_1059_);
v___y_1041_ = v___y_1060_;
v___y_1042_ = v___y_1061_;
v___y_1043_ = v___y_1063_;
v___y_1044_ = v___y_1064_;
v_lower_1045_ = v___y_1065_;
v_upper_1046_ = v___y_1062_;
goto v___jp_1040_;
}
else
{
lean_dec(v___y_1062_);
v___y_1041_ = v___y_1060_;
v___y_1042_ = v___y_1061_;
v___y_1043_ = v___y_1063_;
v___y_1044_ = v___y_1064_;
v_lower_1045_ = v___y_1065_;
v_upper_1046_ = v___y_1059_;
goto v___jp_1040_;
}
}
v___jp_1070_:
{
lean_object* v_maxHostLength_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v_snd_1075_; lean_object* v_fst_1076_; lean_object* v_fst_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1091_; 
v_maxHostLength_1072_ = lean_ctor_get(v_config_1008_, 1);
v___x_1073_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___y_1071_);
v___x_1074_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1069_, v_maxHostLength_1072_, v___x_1073_, v___y_1071_);
v_snd_1075_ = lean_ctor_get(v___x_1074_, 1);
lean_inc(v_snd_1075_);
v_fst_1076_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_fst_1076_);
lean_dec_ref(v___x_1074_);
v_fst_1077_ = lean_ctor_get(v_snd_1075_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_snd_1075_);
if (v_isSharedCheck_1091_ == 0)
{
lean_object* v_unused_1092_; 
v_unused_1092_ = lean_ctor_get(v_snd_1075_, 1);
lean_dec(v_unused_1092_);
v___x_1079_ = v_snd_1075_;
v_isShared_1080_ = v_isSharedCheck_1091_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_fst_1077_);
lean_dec(v_snd_1075_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1091_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
uint8_t v___x_1081_; 
v___x_1081_ = lean_nat_dec_eq(v_fst_1076_, v___x_1073_);
if (v___x_1081_ == 0)
{
lean_object* v_array_1082_; lean_object* v_idx_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
lean_del_object(v___x_1079_);
v_array_1082_ = lean_ctor_get(v___y_1071_, 0);
lean_inc_ref(v_array_1082_);
v_idx_1083_ = lean_ctor_get(v___y_1071_, 1);
lean_inc(v_idx_1083_);
lean_dec_ref(v___y_1071_);
v___x_1084_ = lean_nat_add(v_idx_1083_, v_fst_1076_);
lean_dec(v_fst_1076_);
v___x_1085_ = lean_byte_array_size(v_array_1082_);
v___x_1086_ = lean_nat_dec_le(v_idx_1083_, v___x_1073_);
if (v___x_1086_ == 0)
{
v___y_1059_ = v___x_1084_;
v___y_1060_ = v___x_1073_;
v___y_1061_ = v_array_1082_;
v___y_1062_ = v___x_1085_;
v___y_1063_ = v___x_1081_;
v___y_1064_ = v_fst_1077_;
v___y_1065_ = v_idx_1083_;
goto v___jp_1058_;
}
else
{
lean_dec(v_idx_1083_);
v___y_1059_ = v___x_1084_;
v___y_1060_ = v___x_1073_;
v___y_1061_ = v_array_1082_;
v___y_1062_ = v___x_1085_;
v___y_1063_ = v___x_1081_;
v___y_1064_ = v_fst_1077_;
v___y_1065_ = v___x_1073_;
goto v___jp_1058_;
}
}
else
{
lean_object* v___x_1087_; lean_object* v___x_1089_; 
lean_dec(v_fst_1077_);
lean_dec(v_fst_1076_);
v___x_1087_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__16));
if (v_isShared_1080_ == 0)
{
lean_ctor_set_tag(v___x_1079_, 1);
lean_ctor_set(v___x_1079_, 1, v___x_1087_);
lean_ctor_set(v___x_1079_, 0, v___y_1071_);
v___x_1089_ = v___x_1079_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___y_1071_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
v___jp_1093_:
{
lean_object* v___x_1095_; 
lean_inc_ref(v_pos_1094_);
v___x_1095_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(v_pos_1094_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_pos_1096_; lean_object* v_res_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1105_; 
lean_dec_ref(v_pos_1094_);
v_pos_1096_ = lean_ctor_get(v___x_1095_, 0);
v_res_1097_ = lean_ctor_get(v___x_1095_, 1);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1099_ = v___x_1095_;
v_isShared_1100_ = v_isSharedCheck_1105_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_res_1097_);
lean_inc(v_pos_1096_);
lean_dec(v___x_1095_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1105_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1101_, 0, v_res_1097_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 1, v___x_1101_);
v___x_1103_ = v___x_1099_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_pos_1096_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v___x_1101_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
else
{
lean_object* v_err_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1115_; 
v_err_1106_ = lean_ctor_get(v___x_1095_, 1);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1115_ == 0)
{
lean_object* v_unused_1116_; 
v_unused_1116_ = lean_ctor_get(v___x_1095_, 0);
lean_dec(v_unused_1116_);
v___x_1108_ = v___x_1095_;
v_isShared_1109_ = v_isSharedCheck_1115_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_err_1106_);
lean_dec(v___x_1095_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1115_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v_idx_1110_; uint8_t v___x_1111_; 
v_idx_1110_ = lean_ctor_get(v_pos_1094_, 1);
v___x_1111_ = lean_nat_dec_eq(v_idx_1110_, v_idx_1110_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1113_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v_pos_1094_);
v___x_1113_ = v___x_1108_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_pos_1094_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_err_1106_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
else
{
lean_del_object(v___x_1108_);
lean_dec(v_err_1106_);
v___y_1071_ = v_pos_1094_;
goto v___jp_1070_;
}
}
}
}
v___jp_1117_:
{
v___y_1071_ = v_pos_1118_;
goto v___jp_1070_;
}
v___jp_1120_:
{
if (v___y_1123_ == 0)
{
v_pos_1118_ = v___y_1122_;
v_res_1119_ = v___y_1121_;
goto v___jp_1117_;
}
else
{
v_pos_1094_ = v___y_1122_;
goto v___jp_1093_;
}
}
v___jp_1124_:
{
lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1127_ = lean_byte_array_size(v_array_1067_);
v___x_1128_ = lean_nat_dec_lt(v_idx_1068_, v___x_1127_);
if (v___x_1128_ == 0)
{
lean_dec(v_idx_1068_);
lean_dec_ref(v_array_1067_);
v_pos_1118_ = v_pos_1125_;
v_res_1119_ = v_res_1126_;
goto v___jp_1117_;
}
else
{
uint8_t v___x_1129_; uint8_t v___x_1130_; uint8_t v___x_1131_; 
v___x_1129_ = lean_byte_array_fget(v_array_1067_, v_idx_1068_);
lean_dec(v_idx_1068_);
lean_dec_ref(v_array_1067_);
v___x_1130_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_1131_ = lean_uint8_dec_le(v___x_1130_, v___x_1129_);
if (v___x_1131_ == 0)
{
v___y_1121_ = v_res_1126_;
v___y_1122_ = v_pos_1125_;
v___y_1123_ = v___x_1131_;
goto v___jp_1120_;
}
else
{
uint8_t v___x_1132_; uint8_t v___x_1133_; 
v___x_1132_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_1133_ = lean_uint8_dec_le(v___x_1129_, v___x_1132_);
v___y_1121_ = v_res_1126_;
v___y_1122_ = v_pos_1125_;
v___y_1123_ = v___x_1133_;
goto v___jp_1120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___boxed(lean_object* v_config_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1161_, v_a_1162_);
lean_dec_ref(v_config_1161_);
return v_res_1163_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(lean_object* v___x_1164_, lean_object* v___x_1165_, lean_object* v___x_1166_, lean_object* v_inst_1167_, lean_object* v_R_1168_, lean_object* v_a_1169_, uint8_t v_b_1170_, lean_object* v_c_1171_){
_start:
{
uint8_t v___x_1172_; 
v___x_1172_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_1164_, v___x_1165_, v___x_1166_, v_a_1169_, v_b_1170_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___boxed(lean_object* v___x_1173_, lean_object* v___x_1174_, lean_object* v___x_1175_, lean_object* v_inst_1176_, lean_object* v_R_1177_, lean_object* v_a_1178_, lean_object* v_b_1179_, lean_object* v_c_1180_){
_start:
{
uint8_t v_b_boxed_1181_; uint8_t v_res_1182_; lean_object* v_r_1183_; 
v_b_boxed_1181_ = lean_unbox(v_b_1179_);
v_res_1182_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(v___x_1173_, v___x_1174_, v___x_1175_, v_inst_1176_, v_R_1177_, v_a_1178_, v_b_boxed_1181_, v_c_1180_);
lean_dec_ref(v___x_1174_);
lean_dec_ref(v___x_1173_);
v_r_1183_ = lean_box(v_res_1182_);
return v_r_1183_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(lean_object* v___x_1184_, lean_object* v___x_1185_, lean_object* v___x_1186_, lean_object* v_inst_1187_, lean_object* v_R_1188_, lean_object* v_a_1189_, uint8_t v_b_1190_, lean_object* v_c_1191_){
_start:
{
uint8_t v___x_1192_; 
v___x_1192_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_1184_, v___x_1185_, v_a_1189_, v_b_1190_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___boxed(lean_object* v___x_1193_, lean_object* v___x_1194_, lean_object* v___x_1195_, lean_object* v_inst_1196_, lean_object* v_R_1197_, lean_object* v_a_1198_, lean_object* v_b_1199_, lean_object* v_c_1200_){
_start:
{
uint8_t v_b_boxed_1201_; uint8_t v_res_1202_; lean_object* v_r_1203_; 
v_b_boxed_1201_ = lean_unbox(v_b_1199_);
v_res_1202_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(v___x_1193_, v___x_1194_, v___x_1195_, v_inst_1196_, v_R_1197_, v_a_1198_, v_b_boxed_1201_, v_c_1200_);
lean_dec(v___x_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v___x_1193_);
v_r_1203_ = lean_box(v_res_1202_);
return v_r_1203_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2(void){
_start:
{
uint32_t v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = 47;
v___x_1208_ = lean_uint32_to_uint8(v___x_1207_);
return v___x_1208_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3(void){
_start:
{
uint32_t v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = 63;
v___x_1210_ = lean_uint32_to_uint8(v___x_1209_);
return v___x_1210_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4(void){
_start:
{
uint32_t v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = 35;
v___x_1212_ = lean_uint32_to_uint8(v___x_1211_);
return v___x_1212_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5(void){
_start:
{
uint8_t v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1214_ = lean_uint8_to_nat(v___x_1213_);
return v___x_1214_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5);
v___x_1216_ = l_Nat_reprFast(v___x_1215_);
return v___x_1216_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1217_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6);
v___x_1218_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_1219_ = lean_string_append(v___x_1218_, v___x_1217_);
return v___x_1219_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1220_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_1221_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7);
v___x_1222_ = lean_string_append(v___x_1221_, v___x_1220_);
return v___x_1222_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8);
v___x_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10(void){
_start:
{
uint32_t v___x_1225_; uint8_t v___x_1226_; 
v___x_1225_ = 64;
v___x_1226_ = lean_uint32_to_uint8(v___x_1225_);
return v___x_1226_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11(void){
_start:
{
uint8_t v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1228_ = lean_uint8_to_nat(v___x_1227_);
return v___x_1228_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11);
v___x_1230_ = l_Nat_reprFast(v___x_1229_);
return v___x_1230_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1231_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12);
v___x_1232_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_1233_ = lean_string_append(v___x_1232_, v___x_1231_);
return v___x_1233_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14(void){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1234_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_1235_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13);
v___x_1236_ = lean_string_append(v___x_1235_, v___x_1234_);
return v___x_1236_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15(void){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14);
v___x_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(lean_object* v_config_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v_port_1244_; lean_object* v___y_1245_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v_pos_1251_; lean_object* v___y_1254_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; uint8_t v___y_1266_; lean_object* v___y_1268_; lean_object* v___y_1269_; uint8_t v___y_1270_; uint8_t v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; uint8_t v___y_1274_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; uint8_t v___y_1289_; uint8_t v___y_1290_; uint8_t v___y_1291_; lean_object* v___y_1301_; lean_object* v___y_1302_; uint8_t v___y_1303_; uint8_t v___y_1304_; lean_object* v_pos_1305_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; uint8_t v___y_1311_; uint8_t v___y_1312_; lean_object* v___y_1313_; uint8_t v___y_1314_; lean_object* v_pos_1330_; lean_object* v_res_1331_; lean_object* v_pos_1383_; lean_object* v_res_1384_; lean_object* v_err_1387_; lean_object* v___x_1392_; 
lean_inc_ref(v_a_1240_);
v___x_1392_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(v_config_1239_, v_a_1240_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_pos_1393_; lean_object* v_res_1394_; lean_object* v_array_1395_; lean_object* v_idx_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1412_; 
v_pos_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_pos_1393_);
v_res_1394_ = lean_ctor_get(v___x_1392_, 1);
lean_inc(v_res_1394_);
lean_dec_ref_known(v___x_1392_, 2);
v_array_1395_ = lean_ctor_get(v_pos_1393_, 0);
v_idx_1396_ = lean_ctor_get(v_pos_1393_, 1);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_pos_1393_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1398_ = v_pos_1393_;
v_isShared_1399_ = v_isSharedCheck_1412_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_idx_1396_);
lean_inc(v_array_1395_);
lean_dec(v_pos_1393_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1412_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; uint8_t v___x_1401_; 
v___x_1400_ = lean_byte_array_size(v_array_1395_);
v___x_1401_ = lean_nat_dec_lt(v_idx_1396_, v___x_1400_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; 
lean_del_object(v___x_1398_);
lean_dec(v_idx_1396_);
lean_dec_ref(v_array_1395_);
lean_dec(v_res_1394_);
v___x_1402_ = lean_box(0);
v_err_1387_ = v___x_1402_;
goto v___jp_1386_;
}
else
{
uint8_t v___x_1403_; uint8_t v_got_1404_; uint8_t v___x_1405_; 
v___x_1403_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v_got_1404_ = lean_byte_array_fget(v_array_1395_, v_idx_1396_);
v___x_1405_ = lean_uint8_dec_eq(v_got_1404_, v___x_1403_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; 
lean_del_object(v___x_1398_);
lean_dec(v_idx_1396_);
lean_dec_ref(v_array_1395_);
lean_dec(v_res_1394_);
v___x_1406_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15);
v_err_1387_ = v___x_1406_;
goto v___jp_1386_;
}
else
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
lean_dec_ref(v_a_1240_);
v___x_1407_ = lean_unsigned_to_nat(1u);
v___x_1408_ = lean_nat_add(v_idx_1396_, v___x_1407_);
lean_dec(v_idx_1396_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 1, v___x_1408_);
v___x_1410_ = v___x_1398_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_array_1395_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
v_pos_1383_ = v___x_1410_;
v_res_1384_ = v_res_1394_;
goto v___jp_1382_;
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_pos_1413_; lean_object* v_res_1414_; 
lean_dec_ref(v_a_1240_);
v_pos_1413_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_pos_1413_);
v_res_1414_ = lean_ctor_get(v___x_1392_, 1);
lean_inc(v_res_1414_);
lean_dec_ref_known(v___x_1392_, 2);
v_pos_1383_ = v_pos_1413_;
v_res_1384_ = v_res_1414_;
goto v___jp_1382_;
}
else
{
lean_object* v_err_1415_; 
v_err_1415_ = lean_ctor_get(v___x_1392_, 1);
lean_inc(v_err_1415_);
lean_dec_ref_known(v___x_1392_, 2);
v_err_1387_ = v_err_1415_;
goto v___jp_1386_;
}
}
v___jp_1241_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1246_, 0, v___y_1243_);
lean_ctor_set(v___x_1246_, 1, v___y_1242_);
lean_ctor_set(v___x_1246_, 2, v_port_1244_);
v___x_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___y_1245_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
return v___x_1247_;
}
v___jp_1248_:
{
lean_object* v___x_1252_; 
v___x_1252_ = lean_box(0);
v___y_1242_ = v___y_1249_;
v___y_1243_ = v___y_1250_;
v_port_1244_ = v___x_1252_;
v___y_1245_ = v_pos_1251_;
goto v___jp_1241_;
}
v___jp_1253_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1));
v___x_1256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___y_1254_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
return v___x_1256_;
}
v___jp_1257_:
{
lean_object* v___x_1261_; 
v___x_1261_ = lean_box(1);
v___y_1242_ = v___y_1258_;
v___y_1243_ = v___y_1259_;
v_port_1244_ = v___x_1261_;
v___y_1245_ = v___y_1260_;
goto v___jp_1241_;
}
v___jp_1262_:
{
if (v___y_1266_ == 0)
{
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
v___y_1254_ = v___y_1265_;
goto v___jp_1253_;
}
else
{
v___y_1258_ = v___y_1263_;
v___y_1259_ = v___y_1264_;
v___y_1260_ = v___y_1265_;
goto v___jp_1257_;
}
}
v___jp_1267_:
{
if (v___y_1274_ == 0)
{
if (lean_obj_tag(v___y_1272_) == 0)
{
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
v___y_1254_ = v___y_1273_;
goto v___jp_1253_;
}
else
{
lean_object* v_val_1275_; uint8_t v___x_1276_; uint8_t v___x_1277_; uint8_t v___x_1278_; 
v_val_1275_ = lean_ctor_get(v___y_1272_, 0);
lean_inc(v_val_1275_);
lean_dec_ref_known(v___y_1272_, 1);
v___x_1276_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_1277_ = lean_unbox(v_val_1275_);
v___x_1278_ = lean_uint8_dec_eq(v___x_1277_, v___x_1276_);
if (v___x_1278_ == 0)
{
uint8_t v___x_1279_; uint8_t v___x_1280_; uint8_t v___x_1281_; 
v___x_1279_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_1280_ = lean_unbox(v_val_1275_);
v___x_1281_ = lean_uint8_dec_eq(v___x_1280_, v___x_1279_);
if (v___x_1281_ == 0)
{
uint8_t v___x_1282_; uint8_t v___x_1283_; uint8_t v___x_1284_; 
v___x_1282_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v___x_1283_ = lean_unbox(v_val_1275_);
lean_dec(v_val_1275_);
v___x_1284_ = lean_uint8_dec_eq(v___x_1283_, v___x_1282_);
if (v___x_1284_ == 0)
{
v___y_1263_ = v___y_1268_;
v___y_1264_ = v___y_1269_;
v___y_1265_ = v___y_1273_;
v___y_1266_ = v___x_1284_;
goto v___jp_1262_;
}
else
{
v___y_1263_ = v___y_1268_;
v___y_1264_ = v___y_1269_;
v___y_1265_ = v___y_1273_;
v___y_1266_ = v___y_1271_;
goto v___jp_1262_;
}
}
else
{
lean_dec(v_val_1275_);
v___y_1263_ = v___y_1268_;
v___y_1264_ = v___y_1269_;
v___y_1265_ = v___y_1273_;
v___y_1266_ = v___y_1271_;
goto v___jp_1262_;
}
}
else
{
lean_dec(v_val_1275_);
v___y_1263_ = v___y_1268_;
v___y_1264_ = v___y_1269_;
v___y_1265_ = v___y_1273_;
v___y_1266_ = v___y_1270_;
goto v___jp_1262_;
}
}
}
else
{
lean_dec(v___y_1272_);
v___y_1258_ = v___y_1268_;
v___y_1259_ = v___y_1269_;
v___y_1260_ = v___y_1273_;
goto v___jp_1257_;
}
}
v___jp_1285_:
{
lean_object* v_array_1292_; lean_object* v_idx_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
v_array_1292_ = lean_ctor_get(v___y_1287_, 0);
v_idx_1293_ = lean_ctor_get(v___y_1287_, 1);
v___x_1294_ = lean_byte_array_size(v_array_1292_);
v___x_1295_ = lean_nat_dec_lt(v_idx_1293_, v___x_1294_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; 
v___x_1296_ = lean_box(0);
v___y_1268_ = v___y_1286_;
v___y_1269_ = v___y_1288_;
v___y_1270_ = v___y_1289_;
v___y_1271_ = v___y_1290_;
v___y_1272_ = v___x_1296_;
v___y_1273_ = v___y_1287_;
v___y_1274_ = v___y_1289_;
goto v___jp_1267_;
}
else
{
uint8_t v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1297_ = lean_byte_array_fget(v_array_1292_, v_idx_1293_);
v___x_1298_ = lean_box(v___x_1297_);
v___x_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
v___y_1268_ = v___y_1286_;
v___y_1269_ = v___y_1288_;
v___y_1270_ = v___y_1289_;
v___y_1271_ = v___y_1290_;
v___y_1272_ = v___x_1299_;
v___y_1273_ = v___y_1287_;
v___y_1274_ = v___y_1291_;
goto v___jp_1267_;
}
}
v___jp_1300_:
{
uint8_t v___x_1306_; 
v___x_1306_ = 0;
v___y_1286_ = v___y_1301_;
v___y_1287_ = v_pos_1305_;
v___y_1288_ = v___y_1302_;
v___y_1289_ = v___y_1304_;
v___y_1290_ = v___y_1303_;
v___y_1291_ = v___x_1306_;
goto v___jp_1285_;
}
v___jp_1307_:
{
lean_dec(v___y_1309_);
if (v___y_1314_ == 0)
{
v___y_1301_ = v___y_1308_;
v___y_1302_ = v___y_1310_;
v___y_1303_ = v___y_1312_;
v___y_1304_ = v___y_1311_;
v_pos_1305_ = v___y_1313_;
goto v___jp_1300_;
}
else
{
if (v___y_1311_ == 0)
{
v___y_1286_ = v___y_1308_;
v___y_1287_ = v___y_1313_;
v___y_1288_ = v___y_1310_;
v___y_1289_ = v___y_1311_;
v___y_1290_ = v___y_1312_;
v___y_1291_ = v___y_1311_;
goto v___jp_1285_;
}
else
{
lean_object* v___x_1315_; 
v___x_1315_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___y_1313_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_pos_1316_; lean_object* v_res_1317_; lean_object* v___x_1318_; uint16_t v___x_1319_; 
v_pos_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_pos_1316_);
v_res_1317_ = lean_ctor_get(v___x_1315_, 1);
lean_inc(v_res_1317_);
lean_dec_ref_known(v___x_1315_, 2);
v___x_1318_ = lean_alloc_ctor(2, 0, 2);
v___x_1319_ = lean_unbox(v_res_1317_);
lean_dec(v_res_1317_);
lean_ctor_set_uint16(v___x_1318_, 0, v___x_1319_);
v___y_1242_ = v___y_1308_;
v___y_1243_ = v___y_1310_;
v_port_1244_ = v___x_1318_;
v___y_1245_ = v_pos_1316_;
goto v___jp_1241_;
}
else
{
lean_object* v_pos_1320_; lean_object* v_err_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1308_);
v_pos_1320_ = lean_ctor_get(v___x_1315_, 0);
v_err_1321_ = lean_ctor_get(v___x_1315_, 1);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1315_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_err_1321_);
lean_inc(v_pos_1320_);
lean_dec(v___x_1315_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_pos_1320_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_err_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
}
v___jp_1329_:
{
lean_object* v___x_1332_; 
v___x_1332_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1239_, v_pos_1330_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_pos_1333_; lean_object* v_res_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1372_; 
v_pos_1333_ = lean_ctor_get(v___x_1332_, 0);
v_res_1334_ = lean_ctor_get(v___x_1332_, 1);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1336_ = v___x_1332_;
v_isShared_1337_ = v_isSharedCheck_1372_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_res_1334_);
lean_inc(v_pos_1333_);
lean_dec(v___x_1332_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1372_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v_array_1338_; lean_object* v_idx_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v_array_1338_ = lean_ctor_get(v_pos_1333_, 0);
v_idx_1339_ = lean_ctor_get(v_pos_1333_, 1);
v___x_1340_ = lean_byte_array_size(v_array_1338_);
v___x_1341_ = lean_nat_dec_lt(v_idx_1339_, v___x_1340_);
if (v___x_1341_ == 0)
{
lean_del_object(v___x_1336_);
v___y_1249_ = v_res_1334_;
v___y_1250_ = v_res_1331_;
v_pos_1251_ = v_pos_1333_;
goto v___jp_1248_;
}
else
{
uint8_t v___x_1342_; uint8_t v___x_1343_; uint8_t v___x_1344_; 
v___x_1342_ = lean_byte_array_fget(v_array_1338_, v_idx_1339_);
v___x_1343_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1344_ = lean_uint8_dec_eq(v___x_1342_, v___x_1343_);
if (v___x_1344_ == 0)
{
lean_del_object(v___x_1336_);
v___y_1249_ = v_res_1334_;
v___y_1250_ = v_res_1331_;
v_pos_1251_ = v_pos_1333_;
goto v___jp_1248_;
}
else
{
if (v___x_1344_ == 0)
{
lean_del_object(v___x_1336_);
v___y_1249_ = v_res_1334_;
v___y_1250_ = v_res_1331_;
v_pos_1251_ = v_pos_1333_;
goto v___jp_1248_;
}
else
{
if (v___x_1341_ == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1347_; 
lean_dec(v_res_1334_);
lean_dec(v_res_1331_);
v___x_1345_ = lean_box(0);
if (v_isShared_1337_ == 0)
{
lean_ctor_set_tag(v___x_1336_, 1);
lean_ctor_set(v___x_1336_, 1, v___x_1345_);
v___x_1347_ = v___x_1336_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_pos_1333_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
else
{
if (v___x_1344_ == 0)
{
lean_object* v___x_1349_; lean_object* v___x_1351_; 
lean_dec(v_res_1334_);
lean_dec(v_res_1331_);
v___x_1349_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
if (v_isShared_1337_ == 0)
{
lean_ctor_set_tag(v___x_1336_, 1);
lean_ctor_set(v___x_1336_, 1, v___x_1349_);
v___x_1351_ = v___x_1336_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_pos_1333_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
else
{
lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1369_; 
lean_inc(v_idx_1339_);
lean_inc_ref(v_array_1338_);
lean_del_object(v___x_1336_);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_pos_1333_);
if (v_isSharedCheck_1369_ == 0)
{
lean_object* v_unused_1370_; lean_object* v_unused_1371_; 
v_unused_1370_ = lean_ctor_get(v_pos_1333_, 1);
lean_dec(v_unused_1370_);
v_unused_1371_ = lean_ctor_get(v_pos_1333_, 0);
lean_dec(v_unused_1371_);
v___x_1354_ = v_pos_1333_;
v_isShared_1355_ = v_isSharedCheck_1369_;
goto v_resetjp_1353_;
}
else
{
lean_dec(v_pos_1333_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1369_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1356_ = lean_unsigned_to_nat(1u);
v___x_1357_ = lean_nat_add(v_idx_1339_, v___x_1356_);
lean_dec(v_idx_1339_);
lean_inc(v___x_1357_);
lean_inc_ref(v_array_1338_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 1, v___x_1357_);
v___x_1359_ = v___x_1354_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_array_1338_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
uint8_t v___x_1360_; 
v___x_1360_ = lean_nat_dec_lt(v___x_1357_, v___x_1340_);
if (v___x_1360_ == 0)
{
lean_dec(v___x_1357_);
lean_dec_ref(v_array_1338_);
v___y_1301_ = v_res_1334_;
v___y_1302_ = v_res_1331_;
v___y_1303_ = v___x_1344_;
v___y_1304_ = v___x_1341_;
v_pos_1305_ = v___x_1359_;
goto v___jp_1300_;
}
else
{
uint8_t v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; uint8_t v___x_1365_; 
v___x_1361_ = lean_byte_array_fget(v_array_1338_, v___x_1357_);
lean_dec(v___x_1357_);
lean_dec_ref(v_array_1338_);
v___x_1362_ = lean_box(v___x_1361_);
v___x_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
v___x_1364_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_1365_ = lean_uint8_dec_le(v___x_1364_, v___x_1361_);
if (v___x_1365_ == 0)
{
v___y_1308_ = v_res_1334_;
v___y_1309_ = v___x_1363_;
v___y_1310_ = v_res_1331_;
v___y_1311_ = v___x_1341_;
v___y_1312_ = v___x_1344_;
v___y_1313_ = v___x_1359_;
v___y_1314_ = v___x_1365_;
goto v___jp_1307_;
}
else
{
uint8_t v___x_1366_; uint8_t v___x_1367_; 
v___x_1366_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_1367_ = lean_uint8_dec_le(v___x_1361_, v___x_1366_);
v___y_1308_ = v_res_1334_;
v___y_1309_ = v___x_1363_;
v___y_1310_ = v_res_1331_;
v___y_1311_ = v___x_1341_;
v___y_1312_ = v___x_1344_;
v___y_1313_ = v___x_1359_;
v___y_1314_ = v___x_1367_;
goto v___jp_1307_;
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
lean_object* v_pos_1373_; lean_object* v_err_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_dec(v_res_1331_);
v_pos_1373_ = lean_ctor_get(v___x_1332_, 0);
v_err_1374_ = lean_ctor_get(v___x_1332_, 1);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1332_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_err_1374_);
lean_inc(v_pos_1373_);
lean_dec(v___x_1332_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_pos_1373_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_err_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
v___jp_1382_:
{
lean_object* v___x_1385_; 
v___x_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1385_, 0, v_res_1384_);
v_pos_1330_ = v_pos_1383_;
v_res_1331_ = v___x_1385_;
goto v___jp_1329_;
}
v___jp_1386_:
{
lean_object* v_idx_1388_; uint8_t v___x_1389_; 
v_idx_1388_ = lean_ctor_get(v_a_1240_, 1);
v___x_1389_ = lean_nat_dec_eq(v_idx_1388_, v_idx_1388_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1390_, 0, v_a_1240_);
lean_ctor_set(v___x_1390_, 1, v_err_1387_);
return v___x_1390_;
}
else
{
lean_object* v___x_1391_; 
lean_dec(v_err_1387_);
v___x_1391_ = lean_box(0);
v_pos_1330_ = v_a_1240_;
v_res_1331_ = v___x_1391_;
goto v___jp_1329_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___boxed(lean_object* v_config_1416_, lean_object* v_a_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_1416_, v_a_1417_);
lean_dec_ref(v_config_1416_);
return v_res_1418_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(uint8_t v_c_1419_){
_start:
{
uint8_t v___y_1421_; uint8_t v___y_1425_; uint8_t v___y_1431_; uint8_t v___y_1451_; uint8_t v___y_1457_; uint8_t v___y_1463_; uint8_t v___y_1469_; uint8_t v___y_1475_; uint8_t v___x_1480_; uint8_t v___x_1481_; 
v___x_1480_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_1481_ = lean_uint8_dec_le(v___x_1480_, v_c_1419_);
if (v___x_1481_ == 0)
{
v___y_1475_ = v___x_1481_;
goto v___jp_1474_;
}
else
{
uint8_t v___x_1482_; uint8_t v___x_1483_; 
v___x_1482_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_1483_ = lean_uint8_dec_le(v_c_1419_, v___x_1482_);
v___y_1475_ = v___x_1483_;
goto v___jp_1474_;
}
v___jp_1420_:
{
if (v___y_1421_ == 0)
{
uint8_t v___x_1422_; uint8_t v___x_1423_; 
v___x_1422_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_1423_ = lean_uint8_dec_eq(v_c_1419_, v___x_1422_);
if (v___x_1423_ == 0)
{
return v___y_1421_;
}
else
{
return v___x_1423_;
}
}
else
{
return v___y_1421_;
}
}
v___jp_1424_:
{
if (v___y_1425_ == 0)
{
uint8_t v___x_1426_; uint8_t v___x_1427_; 
v___x_1426_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1427_ = lean_uint8_dec_eq(v_c_1419_, v___x_1426_);
if (v___x_1427_ == 0)
{
uint8_t v___x_1428_; uint8_t v___x_1429_; 
v___x_1428_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1429_ = lean_uint8_dec_eq(v_c_1419_, v___x_1428_);
v___y_1421_ = v___x_1429_;
goto v___jp_1420_;
}
else
{
v___y_1421_ = v___x_1427_;
goto v___jp_1420_;
}
}
else
{
return v___y_1425_;
}
}
v___jp_1430_:
{
if (v___y_1431_ == 0)
{
uint8_t v___x_1432_; uint8_t v___x_1433_; 
v___x_1432_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_1433_ = lean_uint8_dec_eq(v_c_1419_, v___x_1432_);
if (v___x_1433_ == 0)
{
uint8_t v___x_1434_; uint8_t v___x_1435_; 
v___x_1434_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_1435_ = lean_uint8_dec_eq(v_c_1419_, v___x_1434_);
if (v___x_1435_ == 0)
{
uint8_t v___x_1436_; uint8_t v___x_1437_; 
v___x_1436_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_1437_ = lean_uint8_dec_eq(v_c_1419_, v___x_1436_);
if (v___x_1437_ == 0)
{
uint8_t v___x_1438_; uint8_t v___x_1439_; 
v___x_1438_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_1439_ = lean_uint8_dec_eq(v_c_1419_, v___x_1438_);
if (v___x_1439_ == 0)
{
uint8_t v___x_1440_; uint8_t v___x_1441_; 
v___x_1440_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_1441_ = lean_uint8_dec_eq(v_c_1419_, v___x_1440_);
if (v___x_1441_ == 0)
{
uint8_t v___x_1442_; uint8_t v___x_1443_; 
v___x_1442_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_1443_ = lean_uint8_dec_eq(v_c_1419_, v___x_1442_);
if (v___x_1443_ == 0)
{
uint8_t v___x_1444_; uint8_t v___x_1445_; 
v___x_1444_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_1445_ = lean_uint8_dec_eq(v_c_1419_, v___x_1444_);
if (v___x_1445_ == 0)
{
uint8_t v___x_1446_; uint8_t v___x_1447_; 
v___x_1446_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_1447_ = lean_uint8_dec_eq(v_c_1419_, v___x_1446_);
if (v___x_1447_ == 0)
{
uint8_t v___x_1448_; uint8_t v___x_1449_; 
v___x_1448_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_1449_ = lean_uint8_dec_eq(v_c_1419_, v___x_1448_);
v___y_1425_ = v___x_1449_;
goto v___jp_1424_;
}
else
{
v___y_1425_ = v___x_1447_;
goto v___jp_1424_;
}
}
else
{
v___y_1425_ = v___x_1445_;
goto v___jp_1424_;
}
}
else
{
v___y_1425_ = v___x_1443_;
goto v___jp_1424_;
}
}
else
{
v___y_1425_ = v___x_1441_;
goto v___jp_1424_;
}
}
else
{
v___y_1425_ = v___x_1439_;
goto v___jp_1424_;
}
}
else
{
v___y_1425_ = v___x_1437_;
goto v___jp_1424_;
}
}
else
{
v___y_1425_ = v___x_1435_;
goto v___jp_1424_;
}
}
else
{
v___y_1425_ = v___x_1433_;
goto v___jp_1424_;
}
}
else
{
return v___y_1431_;
}
}
v___jp_1450_:
{
if (v___y_1451_ == 0)
{
uint8_t v___x_1452_; uint8_t v___x_1453_; 
v___x_1452_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_1453_ = lean_uint8_dec_eq(v_c_1419_, v___x_1452_);
if (v___x_1453_ == 0)
{
uint8_t v___x_1454_; uint8_t v___x_1455_; 
v___x_1454_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_1455_ = lean_uint8_dec_eq(v_c_1419_, v___x_1454_);
v___y_1431_ = v___x_1455_;
goto v___jp_1430_;
}
else
{
v___y_1431_ = v___x_1453_;
goto v___jp_1430_;
}
}
else
{
return v___y_1451_;
}
}
v___jp_1456_:
{
if (v___y_1457_ == 0)
{
uint8_t v___x_1458_; uint8_t v___x_1459_; 
v___x_1458_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_1459_ = lean_uint8_dec_eq(v_c_1419_, v___x_1458_);
if (v___x_1459_ == 0)
{
uint8_t v___x_1460_; uint8_t v___x_1461_; 
v___x_1460_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_1461_ = lean_uint8_dec_eq(v_c_1419_, v___x_1460_);
v___y_1451_ = v___x_1461_;
goto v___jp_1450_;
}
else
{
v___y_1451_ = v___x_1459_;
goto v___jp_1450_;
}
}
else
{
return v___y_1457_;
}
}
v___jp_1462_:
{
if (v___y_1463_ == 0)
{
uint8_t v___x_1464_; uint8_t v___x_1465_; 
v___x_1464_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_1465_ = lean_uint8_dec_eq(v_c_1419_, v___x_1464_);
if (v___x_1465_ == 0)
{
uint8_t v___x_1466_; uint8_t v___x_1467_; 
v___x_1466_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_1467_ = lean_uint8_dec_eq(v_c_1419_, v___x_1466_);
v___y_1457_ = v___x_1467_;
goto v___jp_1456_;
}
else
{
v___y_1457_ = v___x_1465_;
goto v___jp_1456_;
}
}
else
{
return v___y_1463_;
}
}
v___jp_1468_:
{
if (v___y_1469_ == 0)
{
uint8_t v___x_1470_; uint8_t v___x_1471_; 
v___x_1470_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_1471_ = lean_uint8_dec_le(v___x_1470_, v_c_1419_);
if (v___x_1471_ == 0)
{
v___y_1463_ = v___x_1471_;
goto v___jp_1462_;
}
else
{
uint8_t v___x_1472_; uint8_t v___x_1473_; 
v___x_1472_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_1473_ = lean_uint8_dec_le(v_c_1419_, v___x_1472_);
v___y_1463_ = v___x_1473_;
goto v___jp_1462_;
}
}
else
{
return v___y_1469_;
}
}
v___jp_1474_:
{
if (v___y_1475_ == 0)
{
uint8_t v___x_1476_; uint8_t v___x_1477_; 
v___x_1476_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_1477_ = lean_uint8_dec_le(v___x_1476_, v_c_1419_);
if (v___x_1477_ == 0)
{
v___y_1469_ = v___x_1477_;
goto v___jp_1468_;
}
else
{
uint8_t v___x_1478_; uint8_t v___x_1479_; 
v___x_1478_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_1479_ = lean_uint8_dec_le(v_c_1419_, v___x_1478_);
v___y_1469_ = v___x_1479_;
goto v___jp_1468_;
}
}
else
{
return v___y_1475_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0___boxed(lean_object* v_c_1484_){
_start:
{
uint8_t v_c_boxed_1485_; uint8_t v_res_1486_; lean_object* v_r_1487_; 
v_c_boxed_1485_ = lean_unbox(v_c_1484_);
v_res_1486_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(v_c_boxed_1485_);
v_r_1487_ = lean_box(v_res_1486_);
return v_r_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(lean_object* v_config_1489_, lean_object* v_a_1490_){
_start:
{
lean_object* v_maxSegmentLength_1491_; lean_object* v___f_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v_snd_1495_; lean_object* v_fst_1496_; lean_object* v_fst_1497_; lean_object* v_array_1498_; lean_object* v_idx_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1516_; 
v_maxSegmentLength_1491_ = lean_ctor_get(v_config_1489_, 3);
v___f_1492_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0));
v___x_1493_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1490_);
v___x_1494_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1492_, v_maxSegmentLength_1491_, v___x_1493_, v_a_1490_);
v_snd_1495_ = lean_ctor_get(v___x_1494_, 1);
lean_inc(v_snd_1495_);
v_fst_1496_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_fst_1496_);
lean_dec_ref(v___x_1494_);
v_fst_1497_ = lean_ctor_get(v_snd_1495_, 0);
lean_inc(v_fst_1497_);
lean_dec(v_snd_1495_);
v_array_1498_ = lean_ctor_get(v_a_1490_, 0);
v_idx_1499_ = lean_ctor_get(v_a_1490_, 1);
v_isSharedCheck_1516_ = !lean_is_exclusive(v_a_1490_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1501_ = v_a_1490_;
v_isShared_1502_ = v_isSharedCheck_1516_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_idx_1499_);
lean_inc(v_array_1498_);
lean_dec(v_a_1490_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1516_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v_lower_1504_; lean_object* v_upper_1505_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___y_1513_; uint8_t v___x_1515_; 
v___x_1510_ = lean_nat_add(v_idx_1499_, v_fst_1496_);
lean_dec(v_fst_1496_);
v___x_1511_ = lean_byte_array_size(v_array_1498_);
v___x_1515_ = lean_nat_dec_le(v_idx_1499_, v___x_1493_);
if (v___x_1515_ == 0)
{
v___y_1513_ = v_idx_1499_;
goto v___jp_1512_;
}
else
{
lean_dec(v_idx_1499_);
v___y_1513_ = v___x_1493_;
goto v___jp_1512_;
}
v___jp_1503_:
{
lean_object* v___x_1506_; lean_object* v___x_1508_; 
v___x_1506_ = l_ByteArray_toByteSlice(v_array_1498_, v_lower_1504_, v_upper_1505_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 1, v___x_1506_);
lean_ctor_set(v___x_1501_, 0, v_fst_1497_);
v___x_1508_ = v___x_1501_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_fst_1497_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
v___jp_1512_:
{
uint8_t v___x_1514_; 
v___x_1514_ = lean_nat_dec_le(v___x_1510_, v___x_1511_);
if (v___x_1514_ == 0)
{
lean_dec(v___x_1510_);
v_lower_1504_ = v___y_1513_;
v_upper_1505_ = v___x_1511_;
goto v___jp_1503_;
}
else
{
v_lower_1504_ = v___y_1513_;
v_upper_1505_ = v___x_1510_;
goto v___jp_1503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___boxed(lean_object* v_config_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1517_, v_a_1518_);
lean_dec_ref(v_config_1517_);
return v_res_1519_;
}
}
LEAN_EXPORT uint8_t l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(uint8_t v_c_1520_){
_start:
{
uint8_t v___x_1521_; uint8_t v___x_1522_; 
v___x_1521_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_1522_ = lean_uint8_dec_eq(v_c_1520_, v___x_1521_);
if (v___x_1522_ == 0)
{
uint8_t v___x_1523_; uint8_t v___x_1524_; 
v___x_1523_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v___x_1524_ = lean_uint8_dec_eq(v_c_1520_, v___x_1523_);
return v___x_1524_;
}
else
{
return v___x_1522_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0___boxed(lean_object* v_c_1525_){
_start:
{
uint8_t v_c_boxed_1526_; uint8_t v_res_1527_; lean_object* v_r_1528_; 
v_c_boxed_1526_ = lean_unbox(v_c_1525_);
v_res_1527_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v_c_boxed_1526_);
v_r_1528_ = lean_box(v_res_1527_);
return v_r_1528_;
}
}
LEAN_EXPORT uint8_t l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__1(uint8_t v___y_1529_){
_start:
{
uint8_t v___y_1531_; uint8_t v___y_1537_; uint8_t v___y_1557_; uint8_t v___y_1563_; uint8_t v___y_1569_; uint8_t v___y_1575_; uint8_t v___y_1581_; uint8_t v___x_1586_; uint8_t v___x_1587_; 
v___x_1586_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_1587_ = lean_uint8_dec_le(v___x_1586_, v___y_1529_);
if (v___x_1587_ == 0)
{
v___y_1581_ = v___x_1587_;
goto v___jp_1580_;
}
else
{
uint8_t v___x_1588_; uint8_t v___x_1589_; 
v___x_1588_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_1589_ = lean_uint8_dec_le(v___y_1529_, v___x_1588_);
v___y_1581_ = v___x_1589_;
goto v___jp_1580_;
}
v___jp_1530_:
{
if (v___y_1531_ == 0)
{
uint8_t v___x_1532_; uint8_t v___x_1533_; 
v___x_1532_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1533_ = lean_uint8_dec_eq(v___y_1529_, v___x_1532_);
if (v___x_1533_ == 0)
{
uint8_t v___x_1534_; uint8_t v___x_1535_; 
v___x_1534_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1535_ = lean_uint8_dec_eq(v___y_1529_, v___x_1534_);
return v___x_1535_;
}
else
{
return v___x_1533_;
}
}
else
{
return v___y_1531_;
}
}
v___jp_1536_:
{
if (v___y_1537_ == 0)
{
uint8_t v___x_1538_; uint8_t v___x_1539_; 
v___x_1538_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_1539_ = lean_uint8_dec_eq(v___y_1529_, v___x_1538_);
if (v___x_1539_ == 0)
{
uint8_t v___x_1540_; uint8_t v___x_1541_; 
v___x_1540_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_1541_ = lean_uint8_dec_eq(v___y_1529_, v___x_1540_);
if (v___x_1541_ == 0)
{
uint8_t v___x_1542_; uint8_t v___x_1543_; 
v___x_1542_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_1543_ = lean_uint8_dec_eq(v___y_1529_, v___x_1542_);
if (v___x_1543_ == 0)
{
uint8_t v___x_1544_; uint8_t v___x_1545_; 
v___x_1544_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_1545_ = lean_uint8_dec_eq(v___y_1529_, v___x_1544_);
if (v___x_1545_ == 0)
{
uint8_t v___x_1546_; uint8_t v___x_1547_; 
v___x_1546_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_1547_ = lean_uint8_dec_eq(v___y_1529_, v___x_1546_);
if (v___x_1547_ == 0)
{
uint8_t v___x_1548_; uint8_t v___x_1549_; 
v___x_1548_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_1549_ = lean_uint8_dec_eq(v___y_1529_, v___x_1548_);
if (v___x_1549_ == 0)
{
uint8_t v___x_1550_; uint8_t v___x_1551_; 
v___x_1550_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_1551_ = lean_uint8_dec_eq(v___y_1529_, v___x_1550_);
if (v___x_1551_ == 0)
{
uint8_t v___x_1552_; uint8_t v___x_1553_; 
v___x_1552_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_1553_ = lean_uint8_dec_eq(v___y_1529_, v___x_1552_);
if (v___x_1553_ == 0)
{
uint8_t v___x_1554_; uint8_t v___x_1555_; 
v___x_1554_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_1555_ = lean_uint8_dec_eq(v___y_1529_, v___x_1554_);
v___y_1531_ = v___x_1555_;
goto v___jp_1530_;
}
else
{
v___y_1531_ = v___x_1553_;
goto v___jp_1530_;
}
}
else
{
v___y_1531_ = v___x_1551_;
goto v___jp_1530_;
}
}
else
{
v___y_1531_ = v___x_1549_;
goto v___jp_1530_;
}
}
else
{
v___y_1531_ = v___x_1547_;
goto v___jp_1530_;
}
}
else
{
v___y_1531_ = v___x_1545_;
goto v___jp_1530_;
}
}
else
{
v___y_1531_ = v___x_1543_;
goto v___jp_1530_;
}
}
else
{
v___y_1531_ = v___x_1541_;
goto v___jp_1530_;
}
}
else
{
v___y_1531_ = v___x_1539_;
goto v___jp_1530_;
}
}
else
{
return v___y_1537_;
}
}
v___jp_1556_:
{
if (v___y_1557_ == 0)
{
uint8_t v___x_1558_; uint8_t v___x_1559_; 
v___x_1558_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_1559_ = lean_uint8_dec_eq(v___y_1529_, v___x_1558_);
if (v___x_1559_ == 0)
{
uint8_t v___x_1560_; uint8_t v___x_1561_; 
v___x_1560_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_1561_ = lean_uint8_dec_eq(v___y_1529_, v___x_1560_);
v___y_1537_ = v___x_1561_;
goto v___jp_1536_;
}
else
{
v___y_1537_ = v___x_1559_;
goto v___jp_1536_;
}
}
else
{
return v___y_1557_;
}
}
v___jp_1562_:
{
if (v___y_1563_ == 0)
{
uint8_t v___x_1564_; uint8_t v___x_1565_; 
v___x_1564_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_1565_ = lean_uint8_dec_eq(v___y_1529_, v___x_1564_);
if (v___x_1565_ == 0)
{
uint8_t v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_1567_ = lean_uint8_dec_eq(v___y_1529_, v___x_1566_);
v___y_1557_ = v___x_1567_;
goto v___jp_1556_;
}
else
{
v___y_1557_ = v___x_1565_;
goto v___jp_1556_;
}
}
else
{
return v___y_1563_;
}
}
v___jp_1568_:
{
if (v___y_1569_ == 0)
{
uint8_t v___x_1570_; uint8_t v___x_1571_; 
v___x_1570_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_1571_ = lean_uint8_dec_eq(v___y_1529_, v___x_1570_);
if (v___x_1571_ == 0)
{
uint8_t v___x_1572_; uint8_t v___x_1573_; 
v___x_1572_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_1573_ = lean_uint8_dec_eq(v___y_1529_, v___x_1572_);
v___y_1563_ = v___x_1573_;
goto v___jp_1562_;
}
else
{
v___y_1563_ = v___x_1571_;
goto v___jp_1562_;
}
}
else
{
return v___y_1569_;
}
}
v___jp_1574_:
{
if (v___y_1575_ == 0)
{
uint8_t v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_1577_ = lean_uint8_dec_le(v___x_1576_, v___y_1529_);
if (v___x_1577_ == 0)
{
v___y_1569_ = v___x_1577_;
goto v___jp_1568_;
}
else
{
uint8_t v___x_1578_; uint8_t v___x_1579_; 
v___x_1578_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_1579_ = lean_uint8_dec_le(v___y_1529_, v___x_1578_);
v___y_1569_ = v___x_1579_;
goto v___jp_1568_;
}
}
else
{
return v___y_1575_;
}
}
v___jp_1580_:
{
if (v___y_1581_ == 0)
{
uint8_t v___x_1582_; uint8_t v___x_1583_; 
v___x_1582_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_1583_ = lean_uint8_dec_le(v___x_1582_, v___y_1529_);
if (v___x_1583_ == 0)
{
v___y_1575_ = v___x_1583_;
goto v___jp_1574_;
}
else
{
uint8_t v___x_1584_; uint8_t v___x_1585_; 
v___x_1584_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_1585_ = lean_uint8_dec_le(v___y_1529_, v___x_1584_);
v___y_1575_ = v___x_1585_;
goto v___jp_1574_;
}
}
else
{
return v___y_1581_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__1___boxed(lean_object* v___y_1590_){
_start:
{
uint8_t v___y_20331__boxed_1591_; uint8_t v_res_1592_; lean_object* v_r_1593_; 
v___y_20331__boxed_1591_ = lean_unbox(v___y_1590_);
v_res_1592_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__1(v___y_20331__boxed_1591_);
v_r_1593_ = lean_box(v_res_1592_);
return v_r_1593_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___f_1595_; lean_object* v___x_1596_; 
v___f_1595_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1596_ = l_Std_Http_URI_EncodedString_empty(v___f_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(lean_object* v_config_1604_, lean_object* v_a_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v_array_1619_; lean_object* v_idx_1620_; lean_object* v_fst_1621_; lean_object* v_snd_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1824_; 
v_array_1619_ = lean_ctor_get(v___y_1606_, 0);
v_idx_1620_ = lean_ctor_get(v___y_1606_, 1);
v_fst_1621_ = lean_ctor_get(v_a_1605_, 0);
v_snd_1622_ = lean_ctor_get(v_a_1605_, 1);
v_isSharedCheck_1824_ = !lean_is_exclusive(v_a_1605_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1624_ = v_a_1605_;
v_isShared_1625_ = v_isSharedCheck_1824_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_snd_1622_);
lean_inc(v_fst_1621_);
lean_dec(v_a_1605_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1824_;
goto v_resetjp_1623_;
}
v___jp_1607_:
{
lean_object* v___x_1611_; 
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___y_1609_);
lean_ctor_set(v___x_1611_, 1, v___y_1608_);
v_a_1605_ = v___x_1611_;
v___y_1606_ = v___y_1610_;
goto _start;
}
v___jp_1613_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___y_1615_);
lean_ctor_set(v___x_1617_, 1, v___y_1616_);
v___x_1618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___y_1614_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
return v___x_1618_;
}
v_resetjp_1623_:
{
lean_object* v___x_1626_; uint8_t v___x_1627_; 
v___x_1626_ = lean_byte_array_size(v_array_1619_);
v___x_1627_ = lean_nat_dec_lt(v_idx_1620_, v___x_1626_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1629_; 
lean_dec_ref(v_config_1604_);
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
lean_ctor_set(v___x_1630_, 0, v___y_1606_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
return v___x_1630_;
}
}
else
{
if (v___x_1627_ == 0)
{
lean_object* v___x_1633_; 
lean_dec_ref(v_config_1604_);
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
lean_ctor_set(v___x_1634_, 0, v___y_1606_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
return v___x_1634_;
}
}
else
{
uint8_t v___x_1636_; uint8_t v___x_1637_; 
v___x_1636_ = lean_byte_array_fget(v_array_1619_, v_idx_1620_);
v___x_1637_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1636_);
if (v___x_1637_ == 0)
{
lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; uint8_t v___y_1751_; uint8_t v___y_1755_; uint8_t v___y_1759_; uint8_t v___y_1765_; uint8_t v___y_1785_; uint8_t v___y_1791_; uint8_t v___y_1797_; uint8_t v___y_1803_; uint8_t v___y_1809_; uint8_t v___x_1814_; uint8_t v___x_1815_; 
v___x_1814_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_1815_ = lean_uint8_dec_eq(v___x_1636_, v___x_1814_);
if (v___x_1815_ == 0)
{
uint8_t v___x_1816_; uint8_t v___x_1817_; 
v___x_1816_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_1817_ = lean_uint8_dec_le(v___x_1816_, v___x_1636_);
if (v___x_1817_ == 0)
{
v___y_1809_ = v___x_1817_;
goto v___jp_1808_;
}
else
{
uint8_t v___x_1818_; uint8_t v___x_1819_; 
v___x_1818_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_1819_ = lean_uint8_dec_le(v___x_1636_, v___x_1818_);
v___y_1809_ = v___x_1819_;
goto v___jp_1808_;
}
}
else
{
v___y_1751_ = v___x_1815_;
goto v___jp_1750_;
}
v___jp_1638_:
{
lean_object* v___x_1643_; uint8_t v___x_1644_; 
v___x_1643_ = lean_array_get_size(v___y_1641_);
v___x_1644_ = lean_nat_dec_le(v___y_1640_, v___x_1643_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1648_; 
lean_dec(v___y_1640_);
v___x_1645_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1);
v___x_1646_ = lean_array_push(v___y_1641_, v___x_1645_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 1, v___y_1639_);
lean_ctor_set(v___x_1624_, 0, v___x_1646_);
v___x_1648_ = v___x_1624_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1646_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v___y_1639_);
v___x_1648_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
v_a_1605_ = v___x_1648_;
v___y_1606_ = v___y_1642_;
goto _start;
}
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1639_);
lean_del_object(v___x_1624_);
lean_dec_ref(v_config_1604_);
v___x_1651_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1652_ = l_Nat_reprFast(v___y_1640_);
v___x_1653_ = lean_string_append(v___x_1651_, v___x_1652_);
lean_dec_ref(v___x_1652_);
v___x_1654_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1655_ = lean_string_append(v___x_1653_, v___x_1654_);
v___x_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
v___x_1657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___y_1642_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
return v___x_1657_;
}
}
v___jp_1658_:
{
lean_object* v_maxPathSegments_1659_; lean_object* v_maxTotalPathLength_1660_; lean_object* v___x_1661_; uint8_t v___x_1662_; 
v_maxPathSegments_1659_ = lean_ctor_get(v_config_1604_, 6);
v_maxTotalPathLength_1660_ = lean_ctor_get(v_config_1604_, 7);
v___x_1661_ = lean_array_get_size(v_fst_1621_);
v___x_1662_ = lean_nat_dec_le(v_maxPathSegments_1659_, v___x_1661_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; 
v___x_1663_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1604_, v___y_1606_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_pos_1664_; lean_object* v_res_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1733_; 
v_pos_1664_ = lean_ctor_get(v___x_1663_, 0);
v_res_1665_ = lean_ctor_get(v___x_1663_, 1);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1667_ = v___x_1663_;
v_isShared_1668_ = v_isSharedCheck_1733_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_res_1665_);
lean_inc(v_pos_1664_);
lean_dec(v___x_1663_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1733_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_inc(v_res_1665_);
v___x_1669_ = l_ByteSlice_toByteArray(v_res_1665_);
v___x_1670_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1669_);
if (lean_obj_tag(v___x_1670_) == 1)
{
lean_object* v_val_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1728_; 
v_val_1671_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1673_ = v___x_1670_;
v_isShared_1674_ = v_isSharedCheck_1728_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_val_1671_);
lean_dec(v___x_1670_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1728_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; uint8_t v___x_1677_; 
v___x_1675_ = l_ByteSlice_size(v_res_1665_);
lean_dec(v_res_1665_);
v___x_1676_ = lean_nat_add(v_snd_1622_, v___x_1675_);
lean_dec(v___x_1675_);
lean_dec(v_snd_1622_);
v___x_1677_ = lean_nat_dec_lt(v_maxTotalPathLength_1660_, v___x_1676_);
if (v___x_1677_ == 0)
{
lean_object* v_array_1678_; lean_object* v_idx_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; 
v_array_1678_ = lean_ctor_get(v_pos_1664_, 0);
v_idx_1679_ = lean_ctor_get(v_pos_1664_, 1);
v___x_1680_ = lean_array_push(v_fst_1621_, v_val_1671_);
v___x_1681_ = lean_byte_array_size(v_array_1678_);
v___x_1682_ = lean_nat_dec_lt(v_idx_1679_, v___x_1681_);
if (v___x_1682_ == 0)
{
lean_del_object(v___x_1673_);
lean_del_object(v___x_1667_);
lean_del_object(v___x_1624_);
lean_dec_ref(v_config_1604_);
v___y_1614_ = v_pos_1664_;
v___y_1615_ = v___x_1680_;
v___y_1616_ = v___x_1676_;
goto v___jp_1613_;
}
else
{
uint8_t v___x_1683_; uint8_t v___x_1684_; uint8_t v___x_1685_; 
v___x_1683_ = lean_byte_array_fget(v_array_1678_, v_idx_1679_);
v___x_1684_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_1685_ = lean_uint8_dec_eq(v___x_1683_, v___x_1684_);
if (v___x_1685_ == 0)
{
lean_del_object(v___x_1673_);
lean_del_object(v___x_1667_);
lean_del_object(v___x_1624_);
lean_dec_ref(v_config_1604_);
v___y_1614_ = v_pos_1664_;
v___y_1615_ = v___x_1680_;
v___y_1616_ = v___x_1676_;
goto v___jp_1613_;
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v___x_1686_ = lean_unsigned_to_nat(1u);
v___x_1687_ = lean_nat_add(v___x_1676_, v___x_1686_);
lean_dec(v___x_1676_);
v___x_1688_ = lean_nat_dec_lt(v_maxTotalPathLength_1660_, v___x_1687_);
if (v___x_1688_ == 0)
{
lean_del_object(v___x_1673_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1691_; 
lean_dec(v___x_1687_);
lean_dec_ref(v___x_1680_);
lean_del_object(v___x_1624_);
lean_dec_ref(v_config_1604_);
v___x_1689_ = lean_box(0);
if (v_isShared_1668_ == 0)
{
lean_ctor_set_tag(v___x_1667_, 1);
lean_ctor_set(v___x_1667_, 1, v___x_1689_);
v___x_1691_ = v___x_1667_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_pos_1664_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
else
{
lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1703_; 
lean_inc(v_idx_1679_);
lean_inc_ref(v_array_1678_);
lean_del_object(v___x_1667_);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_pos_1664_);
if (v_isSharedCheck_1703_ == 0)
{
lean_object* v_unused_1704_; lean_object* v_unused_1705_; 
v_unused_1704_ = lean_ctor_get(v_pos_1664_, 1);
lean_dec(v_unused_1704_);
v_unused_1705_ = lean_ctor_get(v_pos_1664_, 0);
lean_dec(v_unused_1705_);
v___x_1694_ = v_pos_1664_;
v_isShared_1695_ = v_isSharedCheck_1703_;
goto v_resetjp_1693_;
}
else
{
lean_dec(v_pos_1664_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1703_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1696_; lean_object* v___x_1698_; 
v___x_1696_ = lean_nat_add(v_idx_1679_, v___x_1686_);
lean_dec(v_idx_1679_);
lean_inc(v___x_1696_);
lean_inc_ref(v_array_1678_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 1, v___x_1696_);
v___x_1698_ = v___x_1694_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_array_1678_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
uint8_t v___x_1699_; 
v___x_1699_ = lean_nat_dec_lt(v___x_1696_, v___x_1681_);
if (v___x_1699_ == 0)
{
lean_dec(v___x_1696_);
lean_dec_ref(v_array_1678_);
if (v___x_1682_ == 0)
{
lean_del_object(v___x_1624_);
v___y_1608_ = v___x_1687_;
v___y_1609_ = v___x_1680_;
v___y_1610_ = v___x_1698_;
goto v___jp_1607_;
}
else
{
lean_inc(v_maxPathSegments_1659_);
v___y_1639_ = v___x_1687_;
v___y_1640_ = v_maxPathSegments_1659_;
v___y_1641_ = v___x_1680_;
v___y_1642_ = v___x_1698_;
goto v___jp_1638_;
}
}
else
{
uint8_t v___x_1700_; uint8_t v___x_1701_; 
v___x_1700_ = lean_byte_array_fget(v_array_1678_, v___x_1696_);
lean_dec(v___x_1696_);
lean_dec_ref(v_array_1678_);
v___x_1701_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1700_);
if (v___x_1701_ == 0)
{
lean_del_object(v___x_1624_);
v___y_1608_ = v___x_1687_;
v___y_1609_ = v___x_1680_;
v___y_1610_ = v___x_1698_;
goto v___jp_1607_;
}
else
{
lean_inc(v_maxPathSegments_1659_);
v___y_1639_ = v___x_1687_;
v___y_1640_ = v_maxPathSegments_1659_;
v___y_1641_ = v___x_1680_;
v___y_1642_ = v___x_1698_;
goto v___jp_1638_;
}
}
}
}
}
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1712_; 
lean_inc(v_maxTotalPathLength_1660_);
lean_dec(v___x_1687_);
lean_dec_ref(v___x_1680_);
lean_del_object(v___x_1624_);
lean_dec_ref(v_config_1604_);
v___x_1706_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4));
v___x_1707_ = l_Nat_reprFast(v_maxTotalPathLength_1660_);
v___x_1708_ = lean_string_append(v___x_1706_, v___x_1707_);
lean_dec_ref(v___x_1707_);
v___x_1709_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5));
v___x_1710_ = lean_string_append(v___x_1708_, v___x_1709_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1710_);
v___x_1712_ = v___x_1673_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
lean_object* v___x_1714_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set_tag(v___x_1667_, 1);
lean_ctor_set(v___x_1667_, 1, v___x_1712_);
v___x_1714_ = v___x_1667_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_pos_1664_);
lean_ctor_set(v_reuseFailAlloc_1715_, 1, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
}
else
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1723_; 
lean_inc(v_maxTotalPathLength_1660_);
lean_dec(v___x_1676_);
lean_dec(v_val_1671_);
lean_del_object(v___x_1624_);
lean_dec(v_fst_1621_);
lean_dec_ref(v_config_1604_);
v___x_1717_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4));
v___x_1718_ = l_Nat_reprFast(v_maxTotalPathLength_1660_);
v___x_1719_ = lean_string_append(v___x_1717_, v___x_1718_);
lean_dec_ref(v___x_1718_);
v___x_1720_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5));
v___x_1721_ = lean_string_append(v___x_1719_, v___x_1720_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1721_);
v___x_1723_ = v___x_1673_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
lean_object* v___x_1725_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set_tag(v___x_1667_, 1);
lean_ctor_set(v___x_1667_, 1, v___x_1723_);
v___x_1725_ = v___x_1667_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_pos_1664_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v___x_1723_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
}
else
{
lean_object* v___x_1729_; lean_object* v___x_1731_; 
lean_dec(v___x_1670_);
lean_dec(v_res_1665_);
lean_del_object(v___x_1624_);
lean_dec(v_snd_1622_);
lean_dec(v_fst_1621_);
lean_dec_ref(v_config_1604_);
v___x_1729_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__7));
if (v_isShared_1668_ == 0)
{
lean_ctor_set_tag(v___x_1667_, 1);
lean_ctor_set(v___x_1667_, 1, v___x_1729_);
v___x_1731_ = v___x_1667_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_pos_1664_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
else
{
lean_object* v_pos_1734_; lean_object* v_err_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_del_object(v___x_1624_);
lean_dec(v_snd_1622_);
lean_dec(v_fst_1621_);
lean_dec_ref(v_config_1604_);
v_pos_1734_ = lean_ctor_get(v___x_1663_, 0);
v_err_1735_ = lean_ctor_get(v___x_1663_, 1);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1663_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_err_1735_);
lean_inc(v_pos_1734_);
lean_dec(v___x_1663_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_pos_1734_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v_err_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
else
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_inc(v_maxPathSegments_1659_);
lean_del_object(v___x_1624_);
lean_dec(v_snd_1622_);
lean_dec(v_fst_1621_);
lean_dec_ref(v_config_1604_);
v___x_1743_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1744_ = l_Nat_reprFast(v_maxPathSegments_1659_);
v___x_1745_ = lean_string_append(v___x_1743_, v___x_1744_);
lean_dec_ref(v___x_1744_);
v___x_1746_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1747_ = lean_string_append(v___x_1745_, v___x_1746_);
v___x_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
v___x_1749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___y_1606_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
return v___x_1749_;
}
}
v___jp_1750_:
{
if (v___y_1751_ == 0)
{
if (v___x_1627_ == 0)
{
goto v___jp_1658_;
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
lean_del_object(v___x_1624_);
lean_dec_ref(v_config_1604_);
v___x_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1752_, 0, v_fst_1621_);
lean_ctor_set(v___x_1752_, 1, v_snd_1622_);
v___x_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___y_1606_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
return v___x_1753_;
}
}
else
{
goto v___jp_1658_;
}
}
v___jp_1754_:
{
if (v___y_1755_ == 0)
{
uint8_t v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_1757_ = lean_uint8_dec_eq(v___x_1636_, v___x_1756_);
if (v___x_1757_ == 0)
{
v___y_1751_ = v___x_1757_;
goto v___jp_1750_;
}
else
{
v___y_1751_ = v___x_1627_;
goto v___jp_1750_;
}
}
else
{
v___y_1751_ = v___x_1627_;
goto v___jp_1750_;
}
}
v___jp_1758_:
{
if (v___y_1759_ == 0)
{
uint8_t v___x_1760_; uint8_t v___x_1761_; 
v___x_1760_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1761_ = lean_uint8_dec_eq(v___x_1636_, v___x_1760_);
if (v___x_1761_ == 0)
{
uint8_t v___x_1762_; uint8_t v___x_1763_; 
v___x_1762_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1763_ = lean_uint8_dec_eq(v___x_1636_, v___x_1762_);
v___y_1755_ = v___x_1763_;
goto v___jp_1754_;
}
else
{
v___y_1755_ = v___x_1761_;
goto v___jp_1754_;
}
}
else
{
v___y_1751_ = v___x_1627_;
goto v___jp_1750_;
}
}
v___jp_1764_:
{
if (v___y_1765_ == 0)
{
uint8_t v___x_1766_; uint8_t v___x_1767_; 
v___x_1766_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_1767_ = lean_uint8_dec_eq(v___x_1636_, v___x_1766_);
if (v___x_1767_ == 0)
{
uint8_t v___x_1768_; uint8_t v___x_1769_; 
v___x_1768_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_1769_ = lean_uint8_dec_eq(v___x_1636_, v___x_1768_);
if (v___x_1769_ == 0)
{
uint8_t v___x_1770_; uint8_t v___x_1771_; 
v___x_1770_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_1771_ = lean_uint8_dec_eq(v___x_1636_, v___x_1770_);
if (v___x_1771_ == 0)
{
uint8_t v___x_1772_; uint8_t v___x_1773_; 
v___x_1772_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_1773_ = lean_uint8_dec_eq(v___x_1636_, v___x_1772_);
if (v___x_1773_ == 0)
{
uint8_t v___x_1774_; uint8_t v___x_1775_; 
v___x_1774_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_1775_ = lean_uint8_dec_eq(v___x_1636_, v___x_1774_);
if (v___x_1775_ == 0)
{
uint8_t v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_1777_ = lean_uint8_dec_eq(v___x_1636_, v___x_1776_);
if (v___x_1777_ == 0)
{
uint8_t v___x_1778_; uint8_t v___x_1779_; 
v___x_1778_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_1779_ = lean_uint8_dec_eq(v___x_1636_, v___x_1778_);
if (v___x_1779_ == 0)
{
uint8_t v___x_1780_; uint8_t v___x_1781_; 
v___x_1780_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_1781_ = lean_uint8_dec_eq(v___x_1636_, v___x_1780_);
if (v___x_1781_ == 0)
{
uint8_t v___x_1782_; uint8_t v___x_1783_; 
v___x_1782_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_1783_ = lean_uint8_dec_eq(v___x_1636_, v___x_1782_);
v___y_1759_ = v___x_1783_;
goto v___jp_1758_;
}
else
{
v___y_1759_ = v___x_1781_;
goto v___jp_1758_;
}
}
else
{
v___y_1759_ = v___x_1779_;
goto v___jp_1758_;
}
}
else
{
v___y_1759_ = v___x_1777_;
goto v___jp_1758_;
}
}
else
{
v___y_1759_ = v___x_1775_;
goto v___jp_1758_;
}
}
else
{
v___y_1759_ = v___x_1773_;
goto v___jp_1758_;
}
}
else
{
v___y_1759_ = v___x_1771_;
goto v___jp_1758_;
}
}
else
{
v___y_1759_ = v___x_1769_;
goto v___jp_1758_;
}
}
else
{
v___y_1759_ = v___x_1767_;
goto v___jp_1758_;
}
}
else
{
v___y_1751_ = v___x_1627_;
goto v___jp_1750_;
}
}
v___jp_1784_:
{
if (v___y_1785_ == 0)
{
uint8_t v___x_1786_; uint8_t v___x_1787_; 
v___x_1786_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_1787_ = lean_uint8_dec_eq(v___x_1636_, v___x_1786_);
if (v___x_1787_ == 0)
{
uint8_t v___x_1788_; uint8_t v___x_1789_; 
v___x_1788_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_1789_ = lean_uint8_dec_eq(v___x_1636_, v___x_1788_);
v___y_1765_ = v___x_1789_;
goto v___jp_1764_;
}
else
{
v___y_1765_ = v___x_1787_;
goto v___jp_1764_;
}
}
else
{
v___y_1751_ = v___x_1627_;
goto v___jp_1750_;
}
}
v___jp_1790_:
{
if (v___y_1791_ == 0)
{
uint8_t v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_1793_ = lean_uint8_dec_eq(v___x_1636_, v___x_1792_);
if (v___x_1793_ == 0)
{
uint8_t v___x_1794_; uint8_t v___x_1795_; 
v___x_1794_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_1795_ = lean_uint8_dec_eq(v___x_1636_, v___x_1794_);
v___y_1785_ = v___x_1795_;
goto v___jp_1784_;
}
else
{
v___y_1785_ = v___x_1793_;
goto v___jp_1784_;
}
}
else
{
v___y_1751_ = v___x_1627_;
goto v___jp_1750_;
}
}
v___jp_1796_:
{
if (v___y_1797_ == 0)
{
uint8_t v___x_1798_; uint8_t v___x_1799_; 
v___x_1798_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_1799_ = lean_uint8_dec_eq(v___x_1636_, v___x_1798_);
if (v___x_1799_ == 0)
{
uint8_t v___x_1800_; uint8_t v___x_1801_; 
v___x_1800_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_1801_ = lean_uint8_dec_eq(v___x_1636_, v___x_1800_);
v___y_1791_ = v___x_1801_;
goto v___jp_1790_;
}
else
{
v___y_1791_ = v___x_1799_;
goto v___jp_1790_;
}
}
else
{
v___y_1751_ = v___x_1627_;
goto v___jp_1750_;
}
}
v___jp_1802_:
{
if (v___y_1803_ == 0)
{
uint8_t v___x_1804_; uint8_t v___x_1805_; 
v___x_1804_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_1805_ = lean_uint8_dec_le(v___x_1804_, v___x_1636_);
if (v___x_1805_ == 0)
{
v___y_1797_ = v___x_1805_;
goto v___jp_1796_;
}
else
{
uint8_t v___x_1806_; uint8_t v___x_1807_; 
v___x_1806_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_1807_ = lean_uint8_dec_le(v___x_1636_, v___x_1806_);
v___y_1797_ = v___x_1807_;
goto v___jp_1796_;
}
}
else
{
v___y_1751_ = v___x_1627_;
goto v___jp_1750_;
}
}
v___jp_1808_:
{
if (v___y_1809_ == 0)
{
uint8_t v___x_1810_; uint8_t v___x_1811_; 
v___x_1810_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_1811_ = lean_uint8_dec_le(v___x_1810_, v___x_1636_);
if (v___x_1811_ == 0)
{
v___y_1803_ = v___x_1811_;
goto v___jp_1802_;
}
else
{
uint8_t v___x_1812_; uint8_t v___x_1813_; 
v___x_1812_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_1813_ = lean_uint8_dec_le(v___x_1636_, v___x_1812_);
v___y_1803_ = v___x_1813_;
goto v___jp_1802_;
}
}
else
{
v___y_1751_ = v___x_1627_;
goto v___jp_1750_;
}
}
}
else
{
lean_object* v___x_1821_; 
lean_dec_ref(v_config_1604_);
if (v_isShared_1625_ == 0)
{
v___x_1821_ = v___x_1624_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_fst_1621_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_snd_1622_);
v___x_1821_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___y_1606_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
return v___x_1822_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(lean_object* v_config_1825_, lean_object* v_a_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v_array_1840_; lean_object* v_idx_1841_; lean_object* v_fst_1842_; lean_object* v_snd_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_2045_; 
v_array_1840_ = lean_ctor_get(v___y_1827_, 0);
v_idx_1841_ = lean_ctor_get(v___y_1827_, 1);
v_fst_1842_ = lean_ctor_get(v_a_1826_, 0);
v_snd_1843_ = lean_ctor_get(v_a_1826_, 1);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_a_1826_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_1845_ = v_a_1826_;
v_isShared_1846_ = v_isSharedCheck_2045_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_snd_1843_);
lean_inc(v_fst_1842_);
lean_dec(v_a_1826_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_2045_;
goto v_resetjp_1844_;
}
v___jp_1828_:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___y_1830_);
lean_ctor_set(v___x_1832_, 1, v___y_1831_);
v___x_1833_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1825_, v___x_1832_, v___y_1829_);
return v___x_1833_;
}
v___jp_1834_:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___y_1836_);
lean_ctor_set(v___x_1838_, 1, v___y_1835_);
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___y_1837_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
return v___x_1839_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; uint8_t v___x_1848_; 
v___x_1847_ = lean_byte_array_size(v_array_1840_);
v___x_1848_ = lean_nat_dec_lt(v_idx_1841_, v___x_1847_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1850_; 
lean_dec_ref(v_config_1825_);
if (v_isShared_1846_ == 0)
{
v___x_1850_ = v___x_1845_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_fst_1842_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v_snd_1843_);
v___x_1850_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v___x_1851_; 
v___x_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___y_1827_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
return v___x_1851_;
}
}
else
{
if (v___x_1848_ == 0)
{
lean_object* v___x_1854_; 
lean_dec_ref(v_config_1825_);
if (v_isShared_1846_ == 0)
{
v___x_1854_ = v___x_1845_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_fst_1842_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_snd_1843_);
v___x_1854_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1855_; 
v___x_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___y_1827_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
return v___x_1855_;
}
}
else
{
uint8_t v___x_1857_; uint8_t v___x_1858_; 
v___x_1857_ = lean_byte_array_fget(v_array_1840_, v_idx_1841_);
v___x_1858_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1857_);
if (v___x_1858_ == 0)
{
lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; uint8_t v___y_1972_; uint8_t v___y_1976_; uint8_t v___y_1980_; uint8_t v___y_1986_; uint8_t v___y_2006_; uint8_t v___y_2012_; uint8_t v___y_2018_; uint8_t v___y_2024_; uint8_t v___y_2030_; uint8_t v___x_2035_; uint8_t v___x_2036_; 
v___x_2035_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2036_ = lean_uint8_dec_eq(v___x_1857_, v___x_2035_);
if (v___x_2036_ == 0)
{
uint8_t v___x_2037_; uint8_t v___x_2038_; 
v___x_2037_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_2038_ = lean_uint8_dec_le(v___x_2037_, v___x_1857_);
if (v___x_2038_ == 0)
{
v___y_2030_ = v___x_2038_;
goto v___jp_2029_;
}
else
{
uint8_t v___x_2039_; uint8_t v___x_2040_; 
v___x_2039_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_2040_ = lean_uint8_dec_le(v___x_1857_, v___x_2039_);
v___y_2030_ = v___x_2040_;
goto v___jp_2029_;
}
}
else
{
v___y_1972_ = v___x_2036_;
goto v___jp_1971_;
}
v___jp_1859_:
{
lean_object* v___x_1864_; uint8_t v___x_1865_; 
v___x_1864_ = lean_array_get_size(v___y_1861_);
v___x_1865_ = lean_nat_dec_le(v___y_1863_, v___x_1864_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1869_; 
lean_dec(v___y_1863_);
v___x_1866_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1);
v___x_1867_ = lean_array_push(v___y_1861_, v___x_1866_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 1, v___y_1862_);
lean_ctor_set(v___x_1845_, 0, v___x_1867_);
v___x_1869_ = v___x_1845_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v___y_1862_);
v___x_1869_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1870_; 
v___x_1870_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1825_, v___x_1869_, v___y_1860_);
return v___x_1870_;
}
}
else
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_del_object(v___x_1845_);
lean_dec_ref(v_config_1825_);
v___x_1872_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1873_ = l_Nat_reprFast(v___y_1863_);
v___x_1874_ = lean_string_append(v___x_1872_, v___x_1873_);
lean_dec_ref(v___x_1873_);
v___x_1875_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1876_ = lean_string_append(v___x_1874_, v___x_1875_);
v___x_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
v___x_1878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___y_1860_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
return v___x_1878_;
}
}
v___jp_1879_:
{
lean_object* v_maxPathSegments_1880_; lean_object* v_maxTotalPathLength_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; 
v_maxPathSegments_1880_ = lean_ctor_get(v_config_1825_, 6);
v_maxTotalPathLength_1881_ = lean_ctor_get(v_config_1825_, 7);
v___x_1882_ = lean_array_get_size(v_fst_1842_);
v___x_1883_ = lean_nat_dec_le(v_maxPathSegments_1880_, v___x_1882_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; 
v___x_1884_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1825_, v___y_1827_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_pos_1885_; lean_object* v_res_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1954_; 
v_pos_1885_ = lean_ctor_get(v___x_1884_, 0);
v_res_1886_ = lean_ctor_get(v___x_1884_, 1);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1888_ = v___x_1884_;
v_isShared_1889_ = v_isSharedCheck_1954_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_res_1886_);
lean_inc(v_pos_1885_);
lean_dec(v___x_1884_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1954_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
lean_inc(v_res_1886_);
v___x_1890_ = l_ByteSlice_toByteArray(v_res_1886_);
v___x_1891_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1890_);
if (lean_obj_tag(v___x_1891_) == 1)
{
lean_object* v_val_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1949_; 
v_val_1892_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1894_ = v___x_1891_;
v_isShared_1895_ = v_isSharedCheck_1949_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_val_1892_);
lean_dec(v___x_1891_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1949_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1896_ = l_ByteSlice_size(v_res_1886_);
lean_dec(v_res_1886_);
v___x_1897_ = lean_nat_add(v_snd_1843_, v___x_1896_);
lean_dec(v___x_1896_);
lean_dec(v_snd_1843_);
v___x_1898_ = lean_nat_dec_lt(v_maxTotalPathLength_1881_, v___x_1897_);
if (v___x_1898_ == 0)
{
lean_object* v_array_1899_; lean_object* v_idx_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; uint8_t v___x_1903_; 
v_array_1899_ = lean_ctor_get(v_pos_1885_, 0);
v_idx_1900_ = lean_ctor_get(v_pos_1885_, 1);
v___x_1901_ = lean_array_push(v_fst_1842_, v_val_1892_);
v___x_1902_ = lean_byte_array_size(v_array_1899_);
v___x_1903_ = lean_nat_dec_lt(v_idx_1900_, v___x_1902_);
if (v___x_1903_ == 0)
{
lean_del_object(v___x_1894_);
lean_del_object(v___x_1888_);
lean_del_object(v___x_1845_);
lean_dec_ref(v_config_1825_);
v___y_1835_ = v___x_1897_;
v___y_1836_ = v___x_1901_;
v___y_1837_ = v_pos_1885_;
goto v___jp_1834_;
}
else
{
uint8_t v___x_1904_; uint8_t v___x_1905_; uint8_t v___x_1906_; 
v___x_1904_ = lean_byte_array_fget(v_array_1899_, v_idx_1900_);
v___x_1905_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_1906_ = lean_uint8_dec_eq(v___x_1904_, v___x_1905_);
if (v___x_1906_ == 0)
{
lean_del_object(v___x_1894_);
lean_del_object(v___x_1888_);
lean_del_object(v___x_1845_);
lean_dec_ref(v_config_1825_);
v___y_1835_ = v___x_1897_;
v___y_1836_ = v___x_1901_;
v___y_1837_ = v_pos_1885_;
goto v___jp_1834_;
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1908_; uint8_t v___x_1909_; 
v___x_1907_ = lean_unsigned_to_nat(1u);
v___x_1908_ = lean_nat_add(v___x_1897_, v___x_1907_);
lean_dec(v___x_1897_);
v___x_1909_ = lean_nat_dec_lt(v_maxTotalPathLength_1881_, v___x_1908_);
if (v___x_1909_ == 0)
{
lean_del_object(v___x_1894_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1910_; lean_object* v___x_1912_; 
lean_dec(v___x_1908_);
lean_dec_ref(v___x_1901_);
lean_del_object(v___x_1845_);
lean_dec_ref(v_config_1825_);
v___x_1910_ = lean_box(0);
if (v_isShared_1889_ == 0)
{
lean_ctor_set_tag(v___x_1888_, 1);
lean_ctor_set(v___x_1888_, 1, v___x_1910_);
v___x_1912_ = v___x_1888_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_pos_1885_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
else
{
lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1924_; 
lean_inc(v_idx_1900_);
lean_inc_ref(v_array_1899_);
lean_del_object(v___x_1888_);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_pos_1885_);
if (v_isSharedCheck_1924_ == 0)
{
lean_object* v_unused_1925_; lean_object* v_unused_1926_; 
v_unused_1925_ = lean_ctor_get(v_pos_1885_, 1);
lean_dec(v_unused_1925_);
v_unused_1926_ = lean_ctor_get(v_pos_1885_, 0);
lean_dec(v_unused_1926_);
v___x_1915_ = v_pos_1885_;
v_isShared_1916_ = v_isSharedCheck_1924_;
goto v_resetjp_1914_;
}
else
{
lean_dec(v_pos_1885_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1924_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1917_; lean_object* v___x_1919_; 
v___x_1917_ = lean_nat_add(v_idx_1900_, v___x_1907_);
lean_dec(v_idx_1900_);
lean_inc(v___x_1917_);
lean_inc_ref(v_array_1899_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 1, v___x_1917_);
v___x_1919_ = v___x_1915_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_array_1899_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v___x_1917_);
v___x_1919_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
uint8_t v___x_1920_; 
v___x_1920_ = lean_nat_dec_lt(v___x_1917_, v___x_1902_);
if (v___x_1920_ == 0)
{
lean_dec(v___x_1917_);
lean_dec_ref(v_array_1899_);
if (v___x_1903_ == 0)
{
lean_del_object(v___x_1845_);
v___y_1829_ = v___x_1919_;
v___y_1830_ = v___x_1901_;
v___y_1831_ = v___x_1908_;
goto v___jp_1828_;
}
else
{
lean_inc(v_maxPathSegments_1880_);
v___y_1860_ = v___x_1919_;
v___y_1861_ = v___x_1901_;
v___y_1862_ = v___x_1908_;
v___y_1863_ = v_maxPathSegments_1880_;
goto v___jp_1859_;
}
}
else
{
uint8_t v___x_1921_; uint8_t v___x_1922_; 
v___x_1921_ = lean_byte_array_fget(v_array_1899_, v___x_1917_);
lean_dec(v___x_1917_);
lean_dec_ref(v_array_1899_);
v___x_1922_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1921_);
if (v___x_1922_ == 0)
{
lean_del_object(v___x_1845_);
v___y_1829_ = v___x_1919_;
v___y_1830_ = v___x_1901_;
v___y_1831_ = v___x_1908_;
goto v___jp_1828_;
}
else
{
lean_inc(v_maxPathSegments_1880_);
v___y_1860_ = v___x_1919_;
v___y_1861_ = v___x_1901_;
v___y_1862_ = v___x_1908_;
v___y_1863_ = v_maxPathSegments_1880_;
goto v___jp_1859_;
}
}
}
}
}
}
else
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1933_; 
lean_inc(v_maxTotalPathLength_1881_);
lean_dec(v___x_1908_);
lean_dec_ref(v___x_1901_);
lean_del_object(v___x_1845_);
lean_dec_ref(v_config_1825_);
v___x_1927_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4));
v___x_1928_ = l_Nat_reprFast(v_maxTotalPathLength_1881_);
v___x_1929_ = lean_string_append(v___x_1927_, v___x_1928_);
lean_dec_ref(v___x_1928_);
v___x_1930_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5));
v___x_1931_ = lean_string_append(v___x_1929_, v___x_1930_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v___x_1931_);
v___x_1933_ = v___x_1894_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1935_; 
if (v_isShared_1889_ == 0)
{
lean_ctor_set_tag(v___x_1888_, 1);
lean_ctor_set(v___x_1888_, 1, v___x_1933_);
v___x_1935_ = v___x_1888_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_pos_1885_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
}
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1944_; 
lean_inc(v_maxTotalPathLength_1881_);
lean_dec(v___x_1897_);
lean_dec(v_val_1892_);
lean_del_object(v___x_1845_);
lean_dec(v_fst_1842_);
lean_dec_ref(v_config_1825_);
v___x_1938_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__4));
v___x_1939_ = l_Nat_reprFast(v_maxTotalPathLength_1881_);
v___x_1940_ = lean_string_append(v___x_1938_, v___x_1939_);
lean_dec_ref(v___x_1939_);
v___x_1941_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5));
v___x_1942_ = lean_string_append(v___x_1940_, v___x_1941_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v___x_1942_);
v___x_1944_ = v___x_1894_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1946_; 
if (v_isShared_1889_ == 0)
{
lean_ctor_set_tag(v___x_1888_, 1);
lean_ctor_set(v___x_1888_, 1, v___x_1944_);
v___x_1946_ = v___x_1888_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_pos_1885_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1952_; 
lean_dec(v___x_1891_);
lean_dec(v_res_1886_);
lean_del_object(v___x_1845_);
lean_dec(v_snd_1843_);
lean_dec(v_fst_1842_);
lean_dec_ref(v_config_1825_);
v___x_1950_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__7));
if (v_isShared_1889_ == 0)
{
lean_ctor_set_tag(v___x_1888_, 1);
lean_ctor_set(v___x_1888_, 1, v___x_1950_);
v___x_1952_ = v___x_1888_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_pos_1885_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v___x_1950_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
else
{
lean_object* v_pos_1955_; lean_object* v_err_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_del_object(v___x_1845_);
lean_dec(v_snd_1843_);
lean_dec(v_fst_1842_);
lean_dec_ref(v_config_1825_);
v_pos_1955_ = lean_ctor_get(v___x_1884_, 0);
v_err_1956_ = lean_ctor_get(v___x_1884_, 1);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1884_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_err_1956_);
lean_inc(v_pos_1955_);
lean_dec(v___x_1884_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_pos_1955_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v_err_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
else
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
lean_inc(v_maxPathSegments_1880_);
lean_del_object(v___x_1845_);
lean_dec(v_snd_1843_);
lean_dec(v_fst_1842_);
lean_dec_ref(v_config_1825_);
v___x_1964_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1965_ = l_Nat_reprFast(v_maxPathSegments_1880_);
v___x_1966_ = lean_string_append(v___x_1964_, v___x_1965_);
lean_dec_ref(v___x_1965_);
v___x_1967_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1968_ = lean_string_append(v___x_1966_, v___x_1967_);
v___x_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
v___x_1970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1970_, 0, v___y_1827_);
lean_ctor_set(v___x_1970_, 1, v___x_1969_);
return v___x_1970_;
}
}
v___jp_1971_:
{
if (v___y_1972_ == 0)
{
if (v___x_1848_ == 0)
{
goto v___jp_1879_;
}
else
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
lean_del_object(v___x_1845_);
lean_dec_ref(v_config_1825_);
v___x_1973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1973_, 0, v_fst_1842_);
lean_ctor_set(v___x_1973_, 1, v_snd_1843_);
v___x_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___y_1827_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
return v___x_1974_;
}
}
else
{
goto v___jp_1879_;
}
}
v___jp_1975_:
{
if (v___y_1976_ == 0)
{
uint8_t v___x_1977_; uint8_t v___x_1978_; 
v___x_1977_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_1978_ = lean_uint8_dec_eq(v___x_1857_, v___x_1977_);
if (v___x_1978_ == 0)
{
v___y_1972_ = v___x_1978_;
goto v___jp_1971_;
}
else
{
v___y_1972_ = v___x_1848_;
goto v___jp_1971_;
}
}
else
{
v___y_1972_ = v___x_1848_;
goto v___jp_1971_;
}
}
v___jp_1979_:
{
if (v___y_1980_ == 0)
{
uint8_t v___x_1981_; uint8_t v___x_1982_; 
v___x_1981_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1982_ = lean_uint8_dec_eq(v___x_1857_, v___x_1981_);
if (v___x_1982_ == 0)
{
uint8_t v___x_1983_; uint8_t v___x_1984_; 
v___x_1983_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1984_ = lean_uint8_dec_eq(v___x_1857_, v___x_1983_);
v___y_1976_ = v___x_1984_;
goto v___jp_1975_;
}
else
{
v___y_1976_ = v___x_1982_;
goto v___jp_1975_;
}
}
else
{
v___y_1972_ = v___x_1848_;
goto v___jp_1971_;
}
}
v___jp_1985_:
{
if (v___y_1986_ == 0)
{
uint8_t v___x_1987_; uint8_t v___x_1988_; 
v___x_1987_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_1988_ = lean_uint8_dec_eq(v___x_1857_, v___x_1987_);
if (v___x_1988_ == 0)
{
uint8_t v___x_1989_; uint8_t v___x_1990_; 
v___x_1989_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_1990_ = lean_uint8_dec_eq(v___x_1857_, v___x_1989_);
if (v___x_1990_ == 0)
{
uint8_t v___x_1991_; uint8_t v___x_1992_; 
v___x_1991_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_1992_ = lean_uint8_dec_eq(v___x_1857_, v___x_1991_);
if (v___x_1992_ == 0)
{
uint8_t v___x_1993_; uint8_t v___x_1994_; 
v___x_1993_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_1994_ = lean_uint8_dec_eq(v___x_1857_, v___x_1993_);
if (v___x_1994_ == 0)
{
uint8_t v___x_1995_; uint8_t v___x_1996_; 
v___x_1995_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_1996_ = lean_uint8_dec_eq(v___x_1857_, v___x_1995_);
if (v___x_1996_ == 0)
{
uint8_t v___x_1997_; uint8_t v___x_1998_; 
v___x_1997_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_1998_ = lean_uint8_dec_eq(v___x_1857_, v___x_1997_);
if (v___x_1998_ == 0)
{
uint8_t v___x_1999_; uint8_t v___x_2000_; 
v___x_1999_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_2000_ = lean_uint8_dec_eq(v___x_1857_, v___x_1999_);
if (v___x_2000_ == 0)
{
uint8_t v___x_2001_; uint8_t v___x_2002_; 
v___x_2001_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_2002_ = lean_uint8_dec_eq(v___x_1857_, v___x_2001_);
if (v___x_2002_ == 0)
{
uint8_t v___x_2003_; uint8_t v___x_2004_; 
v___x_2003_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_2004_ = lean_uint8_dec_eq(v___x_1857_, v___x_2003_);
v___y_1980_ = v___x_2004_;
goto v___jp_1979_;
}
else
{
v___y_1980_ = v___x_2002_;
goto v___jp_1979_;
}
}
else
{
v___y_1980_ = v___x_2000_;
goto v___jp_1979_;
}
}
else
{
v___y_1980_ = v___x_1998_;
goto v___jp_1979_;
}
}
else
{
v___y_1980_ = v___x_1996_;
goto v___jp_1979_;
}
}
else
{
v___y_1980_ = v___x_1994_;
goto v___jp_1979_;
}
}
else
{
v___y_1980_ = v___x_1992_;
goto v___jp_1979_;
}
}
else
{
v___y_1980_ = v___x_1990_;
goto v___jp_1979_;
}
}
else
{
v___y_1980_ = v___x_1988_;
goto v___jp_1979_;
}
}
else
{
v___y_1972_ = v___x_1848_;
goto v___jp_1971_;
}
}
v___jp_2005_:
{
if (v___y_2006_ == 0)
{
uint8_t v___x_2007_; uint8_t v___x_2008_; 
v___x_2007_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_2008_ = lean_uint8_dec_eq(v___x_1857_, v___x_2007_);
if (v___x_2008_ == 0)
{
uint8_t v___x_2009_; uint8_t v___x_2010_; 
v___x_2009_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_2010_ = lean_uint8_dec_eq(v___x_1857_, v___x_2009_);
v___y_1986_ = v___x_2010_;
goto v___jp_1985_;
}
else
{
v___y_1986_ = v___x_2008_;
goto v___jp_1985_;
}
}
else
{
v___y_1972_ = v___x_1848_;
goto v___jp_1971_;
}
}
v___jp_2011_:
{
if (v___y_2012_ == 0)
{
uint8_t v___x_2013_; uint8_t v___x_2014_; 
v___x_2013_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_2014_ = lean_uint8_dec_eq(v___x_1857_, v___x_2013_);
if (v___x_2014_ == 0)
{
uint8_t v___x_2015_; uint8_t v___x_2016_; 
v___x_2015_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_2016_ = lean_uint8_dec_eq(v___x_1857_, v___x_2015_);
v___y_2006_ = v___x_2016_;
goto v___jp_2005_;
}
else
{
v___y_2006_ = v___x_2014_;
goto v___jp_2005_;
}
}
else
{
v___y_1972_ = v___x_1848_;
goto v___jp_1971_;
}
}
v___jp_2017_:
{
if (v___y_2018_ == 0)
{
uint8_t v___x_2019_; uint8_t v___x_2020_; 
v___x_2019_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_2020_ = lean_uint8_dec_eq(v___x_1857_, v___x_2019_);
if (v___x_2020_ == 0)
{
uint8_t v___x_2021_; uint8_t v___x_2022_; 
v___x_2021_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_2022_ = lean_uint8_dec_eq(v___x_1857_, v___x_2021_);
v___y_2012_ = v___x_2022_;
goto v___jp_2011_;
}
else
{
v___y_2012_ = v___x_2020_;
goto v___jp_2011_;
}
}
else
{
v___y_1972_ = v___x_1848_;
goto v___jp_1971_;
}
}
v___jp_2023_:
{
if (v___y_2024_ == 0)
{
uint8_t v___x_2025_; uint8_t v___x_2026_; 
v___x_2025_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_2026_ = lean_uint8_dec_le(v___x_2025_, v___x_1857_);
if (v___x_2026_ == 0)
{
v___y_2018_ = v___x_2026_;
goto v___jp_2017_;
}
else
{
uint8_t v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_2028_ = lean_uint8_dec_le(v___x_1857_, v___x_2027_);
v___y_2018_ = v___x_2028_;
goto v___jp_2017_;
}
}
else
{
v___y_1972_ = v___x_1848_;
goto v___jp_1971_;
}
}
v___jp_2029_:
{
if (v___y_2030_ == 0)
{
uint8_t v___x_2031_; uint8_t v___x_2032_; 
v___x_2031_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_2032_ = lean_uint8_dec_le(v___x_2031_, v___x_1857_);
if (v___x_2032_ == 0)
{
v___y_2024_ = v___x_2032_;
goto v___jp_2023_;
}
else
{
uint8_t v___x_2033_; uint8_t v___x_2034_; 
v___x_2033_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_2034_ = lean_uint8_dec_le(v___x_1857_, v___x_2033_);
v___y_2024_ = v___x_2034_;
goto v___jp_2023_;
}
}
else
{
v___y_1972_ = v___x_1848_;
goto v___jp_1971_;
}
}
}
else
{
lean_object* v___x_2042_; 
lean_dec_ref(v_config_1825_);
if (v_isShared_1846_ == 0)
{
v___x_2042_ = v___x_1845_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_fst_1842_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_snd_1843_);
v___x_2042_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
lean_object* v___x_2043_; 
v___x_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2043_, 0, v___y_1827_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
return v___x_2043_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath(lean_object* v_config_2057_, uint8_t v_forceAbsolute_2058_, uint8_t v_allowEmpty_2059_, lean_object* v_a_2060_){
_start:
{
lean_object* v___y_2062_; lean_object* v___y_2066_; lean_object* v_array_2069_; lean_object* v_idx_2070_; uint8_t v_isAbsolute_2071_; lean_object* v___x_2072_; lean_object* v_segments_2073_; uint8_t v_isAbsolute_2075_; lean_object* v_totalLength_2076_; lean_object* v___y_2077_; lean_object* v___y_2101_; uint8_t v___y_2105_; lean_object* v_pos_2106_; uint8_t v_res_2107_; uint8_t v___y_2109_; lean_object* v_pos_2110_; uint8_t v___y_2116_; lean_object* v___y_2117_; uint8_t v___y_2139_; lean_object* v_pos_2140_; uint8_t v_res_2141_; lean_object* v_pos_2143_; lean_object* v_array_2144_; lean_object* v_idx_2145_; uint8_t v_res_2146_; uint8_t v___y_2151_; lean_object* v___x_2152_; uint8_t v___x_2153_; 
v_array_2069_ = lean_ctor_get(v_a_2060_, 0);
lean_inc_ref(v_array_2069_);
v_idx_2070_ = lean_ctor_get(v_a_2060_, 1);
lean_inc(v_idx_2070_);
v_isAbsolute_2071_ = 0;
v___x_2072_ = lean_unsigned_to_nat(0u);
v_segments_2073_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__4));
v___x_2152_ = lean_byte_array_size(v_array_2069_);
v___x_2153_ = lean_nat_dec_lt(v_idx_2070_, v___x_2152_);
if (v___x_2153_ == 0)
{
v_pos_2143_ = v_a_2060_;
v_array_2144_ = v_array_2069_;
v_idx_2145_ = v_idx_2070_;
v_res_2146_ = v_isAbsolute_2071_;
goto v___jp_2142_;
}
else
{
uint8_t v___x_2154_; uint8_t v___y_2156_; uint8_t v___y_2162_; uint8_t v___y_2168_; uint8_t v___y_2188_; uint8_t v___y_2194_; uint8_t v___y_2200_; uint8_t v___y_2206_; uint8_t v___y_2212_; uint8_t v___x_2217_; uint8_t v___x_2218_; 
v___x_2154_ = lean_byte_array_fget(v_array_2069_, v_idx_2070_);
v___x_2217_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_2218_ = lean_uint8_dec_le(v___x_2217_, v___x_2154_);
if (v___x_2218_ == 0)
{
v___y_2212_ = v___x_2218_;
goto v___jp_2211_;
}
else
{
uint8_t v___x_2219_; uint8_t v___x_2220_; 
v___x_2219_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_2220_ = lean_uint8_dec_le(v___x_2154_, v___x_2219_);
v___y_2212_ = v___x_2220_;
goto v___jp_2211_;
}
v___jp_2155_:
{
if (v___y_2156_ == 0)
{
uint8_t v___x_2157_; uint8_t v___x_2158_; 
v___x_2157_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_2158_ = lean_uint8_dec_eq(v___x_2154_, v___x_2157_);
if (v___x_2158_ == 0)
{
uint8_t v___x_2159_; uint8_t v___x_2160_; 
v___x_2159_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2160_ = lean_uint8_dec_eq(v___x_2154_, v___x_2159_);
v___y_2151_ = v___x_2160_;
goto v___jp_2150_;
}
else
{
v___y_2151_ = v___x_2158_;
goto v___jp_2150_;
}
}
else
{
v___y_2151_ = v___x_2153_;
goto v___jp_2150_;
}
}
v___jp_2161_:
{
if (v___y_2162_ == 0)
{
uint8_t v___x_2163_; uint8_t v___x_2164_; 
v___x_2163_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_2164_ = lean_uint8_dec_eq(v___x_2154_, v___x_2163_);
if (v___x_2164_ == 0)
{
uint8_t v___x_2165_; uint8_t v___x_2166_; 
v___x_2165_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_2166_ = lean_uint8_dec_eq(v___x_2154_, v___x_2165_);
v___y_2156_ = v___x_2166_;
goto v___jp_2155_;
}
else
{
v___y_2156_ = v___x_2164_;
goto v___jp_2155_;
}
}
else
{
v___y_2151_ = v___x_2153_;
goto v___jp_2150_;
}
}
v___jp_2167_:
{
if (v___y_2168_ == 0)
{
uint8_t v___x_2169_; uint8_t v___x_2170_; 
v___x_2169_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_2170_ = lean_uint8_dec_eq(v___x_2154_, v___x_2169_);
if (v___x_2170_ == 0)
{
uint8_t v___x_2171_; uint8_t v___x_2172_; 
v___x_2171_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_2172_ = lean_uint8_dec_eq(v___x_2154_, v___x_2171_);
if (v___x_2172_ == 0)
{
uint8_t v___x_2173_; uint8_t v___x_2174_; 
v___x_2173_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_2174_ = lean_uint8_dec_eq(v___x_2154_, v___x_2173_);
if (v___x_2174_ == 0)
{
uint8_t v___x_2175_; uint8_t v___x_2176_; 
v___x_2175_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_2176_ = lean_uint8_dec_eq(v___x_2154_, v___x_2175_);
if (v___x_2176_ == 0)
{
uint8_t v___x_2177_; uint8_t v___x_2178_; 
v___x_2177_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_2178_ = lean_uint8_dec_eq(v___x_2154_, v___x_2177_);
if (v___x_2178_ == 0)
{
uint8_t v___x_2179_; uint8_t v___x_2180_; 
v___x_2179_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_2180_ = lean_uint8_dec_eq(v___x_2154_, v___x_2179_);
if (v___x_2180_ == 0)
{
uint8_t v___x_2181_; uint8_t v___x_2182_; 
v___x_2181_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_2182_ = lean_uint8_dec_eq(v___x_2154_, v___x_2181_);
if (v___x_2182_ == 0)
{
uint8_t v___x_2183_; uint8_t v___x_2184_; 
v___x_2183_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_2184_ = lean_uint8_dec_eq(v___x_2154_, v___x_2183_);
if (v___x_2184_ == 0)
{
uint8_t v___x_2185_; uint8_t v___x_2186_; 
v___x_2185_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_2186_ = lean_uint8_dec_eq(v___x_2154_, v___x_2185_);
v___y_2162_ = v___x_2186_;
goto v___jp_2161_;
}
else
{
v___y_2162_ = v___x_2184_;
goto v___jp_2161_;
}
}
else
{
v___y_2162_ = v___x_2182_;
goto v___jp_2161_;
}
}
else
{
v___y_2162_ = v___x_2180_;
goto v___jp_2161_;
}
}
else
{
v___y_2162_ = v___x_2178_;
goto v___jp_2161_;
}
}
else
{
v___y_2162_ = v___x_2176_;
goto v___jp_2161_;
}
}
else
{
v___y_2162_ = v___x_2174_;
goto v___jp_2161_;
}
}
else
{
v___y_2162_ = v___x_2172_;
goto v___jp_2161_;
}
}
else
{
v___y_2162_ = v___x_2170_;
goto v___jp_2161_;
}
}
else
{
v___y_2151_ = v___x_2153_;
goto v___jp_2150_;
}
}
v___jp_2187_:
{
if (v___y_2188_ == 0)
{
uint8_t v___x_2189_; uint8_t v___x_2190_; 
v___x_2189_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_2190_ = lean_uint8_dec_eq(v___x_2154_, v___x_2189_);
if (v___x_2190_ == 0)
{
uint8_t v___x_2191_; uint8_t v___x_2192_; 
v___x_2191_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_2192_ = lean_uint8_dec_eq(v___x_2154_, v___x_2191_);
v___y_2168_ = v___x_2192_;
goto v___jp_2167_;
}
else
{
v___y_2168_ = v___x_2190_;
goto v___jp_2167_;
}
}
else
{
v___y_2151_ = v___x_2153_;
goto v___jp_2150_;
}
}
v___jp_2193_:
{
if (v___y_2194_ == 0)
{
uint8_t v___x_2195_; uint8_t v___x_2196_; 
v___x_2195_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_2196_ = lean_uint8_dec_eq(v___x_2154_, v___x_2195_);
if (v___x_2196_ == 0)
{
uint8_t v___x_2197_; uint8_t v___x_2198_; 
v___x_2197_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_2198_ = lean_uint8_dec_eq(v___x_2154_, v___x_2197_);
v___y_2188_ = v___x_2198_;
goto v___jp_2187_;
}
else
{
v___y_2188_ = v___x_2196_;
goto v___jp_2187_;
}
}
else
{
v___y_2151_ = v___x_2153_;
goto v___jp_2150_;
}
}
v___jp_2199_:
{
if (v___y_2200_ == 0)
{
uint8_t v___x_2201_; uint8_t v___x_2202_; 
v___x_2201_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_2202_ = lean_uint8_dec_eq(v___x_2154_, v___x_2201_);
if (v___x_2202_ == 0)
{
uint8_t v___x_2203_; uint8_t v___x_2204_; 
v___x_2203_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_2204_ = lean_uint8_dec_eq(v___x_2154_, v___x_2203_);
v___y_2194_ = v___x_2204_;
goto v___jp_2193_;
}
else
{
v___y_2194_ = v___x_2202_;
goto v___jp_2193_;
}
}
else
{
v___y_2151_ = v___x_2153_;
goto v___jp_2150_;
}
}
v___jp_2205_:
{
if (v___y_2206_ == 0)
{
uint8_t v___x_2207_; uint8_t v___x_2208_; 
v___x_2207_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_2208_ = lean_uint8_dec_le(v___x_2207_, v___x_2154_);
if (v___x_2208_ == 0)
{
v___y_2200_ = v___x_2208_;
goto v___jp_2199_;
}
else
{
uint8_t v___x_2209_; uint8_t v___x_2210_; 
v___x_2209_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_2210_ = lean_uint8_dec_le(v___x_2154_, v___x_2209_);
v___y_2200_ = v___x_2210_;
goto v___jp_2199_;
}
}
else
{
v___y_2151_ = v___x_2153_;
goto v___jp_2150_;
}
}
v___jp_2211_:
{
if (v___y_2212_ == 0)
{
uint8_t v___x_2213_; uint8_t v___x_2214_; 
v___x_2213_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_2214_ = lean_uint8_dec_le(v___x_2213_, v___x_2154_);
if (v___x_2214_ == 0)
{
v___y_2206_ = v___x_2214_;
goto v___jp_2205_;
}
else
{
uint8_t v___x_2215_; uint8_t v___x_2216_; 
v___x_2215_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_2216_ = lean_uint8_dec_le(v___x_2154_, v___x_2215_);
v___y_2206_ = v___x_2216_;
goto v___jp_2205_;
}
}
else
{
v___y_2151_ = v___x_2153_;
goto v___jp_2150_;
}
}
}
v___jp_2061_:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2063_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__1));
v___x_2064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___y_2062_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
return v___x_2064_;
}
v___jp_2065_:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__3));
v___x_2068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___y_2066_);
lean_ctor_set(v___x_2068_, 1, v___x_2067_);
return v___x_2068_;
}
v___jp_2074_:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2078_, 0, v_segments_2073_);
lean_ctor_set(v___x_2078_, 1, v_totalLength_2076_);
v___x_2079_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(v_config_2057_, v___x_2078_, v___y_2077_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_res_2080_; lean_object* v_pos_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2090_; 
v_res_2080_ = lean_ctor_get(v___x_2079_, 1);
v_pos_2081_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2083_ = v___x_2079_;
v_isShared_2084_ = v_isSharedCheck_2090_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_res_2080_);
lean_inc(v_pos_2081_);
lean_dec(v___x_2079_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2090_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v_fst_2085_; lean_object* v___x_2086_; lean_object* v___x_2088_; 
v_fst_2085_ = lean_ctor_get(v_res_2080_, 0);
lean_inc(v_fst_2085_);
lean_dec(v_res_2080_);
v___x_2086_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2086_, 0, v_fst_2085_);
lean_ctor_set_uint8(v___x_2086_, sizeof(void*)*1, v_isAbsolute_2075_);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 1, v___x_2086_);
v___x_2088_ = v___x_2083_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_pos_2081_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
else
{
lean_object* v_pos_2091_; lean_object* v_err_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
v_pos_2091_ = lean_ctor_get(v___x_2079_, 0);
v_err_2092_ = lean_ctor_get(v___x_2079_, 1);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2079_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_err_2092_);
lean_inc(v_pos_2091_);
lean_dec(v___x_2079_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_pos_2091_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_err_2092_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
v___jp_2100_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__5));
v___x_2103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___y_2101_);
lean_ctor_set(v___x_2103_, 1, v___x_2102_);
return v___x_2103_;
}
v___jp_2104_:
{
if (v_allowEmpty_2059_ == 0)
{
v___y_2062_ = v_pos_2106_;
goto v___jp_2061_;
}
else
{
if (v_res_2107_ == 0)
{
if (v___y_2105_ == 0)
{
v___y_2101_ = v_pos_2106_;
goto v___jp_2100_;
}
else
{
v___y_2062_ = v_pos_2106_;
goto v___jp_2061_;
}
}
else
{
v___y_2101_ = v_pos_2106_;
goto v___jp_2100_;
}
}
}
v___jp_2108_:
{
if (v_forceAbsolute_2058_ == 0)
{
v_isAbsolute_2075_ = v_isAbsolute_2071_;
v_totalLength_2076_ = v___x_2072_;
v___y_2077_ = v_pos_2110_;
goto v___jp_2074_;
}
else
{
lean_object* v_array_2111_; lean_object* v_idx_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; 
lean_dec_ref(v_config_2057_);
v_array_2111_ = lean_ctor_get(v_pos_2110_, 0);
v_idx_2112_ = lean_ctor_get(v_pos_2110_, 1);
v___x_2113_ = lean_byte_array_size(v_array_2111_);
v___x_2114_ = lean_nat_dec_lt(v_idx_2112_, v___x_2113_);
if (v___x_2114_ == 0)
{
v___y_2105_ = v___y_2109_;
v_pos_2106_ = v_pos_2110_;
v_res_2107_ = v_forceAbsolute_2058_;
goto v___jp_2104_;
}
else
{
v___y_2105_ = v___y_2109_;
v_pos_2106_ = v_pos_2110_;
v_res_2107_ = v_isAbsolute_2071_;
goto v___jp_2104_;
}
}
}
v___jp_2115_:
{
lean_object* v_array_2118_; lean_object* v_idx_2119_; lean_object* v___x_2120_; uint8_t v___x_2121_; 
v_array_2118_ = lean_ctor_get(v___y_2117_, 0);
v_idx_2119_ = lean_ctor_get(v___y_2117_, 1);
v___x_2120_ = lean_byte_array_size(v_array_2118_);
v___x_2121_ = lean_nat_dec_lt(v_idx_2119_, v___x_2120_);
if (v___x_2121_ == 0)
{
v___y_2109_ = v___y_2116_;
v_pos_2110_ = v___y_2117_;
goto v___jp_2108_;
}
else
{
uint8_t v___x_2122_; uint8_t v___x_2123_; uint8_t v___x_2124_; 
v___x_2122_ = lean_byte_array_fget(v_array_2118_, v_idx_2119_);
v___x_2123_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2124_ = lean_uint8_dec_eq(v___x_2122_, v___x_2123_);
if (v___x_2124_ == 0)
{
v___y_2109_ = v___y_2116_;
v_pos_2110_ = v___y_2117_;
goto v___jp_2108_;
}
else
{
if (v___x_2121_ == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
lean_dec_ref(v_config_2057_);
v___x_2125_ = lean_box(0);
v___x_2126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___y_2117_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
return v___x_2126_;
}
else
{
lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2135_; 
lean_inc(v_idx_2119_);
lean_inc_ref(v_array_2118_);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___y_2117_);
if (v_isSharedCheck_2135_ == 0)
{
lean_object* v_unused_2136_; lean_object* v_unused_2137_; 
v_unused_2136_ = lean_ctor_get(v___y_2117_, 1);
lean_dec(v_unused_2136_);
v_unused_2137_ = lean_ctor_get(v___y_2117_, 0);
lean_dec(v_unused_2137_);
v___x_2128_ = v___y_2117_;
v_isShared_2129_ = v_isSharedCheck_2135_;
goto v_resetjp_2127_;
}
else
{
lean_dec(v___y_2117_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2135_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2133_; 
v___x_2130_ = lean_unsigned_to_nat(1u);
v___x_2131_ = lean_nat_add(v_idx_2119_, v___x_2130_);
lean_dec(v_idx_2119_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 1, v___x_2131_);
v___x_2133_ = v___x_2128_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_array_2118_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
v_isAbsolute_2075_ = v___x_2121_;
v_totalLength_2076_ = v___x_2130_;
v___y_2077_ = v___x_2133_;
goto v___jp_2074_;
}
}
}
}
}
}
v___jp_2138_:
{
if (v_allowEmpty_2059_ == 0)
{
if (v_res_2141_ == 0)
{
if (v___y_2139_ == 0)
{
lean_dec_ref(v_config_2057_);
v___y_2066_ = v_pos_2140_;
goto v___jp_2065_;
}
else
{
v___y_2116_ = v___y_2139_;
v___y_2117_ = v_pos_2140_;
goto v___jp_2115_;
}
}
else
{
lean_dec_ref(v_config_2057_);
v___y_2066_ = v_pos_2140_;
goto v___jp_2065_;
}
}
else
{
v___y_2116_ = v___y_2139_;
v___y_2117_ = v_pos_2140_;
goto v___jp_2115_;
}
}
v___jp_2142_:
{
lean_object* v___x_2147_; uint8_t v___x_2148_; 
v___x_2147_ = lean_byte_array_size(v_array_2144_);
lean_dec_ref(v_array_2144_);
v___x_2148_ = lean_nat_dec_lt(v_idx_2145_, v___x_2147_);
lean_dec(v_idx_2145_);
if (v___x_2148_ == 0)
{
uint8_t v___x_2149_; 
v___x_2149_ = 1;
v___y_2139_ = v_res_2146_;
v_pos_2140_ = v_pos_2143_;
v_res_2141_ = v___x_2149_;
goto v___jp_2138_;
}
else
{
v___y_2139_ = v_res_2146_;
v_pos_2140_ = v_pos_2143_;
v_res_2141_ = v_isAbsolute_2071_;
goto v___jp_2138_;
}
}
v___jp_2150_:
{
if (v___y_2151_ == 0)
{
v_pos_2143_ = v_a_2060_;
v_array_2144_ = v_array_2069_;
v_idx_2145_ = v_idx_2070_;
v_res_2146_ = v_isAbsolute_2071_;
goto v___jp_2142_;
}
else
{
v_pos_2143_ = v_a_2060_;
v_array_2144_ = v_array_2069_;
v_idx_2145_ = v_idx_2070_;
v_res_2146_ = v___y_2151_;
goto v___jp_2142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath___boxed(lean_object* v_config_2221_, lean_object* v_forceAbsolute_2222_, lean_object* v_allowEmpty_2223_, lean_object* v_a_2224_){
_start:
{
uint8_t v_forceAbsolute_boxed_2225_; uint8_t v_allowEmpty_boxed_2226_; lean_object* v_res_2227_; 
v_forceAbsolute_boxed_2225_ = lean_unbox(v_forceAbsolute_2222_);
v_allowEmpty_boxed_2226_ = lean_unbox(v_allowEmpty_2223_);
v_res_2227_ = l_Std_Http_URI_Parser_parsePath(v_config_2221_, v_forceAbsolute_boxed_2225_, v_allowEmpty_boxed_2226_, v_a_2224_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0(lean_object* v_config_2228_, lean_object* v_inst_2229_, lean_object* v_a_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v___x_2232_; 
v___x_2232_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(v_config_2228_, v_a_2230_, v___y_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(lean_object* v_config_2233_, lean_object* v_inst_2234_, lean_object* v_a_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v___x_2237_; 
v___x_2237_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_2233_, v_a_2235_, v___y_2236_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(lean_object* v_s_2238_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0));
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___boxed(lean_object* v_s_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(v_s_2240_);
lean_dec_ref(v_s_2240_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(lean_object* v_s_2242_){
_start:
{
lean_object* v___x_2243_; 
v___x_2243_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0));
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___boxed(lean_object* v_s_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v_s_2244_);
lean_dec_ref(v_s_2244_);
return v_res_2245_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(uint8_t v_c_2246_){
_start:
{
uint8_t v___y_2248_; uint8_t v___y_2252_; uint8_t v___y_2258_; uint8_t v___y_2264_; uint8_t v___y_2284_; uint8_t v___y_2290_; uint8_t v___y_2296_; uint8_t v___y_2302_; uint8_t v___y_2308_; uint8_t v___x_2313_; uint8_t v___x_2314_; 
v___x_2313_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_2314_ = lean_uint8_dec_le(v___x_2313_, v_c_2246_);
if (v___x_2314_ == 0)
{
v___y_2308_ = v___x_2314_;
goto v___jp_2307_;
}
else
{
uint8_t v___x_2315_; uint8_t v___x_2316_; 
v___x_2315_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_2316_ = lean_uint8_dec_le(v_c_2246_, v___x_2315_);
v___y_2308_ = v___x_2316_;
goto v___jp_2307_;
}
v___jp_2247_:
{
if (v___y_2248_ == 0)
{
uint8_t v___x_2249_; uint8_t v___x_2250_; 
v___x_2249_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_2250_ = lean_uint8_dec_eq(v_c_2246_, v___x_2249_);
if (v___x_2250_ == 0)
{
return v___y_2248_;
}
else
{
return v___x_2250_;
}
}
else
{
return v___y_2248_;
}
}
v___jp_2251_:
{
if (v___y_2252_ == 0)
{
uint8_t v___x_2253_; uint8_t v___x_2254_; 
v___x_2253_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2254_ = lean_uint8_dec_eq(v_c_2246_, v___x_2253_);
if (v___x_2254_ == 0)
{
uint8_t v___x_2255_; uint8_t v___x_2256_; 
v___x_2255_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_2256_ = lean_uint8_dec_eq(v_c_2246_, v___x_2255_);
v___y_2248_ = v___x_2256_;
goto v___jp_2247_;
}
else
{
v___y_2248_ = v___x_2254_;
goto v___jp_2247_;
}
}
else
{
return v___y_2252_;
}
}
v___jp_2257_:
{
if (v___y_2258_ == 0)
{
uint8_t v___x_2259_; uint8_t v___x_2260_; 
v___x_2259_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_2260_ = lean_uint8_dec_eq(v_c_2246_, v___x_2259_);
if (v___x_2260_ == 0)
{
uint8_t v___x_2261_; uint8_t v___x_2262_; 
v___x_2261_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_2262_ = lean_uint8_dec_eq(v_c_2246_, v___x_2261_);
v___y_2252_ = v___x_2262_;
goto v___jp_2251_;
}
else
{
v___y_2252_ = v___x_2260_;
goto v___jp_2251_;
}
}
else
{
return v___y_2258_;
}
}
v___jp_2263_:
{
if (v___y_2264_ == 0)
{
uint8_t v___x_2265_; uint8_t v___x_2266_; 
v___x_2265_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_2266_ = lean_uint8_dec_eq(v_c_2246_, v___x_2265_);
if (v___x_2266_ == 0)
{
uint8_t v___x_2267_; uint8_t v___x_2268_; 
v___x_2267_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_2268_ = lean_uint8_dec_eq(v_c_2246_, v___x_2267_);
if (v___x_2268_ == 0)
{
uint8_t v___x_2269_; uint8_t v___x_2270_; 
v___x_2269_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_2270_ = lean_uint8_dec_eq(v_c_2246_, v___x_2269_);
if (v___x_2270_ == 0)
{
uint8_t v___x_2271_; uint8_t v___x_2272_; 
v___x_2271_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_2272_ = lean_uint8_dec_eq(v_c_2246_, v___x_2271_);
if (v___x_2272_ == 0)
{
uint8_t v___x_2273_; uint8_t v___x_2274_; 
v___x_2273_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_2274_ = lean_uint8_dec_eq(v_c_2246_, v___x_2273_);
if (v___x_2274_ == 0)
{
uint8_t v___x_2275_; uint8_t v___x_2276_; 
v___x_2275_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_2276_ = lean_uint8_dec_eq(v_c_2246_, v___x_2275_);
if (v___x_2276_ == 0)
{
uint8_t v___x_2277_; uint8_t v___x_2278_; 
v___x_2277_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_2278_ = lean_uint8_dec_eq(v_c_2246_, v___x_2277_);
if (v___x_2278_ == 0)
{
uint8_t v___x_2279_; uint8_t v___x_2280_; 
v___x_2279_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_2280_ = lean_uint8_dec_eq(v_c_2246_, v___x_2279_);
if (v___x_2280_ == 0)
{
uint8_t v___x_2281_; uint8_t v___x_2282_; 
v___x_2281_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_2282_ = lean_uint8_dec_eq(v_c_2246_, v___x_2281_);
v___y_2258_ = v___x_2282_;
goto v___jp_2257_;
}
else
{
v___y_2258_ = v___x_2280_;
goto v___jp_2257_;
}
}
else
{
v___y_2258_ = v___x_2278_;
goto v___jp_2257_;
}
}
else
{
v___y_2258_ = v___x_2276_;
goto v___jp_2257_;
}
}
else
{
v___y_2258_ = v___x_2274_;
goto v___jp_2257_;
}
}
else
{
v___y_2258_ = v___x_2272_;
goto v___jp_2257_;
}
}
else
{
v___y_2258_ = v___x_2270_;
goto v___jp_2257_;
}
}
else
{
v___y_2258_ = v___x_2268_;
goto v___jp_2257_;
}
}
else
{
v___y_2258_ = v___x_2266_;
goto v___jp_2257_;
}
}
else
{
return v___y_2264_;
}
}
v___jp_2283_:
{
if (v___y_2284_ == 0)
{
uint8_t v___x_2285_; uint8_t v___x_2286_; 
v___x_2285_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_2286_ = lean_uint8_dec_eq(v_c_2246_, v___x_2285_);
if (v___x_2286_ == 0)
{
uint8_t v___x_2287_; uint8_t v___x_2288_; 
v___x_2287_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_2288_ = lean_uint8_dec_eq(v_c_2246_, v___x_2287_);
v___y_2264_ = v___x_2288_;
goto v___jp_2263_;
}
else
{
v___y_2264_ = v___x_2286_;
goto v___jp_2263_;
}
}
else
{
return v___y_2284_;
}
}
v___jp_2289_:
{
if (v___y_2290_ == 0)
{
uint8_t v___x_2291_; uint8_t v___x_2292_; 
v___x_2291_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_2292_ = lean_uint8_dec_eq(v_c_2246_, v___x_2291_);
if (v___x_2292_ == 0)
{
uint8_t v___x_2293_; uint8_t v___x_2294_; 
v___x_2293_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_2294_ = lean_uint8_dec_eq(v_c_2246_, v___x_2293_);
v___y_2284_ = v___x_2294_;
goto v___jp_2283_;
}
else
{
v___y_2284_ = v___x_2292_;
goto v___jp_2283_;
}
}
else
{
return v___y_2290_;
}
}
v___jp_2295_:
{
if (v___y_2296_ == 0)
{
uint8_t v___x_2297_; uint8_t v___x_2298_; 
v___x_2297_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_2298_ = lean_uint8_dec_eq(v_c_2246_, v___x_2297_);
if (v___x_2298_ == 0)
{
uint8_t v___x_2299_; uint8_t v___x_2300_; 
v___x_2299_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_2300_ = lean_uint8_dec_eq(v_c_2246_, v___x_2299_);
v___y_2290_ = v___x_2300_;
goto v___jp_2289_;
}
else
{
v___y_2290_ = v___x_2298_;
goto v___jp_2289_;
}
}
else
{
return v___y_2296_;
}
}
v___jp_2301_:
{
if (v___y_2302_ == 0)
{
uint8_t v___x_2303_; uint8_t v___x_2304_; 
v___x_2303_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_2304_ = lean_uint8_dec_le(v___x_2303_, v_c_2246_);
if (v___x_2304_ == 0)
{
v___y_2296_ = v___x_2304_;
goto v___jp_2295_;
}
else
{
uint8_t v___x_2305_; uint8_t v___x_2306_; 
v___x_2305_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_2306_ = lean_uint8_dec_le(v_c_2246_, v___x_2305_);
v___y_2296_ = v___x_2306_;
goto v___jp_2295_;
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
v___x_2309_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_2310_ = lean_uint8_dec_le(v___x_2309_, v_c_2246_);
if (v___x_2310_ == 0)
{
v___y_2302_ = v___x_2310_;
goto v___jp_2301_;
}
else
{
uint8_t v___x_2311_; uint8_t v___x_2312_; 
v___x_2311_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_2312_ = lean_uint8_dec_le(v_c_2246_, v___x_2311_);
v___y_2302_ = v___x_2312_;
goto v___jp_2301_;
}
}
else
{
return v___y_2308_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed(lean_object* v_c_2317_){
_start:
{
uint8_t v_c_boxed_2318_; uint8_t v_res_2319_; lean_object* v_r_2320_; 
v_c_boxed_2318_ = lean_unbox(v_c_2317_);
v_res_2319_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(v_c_boxed_2318_);
v_r_2320_ = lean_box(v_res_2319_);
return v_r_2320_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(lean_object* v___x_2321_, lean_object* v___x_2322_, lean_object* v_a_2323_, lean_object* v_b_2324_){
_start:
{
lean_object* v_it_2326_; 
if (lean_obj_tag(v_a_2323_) == 0)
{
lean_object* v_currPos_2330_; lean_object* v_searcher_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2357_; 
v_currPos_2330_ = lean_ctor_get(v_a_2323_, 0);
v_searcher_2331_ = lean_ctor_get(v_a_2323_, 1);
v_isSharedCheck_2357_ = !lean_is_exclusive(v_a_2323_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2333_ = v_a_2323_;
v_isShared_2334_ = v_isSharedCheck_2357_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_searcher_2331_);
lean_inc(v_currPos_2330_);
lean_dec(v_a_2323_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2357_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v_str_2335_; lean_object* v_startInclusive_2336_; lean_object* v_endExclusive_2337_; lean_object* v___x_2338_; uint8_t v___x_2339_; 
v_str_2335_ = lean_ctor_get(v___x_2321_, 0);
v_startInclusive_2336_ = lean_ctor_get(v___x_2321_, 1);
v_endExclusive_2337_ = lean_ctor_get(v___x_2321_, 2);
v___x_2338_ = lean_nat_sub(v_endExclusive_2337_, v_startInclusive_2336_);
v___x_2339_ = lean_nat_dec_eq(v_searcher_2331_, v___x_2338_);
lean_dec(v___x_2338_);
if (v___x_2339_ == 0)
{
uint32_t v___x_2340_; lean_object* v___x_2341_; uint32_t v___x_2342_; uint8_t v___x_2343_; 
v___x_2340_ = 38;
v___x_2341_ = lean_nat_add(v_startInclusive_2336_, v_searcher_2331_);
v___x_2342_ = lean_string_utf8_get_fast(v_str_2335_, v___x_2341_);
v___x_2343_ = lean_uint32_dec_eq(v___x_2342_, v___x_2340_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2347_; 
lean_dec(v_searcher_2331_);
v___x_2344_ = lean_string_utf8_next_fast(v_str_2335_, v___x_2341_);
lean_dec(v___x_2341_);
v___x_2345_ = lean_nat_sub(v___x_2344_, v_startInclusive_2336_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 1, v___x_2345_);
v___x_2347_ = v___x_2333_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_currPos_2330_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
v_a_2323_ = v___x_2347_;
goto _start;
}
}
else
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v_nextIt_2354_; 
lean_dec(v_currPos_2330_);
v___x_2350_ = lean_string_utf8_next_fast(v_str_2335_, v___x_2341_);
v___x_2351_ = lean_nat_sub(v___x_2350_, v___x_2341_);
lean_dec(v___x_2341_);
v___x_2352_ = lean_nat_add(v_searcher_2331_, v___x_2351_);
lean_dec(v___x_2351_);
lean_dec(v_searcher_2331_);
lean_inc(v___x_2352_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 1, v___x_2352_);
lean_ctor_set(v___x_2333_, 0, v___x_2352_);
v_nextIt_2354_ = v___x_2333_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2352_);
lean_ctor_set(v_reuseFailAlloc_2355_, 1, v___x_2352_);
v_nextIt_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
v_it_2326_ = v_nextIt_2354_;
goto v___jp_2325_;
}
}
}
else
{
lean_object* v___x_2356_; 
lean_del_object(v___x_2333_);
lean_dec(v_searcher_2331_);
lean_dec(v_currPos_2330_);
v___x_2356_ = lean_box(1);
v_it_2326_ = v___x_2356_;
goto v___jp_2325_;
}
}
}
else
{
return v_b_2324_;
}
v___jp_2325_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = lean_unsigned_to_nat(1u);
v___x_2328_ = lean_nat_add(v_b_2324_, v___x_2327_);
lean_dec(v_b_2324_);
v_a_2323_ = v_it_2326_;
v_b_2324_ = v___x_2328_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg___boxed(lean_object* v___x_2358_, lean_object* v___x_2359_, lean_object* v_a_2360_, lean_object* v_b_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2358_, v___x_2359_, v_a_2360_, v_b_2361_);
lean_dec(v___x_2359_);
lean_dec_ref(v___x_2358_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(lean_object* v___x_2363_, lean_object* v___x_2364_, lean_object* v___x_2365_, lean_object* v_a_2366_, lean_object* v_b_2367_){
_start:
{
lean_object* v_it_2369_; 
if (lean_obj_tag(v_a_2366_) == 0)
{
lean_object* v_currPos_2373_; lean_object* v_searcher_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2400_; 
v_currPos_2373_ = lean_ctor_get(v_a_2366_, 0);
v_searcher_2374_ = lean_ctor_get(v_a_2366_, 1);
v_isSharedCheck_2400_ = !lean_is_exclusive(v_a_2366_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2376_ = v_a_2366_;
v_isShared_2377_ = v_isSharedCheck_2400_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_searcher_2374_);
lean_inc(v_currPos_2373_);
lean_dec(v_a_2366_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2400_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v_str_2378_; lean_object* v_startInclusive_2379_; lean_object* v_endExclusive_2380_; lean_object* v___x_2381_; uint8_t v___x_2382_; 
v_str_2378_ = lean_ctor_get(v___x_2364_, 0);
v_startInclusive_2379_ = lean_ctor_get(v___x_2364_, 1);
v_endExclusive_2380_ = lean_ctor_get(v___x_2364_, 2);
v___x_2381_ = lean_nat_sub(v_endExclusive_2380_, v_startInclusive_2379_);
v___x_2382_ = lean_nat_dec_eq(v_searcher_2374_, v___x_2381_);
lean_dec(v___x_2381_);
if (v___x_2382_ == 0)
{
lean_object* v___x_2383_; uint32_t v___x_2384_; uint32_t v___x_2385_; uint8_t v___x_2386_; 
v___x_2383_ = lean_nat_add(v_startInclusive_2379_, v_searcher_2374_);
v___x_2384_ = lean_string_utf8_get_fast(v_str_2378_, v___x_2383_);
v___x_2385_ = 38;
v___x_2386_ = lean_uint32_dec_eq(v___x_2384_, v___x_2385_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2390_; 
lean_dec(v_searcher_2374_);
v___x_2387_ = lean_string_utf8_next_fast(v_str_2378_, v___x_2383_);
lean_dec(v___x_2383_);
v___x_2388_ = lean_nat_sub(v___x_2387_, v_startInclusive_2379_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 1, v___x_2388_);
v___x_2390_ = v___x_2376_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_currPos_2373_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v___x_2388_);
v___x_2390_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2364_, v___x_2365_, v___x_2390_, v_b_2367_);
return v___x_2391_;
}
}
else
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v_nextIt_2397_; 
lean_dec(v_currPos_2373_);
v___x_2393_ = lean_string_utf8_next_fast(v_str_2378_, v___x_2383_);
v___x_2394_ = lean_nat_sub(v___x_2393_, v___x_2383_);
lean_dec(v___x_2383_);
v___x_2395_ = lean_nat_add(v_searcher_2374_, v___x_2394_);
lean_dec(v___x_2394_);
lean_dec(v_searcher_2374_);
lean_inc(v___x_2395_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 1, v___x_2395_);
lean_ctor_set(v___x_2376_, 0, v___x_2395_);
v_nextIt_2397_ = v___x_2376_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2395_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v___x_2395_);
v_nextIt_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
v_it_2369_ = v_nextIt_2397_;
goto v___jp_2368_;
}
}
}
else
{
lean_object* v___x_2399_; 
lean_del_object(v___x_2376_);
lean_dec(v_searcher_2374_);
lean_dec(v_currPos_2373_);
v___x_2399_ = lean_box(1);
v_it_2369_ = v___x_2399_;
goto v___jp_2368_;
}
}
}
else
{
return v_b_2367_;
}
v___jp_2368_:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2370_ = lean_unsigned_to_nat(1u);
v___x_2371_ = lean_nat_add(v_b_2367_, v___x_2370_);
lean_dec(v_b_2367_);
v___x_2372_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2364_, v___x_2365_, v_it_2369_, v___x_2371_);
return v___x_2372_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg___boxed(lean_object* v___x_2401_, lean_object* v___x_2402_, lean_object* v___x_2403_, lean_object* v_a_2404_, lean_object* v_b_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2401_, v___x_2402_, v___x_2403_, v_a_2404_, v_b_2405_);
lean_dec(v___x_2403_);
lean_dec_ref(v___x_2402_);
lean_dec_ref(v___x_2401_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(lean_object* v_out_2407_, lean_object* v_a_2408_, lean_object* v_b_2409_){
_start:
{
if (lean_obj_tag(v_a_2408_) == 0)
{
lean_object* v_currPos_2410_; lean_object* v_searcher_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2450_; 
v_currPos_2410_ = lean_ctor_get(v_a_2408_, 0);
v_searcher_2411_ = lean_ctor_get(v_a_2408_, 1);
v_isSharedCheck_2450_ = !lean_is_exclusive(v_a_2408_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2413_ = v_a_2408_;
v_isShared_2414_ = v_isSharedCheck_2450_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_searcher_2411_);
lean_inc(v_currPos_2410_);
lean_dec(v_a_2408_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2450_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v_str_2415_; lean_object* v_startInclusive_2416_; lean_object* v_endExclusive_2417_; lean_object* v_it_2419_; lean_object* v_startInclusive_2420_; lean_object* v_endExclusive_2421_; lean_object* v___x_2428_; uint8_t v___x_2429_; 
v_str_2415_ = lean_ctor_get(v_out_2407_, 0);
v_startInclusive_2416_ = lean_ctor_get(v_out_2407_, 1);
v_endExclusive_2417_ = lean_ctor_get(v_out_2407_, 2);
v___x_2428_ = lean_nat_sub(v_endExclusive_2417_, v_startInclusive_2416_);
v___x_2429_ = lean_nat_dec_eq(v_searcher_2411_, v___x_2428_);
if (v___x_2429_ == 0)
{
uint32_t v___x_2430_; lean_object* v___x_2431_; uint32_t v___x_2432_; uint8_t v___x_2433_; 
lean_dec(v___x_2428_);
v___x_2430_ = 61;
v___x_2431_ = lean_nat_add(v_startInclusive_2416_, v_searcher_2411_);
v___x_2432_ = lean_string_utf8_get_fast(v_str_2415_, v___x_2431_);
v___x_2433_ = lean_uint32_dec_eq(v___x_2432_, v___x_2430_);
if (v___x_2433_ == 0)
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2437_; 
lean_dec(v_searcher_2411_);
v___x_2434_ = lean_string_utf8_next_fast(v_str_2415_, v___x_2431_);
lean_dec(v___x_2431_);
v___x_2435_ = lean_nat_sub(v___x_2434_, v_startInclusive_2416_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 1, v___x_2435_);
v___x_2437_ = v___x_2413_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_currPos_2410_);
lean_ctor_set(v_reuseFailAlloc_2439_, 1, v___x_2435_);
v___x_2437_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
v_a_2408_ = v___x_2437_;
goto _start;
}
}
else
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v_slice_2443_; lean_object* v_nextIt_2445_; 
v___x_2440_ = lean_string_utf8_next_fast(v_str_2415_, v___x_2431_);
v___x_2441_ = lean_nat_sub(v___x_2440_, v___x_2431_);
lean_dec(v___x_2431_);
v___x_2442_ = lean_nat_add(v_searcher_2411_, v___x_2441_);
lean_dec(v___x_2441_);
v_slice_2443_ = l_String_Slice_subslice_x21(v_out_2407_, v_currPos_2410_, v_searcher_2411_);
lean_inc(v___x_2442_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 1, v___x_2442_);
lean_ctor_set(v___x_2413_, 0, v___x_2442_);
v_nextIt_2445_ = v___x_2413_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2442_);
lean_ctor_set(v_reuseFailAlloc_2448_, 1, v___x_2442_);
v_nextIt_2445_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
lean_object* v_startInclusive_2446_; lean_object* v_endExclusive_2447_; 
v_startInclusive_2446_ = lean_ctor_get(v_slice_2443_, 0);
lean_inc(v_startInclusive_2446_);
v_endExclusive_2447_ = lean_ctor_get(v_slice_2443_, 1);
lean_inc(v_endExclusive_2447_);
lean_dec_ref(v_slice_2443_);
v_it_2419_ = v_nextIt_2445_;
v_startInclusive_2420_ = v_startInclusive_2446_;
v_endExclusive_2421_ = v_endExclusive_2447_;
goto v___jp_2418_;
}
}
}
else
{
lean_object* v___x_2449_; 
lean_del_object(v___x_2413_);
lean_dec(v_searcher_2411_);
v___x_2449_ = lean_box(1);
v_it_2419_ = v___x_2449_;
v_startInclusive_2420_ = v_currPos_2410_;
v_endExclusive_2421_ = v___x_2428_;
goto v___jp_2418_;
}
v___jp_2418_:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2422_ = lean_nat_add(v_startInclusive_2416_, v_startInclusive_2420_);
lean_dec(v_startInclusive_2420_);
v___x_2423_ = lean_nat_add(v_startInclusive_2416_, v_endExclusive_2421_);
lean_dec(v_endExclusive_2421_);
lean_inc_ref(v_str_2415_);
v___x_2424_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2424_, 0, v_str_2415_);
lean_ctor_set(v___x_2424_, 1, v___x_2422_);
lean_ctor_set(v___x_2424_, 2, v___x_2423_);
v___x_2425_ = l_String_Slice_toString(v___x_2424_);
lean_dec_ref_known(v___x_2424_, 3);
v___x_2426_ = lean_array_push(v_b_2409_, v___x_2425_);
v_a_2408_ = v_it_2419_;
v_b_2409_ = v___x_2426_;
goto _start;
}
}
}
else
{
return v_b_2409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg___boxed(lean_object* v_out_2451_, lean_object* v_a_2452_, lean_object* v_b_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2451_, v_a_2452_, v_b_2453_);
lean_dec_ref(v_out_2451_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(lean_object* v___x_2458_, lean_object* v___x_2459_, lean_object* v___x_2460_, lean_object* v_a_2461_, lean_object* v_b_2462_){
_start:
{
lean_object* v_it_2464_; lean_object* v_startInclusive_2465_; lean_object* v_endExclusive_2466_; 
if (lean_obj_tag(v_a_2461_) == 0)
{
lean_object* v_currPos_2491_; lean_object* v_searcher_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2521_; 
v_currPos_2491_ = lean_ctor_get(v_a_2461_, 0);
v_searcher_2492_ = lean_ctor_get(v_a_2461_, 1);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_a_2461_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2494_ = v_a_2461_;
v_isShared_2495_ = v_isSharedCheck_2521_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_searcher_2492_);
lean_inc(v_currPos_2491_);
lean_dec(v_a_2461_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2521_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v_str_2496_; lean_object* v_startInclusive_2497_; lean_object* v_endExclusive_2498_; lean_object* v___x_2499_; uint8_t v___x_2500_; 
v_str_2496_ = lean_ctor_get(v___x_2459_, 0);
v_startInclusive_2497_ = lean_ctor_get(v___x_2459_, 1);
v_endExclusive_2498_ = lean_ctor_get(v___x_2459_, 2);
v___x_2499_ = lean_nat_sub(v_endExclusive_2498_, v_startInclusive_2497_);
v___x_2500_ = lean_nat_dec_eq(v_searcher_2492_, v___x_2499_);
lean_dec(v___x_2499_);
if (v___x_2500_ == 0)
{
uint32_t v___x_2501_; lean_object* v___x_2502_; uint32_t v___x_2503_; uint8_t v___x_2504_; 
v___x_2501_ = 38;
v___x_2502_ = lean_nat_add(v_startInclusive_2497_, v_searcher_2492_);
v___x_2503_ = lean_string_utf8_get_fast(v_str_2496_, v___x_2502_);
v___x_2504_ = lean_uint32_dec_eq(v___x_2503_, v___x_2501_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2508_; 
lean_dec(v_searcher_2492_);
v___x_2505_ = lean_string_utf8_next_fast(v_str_2496_, v___x_2502_);
lean_dec(v___x_2502_);
v___x_2506_ = lean_nat_sub(v___x_2505_, v_startInclusive_2497_);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 1, v___x_2506_);
v___x_2508_ = v___x_2494_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_currPos_2491_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v___x_2506_);
v___x_2508_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
v_a_2461_ = v___x_2508_;
goto _start;
}
}
else
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v_slice_2514_; lean_object* v_nextIt_2516_; 
v___x_2511_ = lean_string_utf8_next_fast(v_str_2496_, v___x_2502_);
v___x_2512_ = lean_nat_sub(v___x_2511_, v___x_2502_);
lean_dec(v___x_2502_);
v___x_2513_ = lean_nat_add(v_searcher_2492_, v___x_2512_);
lean_dec(v___x_2512_);
v_slice_2514_ = l_String_Slice_subslice_x21(v___x_2459_, v_currPos_2491_, v_searcher_2492_);
lean_inc(v___x_2513_);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 1, v___x_2513_);
lean_ctor_set(v___x_2494_, 0, v___x_2513_);
v_nextIt_2516_ = v___x_2494_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2513_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v___x_2513_);
v_nextIt_2516_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v_startInclusive_2517_; lean_object* v_endExclusive_2518_; 
v_startInclusive_2517_ = lean_ctor_get(v_slice_2514_, 0);
lean_inc(v_startInclusive_2517_);
v_endExclusive_2518_ = lean_ctor_get(v_slice_2514_, 1);
lean_inc(v_endExclusive_2518_);
lean_dec_ref(v_slice_2514_);
v_it_2464_ = v_nextIt_2516_;
v_startInclusive_2465_ = v_startInclusive_2517_;
v_endExclusive_2466_ = v_endExclusive_2518_;
goto v___jp_2463_;
}
}
}
else
{
lean_object* v___x_2520_; 
lean_del_object(v___x_2494_);
lean_dec(v_searcher_2492_);
v___x_2520_ = lean_box(1);
lean_inc(v___x_2460_);
v_it_2464_ = v___x_2520_;
v_startInclusive_2465_ = v_currPos_2491_;
v_endExclusive_2466_ = v___x_2460_;
goto v___jp_2463_;
}
}
}
else
{
lean_object* v___x_2522_; 
lean_dec(v___x_2460_);
lean_dec_ref(v___x_2458_);
v___x_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2522_, 0, v_b_2462_);
return v___x_2522_;
}
v___jp_2463_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
lean_inc_ref(v___x_2458_);
v___x_2467_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2458_);
lean_ctor_set(v___x_2467_, 1, v_startInclusive_2465_);
lean_ctor_set(v___x_2467_, 2, v_endExclusive_2466_);
v___x_2468_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v___x_2467_);
v___x_2469_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2470_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2467_, v___x_2468_, v___x_2469_);
lean_dec_ref_known(v___x_2467_, 3);
v___x_2471_ = lean_array_to_list(v___x_2470_);
if (lean_obj_tag(v___x_2471_) == 0)
{
v_a_2461_ = v_it_2464_;
goto _start;
}
else
{
lean_object* v_tail_2473_; 
v_tail_2473_ = lean_ctor_get(v___x_2471_, 1);
lean_inc(v_tail_2473_);
if (lean_obj_tag(v_tail_2473_) == 0)
{
lean_object* v_head_2474_; lean_object* v___x_2475_; 
v_head_2474_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_head_2474_);
lean_dec_ref_known(v___x_2471_, 2);
v___x_2475_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2474_);
lean_dec(v_head_2474_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v___x_2476_; 
lean_dec(v_it_2464_);
lean_dec_ref(v_b_2462_);
lean_dec(v___x_2460_);
lean_dec_ref(v___x_2458_);
v___x_2476_ = lean_box(0);
return v___x_2476_;
}
else
{
lean_object* v_val_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v_val_2477_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_val_2477_);
lean_dec_ref_known(v___x_2475_, 1);
v___x_2478_ = lean_box(0);
v___x_2479_ = l_Std_Http_URI_Query_insertEncoded(v_b_2462_, v_val_2477_, v___x_2478_);
v_a_2461_ = v_it_2464_;
v_b_2462_ = v___x_2479_;
goto _start;
}
}
else
{
lean_object* v_head_2481_; lean_object* v___x_2482_; 
v_head_2481_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_head_2481_);
lean_dec_ref_known(v___x_2471_, 2);
v___x_2482_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2481_);
lean_dec(v_head_2481_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v___x_2483_; 
lean_dec(v_tail_2473_);
lean_dec(v_it_2464_);
lean_dec_ref(v_b_2462_);
lean_dec(v___x_2460_);
lean_dec_ref(v___x_2458_);
v___x_2483_ = lean_box(0);
return v___x_2483_;
}
else
{
lean_object* v_val_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v_val_2484_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_val_2484_);
lean_dec_ref_known(v___x_2482_, 1);
v___x_2485_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2486_ = l_String_intercalate(v___x_2485_, v_tail_2473_);
v___x_2487_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2486_);
lean_dec_ref(v___x_2486_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v___x_2488_; 
lean_dec(v_val_2484_);
lean_dec(v_it_2464_);
lean_dec_ref(v_b_2462_);
lean_dec(v___x_2460_);
lean_dec_ref(v___x_2458_);
v___x_2488_ = lean_box(0);
return v___x_2488_;
}
else
{
lean_object* v___x_2489_; 
v___x_2489_ = l_Std_Http_URI_Query_insertEncoded(v_b_2462_, v_val_2484_, v___x_2487_);
v_a_2461_ = v_it_2464_;
v_b_2462_ = v___x_2489_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___boxed(lean_object* v___x_2523_, lean_object* v___x_2524_, lean_object* v___x_2525_, lean_object* v_a_2526_, lean_object* v_b_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2523_, v___x_2524_, v___x_2525_, v_a_2526_, v_b_2527_);
lean_dec_ref(v___x_2524_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(lean_object* v___x_2529_, lean_object* v___x_2530_, lean_object* v___x_2531_, lean_object* v_a_2532_, lean_object* v_b_2533_){
_start:
{
lean_object* v_it_2535_; lean_object* v_startInclusive_2536_; lean_object* v_endExclusive_2537_; 
if (lean_obj_tag(v_a_2532_) == 0)
{
lean_object* v_currPos_2562_; lean_object* v_searcher_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2592_; 
v_currPos_2562_ = lean_ctor_get(v_a_2532_, 0);
v_searcher_2563_ = lean_ctor_get(v_a_2532_, 1);
v_isSharedCheck_2592_ = !lean_is_exclusive(v_a_2532_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2565_ = v_a_2532_;
v_isShared_2566_ = v_isSharedCheck_2592_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_searcher_2563_);
lean_inc(v_currPos_2562_);
lean_dec(v_a_2532_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2592_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v_str_2567_; lean_object* v_startInclusive_2568_; lean_object* v_endExclusive_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v_str_2567_ = lean_ctor_get(v___x_2530_, 0);
v_startInclusive_2568_ = lean_ctor_get(v___x_2530_, 1);
v_endExclusive_2569_ = lean_ctor_get(v___x_2530_, 2);
v___x_2570_ = lean_nat_sub(v_endExclusive_2569_, v_startInclusive_2568_);
v___x_2571_ = lean_nat_dec_eq(v_searcher_2563_, v___x_2570_);
lean_dec(v___x_2570_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; uint32_t v___x_2573_; uint32_t v___x_2574_; uint8_t v___x_2575_; 
v___x_2572_ = lean_nat_add(v_startInclusive_2568_, v_searcher_2563_);
v___x_2573_ = lean_string_utf8_get_fast(v_str_2567_, v___x_2572_);
v___x_2574_ = 38;
v___x_2575_ = lean_uint32_dec_eq(v___x_2573_, v___x_2574_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2579_; 
lean_dec(v_searcher_2563_);
v___x_2576_ = lean_string_utf8_next_fast(v_str_2567_, v___x_2572_);
lean_dec(v___x_2572_);
v___x_2577_ = lean_nat_sub(v___x_2576_, v_startInclusive_2568_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 1, v___x_2577_);
v___x_2579_ = v___x_2565_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_currPos_2562_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2529_, v___x_2530_, v___x_2531_, v___x_2579_, v_b_2533_);
return v___x_2580_;
}
}
else
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v_slice_2585_; lean_object* v_nextIt_2587_; 
v___x_2582_ = lean_string_utf8_next_fast(v_str_2567_, v___x_2572_);
v___x_2583_ = lean_nat_sub(v___x_2582_, v___x_2572_);
lean_dec(v___x_2572_);
v___x_2584_ = lean_nat_add(v_searcher_2563_, v___x_2583_);
lean_dec(v___x_2583_);
v_slice_2585_ = l_String_Slice_subslice_x21(v___x_2530_, v_currPos_2562_, v_searcher_2563_);
lean_inc(v___x_2584_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 1, v___x_2584_);
lean_ctor_set(v___x_2565_, 0, v___x_2584_);
v_nextIt_2587_ = v___x_2565_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2584_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v___x_2584_);
v_nextIt_2587_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
lean_object* v_startInclusive_2588_; lean_object* v_endExclusive_2589_; 
v_startInclusive_2588_ = lean_ctor_get(v_slice_2585_, 0);
lean_inc(v_startInclusive_2588_);
v_endExclusive_2589_ = lean_ctor_get(v_slice_2585_, 1);
lean_inc(v_endExclusive_2589_);
lean_dec_ref(v_slice_2585_);
v_it_2535_ = v_nextIt_2587_;
v_startInclusive_2536_ = v_startInclusive_2588_;
v_endExclusive_2537_ = v_endExclusive_2589_;
goto v___jp_2534_;
}
}
}
else
{
lean_object* v___x_2591_; 
lean_del_object(v___x_2565_);
lean_dec(v_searcher_2563_);
v___x_2591_ = lean_box(1);
lean_inc(v___x_2531_);
v_it_2535_ = v___x_2591_;
v_startInclusive_2536_ = v_currPos_2562_;
v_endExclusive_2537_ = v___x_2531_;
goto v___jp_2534_;
}
}
}
else
{
lean_object* v___x_2593_; 
lean_dec(v___x_2531_);
lean_dec_ref(v___x_2529_);
v___x_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2593_, 0, v_b_2533_);
return v___x_2593_;
}
v___jp_2534_:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_inc_ref(v___x_2529_);
v___x_2538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2529_);
lean_ctor_set(v___x_2538_, 1, v_startInclusive_2536_);
lean_ctor_set(v___x_2538_, 2, v_endExclusive_2537_);
v___x_2539_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v___x_2538_);
v___x_2540_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2541_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2538_, v___x_2539_, v___x_2540_);
lean_dec_ref_known(v___x_2538_, 3);
v___x_2542_ = lean_array_to_list(v___x_2541_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v___x_2543_; 
v___x_2543_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2529_, v___x_2530_, v___x_2531_, v_it_2535_, v_b_2533_);
return v___x_2543_;
}
else
{
lean_object* v_tail_2544_; 
v_tail_2544_ = lean_ctor_get(v___x_2542_, 1);
lean_inc(v_tail_2544_);
if (lean_obj_tag(v_tail_2544_) == 0)
{
lean_object* v_head_2545_; lean_object* v___x_2546_; 
v_head_2545_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_head_2545_);
lean_dec_ref_known(v___x_2542_, 2);
v___x_2546_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2545_);
lean_dec(v_head_2545_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v___x_2547_; 
lean_dec(v_it_2535_);
lean_dec_ref(v_b_2533_);
lean_dec(v___x_2531_);
lean_dec_ref(v___x_2529_);
v___x_2547_ = lean_box(0);
return v___x_2547_;
}
else
{
lean_object* v_val_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v_val_2548_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_val_2548_);
lean_dec_ref_known(v___x_2546_, 1);
v___x_2549_ = lean_box(0);
v___x_2550_ = l_Std_Http_URI_Query_insertEncoded(v_b_2533_, v_val_2548_, v___x_2549_);
v___x_2551_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2529_, v___x_2530_, v___x_2531_, v_it_2535_, v___x_2550_);
return v___x_2551_;
}
}
else
{
lean_object* v_head_2552_; lean_object* v___x_2553_; 
v_head_2552_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_head_2552_);
lean_dec_ref_known(v___x_2542_, 2);
v___x_2553_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2552_);
lean_dec(v_head_2552_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v___x_2554_; 
lean_dec(v_tail_2544_);
lean_dec(v_it_2535_);
lean_dec_ref(v_b_2533_);
lean_dec(v___x_2531_);
lean_dec_ref(v___x_2529_);
v___x_2554_ = lean_box(0);
return v___x_2554_;
}
else
{
lean_object* v_val_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v_val_2555_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_val_2555_);
lean_dec_ref_known(v___x_2553_, 1);
v___x_2556_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2557_ = l_String_intercalate(v___x_2556_, v_tail_2544_);
v___x_2558_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2557_);
lean_dec_ref(v___x_2557_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v___x_2559_; 
lean_dec(v_val_2555_);
lean_dec(v_it_2535_);
lean_dec_ref(v_b_2533_);
lean_dec(v___x_2531_);
lean_dec_ref(v___x_2529_);
v___x_2559_ = lean_box(0);
return v___x_2559_;
}
else
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2560_ = l_Std_Http_URI_Query_insertEncoded(v_b_2533_, v_val_2555_, v___x_2558_);
v___x_2561_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2529_, v___x_2530_, v___x_2531_, v_it_2535_, v___x_2560_);
return v___x_2561_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg___boxed(lean_object* v___x_2594_, lean_object* v___x_2595_, lean_object* v___x_2596_, lean_object* v_a_2597_, lean_object* v_b_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2594_, v___x_2595_, v___x_2596_, v_a_2597_, v_b_2598_);
lean_dec_ref(v___x_2595_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(lean_object* v_config_2605_, lean_object* v_a_2606_){
_start:
{
lean_object* v_maxQueryLength_2607_; lean_object* v_maxQueryParams_2608_; lean_object* v___f_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v_snd_2612_; lean_object* v_fst_2613_; lean_object* v_fst_2614_; lean_object* v_array_2615_; lean_object* v_idx_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2666_; 
v_maxQueryLength_2607_ = lean_ctor_get(v_config_2605_, 4);
lean_inc(v_maxQueryLength_2607_);
v_maxQueryParams_2608_ = lean_ctor_get(v_config_2605_, 8);
lean_inc(v_maxQueryParams_2608_);
lean_dec_ref(v_config_2605_);
v___f_2609_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2610_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2606_);
v___x_2611_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2609_, v_maxQueryLength_2607_, v___x_2610_, v_a_2606_);
lean_dec(v_maxQueryLength_2607_);
v_snd_2612_ = lean_ctor_get(v___x_2611_, 1);
lean_inc(v_snd_2612_);
v_fst_2613_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_fst_2613_);
lean_dec_ref(v___x_2611_);
v_fst_2614_ = lean_ctor_get(v_snd_2612_, 0);
lean_inc(v_fst_2614_);
lean_dec(v_snd_2612_);
v_array_2615_ = lean_ctor_get(v_a_2606_, 0);
v_idx_2616_ = lean_ctor_get(v_a_2606_, 1);
v_isSharedCheck_2666_ = !lean_is_exclusive(v_a_2606_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2618_ = v_a_2606_;
v_isShared_2619_ = v_isSharedCheck_2666_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_idx_2616_);
lean_inc(v_array_2615_);
lean_dec(v_a_2606_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2666_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v_lower_2621_; lean_object* v_upper_2622_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___y_2663_; uint8_t v___x_2665_; 
v___x_2660_ = lean_nat_add(v_idx_2616_, v_fst_2613_);
lean_dec(v_fst_2613_);
v___x_2661_ = lean_byte_array_size(v_array_2615_);
v___x_2665_ = lean_nat_dec_le(v_idx_2616_, v___x_2610_);
if (v___x_2665_ == 0)
{
v___y_2663_ = v_idx_2616_;
goto v___jp_2662_;
}
else
{
lean_dec(v_idx_2616_);
v___y_2663_ = v___x_2610_;
goto v___jp_2662_;
}
v___jp_2620_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; uint8_t v___x_2625_; 
v___x_2623_ = l_ByteArray_toByteSlice(v_array_2615_, v_lower_2621_, v_upper_2622_);
v___x_2624_ = l_ByteSlice_toByteArray(v___x_2623_);
v___x_2625_ = lean_string_validate_utf8(v___x_2624_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; lean_object* v___x_2628_; 
lean_dec_ref(v___x_2624_);
lean_dec(v_maxQueryParams_2608_);
v___x_2626_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2619_ == 0)
{
lean_ctor_set_tag(v___x_2618_, 1);
lean_ctor_set(v___x_2618_, 1, v___x_2626_);
lean_ctor_set(v___x_2618_, 0, v_fst_2614_);
v___x_2628_ = v___x_2618_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_fst_2614_);
lean_ctor_set(v_reuseFailAlloc_2629_, 1, v___x_2626_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
else
{
lean_object* v___x_2630_; lean_object* v___x_2631_; uint8_t v___x_2632_; 
v___x_2630_ = lean_string_from_utf8_unchecked(v___x_2624_);
v___x_2631_ = lean_string_utf8_byte_size(v___x_2630_);
v___x_2632_ = lean_nat_dec_eq(v___x_2631_, v___x_2610_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; uint8_t v___x_2636_; 
lean_inc_ref(v___x_2630_);
v___x_2633_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2630_);
lean_ctor_set(v___x_2633_, 1, v___x_2610_);
lean_ctor_set(v___x_2633_, 2, v___x_2631_);
v___x_2634_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(v___x_2633_);
lean_inc(v___x_2634_);
v___x_2635_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2630_, v___x_2633_, v___x_2631_, v___x_2634_, v___x_2610_);
v___x_2636_ = lean_nat_dec_lt(v_maxQueryParams_2608_, v___x_2635_);
lean_dec(v___x_2635_);
if (v___x_2636_ == 0)
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
lean_dec(v_maxQueryParams_2608_);
v___x_2637_ = l_Std_Http_URI_Query_empty;
v___x_2638_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2630_, v___x_2633_, v___x_2631_, v___x_2634_, v___x_2637_);
lean_dec_ref_known(v___x_2633_, 3);
if (lean_obj_tag(v___x_2638_) == 1)
{
lean_object* v_val_2639_; lean_object* v___x_2641_; 
v_val_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_val_2639_);
lean_dec_ref_known(v___x_2638_, 1);
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 1, v_val_2639_);
lean_ctor_set(v___x_2618_, 0, v_fst_2614_);
v___x_2641_ = v___x_2618_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_fst_2614_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v_val_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
else
{
lean_object* v___x_2643_; lean_object* v___x_2645_; 
lean_dec(v___x_2638_);
v___x_2643_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2619_ == 0)
{
lean_ctor_set_tag(v___x_2618_, 1);
lean_ctor_set(v___x_2618_, 1, v___x_2643_);
lean_ctor_set(v___x_2618_, 0, v_fst_2614_);
v___x_2645_ = v___x_2618_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_fst_2614_);
lean_ctor_set(v_reuseFailAlloc_2646_, 1, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
else
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2654_; 
lean_dec(v___x_2634_);
lean_dec_ref_known(v___x_2633_, 3);
lean_dec_ref(v___x_2630_);
v___x_2647_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3));
v___x_2648_ = l_Nat_reprFast(v_maxQueryParams_2608_);
v___x_2649_ = lean_string_append(v___x_2647_, v___x_2648_);
lean_dec_ref(v___x_2648_);
v___x_2650_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_2651_ = lean_string_append(v___x_2649_, v___x_2650_);
v___x_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2651_);
if (v_isShared_2619_ == 0)
{
lean_ctor_set_tag(v___x_2618_, 1);
lean_ctor_set(v___x_2618_, 1, v___x_2652_);
lean_ctor_set(v___x_2618_, 0, v_fst_2614_);
v___x_2654_ = v___x_2618_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_fst_2614_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v___x_2652_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2658_; 
lean_dec_ref(v___x_2630_);
lean_dec(v_maxQueryParams_2608_);
v___x_2656_ = l_Std_Http_URI_Query_empty;
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 1, v___x_2656_);
lean_ctor_set(v___x_2618_, 0, v_fst_2614_);
v___x_2658_ = v___x_2618_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_fst_2614_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v___x_2656_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
v___jp_2662_:
{
uint8_t v___x_2664_; 
v___x_2664_ = lean_nat_dec_le(v___x_2660_, v___x_2661_);
if (v___x_2664_ == 0)
{
lean_dec(v___x_2660_);
v_lower_2621_ = v___y_2663_;
v_upper_2622_ = v___x_2661_;
goto v___jp_2620_;
}
else
{
v_lower_2621_ = v___y_2663_;
v_upper_2622_ = v___x_2660_;
goto v___jp_2620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(lean_object* v___x_2667_, lean_object* v___x_2668_, lean_object* v___x_2669_, lean_object* v_inst_2670_, lean_object* v_R_2671_, lean_object* v_a_2672_, lean_object* v_b_2673_, lean_object* v_c_2674_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2667_, v___x_2668_, v___x_2669_, v_a_2672_, v_b_2673_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___boxed(lean_object* v___x_2676_, lean_object* v___x_2677_, lean_object* v___x_2678_, lean_object* v_inst_2679_, lean_object* v_R_2680_, lean_object* v_a_2681_, lean_object* v_b_2682_, lean_object* v_c_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(v___x_2676_, v___x_2677_, v___x_2678_, v_inst_2679_, v_R_2680_, v_a_2681_, v_b_2682_, v_c_2683_);
lean_dec(v___x_2678_);
lean_dec_ref(v___x_2677_);
lean_dec_ref(v___x_2676_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(lean_object* v_out_2685_, lean_object* v_inst_2686_, lean_object* v_R_2687_, lean_object* v_a_2688_, lean_object* v_b_2689_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2685_, v_a_2688_, v_b_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___boxed(lean_object* v_out_2691_, lean_object* v_inst_2692_, lean_object* v_R_2693_, lean_object* v_a_2694_, lean_object* v_b_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(v_out_2691_, v_inst_2692_, v_R_2693_, v_a_2694_, v_b_2695_);
lean_dec_ref(v_out_2691_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(lean_object* v___x_2697_, lean_object* v___x_2698_, lean_object* v___x_2699_, lean_object* v_inst_2700_, lean_object* v_R_2701_, lean_object* v_a_2702_, lean_object* v_b_2703_, lean_object* v_c_2704_){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2697_, v___x_2698_, v___x_2699_, v_a_2702_, v_b_2703_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___boxed(lean_object* v___x_2706_, lean_object* v___x_2707_, lean_object* v___x_2708_, lean_object* v_inst_2709_, lean_object* v_R_2710_, lean_object* v_a_2711_, lean_object* v_b_2712_, lean_object* v_c_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(v___x_2706_, v___x_2707_, v___x_2708_, v_inst_2709_, v_R_2710_, v_a_2711_, v_b_2712_, v_c_2713_);
lean_dec_ref(v___x_2707_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(lean_object* v___x_2715_, lean_object* v___x_2716_, lean_object* v___x_2717_, lean_object* v_inst_2718_, lean_object* v_R_2719_, lean_object* v_a_2720_, lean_object* v_b_2721_, lean_object* v_c_2722_){
_start:
{
lean_object* v___x_2723_; 
v___x_2723_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2716_, v___x_2717_, v_a_2720_, v_b_2721_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___boxed(lean_object* v___x_2724_, lean_object* v___x_2725_, lean_object* v___x_2726_, lean_object* v_inst_2727_, lean_object* v_R_2728_, lean_object* v_a_2729_, lean_object* v_b_2730_, lean_object* v_c_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(v___x_2724_, v___x_2725_, v___x_2726_, v_inst_2727_, v_R_2728_, v_a_2729_, v_b_2730_, v_c_2731_);
lean_dec(v___x_2726_);
lean_dec_ref(v___x_2725_);
lean_dec_ref(v___x_2724_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(lean_object* v___x_2733_, lean_object* v___x_2734_, lean_object* v___x_2735_, lean_object* v_inst_2736_, lean_object* v_R_2737_, lean_object* v_a_2738_, lean_object* v_b_2739_, lean_object* v_c_2740_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2733_, v___x_2734_, v___x_2735_, v_a_2738_, v_b_2739_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___boxed(lean_object* v___x_2742_, lean_object* v___x_2743_, lean_object* v___x_2744_, lean_object* v_inst_2745_, lean_object* v_R_2746_, lean_object* v_a_2747_, lean_object* v_b_2748_, lean_object* v_c_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(v___x_2742_, v___x_2743_, v___x_2744_, v_inst_2745_, v_R_2746_, v_a_2747_, v_b_2748_, v_c_2749_);
lean_dec_ref(v___x_2743_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(lean_object* v_config_2754_, lean_object* v_a_2755_){
_start:
{
lean_object* v_maxFragmentLength_2756_; lean_object* v___f_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v_snd_2760_; lean_object* v_fst_2761_; lean_object* v_fst_2762_; lean_object* v_array_2763_; lean_object* v_idx_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2788_; 
v_maxFragmentLength_2756_ = lean_ctor_get(v_config_2754_, 5);
v___f_2757_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2758_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2755_);
v___x_2759_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2757_, v_maxFragmentLength_2756_, v___x_2758_, v_a_2755_);
v_snd_2760_ = lean_ctor_get(v___x_2759_, 1);
lean_inc(v_snd_2760_);
v_fst_2761_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_fst_2761_);
lean_dec_ref(v___x_2759_);
v_fst_2762_ = lean_ctor_get(v_snd_2760_, 0);
lean_inc(v_fst_2762_);
lean_dec(v_snd_2760_);
v_array_2763_ = lean_ctor_get(v_a_2755_, 0);
v_idx_2764_ = lean_ctor_get(v_a_2755_, 1);
v_isSharedCheck_2788_ = !lean_is_exclusive(v_a_2755_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2766_ = v_a_2755_;
v_isShared_2767_ = v_isSharedCheck_2788_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_idx_2764_);
lean_inc(v_array_2763_);
lean_dec(v_a_2755_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2788_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v_lower_2769_; lean_object* v_upper_2770_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___y_2785_; uint8_t v___x_2787_; 
v___x_2782_ = lean_nat_add(v_idx_2764_, v_fst_2761_);
lean_dec(v_fst_2761_);
v___x_2783_ = lean_byte_array_size(v_array_2763_);
v___x_2787_ = lean_nat_dec_le(v_idx_2764_, v___x_2758_);
if (v___x_2787_ == 0)
{
v___y_2785_ = v_idx_2764_;
goto v___jp_2784_;
}
else
{
lean_dec(v_idx_2764_);
v___y_2785_ = v___x_2758_;
goto v___jp_2784_;
}
v___jp_2768_:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2771_ = l_ByteArray_toByteSlice(v_array_2763_, v_lower_2769_, v_upper_2770_);
v___x_2772_ = l_ByteSlice_toByteArray(v___x_2771_);
v___x_2773_ = l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(v___x_2772_);
if (lean_obj_tag(v___x_2773_) == 1)
{
lean_object* v_val_2774_; lean_object* v___x_2776_; 
v_val_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_val_2774_);
lean_dec_ref_known(v___x_2773_, 1);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 1, v_val_2774_);
lean_ctor_set(v___x_2766_, 0, v_fst_2762_);
v___x_2776_ = v___x_2766_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_fst_2762_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v_val_2774_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
else
{
lean_object* v___x_2778_; lean_object* v___x_2780_; 
lean_dec(v___x_2773_);
v___x_2778_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1));
if (v_isShared_2767_ == 0)
{
lean_ctor_set_tag(v___x_2766_, 1);
lean_ctor_set(v___x_2766_, 1, v___x_2778_);
lean_ctor_set(v___x_2766_, 0, v_fst_2762_);
v___x_2780_ = v___x_2766_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_fst_2762_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v___x_2778_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
v___jp_2784_:
{
uint8_t v___x_2786_; 
v___x_2786_ = lean_nat_dec_le(v___x_2782_, v___x_2783_);
if (v___x_2786_ == 0)
{
lean_dec(v___x_2782_);
v_lower_2769_ = v___y_2785_;
v_upper_2770_ = v___x_2783_;
goto v___jp_2768_;
}
else
{
v_lower_2769_ = v___y_2785_;
v_upper_2770_ = v___x_2782_;
goto v___jp_2768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___boxed(lean_object* v_config_2789_, lean_object* v_a_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2789_, v_a_2790_);
lean_dec_ref(v_config_2789_);
return v_res_2791_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1(void){
_start:
{
lean_object* v___x_2793_; lean_object* v_utf8_2794_; 
v___x_2793_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0));
v_utf8_2794_ = lean_string_to_utf8(v___x_2793_);
return v_utf8_2794_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(lean_object* v_config_2795_, lean_object* v_a_2796_){
_start:
{
lean_object* v_pos_2798_; lean_object* v_utf8_2833_; lean_object* v___x_2834_; 
v_utf8_2833_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_2796_);
v___x_2834_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_2833_, v_a_2796_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_pos_2835_; 
lean_dec_ref(v_a_2796_);
v_pos_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_pos_2835_);
lean_dec_ref_known(v___x_2834_, 2);
v_pos_2798_ = v_pos_2835_;
goto v___jp_2797_;
}
else
{
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_pos_2836_; 
lean_dec_ref(v_a_2796_);
v_pos_2836_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_pos_2836_);
lean_dec_ref_known(v___x_2834_, 2);
v_pos_2798_ = v_pos_2836_;
goto v___jp_2797_;
}
else
{
lean_object* v_err_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2868_; 
v_err_2837_ = lean_ctor_get(v___x_2834_, 1);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2868_ == 0)
{
lean_object* v_unused_2869_; 
v_unused_2869_ = lean_ctor_get(v___x_2834_, 0);
lean_dec(v_unused_2869_);
v___x_2839_ = v___x_2834_;
v_isShared_2840_ = v_isSharedCheck_2868_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_err_2837_);
lean_dec(v___x_2834_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2868_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v_idx_2841_; uint8_t v___x_2842_; 
v_idx_2841_ = lean_ctor_get(v_a_2796_, 1);
v___x_2842_ = lean_nat_dec_eq(v_idx_2841_, v_idx_2841_);
if (v___x_2842_ == 0)
{
lean_object* v___x_2844_; 
lean_dec_ref(v_config_2795_);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 0, v_a_2796_);
v___x_2844_ = v___x_2839_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2796_);
lean_ctor_set(v_reuseFailAlloc_2845_, 1, v_err_2837_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
else
{
uint8_t v___x_2846_; lean_object* v___x_2847_; 
lean_del_object(v___x_2839_);
lean_dec(v_err_2837_);
v___x_2846_ = 0;
v___x_2847_ = l_Std_Http_URI_Parser_parsePath(v_config_2795_, v___x_2846_, v___x_2842_, v_a_2796_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_pos_2848_; lean_object* v_res_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2858_; 
v_pos_2848_ = lean_ctor_get(v___x_2847_, 0);
v_res_2849_ = lean_ctor_get(v___x_2847_, 1);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2851_ = v___x_2847_;
v_isShared_2852_ = v_isSharedCheck_2858_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_res_2849_);
lean_inc(v_pos_2848_);
lean_dec(v___x_2847_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2858_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2856_; 
v___x_2853_ = lean_box(0);
v___x_2854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2853_);
lean_ctor_set(v___x_2854_, 1, v_res_2849_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 1, v___x_2854_);
v___x_2856_ = v___x_2851_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_pos_2848_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v___x_2854_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
else
{
lean_object* v_pos_2859_; lean_object* v_err_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
v_pos_2859_ = lean_ctor_get(v___x_2847_, 0);
v_err_2860_ = lean_ctor_get(v___x_2847_, 1);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2847_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_err_2860_);
lean_inc(v_pos_2859_);
lean_dec(v___x_2847_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_pos_2859_);
lean_ctor_set(v_reuseFailAlloc_2866_, 1, v_err_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
}
}
}
v___jp_2797_:
{
lean_object* v___x_2799_; 
v___x_2799_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_2795_, v_pos_2798_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_pos_2800_; lean_object* v_res_2801_; uint8_t v___x_2802_; lean_object* v___x_2803_; 
v_pos_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_pos_2800_);
v_res_2801_ = lean_ctor_get(v___x_2799_, 1);
lean_inc(v_res_2801_);
lean_dec_ref_known(v___x_2799_, 2);
v___x_2802_ = 1;
v___x_2803_ = l_Std_Http_URI_Parser_parsePath(v_config_2795_, v___x_2802_, v___x_2802_, v_pos_2800_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v_pos_2804_; lean_object* v_res_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2814_; 
v_pos_2804_ = lean_ctor_get(v___x_2803_, 0);
v_res_2805_ = lean_ctor_get(v___x_2803_, 1);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2807_ = v___x_2803_;
v_isShared_2808_ = v_isSharedCheck_2814_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_res_2805_);
lean_inc(v_pos_2804_);
lean_dec(v___x_2803_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2814_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2812_; 
v___x_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2809_, 0, v_res_2801_);
v___x_2810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2809_);
lean_ctor_set(v___x_2810_, 1, v_res_2805_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 1, v___x_2810_);
v___x_2812_ = v___x_2807_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_pos_2804_);
lean_ctor_set(v_reuseFailAlloc_2813_, 1, v___x_2810_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
else
{
lean_object* v_pos_2815_; lean_object* v_err_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_dec(v_res_2801_);
v_pos_2815_ = lean_ctor_get(v___x_2803_, 0);
v_err_2816_ = lean_ctor_get(v___x_2803_, 1);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2803_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_err_2816_);
lean_inc(v_pos_2815_);
lean_dec(v___x_2803_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_pos_2815_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v_err_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
else
{
lean_object* v_pos_2824_; lean_object* v_err_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_dec_ref(v_config_2795_);
v_pos_2824_ = lean_ctor_get(v___x_2799_, 0);
v_err_2825_ = lean_ctor_get(v___x_2799_, 1);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2799_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_err_2825_);
lean_inc(v_pos_2824_);
lean_dec(v___x_2799_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_pos_2824_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v_err_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__0(void){
_start:
{
uint8_t v___x_2870_; lean_object* v___x_2871_; 
v___x_2870_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v___x_2871_ = lean_uint8_to_nat(v___x_2870_);
return v___x_2871_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__1(void){
_start:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2872_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__0, &l_Std_Http_URI_Parser_parseURI___closed__0_once, _init_l_Std_Http_URI_Parser_parseURI___closed__0);
v___x_2873_ = l_Nat_reprFast(v___x_2872_);
return v___x_2873_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__2(void){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2874_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__1, &l_Std_Http_URI_Parser_parseURI___closed__1_once, _init_l_Std_Http_URI_Parser_parseURI___closed__1);
v___x_2875_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_2876_ = lean_string_append(v___x_2875_, v___x_2874_);
return v___x_2876_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__3(void){
_start:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2877_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_2878_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__2, &l_Std_Http_URI_Parser_parseURI___closed__2_once, _init_l_Std_Http_URI_Parser_parseURI___closed__2);
v___x_2879_ = lean_string_append(v___x_2878_, v___x_2877_);
return v___x_2879_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__4(void){
_start:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2880_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__3, &l_Std_Http_URI_Parser_parseURI___closed__3_once, _init_l_Std_Http_URI_Parser_parseURI___closed__3);
v___x_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2880_);
return v___x_2881_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__7(void){
_start:
{
uint8_t v___x_2885_; lean_object* v___x_2886_; 
v___x_2885_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_2886_ = lean_uint8_to_nat(v___x_2885_);
return v___x_2886_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__8(void){
_start:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2887_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__7, &l_Std_Http_URI_Parser_parseURI___closed__7_once, _init_l_Std_Http_URI_Parser_parseURI___closed__7);
v___x_2888_ = l_Nat_reprFast(v___x_2887_);
return v___x_2888_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__9(void){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2889_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__8, &l_Std_Http_URI_Parser_parseURI___closed__8_once, _init_l_Std_Http_URI_Parser_parseURI___closed__8);
v___x_2890_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_2891_ = lean_string_append(v___x_2890_, v___x_2889_);
return v___x_2891_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__10(void){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2892_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_2893_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__9, &l_Std_Http_URI_Parser_parseURI___closed__9_once, _init_l_Std_Http_URI_Parser_parseURI___closed__9);
v___x_2894_ = lean_string_append(v___x_2893_, v___x_2892_);
return v___x_2894_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__11(void){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__10, &l_Std_Http_URI_Parser_parseURI___closed__10_once, _init_l_Std_Http_URI_Parser_parseURI___closed__10);
v___x_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURI(lean_object* v_config_2897_, lean_object* v_a_2898_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_2897_, v_a_2898_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_pos_2900_; lean_object* v_res_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_3041_; 
v_pos_2900_ = lean_ctor_get(v___x_2899_, 0);
v_res_2901_ = lean_ctor_get(v___x_2899_, 1);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_2903_ = v___x_2899_;
v_isShared_2904_ = v_isSharedCheck_3041_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_res_2901_);
lean_inc(v_pos_2900_);
lean_dec(v___x_2899_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_3041_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v_array_2905_; lean_object* v_idx_2906_; lean_object* v___x_2907_; uint8_t v___x_2908_; 
v_array_2905_ = lean_ctor_get(v_pos_2900_, 0);
v_idx_2906_ = lean_ctor_get(v_pos_2900_, 1);
v___x_2907_ = lean_byte_array_size(v_array_2905_);
v___x_2908_ = lean_nat_dec_lt(v_idx_2906_, v___x_2907_);
if (v___x_2908_ == 0)
{
lean_object* v___x_2909_; lean_object* v___x_2911_; 
lean_dec(v_res_2901_);
lean_dec_ref(v_config_2897_);
v___x_2909_ = lean_box(0);
if (v_isShared_2904_ == 0)
{
lean_ctor_set_tag(v___x_2903_, 1);
lean_ctor_set(v___x_2903_, 1, v___x_2909_);
v___x_2911_ = v___x_2903_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_pos_2900_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v___x_2909_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
else
{
uint8_t v___x_2913_; uint8_t v_got_2914_; uint8_t v___x_2915_; 
v___x_2913_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v_got_2914_ = lean_byte_array_fget(v_array_2905_, v_idx_2906_);
v___x_2915_ = lean_uint8_dec_eq(v_got_2914_, v___x_2913_);
if (v___x_2915_ == 0)
{
lean_object* v___x_2916_; lean_object* v___x_2918_; 
lean_dec(v_res_2901_);
lean_dec_ref(v_config_2897_);
v___x_2916_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
if (v_isShared_2904_ == 0)
{
lean_ctor_set_tag(v___x_2903_, 1);
lean_ctor_set(v___x_2903_, 1, v___x_2916_);
v___x_2918_ = v___x_2903_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_pos_2900_);
lean_ctor_set(v_reuseFailAlloc_2919_, 1, v___x_2916_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
else
{
lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_3038_; 
lean_inc(v_idx_2906_);
lean_inc_ref(v_array_2905_);
v_isSharedCheck_3038_ = !lean_is_exclusive(v_pos_2900_);
if (v_isSharedCheck_3038_ == 0)
{
lean_object* v_unused_3039_; lean_object* v_unused_3040_; 
v_unused_3039_ = lean_ctor_get(v_pos_2900_, 1);
lean_dec(v_unused_3039_);
v_unused_3040_ = lean_ctor_get(v_pos_2900_, 0);
lean_dec(v_unused_3040_);
v___x_2921_ = v_pos_2900_;
v_isShared_2922_ = v_isSharedCheck_3038_;
goto v_resetjp_2920_;
}
else
{
lean_dec(v_pos_2900_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_3038_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2926_; 
v___x_2923_ = lean_unsigned_to_nat(1u);
v___x_2924_ = lean_nat_add(v_idx_2906_, v___x_2923_);
lean_dec(v_idx_2906_);
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 1, v___x_2924_);
v___x_2926_ = v___x_2921_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_array_2905_);
lean_ctor_set(v_reuseFailAlloc_3037_, 1, v___x_2924_);
v___x_2926_ = v_reuseFailAlloc_3037_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
lean_object* v___x_2927_; 
lean_inc_ref(v_config_2897_);
v___x_2927_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2897_, v___x_2926_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_res_2928_; lean_object* v_pos_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_3027_; 
v_res_2928_ = lean_ctor_get(v___x_2927_, 1);
v_pos_2929_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_2931_ = v___x_2927_;
v_isShared_2932_ = v_isSharedCheck_3027_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_res_2928_);
lean_inc(v_pos_2929_);
lean_dec(v___x_2927_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_3027_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v_fst_2933_; lean_object* v_snd_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_3026_; 
v_fst_2933_ = lean_ctor_get(v_res_2928_, 0);
v_snd_2934_ = lean_ctor_get(v_res_2928_, 1);
v_isSharedCheck_3026_ = !lean_is_exclusive(v_res_2928_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_2936_ = v_res_2928_;
v_isShared_2937_ = v_isSharedCheck_3026_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_snd_2934_);
lean_inc(v_fst_2933_);
lean_dec(v_res_2928_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_3026_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___y_2939_; lean_object* v_pos_2940_; lean_object* v_res_2941_; lean_object* v___y_2947_; lean_object* v_idx_2948_; lean_object* v_pos_2949_; lean_object* v_idx_2950_; lean_object* v_err_2951_; lean_object* v___y_2958_; lean_object* v_idx_2959_; lean_object* v_pos_2960_; lean_object* v_err_2961_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v_array_2992_; lean_object* v_idx_2993_; lean_object* v_pos_2995_; lean_object* v_idx_2996_; lean_object* v_err_2997_; lean_object* v___x_3003_; uint8_t v___x_3004_; 
v_array_2992_ = lean_ctor_get(v_pos_2929_, 0);
v_idx_2993_ = lean_ctor_get(v_pos_2929_, 1);
lean_inc(v_idx_2993_);
v___x_3003_ = lean_byte_array_size(v_array_2992_);
v___x_3004_ = lean_nat_dec_lt(v_idx_2993_, v___x_3003_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3005_; 
v___x_3005_ = lean_box(0);
lean_inc(v_idx_2993_);
v_pos_2995_ = v_pos_2929_;
v_idx_2996_ = v_idx_2993_;
v_err_2997_ = v___x_3005_;
goto v___jp_2994_;
}
else
{
uint8_t v___x_3006_; uint8_t v_got_3007_; uint8_t v___x_3008_; 
v___x_3006_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3007_ = lean_byte_array_fget(v_array_2992_, v_idx_2993_);
v___x_3008_ = lean_uint8_dec_eq(v_got_3007_, v___x_3006_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; 
v___x_3009_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_2993_);
v_pos_2995_ = v_pos_2929_;
v_idx_2996_ = v_idx_2993_;
v_err_2997_ = v___x_3009_;
goto v___jp_2994_;
}
else
{
lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3023_; 
lean_inc_ref(v_array_2992_);
v_isSharedCheck_3023_ = !lean_is_exclusive(v_pos_2929_);
if (v_isSharedCheck_3023_ == 0)
{
lean_object* v_unused_3024_; lean_object* v_unused_3025_; 
v_unused_3024_ = lean_ctor_get(v_pos_2929_, 1);
lean_dec(v_unused_3024_);
v_unused_3025_ = lean_ctor_get(v_pos_2929_, 0);
lean_dec(v_unused_3025_);
v___x_3011_ = v_pos_2929_;
v_isShared_3012_ = v_isSharedCheck_3023_;
goto v_resetjp_3010_;
}
else
{
lean_dec(v_pos_2929_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3023_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3013_; lean_object* v___x_3015_; 
v___x_3013_ = lean_nat_add(v_idx_2993_, v___x_2923_);
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 1, v___x_3013_);
v___x_3015_ = v___x_3011_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_array_2992_);
lean_ctor_set(v_reuseFailAlloc_3022_, 1, v___x_3013_);
v___x_3015_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
lean_object* v___x_3016_; 
lean_inc_ref(v_config_2897_);
v___x_3016_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2897_, v___x_3015_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_pos_3017_; lean_object* v_res_3018_; 
lean_dec(v_idx_2993_);
lean_del_object(v___x_2936_);
v_pos_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_pos_3017_);
v_res_3018_ = lean_ctor_get(v___x_3016_, 1);
lean_inc(v_res_3018_);
lean_dec_ref_known(v___x_3016_, 2);
v___y_2964_ = v_pos_3017_;
v___y_2965_ = v_res_3018_;
goto v___jp_2963_;
}
else
{
lean_object* v_pos_3019_; lean_object* v_err_3020_; lean_object* v_idx_3021_; 
v_pos_3019_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_pos_3019_);
v_err_3020_ = lean_ctor_get(v___x_3016_, 1);
lean_inc(v_err_3020_);
lean_dec_ref_known(v___x_3016_, 2);
v_idx_3021_ = lean_ctor_get(v_pos_3019_, 1);
lean_inc(v_idx_3021_);
v_pos_2995_ = v_pos_3019_;
v_idx_2996_ = v_idx_3021_;
v_err_2997_ = v_err_3020_;
goto v___jp_2994_;
}
}
}
}
}
v___jp_2938_:
{
lean_object* v___x_2942_; lean_object* v___x_2944_; 
v___x_2942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2942_, 0, v_res_2901_);
lean_ctor_set(v___x_2942_, 1, v_fst_2933_);
lean_ctor_set(v___x_2942_, 2, v_snd_2934_);
lean_ctor_set(v___x_2942_, 3, v___y_2939_);
lean_ctor_set(v___x_2942_, 4, v_res_2941_);
if (v_isShared_2932_ == 0)
{
lean_ctor_set(v___x_2931_, 1, v___x_2942_);
lean_ctor_set(v___x_2931_, 0, v_pos_2940_);
v___x_2944_ = v___x_2931_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_pos_2940_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v___x_2942_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
v___jp_2946_:
{
uint8_t v___x_2952_; 
v___x_2952_ = lean_nat_dec_eq(v_idx_2948_, v_idx_2950_);
lean_dec(v_idx_2950_);
lean_dec(v_idx_2948_);
if (v___x_2952_ == 0)
{
lean_object* v___x_2954_; 
lean_dec_ref(v___y_2947_);
lean_dec(v_snd_2934_);
lean_dec(v_fst_2933_);
lean_del_object(v___x_2931_);
lean_dec(v_res_2901_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set_tag(v___x_2903_, 1);
lean_ctor_set(v___x_2903_, 1, v_err_2951_);
lean_ctor_set(v___x_2903_, 0, v_pos_2949_);
v___x_2954_ = v___x_2903_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_pos_2949_);
lean_ctor_set(v_reuseFailAlloc_2955_, 1, v_err_2951_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
else
{
lean_object* v___x_2956_; 
lean_dec(v_err_2951_);
lean_del_object(v___x_2903_);
v___x_2956_ = lean_box(0);
v___y_2939_ = v___y_2947_;
v_pos_2940_ = v_pos_2949_;
v_res_2941_ = v___x_2956_;
goto v___jp_2938_;
}
}
v___jp_2957_:
{
lean_object* v_idx_2962_; 
v_idx_2962_ = lean_ctor_get(v_pos_2960_, 1);
lean_inc(v_idx_2962_);
v___y_2947_ = v___y_2958_;
v_idx_2948_ = v_idx_2959_;
v_pos_2949_ = v_pos_2960_;
v_idx_2950_ = v_idx_2962_;
v_err_2951_ = v_err_2961_;
goto v___jp_2946_;
}
v___jp_2963_:
{
lean_object* v_array_2966_; lean_object* v_idx_2967_; lean_object* v___x_2968_; uint8_t v___x_2969_; 
v_array_2966_ = lean_ctor_get(v___y_2964_, 0);
v_idx_2967_ = lean_ctor_get(v___y_2964_, 1);
lean_inc(v_idx_2967_);
v___x_2968_ = lean_byte_array_size(v_array_2966_);
v___x_2969_ = lean_nat_dec_lt(v_idx_2967_, v___x_2968_);
if (v___x_2969_ == 0)
{
lean_object* v___x_2970_; 
lean_dec_ref(v_config_2897_);
v___x_2970_ = lean_box(0);
lean_inc(v_idx_2967_);
v___y_2947_ = v___y_2965_;
v_idx_2948_ = v_idx_2967_;
v_pos_2949_ = v___y_2964_;
v_idx_2950_ = v_idx_2967_;
v_err_2951_ = v___x_2970_;
goto v___jp_2946_;
}
else
{
uint8_t v___x_2971_; uint8_t v_got_2972_; uint8_t v___x_2973_; 
v___x_2971_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v_got_2972_ = lean_byte_array_fget(v_array_2966_, v_idx_2967_);
v___x_2973_ = lean_uint8_dec_eq(v_got_2972_, v___x_2971_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; 
lean_dec_ref(v_config_2897_);
v___x_2974_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__4, &l_Std_Http_URI_Parser_parseURI___closed__4_once, _init_l_Std_Http_URI_Parser_parseURI___closed__4);
lean_inc(v_idx_2967_);
v___y_2947_ = v___y_2965_;
v_idx_2948_ = v_idx_2967_;
v_pos_2949_ = v___y_2964_;
v_idx_2950_ = v_idx_2967_;
v_err_2951_ = v___x_2974_;
goto v___jp_2946_;
}
else
{
lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2989_; 
lean_inc_ref(v_array_2966_);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___y_2964_);
if (v_isSharedCheck_2989_ == 0)
{
lean_object* v_unused_2990_; lean_object* v_unused_2991_; 
v_unused_2990_ = lean_ctor_get(v___y_2964_, 1);
lean_dec(v_unused_2990_);
v_unused_2991_ = lean_ctor_get(v___y_2964_, 0);
lean_dec(v_unused_2991_);
v___x_2976_ = v___y_2964_;
v_isShared_2977_ = v_isSharedCheck_2989_;
goto v_resetjp_2975_;
}
else
{
lean_dec(v___y_2964_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2989_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2978_; lean_object* v___x_2980_; 
v___x_2978_ = lean_nat_add(v_idx_2967_, v___x_2923_);
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 1, v___x_2978_);
v___x_2980_ = v___x_2976_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_array_2966_);
lean_ctor_set(v_reuseFailAlloc_2988_, 1, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
lean_object* v___x_2981_; 
v___x_2981_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2897_, v___x_2980_);
lean_dec_ref(v_config_2897_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v_pos_2982_; lean_object* v_res_2983_; lean_object* v___x_2984_; 
v_pos_2982_ = lean_ctor_get(v___x_2981_, 0);
lean_inc(v_pos_2982_);
v_res_2983_ = lean_ctor_get(v___x_2981_, 1);
lean_inc(v_res_2983_);
lean_dec_ref_known(v___x_2981_, 2);
v___x_2984_ = l_Std_Http_URI_EncodedFragment_decode(v_res_2983_);
lean_dec(v_res_2983_);
if (lean_obj_tag(v___x_2984_) == 1)
{
lean_dec(v_idx_2967_);
lean_del_object(v___x_2903_);
v___y_2939_ = v___y_2965_;
v_pos_2940_ = v_pos_2982_;
v_res_2941_ = v___x_2984_;
goto v___jp_2938_;
}
else
{
lean_object* v___x_2985_; 
lean_dec(v___x_2984_);
v___x_2985_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__6));
v___y_2958_ = v___y_2965_;
v_idx_2959_ = v_idx_2967_;
v_pos_2960_ = v_pos_2982_;
v_err_2961_ = v___x_2985_;
goto v___jp_2957_;
}
}
else
{
lean_object* v_pos_2986_; lean_object* v_err_2987_; 
v_pos_2986_ = lean_ctor_get(v___x_2981_, 0);
lean_inc(v_pos_2986_);
v_err_2987_ = lean_ctor_get(v___x_2981_, 1);
lean_inc(v_err_2987_);
lean_dec_ref_known(v___x_2981_, 2);
v___y_2958_ = v___y_2965_;
v_idx_2959_ = v_idx_2967_;
v_pos_2960_ = v_pos_2986_;
v_err_2961_ = v_err_2987_;
goto v___jp_2957_;
}
}
}
}
}
}
v___jp_2994_:
{
uint8_t v___x_2998_; 
v___x_2998_ = lean_nat_dec_eq(v_idx_2993_, v_idx_2996_);
lean_dec(v_idx_2996_);
lean_dec(v_idx_2993_);
if (v___x_2998_ == 0)
{
lean_object* v___x_3000_; 
lean_dec(v_snd_2934_);
lean_dec(v_fst_2933_);
lean_del_object(v___x_2931_);
lean_del_object(v___x_2903_);
lean_dec(v_res_2901_);
lean_dec_ref(v_config_2897_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set_tag(v___x_2936_, 1);
lean_ctor_set(v___x_2936_, 1, v_err_2997_);
lean_ctor_set(v___x_2936_, 0, v_pos_2995_);
v___x_3000_ = v___x_2936_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_pos_2995_);
lean_ctor_set(v_reuseFailAlloc_3001_, 1, v_err_2997_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
else
{
lean_object* v___x_3002_; 
lean_dec(v_err_2997_);
lean_del_object(v___x_2936_);
v___x_3002_ = l_Std_Http_URI_Query_empty;
v___y_2964_ = v_pos_2995_;
v___y_2965_ = v___x_3002_;
goto v___jp_2963_;
}
}
}
}
}
else
{
lean_object* v_pos_3028_; lean_object* v_err_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_del_object(v___x_2903_);
lean_dec(v_res_2901_);
lean_dec_ref(v_config_2897_);
v_pos_3028_ = lean_ctor_get(v___x_2927_, 0);
v_err_3029_ = lean_ctor_get(v___x_2927_, 1);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_2927_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_err_3029_);
lean_inc(v_pos_3028_);
lean_dec(v___x_2927_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_pos_3028_);
lean_ctor_set(v_reuseFailAlloc_3035_, 1, v_err_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
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
lean_object* v_pos_3042_; lean_object* v_err_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_dec_ref(v_config_2897_);
v_pos_3042_ = lean_ctor_get(v___x_2899_, 0);
v_err_3043_ = lean_ctor_get(v___x_2899_, 1);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_2899_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_err_3043_);
lean_inc(v_pos_3042_);
lean_dec(v___x_2899_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_pos_3042_);
lean_ctor_set(v_reuseFailAlloc_3049_, 1, v_err_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0(void){
_start:
{
uint8_t v___x_3051_; lean_object* v___x_3052_; 
v___x_3051_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_3052_ = lean_uint8_to_nat(v___x_3051_);
return v___x_3052_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1(void){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0);
v___x_3054_ = l_Nat_reprFast(v___x_3053_);
return v___x_3054_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2(void){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3055_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1);
v___x_3056_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_3057_ = lean_string_append(v___x_3056_, v___x_3055_);
return v___x_3057_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3(void){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3058_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_3059_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2);
v___x_3060_ = lean_string_append(v___x_3059_, v___x_3058_);
return v___x_3060_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4(void){
_start:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3061_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3);
v___x_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3061_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(lean_object* v_a_3063_){
_start:
{
lean_object* v_array_3064_; lean_object* v_idx_3065_; lean_object* v___x_3066_; uint8_t v___x_3067_; 
v_array_3064_ = lean_ctor_get(v_a_3063_, 0);
v_idx_3065_ = lean_ctor_get(v_a_3063_, 1);
v___x_3066_ = lean_byte_array_size(v_array_3064_);
v___x_3067_ = lean_nat_dec_lt(v_idx_3065_, v___x_3066_);
if (v___x_3067_ == 0)
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3068_ = lean_box(0);
v___x_3069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3069_, 0, v_a_3063_);
lean_ctor_set(v___x_3069_, 1, v___x_3068_);
return v___x_3069_;
}
else
{
uint8_t v___x_3070_; uint8_t v_got_3071_; uint8_t v___x_3072_; 
v___x_3070_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v_got_3071_ = lean_byte_array_fget(v_array_3064_, v_idx_3065_);
v___x_3072_ = lean_uint8_dec_eq(v_got_3071_, v___x_3070_);
if (v___x_3072_ == 0)
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3073_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4);
v___x_3074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3074_, 0, v_a_3063_);
lean_ctor_set(v___x_3074_, 1, v___x_3073_);
return v___x_3074_;
}
else
{
lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3085_; 
lean_inc(v_idx_3065_);
lean_inc_ref(v_array_3064_);
v_isSharedCheck_3085_ = !lean_is_exclusive(v_a_3063_);
if (v_isSharedCheck_3085_ == 0)
{
lean_object* v_unused_3086_; lean_object* v_unused_3087_; 
v_unused_3086_ = lean_ctor_get(v_a_3063_, 1);
lean_dec(v_unused_3086_);
v_unused_3087_ = lean_ctor_get(v_a_3063_, 0);
lean_dec(v_unused_3087_);
v___x_3076_ = v_a_3063_;
v_isShared_3077_ = v_isSharedCheck_3085_;
goto v_resetjp_3075_;
}
else
{
lean_dec(v_a_3063_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3085_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3081_; 
v___x_3078_ = lean_unsigned_to_nat(1u);
v___x_3079_ = lean_nat_add(v_idx_3065_, v___x_3078_);
lean_dec(v_idx_3065_);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 1, v___x_3079_);
v___x_3081_ = v___x_3076_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_array_3064_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v___x_3079_);
v___x_3081_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = lean_box(3);
v___x_3083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3081_);
lean_ctor_set(v___x_3083_, 1, v___x_3082_);
return v___x_3083_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(lean_object* v_config_3091_, lean_object* v_a_3092_){
_start:
{
lean_object* v_array_3096_; lean_object* v_idx_3097_; lean_object* v___x_3098_; uint8_t v___x_3099_; 
v_array_3096_ = lean_ctor_get(v_a_3092_, 0);
v_idx_3097_ = lean_ctor_get(v_a_3092_, 1);
v___x_3098_ = lean_byte_array_size(v_array_3096_);
v___x_3099_ = lean_nat_dec_lt(v_idx_3097_, v___x_3098_);
if (v___x_3099_ == 0)
{
lean_dec_ref(v_config_3091_);
goto v___jp_3093_;
}
else
{
uint8_t v___x_3100_; uint8_t v___x_3101_; uint8_t v___x_3102_; 
v___x_3100_ = lean_byte_array_fget(v_array_3096_, v_idx_3097_);
v___x_3101_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_3102_ = lean_uint8_dec_eq(v___x_3100_, v___x_3101_);
if (v___x_3102_ == 0)
{
lean_dec_ref(v_config_3091_);
goto v___jp_3093_;
}
else
{
if (v___x_3102_ == 0)
{
lean_dec_ref(v_config_3091_);
goto v___jp_3093_;
}
else
{
lean_object* v___x_3103_; 
lean_inc_ref(v_a_3092_);
lean_inc_ref(v_config_3091_);
v___x_3103_ = l_Std_Http_URI_Parser_parsePath(v_config_3091_, v___x_3102_, v___x_3102_, v_a_3092_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_pos_3104_; lean_object* v_res_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3150_; 
v_pos_3104_ = lean_ctor_get(v___x_3103_, 0);
v_res_3105_ = lean_ctor_get(v___x_3103_, 1);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3107_ = v___x_3103_;
v_isShared_3108_ = v_isSharedCheck_3150_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_res_3105_);
lean_inc(v_pos_3104_);
lean_dec(v___x_3103_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3150_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v_pos_3110_; lean_object* v_res_3111_; lean_object* v_array_3116_; lean_object* v_idx_3117_; lean_object* v_pos_3119_; lean_object* v_idx_3120_; lean_object* v_err_3121_; lean_object* v___x_3125_; uint8_t v___x_3126_; 
v_array_3116_ = lean_ctor_get(v_pos_3104_, 0);
v_idx_3117_ = lean_ctor_get(v_pos_3104_, 1);
lean_inc(v_idx_3117_);
v___x_3125_ = lean_byte_array_size(v_array_3116_);
v___x_3126_ = lean_nat_dec_lt(v_idx_3117_, v___x_3125_);
if (v___x_3126_ == 0)
{
lean_object* v___x_3127_; 
lean_dec_ref(v_config_3091_);
v___x_3127_ = lean_box(0);
lean_inc(v_idx_3117_);
v_pos_3119_ = v_pos_3104_;
v_idx_3120_ = v_idx_3117_;
v_err_3121_ = v___x_3127_;
goto v___jp_3118_;
}
else
{
uint8_t v___x_3128_; uint8_t v_got_3129_; uint8_t v___x_3130_; 
v___x_3128_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3129_ = lean_byte_array_fget(v_array_3116_, v_idx_3117_);
v___x_3130_ = lean_uint8_dec_eq(v_got_3129_, v___x_3128_);
if (v___x_3130_ == 0)
{
lean_object* v___x_3131_; 
lean_dec_ref(v_config_3091_);
v___x_3131_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3117_);
v_pos_3119_ = v_pos_3104_;
v_idx_3120_ = v_idx_3117_;
v_err_3121_ = v___x_3131_;
goto v___jp_3118_;
}
else
{
lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3147_; 
lean_inc_ref(v_array_3116_);
v_isSharedCheck_3147_ = !lean_is_exclusive(v_pos_3104_);
if (v_isSharedCheck_3147_ == 0)
{
lean_object* v_unused_3148_; lean_object* v_unused_3149_; 
v_unused_3148_ = lean_ctor_get(v_pos_3104_, 1);
lean_dec(v_unused_3148_);
v_unused_3149_ = lean_ctor_get(v_pos_3104_, 0);
lean_dec(v_unused_3149_);
v___x_3133_ = v_pos_3104_;
v_isShared_3134_ = v_isSharedCheck_3147_;
goto v_resetjp_3132_;
}
else
{
lean_dec(v_pos_3104_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3147_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3138_; 
v___x_3135_ = lean_unsigned_to_nat(1u);
v___x_3136_ = lean_nat_add(v_idx_3117_, v___x_3135_);
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 1, v___x_3136_);
v___x_3138_ = v___x_3133_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_array_3116_);
lean_ctor_set(v_reuseFailAlloc_3146_, 1, v___x_3136_);
v___x_3138_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
lean_object* v___x_3139_; 
v___x_3139_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3091_, v___x_3138_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_pos_3140_; lean_object* v_res_3141_; lean_object* v___x_3142_; 
lean_dec(v_idx_3117_);
lean_dec_ref(v_a_3092_);
v_pos_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_pos_3140_);
v_res_3141_ = lean_ctor_get(v___x_3139_, 1);
lean_inc(v_res_3141_);
lean_dec_ref_known(v___x_3139_, 2);
v___x_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3142_, 0, v_res_3141_);
v_pos_3110_ = v_pos_3140_;
v_res_3111_ = v___x_3142_;
goto v___jp_3109_;
}
else
{
lean_object* v_pos_3143_; lean_object* v_err_3144_; lean_object* v_idx_3145_; 
v_pos_3143_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_pos_3143_);
v_err_3144_ = lean_ctor_get(v___x_3139_, 1);
lean_inc(v_err_3144_);
lean_dec_ref_known(v___x_3139_, 2);
v_idx_3145_ = lean_ctor_get(v_pos_3143_, 1);
lean_inc(v_idx_3145_);
v_pos_3119_ = v_pos_3143_;
v_idx_3120_ = v_idx_3145_;
v_err_3121_ = v_err_3144_;
goto v___jp_3118_;
}
}
}
}
}
v___jp_3109_:
{
lean_object* v___x_3112_; lean_object* v___x_3114_; 
v___x_3112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3112_, 0, v_res_3105_);
lean_ctor_set(v___x_3112_, 1, v_res_3111_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 1, v___x_3112_);
lean_ctor_set(v___x_3107_, 0, v_pos_3110_);
v___x_3114_ = v___x_3107_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_pos_3110_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v___x_3112_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
v___jp_3118_:
{
uint8_t v___x_3122_; 
v___x_3122_ = lean_nat_dec_eq(v_idx_3117_, v_idx_3120_);
lean_dec(v_idx_3120_);
lean_dec(v_idx_3117_);
if (v___x_3122_ == 0)
{
lean_object* v___x_3123_; 
lean_dec_ref(v_pos_3119_);
lean_del_object(v___x_3107_);
lean_dec(v_res_3105_);
v___x_3123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3123_, 0, v_a_3092_);
lean_ctor_set(v___x_3123_, 1, v_err_3121_);
return v___x_3123_;
}
else
{
lean_object* v___x_3124_; 
lean_dec(v_err_3121_);
lean_dec_ref(v_a_3092_);
v___x_3124_ = lean_box(0);
v_pos_3110_ = v_pos_3119_;
v_res_3111_ = v___x_3124_;
goto v___jp_3109_;
}
}
}
}
else
{
lean_object* v_err_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3158_; 
lean_dec_ref(v_config_3091_);
v_err_3151_ = lean_ctor_get(v___x_3103_, 1);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3158_ == 0)
{
lean_object* v_unused_3159_; 
v_unused_3159_ = lean_ctor_get(v___x_3103_, 0);
lean_dec(v_unused_3159_);
v___x_3153_ = v___x_3103_;
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_err_3151_);
lean_dec(v___x_3103_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3156_; 
if (v_isShared_3154_ == 0)
{
lean_ctor_set(v___x_3153_, 0, v_a_3092_);
v___x_3156_ = v___x_3153_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_a_3092_);
lean_ctor_set(v_reuseFailAlloc_3157_, 1, v_err_3151_);
v___x_3156_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
return v___x_3156_;
}
}
}
}
}
}
v___jp_3093_:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3094_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1));
v___x_3095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3095_, 0, v_a_3092_);
lean_ctor_set(v___x_3095_, 1, v___x_3094_);
return v___x_3095_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(lean_object* v_config_3160_, lean_object* v_scheme_3161_, lean_object* v_a_3162_){
_start:
{
lean_object* v_array_3163_; lean_object* v_idx_3164_; lean_object* v___x_3165_; uint8_t v___x_3166_; 
v_array_3163_ = lean_ctor_get(v_a_3162_, 0);
v_idx_3164_ = lean_ctor_get(v_a_3162_, 1);
v___x_3165_ = lean_byte_array_size(v_array_3163_);
v___x_3166_ = lean_nat_dec_lt(v_idx_3164_, v___x_3165_);
if (v___x_3166_ == 0)
{
lean_object* v___x_3167_; lean_object* v___x_3168_; 
lean_dec_ref(v_scheme_3161_);
lean_dec_ref(v_config_3160_);
v___x_3167_ = lean_box(0);
v___x_3168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3168_, 0, v_a_3162_);
lean_ctor_set(v___x_3168_, 1, v___x_3167_);
return v___x_3168_;
}
else
{
uint8_t v___x_3169_; uint8_t v_got_3170_; uint8_t v___x_3171_; 
v___x_3169_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v_got_3170_ = lean_byte_array_fget(v_array_3163_, v_idx_3164_);
v___x_3171_ = lean_uint8_dec_eq(v_got_3170_, v___x_3169_);
if (v___x_3171_ == 0)
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
lean_dec_ref(v_scheme_3161_);
lean_dec_ref(v_config_3160_);
v___x_3172_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
v___x_3173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3173_, 0, v_a_3162_);
lean_ctor_set(v___x_3173_, 1, v___x_3172_);
return v___x_3173_;
}
else
{
lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3247_; 
lean_inc(v_idx_3164_);
lean_inc_ref(v_array_3163_);
v_isSharedCheck_3247_ = !lean_is_exclusive(v_a_3162_);
if (v_isSharedCheck_3247_ == 0)
{
lean_object* v_unused_3248_; lean_object* v_unused_3249_; 
v_unused_3248_ = lean_ctor_get(v_a_3162_, 1);
lean_dec(v_unused_3248_);
v_unused_3249_ = lean_ctor_get(v_a_3162_, 0);
lean_dec(v_unused_3249_);
v___x_3175_ = v_a_3162_;
v_isShared_3176_ = v_isSharedCheck_3247_;
goto v_resetjp_3174_;
}
else
{
lean_dec(v_a_3162_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3247_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3180_; 
v___x_3177_ = lean_unsigned_to_nat(1u);
v___x_3178_ = lean_nat_add(v_idx_3164_, v___x_3177_);
lean_dec(v_idx_3164_);
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 1, v___x_3178_);
v___x_3180_ = v___x_3175_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_array_3163_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v___x_3178_);
v___x_3180_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
lean_object* v___x_3181_; 
lean_inc_ref(v_config_3160_);
v___x_3181_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3160_, v___x_3180_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_res_3182_; lean_object* v_pos_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3236_; 
v_res_3182_ = lean_ctor_get(v___x_3181_, 1);
v_pos_3183_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3185_ = v___x_3181_;
v_isShared_3186_ = v_isSharedCheck_3236_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_res_3182_);
lean_inc(v_pos_3183_);
lean_dec(v___x_3181_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3236_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v_fst_3187_; lean_object* v_snd_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3235_; 
v_fst_3187_ = lean_ctor_get(v_res_3182_, 0);
v_snd_3188_ = lean_ctor_get(v_res_3182_, 1);
v_isSharedCheck_3235_ = !lean_is_exclusive(v_res_3182_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3190_ = v_res_3182_;
v_isShared_3191_ = v_isSharedCheck_3235_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_snd_3188_);
lean_inc(v_fst_3187_);
lean_dec(v_res_3182_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3235_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v_array_3201_; lean_object* v_idx_3202_; lean_object* v_pos_3204_; lean_object* v_idx_3205_; lean_object* v_err_3206_; lean_object* v___x_3212_; uint8_t v___x_3213_; 
v_array_3201_ = lean_ctor_get(v_pos_3183_, 0);
v_idx_3202_ = lean_ctor_get(v_pos_3183_, 1);
lean_inc(v_idx_3202_);
v___x_3212_ = lean_byte_array_size(v_array_3201_);
v___x_3213_ = lean_nat_dec_lt(v_idx_3202_, v___x_3212_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; 
lean_dec_ref(v_config_3160_);
v___x_3214_ = lean_box(0);
lean_inc(v_idx_3202_);
v_pos_3204_ = v_pos_3183_;
v_idx_3205_ = v_idx_3202_;
v_err_3206_ = v___x_3214_;
goto v___jp_3203_;
}
else
{
uint8_t v___x_3215_; uint8_t v_got_3216_; uint8_t v___x_3217_; 
v___x_3215_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3216_ = lean_byte_array_fget(v_array_3201_, v_idx_3202_);
v___x_3217_ = lean_uint8_dec_eq(v_got_3216_, v___x_3215_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3218_; 
lean_dec_ref(v_config_3160_);
v___x_3218_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3202_);
v_pos_3204_ = v_pos_3183_;
v_idx_3205_ = v_idx_3202_;
v_err_3206_ = v___x_3218_;
goto v___jp_3203_;
}
else
{
lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3232_; 
lean_inc_ref(v_array_3201_);
v_isSharedCheck_3232_ = !lean_is_exclusive(v_pos_3183_);
if (v_isSharedCheck_3232_ == 0)
{
lean_object* v_unused_3233_; lean_object* v_unused_3234_; 
v_unused_3233_ = lean_ctor_get(v_pos_3183_, 1);
lean_dec(v_unused_3233_);
v_unused_3234_ = lean_ctor_get(v_pos_3183_, 0);
lean_dec(v_unused_3234_);
v___x_3220_ = v_pos_3183_;
v_isShared_3221_ = v_isSharedCheck_3232_;
goto v_resetjp_3219_;
}
else
{
lean_dec(v_pos_3183_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3232_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3222_; lean_object* v___x_3224_; 
v___x_3222_ = lean_nat_add(v_idx_3202_, v___x_3177_);
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 1, v___x_3222_);
v___x_3224_ = v___x_3220_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_array_3201_);
lean_ctor_set(v_reuseFailAlloc_3231_, 1, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
lean_object* v___x_3225_; 
v___x_3225_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3160_, v___x_3224_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_pos_3226_; lean_object* v_res_3227_; 
lean_dec(v_idx_3202_);
lean_del_object(v___x_3190_);
v_pos_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_pos_3226_);
v_res_3227_ = lean_ctor_get(v___x_3225_, 1);
lean_inc(v_res_3227_);
lean_dec_ref_known(v___x_3225_, 2);
v___y_3193_ = v_pos_3226_;
v___y_3194_ = v_res_3227_;
goto v___jp_3192_;
}
else
{
lean_object* v_pos_3228_; lean_object* v_err_3229_; lean_object* v_idx_3230_; 
v_pos_3228_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_pos_3228_);
v_err_3229_ = lean_ctor_get(v___x_3225_, 1);
lean_inc(v_err_3229_);
lean_dec_ref_known(v___x_3225_, 2);
v_idx_3230_ = lean_ctor_get(v_pos_3228_, 1);
lean_inc(v_idx_3230_);
v_pos_3204_ = v_pos_3228_;
v_idx_3205_ = v_idx_3230_;
v_err_3206_ = v_err_3229_;
goto v___jp_3203_;
}
}
}
}
}
v___jp_3192_:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3199_; 
v___x_3195_ = lean_box(0);
v___x_3196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3196_, 0, v_scheme_3161_);
lean_ctor_set(v___x_3196_, 1, v_fst_3187_);
lean_ctor_set(v___x_3196_, 2, v_snd_3188_);
lean_ctor_set(v___x_3196_, 3, v___y_3194_);
lean_ctor_set(v___x_3196_, 4, v___x_3195_);
v___x_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3196_);
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 1, v___x_3197_);
lean_ctor_set(v___x_3185_, 0, v___y_3193_);
v___x_3199_ = v___x_3185_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___y_3193_);
lean_ctor_set(v_reuseFailAlloc_3200_, 1, v___x_3197_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
v___jp_3203_:
{
uint8_t v___x_3207_; 
v___x_3207_ = lean_nat_dec_eq(v_idx_3202_, v_idx_3205_);
lean_dec(v_idx_3205_);
lean_dec(v_idx_3202_);
if (v___x_3207_ == 0)
{
lean_object* v___x_3209_; 
lean_dec(v_snd_3188_);
lean_dec(v_fst_3187_);
lean_del_object(v___x_3185_);
lean_dec_ref(v_scheme_3161_);
if (v_isShared_3191_ == 0)
{
lean_ctor_set_tag(v___x_3190_, 1);
lean_ctor_set(v___x_3190_, 1, v_err_3206_);
lean_ctor_set(v___x_3190_, 0, v_pos_3204_);
v___x_3209_ = v___x_3190_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_pos_3204_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v_err_3206_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
else
{
lean_object* v___x_3211_; 
lean_dec(v_err_3206_);
lean_del_object(v___x_3190_);
v___x_3211_ = l_Std_Http_URI_Query_empty;
v___y_3193_ = v_pos_3204_;
v___y_3194_ = v___x_3211_;
goto v___jp_3192_;
}
}
}
}
}
else
{
lean_object* v_pos_3237_; lean_object* v_err_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3245_; 
lean_dec_ref(v_scheme_3161_);
lean_dec_ref(v_config_3160_);
v_pos_3237_ = lean_ctor_get(v___x_3181_, 0);
v_err_3238_ = lean_ctor_get(v___x_3181_, 1);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3240_ = v___x_3181_;
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_err_3238_);
lean_inc(v_pos_3237_);
lean_dec(v___x_3181_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3243_; 
if (v_isShared_3241_ == 0)
{
v___x_3243_ = v___x_3240_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_pos_3237_);
lean_ctor_set(v_reuseFailAlloc_3244_, 1, v_err_3238_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(lean_object* v_config_3258_, lean_object* v_a_3259_){
_start:
{
lean_object* v___x_3263_; 
lean_inc_ref(v_a_3259_);
v___x_3263_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3258_, v_a_3259_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_object* v_pos_3264_; lean_object* v_res_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3361_; 
v_pos_3264_ = lean_ctor_get(v___x_3263_, 0);
v_res_3265_ = lean_ctor_get(v___x_3263_, 1);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3267_ = v___x_3263_;
v_isShared_3268_ = v_isSharedCheck_3361_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_res_3265_);
lean_inc(v_pos_3264_);
lean_dec(v___x_3263_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3361_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3281_; lean_object* v_idx_3282_; lean_object* v___y_3283_; lean_object* v_pos_3284_; lean_object* v_idx_3285_; lean_object* v_err_3286_; uint8_t v___y_3291_; lean_object* v___x_3357_; uint8_t v___x_3358_; 
v___x_3357_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__4));
v___x_3358_ = lean_string_dec_eq(v_res_3265_, v___x_3357_);
if (v___x_3358_ == 0)
{
lean_object* v___x_3359_; uint8_t v___x_3360_; 
v___x_3359_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5));
v___x_3360_ = lean_string_dec_eq(v_res_3265_, v___x_3359_);
v___y_3291_ = v___x_3360_;
goto v___jp_3290_;
}
else
{
v___y_3291_ = v___x_3358_;
goto v___jp_3290_;
}
v___jp_3269_:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3278_; 
v___x_3274_ = lean_box(0);
v___x_3275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3275_, 0, v_res_3265_);
lean_ctor_set(v___x_3275_, 1, v___y_3270_);
lean_ctor_set(v___x_3275_, 2, v___y_3272_);
lean_ctor_set(v___x_3275_, 3, v___y_3273_);
lean_ctor_set(v___x_3275_, 4, v___x_3274_);
v___x_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3275_);
if (v_isShared_3268_ == 0)
{
lean_ctor_set(v___x_3267_, 1, v___x_3276_);
lean_ctor_set(v___x_3267_, 0, v___y_3271_);
v___x_3278_ = v___x_3267_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v___y_3271_);
lean_ctor_set(v_reuseFailAlloc_3279_, 1, v___x_3276_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
v___jp_3280_:
{
uint8_t v___x_3287_; 
v___x_3287_ = lean_nat_dec_eq(v_idx_3282_, v_idx_3285_);
lean_dec(v_idx_3285_);
lean_dec(v_idx_3282_);
if (v___x_3287_ == 0)
{
lean_object* v___x_3288_; 
lean_dec_ref(v_pos_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3281_);
lean_del_object(v___x_3267_);
lean_dec(v_res_3265_);
v___x_3288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3288_, 0, v_a_3259_);
lean_ctor_set(v___x_3288_, 1, v_err_3286_);
return v___x_3288_;
}
else
{
lean_object* v___x_3289_; 
lean_dec(v_err_3286_);
lean_dec_ref(v_a_3259_);
v___x_3289_ = l_Std_Http_URI_Query_empty;
v___y_3270_ = v___y_3281_;
v___y_3271_ = v_pos_3284_;
v___y_3272_ = v___y_3283_;
v___y_3273_ = v___x_3289_;
goto v___jp_3269_;
}
}
v___jp_3290_:
{
if (v___y_3291_ == 0)
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
lean_del_object(v___x_3267_);
lean_dec(v_res_3265_);
lean_dec(v_pos_3264_);
lean_dec_ref(v_config_3258_);
v___x_3292_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3));
v___x_3293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3293_, 0, v_a_3259_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
return v___x_3293_;
}
else
{
lean_object* v_array_3294_; lean_object* v_idx_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3356_; 
v_array_3294_ = lean_ctor_get(v_pos_3264_, 0);
v_idx_3295_ = lean_ctor_get(v_pos_3264_, 1);
v_isSharedCheck_3356_ = !lean_is_exclusive(v_pos_3264_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3297_ = v_pos_3264_;
v_isShared_3298_ = v_isSharedCheck_3356_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_idx_3295_);
lean_inc(v_array_3294_);
lean_dec(v_pos_3264_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3356_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3299_; uint8_t v___x_3300_; 
v___x_3299_ = lean_byte_array_size(v_array_3294_);
v___x_3300_ = lean_nat_dec_lt(v_idx_3295_, v___x_3299_);
if (v___x_3300_ == 0)
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
lean_del_object(v___x_3297_);
lean_dec(v_idx_3295_);
lean_dec_ref(v_array_3294_);
lean_del_object(v___x_3267_);
lean_dec(v_res_3265_);
lean_dec_ref(v_config_3258_);
v___x_3301_ = lean_box(0);
v___x_3302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3302_, 0, v_a_3259_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
return v___x_3302_;
}
else
{
uint8_t v___x_3303_; uint8_t v_got_3304_; uint8_t v___x_3305_; 
v___x_3303_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v_got_3304_ = lean_byte_array_fget(v_array_3294_, v_idx_3295_);
v___x_3305_ = lean_uint8_dec_eq(v_got_3304_, v___x_3303_);
if (v___x_3305_ == 0)
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
lean_del_object(v___x_3297_);
lean_dec(v_idx_3295_);
lean_dec_ref(v_array_3294_);
lean_del_object(v___x_3267_);
lean_dec(v_res_3265_);
lean_dec_ref(v_config_3258_);
v___x_3306_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
v___x_3307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3307_, 0, v_a_3259_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
return v___x_3307_;
}
else
{
lean_object* v___x_3308_; lean_object* v___x_3309_; uint8_t v___x_3310_; 
v___x_3308_ = lean_unsigned_to_nat(1u);
v___x_3309_ = lean_nat_add(v_idx_3295_, v___x_3308_);
lean_dec(v_idx_3295_);
v___x_3310_ = lean_nat_dec_lt(v___x_3309_, v___x_3299_);
if (v___x_3310_ == 0)
{
lean_dec(v___x_3309_);
lean_del_object(v___x_3297_);
lean_dec_ref(v_array_3294_);
lean_del_object(v___x_3267_);
lean_dec(v_res_3265_);
lean_dec_ref(v_config_3258_);
goto v___jp_3260_;
}
else
{
uint8_t v___x_3311_; uint8_t v___x_3312_; uint8_t v___x_3313_; 
v___x_3311_ = lean_byte_array_fget(v_array_3294_, v___x_3309_);
v___x_3312_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_3313_ = lean_uint8_dec_eq(v___x_3311_, v___x_3312_);
if (v___x_3313_ == 0)
{
lean_dec(v___x_3309_);
lean_del_object(v___x_3297_);
lean_dec_ref(v_array_3294_);
lean_del_object(v___x_3267_);
lean_dec(v_res_3265_);
lean_dec_ref(v_config_3258_);
goto v___jp_3260_;
}
else
{
if (v___x_3313_ == 0)
{
lean_dec(v___x_3309_);
lean_del_object(v___x_3297_);
lean_dec_ref(v_array_3294_);
lean_del_object(v___x_3267_);
lean_dec(v_res_3265_);
lean_dec_ref(v_config_3258_);
goto v___jp_3260_;
}
else
{
lean_object* v___x_3315_; 
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 1, v___x_3309_);
v___x_3315_ = v___x_3297_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_array_3294_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v___x_3309_);
v___x_3315_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
lean_object* v___x_3316_; 
lean_inc_ref(v_config_3258_);
v___x_3316_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3258_, v___x_3315_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v_res_3317_; lean_object* v_pos_3318_; lean_object* v_fst_3319_; lean_object* v_snd_3320_; lean_object* v_array_3321_; lean_object* v_idx_3322_; lean_object* v___x_3323_; uint8_t v___x_3324_; 
v_res_3317_ = lean_ctor_get(v___x_3316_, 1);
lean_inc(v_res_3317_);
v_pos_3318_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_pos_3318_);
lean_dec_ref_known(v___x_3316_, 2);
v_fst_3319_ = lean_ctor_get(v_res_3317_, 0);
lean_inc(v_fst_3319_);
v_snd_3320_ = lean_ctor_get(v_res_3317_, 1);
lean_inc(v_snd_3320_);
lean_dec(v_res_3317_);
v_array_3321_ = lean_ctor_get(v_pos_3318_, 0);
v_idx_3322_ = lean_ctor_get(v_pos_3318_, 1);
lean_inc(v_idx_3322_);
v___x_3323_ = lean_byte_array_size(v_array_3321_);
v___x_3324_ = lean_nat_dec_lt(v_idx_3322_, v___x_3323_);
if (v___x_3324_ == 0)
{
lean_object* v___x_3325_; 
lean_dec_ref(v_config_3258_);
v___x_3325_ = lean_box(0);
lean_inc(v_idx_3322_);
v___y_3281_ = v_fst_3319_;
v_idx_3282_ = v_idx_3322_;
v___y_3283_ = v_snd_3320_;
v_pos_3284_ = v_pos_3318_;
v_idx_3285_ = v_idx_3322_;
v_err_3286_ = v___x_3325_;
goto v___jp_3280_;
}
else
{
uint8_t v___x_3326_; uint8_t v_got_3327_; uint8_t v___x_3328_; 
v___x_3326_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3327_ = lean_byte_array_fget(v_array_3321_, v_idx_3322_);
v___x_3328_ = lean_uint8_dec_eq(v_got_3327_, v___x_3326_);
if (v___x_3328_ == 0)
{
lean_object* v___x_3329_; 
lean_dec_ref(v_config_3258_);
v___x_3329_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3322_);
v___y_3281_ = v_fst_3319_;
v_idx_3282_ = v_idx_3322_;
v___y_3283_ = v_snd_3320_;
v_pos_3284_ = v_pos_3318_;
v_idx_3285_ = v_idx_3322_;
v_err_3286_ = v___x_3329_;
goto v___jp_3280_;
}
else
{
lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3343_; 
lean_inc_ref(v_array_3321_);
v_isSharedCheck_3343_ = !lean_is_exclusive(v_pos_3318_);
if (v_isSharedCheck_3343_ == 0)
{
lean_object* v_unused_3344_; lean_object* v_unused_3345_; 
v_unused_3344_ = lean_ctor_get(v_pos_3318_, 1);
lean_dec(v_unused_3344_);
v_unused_3345_ = lean_ctor_get(v_pos_3318_, 0);
lean_dec(v_unused_3345_);
v___x_3331_ = v_pos_3318_;
v_isShared_3332_ = v_isSharedCheck_3343_;
goto v_resetjp_3330_;
}
else
{
lean_dec(v_pos_3318_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3343_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3333_; lean_object* v___x_3335_; 
v___x_3333_ = lean_nat_add(v_idx_3322_, v___x_3308_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 1, v___x_3333_);
v___x_3335_ = v___x_3331_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_array_3321_);
lean_ctor_set(v_reuseFailAlloc_3342_, 1, v___x_3333_);
v___x_3335_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
lean_object* v___x_3336_; 
v___x_3336_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3258_, v___x_3335_);
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_object* v_pos_3337_; lean_object* v_res_3338_; 
lean_dec(v_idx_3322_);
lean_dec_ref(v_a_3259_);
v_pos_3337_ = lean_ctor_get(v___x_3336_, 0);
lean_inc(v_pos_3337_);
v_res_3338_ = lean_ctor_get(v___x_3336_, 1);
lean_inc(v_res_3338_);
lean_dec_ref_known(v___x_3336_, 2);
v___y_3270_ = v_fst_3319_;
v___y_3271_ = v_pos_3337_;
v___y_3272_ = v_snd_3320_;
v___y_3273_ = v_res_3338_;
goto v___jp_3269_;
}
else
{
lean_object* v_pos_3339_; lean_object* v_err_3340_; lean_object* v_idx_3341_; 
v_pos_3339_ = lean_ctor_get(v___x_3336_, 0);
lean_inc(v_pos_3339_);
v_err_3340_ = lean_ctor_get(v___x_3336_, 1);
lean_inc(v_err_3340_);
lean_dec_ref_known(v___x_3336_, 2);
v_idx_3341_ = lean_ctor_get(v_pos_3339_, 1);
lean_inc(v_idx_3341_);
v___y_3281_ = v_fst_3319_;
v_idx_3282_ = v_idx_3322_;
v___y_3283_ = v_snd_3320_;
v_pos_3284_ = v_pos_3339_;
v_idx_3285_ = v_idx_3341_;
v_err_3286_ = v_err_3340_;
goto v___jp_3280_;
}
}
}
}
}
}
else
{
lean_object* v_err_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
lean_del_object(v___x_3267_);
lean_dec(v_res_3265_);
lean_dec_ref(v_config_3258_);
v_err_3346_ = lean_ctor_get(v___x_3316_, 1);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3353_ == 0)
{
lean_object* v_unused_3354_; 
v_unused_3354_ = lean_ctor_get(v___x_3316_, 0);
lean_dec(v_unused_3354_);
v___x_3348_ = v___x_3316_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_err_3346_);
lean_dec(v___x_3316_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3351_; 
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 0, v_a_3259_);
v___x_3351_ = v___x_3348_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3259_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v_err_3346_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
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
lean_object* v_err_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
lean_dec_ref(v_config_3258_);
v_err_3362_ = lean_ctor_get(v___x_3263_, 1);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3369_ == 0)
{
lean_object* v_unused_3370_; 
v_unused_3370_ = lean_ctor_get(v___x_3263_, 0);
lean_dec(v_unused_3370_);
v___x_3364_ = v___x_3263_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_err_3362_);
lean_dec(v___x_3263_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 0, v_a_3259_);
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3259_);
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
v___jp_3260_:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3261_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1));
v___x_3262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3262_, 0, v_a_3259_);
lean_ctor_set(v___x_3262_, 1, v___x_3261_);
return v___x_3262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(lean_object* v_config_3371_, lean_object* v_a_3372_){
_start:
{
lean_object* v___x_3373_; 
lean_inc_ref(v_a_3372_);
v___x_3373_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3371_, v_a_3372_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_pos_3374_; lean_object* v_res_3375_; lean_object* v___x_3376_; 
v_pos_3374_ = lean_ctor_get(v___x_3373_, 0);
lean_inc(v_pos_3374_);
v_res_3375_ = lean_ctor_get(v___x_3373_, 1);
lean_inc(v_res_3375_);
lean_dec_ref_known(v___x_3373_, 2);
v___x_3376_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(v_config_3371_, v_res_3375_, v_pos_3374_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_dec_ref(v_a_3372_);
return v___x_3376_;
}
else
{
lean_object* v_err_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
v_err_3377_ = lean_ctor_get(v___x_3376_, 1);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3384_ == 0)
{
lean_object* v_unused_3385_; 
v_unused_3385_ = lean_ctor_get(v___x_3376_, 0);
lean_dec(v_unused_3385_);
v___x_3379_ = v___x_3376_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_err_3377_);
lean_dec(v___x_3376_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 0, v_a_3372_);
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3372_);
lean_ctor_set(v_reuseFailAlloc_3383_, 1, v_err_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
else
{
lean_object* v_err_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3393_; 
lean_dec_ref(v_config_3371_);
v_err_3386_ = lean_ctor_get(v___x_3373_, 1);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3393_ == 0)
{
lean_object* v_unused_3394_; 
v_unused_3394_ = lean_ctor_get(v___x_3373_, 0);
lean_dec(v_unused_3394_);
v___x_3388_ = v___x_3373_;
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_err_3386_);
lean_dec(v___x_3373_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3391_; 
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 0, v_a_3372_);
v___x_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3372_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_err_3386_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(lean_object* v_config_3395_, lean_object* v_a_3396_){
_start:
{
lean_object* v___x_3397_; 
lean_inc_ref(v_a_3396_);
v___x_3397_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3395_, v_a_3396_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_pos_3398_; lean_object* v_res_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3451_; 
v_pos_3398_ = lean_ctor_get(v___x_3397_, 0);
v_res_3399_ = lean_ctor_get(v___x_3397_, 1);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3401_ = v___x_3397_;
v_isShared_3402_ = v_isSharedCheck_3451_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_res_3399_);
lean_inc(v_pos_3398_);
lean_dec(v___x_3397_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3451_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v_array_3403_; lean_object* v_idx_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3450_; 
v_array_3403_ = lean_ctor_get(v_pos_3398_, 0);
v_idx_3404_ = lean_ctor_get(v_pos_3398_, 1);
v_isSharedCheck_3450_ = !lean_is_exclusive(v_pos_3398_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3406_ = v_pos_3398_;
v_isShared_3407_ = v_isSharedCheck_3450_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_idx_3404_);
lean_inc(v_array_3403_);
lean_dec(v_pos_3398_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3450_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3408_; uint8_t v___x_3409_; 
v___x_3408_ = lean_byte_array_size(v_array_3403_);
v___x_3409_ = lean_nat_dec_lt(v_idx_3404_, v___x_3408_);
if (v___x_3409_ == 0)
{
lean_object* v___x_3410_; lean_object* v___x_3412_; 
lean_del_object(v___x_3406_);
lean_dec(v_idx_3404_);
lean_dec_ref(v_array_3403_);
lean_dec(v_res_3399_);
v___x_3410_ = lean_box(0);
if (v_isShared_3402_ == 0)
{
lean_ctor_set_tag(v___x_3401_, 1);
lean_ctor_set(v___x_3401_, 1, v___x_3410_);
lean_ctor_set(v___x_3401_, 0, v_a_3396_);
v___x_3412_ = v___x_3401_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3396_);
lean_ctor_set(v_reuseFailAlloc_3413_, 1, v___x_3410_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
else
{
uint8_t v___x_3414_; uint8_t v_got_3415_; uint8_t v___x_3416_; 
v___x_3414_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v_got_3415_ = lean_byte_array_fget(v_array_3403_, v_idx_3404_);
v___x_3416_ = lean_uint8_dec_eq(v_got_3415_, v___x_3414_);
if (v___x_3416_ == 0)
{
lean_object* v___x_3417_; lean_object* v___x_3419_; 
lean_del_object(v___x_3406_);
lean_dec(v_idx_3404_);
lean_dec_ref(v_array_3403_);
lean_dec(v_res_3399_);
v___x_3417_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
if (v_isShared_3402_ == 0)
{
lean_ctor_set_tag(v___x_3401_, 1);
lean_ctor_set(v___x_3401_, 1, v___x_3417_);
lean_ctor_set(v___x_3401_, 0, v_a_3396_);
v___x_3419_ = v___x_3401_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3396_);
lean_ctor_set(v_reuseFailAlloc_3420_, 1, v___x_3417_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
else
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3424_; 
lean_del_object(v___x_3401_);
v___x_3421_ = lean_unsigned_to_nat(1u);
v___x_3422_ = lean_nat_add(v_idx_3404_, v___x_3421_);
lean_dec(v_idx_3404_);
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 1, v___x_3422_);
v___x_3424_ = v___x_3406_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_array_3403_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v___x_3422_);
v___x_3424_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
lean_object* v___x_3425_; 
v___x_3425_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_3424_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_pos_3426_; lean_object* v_res_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3439_; 
lean_dec_ref(v_a_3396_);
v_pos_3426_ = lean_ctor_get(v___x_3425_, 0);
v_res_3427_ = lean_ctor_get(v___x_3425_, 1);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3429_ = v___x_3425_;
v_isShared_3430_ = v_isSharedCheck_3439_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_res_3427_);
lean_inc(v_pos_3426_);
lean_dec(v___x_3425_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3439_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; uint16_t v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3437_; 
v___x_3431_ = lean_box(0);
v___x_3432_ = lean_alloc_ctor(2, 0, 2);
v___x_3433_ = lean_unbox(v_res_3427_);
lean_dec(v_res_3427_);
lean_ctor_set_uint16(v___x_3432_, 0, v___x_3433_);
v___x_3434_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3431_);
lean_ctor_set(v___x_3434_, 1, v_res_3399_);
lean_ctor_set(v___x_3434_, 2, v___x_3432_);
v___x_3435_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3434_);
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 1, v___x_3435_);
v___x_3437_ = v___x_3429_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_pos_3426_);
lean_ctor_set(v_reuseFailAlloc_3438_, 1, v___x_3435_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
else
{
lean_object* v_err_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
lean_dec(v_res_3399_);
v_err_3440_ = lean_ctor_get(v___x_3425_, 1);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3447_ == 0)
{
lean_object* v_unused_3448_; 
v_unused_3448_ = lean_ctor_get(v___x_3425_, 0);
lean_dec(v_unused_3448_);
v___x_3442_ = v___x_3425_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_err_3440_);
lean_dec(v___x_3425_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 0, v_a_3396_);
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3396_);
lean_ctor_set(v_reuseFailAlloc_3446_, 1, v_err_3440_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
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
lean_object* v_err_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3459_; 
v_err_3452_ = lean_ctor_get(v___x_3397_, 1);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3459_ == 0)
{
lean_object* v_unused_3460_; 
v_unused_3460_ = lean_ctor_get(v___x_3397_, 0);
lean_dec(v_unused_3460_);
v___x_3454_ = v___x_3397_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_err_3452_);
lean_dec(v___x_3397_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 0, v_a_3396_);
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_a_3396_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_err_3452_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority___boxed(lean_object* v_config_3461_, lean_object* v_a_3462_){
_start:
{
lean_object* v_res_3463_; 
v_res_3463_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3461_, v_a_3462_);
lean_dec_ref(v_config_3461_);
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object* v_config_3464_, lean_object* v_a_3465_){
_start:
{
lean_object* v___x_3466_; 
lean_inc_ref(v_a_3465_);
v___x_3466_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(v_a_3465_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_dec_ref(v_a_3465_);
lean_dec_ref(v_config_3464_);
return v___x_3466_;
}
else
{
lean_object* v_pos_3467_; lean_object* v_idx_3468_; lean_object* v_idx_3469_; uint8_t v___x_3470_; 
v_pos_3467_ = lean_ctor_get(v___x_3466_, 0);
lean_inc(v_pos_3467_);
v_idx_3468_ = lean_ctor_get(v_a_3465_, 1);
lean_inc(v_idx_3468_);
lean_dec_ref(v_a_3465_);
v_idx_3469_ = lean_ctor_get(v_pos_3467_, 1);
lean_inc(v_idx_3469_);
v___x_3470_ = lean_nat_dec_eq(v_idx_3468_, v_idx_3469_);
lean_dec(v_idx_3468_);
if (v___x_3470_ == 0)
{
lean_dec(v_idx_3469_);
lean_dec(v_pos_3467_);
lean_dec_ref(v_config_3464_);
return v___x_3466_;
}
else
{
lean_object* v___x_3471_; 
lean_dec_ref_known(v___x_3466_, 2);
lean_inc_ref(v_config_3464_);
v___x_3471_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(v_config_3464_, v_pos_3467_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_dec(v_idx_3469_);
lean_dec_ref(v_config_3464_);
return v___x_3471_;
}
else
{
lean_object* v_pos_3472_; lean_object* v_idx_3473_; uint8_t v___x_3474_; 
v_pos_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_pos_3472_);
v_idx_3473_ = lean_ctor_get(v_pos_3472_, 1);
lean_inc(v_idx_3473_);
v___x_3474_ = lean_nat_dec_eq(v_idx_3469_, v_idx_3473_);
lean_dec(v_idx_3469_);
if (v___x_3474_ == 0)
{
lean_dec(v_idx_3473_);
lean_dec(v_pos_3472_);
lean_dec_ref(v_config_3464_);
return v___x_3471_;
}
else
{
lean_object* v___x_3475_; 
lean_dec_ref_known(v___x_3471_, 2);
lean_inc_ref(v_config_3464_);
v___x_3475_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(v_config_3464_, v_pos_3472_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_dec(v_idx_3473_);
lean_dec_ref(v_config_3464_);
return v___x_3475_;
}
else
{
lean_object* v_pos_3476_; lean_object* v_idx_3477_; uint8_t v___x_3478_; 
v_pos_3476_ = lean_ctor_get(v___x_3475_, 0);
lean_inc(v_pos_3476_);
v_idx_3477_ = lean_ctor_get(v_pos_3476_, 1);
lean_inc(v_idx_3477_);
v___x_3478_ = lean_nat_dec_eq(v_idx_3473_, v_idx_3477_);
lean_dec(v_idx_3473_);
if (v___x_3478_ == 0)
{
lean_dec(v_idx_3477_);
lean_dec(v_pos_3476_);
lean_dec_ref(v_config_3464_);
return v___x_3475_;
}
else
{
lean_object* v___x_3479_; 
lean_dec_ref_known(v___x_3475_, 2);
v___x_3479_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3464_, v_pos_3476_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_dec(v_idx_3477_);
lean_dec_ref(v_config_3464_);
return v___x_3479_;
}
else
{
lean_object* v_pos_3480_; lean_object* v_idx_3481_; uint8_t v___x_3482_; 
v_pos_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_pos_3480_);
v_idx_3481_ = lean_ctor_get(v_pos_3480_, 1);
v___x_3482_ = lean_nat_dec_eq(v_idx_3477_, v_idx_3481_);
lean_dec(v_idx_3477_);
if (v___x_3482_ == 0)
{
lean_dec(v_pos_3480_);
lean_dec_ref(v_config_3464_);
return v___x_3479_;
}
else
{
lean_object* v___x_3483_; 
lean_dec_ref_known(v___x_3479_, 2);
v___x_3483_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(v_config_3464_, v_pos_3480_);
return v___x_3483_;
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
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader(lean_object* v_config_3490_, lean_object* v_a_3491_){
_start:
{
lean_object* v___y_3493_; lean_object* v___x_3496_; 
v___x_3496_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3490_, v_a_3491_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_pos_3497_; lean_object* v_res_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3571_; 
v_pos_3497_ = lean_ctor_get(v___x_3496_, 0);
v_res_3498_ = lean_ctor_get(v___x_3496_, 1);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3500_ = v___x_3496_;
v_isShared_3501_ = v_isSharedCheck_3571_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_res_3498_);
lean_inc(v_pos_3497_);
lean_dec(v___x_3496_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3571_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v_port_3503_; lean_object* v___y_3504_; lean_object* v_pos_3518_; lean_object* v_array_3520_; lean_object* v_idx_3521_; lean_object* v___x_3522_; uint8_t v___x_3523_; lean_object* v___y_3525_; lean_object* v_array_3526_; lean_object* v_idx_3527_; 
v_array_3520_ = lean_ctor_get(v_pos_3497_, 0);
v_idx_3521_ = lean_ctor_get(v_pos_3497_, 1);
v___x_3522_ = lean_byte_array_size(v_array_3520_);
v___x_3523_ = lean_nat_dec_lt(v_idx_3521_, v___x_3522_);
if (v___x_3523_ == 0)
{
v_pos_3518_ = v_pos_3497_;
goto v___jp_3517_;
}
else
{
uint8_t v___x_3531_; uint8_t v___x_3532_; uint8_t v___x_3533_; 
v___x_3531_ = lean_byte_array_fget(v_array_3520_, v_idx_3521_);
v___x_3532_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_3533_ = lean_uint8_dec_eq(v___x_3531_, v___x_3532_);
if (v___x_3533_ == 0)
{
v_pos_3518_ = v_pos_3497_;
goto v___jp_3517_;
}
else
{
if (v___x_3533_ == 0)
{
v_pos_3518_ = v_pos_3497_;
goto v___jp_3517_;
}
else
{
if (v___x_3523_ == 0)
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
lean_del_object(v___x_3500_);
lean_dec(v_res_3498_);
v___x_3534_ = lean_box(0);
v___x_3535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3535_, 0, v_pos_3497_);
lean_ctor_set(v___x_3535_, 1, v___x_3534_);
return v___x_3535_;
}
else
{
if (v___x_3533_ == 0)
{
lean_object* v___x_3536_; lean_object* v___x_3537_; 
lean_del_object(v___x_3500_);
lean_dec(v_res_3498_);
v___x_3536_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
v___x_3537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3537_, 0, v_pos_3497_);
lean_ctor_set(v___x_3537_, 1, v___x_3536_);
return v___x_3537_;
}
else
{
lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3568_; 
lean_inc(v_idx_3521_);
lean_inc_ref(v_array_3520_);
v_isSharedCheck_3568_ = !lean_is_exclusive(v_pos_3497_);
if (v_isSharedCheck_3568_ == 0)
{
lean_object* v_unused_3569_; lean_object* v_unused_3570_; 
v_unused_3569_ = lean_ctor_get(v_pos_3497_, 1);
lean_dec(v_unused_3569_);
v_unused_3570_ = lean_ctor_get(v_pos_3497_, 0);
lean_dec(v_unused_3570_);
v___x_3539_ = v_pos_3497_;
v_isShared_3540_ = v_isSharedCheck_3568_;
goto v_resetjp_3538_;
}
else
{
lean_dec(v_pos_3497_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3568_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3544_; 
v___x_3541_ = lean_unsigned_to_nat(1u);
v___x_3542_ = lean_nat_add(v_idx_3521_, v___x_3541_);
lean_dec(v_idx_3521_);
lean_inc(v___x_3542_);
lean_inc_ref(v_array_3520_);
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 1, v___x_3542_);
v___x_3544_ = v___x_3539_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_array_3520_);
lean_ctor_set(v_reuseFailAlloc_3567_, 1, v___x_3542_);
v___x_3544_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
uint8_t v___y_3546_; uint8_t v___x_3561_; 
v___x_3561_ = lean_nat_dec_lt(v___x_3542_, v___x_3522_);
if (v___x_3561_ == 0)
{
v___y_3525_ = v___x_3544_;
v_array_3526_ = v_array_3520_;
v_idx_3527_ = v___x_3542_;
goto v___jp_3524_;
}
else
{
uint8_t v___x_3562_; uint8_t v___x_3563_; uint8_t v___x_3564_; 
v___x_3562_ = lean_byte_array_fget(v_array_3520_, v___x_3542_);
v___x_3563_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_3564_ = lean_uint8_dec_le(v___x_3563_, v___x_3562_);
if (v___x_3564_ == 0)
{
v___y_3546_ = v___x_3564_;
goto v___jp_3545_;
}
else
{
uint8_t v___x_3565_; uint8_t v___x_3566_; 
v___x_3565_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_3566_ = lean_uint8_dec_le(v___x_3562_, v___x_3565_);
v___y_3546_ = v___x_3566_;
goto v___jp_3545_;
}
}
v___jp_3545_:
{
if (v___y_3546_ == 0)
{
v___y_3525_ = v___x_3544_;
v_array_3526_ = v_array_3520_;
v_idx_3527_ = v___x_3542_;
goto v___jp_3524_;
}
else
{
if (v___x_3523_ == 0)
{
v___y_3525_ = v___x_3544_;
v_array_3526_ = v_array_3520_;
v_idx_3527_ = v___x_3542_;
goto v___jp_3524_;
}
else
{
lean_object* v___x_3547_; 
lean_dec(v___x_3542_);
lean_dec_ref(v_array_3520_);
v___x_3547_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_3544_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_pos_3548_; lean_object* v_res_3549_; lean_object* v___x_3550_; uint16_t v___x_3551_; 
v_pos_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_pos_3548_);
v_res_3549_ = lean_ctor_get(v___x_3547_, 1);
lean_inc(v_res_3549_);
lean_dec_ref_known(v___x_3547_, 2);
v___x_3550_ = lean_alloc_ctor(2, 0, 2);
v___x_3551_ = lean_unbox(v_res_3549_);
lean_dec(v_res_3549_);
lean_ctor_set_uint16(v___x_3550_, 0, v___x_3551_);
v_port_3503_ = v___x_3550_;
v___y_3504_ = v_pos_3548_;
goto v___jp_3502_;
}
else
{
lean_object* v_pos_3552_; lean_object* v_err_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
lean_del_object(v___x_3500_);
lean_dec(v_res_3498_);
v_pos_3552_ = lean_ctor_get(v___x_3547_, 0);
v_err_3553_ = lean_ctor_get(v___x_3547_, 1);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3547_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_err_3553_);
lean_inc(v_pos_3552_);
lean_dec(v___x_3547_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_pos_3552_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v_err_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
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
v___jp_3502_:
{
lean_object* v_array_3505_; lean_object* v_idx_3506_; lean_object* v___x_3507_; uint8_t v___x_3508_; 
v_array_3505_ = lean_ctor_get(v___y_3504_, 0);
v_idx_3506_ = lean_ctor_get(v___y_3504_, 1);
v___x_3507_ = lean_byte_array_size(v_array_3505_);
v___x_3508_ = lean_nat_dec_lt(v_idx_3506_, v___x_3507_);
if (v___x_3508_ == 0)
{
lean_object* v___x_3509_; lean_object* v___x_3511_; 
v___x_3509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3509_, 0, v_res_3498_);
lean_ctor_set(v___x_3509_, 1, v_port_3503_);
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 1, v___x_3509_);
lean_ctor_set(v___x_3500_, 0, v___y_3504_);
v___x_3511_ = v___x_3500_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v___y_3504_);
lean_ctor_set(v_reuseFailAlloc_3512_, 1, v___x_3509_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
else
{
lean_object* v___x_3513_; lean_object* v___x_3515_; 
lean_dec(v_port_3503_);
lean_dec(v_res_3498_);
v___x_3513_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__3));
if (v_isShared_3501_ == 0)
{
lean_ctor_set_tag(v___x_3500_, 1);
lean_ctor_set(v___x_3500_, 1, v___x_3513_);
lean_ctor_set(v___x_3500_, 0, v___y_3504_);
v___x_3515_ = v___x_3500_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___y_3504_);
lean_ctor_set(v_reuseFailAlloc_3516_, 1, v___x_3513_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
v___jp_3517_:
{
lean_object* v___x_3519_; 
v___x_3519_ = lean_box(0);
v_port_3503_ = v___x_3519_;
v___y_3504_ = v_pos_3518_;
goto v___jp_3502_;
}
v___jp_3524_:
{
lean_object* v___x_3528_; uint8_t v___x_3529_; 
v___x_3528_ = lean_byte_array_size(v_array_3526_);
lean_dec_ref(v_array_3526_);
v___x_3529_ = lean_nat_dec_lt(v_idx_3527_, v___x_3528_);
lean_dec(v_idx_3527_);
if (v___x_3529_ == 0)
{
if (v___x_3523_ == 0)
{
lean_del_object(v___x_3500_);
lean_dec(v_res_3498_);
v___y_3493_ = v___y_3525_;
goto v___jp_3492_;
}
else
{
lean_object* v___x_3530_; 
v___x_3530_ = lean_box(1);
v_port_3503_ = v___x_3530_;
v___y_3504_ = v___y_3525_;
goto v___jp_3502_;
}
}
else
{
lean_del_object(v___x_3500_);
lean_dec(v_res_3498_);
v___y_3493_ = v___y_3525_;
goto v___jp_3492_;
}
}
}
}
else
{
lean_object* v_pos_3572_; lean_object* v_err_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3580_; 
v_pos_3572_ = lean_ctor_get(v___x_3496_, 0);
v_err_3573_ = lean_ctor_get(v___x_3496_, 1);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3575_ = v___x_3496_;
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_err_3573_);
lean_inc(v_pos_3572_);
lean_dec(v___x_3496_);
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
v___jp_3492_:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3494_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__1));
v___x_3495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___y_3493_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
return v___x_3495_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader___boxed(lean_object* v_config_3581_, lean_object* v_a_3582_){
_start:
{
lean_object* v_res_3583_; 
v_res_3583_ = l_Std_Http_URI_Parser_parseHostHeader(v_config_3581_, v_a_3582_);
lean_dec_ref(v_config_3581_);
return v_res_3583_;
}
}
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec_ByteArray(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_URI_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_URI_Config(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_URI_Parser(uint8_t builtin) {
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
