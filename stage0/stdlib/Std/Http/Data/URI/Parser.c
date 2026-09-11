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
uint8_t lean_uint32_to_uint8(uint32_t);
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
lean_object* v___y_219_; lean_object* v___y_223_; lean_object* v___y_224_; uint8_t v___y_225_; uint8_t v___y_226_; uint8_t v___y_229_; lean_object* v___y_230_; lean_object* v___y_231_; uint8_t v___y_232_; uint8_t v___y_233_; uint32_t v___y_235_; uint8_t v___y_236_; lean_object* v___y_237_; lean_object* v___y_238_; uint8_t v___y_239_; uint8_t v___y_240_; lean_object* v_maxSchemeLength_245_; lean_object* v___x_246_; uint8_t v___x_247_; lean_object* v___y_249_; lean_object* v___y_250_; uint8_t v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v_lower_269_; lean_object* v_upper_270_; lean_object* v___y_283_; uint8_t v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; 
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
v___y_284_ = v_res_299_;
v___y_285_ = v_fst_305_;
v___y_286_ = v___x_308_;
v___y_287_ = v_array_306_;
v___y_288_ = v_idx_307_;
goto v___jp_282_;
}
else
{
lean_dec(v_idx_307_);
v___y_283_ = v___x_309_;
v___y_284_ = v_res_299_;
v___y_285_ = v_fst_305_;
v___y_286_ = v___x_308_;
v___y_287_ = v_array_306_;
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
v___x_271_ = l_ByteArray_toByteSlice(v___y_268_, v_lower_269_, v_upper_270_);
v___x_272_ = l_ByteArray_empty;
v___x_273_ = lean_byte_array_push(v___x_272_, v___y_266_);
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
v___y_249_ = v___y_267_;
v___y_250_ = v___x_280_;
goto v___jp_248_;
}
else
{
lean_object* v___x_281_; 
v___x_281_ = lean_string_from_utf8_unchecked(v___x_277_);
v___y_249_ = v___y_267_;
v___y_250_ = v___x_281_;
goto v___jp_248_;
}
}
v___jp_282_:
{
uint8_t v___x_289_; 
v___x_289_ = lean_nat_dec_le(v___y_286_, v___y_283_);
if (v___x_289_ == 0)
{
lean_dec(v___y_286_);
v___y_266_ = v___y_284_;
v___y_267_ = v___y_285_;
v___y_268_ = v___y_287_;
v_lower_269_ = v___y_288_;
v_upper_270_ = v___y_283_;
goto v___jp_265_;
}
else
{
lean_dec(v___y_283_);
v___y_266_ = v___y_284_;
v___y_267_ = v___y_285_;
v___y_268_ = v___y_287_;
v_lower_269_ = v___y_288_;
v_upper_270_ = v___y_286_;
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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg(){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___boxed(lean_object* v___dummy_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg();
return v_res_883_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0(void){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg();
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(lean_object* v_s_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___boxed(lean_object* v_s_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(v_s_887_);
lean_dec_ref(v_s_887_);
return v_res_888_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(uint8_t v_x_889_){
_start:
{
uint8_t v___y_891_; uint8_t v___x_906_; uint8_t v___x_907_; 
v___x_906_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_907_ = lean_uint8_dec_le(v___x_906_, v_x_889_);
if (v___x_907_ == 0)
{
goto v___jp_901_;
}
else
{
uint8_t v___x_908_; uint8_t v___x_909_; 
v___x_908_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_909_ = lean_uint8_dec_le(v_x_889_, v___x_908_);
if (v___x_909_ == 0)
{
goto v___jp_901_;
}
else
{
v___y_891_ = v___x_909_;
goto v___jp_890_;
}
}
v___jp_890_:
{
uint8_t v___x_892_; uint8_t v___x_893_; 
v___x_892_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_893_ = lean_uint8_dec_eq(v_x_889_, v___x_892_);
if (v___x_893_ == 0)
{
if (v___y_891_ == 0)
{
uint8_t v___x_894_; uint8_t v___x_895_; 
v___x_894_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_895_ = lean_uint8_dec_eq(v_x_889_, v___x_894_);
return v___x_895_;
}
else
{
return v___y_891_;
}
}
else
{
if (v___y_891_ == 0)
{
return v___x_893_;
}
else
{
return v___y_891_;
}
}
}
v___jp_896_:
{
uint8_t v___x_897_; uint8_t v___x_898_; 
v___x_897_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_898_ = lean_uint8_dec_le(v___x_897_, v_x_889_);
if (v___x_898_ == 0)
{
v___y_891_ = v___x_898_;
goto v___jp_890_;
}
else
{
uint8_t v___x_899_; uint8_t v___x_900_; 
v___x_899_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_900_ = lean_uint8_dec_le(v_x_889_, v___x_899_);
v___y_891_ = v___x_900_;
goto v___jp_890_;
}
}
v___jp_901_:
{
uint8_t v___x_902_; uint8_t v___x_903_; 
v___x_902_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_903_ = lean_uint8_dec_le(v___x_902_, v_x_889_);
if (v___x_903_ == 0)
{
goto v___jp_896_;
}
else
{
uint8_t v___x_904_; uint8_t v___x_905_; 
v___x_904_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_905_ = lean_uint8_dec_le(v_x_889_, v___x_904_);
if (v___x_905_ == 0)
{
goto v___jp_896_;
}
else
{
v___y_891_ = v___x_905_;
goto v___jp_890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed(lean_object* v_x_910_){
_start:
{
uint8_t v_x_boxed_911_; uint8_t v_res_912_; lean_object* v_r_913_; 
v_x_boxed_911_ = lean_unbox(v_x_910_);
v_res_912_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(v_x_boxed_911_);
v_r_913_ = lean_box(v_res_912_);
return v_r_913_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1___redArg(lean_object* v___x_914_, lean_object* v_a_915_, uint8_t v_b_916_){
_start:
{
if (lean_obj_tag(v_a_915_) == 0)
{
lean_object* v_currPos_917_; lean_object* v_searcher_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_938_; 
v_currPos_917_ = lean_ctor_get(v_a_915_, 0);
v_searcher_918_ = lean_ctor_get(v_a_915_, 1);
v_isSharedCheck_938_ = !lean_is_exclusive(v_a_915_);
if (v_isSharedCheck_938_ == 0)
{
v___x_920_ = v_a_915_;
v_isShared_921_ = v_isSharedCheck_938_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_searcher_918_);
lean_inc(v_currPos_917_);
lean_dec(v_a_915_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_938_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v_str_922_; lean_object* v_startInclusive_923_; lean_object* v_endExclusive_924_; uint8_t v___x_925_; lean_object* v___x_926_; uint8_t v_decide_927_; 
v_str_922_ = lean_ctor_get(v___x_914_, 0);
v_startInclusive_923_ = lean_ctor_get(v___x_914_, 1);
v_endExclusive_924_ = lean_ctor_get(v___x_914_, 2);
v___x_925_ = 0;
v___x_926_ = lean_nat_sub(v_endExclusive_924_, v_startInclusive_923_);
v_decide_927_ = lean_nat_dec_eq(v_searcher_918_, v___x_926_);
lean_dec(v___x_926_);
if (v_decide_927_ == 0)
{
uint32_t v___x_928_; lean_object* v___x_929_; uint32_t v___x_930_; uint8_t v___x_931_; 
v___x_928_ = 46;
v___x_929_ = lean_nat_add(v_startInclusive_923_, v_searcher_918_);
lean_dec(v_searcher_918_);
v___x_930_ = lean_string_utf8_get_fast(v_str_922_, v___x_929_);
v___x_931_ = lean_uint32_dec_eq(v___x_930_, v___x_928_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_932_ = lean_string_utf8_next_fast(v_str_922_, v___x_929_);
lean_dec(v___x_929_);
v___x_933_ = lean_nat_sub(v___x_932_, v_startInclusive_923_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 1, v___x_933_);
v___x_935_ = v___x_920_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_currPos_917_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v___x_933_);
v___x_935_ = v_reuseFailAlloc_937_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
v_a_915_ = v___x_935_;
goto _start;
}
}
else
{
lean_dec(v___x_929_);
lean_del_object(v___x_920_);
lean_dec(v_currPos_917_);
return v___x_925_;
}
}
else
{
lean_del_object(v___x_920_);
lean_dec(v_searcher_918_);
lean_dec(v_currPos_917_);
return v___x_925_;
}
}
}
else
{
return v_b_916_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1___redArg___boxed(lean_object* v___x_939_, lean_object* v_a_940_, lean_object* v_b_941_){
_start:
{
uint8_t v_b_boxed_942_; uint8_t v_res_943_; lean_object* v_r_944_; 
v_b_boxed_942_ = lean_unbox(v_b_941_);
v_res_943_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1___redArg(v___x_939_, v_a_940_, v_b_boxed_942_);
lean_dec_ref(v___x_939_);
v_r_944_ = lean_box(v_res_943_);
return v_r_944_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(lean_object* v___x_945_, lean_object* v___x_946_, lean_object* v___x_947_, lean_object* v_a_948_, uint8_t v_b_949_){
_start:
{
if (lean_obj_tag(v_a_948_) == 0)
{
lean_object* v_currPos_950_; lean_object* v_searcher_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_971_; 
v_currPos_950_ = lean_ctor_get(v_a_948_, 0);
v_searcher_951_ = lean_ctor_get(v_a_948_, 1);
v_isSharedCheck_971_ = !lean_is_exclusive(v_a_948_);
if (v_isSharedCheck_971_ == 0)
{
v___x_953_ = v_a_948_;
v_isShared_954_ = v_isSharedCheck_971_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_searcher_951_);
lean_inc(v_currPos_950_);
lean_dec(v_a_948_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_971_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v_str_955_; lean_object* v_startInclusive_956_; lean_object* v_endExclusive_957_; uint8_t v___x_958_; lean_object* v___x_959_; uint8_t v_decide_960_; 
v_str_955_ = lean_ctor_get(v___x_946_, 0);
v_startInclusive_956_ = lean_ctor_get(v___x_946_, 1);
v_endExclusive_957_ = lean_ctor_get(v___x_946_, 2);
v___x_958_ = 0;
v___x_959_ = lean_nat_sub(v_endExclusive_957_, v_startInclusive_956_);
v_decide_960_ = lean_nat_dec_eq(v_searcher_951_, v___x_959_);
lean_dec(v___x_959_);
if (v_decide_960_ == 0)
{
lean_object* v___x_961_; uint32_t v___x_962_; uint32_t v___x_963_; uint8_t v___x_964_; 
v___x_961_ = lean_nat_add(v_startInclusive_956_, v_searcher_951_);
lean_dec(v_searcher_951_);
v___x_962_ = lean_string_utf8_get_fast(v_str_955_, v___x_961_);
v___x_963_ = 46;
v___x_964_ = lean_uint32_dec_eq(v___x_962_, v___x_963_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_965_ = lean_string_utf8_next_fast(v_str_955_, v___x_961_);
lean_dec(v___x_961_);
v___x_966_ = lean_nat_sub(v___x_965_, v_startInclusive_956_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v___x_966_);
v___x_968_ = v___x_953_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_currPos_950_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v___x_966_);
v___x_968_ = v_reuseFailAlloc_970_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
uint8_t v___x_969_; 
v___x_969_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1___redArg(v___x_946_, v___x_968_, v_b_949_);
return v___x_969_;
}
}
else
{
lean_dec(v___x_961_);
lean_del_object(v___x_953_);
lean_dec(v_currPos_950_);
return v___x_958_;
}
}
else
{
lean_del_object(v___x_953_);
lean_dec(v_searcher_951_);
lean_dec(v_currPos_950_);
return v___x_958_;
}
}
}
else
{
return v_b_949_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg___boxed(lean_object* v___x_972_, lean_object* v___x_973_, lean_object* v___x_974_, lean_object* v_a_975_, lean_object* v_b_976_){
_start:
{
uint8_t v_b_boxed_977_; uint8_t v_res_978_; lean_object* v_r_979_; 
v_b_boxed_977_ = lean_unbox(v_b_976_);
v_res_978_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_972_, v___x_973_, v___x_974_, v_a_975_, v_b_boxed_977_);
lean_dec(v___x_974_);
lean_dec_ref(v___x_973_);
lean_dec_ref(v___x_972_);
v_r_979_ = lean_box(v_res_978_);
return v_r_979_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___redArg(uint8_t v___x_980_, lean_object* v___x_981_, lean_object* v___x_982_, lean_object* v___x_983_, lean_object* v_a_984_, uint8_t v_b_985_){
_start:
{
lean_object* v_it_987_; lean_object* v_startInclusive_988_; lean_object* v_endExclusive_989_; 
if (lean_obj_tag(v_a_984_) == 0)
{
lean_object* v_currPos_993_; lean_object* v_searcher_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1023_; 
v_currPos_993_ = lean_ctor_get(v_a_984_, 0);
v_searcher_994_ = lean_ctor_get(v_a_984_, 1);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_a_984_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_996_ = v_a_984_;
v_isShared_997_ = v_isSharedCheck_1023_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_searcher_994_);
lean_inc(v_currPos_993_);
lean_dec(v_a_984_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1023_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v_str_998_; lean_object* v_startInclusive_999_; lean_object* v_endExclusive_1000_; lean_object* v___x_1001_; uint8_t v_decide_1002_; 
v_str_998_ = lean_ctor_get(v___x_982_, 0);
v_startInclusive_999_ = lean_ctor_get(v___x_982_, 1);
v_endExclusive_1000_ = lean_ctor_get(v___x_982_, 2);
v___x_1001_ = lean_nat_sub(v_endExclusive_1000_, v_startInclusive_999_);
v_decide_1002_ = lean_nat_dec_eq(v_searcher_994_, v___x_1001_);
lean_dec(v___x_1001_);
if (v_decide_1002_ == 0)
{
uint32_t v___x_1003_; lean_object* v___x_1004_; uint32_t v___x_1005_; uint8_t v___x_1006_; 
v___x_1003_ = 46;
v___x_1004_ = lean_nat_add(v_startInclusive_999_, v_searcher_994_);
v___x_1005_ = lean_string_utf8_get_fast(v_str_998_, v___x_1004_);
v___x_1006_ = lean_uint32_dec_eq(v___x_1005_, v___x_1003_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1010_; 
lean_dec(v_searcher_994_);
v___x_1007_ = lean_string_utf8_next_fast(v_str_998_, v___x_1004_);
lean_dec(v___x_1004_);
v___x_1008_ = lean_nat_sub(v___x_1007_, v_startInclusive_999_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 1, v___x_1008_);
v___x_1010_ = v___x_996_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_currPos_993_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
v_a_984_ = v___x_1010_;
goto _start;
}
}
else
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v_slice_1016_; lean_object* v_nextIt_1018_; 
v___x_1013_ = lean_string_utf8_next_fast(v_str_998_, v___x_1004_);
v___x_1014_ = lean_nat_sub(v___x_1013_, v___x_1004_);
lean_dec(v___x_1004_);
v___x_1015_ = lean_nat_add(v_searcher_994_, v___x_1014_);
lean_dec(v___x_1014_);
v_slice_1016_ = l_String_Slice_subslice_x21(v___x_982_, v_currPos_993_, v_searcher_994_);
lean_inc(v___x_1015_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 1, v___x_1015_);
lean_ctor_set(v___x_996_, 0, v___x_1015_);
v_nextIt_1018_ = v___x_996_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v___x_1015_);
v_nextIt_1018_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
lean_object* v_startInclusive_1019_; lean_object* v_endExclusive_1020_; 
v_startInclusive_1019_ = lean_ctor_get(v_slice_1016_, 0);
lean_inc(v_startInclusive_1019_);
v_endExclusive_1020_ = lean_ctor_get(v_slice_1016_, 1);
lean_inc(v_endExclusive_1020_);
lean_dec_ref(v_slice_1016_);
v_it_987_ = v_nextIt_1018_;
v_startInclusive_988_ = v_startInclusive_1019_;
v_endExclusive_989_ = v_endExclusive_1020_;
goto v___jp_986_;
}
}
}
else
{
lean_object* v___x_1022_; 
lean_del_object(v___x_996_);
lean_dec(v_searcher_994_);
v___x_1022_ = lean_box(1);
lean_inc(v___x_983_);
v_it_987_ = v___x_1022_;
v_startInclusive_988_ = v_currPos_993_;
v_endExclusive_989_ = v___x_983_;
goto v___jp_986_;
}
}
}
else
{
lean_dec(v___x_983_);
return v_b_985_;
}
v___jp_986_:
{
lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_990_ = lean_string_utf8_extract_fast(v___x_981_, v_startInclusive_988_, v_endExclusive_989_);
lean_dec(v_endExclusive_989_);
lean_dec(v_startInclusive_988_);
v___x_991_ = l_Std_Http_URI_isValidDomainLabel(v___x_990_);
if (v___x_991_ == 0)
{
lean_dec(v_it_987_);
lean_dec(v___x_983_);
return v___x_991_;
}
else
{
{
lean_object* _tmp_4 = v_it_987_;
uint8_t _tmp_5 = v___x_980_;
v_a_984_ = _tmp_4;
v_b_985_ = _tmp_5;
}
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___redArg___boxed(lean_object* v___x_1024_, lean_object* v___x_1025_, lean_object* v___x_1026_, lean_object* v___x_1027_, lean_object* v_a_1028_, lean_object* v_b_1029_){
_start:
{
uint8_t v___x_10848__boxed_1030_; uint8_t v_b_boxed_1031_; uint8_t v_res_1032_; lean_object* v_r_1033_; 
v___x_10848__boxed_1030_ = lean_unbox(v___x_1024_);
v_b_boxed_1031_ = lean_unbox(v_b_1029_);
v_res_1032_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___redArg(v___x_10848__boxed_1030_, v___x_1025_, v___x_1026_, v___x_1027_, v_a_1028_, v_b_boxed_1031_);
lean_dec_ref(v___x_1026_);
lean_dec_ref(v___x_1025_);
v_r_1033_ = lean_box(v_res_1032_);
return v_r_1033_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(uint8_t v___x_1034_, lean_object* v___x_1035_, lean_object* v___x_1036_, lean_object* v___x_1037_, lean_object* v_a_1038_, uint8_t v_b_1039_){
_start:
{
lean_object* v_it_1041_; lean_object* v_startInclusive_1042_; lean_object* v_endExclusive_1043_; 
if (lean_obj_tag(v_a_1038_) == 0)
{
lean_object* v_currPos_1047_; lean_object* v_searcher_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1077_; 
v_currPos_1047_ = lean_ctor_get(v_a_1038_, 0);
v_searcher_1048_ = lean_ctor_get(v_a_1038_, 1);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_a_1038_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1050_ = v_a_1038_;
v_isShared_1051_ = v_isSharedCheck_1077_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_searcher_1048_);
lean_inc(v_currPos_1047_);
lean_dec(v_a_1038_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1077_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v_str_1052_; lean_object* v_startInclusive_1053_; lean_object* v_endExclusive_1054_; lean_object* v___x_1055_; uint8_t v_decide_1056_; 
v_str_1052_ = lean_ctor_get(v___x_1036_, 0);
v_startInclusive_1053_ = lean_ctor_get(v___x_1036_, 1);
v_endExclusive_1054_ = lean_ctor_get(v___x_1036_, 2);
v___x_1055_ = lean_nat_sub(v_endExclusive_1054_, v_startInclusive_1053_);
v_decide_1056_ = lean_nat_dec_eq(v_searcher_1048_, v___x_1055_);
lean_dec(v___x_1055_);
if (v_decide_1056_ == 0)
{
lean_object* v___x_1057_; uint32_t v___x_1058_; uint32_t v___x_1059_; uint8_t v___x_1060_; 
v___x_1057_ = lean_nat_add(v_startInclusive_1053_, v_searcher_1048_);
v___x_1058_ = lean_string_utf8_get_fast(v_str_1052_, v___x_1057_);
v___x_1059_ = 46;
v___x_1060_ = lean_uint32_dec_eq(v___x_1058_, v___x_1059_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1064_; 
lean_dec(v_searcher_1048_);
v___x_1061_ = lean_string_utf8_next_fast(v_str_1052_, v___x_1057_);
lean_dec(v___x_1057_);
v___x_1062_ = lean_nat_sub(v___x_1061_, v_startInclusive_1053_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 1, v___x_1062_);
v___x_1064_ = v___x_1050_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_currPos_1047_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
uint8_t v___x_1065_; 
v___x_1065_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___redArg(v___x_1034_, v___x_1035_, v___x_1036_, v___x_1037_, v___x_1064_, v_b_1039_);
return v___x_1065_;
}
}
else
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v_slice_1070_; lean_object* v_nextIt_1072_; 
v___x_1067_ = lean_string_utf8_next_fast(v_str_1052_, v___x_1057_);
v___x_1068_ = lean_nat_sub(v___x_1067_, v___x_1057_);
lean_dec(v___x_1057_);
v___x_1069_ = lean_nat_add(v_searcher_1048_, v___x_1068_);
lean_dec(v___x_1068_);
v_slice_1070_ = l_String_Slice_subslice_x21(v___x_1036_, v_currPos_1047_, v_searcher_1048_);
lean_inc(v___x_1069_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 1, v___x_1069_);
lean_ctor_set(v___x_1050_, 0, v___x_1069_);
v_nextIt_1072_ = v___x_1050_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v___x_1069_);
v_nextIt_1072_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v_startInclusive_1073_; lean_object* v_endExclusive_1074_; 
v_startInclusive_1073_ = lean_ctor_get(v_slice_1070_, 0);
lean_inc(v_startInclusive_1073_);
v_endExclusive_1074_ = lean_ctor_get(v_slice_1070_, 1);
lean_inc(v_endExclusive_1074_);
lean_dec_ref(v_slice_1070_);
v_it_1041_ = v_nextIt_1072_;
v_startInclusive_1042_ = v_startInclusive_1073_;
v_endExclusive_1043_ = v_endExclusive_1074_;
goto v___jp_1040_;
}
}
}
else
{
lean_object* v___x_1076_; 
lean_del_object(v___x_1050_);
lean_dec(v_searcher_1048_);
v___x_1076_ = lean_box(1);
lean_inc(v___x_1037_);
v_it_1041_ = v___x_1076_;
v_startInclusive_1042_ = v_currPos_1047_;
v_endExclusive_1043_ = v___x_1037_;
goto v___jp_1040_;
}
}
}
else
{
lean_dec(v___x_1037_);
return v_b_1039_;
}
v___jp_1040_:
{
lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1044_ = lean_string_utf8_extract_fast(v___x_1035_, v_startInclusive_1042_, v_endExclusive_1043_);
lean_dec(v_endExclusive_1043_);
lean_dec(v_startInclusive_1042_);
v___x_1045_ = l_Std_Http_URI_isValidDomainLabel(v___x_1044_);
if (v___x_1045_ == 0)
{
lean_dec(v_it_1041_);
lean_dec(v___x_1037_);
return v___x_1045_;
}
else
{
uint8_t v___x_1046_; 
v___x_1046_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___redArg(v___x_1034_, v___x_1035_, v___x_1036_, v___x_1037_, v_it_1041_, v___x_1034_);
return v___x_1046_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg___boxed(lean_object* v___x_1078_, lean_object* v___x_1079_, lean_object* v___x_1080_, lean_object* v___x_1081_, lean_object* v_a_1082_, lean_object* v_b_1083_){
_start:
{
uint8_t v___x_10918__boxed_1084_; uint8_t v_b_boxed_1085_; uint8_t v_res_1086_; lean_object* v_r_1087_; 
v___x_10918__boxed_1084_ = lean_unbox(v___x_1078_);
v_b_boxed_1085_ = lean_unbox(v_b_1083_);
v_res_1086_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_10918__boxed_1084_, v___x_1079_, v___x_1080_, v___x_1081_, v_a_1082_, v_b_boxed_1085_);
lean_dec_ref(v___x_1080_);
lean_dec_ref(v___x_1079_);
v_r_1087_ = lean_box(v_res_1086_);
return v_r_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(lean_object* v_config_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v___y_1096_; lean_object* v___y_1097_; uint8_t v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; uint8_t v___y_1107_; uint8_t v___y_1111_; uint8_t v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; uint8_t v___y_1118_; uint8_t v___y_1121_; uint8_t v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; uint8_t v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; uint8_t v___y_1129_; uint8_t v___y_1131_; uint8_t v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; uint8_t v___y_1140_; uint8_t v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v_lower_1150_; lean_object* v_upper_1151_; uint8_t v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v_array_1172_; lean_object* v_idx_1173_; lean_object* v___f_1174_; lean_object* v___y_1176_; lean_object* v_pos_1199_; lean_object* v_pos_1223_; lean_object* v_res_1224_; lean_object* v_pos_1226_; lean_object* v_res_1227_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v_array_1172_ = lean_ctor_get(v_a_1094_, 0);
v_idx_1173_ = lean_ctor_get(v_a_1094_, 1);
v___f_1174_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3));
v___x_1235_ = lean_byte_array_size(v_array_1172_);
v___x_1236_ = lean_nat_dec_lt(v_idx_1173_, v___x_1235_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; 
lean_inc(v_idx_1173_);
lean_inc_ref(v_array_1172_);
v___x_1237_ = lean_box(0);
v_pos_1226_ = v_a_1094_;
v_res_1227_ = v___x_1237_;
goto v___jp_1225_;
}
else
{
uint8_t v___x_1238_; uint8_t v___x_1239_; uint8_t v___x_1240_; 
v___x_1238_ = lean_byte_array_fget(v_array_1172_, v_idx_1173_);
v___x_1239_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1);
v___x_1240_ = lean_uint8_dec_eq(v___x_1238_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; 
lean_inc(v_idx_1173_);
lean_inc_ref(v_array_1172_);
v___x_1241_ = lean_box(0);
v_pos_1226_ = v_a_1094_;
v_res_1227_ = v___x_1241_;
goto v___jp_1225_;
}
else
{
lean_object* v___x_1242_; 
v___x_1242_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(v_a_1094_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_pos_1243_; lean_object* v_res_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1252_; 
v_pos_1243_ = lean_ctor_get(v___x_1242_, 0);
v_res_1244_ = lean_ctor_get(v___x_1242_, 1);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1246_ = v___x_1242_;
v_isShared_1247_ = v_isSharedCheck_1252_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_res_1244_);
lean_inc(v_pos_1243_);
lean_dec(v___x_1242_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1252_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1248_; lean_object* v___x_1250_; 
v___x_1248_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1248_, 0, v_res_1244_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v___x_1248_);
v___x_1250_ = v___x_1246_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_pos_1243_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
else
{
lean_object* v_pos_1253_; lean_object* v_err_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
v_pos_1253_ = lean_ctor_get(v___x_1242_, 0);
v_err_1254_ = lean_ctor_get(v___x_1242_, 1);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1242_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_err_1254_);
lean_inc(v_pos_1253_);
lean_dec(v___x_1242_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_pos_1253_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_err_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
}
v___jp_1095_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1098_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0));
v___x_1099_ = lean_string_append(v___x_1098_, v___y_1097_);
lean_dec_ref(v___y_1097_);
v___x_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
v___x_1101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___y_1096_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
return v___x_1101_;
}
v___jp_1102_:
{
if (v___y_1103_ == 0)
{
lean_dec_ref(v___y_1104_);
v___y_1096_ = v___y_1105_;
v___y_1097_ = v___y_1106_;
goto v___jp_1095_;
}
else
{
if (v___y_1107_ == 0)
{
lean_dec_ref(v___y_1104_);
v___y_1096_ = v___y_1105_;
v___y_1097_ = v___y_1106_;
goto v___jp_1095_;
}
else
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
lean_dec_ref(v___y_1106_);
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v___y_1104_);
v___x_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___y_1105_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
return v___x_1109_;
}
}
}
v___jp_1110_:
{
uint8_t v___x_1119_; 
v___x_1119_ = lean_nat_dec_eq(v___y_1114_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec(v___y_1114_);
if (v___x_1119_ == 0)
{
v___y_1103_ = v___y_1118_;
v___y_1104_ = v___y_1113_;
v___y_1105_ = v___y_1115_;
v___y_1106_ = v___y_1117_;
v___y_1107_ = v___y_1111_;
goto v___jp_1102_;
}
else
{
v___y_1103_ = v___y_1118_;
v___y_1104_ = v___y_1113_;
v___y_1105_ = v___y_1115_;
v___y_1106_ = v___y_1117_;
v___y_1107_ = v___y_1112_;
goto v___jp_1102_;
}
}
v___jp_1120_:
{
if (v___y_1125_ == 0)
{
v___y_1111_ = v___y_1121_;
v___y_1112_ = v___y_1122_;
v___y_1113_ = v___y_1123_;
v___y_1114_ = v___y_1124_;
v___y_1115_ = v___y_1126_;
v___y_1116_ = v___y_1127_;
v___y_1117_ = v___y_1128_;
v___y_1118_ = v___y_1125_;
goto v___jp_1110_;
}
else
{
v___y_1111_ = v___y_1121_;
v___y_1112_ = v___y_1122_;
v___y_1113_ = v___y_1123_;
v___y_1114_ = v___y_1124_;
v___y_1115_ = v___y_1126_;
v___y_1116_ = v___y_1127_;
v___y_1117_ = v___y_1128_;
v___y_1118_ = v___y_1129_;
goto v___jp_1110_;
}
}
v___jp_1130_:
{
uint8_t v___x_1141_; 
lean_inc(v___y_1136_);
v___x_1141_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___y_1131_, v___y_1135_, v___y_1133_, v___y_1136_, v___y_1134_, v___y_1131_);
lean_dec_ref(v___y_1133_);
if (v___x_1141_ == 0)
{
v___y_1121_ = v___y_1131_;
v___y_1122_ = v___y_1132_;
v___y_1123_ = v___y_1135_;
v___y_1124_ = v___y_1136_;
v___y_1125_ = v___y_1140_;
v___y_1126_ = v___y_1137_;
v___y_1127_ = v___y_1138_;
v___y_1128_ = v___y_1139_;
v___y_1129_ = v___x_1141_;
goto v___jp_1120_;
}
else
{
lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1142_ = lean_string_length(v___y_1135_);
v___x_1143_ = lean_unsigned_to_nat(255u);
v___x_1144_ = lean_nat_dec_le(v___x_1142_, v___x_1143_);
v___y_1121_ = v___y_1131_;
v___y_1122_ = v___y_1132_;
v___y_1123_ = v___y_1135_;
v___y_1124_ = v___y_1136_;
v___y_1125_ = v___y_1140_;
v___y_1126_ = v___y_1137_;
v___y_1127_ = v___y_1138_;
v___y_1128_ = v___y_1139_;
v___y_1129_ = v___x_1144_;
goto v___jp_1120_;
}
}
v___jp_1145_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1152_ = l_ByteArray_toByteSlice(v___y_1147_, v_lower_1150_, v_upper_1151_);
v___x_1153_ = l_ByteSlice_toByteArray(v___x_1152_);
v___x_1154_ = lean_string_validate_utf8(v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
lean_dec_ref(v___x_1153_);
lean_dec(v___y_1149_);
v___x_1155_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2));
v___x_1156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___y_1148_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
return v___x_1156_;
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1157_ = lean_string_from_utf8_unchecked(v___x_1153_);
lean_inc_n(v___y_1149_, 2);
lean_inc_ref(v___x_1157_);
v___x_1158_ = l_String_mapAux___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___x_1157_, v___y_1149_);
v___x_1159_ = lean_string_utf8_byte_size(v___x_1158_);
lean_inc_ref(v___x_1158_);
v___x_1160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1158_);
lean_ctor_set(v___x_1160_, 1, v___y_1149_);
lean_ctor_set(v___x_1160_, 2, v___x_1159_);
v___x_1161_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0);
v___x_1162_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_1158_, v___x_1160_, v___x_1159_, v___x_1161_, v___x_1154_);
if (v___x_1162_ == 0)
{
v___y_1131_ = v___x_1154_;
v___y_1132_ = v___y_1146_;
v___y_1133_ = v___x_1160_;
v___y_1134_ = v___x_1161_;
v___y_1135_ = v___x_1158_;
v___y_1136_ = v___x_1159_;
v___y_1137_ = v___y_1148_;
v___y_1138_ = v___y_1149_;
v___y_1139_ = v___x_1157_;
v___y_1140_ = v___x_1154_;
goto v___jp_1130_;
}
else
{
v___y_1131_ = v___x_1154_;
v___y_1132_ = v___y_1146_;
v___y_1133_ = v___x_1160_;
v___y_1134_ = v___x_1161_;
v___y_1135_ = v___x_1158_;
v___y_1136_ = v___x_1159_;
v___y_1137_ = v___y_1148_;
v___y_1138_ = v___y_1149_;
v___y_1139_ = v___x_1157_;
v___y_1140_ = v___y_1146_;
goto v___jp_1130_;
}
}
}
v___jp_1163_:
{
uint8_t v___x_1171_; 
v___x_1171_ = lean_nat_dec_le(v___y_1167_, v___y_1166_);
if (v___x_1171_ == 0)
{
lean_dec(v___y_1167_);
v___y_1146_ = v___y_1164_;
v___y_1147_ = v___y_1165_;
v___y_1148_ = v___y_1168_;
v___y_1149_ = v___y_1169_;
v_lower_1150_ = v___y_1170_;
v_upper_1151_ = v___y_1166_;
goto v___jp_1145_;
}
else
{
lean_dec(v___y_1166_);
v___y_1146_ = v___y_1164_;
v___y_1147_ = v___y_1165_;
v___y_1148_ = v___y_1168_;
v___y_1149_ = v___y_1169_;
v_lower_1150_ = v___y_1170_;
v_upper_1151_ = v___y_1167_;
goto v___jp_1145_;
}
}
v___jp_1175_:
{
lean_object* v_maxHostLength_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v_snd_1180_; lean_object* v_fst_1181_; lean_object* v_fst_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1196_; 
v_maxHostLength_1177_ = lean_ctor_get(v_config_1093_, 1);
v___x_1178_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___y_1176_);
v___x_1179_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1174_, v_maxHostLength_1177_, v___x_1178_, v___y_1176_);
v_snd_1180_ = lean_ctor_get(v___x_1179_, 1);
lean_inc(v_snd_1180_);
v_fst_1181_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_fst_1181_);
lean_dec_ref(v___x_1179_);
v_fst_1182_ = lean_ctor_get(v_snd_1180_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_snd_1180_);
if (v_isSharedCheck_1196_ == 0)
{
lean_object* v_unused_1197_; 
v_unused_1197_ = lean_ctor_get(v_snd_1180_, 1);
lean_dec(v_unused_1197_);
v___x_1184_ = v_snd_1180_;
v_isShared_1185_ = v_isSharedCheck_1196_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_fst_1182_);
lean_dec(v_snd_1180_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1196_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
uint8_t v___x_1186_; 
v___x_1186_ = lean_nat_dec_eq(v_fst_1181_, v___x_1178_);
if (v___x_1186_ == 0)
{
lean_object* v_array_1187_; lean_object* v_idx_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; uint8_t v___x_1191_; 
lean_del_object(v___x_1184_);
v_array_1187_ = lean_ctor_get(v___y_1176_, 0);
lean_inc_ref(v_array_1187_);
v_idx_1188_ = lean_ctor_get(v___y_1176_, 1);
lean_inc(v_idx_1188_);
lean_dec_ref(v___y_1176_);
v___x_1189_ = lean_nat_add(v_idx_1188_, v_fst_1181_);
lean_dec(v_fst_1181_);
v___x_1190_ = lean_byte_array_size(v_array_1187_);
v___x_1191_ = lean_nat_dec_le(v_idx_1188_, v___x_1178_);
if (v___x_1191_ == 0)
{
v___y_1164_ = v___x_1186_;
v___y_1165_ = v_array_1187_;
v___y_1166_ = v___x_1190_;
v___y_1167_ = v___x_1189_;
v___y_1168_ = v_fst_1182_;
v___y_1169_ = v___x_1178_;
v___y_1170_ = v_idx_1188_;
goto v___jp_1163_;
}
else
{
lean_dec(v_idx_1188_);
v___y_1164_ = v___x_1186_;
v___y_1165_ = v_array_1187_;
v___y_1166_ = v___x_1190_;
v___y_1167_ = v___x_1189_;
v___y_1168_ = v_fst_1182_;
v___y_1169_ = v___x_1178_;
v___y_1170_ = v___x_1178_;
goto v___jp_1163_;
}
}
else
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
lean_dec(v_fst_1182_);
lean_dec(v_fst_1181_);
v___x_1192_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__17));
if (v_isShared_1185_ == 0)
{
lean_ctor_set_tag(v___x_1184_, 1);
lean_ctor_set(v___x_1184_, 1, v___x_1192_);
lean_ctor_set(v___x_1184_, 0, v___y_1176_);
v___x_1194_ = v___x_1184_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___y_1176_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
v___jp_1198_:
{
lean_object* v___x_1200_; 
lean_inc_ref(v_pos_1199_);
v___x_1200_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(v_pos_1199_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_pos_1201_; lean_object* v_res_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1210_; 
lean_dec_ref(v_pos_1199_);
v_pos_1201_ = lean_ctor_get(v___x_1200_, 0);
v_res_1202_ = lean_ctor_get(v___x_1200_, 1);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1204_ = v___x_1200_;
v_isShared_1205_ = v_isSharedCheck_1210_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_res_1202_);
lean_inc(v_pos_1201_);
lean_dec(v___x_1200_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1210_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1208_; 
v___x_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1206_, 0, v_res_1202_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v___x_1206_);
v___x_1208_ = v___x_1204_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_pos_1201_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
else
{
lean_object* v_err_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1220_; 
v_err_1211_ = lean_ctor_get(v___x_1200_, 1);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; 
v_unused_1221_ = lean_ctor_get(v___x_1200_, 0);
lean_dec(v_unused_1221_);
v___x_1213_ = v___x_1200_;
v_isShared_1214_ = v_isSharedCheck_1220_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_err_1211_);
lean_dec(v___x_1200_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1220_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v_idx_1215_; uint8_t v___x_1216_; 
v_idx_1215_ = lean_ctor_get(v_pos_1199_, 1);
v___x_1216_ = lean_nat_dec_eq(v_idx_1215_, v_idx_1215_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1218_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v_pos_1199_);
v___x_1218_ = v___x_1213_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_pos_1199_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_err_1211_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
else
{
lean_del_object(v___x_1213_);
lean_dec(v_err_1211_);
v___y_1176_ = v_pos_1199_;
goto v___jp_1175_;
}
}
}
}
v___jp_1222_:
{
v___y_1176_ = v_pos_1223_;
goto v___jp_1175_;
}
v___jp_1225_:
{
lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = lean_byte_array_size(v_array_1172_);
v___x_1229_ = lean_nat_dec_lt(v_idx_1173_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_dec(v_idx_1173_);
lean_dec_ref(v_array_1172_);
v_pos_1223_ = v_pos_1226_;
v_res_1224_ = v_res_1227_;
goto v___jp_1222_;
}
else
{
uint8_t v___x_1230_; uint8_t v___x_1231_; uint8_t v___x_1232_; 
v___x_1230_ = lean_byte_array_fget(v_array_1172_, v_idx_1173_);
lean_dec(v_idx_1173_);
lean_dec_ref(v_array_1172_);
v___x_1231_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_1232_ = lean_uint8_dec_le(v___x_1231_, v___x_1230_);
if (v___x_1232_ == 0)
{
v_pos_1223_ = v_pos_1226_;
v_res_1224_ = v_res_1227_;
goto v___jp_1222_;
}
else
{
uint8_t v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_1234_ = lean_uint8_dec_le(v___x_1230_, v___x_1233_);
if (v___x_1234_ == 0)
{
v_pos_1223_ = v_pos_1226_;
v_res_1224_ = v_res_1227_;
goto v___jp_1222_;
}
else
{
v_pos_1199_ = v_pos_1226_;
goto v___jp_1198_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___boxed(lean_object* v_config_1262_, lean_object* v_a_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1262_, v_a_1263_);
lean_dec_ref(v_config_1262_);
return v_res_1264_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(lean_object* v___x_1265_, lean_object* v___x_1266_, lean_object* v___x_1267_, lean_object* v_inst_1268_, lean_object* v_R_1269_, lean_object* v_a_1270_, uint8_t v_b_1271_, lean_object* v_c_1272_){
_start:
{
uint8_t v___x_1273_; 
v___x_1273_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_1265_, v___x_1266_, v___x_1267_, v_a_1270_, v_b_1271_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___boxed(lean_object* v___x_1274_, lean_object* v___x_1275_, lean_object* v___x_1276_, lean_object* v_inst_1277_, lean_object* v_R_1278_, lean_object* v_a_1279_, lean_object* v_b_1280_, lean_object* v_c_1281_){
_start:
{
uint8_t v_b_boxed_1282_; uint8_t v_res_1283_; lean_object* v_r_1284_; 
v_b_boxed_1282_ = lean_unbox(v_b_1280_);
v_res_1283_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(v___x_1274_, v___x_1275_, v___x_1276_, v_inst_1277_, v_R_1278_, v_a_1279_, v_b_boxed_1282_, v_c_1281_);
lean_dec(v___x_1276_);
lean_dec_ref(v___x_1275_);
lean_dec_ref(v___x_1274_);
v_r_1284_ = lean_box(v_res_1283_);
return v_r_1284_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(uint8_t v___x_1285_, lean_object* v___x_1286_, lean_object* v___x_1287_, lean_object* v___x_1288_, lean_object* v_inst_1289_, lean_object* v_R_1290_, lean_object* v_a_1291_, uint8_t v_b_1292_, lean_object* v_c_1293_){
_start:
{
uint8_t v___x_1294_; 
v___x_1294_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_1285_, v___x_1286_, v___x_1287_, v___x_1288_, v_a_1291_, v_b_1292_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___boxed(lean_object* v___x_1295_, lean_object* v___x_1296_, lean_object* v___x_1297_, lean_object* v___x_1298_, lean_object* v_inst_1299_, lean_object* v_R_1300_, lean_object* v_a_1301_, lean_object* v_b_1302_, lean_object* v_c_1303_){
_start:
{
uint8_t v___x_11354__boxed_1304_; uint8_t v_b_boxed_1305_; uint8_t v_res_1306_; lean_object* v_r_1307_; 
v___x_11354__boxed_1304_ = lean_unbox(v___x_1295_);
v_b_boxed_1305_ = lean_unbox(v_b_1302_);
v_res_1306_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(v___x_11354__boxed_1304_, v___x_1296_, v___x_1297_, v___x_1298_, v_inst_1299_, v_R_1300_, v_a_1301_, v_b_boxed_1305_, v_c_1303_);
lean_dec_ref(v___x_1297_);
lean_dec_ref(v___x_1296_);
v_r_1307_ = lean_box(v_res_1306_);
return v_r_1307_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1(lean_object* v___x_1308_, lean_object* v___x_1309_, lean_object* v___x_1310_, lean_object* v_inst_1311_, lean_object* v_R_1312_, lean_object* v_a_1313_, uint8_t v_b_1314_, lean_object* v_c_1315_){
_start:
{
uint8_t v___x_1316_; 
v___x_1316_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1___redArg(v___x_1309_, v_a_1313_, v_b_1314_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1___boxed(lean_object* v___x_1317_, lean_object* v___x_1318_, lean_object* v___x_1319_, lean_object* v_inst_1320_, lean_object* v_R_1321_, lean_object* v_a_1322_, lean_object* v_b_1323_, lean_object* v_c_1324_){
_start:
{
uint8_t v_b_boxed_1325_; uint8_t v_res_1326_; lean_object* v_r_1327_; 
v_b_boxed_1325_ = lean_unbox(v_b_1323_);
v_res_1326_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1_spec__1(v___x_1317_, v___x_1318_, v___x_1319_, v_inst_1320_, v_R_1321_, v_a_1322_, v_b_boxed_1325_, v_c_1324_);
lean_dec(v___x_1319_);
lean_dec_ref(v___x_1318_);
lean_dec_ref(v___x_1317_);
v_r_1327_ = lean_box(v_res_1326_);
return v_r_1327_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3(uint8_t v___x_1328_, lean_object* v___x_1329_, lean_object* v___x_1330_, lean_object* v___x_1331_, lean_object* v_inst_1332_, lean_object* v_R_1333_, lean_object* v_a_1334_, uint8_t v_b_1335_, lean_object* v_c_1336_){
_start:
{
uint8_t v___x_1337_; 
v___x_1337_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___redArg(v___x_1328_, v___x_1329_, v___x_1330_, v___x_1331_, v_a_1334_, v_b_1335_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3___boxed(lean_object* v___x_1338_, lean_object* v___x_1339_, lean_object* v___x_1340_, lean_object* v___x_1341_, lean_object* v_inst_1342_, lean_object* v_R_1343_, lean_object* v_a_1344_, lean_object* v_b_1345_, lean_object* v_c_1346_){
_start:
{
uint8_t v___x_11385__boxed_1347_; uint8_t v_b_boxed_1348_; uint8_t v_res_1349_; lean_object* v_r_1350_; 
v___x_11385__boxed_1347_ = lean_unbox(v___x_1338_);
v_b_boxed_1348_ = lean_unbox(v_b_1345_);
v_res_1349_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2_spec__3(v___x_11385__boxed_1347_, v___x_1339_, v___x_1340_, v___x_1341_, v_inst_1342_, v_R_1343_, v_a_1344_, v_b_boxed_1348_, v_c_1346_);
lean_dec_ref(v___x_1340_);
lean_dec_ref(v___x_1339_);
v_r_1350_ = lean_box(v_res_1349_);
return v_r_1350_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2(void){
_start:
{
uint32_t v___x_1354_; uint8_t v___x_1355_; 
v___x_1354_ = 47;
v___x_1355_ = lean_uint32_to_uint8(v___x_1354_);
return v___x_1355_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3(void){
_start:
{
uint32_t v___x_1356_; uint8_t v___x_1357_; 
v___x_1356_ = 63;
v___x_1357_ = lean_uint32_to_uint8(v___x_1356_);
return v___x_1357_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4(void){
_start:
{
uint32_t v___x_1358_; uint8_t v___x_1359_; 
v___x_1358_ = 35;
v___x_1359_ = lean_uint32_to_uint8(v___x_1358_);
return v___x_1359_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5(void){
_start:
{
uint8_t v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_1361_ = lean_uint8_to_nat(v___x_1360_);
return v___x_1361_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6(void){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5);
v___x_1363_ = l_Nat_reprFast(v___x_1362_);
return v___x_1363_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7(void){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1364_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6);
v___x_1365_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_1366_ = lean_string_append(v___x_1365_, v___x_1364_);
return v___x_1366_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8(void){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1367_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_1368_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7);
v___x_1369_ = lean_string_append(v___x_1368_, v___x_1367_);
return v___x_1369_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9(void){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8);
v___x_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
return v___x_1371_;
}
}
static uint8_t _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10(void){
_start:
{
uint32_t v___x_1372_; uint8_t v___x_1373_; 
v___x_1372_ = 64;
v___x_1373_ = lean_uint32_to_uint8(v___x_1372_);
return v___x_1373_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11(void){
_start:
{
uint8_t v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1375_ = lean_uint8_to_nat(v___x_1374_);
return v___x_1375_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12(void){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11);
v___x_1377_ = l_Nat_reprFast(v___x_1376_);
return v___x_1377_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13(void){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1378_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12);
v___x_1379_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_1380_ = lean_string_append(v___x_1379_, v___x_1378_);
return v___x_1380_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14(void){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1381_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_1382_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13);
v___x_1383_ = lean_string_append(v___x_1382_, v___x_1381_);
return v___x_1383_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15(void){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14);
v___x_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(lean_object* v_config_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v_port_1391_; lean_object* v___y_1392_; lean_object* v___y_1396_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; uint8_t v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; uint8_t v___y_1409_; lean_object* v___y_1411_; uint8_t v_val_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1422_; lean_object* v___y_1423_; uint8_t v___y_1424_; lean_object* v_pos_1425_; lean_object* v_array_1426_; lean_object* v_idx_1427_; lean_object* v_res_1428_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; uint8_t v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v_pos_1443_; lean_object* v_pos_1446_; lean_object* v_res_1447_; lean_object* v_pos_1512_; lean_object* v_res_1513_; lean_object* v_err_1516_; lean_object* v___x_1521_; 
lean_inc_ref(v_a_1387_);
v___x_1521_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(v_config_1386_, v_a_1387_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_pos_1522_; lean_object* v_res_1523_; lean_object* v_array_1524_; lean_object* v_idx_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1541_; 
v_pos_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_pos_1522_);
v_res_1523_ = lean_ctor_get(v___x_1521_, 1);
lean_inc(v_res_1523_);
lean_dec_ref_known(v___x_1521_, 2);
v_array_1524_ = lean_ctor_get(v_pos_1522_, 0);
v_idx_1525_ = lean_ctor_get(v_pos_1522_, 1);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_pos_1522_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1527_ = v_pos_1522_;
v_isShared_1528_ = v_isSharedCheck_1541_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_idx_1525_);
lean_inc(v_array_1524_);
lean_dec(v_pos_1522_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1541_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; uint8_t v___x_1530_; 
v___x_1529_ = lean_byte_array_size(v_array_1524_);
v___x_1530_ = lean_nat_dec_lt(v_idx_1525_, v___x_1529_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; 
lean_del_object(v___x_1527_);
lean_dec(v_idx_1525_);
lean_dec_ref(v_array_1524_);
lean_dec(v_res_1523_);
v___x_1531_ = lean_box(0);
v_err_1516_ = v___x_1531_;
goto v___jp_1515_;
}
else
{
uint8_t v___x_1532_; uint8_t v_got_1533_; uint8_t v___x_1534_; 
v___x_1532_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v_got_1533_ = lean_byte_array_fget(v_array_1524_, v_idx_1525_);
v___x_1534_ = lean_uint8_dec_eq(v_got_1533_, v___x_1532_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; 
lean_del_object(v___x_1527_);
lean_dec(v_idx_1525_);
lean_dec_ref(v_array_1524_);
lean_dec(v_res_1523_);
v___x_1535_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15);
v_err_1516_ = v___x_1535_;
goto v___jp_1515_;
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1539_; 
lean_dec_ref(v_a_1387_);
v___x_1536_ = lean_unsigned_to_nat(1u);
v___x_1537_ = lean_nat_add(v_idx_1525_, v___x_1536_);
lean_dec(v_idx_1525_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 1, v___x_1537_);
v___x_1539_ = v___x_1527_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_array_1524_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v___x_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
v_pos_1512_ = v___x_1539_;
v_res_1513_ = v_res_1523_;
goto v___jp_1511_;
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_pos_1542_; lean_object* v_res_1543_; 
lean_dec_ref(v_a_1387_);
v_pos_1542_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_pos_1542_);
v_res_1543_ = lean_ctor_get(v___x_1521_, 1);
lean_inc(v_res_1543_);
lean_dec_ref_known(v___x_1521_, 2);
v_pos_1512_ = v_pos_1542_;
v_res_1513_ = v_res_1543_;
goto v___jp_1511_;
}
else
{
lean_object* v_err_1544_; 
v_err_1544_ = lean_ctor_get(v___x_1521_, 1);
lean_inc(v_err_1544_);
lean_dec_ref_known(v___x_1521_, 2);
v_err_1516_ = v_err_1544_;
goto v___jp_1515_;
}
}
v___jp_1388_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1393_, 0, v___y_1389_);
lean_ctor_set(v___x_1393_, 1, v___y_1390_);
lean_ctor_set(v___x_1393_, 2, v_port_1391_);
v___x_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___y_1392_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
return v___x_1394_;
}
v___jp_1395_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1));
v___x_1398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___y_1396_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
return v___x_1398_;
}
v___jp_1399_:
{
lean_object* v___x_1403_; 
v___x_1403_ = lean_box(1);
v___y_1389_ = v___y_1400_;
v___y_1390_ = v___y_1401_;
v_port_1391_ = v___x_1403_;
v___y_1392_ = v___y_1402_;
goto v___jp_1388_;
}
v___jp_1404_:
{
if (v___y_1405_ == 0)
{
if (v___y_1409_ == 0)
{
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
v___y_1396_ = v___y_1408_;
goto v___jp_1395_;
}
else
{
v___y_1400_ = v___y_1406_;
v___y_1401_ = v___y_1407_;
v___y_1402_ = v___y_1408_;
goto v___jp_1399_;
}
}
else
{
v___y_1400_ = v___y_1406_;
v___y_1401_ = v___y_1407_;
v___y_1402_ = v___y_1408_;
goto v___jp_1399_;
}
}
v___jp_1410_:
{
uint8_t v___x_1415_; uint8_t v___x_1416_; uint8_t v___x_1417_; uint8_t v___x_1418_; 
v___x_1415_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_1416_ = lean_uint8_dec_eq(v_val_1412_, v___x_1415_);
v___x_1417_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_1418_ = lean_uint8_dec_eq(v_val_1412_, v___x_1417_);
if (v___x_1418_ == 0)
{
uint8_t v___x_1419_; uint8_t v___x_1420_; 
v___x_1419_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v___x_1420_ = lean_uint8_dec_eq(v_val_1412_, v___x_1419_);
v___y_1405_ = v___x_1416_;
v___y_1406_ = v___y_1411_;
v___y_1407_ = v___y_1413_;
v___y_1408_ = v___y_1414_;
v___y_1409_ = v___x_1420_;
goto v___jp_1404_;
}
else
{
v___y_1405_ = v___x_1416_;
v___y_1406_ = v___y_1411_;
v___y_1407_ = v___y_1413_;
v___y_1408_ = v___y_1414_;
v___y_1409_ = v___x_1418_;
goto v___jp_1404_;
}
}
v___jp_1421_:
{
lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1429_ = lean_byte_array_size(v_array_1426_);
v___x_1430_ = lean_nat_dec_lt(v_idx_1427_, v___x_1429_);
if (v___x_1430_ == 0)
{
lean_dec(v_idx_1427_);
lean_dec_ref(v_array_1426_);
if (v___y_1424_ == 0)
{
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
v___y_1396_ = v_pos_1425_;
goto v___jp_1395_;
}
else
{
v___y_1400_ = v___y_1422_;
v___y_1401_ = v___y_1423_;
v___y_1402_ = v_pos_1425_;
goto v___jp_1399_;
}
}
else
{
uint8_t v___x_1431_; 
v___x_1431_ = lean_byte_array_fget(v_array_1426_, v_idx_1427_);
lean_dec(v_idx_1427_);
lean_dec_ref(v_array_1426_);
v___y_1411_ = v___y_1422_;
v_val_1412_ = v___x_1431_;
v___y_1413_ = v___y_1423_;
v___y_1414_ = v_pos_1425_;
goto v___jp_1410_;
}
}
v___jp_1432_:
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_box(0);
v___y_1422_ = v___y_1435_;
v___y_1423_ = v___y_1436_;
v___y_1424_ = v___y_1437_;
v_pos_1425_ = v___y_1434_;
v_array_1426_ = v___y_1433_;
v_idx_1427_ = v___y_1438_;
v_res_1428_ = v___x_1439_;
goto v___jp_1421_;
}
v___jp_1440_:
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_box(0);
v___y_1389_ = v___y_1441_;
v___y_1390_ = v___y_1442_;
v_port_1391_ = v___x_1444_;
v___y_1392_ = v_pos_1443_;
goto v___jp_1388_;
}
v___jp_1445_:
{
lean_object* v___x_1448_; 
v___x_1448_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1386_, v_pos_1446_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_pos_1449_; lean_object* v_res_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1501_; 
v_pos_1449_ = lean_ctor_get(v___x_1448_, 0);
v_res_1450_ = lean_ctor_get(v___x_1448_, 1);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1452_ = v___x_1448_;
v_isShared_1453_ = v_isSharedCheck_1501_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_res_1450_);
lean_inc(v_pos_1449_);
lean_dec(v___x_1448_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1501_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v_array_1454_; lean_object* v_idx_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
v_array_1454_ = lean_ctor_get(v_pos_1449_, 0);
v_idx_1455_ = lean_ctor_get(v_pos_1449_, 1);
v___x_1456_ = lean_byte_array_size(v_array_1454_);
v___x_1457_ = lean_nat_dec_lt(v_idx_1455_, v___x_1456_);
if (v___x_1457_ == 0)
{
lean_del_object(v___x_1452_);
v___y_1441_ = v_res_1447_;
v___y_1442_ = v_res_1450_;
v_pos_1443_ = v_pos_1449_;
goto v___jp_1440_;
}
else
{
uint8_t v___x_1458_; uint8_t v___x_1459_; uint8_t v___x_1460_; 
v___x_1458_ = lean_byte_array_fget(v_array_1454_, v_idx_1455_);
v___x_1459_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_1460_ = lean_uint8_dec_eq(v___x_1458_, v___x_1459_);
if (v___x_1460_ == 0)
{
lean_del_object(v___x_1452_);
v___y_1441_ = v_res_1447_;
v___y_1442_ = v_res_1450_;
v_pos_1443_ = v_pos_1449_;
goto v___jp_1440_;
}
else
{
if (v___x_1460_ == 0)
{
lean_del_object(v___x_1452_);
v___y_1441_ = v_res_1447_;
v___y_1442_ = v_res_1450_;
v_pos_1443_ = v_pos_1449_;
goto v___jp_1440_;
}
else
{
if (v___x_1457_ == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1463_; 
lean_dec(v_res_1450_);
lean_dec(v_res_1447_);
v___x_1461_ = lean_box(0);
if (v_isShared_1453_ == 0)
{
lean_ctor_set_tag(v___x_1452_, 1);
lean_ctor_set(v___x_1452_, 1, v___x_1461_);
v___x_1463_ = v___x_1452_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_pos_1449_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v___x_1461_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
else
{
if (v___x_1460_ == 0)
{
lean_object* v___x_1465_; lean_object* v___x_1467_; 
lean_dec(v_res_1450_);
lean_dec(v_res_1447_);
v___x_1465_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
if (v_isShared_1453_ == 0)
{
lean_ctor_set_tag(v___x_1452_, 1);
lean_ctor_set(v___x_1452_, 1, v___x_1465_);
v___x_1467_ = v___x_1452_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_pos_1449_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
else
{
lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1498_; 
lean_inc(v_idx_1455_);
lean_inc_ref(v_array_1454_);
lean_del_object(v___x_1452_);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_pos_1449_);
if (v_isSharedCheck_1498_ == 0)
{
lean_object* v_unused_1499_; lean_object* v_unused_1500_; 
v_unused_1499_ = lean_ctor_get(v_pos_1449_, 1);
lean_dec(v_unused_1499_);
v_unused_1500_ = lean_ctor_get(v_pos_1449_, 0);
lean_dec(v_unused_1500_);
v___x_1470_ = v_pos_1449_;
v_isShared_1471_ = v_isSharedCheck_1498_;
goto v_resetjp_1469_;
}
else
{
lean_dec(v_pos_1449_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1498_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1472_ = lean_unsigned_to_nat(1u);
v___x_1473_ = lean_nat_add(v_idx_1455_, v___x_1472_);
lean_dec(v_idx_1455_);
lean_inc(v___x_1473_);
lean_inc_ref(v_array_1454_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 1, v___x_1473_);
v___x_1475_ = v___x_1470_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_array_1454_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v___x_1473_);
v___x_1475_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
uint8_t v___x_1476_; 
v___x_1476_ = lean_nat_dec_lt(v___x_1473_, v___x_1456_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; 
v___x_1477_ = lean_box(0);
v___y_1422_ = v_res_1447_;
v___y_1423_ = v_res_1450_;
v___y_1424_ = v___x_1460_;
v_pos_1425_ = v___x_1475_;
v_array_1426_ = v_array_1454_;
v_idx_1427_ = v___x_1473_;
v_res_1428_ = v___x_1477_;
goto v___jp_1421_;
}
else
{
uint8_t v___x_1478_; uint8_t v___x_1479_; uint8_t v___x_1480_; 
v___x_1478_ = lean_byte_array_fget(v_array_1454_, v___x_1473_);
v___x_1479_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_1480_ = lean_uint8_dec_le(v___x_1479_, v___x_1478_);
if (v___x_1480_ == 0)
{
v___y_1433_ = v_array_1454_;
v___y_1434_ = v___x_1475_;
v___y_1435_ = v_res_1447_;
v___y_1436_ = v_res_1450_;
v___y_1437_ = v___x_1460_;
v___y_1438_ = v___x_1473_;
goto v___jp_1432_;
}
else
{
uint8_t v___x_1481_; uint8_t v___x_1482_; 
v___x_1481_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_1482_ = lean_uint8_dec_le(v___x_1478_, v___x_1481_);
if (v___x_1482_ == 0)
{
v___y_1433_ = v_array_1454_;
v___y_1434_ = v___x_1475_;
v___y_1435_ = v_res_1447_;
v___y_1436_ = v_res_1450_;
v___y_1437_ = v___x_1460_;
v___y_1438_ = v___x_1473_;
goto v___jp_1432_;
}
else
{
lean_object* v___x_1483_; 
lean_dec(v___x_1473_);
lean_dec_ref(v_array_1454_);
v___x_1483_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_1475_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_pos_1484_; lean_object* v_res_1485_; lean_object* v___x_1486_; uint16_t v___x_1487_; 
v_pos_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_pos_1484_);
v_res_1485_ = lean_ctor_get(v___x_1483_, 1);
lean_inc(v_res_1485_);
lean_dec_ref_known(v___x_1483_, 2);
v___x_1486_ = lean_alloc_ctor(2, 0, 2);
v___x_1487_ = lean_unbox(v_res_1485_);
lean_dec(v_res_1485_);
lean_ctor_set_uint16(v___x_1486_, 0, v___x_1487_);
v___y_1389_ = v_res_1447_;
v___y_1390_ = v_res_1450_;
v_port_1391_ = v___x_1486_;
v___y_1392_ = v_pos_1484_;
goto v___jp_1388_;
}
else
{
lean_object* v_pos_1488_; lean_object* v_err_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec(v_res_1450_);
lean_dec(v_res_1447_);
v_pos_1488_ = lean_ctor_get(v___x_1483_, 0);
v_err_1489_ = lean_ctor_get(v___x_1483_, 1);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1483_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_err_1489_);
lean_inc(v_pos_1488_);
lean_dec(v___x_1483_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_pos_1488_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_err_1489_);
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
lean_object* v_pos_1502_; lean_object* v_err_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
lean_dec(v_res_1447_);
v_pos_1502_ = lean_ctor_get(v___x_1448_, 0);
v_err_1503_ = lean_ctor_get(v___x_1448_, 1);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1448_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_err_1503_);
lean_inc(v_pos_1502_);
lean_dec(v___x_1448_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_pos_1502_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_err_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
v___jp_1511_:
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1514_, 0, v_res_1513_);
v_pos_1446_ = v_pos_1512_;
v_res_1447_ = v___x_1514_;
goto v___jp_1445_;
}
v___jp_1515_:
{
lean_object* v_idx_1517_; uint8_t v___x_1518_; 
v_idx_1517_ = lean_ctor_get(v_a_1387_, 1);
v___x_1518_ = lean_nat_dec_eq(v_idx_1517_, v_idx_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; 
v___x_1519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1519_, 0, v_a_1387_);
lean_ctor_set(v___x_1519_, 1, v_err_1516_);
return v___x_1519_;
}
else
{
lean_object* v___x_1520_; 
lean_dec(v_err_1516_);
v___x_1520_ = lean_box(0);
v_pos_1446_ = v_a_1387_;
v_res_1447_ = v___x_1520_;
goto v___jp_1445_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___boxed(lean_object* v_config_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_1545_, v_a_1546_);
lean_dec_ref(v_config_1545_);
return v_res_1547_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(uint8_t v_c_1548_){
_start:
{
uint8_t v___y_1550_; uint8_t v___x_1598_; uint8_t v___x_1599_; 
v___x_1598_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_1599_ = lean_uint8_dec_le(v___x_1598_, v_c_1548_);
if (v___x_1599_ == 0)
{
goto v___jp_1593_;
}
else
{
uint8_t v___x_1600_; uint8_t v___x_1601_; 
v___x_1600_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_1601_ = lean_uint8_dec_le(v_c_1548_, v___x_1600_);
if (v___x_1601_ == 0)
{
goto v___jp_1593_;
}
else
{
v___y_1550_ = v___x_1601_;
goto v___jp_1549_;
}
}
v___jp_1549_:
{
if (v___y_1550_ == 0)
{
uint8_t v___x_1551_; uint8_t v___x_1552_; 
v___x_1551_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1552_ = lean_uint8_dec_eq(v_c_1548_, v___x_1551_);
return v___x_1552_;
}
else
{
return v___y_1550_;
}
}
v___jp_1553_:
{
uint8_t v___x_1554_; uint8_t v___x_1555_; 
v___x_1554_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_1555_ = lean_uint8_dec_eq(v_c_1548_, v___x_1554_);
if (v___x_1555_ == 0)
{
uint8_t v___x_1556_; uint8_t v___x_1557_; 
v___x_1556_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_1557_ = lean_uint8_dec_eq(v_c_1548_, v___x_1556_);
if (v___x_1557_ == 0)
{
uint8_t v___x_1558_; uint8_t v___x_1559_; 
v___x_1558_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_1559_ = lean_uint8_dec_eq(v_c_1548_, v___x_1558_);
if (v___x_1559_ == 0)
{
uint8_t v___x_1560_; uint8_t v___x_1561_; 
v___x_1560_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_1561_ = lean_uint8_dec_eq(v_c_1548_, v___x_1560_);
if (v___x_1561_ == 0)
{
uint8_t v___x_1562_; uint8_t v___x_1563_; 
v___x_1562_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_1563_ = lean_uint8_dec_eq(v_c_1548_, v___x_1562_);
if (v___x_1563_ == 0)
{
uint8_t v___x_1564_; uint8_t v___x_1565_; 
v___x_1564_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_1565_ = lean_uint8_dec_eq(v_c_1548_, v___x_1564_);
if (v___x_1565_ == 0)
{
uint8_t v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_1567_ = lean_uint8_dec_eq(v_c_1548_, v___x_1566_);
if (v___x_1567_ == 0)
{
uint8_t v___x_1568_; uint8_t v___x_1569_; 
v___x_1568_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_1569_ = lean_uint8_dec_eq(v_c_1548_, v___x_1568_);
if (v___x_1569_ == 0)
{
uint8_t v___x_1570_; uint8_t v___x_1571_; 
v___x_1570_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_1571_ = lean_uint8_dec_eq(v_c_1548_, v___x_1570_);
if (v___x_1571_ == 0)
{
uint8_t v___x_1572_; uint8_t v___x_1573_; 
v___x_1572_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_1573_ = lean_uint8_dec_eq(v_c_1548_, v___x_1572_);
if (v___x_1573_ == 0)
{
uint8_t v___x_1574_; uint8_t v___x_1575_; 
v___x_1574_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_1575_ = lean_uint8_dec_eq(v_c_1548_, v___x_1574_);
if (v___x_1575_ == 0)
{
uint8_t v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_1577_ = lean_uint8_dec_eq(v_c_1548_, v___x_1576_);
if (v___x_1577_ == 0)
{
uint8_t v___x_1578_; uint8_t v___x_1579_; 
v___x_1578_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_1579_ = lean_uint8_dec_eq(v_c_1548_, v___x_1578_);
if (v___x_1579_ == 0)
{
uint8_t v___x_1580_; uint8_t v___x_1581_; 
v___x_1580_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_1581_ = lean_uint8_dec_eq(v_c_1548_, v___x_1580_);
if (v___x_1581_ == 0)
{
uint8_t v___x_1582_; uint8_t v___x_1583_; 
v___x_1582_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_1583_ = lean_uint8_dec_eq(v_c_1548_, v___x_1582_);
if (v___x_1583_ == 0)
{
uint8_t v___x_1584_; uint8_t v___x_1585_; 
v___x_1584_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_1585_ = lean_uint8_dec_eq(v_c_1548_, v___x_1584_);
if (v___x_1585_ == 0)
{
uint8_t v___x_1586_; uint8_t v___x_1587_; 
v___x_1586_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1587_ = lean_uint8_dec_eq(v_c_1548_, v___x_1586_);
v___y_1550_ = v___x_1587_;
goto v___jp_1549_;
}
else
{
v___y_1550_ = v___x_1585_;
goto v___jp_1549_;
}
}
else
{
v___y_1550_ = v___x_1583_;
goto v___jp_1549_;
}
}
else
{
v___y_1550_ = v___x_1581_;
goto v___jp_1549_;
}
}
else
{
v___y_1550_ = v___x_1579_;
goto v___jp_1549_;
}
}
else
{
v___y_1550_ = v___x_1577_;
goto v___jp_1549_;
}
}
else
{
v___y_1550_ = v___x_1575_;
goto v___jp_1549_;
}
}
else
{
v___y_1550_ = v___x_1573_;
goto v___jp_1549_;
}
}
else
{
v___y_1550_ = v___x_1571_;
goto v___jp_1549_;
}
}
else
{
v___y_1550_ = v___x_1569_;
goto v___jp_1549_;
}
}
else
{
v___y_1550_ = v___x_1567_;
goto v___jp_1549_;
}
}
else
{
v___y_1550_ = v___x_1565_;
goto v___jp_1549_;
}
}
else
{
v___y_1550_ = v___x_1563_;
goto v___jp_1549_;
}
}
else
{
v___y_1550_ = v___x_1561_;
goto v___jp_1549_;
}
}
else
{
v___y_1550_ = v___x_1559_;
goto v___jp_1549_;
}
}
else
{
v___y_1550_ = v___x_1557_;
goto v___jp_1549_;
}
}
else
{
v___y_1550_ = v___x_1555_;
goto v___jp_1549_;
}
}
v___jp_1588_:
{
uint8_t v___x_1589_; uint8_t v___x_1590_; 
v___x_1589_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_1590_ = lean_uint8_dec_le(v___x_1589_, v_c_1548_);
if (v___x_1590_ == 0)
{
goto v___jp_1553_;
}
else
{
uint8_t v___x_1591_; uint8_t v___x_1592_; 
v___x_1591_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_1592_ = lean_uint8_dec_le(v_c_1548_, v___x_1591_);
if (v___x_1592_ == 0)
{
goto v___jp_1553_;
}
else
{
v___y_1550_ = v___x_1592_;
goto v___jp_1549_;
}
}
}
v___jp_1593_:
{
uint8_t v___x_1594_; uint8_t v___x_1595_; 
v___x_1594_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_1595_ = lean_uint8_dec_le(v___x_1594_, v_c_1548_);
if (v___x_1595_ == 0)
{
goto v___jp_1588_;
}
else
{
uint8_t v___x_1596_; uint8_t v___x_1597_; 
v___x_1596_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_1597_ = lean_uint8_dec_le(v_c_1548_, v___x_1596_);
if (v___x_1597_ == 0)
{
goto v___jp_1588_;
}
else
{
v___y_1550_ = v___x_1597_;
goto v___jp_1549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0___boxed(lean_object* v_c_1602_){
_start:
{
uint8_t v_c_boxed_1603_; uint8_t v_res_1604_; lean_object* v_r_1605_; 
v_c_boxed_1603_ = lean_unbox(v_c_1602_);
v_res_1604_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(v_c_boxed_1603_);
v_r_1605_ = lean_box(v_res_1604_);
return v_r_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(lean_object* v_config_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v_maxSegmentLength_1609_; lean_object* v___f_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v_snd_1613_; lean_object* v_fst_1614_; lean_object* v_fst_1615_; lean_object* v_array_1616_; lean_object* v_idx_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1634_; 
v_maxSegmentLength_1609_ = lean_ctor_get(v_config_1607_, 3);
v___f_1610_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0));
v___x_1611_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1608_);
v___x_1612_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1610_, v_maxSegmentLength_1609_, v___x_1611_, v_a_1608_);
v_snd_1613_ = lean_ctor_get(v___x_1612_, 1);
lean_inc(v_snd_1613_);
v_fst_1614_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_fst_1614_);
lean_dec_ref(v___x_1612_);
v_fst_1615_ = lean_ctor_get(v_snd_1613_, 0);
lean_inc(v_fst_1615_);
lean_dec(v_snd_1613_);
v_array_1616_ = lean_ctor_get(v_a_1608_, 0);
v_idx_1617_ = lean_ctor_get(v_a_1608_, 1);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_a_1608_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1619_ = v_a_1608_;
v_isShared_1620_ = v_isSharedCheck_1634_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_idx_1617_);
lean_inc(v_array_1616_);
lean_dec(v_a_1608_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1634_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v_lower_1622_; lean_object* v_upper_1623_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___y_1631_; uint8_t v___x_1633_; 
v___x_1628_ = lean_nat_add(v_idx_1617_, v_fst_1614_);
lean_dec(v_fst_1614_);
v___x_1629_ = lean_byte_array_size(v_array_1616_);
v___x_1633_ = lean_nat_dec_le(v_idx_1617_, v___x_1611_);
if (v___x_1633_ == 0)
{
v___y_1631_ = v_idx_1617_;
goto v___jp_1630_;
}
else
{
lean_dec(v_idx_1617_);
v___y_1631_ = v___x_1611_;
goto v___jp_1630_;
}
v___jp_1621_:
{
lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1624_ = l_ByteArray_toByteSlice(v_array_1616_, v_lower_1622_, v_upper_1623_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 1, v___x_1624_);
lean_ctor_set(v___x_1619_, 0, v_fst_1615_);
v___x_1626_ = v___x_1619_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_fst_1615_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v___x_1624_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
v___jp_1630_:
{
uint8_t v___x_1632_; 
v___x_1632_ = lean_nat_dec_le(v___x_1628_, v___x_1629_);
if (v___x_1632_ == 0)
{
lean_dec(v___x_1628_);
v_lower_1622_ = v___y_1631_;
v_upper_1623_ = v___x_1629_;
goto v___jp_1621_;
}
else
{
v_lower_1622_ = v___y_1631_;
v_upper_1623_ = v___x_1628_;
goto v___jp_1621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___boxed(lean_object* v_config_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1635_, v_a_1636_);
lean_dec_ref(v_config_1635_);
return v_res_1637_;
}
}
LEAN_EXPORT uint8_t l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(uint8_t v_c_1638_){
_start:
{
uint8_t v___x_1639_; uint8_t v___x_1640_; 
v___x_1639_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_1640_ = lean_uint8_dec_eq(v_c_1638_, v___x_1639_);
if (v___x_1640_ == 0)
{
uint8_t v___x_1641_; uint8_t v___x_1642_; 
v___x_1641_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v___x_1642_ = lean_uint8_dec_eq(v_c_1638_, v___x_1641_);
return v___x_1642_;
}
else
{
return v___x_1640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0___boxed(lean_object* v_c_1643_){
_start:
{
uint8_t v_c_boxed_1644_; uint8_t v_res_1645_; lean_object* v_r_1646_; 
v_c_boxed_1644_ = lean_unbox(v_c_1643_);
v_res_1645_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v_c_boxed_1644_);
v_r_1646_ = lean_box(v_res_1645_);
return v_r_1646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(lean_object* v_config_1654_, lean_object* v_a_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v_array_1681_; lean_object* v_idx_1682_; lean_object* v_fst_1683_; lean_object* v_snd_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1860_; 
v_array_1681_ = lean_ctor_get(v___y_1656_, 0);
v_idx_1682_ = lean_ctor_get(v___y_1656_, 1);
v_fst_1683_ = lean_ctor_get(v_a_1655_, 0);
v_snd_1684_ = lean_ctor_get(v_a_1655_, 1);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_a_1655_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1686_ = v_a_1655_;
v_isShared_1687_ = v_isSharedCheck_1860_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_snd_1684_);
lean_inc(v_fst_1683_);
lean_dec(v_a_1655_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1860_;
goto v_resetjp_1685_;
}
v___jp_1657_:
{
lean_object* v___x_1662_; uint8_t v___x_1663_; 
v___x_1662_ = lean_array_get_size(v___y_1660_);
v___x_1663_ = lean_nat_dec_le(v___y_1658_, v___x_1662_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
lean_dec(v___y_1658_);
v___x_1664_ = l_ByteArray_empty;
v___x_1665_ = lean_array_push(v___y_1660_, v___x_1664_);
v___x_1666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
lean_ctor_set(v___x_1666_, 1, v___y_1659_);
v_a_1655_ = v___x_1666_;
v___y_1656_ = v___y_1661_;
goto _start;
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v_config_1654_);
v___x_1668_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1669_ = l_Nat_reprFast(v___y_1658_);
v___x_1670_ = lean_string_append(v___x_1668_, v___x_1669_);
lean_dec_ref(v___x_1669_);
v___x_1671_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1672_ = lean_string_append(v___x_1670_, v___x_1671_);
v___x_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
v___x_1674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___y_1661_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
return v___x_1674_;
}
}
v___jp_1675_:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___y_1678_);
lean_ctor_set(v___x_1679_, 1, v___y_1676_);
v___x_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___y_1677_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
return v___x_1680_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; uint8_t v___x_1689_; 
v___x_1688_ = lean_byte_array_size(v_array_1681_);
v___x_1689_ = lean_nat_dec_lt(v_idx_1682_, v___x_1688_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1691_; 
lean_dec_ref(v_config_1654_);
if (v_isShared_1687_ == 0)
{
v___x_1691_ = v___x_1686_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_fst_1683_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_snd_1684_);
v___x_1691_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___y_1656_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
return v___x_1692_;
}
}
else
{
if (v___x_1689_ == 0)
{
lean_object* v___x_1695_; 
lean_dec_ref(v_config_1654_);
if (v_isShared_1687_ == 0)
{
v___x_1695_ = v___x_1686_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_fst_1683_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v_snd_1684_);
v___x_1695_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
lean_object* v___x_1696_; 
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___y_1656_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
return v___x_1696_;
}
}
else
{
uint8_t v___x_1698_; uint8_t v___x_1699_; 
v___x_1698_ = lean_byte_array_fget(v_array_1681_, v_idx_1682_);
v___x_1699_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1698_);
if (v___x_1699_ == 0)
{
uint8_t v___x_1700_; uint8_t v___y_1797_; uint8_t v___x_1800_; uint8_t v___y_1802_; uint8_t v___y_1804_; uint8_t v___x_1852_; uint8_t v___x_1853_; 
v___x_1700_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_1800_ = lean_uint8_dec_eq(v___x_1698_, v___x_1700_);
v___x_1852_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_1853_ = lean_uint8_dec_le(v___x_1852_, v___x_1698_);
if (v___x_1853_ == 0)
{
goto v___jp_1847_;
}
else
{
uint8_t v___x_1854_; uint8_t v___x_1855_; 
v___x_1854_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_1855_ = lean_uint8_dec_le(v___x_1698_, v___x_1854_);
if (v___x_1855_ == 0)
{
goto v___jp_1847_;
}
else
{
v___y_1804_ = v___x_1855_;
goto v___jp_1803_;
}
}
v___jp_1701_:
{
lean_object* v_maxPathSegments_1702_; lean_object* v_maxTotalPathLength_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; 
v_maxPathSegments_1702_ = lean_ctor_get(v_config_1654_, 6);
v_maxTotalPathLength_1703_ = lean_ctor_get(v_config_1654_, 7);
v___x_1704_ = lean_array_get_size(v_fst_1683_);
v___x_1705_ = lean_nat_dec_le(v_maxPathSegments_1702_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; 
v___x_1706_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1654_, v___y_1656_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_pos_1707_; lean_object* v_res_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1779_; 
v_pos_1707_ = lean_ctor_get(v___x_1706_, 0);
v_res_1708_ = lean_ctor_get(v___x_1706_, 1);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1710_ = v___x_1706_;
v_isShared_1711_ = v_isSharedCheck_1779_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_res_1708_);
lean_inc(v_pos_1707_);
lean_dec(v___x_1706_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1779_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
lean_inc(v_res_1708_);
v___x_1712_ = l_ByteSlice_toByteArray(v_res_1708_);
v___x_1713_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1712_);
if (lean_obj_tag(v___x_1713_) == 1)
{
lean_object* v_val_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1774_; 
v_val_1714_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1716_ = v___x_1713_;
v_isShared_1717_ = v_isSharedCheck_1774_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_val_1714_);
lean_dec(v___x_1713_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1774_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; uint8_t v___x_1720_; 
v___x_1718_ = l_ByteSlice_size(v_res_1708_);
lean_dec(v_res_1708_);
v___x_1719_ = lean_nat_add(v_snd_1684_, v___x_1718_);
lean_dec(v___x_1718_);
lean_dec(v_snd_1684_);
v___x_1720_ = lean_nat_dec_lt(v_maxTotalPathLength_1703_, v___x_1719_);
if (v___x_1720_ == 0)
{
lean_object* v_array_1721_; lean_object* v_idx_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; 
v_array_1721_ = lean_ctor_get(v_pos_1707_, 0);
v_idx_1722_ = lean_ctor_get(v_pos_1707_, 1);
v___x_1723_ = lean_array_push(v_fst_1683_, v_val_1714_);
v___x_1724_ = lean_byte_array_size(v_array_1721_);
v___x_1725_ = lean_nat_dec_lt(v_idx_1722_, v___x_1724_);
if (v___x_1725_ == 0)
{
lean_del_object(v___x_1716_);
lean_del_object(v___x_1710_);
lean_del_object(v___x_1686_);
lean_dec_ref(v_config_1654_);
v___y_1676_ = v___x_1719_;
v___y_1677_ = v_pos_1707_;
v___y_1678_ = v___x_1723_;
goto v___jp_1675_;
}
else
{
uint8_t v___x_1726_; uint8_t v___x_1727_; 
v___x_1726_ = lean_byte_array_fget(v_array_1721_, v_idx_1722_);
v___x_1727_ = lean_uint8_dec_eq(v___x_1726_, v___x_1700_);
if (v___x_1727_ == 0)
{
lean_del_object(v___x_1716_);
lean_del_object(v___x_1710_);
lean_del_object(v___x_1686_);
lean_dec_ref(v_config_1654_);
v___y_1676_ = v___x_1719_;
v___y_1677_ = v_pos_1707_;
v___y_1678_ = v___x_1723_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1729_; uint8_t v___x_1730_; 
v___x_1728_ = lean_unsigned_to_nat(1u);
v___x_1729_ = lean_nat_add(v___x_1719_, v___x_1728_);
lean_dec(v___x_1719_);
v___x_1730_ = lean_nat_dec_lt(v_maxTotalPathLength_1703_, v___x_1729_);
if (v___x_1730_ == 0)
{
lean_del_object(v___x_1716_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1731_; lean_object* v___x_1733_; 
lean_dec(v___x_1729_);
lean_dec_ref(v___x_1723_);
lean_del_object(v___x_1686_);
lean_dec_ref(v_config_1654_);
v___x_1731_ = lean_box(0);
if (v_isShared_1711_ == 0)
{
lean_ctor_set_tag(v___x_1710_, 1);
lean_ctor_set(v___x_1710_, 1, v___x_1731_);
v___x_1733_ = v___x_1710_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_pos_1707_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v___x_1731_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
else
{
lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1749_; 
lean_inc(v_idx_1722_);
lean_inc_ref(v_array_1721_);
lean_del_object(v___x_1710_);
v_isSharedCheck_1749_ = !lean_is_exclusive(v_pos_1707_);
if (v_isSharedCheck_1749_ == 0)
{
lean_object* v_unused_1750_; lean_object* v_unused_1751_; 
v_unused_1750_ = lean_ctor_get(v_pos_1707_, 1);
lean_dec(v_unused_1750_);
v_unused_1751_ = lean_ctor_get(v_pos_1707_, 0);
lean_dec(v_unused_1751_);
v___x_1736_ = v_pos_1707_;
v_isShared_1737_ = v_isSharedCheck_1749_;
goto v_resetjp_1735_;
}
else
{
lean_dec(v_pos_1707_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1749_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1738_ = lean_nat_add(v_idx_1722_, v___x_1728_);
lean_dec(v_idx_1722_);
lean_inc(v___x_1738_);
lean_inc_ref(v_array_1721_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 1, v___x_1738_);
v___x_1740_ = v___x_1736_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_array_1721_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
uint8_t v___x_1741_; 
v___x_1741_ = lean_nat_dec_lt(v___x_1738_, v___x_1724_);
if (v___x_1741_ == 0)
{
lean_dec(v___x_1738_);
lean_dec_ref(v_array_1721_);
lean_del_object(v___x_1686_);
lean_inc(v_maxPathSegments_1702_);
v___y_1658_ = v_maxPathSegments_1702_;
v___y_1659_ = v___x_1729_;
v___y_1660_ = v___x_1723_;
v___y_1661_ = v___x_1740_;
goto v___jp_1657_;
}
else
{
uint8_t v___x_1742_; uint8_t v___x_1743_; 
v___x_1742_ = lean_byte_array_fget(v_array_1721_, v___x_1738_);
lean_dec(v___x_1738_);
lean_dec_ref(v_array_1721_);
v___x_1743_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1742_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1745_; 
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 1, v___x_1729_);
lean_ctor_set(v___x_1686_, 0, v___x_1723_);
v___x_1745_ = v___x_1686_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1723_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v___x_1729_);
v___x_1745_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
v_a_1655_ = v___x_1745_;
v___y_1656_ = v___x_1740_;
goto _start;
}
}
else
{
lean_del_object(v___x_1686_);
lean_inc(v_maxPathSegments_1702_);
v___y_1658_ = v_maxPathSegments_1702_;
v___y_1659_ = v___x_1729_;
v___y_1660_ = v___x_1723_;
v___y_1661_ = v___x_1740_;
goto v___jp_1657_;
}
}
}
}
}
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1758_; 
lean_inc(v_maxTotalPathLength_1703_);
lean_dec(v___x_1729_);
lean_dec_ref(v___x_1723_);
lean_del_object(v___x_1686_);
lean_dec_ref(v_config_1654_);
v___x_1752_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1753_ = l_Nat_reprFast(v_maxTotalPathLength_1703_);
v___x_1754_ = lean_string_append(v___x_1752_, v___x_1753_);
lean_dec_ref(v___x_1753_);
v___x_1755_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1756_ = lean_string_append(v___x_1754_, v___x_1755_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 0, v___x_1756_);
v___x_1758_ = v___x_1716_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1760_; 
if (v_isShared_1711_ == 0)
{
lean_ctor_set_tag(v___x_1710_, 1);
lean_ctor_set(v___x_1710_, 1, v___x_1758_);
v___x_1760_ = v___x_1710_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_pos_1707_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v___x_1758_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
}
}
else
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1769_; 
lean_inc(v_maxTotalPathLength_1703_);
lean_dec(v___x_1719_);
lean_dec(v_val_1714_);
lean_del_object(v___x_1686_);
lean_dec(v_fst_1683_);
lean_dec_ref(v_config_1654_);
v___x_1763_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1764_ = l_Nat_reprFast(v_maxTotalPathLength_1703_);
v___x_1765_ = lean_string_append(v___x_1763_, v___x_1764_);
lean_dec_ref(v___x_1764_);
v___x_1766_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1767_ = lean_string_append(v___x_1765_, v___x_1766_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 0, v___x_1767_);
v___x_1769_ = v___x_1716_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1767_);
v___x_1769_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
lean_object* v___x_1771_; 
if (v_isShared_1711_ == 0)
{
lean_ctor_set_tag(v___x_1710_, 1);
lean_ctor_set(v___x_1710_, 1, v___x_1769_);
v___x_1771_ = v___x_1710_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_pos_1707_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
}
else
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
lean_dec(v___x_1713_);
lean_dec(v_res_1708_);
lean_del_object(v___x_1686_);
lean_dec(v_snd_1684_);
lean_dec(v_fst_1683_);
lean_dec_ref(v_config_1654_);
v___x_1775_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5));
if (v_isShared_1711_ == 0)
{
lean_ctor_set_tag(v___x_1710_, 1);
lean_ctor_set(v___x_1710_, 1, v___x_1775_);
v___x_1777_ = v___x_1710_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_pos_1707_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
else
{
lean_object* v_pos_1780_; lean_object* v_err_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_del_object(v___x_1686_);
lean_dec(v_snd_1684_);
lean_dec(v_fst_1683_);
lean_dec_ref(v_config_1654_);
v_pos_1780_ = lean_ctor_get(v___x_1706_, 0);
v_err_1781_ = lean_ctor_get(v___x_1706_, 1);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1706_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_err_1781_);
lean_inc(v_pos_1780_);
lean_dec(v___x_1706_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_pos_1780_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_err_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
else
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
lean_inc(v_maxPathSegments_1702_);
lean_del_object(v___x_1686_);
lean_dec(v_snd_1684_);
lean_dec(v_fst_1683_);
lean_dec_ref(v_config_1654_);
v___x_1789_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1790_ = l_Nat_reprFast(v_maxPathSegments_1702_);
v___x_1791_ = lean_string_append(v___x_1789_, v___x_1790_);
lean_dec_ref(v___x_1790_);
v___x_1792_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1793_ = lean_string_append(v___x_1791_, v___x_1792_);
v___x_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
v___x_1795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___y_1656_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
return v___x_1795_;
}
}
v___jp_1796_:
{
if (v___y_1797_ == 0)
{
if (v___x_1689_ == 0)
{
goto v___jp_1701_;
}
else
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
lean_del_object(v___x_1686_);
lean_dec_ref(v_config_1654_);
v___x_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1798_, 0, v_fst_1683_);
lean_ctor_set(v___x_1798_, 1, v_snd_1684_);
v___x_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___y_1656_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
return v___x_1799_;
}
}
else
{
goto v___jp_1701_;
}
}
v___jp_1801_:
{
if (v___x_1800_ == 0)
{
v___y_1797_ = v___y_1802_;
goto v___jp_1796_;
}
else
{
v___y_1797_ = v___x_1800_;
goto v___jp_1796_;
}
}
v___jp_1803_:
{
if (v___y_1804_ == 0)
{
uint8_t v___x_1805_; uint8_t v___x_1806_; 
v___x_1805_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1806_ = lean_uint8_dec_eq(v___x_1698_, v___x_1805_);
v___y_1802_ = v___x_1806_;
goto v___jp_1801_;
}
else
{
v___y_1802_ = v___y_1804_;
goto v___jp_1801_;
}
}
v___jp_1807_:
{
uint8_t v___x_1808_; uint8_t v___x_1809_; 
v___x_1808_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_1809_ = lean_uint8_dec_eq(v___x_1698_, v___x_1808_);
if (v___x_1809_ == 0)
{
uint8_t v___x_1810_; uint8_t v___x_1811_; 
v___x_1810_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_1811_ = lean_uint8_dec_eq(v___x_1698_, v___x_1810_);
if (v___x_1811_ == 0)
{
uint8_t v___x_1812_; uint8_t v___x_1813_; 
v___x_1812_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_1813_ = lean_uint8_dec_eq(v___x_1698_, v___x_1812_);
if (v___x_1813_ == 0)
{
uint8_t v___x_1814_; uint8_t v___x_1815_; 
v___x_1814_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_1815_ = lean_uint8_dec_eq(v___x_1698_, v___x_1814_);
if (v___x_1815_ == 0)
{
uint8_t v___x_1816_; uint8_t v___x_1817_; 
v___x_1816_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_1817_ = lean_uint8_dec_eq(v___x_1698_, v___x_1816_);
if (v___x_1817_ == 0)
{
uint8_t v___x_1818_; uint8_t v___x_1819_; 
v___x_1818_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_1819_ = lean_uint8_dec_eq(v___x_1698_, v___x_1818_);
if (v___x_1819_ == 0)
{
uint8_t v___x_1820_; uint8_t v___x_1821_; 
v___x_1820_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_1821_ = lean_uint8_dec_eq(v___x_1698_, v___x_1820_);
if (v___x_1821_ == 0)
{
uint8_t v___x_1822_; uint8_t v___x_1823_; 
v___x_1822_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_1823_ = lean_uint8_dec_eq(v___x_1698_, v___x_1822_);
if (v___x_1823_ == 0)
{
uint8_t v___x_1824_; uint8_t v___x_1825_; 
v___x_1824_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_1825_ = lean_uint8_dec_eq(v___x_1698_, v___x_1824_);
if (v___x_1825_ == 0)
{
uint8_t v___x_1826_; uint8_t v___x_1827_; 
v___x_1826_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_1827_ = lean_uint8_dec_eq(v___x_1698_, v___x_1826_);
if (v___x_1827_ == 0)
{
uint8_t v___x_1828_; uint8_t v___x_1829_; 
v___x_1828_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_1829_ = lean_uint8_dec_eq(v___x_1698_, v___x_1828_);
if (v___x_1829_ == 0)
{
uint8_t v___x_1830_; uint8_t v___x_1831_; 
v___x_1830_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_1831_ = lean_uint8_dec_eq(v___x_1698_, v___x_1830_);
if (v___x_1831_ == 0)
{
uint8_t v___x_1832_; uint8_t v___x_1833_; 
v___x_1832_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_1833_ = lean_uint8_dec_eq(v___x_1698_, v___x_1832_);
if (v___x_1833_ == 0)
{
uint8_t v___x_1834_; uint8_t v___x_1835_; 
v___x_1834_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_1835_ = lean_uint8_dec_eq(v___x_1698_, v___x_1834_);
if (v___x_1835_ == 0)
{
uint8_t v___x_1836_; uint8_t v___x_1837_; 
v___x_1836_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_1837_ = lean_uint8_dec_eq(v___x_1698_, v___x_1836_);
if (v___x_1837_ == 0)
{
uint8_t v___x_1838_; uint8_t v___x_1839_; 
v___x_1838_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_1839_ = lean_uint8_dec_eq(v___x_1698_, v___x_1838_);
if (v___x_1839_ == 0)
{
uint8_t v___x_1840_; uint8_t v___x_1841_; 
v___x_1840_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1841_ = lean_uint8_dec_eq(v___x_1698_, v___x_1840_);
v___y_1804_ = v___x_1841_;
goto v___jp_1803_;
}
else
{
v___y_1804_ = v___x_1839_;
goto v___jp_1803_;
}
}
else
{
v___y_1804_ = v___x_1837_;
goto v___jp_1803_;
}
}
else
{
v___y_1804_ = v___x_1835_;
goto v___jp_1803_;
}
}
else
{
v___y_1804_ = v___x_1833_;
goto v___jp_1803_;
}
}
else
{
v___y_1804_ = v___x_1831_;
goto v___jp_1803_;
}
}
else
{
v___y_1804_ = v___x_1829_;
goto v___jp_1803_;
}
}
else
{
v___y_1804_ = v___x_1827_;
goto v___jp_1803_;
}
}
else
{
v___y_1804_ = v___x_1825_;
goto v___jp_1803_;
}
}
else
{
v___y_1804_ = v___x_1823_;
goto v___jp_1803_;
}
}
else
{
v___y_1804_ = v___x_1821_;
goto v___jp_1803_;
}
}
else
{
v___y_1804_ = v___x_1819_;
goto v___jp_1803_;
}
}
else
{
v___y_1804_ = v___x_1817_;
goto v___jp_1803_;
}
}
else
{
v___y_1804_ = v___x_1815_;
goto v___jp_1803_;
}
}
else
{
v___y_1804_ = v___x_1813_;
goto v___jp_1803_;
}
}
else
{
v___y_1804_ = v___x_1811_;
goto v___jp_1803_;
}
}
else
{
v___y_1804_ = v___x_1809_;
goto v___jp_1803_;
}
}
v___jp_1842_:
{
uint8_t v___x_1843_; uint8_t v___x_1844_; 
v___x_1843_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_1844_ = lean_uint8_dec_le(v___x_1843_, v___x_1698_);
if (v___x_1844_ == 0)
{
goto v___jp_1807_;
}
else
{
uint8_t v___x_1845_; uint8_t v___x_1846_; 
v___x_1845_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_1846_ = lean_uint8_dec_le(v___x_1698_, v___x_1845_);
if (v___x_1846_ == 0)
{
goto v___jp_1807_;
}
else
{
v___y_1804_ = v___x_1846_;
goto v___jp_1803_;
}
}
}
v___jp_1847_:
{
uint8_t v___x_1848_; uint8_t v___x_1849_; 
v___x_1848_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_1849_ = lean_uint8_dec_le(v___x_1848_, v___x_1698_);
if (v___x_1849_ == 0)
{
goto v___jp_1842_;
}
else
{
uint8_t v___x_1850_; uint8_t v___x_1851_; 
v___x_1850_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_1851_ = lean_uint8_dec_le(v___x_1698_, v___x_1850_);
if (v___x_1851_ == 0)
{
goto v___jp_1842_;
}
else
{
v___y_1804_ = v___x_1851_;
goto v___jp_1803_;
}
}
}
}
else
{
lean_object* v___x_1857_; 
lean_dec_ref(v_config_1654_);
if (v_isShared_1687_ == 0)
{
v___x_1857_ = v___x_1686_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_fst_1683_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_snd_1684_);
v___x_1857_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
lean_object* v___x_1858_; 
v___x_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___y_1656_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
return v___x_1858_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(lean_object* v_config_1861_, lean_object* v_a_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v_array_1888_; lean_object* v_idx_1889_; lean_object* v_fst_1890_; lean_object* v_snd_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_2067_; 
v_array_1888_ = lean_ctor_get(v___y_1863_, 0);
v_idx_1889_ = lean_ctor_get(v___y_1863_, 1);
v_fst_1890_ = lean_ctor_get(v_a_1862_, 0);
v_snd_1891_ = lean_ctor_get(v_a_1862_, 1);
v_isSharedCheck_2067_ = !lean_is_exclusive(v_a_1862_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_1893_ = v_a_1862_;
v_isShared_1894_ = v_isSharedCheck_2067_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_snd_1891_);
lean_inc(v_fst_1890_);
lean_dec(v_a_1862_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_2067_;
goto v_resetjp_1892_;
}
v___jp_1864_:
{
lean_object* v___x_1869_; uint8_t v___x_1870_; 
v___x_1869_ = lean_array_get_size(v___y_1867_);
v___x_1870_ = lean_nat_dec_le(v___y_1866_, v___x_1869_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
lean_dec(v___y_1866_);
v___x_1871_ = l_ByteArray_empty;
v___x_1872_ = lean_array_push(v___y_1867_, v___x_1871_);
v___x_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
lean_ctor_set(v___x_1873_, 1, v___y_1865_);
v___x_1874_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1861_, v___x_1873_, v___y_1868_);
return v___x_1874_;
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1865_);
lean_dec_ref(v_config_1861_);
v___x_1875_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1876_ = l_Nat_reprFast(v___y_1866_);
v___x_1877_ = lean_string_append(v___x_1875_, v___x_1876_);
lean_dec_ref(v___x_1876_);
v___x_1878_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1879_ = lean_string_append(v___x_1877_, v___x_1878_);
v___x_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
v___x_1881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___y_1868_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
return v___x_1881_;
}
}
v___jp_1882_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___y_1885_);
lean_ctor_set(v___x_1886_, 1, v___y_1883_);
v___x_1887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1887_, 0, v___y_1884_);
lean_ctor_set(v___x_1887_, 1, v___x_1886_);
return v___x_1887_;
}
v_resetjp_1892_:
{
lean_object* v___x_1895_; uint8_t v___x_1896_; 
v___x_1895_ = lean_byte_array_size(v_array_1888_);
v___x_1896_ = lean_nat_dec_lt(v_idx_1889_, v___x_1895_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1898_; 
lean_dec_ref(v_config_1861_);
if (v_isShared_1894_ == 0)
{
v___x_1898_ = v___x_1893_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_fst_1890_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_snd_1891_);
v___x_1898_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1899_; 
v___x_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___y_1863_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
return v___x_1899_;
}
}
else
{
if (v___x_1896_ == 0)
{
lean_object* v___x_1902_; 
lean_dec_ref(v_config_1861_);
if (v_isShared_1894_ == 0)
{
v___x_1902_ = v___x_1893_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_fst_1890_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_snd_1891_);
v___x_1902_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
lean_object* v___x_1903_; 
v___x_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___y_1863_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
return v___x_1903_;
}
}
else
{
uint8_t v___x_1905_; uint8_t v___x_1906_; 
v___x_1905_ = lean_byte_array_fget(v_array_1888_, v_idx_1889_);
v___x_1906_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1905_);
if (v___x_1906_ == 0)
{
uint8_t v___x_1907_; uint8_t v___y_2004_; uint8_t v___x_2007_; uint8_t v___y_2009_; uint8_t v___y_2011_; uint8_t v___x_2059_; uint8_t v___x_2060_; 
v___x_1907_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2007_ = lean_uint8_dec_eq(v___x_1905_, v___x_1907_);
v___x_2059_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_2060_ = lean_uint8_dec_le(v___x_2059_, v___x_1905_);
if (v___x_2060_ == 0)
{
goto v___jp_2054_;
}
else
{
uint8_t v___x_2061_; uint8_t v___x_2062_; 
v___x_2061_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_2062_ = lean_uint8_dec_le(v___x_1905_, v___x_2061_);
if (v___x_2062_ == 0)
{
goto v___jp_2054_;
}
else
{
v___y_2011_ = v___x_2062_;
goto v___jp_2010_;
}
}
v___jp_1908_:
{
lean_object* v_maxPathSegments_1909_; lean_object* v_maxTotalPathLength_1910_; lean_object* v___x_1911_; uint8_t v___x_1912_; 
v_maxPathSegments_1909_ = lean_ctor_get(v_config_1861_, 6);
v_maxTotalPathLength_1910_ = lean_ctor_get(v_config_1861_, 7);
v___x_1911_ = lean_array_get_size(v_fst_1890_);
v___x_1912_ = lean_nat_dec_le(v_maxPathSegments_1909_, v___x_1911_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; 
v___x_1913_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1861_, v___y_1863_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_pos_1914_; lean_object* v_res_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1986_; 
v_pos_1914_ = lean_ctor_get(v___x_1913_, 0);
v_res_1915_ = lean_ctor_get(v___x_1913_, 1);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1917_ = v___x_1913_;
v_isShared_1918_ = v_isSharedCheck_1986_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_res_1915_);
lean_inc(v_pos_1914_);
lean_dec(v___x_1913_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1986_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
lean_inc(v_res_1915_);
v___x_1919_ = l_ByteSlice_toByteArray(v_res_1915_);
v___x_1920_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1919_);
if (lean_obj_tag(v___x_1920_) == 1)
{
lean_object* v_val_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1981_; 
v_val_1921_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1923_ = v___x_1920_;
v_isShared_1924_ = v_isSharedCheck_1981_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_val_1921_);
lean_dec(v___x_1920_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1981_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; 
v___x_1925_ = l_ByteSlice_size(v_res_1915_);
lean_dec(v_res_1915_);
v___x_1926_ = lean_nat_add(v_snd_1891_, v___x_1925_);
lean_dec(v___x_1925_);
lean_dec(v_snd_1891_);
v___x_1927_ = lean_nat_dec_lt(v_maxTotalPathLength_1910_, v___x_1926_);
if (v___x_1927_ == 0)
{
lean_object* v_array_1928_; lean_object* v_idx_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; 
v_array_1928_ = lean_ctor_get(v_pos_1914_, 0);
v_idx_1929_ = lean_ctor_get(v_pos_1914_, 1);
v___x_1930_ = lean_array_push(v_fst_1890_, v_val_1921_);
v___x_1931_ = lean_byte_array_size(v_array_1928_);
v___x_1932_ = lean_nat_dec_lt(v_idx_1929_, v___x_1931_);
if (v___x_1932_ == 0)
{
lean_del_object(v___x_1923_);
lean_del_object(v___x_1917_);
lean_del_object(v___x_1893_);
lean_dec_ref(v_config_1861_);
v___y_1883_ = v___x_1926_;
v___y_1884_ = v_pos_1914_;
v___y_1885_ = v___x_1930_;
goto v___jp_1882_;
}
else
{
uint8_t v___x_1933_; uint8_t v___x_1934_; 
v___x_1933_ = lean_byte_array_fget(v_array_1928_, v_idx_1929_);
v___x_1934_ = lean_uint8_dec_eq(v___x_1933_, v___x_1907_);
if (v___x_1934_ == 0)
{
lean_del_object(v___x_1923_);
lean_del_object(v___x_1917_);
lean_del_object(v___x_1893_);
lean_dec_ref(v_config_1861_);
v___y_1883_ = v___x_1926_;
v___y_1884_ = v_pos_1914_;
v___y_1885_ = v___x_1930_;
goto v___jp_1882_;
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; 
v___x_1935_ = lean_unsigned_to_nat(1u);
v___x_1936_ = lean_nat_add(v___x_1926_, v___x_1935_);
lean_dec(v___x_1926_);
v___x_1937_ = lean_nat_dec_lt(v_maxTotalPathLength_1910_, v___x_1936_);
if (v___x_1937_ == 0)
{
lean_del_object(v___x_1923_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1938_; lean_object* v___x_1940_; 
lean_dec(v___x_1936_);
lean_dec_ref(v___x_1930_);
lean_del_object(v___x_1893_);
lean_dec_ref(v_config_1861_);
v___x_1938_ = lean_box(0);
if (v_isShared_1918_ == 0)
{
lean_ctor_set_tag(v___x_1917_, 1);
lean_ctor_set(v___x_1917_, 1, v___x_1938_);
v___x_1940_ = v___x_1917_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_pos_1914_);
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
lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1956_; 
lean_inc(v_idx_1929_);
lean_inc_ref(v_array_1928_);
lean_del_object(v___x_1917_);
v_isSharedCheck_1956_ = !lean_is_exclusive(v_pos_1914_);
if (v_isSharedCheck_1956_ == 0)
{
lean_object* v_unused_1957_; lean_object* v_unused_1958_; 
v_unused_1957_ = lean_ctor_get(v_pos_1914_, 1);
lean_dec(v_unused_1957_);
v_unused_1958_ = lean_ctor_get(v_pos_1914_, 0);
lean_dec(v_unused_1958_);
v___x_1943_ = v_pos_1914_;
v_isShared_1944_ = v_isSharedCheck_1956_;
goto v_resetjp_1942_;
}
else
{
lean_dec(v_pos_1914_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1956_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1945_; lean_object* v___x_1947_; 
v___x_1945_ = lean_nat_add(v_idx_1929_, v___x_1935_);
lean_dec(v_idx_1929_);
lean_inc(v___x_1945_);
lean_inc_ref(v_array_1928_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 1, v___x_1945_);
v___x_1947_ = v___x_1943_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_array_1928_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
uint8_t v___x_1948_; 
v___x_1948_ = lean_nat_dec_lt(v___x_1945_, v___x_1931_);
if (v___x_1948_ == 0)
{
lean_dec(v___x_1945_);
lean_dec_ref(v_array_1928_);
lean_del_object(v___x_1893_);
lean_inc(v_maxPathSegments_1909_);
v___y_1865_ = v___x_1936_;
v___y_1866_ = v_maxPathSegments_1909_;
v___y_1867_ = v___x_1930_;
v___y_1868_ = v___x_1947_;
goto v___jp_1864_;
}
else
{
uint8_t v___x_1949_; uint8_t v___x_1950_; 
v___x_1949_ = lean_byte_array_fget(v_array_1928_, v___x_1945_);
lean_dec(v___x_1945_);
lean_dec_ref(v_array_1928_);
v___x_1950_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg___lam__0(v___x_1949_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1952_; 
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 1, v___x_1936_);
lean_ctor_set(v___x_1893_, 0, v___x_1930_);
v___x_1952_ = v___x_1893_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1930_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v___x_1936_);
v___x_1952_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
lean_object* v___x_1953_; 
v___x_1953_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1861_, v___x_1952_, v___x_1947_);
return v___x_1953_;
}
}
else
{
lean_del_object(v___x_1893_);
lean_inc(v_maxPathSegments_1909_);
v___y_1865_ = v___x_1936_;
v___y_1866_ = v_maxPathSegments_1909_;
v___y_1867_ = v___x_1930_;
v___y_1868_ = v___x_1947_;
goto v___jp_1864_;
}
}
}
}
}
}
else
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1965_; 
lean_inc(v_maxTotalPathLength_1910_);
lean_dec(v___x_1936_);
lean_dec_ref(v___x_1930_);
lean_del_object(v___x_1893_);
lean_dec_ref(v_config_1861_);
v___x_1959_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1960_ = l_Nat_reprFast(v_maxTotalPathLength_1910_);
v___x_1961_ = lean_string_append(v___x_1959_, v___x_1960_);
lean_dec_ref(v___x_1960_);
v___x_1962_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1963_ = lean_string_append(v___x_1961_, v___x_1962_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1963_);
v___x_1965_ = v___x_1923_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1963_);
v___x_1965_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
lean_object* v___x_1967_; 
if (v_isShared_1918_ == 0)
{
lean_ctor_set_tag(v___x_1917_, 1);
lean_ctor_set(v___x_1917_, 1, v___x_1965_);
v___x_1967_ = v___x_1917_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_pos_1914_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
}
else
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1976_; 
lean_inc(v_maxTotalPathLength_1910_);
lean_dec(v___x_1926_);
lean_dec(v_val_1921_);
lean_del_object(v___x_1893_);
lean_dec(v_fst_1890_);
lean_dec_ref(v_config_1861_);
v___x_1970_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__2));
v___x_1971_ = l_Nat_reprFast(v_maxTotalPathLength_1910_);
v___x_1972_ = lean_string_append(v___x_1970_, v___x_1971_);
lean_dec_ref(v___x_1971_);
v___x_1973_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__3));
v___x_1974_ = lean_string_append(v___x_1972_, v___x_1973_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1974_);
v___x_1976_ = v___x_1923_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1974_);
v___x_1976_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1978_; 
if (v_isShared_1918_ == 0)
{
lean_ctor_set_tag(v___x_1917_, 1);
lean_ctor_set(v___x_1917_, 1, v___x_1976_);
v___x_1978_ = v___x_1917_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_pos_1914_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1984_; 
lean_dec(v___x_1920_);
lean_dec(v_res_1915_);
lean_del_object(v___x_1893_);
lean_dec(v_snd_1891_);
lean_dec(v_fst_1890_);
lean_dec_ref(v_config_1861_);
v___x_1982_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__5));
if (v_isShared_1918_ == 0)
{
lean_ctor_set_tag(v___x_1917_, 1);
lean_ctor_set(v___x_1917_, 1, v___x_1982_);
v___x_1984_ = v___x_1917_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_pos_1914_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v___x_1982_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
else
{
lean_object* v_pos_1987_; lean_object* v_err_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_del_object(v___x_1893_);
lean_dec(v_snd_1891_);
lean_dec(v_fst_1890_);
lean_dec_ref(v_config_1861_);
v_pos_1987_ = lean_ctor_get(v___x_1913_, 0);
v_err_1988_ = lean_ctor_get(v___x_1913_, 1);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1913_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_err_1988_);
lean_inc(v_pos_1987_);
lean_dec(v___x_1913_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_pos_1987_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_err_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
else
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
lean_inc(v_maxPathSegments_1909_);
lean_del_object(v___x_1893_);
lean_dec(v_snd_1891_);
lean_dec(v_fst_1890_);
lean_dec_ref(v_config_1861_);
v___x_1996_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1997_ = l_Nat_reprFast(v_maxPathSegments_1909_);
v___x_1998_ = lean_string_append(v___x_1996_, v___x_1997_);
lean_dec_ref(v___x_1997_);
v___x_1999_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_2000_ = lean_string_append(v___x_1998_, v___x_1999_);
v___x_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
v___x_2002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___y_1863_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
return v___x_2002_;
}
}
v___jp_2003_:
{
if (v___y_2004_ == 0)
{
if (v___x_1896_ == 0)
{
goto v___jp_1908_;
}
else
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
lean_del_object(v___x_1893_);
lean_dec_ref(v_config_1861_);
v___x_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2005_, 0, v_fst_1890_);
lean_ctor_set(v___x_2005_, 1, v_snd_1891_);
v___x_2006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___y_1863_);
lean_ctor_set(v___x_2006_, 1, v___x_2005_);
return v___x_2006_;
}
}
else
{
goto v___jp_1908_;
}
}
v___jp_2008_:
{
if (v___x_2007_ == 0)
{
v___y_2004_ = v___y_2009_;
goto v___jp_2003_;
}
else
{
v___y_2004_ = v___x_2007_;
goto v___jp_2003_;
}
}
v___jp_2010_:
{
if (v___y_2011_ == 0)
{
uint8_t v___x_2012_; uint8_t v___x_2013_; 
v___x_2012_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_2013_ = lean_uint8_dec_eq(v___x_1905_, v___x_2012_);
v___y_2009_ = v___x_2013_;
goto v___jp_2008_;
}
else
{
v___y_2009_ = v___y_2011_;
goto v___jp_2008_;
}
}
v___jp_2014_:
{
uint8_t v___x_2015_; uint8_t v___x_2016_; 
v___x_2015_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_2016_ = lean_uint8_dec_eq(v___x_1905_, v___x_2015_);
if (v___x_2016_ == 0)
{
uint8_t v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_2018_ = lean_uint8_dec_eq(v___x_1905_, v___x_2017_);
if (v___x_2018_ == 0)
{
uint8_t v___x_2019_; uint8_t v___x_2020_; 
v___x_2019_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_2020_ = lean_uint8_dec_eq(v___x_1905_, v___x_2019_);
if (v___x_2020_ == 0)
{
uint8_t v___x_2021_; uint8_t v___x_2022_; 
v___x_2021_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_2022_ = lean_uint8_dec_eq(v___x_1905_, v___x_2021_);
if (v___x_2022_ == 0)
{
uint8_t v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_2024_ = lean_uint8_dec_eq(v___x_1905_, v___x_2023_);
if (v___x_2024_ == 0)
{
uint8_t v___x_2025_; uint8_t v___x_2026_; 
v___x_2025_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_2026_ = lean_uint8_dec_eq(v___x_1905_, v___x_2025_);
if (v___x_2026_ == 0)
{
uint8_t v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_2028_ = lean_uint8_dec_eq(v___x_1905_, v___x_2027_);
if (v___x_2028_ == 0)
{
uint8_t v___x_2029_; uint8_t v___x_2030_; 
v___x_2029_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_2030_ = lean_uint8_dec_eq(v___x_1905_, v___x_2029_);
if (v___x_2030_ == 0)
{
uint8_t v___x_2031_; uint8_t v___x_2032_; 
v___x_2031_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_2032_ = lean_uint8_dec_eq(v___x_1905_, v___x_2031_);
if (v___x_2032_ == 0)
{
uint8_t v___x_2033_; uint8_t v___x_2034_; 
v___x_2033_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_2034_ = lean_uint8_dec_eq(v___x_1905_, v___x_2033_);
if (v___x_2034_ == 0)
{
uint8_t v___x_2035_; uint8_t v___x_2036_; 
v___x_2035_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_2036_ = lean_uint8_dec_eq(v___x_1905_, v___x_2035_);
if (v___x_2036_ == 0)
{
uint8_t v___x_2037_; uint8_t v___x_2038_; 
v___x_2037_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_2038_ = lean_uint8_dec_eq(v___x_1905_, v___x_2037_);
if (v___x_2038_ == 0)
{
uint8_t v___x_2039_; uint8_t v___x_2040_; 
v___x_2039_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_2040_ = lean_uint8_dec_eq(v___x_1905_, v___x_2039_);
if (v___x_2040_ == 0)
{
uint8_t v___x_2041_; uint8_t v___x_2042_; 
v___x_2041_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_2042_ = lean_uint8_dec_eq(v___x_1905_, v___x_2041_);
if (v___x_2042_ == 0)
{
uint8_t v___x_2043_; uint8_t v___x_2044_; 
v___x_2043_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_2044_ = lean_uint8_dec_eq(v___x_1905_, v___x_2043_);
if (v___x_2044_ == 0)
{
uint8_t v___x_2045_; uint8_t v___x_2046_; 
v___x_2045_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_2046_ = lean_uint8_dec_eq(v___x_1905_, v___x_2045_);
if (v___x_2046_ == 0)
{
uint8_t v___x_2047_; uint8_t v___x_2048_; 
v___x_2047_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_2048_ = lean_uint8_dec_eq(v___x_1905_, v___x_2047_);
v___y_2011_ = v___x_2048_;
goto v___jp_2010_;
}
else
{
v___y_2011_ = v___x_2046_;
goto v___jp_2010_;
}
}
else
{
v___y_2011_ = v___x_2044_;
goto v___jp_2010_;
}
}
else
{
v___y_2011_ = v___x_2042_;
goto v___jp_2010_;
}
}
else
{
v___y_2011_ = v___x_2040_;
goto v___jp_2010_;
}
}
else
{
v___y_2011_ = v___x_2038_;
goto v___jp_2010_;
}
}
else
{
v___y_2011_ = v___x_2036_;
goto v___jp_2010_;
}
}
else
{
v___y_2011_ = v___x_2034_;
goto v___jp_2010_;
}
}
else
{
v___y_2011_ = v___x_2032_;
goto v___jp_2010_;
}
}
else
{
v___y_2011_ = v___x_2030_;
goto v___jp_2010_;
}
}
else
{
v___y_2011_ = v___x_2028_;
goto v___jp_2010_;
}
}
else
{
v___y_2011_ = v___x_2026_;
goto v___jp_2010_;
}
}
else
{
v___y_2011_ = v___x_2024_;
goto v___jp_2010_;
}
}
else
{
v___y_2011_ = v___x_2022_;
goto v___jp_2010_;
}
}
else
{
v___y_2011_ = v___x_2020_;
goto v___jp_2010_;
}
}
else
{
v___y_2011_ = v___x_2018_;
goto v___jp_2010_;
}
}
else
{
v___y_2011_ = v___x_2016_;
goto v___jp_2010_;
}
}
v___jp_2049_:
{
uint8_t v___x_2050_; uint8_t v___x_2051_; 
v___x_2050_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_2051_ = lean_uint8_dec_le(v___x_2050_, v___x_1905_);
if (v___x_2051_ == 0)
{
goto v___jp_2014_;
}
else
{
uint8_t v___x_2052_; uint8_t v___x_2053_; 
v___x_2052_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_2053_ = lean_uint8_dec_le(v___x_1905_, v___x_2052_);
if (v___x_2053_ == 0)
{
goto v___jp_2014_;
}
else
{
v___y_2011_ = v___x_2053_;
goto v___jp_2010_;
}
}
}
v___jp_2054_:
{
uint8_t v___x_2055_; uint8_t v___x_2056_; 
v___x_2055_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_2056_ = lean_uint8_dec_le(v___x_2055_, v___x_1905_);
if (v___x_2056_ == 0)
{
goto v___jp_2049_;
}
else
{
uint8_t v___x_2057_; uint8_t v___x_2058_; 
v___x_2057_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_2058_ = lean_uint8_dec_le(v___x_1905_, v___x_2057_);
if (v___x_2058_ == 0)
{
goto v___jp_2049_;
}
else
{
v___y_2011_ = v___x_2058_;
goto v___jp_2010_;
}
}
}
}
else
{
lean_object* v___x_2064_; 
lean_dec_ref(v_config_1861_);
if (v_isShared_1894_ == 0)
{
v___x_2064_ = v___x_1893_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_fst_1890_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v_snd_1891_);
v___x_2064_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
lean_object* v___x_2065_; 
v___x_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___y_1863_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
return v___x_2065_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath(lean_object* v_config_2079_, uint8_t v_forceAbsolute_2080_, uint8_t v_allowEmpty_2081_, lean_object* v_a_2082_){
_start:
{
lean_object* v___y_2084_; lean_object* v_array_2087_; lean_object* v_idx_2088_; uint8_t v_isAbsolute_2089_; lean_object* v___x_2090_; lean_object* v_segments_2091_; uint8_t v_isAbsolute_2093_; lean_object* v_totalLength_2094_; lean_object* v___y_2095_; lean_object* v___y_2119_; uint8_t v___y_2120_; lean_object* v___y_2124_; uint8_t v___y_2125_; uint8_t v___y_2126_; uint8_t v___y_2128_; lean_object* v_pos_2129_; uint8_t v_res_2130_; uint8_t v___y_2133_; lean_object* v_pos_2134_; uint8_t v_res_2135_; uint8_t v___y_2158_; lean_object* v___y_2159_; uint8_t v___y_2160_; uint8_t v___y_2169_; lean_object* v___y_2170_; uint8_t v___y_2171_; uint8_t v___y_2172_; uint8_t v___y_2176_; uint8_t v___y_2177_; uint8_t v___y_2178_; lean_object* v___y_2179_; uint8_t v___y_2180_; uint8_t v___y_2182_; lean_object* v___y_2183_; uint8_t v___y_2184_; uint8_t v___y_2185_; uint8_t v___y_2188_; lean_object* v_pos_2189_; uint8_t v_res_2190_; lean_object* v_pos_2193_; lean_object* v_array_2194_; lean_object* v_idx_2195_; uint8_t v_res_2196_; uint8_t v___y_2201_; uint8_t v___y_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v_array_2087_ = lean_ctor_get(v_a_2082_, 0);
lean_inc_ref(v_array_2087_);
v_idx_2088_ = lean_ctor_get(v_a_2082_, 1);
lean_inc(v_idx_2088_);
v_isAbsolute_2089_ = 0;
v___x_2090_ = lean_unsigned_to_nat(0u);
v_segments_2091_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__2));
v___x_2203_ = lean_byte_array_size(v_array_2087_);
v___x_2204_ = lean_nat_dec_lt(v_idx_2088_, v___x_2203_);
if (v___x_2204_ == 0)
{
v_pos_2193_ = v_a_2082_;
v_array_2194_ = v_array_2087_;
v_idx_2195_ = v_idx_2088_;
v_res_2196_ = v_isAbsolute_2089_;
goto v___jp_2192_;
}
else
{
uint8_t v___x_2205_; uint8_t v___y_2207_; uint8_t v___x_2257_; uint8_t v___x_2258_; 
v___x_2205_ = lean_byte_array_fget(v_array_2087_, v_idx_2088_);
v___x_2257_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_2258_ = lean_uint8_dec_le(v___x_2257_, v___x_2205_);
if (v___x_2258_ == 0)
{
goto v___jp_2252_;
}
else
{
uint8_t v___x_2259_; uint8_t v___x_2260_; 
v___x_2259_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_2260_ = lean_uint8_dec_le(v___x_2205_, v___x_2259_);
if (v___x_2260_ == 0)
{
goto v___jp_2252_;
}
else
{
v___y_2207_ = v___x_2260_;
goto v___jp_2206_;
}
}
v___jp_2206_:
{
uint8_t v___x_2208_; uint8_t v___x_2209_; 
v___x_2208_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_2209_ = lean_uint8_dec_eq(v___x_2205_, v___x_2208_);
if (v___x_2209_ == 0)
{
uint8_t v___x_2210_; uint8_t v___x_2211_; 
v___x_2210_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2211_ = lean_uint8_dec_eq(v___x_2205_, v___x_2210_);
v___y_2201_ = v___y_2207_;
v___y_2202_ = v___x_2211_;
goto v___jp_2200_;
}
else
{
v___y_2201_ = v___y_2207_;
v___y_2202_ = v___x_2209_;
goto v___jp_2200_;
}
}
v___jp_2212_:
{
uint8_t v___x_2213_; uint8_t v___x_2214_; 
v___x_2213_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_2214_ = lean_uint8_dec_eq(v___x_2205_, v___x_2213_);
if (v___x_2214_ == 0)
{
uint8_t v___x_2215_; uint8_t v___x_2216_; 
v___x_2215_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_2216_ = lean_uint8_dec_eq(v___x_2205_, v___x_2215_);
if (v___x_2216_ == 0)
{
uint8_t v___x_2217_; uint8_t v___x_2218_; 
v___x_2217_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_2218_ = lean_uint8_dec_eq(v___x_2205_, v___x_2217_);
if (v___x_2218_ == 0)
{
uint8_t v___x_2219_; uint8_t v___x_2220_; 
v___x_2219_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_2220_ = lean_uint8_dec_eq(v___x_2205_, v___x_2219_);
if (v___x_2220_ == 0)
{
uint8_t v___x_2221_; uint8_t v___x_2222_; 
v___x_2221_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_2222_ = lean_uint8_dec_eq(v___x_2205_, v___x_2221_);
if (v___x_2222_ == 0)
{
uint8_t v___x_2223_; uint8_t v___x_2224_; 
v___x_2223_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_2224_ = lean_uint8_dec_eq(v___x_2205_, v___x_2223_);
if (v___x_2224_ == 0)
{
uint8_t v___x_2225_; uint8_t v___x_2226_; 
v___x_2225_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_2226_ = lean_uint8_dec_eq(v___x_2205_, v___x_2225_);
if (v___x_2226_ == 0)
{
uint8_t v___x_2227_; uint8_t v___x_2228_; 
v___x_2227_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_2228_ = lean_uint8_dec_eq(v___x_2205_, v___x_2227_);
if (v___x_2228_ == 0)
{
uint8_t v___x_2229_; uint8_t v___x_2230_; 
v___x_2229_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_2230_ = lean_uint8_dec_eq(v___x_2205_, v___x_2229_);
if (v___x_2230_ == 0)
{
uint8_t v___x_2231_; uint8_t v___x_2232_; 
v___x_2231_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_2232_ = lean_uint8_dec_eq(v___x_2205_, v___x_2231_);
if (v___x_2232_ == 0)
{
uint8_t v___x_2233_; uint8_t v___x_2234_; 
v___x_2233_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_2234_ = lean_uint8_dec_eq(v___x_2205_, v___x_2233_);
if (v___x_2234_ == 0)
{
uint8_t v___x_2235_; uint8_t v___x_2236_; 
v___x_2235_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_2236_ = lean_uint8_dec_eq(v___x_2205_, v___x_2235_);
if (v___x_2236_ == 0)
{
uint8_t v___x_2237_; uint8_t v___x_2238_; 
v___x_2237_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_2238_ = lean_uint8_dec_eq(v___x_2205_, v___x_2237_);
if (v___x_2238_ == 0)
{
uint8_t v___x_2239_; uint8_t v___x_2240_; 
v___x_2239_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_2240_ = lean_uint8_dec_eq(v___x_2205_, v___x_2239_);
if (v___x_2240_ == 0)
{
uint8_t v___x_2241_; uint8_t v___x_2242_; 
v___x_2241_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_2242_ = lean_uint8_dec_eq(v___x_2205_, v___x_2241_);
if (v___x_2242_ == 0)
{
uint8_t v___x_2243_; uint8_t v___x_2244_; 
v___x_2243_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_2244_ = lean_uint8_dec_eq(v___x_2205_, v___x_2243_);
if (v___x_2244_ == 0)
{
uint8_t v___x_2245_; uint8_t v___x_2246_; 
v___x_2245_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_2246_ = lean_uint8_dec_eq(v___x_2205_, v___x_2245_);
v___y_2207_ = v___x_2246_;
goto v___jp_2206_;
}
else
{
v___y_2207_ = v___x_2244_;
goto v___jp_2206_;
}
}
else
{
v___y_2207_ = v___x_2242_;
goto v___jp_2206_;
}
}
else
{
v___y_2207_ = v___x_2240_;
goto v___jp_2206_;
}
}
else
{
v___y_2207_ = v___x_2238_;
goto v___jp_2206_;
}
}
else
{
v___y_2207_ = v___x_2236_;
goto v___jp_2206_;
}
}
else
{
v___y_2207_ = v___x_2234_;
goto v___jp_2206_;
}
}
else
{
v___y_2207_ = v___x_2232_;
goto v___jp_2206_;
}
}
else
{
v___y_2207_ = v___x_2230_;
goto v___jp_2206_;
}
}
else
{
v___y_2207_ = v___x_2228_;
goto v___jp_2206_;
}
}
else
{
v___y_2207_ = v___x_2226_;
goto v___jp_2206_;
}
}
else
{
v___y_2207_ = v___x_2224_;
goto v___jp_2206_;
}
}
else
{
v___y_2207_ = v___x_2222_;
goto v___jp_2206_;
}
}
else
{
v___y_2207_ = v___x_2220_;
goto v___jp_2206_;
}
}
else
{
v___y_2207_ = v___x_2218_;
goto v___jp_2206_;
}
}
else
{
v___y_2207_ = v___x_2216_;
goto v___jp_2206_;
}
}
else
{
v___y_2207_ = v___x_2214_;
goto v___jp_2206_;
}
}
v___jp_2247_:
{
uint8_t v___x_2248_; uint8_t v___x_2249_; 
v___x_2248_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_2249_ = lean_uint8_dec_le(v___x_2248_, v___x_2205_);
if (v___x_2249_ == 0)
{
goto v___jp_2212_;
}
else
{
uint8_t v___x_2250_; uint8_t v___x_2251_; 
v___x_2250_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_2251_ = lean_uint8_dec_le(v___x_2205_, v___x_2250_);
if (v___x_2251_ == 0)
{
goto v___jp_2212_;
}
else
{
v___y_2207_ = v___x_2251_;
goto v___jp_2206_;
}
}
}
v___jp_2252_:
{
uint8_t v___x_2253_; uint8_t v___x_2254_; 
v___x_2253_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_2254_ = lean_uint8_dec_le(v___x_2253_, v___x_2205_);
if (v___x_2254_ == 0)
{
goto v___jp_2247_;
}
else
{
uint8_t v___x_2255_; uint8_t v___x_2256_; 
v___x_2255_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_2256_ = lean_uint8_dec_le(v___x_2205_, v___x_2255_);
if (v___x_2256_ == 0)
{
goto v___jp_2247_;
}
else
{
v___y_2207_ = v___x_2256_;
goto v___jp_2206_;
}
}
}
}
v___jp_2083_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__1));
v___x_2086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___y_2084_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
return v___x_2086_;
}
v___jp_2092_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2096_, 0, v_segments_2091_);
lean_ctor_set(v___x_2096_, 1, v_totalLength_2094_);
v___x_2097_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(v_config_2079_, v___x_2096_, v___y_2095_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_res_2098_; lean_object* v_pos_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2108_; 
v_res_2098_ = lean_ctor_get(v___x_2097_, 1);
v_pos_2099_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2101_ = v___x_2097_;
v_isShared_2102_ = v_isSharedCheck_2108_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_res_2098_);
lean_inc(v_pos_2099_);
lean_dec(v___x_2097_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2108_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v_fst_2103_; lean_object* v___x_2104_; lean_object* v___x_2106_; 
v_fst_2103_ = lean_ctor_get(v_res_2098_, 0);
lean_inc(v_fst_2103_);
lean_dec(v_res_2098_);
v___x_2104_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2104_, 0, v_fst_2103_);
lean_ctor_set_uint8(v___x_2104_, sizeof(void*)*1, v_isAbsolute_2093_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 1, v___x_2104_);
v___x_2106_ = v___x_2101_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_pos_2099_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
else
{
lean_object* v_pos_2109_; lean_object* v_err_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
v_pos_2109_ = lean_ctor_get(v___x_2097_, 0);
v_err_2110_ = lean_ctor_get(v___x_2097_, 1);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2097_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_err_2110_);
lean_inc(v_pos_2109_);
lean_dec(v___x_2097_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_pos_2109_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_err_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
v___jp_2118_:
{
if (v_allowEmpty_2081_ == 0)
{
v___y_2084_ = v___y_2119_;
goto v___jp_2083_;
}
else
{
if (v___y_2120_ == 0)
{
v___y_2084_ = v___y_2119_;
goto v___jp_2083_;
}
else
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__3));
v___x_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___y_2119_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
return v___x_2122_;
}
}
}
v___jp_2123_:
{
if (v___y_2125_ == 0)
{
v___y_2119_ = v___y_2124_;
v___y_2120_ = v___y_2126_;
goto v___jp_2118_;
}
else
{
v___y_2119_ = v___y_2124_;
v___y_2120_ = v___y_2125_;
goto v___jp_2118_;
}
}
v___jp_2127_:
{
if (v___y_2128_ == 0)
{
uint8_t v___x_2131_; 
v___x_2131_ = 1;
v___y_2124_ = v_pos_2129_;
v___y_2125_ = v_res_2130_;
v___y_2126_ = v___x_2131_;
goto v___jp_2123_;
}
else
{
v___y_2124_ = v_pos_2129_;
v___y_2125_ = v_res_2130_;
v___y_2126_ = v_isAbsolute_2089_;
goto v___jp_2123_;
}
}
v___jp_2132_:
{
if (v_res_2135_ == 0)
{
if (v_forceAbsolute_2080_ == 0)
{
v_isAbsolute_2093_ = v_isAbsolute_2089_;
v_totalLength_2094_ = v___x_2090_;
v___y_2095_ = v_pos_2134_;
goto v___jp_2092_;
}
else
{
lean_object* v_array_2136_; lean_object* v_idx_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
lean_dec_ref(v_config_2079_);
v_array_2136_ = lean_ctor_get(v_pos_2134_, 0);
v_idx_2137_ = lean_ctor_get(v_pos_2134_, 1);
v___x_2138_ = lean_byte_array_size(v_array_2136_);
v___x_2139_ = lean_nat_dec_lt(v_idx_2137_, v___x_2138_);
if (v___x_2139_ == 0)
{
v___y_2128_ = v___y_2133_;
v_pos_2129_ = v_pos_2134_;
v_res_2130_ = v_forceAbsolute_2080_;
goto v___jp_2127_;
}
else
{
v___y_2128_ = v___y_2133_;
v_pos_2129_ = v_pos_2134_;
v_res_2130_ = v_res_2135_;
goto v___jp_2127_;
}
}
}
else
{
lean_object* v_array_2140_; lean_object* v_idx_2141_; lean_object* v___x_2142_; uint8_t v___x_2143_; 
v_array_2140_ = lean_ctor_get(v_pos_2134_, 0);
v_idx_2141_ = lean_ctor_get(v_pos_2134_, 1);
v___x_2142_ = lean_byte_array_size(v_array_2140_);
v___x_2143_ = lean_nat_dec_lt(v_idx_2141_, v___x_2142_);
if (v___x_2143_ == 0)
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
lean_dec_ref(v_config_2079_);
v___x_2144_ = lean_box(0);
v___x_2145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2145_, 0, v_pos_2134_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
return v___x_2145_;
}
else
{
lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2154_; 
lean_inc(v_idx_2141_);
lean_inc_ref(v_array_2140_);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_pos_2134_);
if (v_isSharedCheck_2154_ == 0)
{
lean_object* v_unused_2155_; lean_object* v_unused_2156_; 
v_unused_2155_ = lean_ctor_get(v_pos_2134_, 1);
lean_dec(v_unused_2155_);
v_unused_2156_ = lean_ctor_get(v_pos_2134_, 0);
lean_dec(v_unused_2156_);
v___x_2147_ = v_pos_2134_;
v_isShared_2148_ = v_isSharedCheck_2154_;
goto v_resetjp_2146_;
}
else
{
lean_dec(v_pos_2134_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2154_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2149_ = lean_unsigned_to_nat(1u);
v___x_2150_ = lean_nat_add(v_idx_2141_, v___x_2149_);
lean_dec(v_idx_2141_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 1, v___x_2150_);
v___x_2152_ = v___x_2147_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_array_2140_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
v_isAbsolute_2093_ = v___x_2143_;
v_totalLength_2094_ = v___x_2149_;
v___y_2095_ = v___x_2152_;
goto v___jp_2092_;
}
}
}
}
}
v___jp_2157_:
{
lean_object* v_array_2161_; lean_object* v_idx_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; 
v_array_2161_ = lean_ctor_get(v___y_2159_, 0);
v_idx_2162_ = lean_ctor_get(v___y_2159_, 1);
v___x_2163_ = lean_byte_array_size(v_array_2161_);
v___x_2164_ = lean_nat_dec_lt(v_idx_2162_, v___x_2163_);
if (v___x_2164_ == 0)
{
v___y_2133_ = v___y_2158_;
v_pos_2134_ = v___y_2159_;
v_res_2135_ = v___y_2160_;
goto v___jp_2132_;
}
else
{
uint8_t v___x_2165_; uint8_t v___x_2166_; uint8_t v___x_2167_; 
v___x_2165_ = lean_byte_array_fget(v_array_2161_, v_idx_2162_);
v___x_2166_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2167_ = lean_uint8_dec_eq(v___x_2165_, v___x_2166_);
if (v___x_2167_ == 0)
{
v___y_2133_ = v___y_2158_;
v_pos_2134_ = v___y_2159_;
v_res_2135_ = v___y_2160_;
goto v___jp_2132_;
}
else
{
v___y_2133_ = v___y_2158_;
v_pos_2134_ = v___y_2159_;
v_res_2135_ = v___x_2167_;
goto v___jp_2132_;
}
}
}
v___jp_2168_:
{
if (v___y_2169_ == 0)
{
v___y_2158_ = v___y_2171_;
v___y_2159_ = v___y_2170_;
v___y_2160_ = v___y_2169_;
goto v___jp_2157_;
}
else
{
if (v___y_2172_ == 0)
{
v___y_2158_ = v___y_2171_;
v___y_2159_ = v___y_2170_;
v___y_2160_ = v___y_2172_;
goto v___jp_2157_;
}
else
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
lean_dec_ref(v_config_2079_);
v___x_2173_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__5));
v___x_2174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___y_2170_);
lean_ctor_set(v___x_2174_, 1, v___x_2173_);
return v___x_2174_;
}
}
}
v___jp_2175_:
{
if (v___y_2176_ == 0)
{
v___y_2169_ = v___y_2177_;
v___y_2170_ = v___y_2179_;
v___y_2171_ = v___y_2178_;
v___y_2172_ = v___y_2180_;
goto v___jp_2168_;
}
else
{
v___y_2169_ = v___y_2177_;
v___y_2170_ = v___y_2179_;
v___y_2171_ = v___y_2178_;
v___y_2172_ = v___y_2176_;
goto v___jp_2168_;
}
}
v___jp_2181_:
{
if (v___y_2184_ == 0)
{
uint8_t v___x_2186_; 
v___x_2186_ = 1;
v___y_2176_ = v___y_2182_;
v___y_2177_ = v___y_2185_;
v___y_2178_ = v___y_2184_;
v___y_2179_ = v___y_2183_;
v___y_2180_ = v___x_2186_;
goto v___jp_2175_;
}
else
{
v___y_2176_ = v___y_2182_;
v___y_2177_ = v___y_2185_;
v___y_2178_ = v___y_2184_;
v___y_2179_ = v___y_2183_;
v___y_2180_ = v_isAbsolute_2089_;
goto v___jp_2175_;
}
}
v___jp_2187_:
{
if (v_allowEmpty_2081_ == 0)
{
uint8_t v___x_2191_; 
v___x_2191_ = 1;
v___y_2182_ = v_res_2190_;
v___y_2183_ = v_pos_2189_;
v___y_2184_ = v___y_2188_;
v___y_2185_ = v___x_2191_;
goto v___jp_2181_;
}
else
{
v___y_2182_ = v_res_2190_;
v___y_2183_ = v_pos_2189_;
v___y_2184_ = v___y_2188_;
v___y_2185_ = v_isAbsolute_2089_;
goto v___jp_2181_;
}
}
v___jp_2192_:
{
lean_object* v___x_2197_; uint8_t v___x_2198_; 
v___x_2197_ = lean_byte_array_size(v_array_2194_);
lean_dec_ref(v_array_2194_);
v___x_2198_ = lean_nat_dec_lt(v_idx_2195_, v___x_2197_);
lean_dec(v_idx_2195_);
if (v___x_2198_ == 0)
{
uint8_t v___x_2199_; 
v___x_2199_ = 1;
v___y_2188_ = v_res_2196_;
v_pos_2189_ = v_pos_2193_;
v_res_2190_ = v___x_2199_;
goto v___jp_2187_;
}
else
{
v___y_2188_ = v_res_2196_;
v_pos_2189_ = v_pos_2193_;
v_res_2190_ = v_isAbsolute_2089_;
goto v___jp_2187_;
}
}
v___jp_2200_:
{
if (v___y_2201_ == 0)
{
if (v___y_2202_ == 0)
{
v_pos_2193_ = v_a_2082_;
v_array_2194_ = v_array_2087_;
v_idx_2195_ = v_idx_2088_;
v_res_2196_ = v_isAbsolute_2089_;
goto v___jp_2192_;
}
else
{
v_pos_2193_ = v_a_2082_;
v_array_2194_ = v_array_2087_;
v_idx_2195_ = v_idx_2088_;
v_res_2196_ = v___y_2202_;
goto v___jp_2192_;
}
}
else
{
v_pos_2193_ = v_a_2082_;
v_array_2194_ = v_array_2087_;
v_idx_2195_ = v_idx_2088_;
v_res_2196_ = v___y_2201_;
goto v___jp_2192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath___boxed(lean_object* v_config_2261_, lean_object* v_forceAbsolute_2262_, lean_object* v_allowEmpty_2263_, lean_object* v_a_2264_){
_start:
{
uint8_t v_forceAbsolute_boxed_2265_; uint8_t v_allowEmpty_boxed_2266_; lean_object* v_res_2267_; 
v_forceAbsolute_boxed_2265_ = lean_unbox(v_forceAbsolute_2262_);
v_allowEmpty_boxed_2266_ = lean_unbox(v_allowEmpty_2263_);
v_res_2267_ = l_Std_Http_URI_Parser_parsePath(v_config_2261_, v_forceAbsolute_boxed_2265_, v_allowEmpty_boxed_2266_, v_a_2264_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0(lean_object* v_config_2268_, lean_object* v_inst_2269_, lean_object* v_a_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(v_config_2268_, v_a_2270_, v___y_2271_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(lean_object* v_config_2273_, lean_object* v_inst_2274_, lean_object* v_a_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v___x_2277_; 
v___x_2277_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_2273_, v_a_2275_, v___y_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg(){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg___boxed(lean_object* v___dummy_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg();
return v_res_2281_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2282_; 
v___x_2282_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg();
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(lean_object* v_s_2283_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___boxed(lean_object* v_s_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(v_s_2285_);
lean_dec_ref(v_s_2285_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg(){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg___boxed(lean_object* v___dummy_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg();
return v_res_2290_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg();
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(lean_object* v_s_2292_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___boxed(lean_object* v_s_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v_s_2294_);
lean_dec_ref(v_s_2294_);
return v_res_2295_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(uint8_t v_c_2296_){
_start:
{
uint8_t v___y_2298_; uint8_t v___x_2350_; uint8_t v___x_2351_; 
v___x_2350_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_2351_ = lean_uint8_dec_le(v___x_2350_, v_c_2296_);
if (v___x_2351_ == 0)
{
goto v___jp_2345_;
}
else
{
uint8_t v___x_2352_; uint8_t v___x_2353_; 
v___x_2352_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_2353_ = lean_uint8_dec_le(v_c_2296_, v___x_2352_);
if (v___x_2353_ == 0)
{
goto v___jp_2345_;
}
else
{
v___y_2298_ = v___x_2353_;
goto v___jp_2297_;
}
}
v___jp_2297_:
{
if (v___y_2298_ == 0)
{
uint8_t v___x_2299_; uint8_t v___x_2300_; 
v___x_2299_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_2300_ = lean_uint8_dec_eq(v_c_2296_, v___x_2299_);
return v___x_2300_;
}
else
{
return v___y_2298_;
}
}
v___jp_2301_:
{
uint8_t v___x_2302_; uint8_t v___x_2303_; 
v___x_2302_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_2303_ = lean_uint8_dec_eq(v_c_2296_, v___x_2302_);
if (v___x_2303_ == 0)
{
uint8_t v___x_2304_; uint8_t v___x_2305_; 
v___x_2304_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_2305_ = lean_uint8_dec_eq(v_c_2296_, v___x_2304_);
if (v___x_2305_ == 0)
{
uint8_t v___x_2306_; uint8_t v___x_2307_; 
v___x_2306_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_2307_ = lean_uint8_dec_eq(v_c_2296_, v___x_2306_);
if (v___x_2307_ == 0)
{
uint8_t v___x_2308_; uint8_t v___x_2309_; 
v___x_2308_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_2309_ = lean_uint8_dec_eq(v_c_2296_, v___x_2308_);
if (v___x_2309_ == 0)
{
uint8_t v___x_2310_; uint8_t v___x_2311_; 
v___x_2310_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_2311_ = lean_uint8_dec_eq(v_c_2296_, v___x_2310_);
if (v___x_2311_ == 0)
{
uint8_t v___x_2312_; uint8_t v___x_2313_; 
v___x_2312_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_2313_ = lean_uint8_dec_eq(v_c_2296_, v___x_2312_);
if (v___x_2313_ == 0)
{
uint8_t v___x_2314_; uint8_t v___x_2315_; 
v___x_2314_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_2315_ = lean_uint8_dec_eq(v_c_2296_, v___x_2314_);
if (v___x_2315_ == 0)
{
uint8_t v___x_2316_; uint8_t v___x_2317_; 
v___x_2316_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_2317_ = lean_uint8_dec_eq(v_c_2296_, v___x_2316_);
if (v___x_2317_ == 0)
{
uint8_t v___x_2318_; uint8_t v___x_2319_; 
v___x_2318_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_2319_ = lean_uint8_dec_eq(v_c_2296_, v___x_2318_);
if (v___x_2319_ == 0)
{
uint8_t v___x_2320_; uint8_t v___x_2321_; 
v___x_2320_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_2321_ = lean_uint8_dec_eq(v_c_2296_, v___x_2320_);
if (v___x_2321_ == 0)
{
uint8_t v___x_2322_; uint8_t v___x_2323_; 
v___x_2322_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_2323_ = lean_uint8_dec_eq(v_c_2296_, v___x_2322_);
if (v___x_2323_ == 0)
{
uint8_t v___x_2324_; uint8_t v___x_2325_; 
v___x_2324_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_2325_ = lean_uint8_dec_eq(v_c_2296_, v___x_2324_);
if (v___x_2325_ == 0)
{
uint8_t v___x_2326_; uint8_t v___x_2327_; 
v___x_2326_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_2327_ = lean_uint8_dec_eq(v_c_2296_, v___x_2326_);
if (v___x_2327_ == 0)
{
uint8_t v___x_2328_; uint8_t v___x_2329_; 
v___x_2328_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_2329_ = lean_uint8_dec_eq(v_c_2296_, v___x_2328_);
if (v___x_2329_ == 0)
{
uint8_t v___x_2330_; uint8_t v___x_2331_; 
v___x_2330_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_2331_ = lean_uint8_dec_eq(v_c_2296_, v___x_2330_);
if (v___x_2331_ == 0)
{
uint8_t v___x_2332_; uint8_t v___x_2333_; 
v___x_2332_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_2333_ = lean_uint8_dec_eq(v_c_2296_, v___x_2332_);
if (v___x_2333_ == 0)
{
uint8_t v___x_2334_; uint8_t v___x_2335_; 
v___x_2334_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_2335_ = lean_uint8_dec_eq(v_c_2296_, v___x_2334_);
if (v___x_2335_ == 0)
{
uint8_t v___x_2336_; uint8_t v___x_2337_; 
v___x_2336_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2337_ = lean_uint8_dec_eq(v_c_2296_, v___x_2336_);
if (v___x_2337_ == 0)
{
uint8_t v___x_2338_; uint8_t v___x_2339_; 
v___x_2338_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_2339_ = lean_uint8_dec_eq(v_c_2296_, v___x_2338_);
v___y_2298_ = v___x_2339_;
goto v___jp_2297_;
}
else
{
v___y_2298_ = v___x_2337_;
goto v___jp_2297_;
}
}
else
{
v___y_2298_ = v___x_2335_;
goto v___jp_2297_;
}
}
else
{
v___y_2298_ = v___x_2333_;
goto v___jp_2297_;
}
}
else
{
v___y_2298_ = v___x_2331_;
goto v___jp_2297_;
}
}
else
{
v___y_2298_ = v___x_2329_;
goto v___jp_2297_;
}
}
else
{
v___y_2298_ = v___x_2327_;
goto v___jp_2297_;
}
}
else
{
v___y_2298_ = v___x_2325_;
goto v___jp_2297_;
}
}
else
{
v___y_2298_ = v___x_2323_;
goto v___jp_2297_;
}
}
else
{
v___y_2298_ = v___x_2321_;
goto v___jp_2297_;
}
}
else
{
v___y_2298_ = v___x_2319_;
goto v___jp_2297_;
}
}
else
{
v___y_2298_ = v___x_2317_;
goto v___jp_2297_;
}
}
else
{
v___y_2298_ = v___x_2315_;
goto v___jp_2297_;
}
}
else
{
v___y_2298_ = v___x_2313_;
goto v___jp_2297_;
}
}
else
{
v___y_2298_ = v___x_2311_;
goto v___jp_2297_;
}
}
else
{
v___y_2298_ = v___x_2309_;
goto v___jp_2297_;
}
}
else
{
v___y_2298_ = v___x_2307_;
goto v___jp_2297_;
}
}
else
{
v___y_2298_ = v___x_2305_;
goto v___jp_2297_;
}
}
else
{
v___y_2298_ = v___x_2303_;
goto v___jp_2297_;
}
}
v___jp_2340_:
{
uint8_t v___x_2341_; uint8_t v___x_2342_; 
v___x_2341_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_2342_ = lean_uint8_dec_le(v___x_2341_, v_c_2296_);
if (v___x_2342_ == 0)
{
goto v___jp_2301_;
}
else
{
uint8_t v___x_2343_; uint8_t v___x_2344_; 
v___x_2343_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_2344_ = lean_uint8_dec_le(v_c_2296_, v___x_2343_);
if (v___x_2344_ == 0)
{
goto v___jp_2301_;
}
else
{
v___y_2298_ = v___x_2344_;
goto v___jp_2297_;
}
}
}
v___jp_2345_:
{
uint8_t v___x_2346_; uint8_t v___x_2347_; 
v___x_2346_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_2347_ = lean_uint8_dec_le(v___x_2346_, v_c_2296_);
if (v___x_2347_ == 0)
{
goto v___jp_2340_;
}
else
{
uint8_t v___x_2348_; uint8_t v___x_2349_; 
v___x_2348_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_2349_ = lean_uint8_dec_le(v_c_2296_, v___x_2348_);
if (v___x_2349_ == 0)
{
goto v___jp_2340_;
}
else
{
v___y_2298_ = v___x_2349_;
goto v___jp_2297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed(lean_object* v_c_2354_){
_start:
{
uint8_t v_c_boxed_2355_; uint8_t v_res_2356_; lean_object* v_r_2357_; 
v_c_boxed_2355_ = lean_unbox(v_c_2354_);
v_res_2356_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(v_c_boxed_2355_);
v_r_2357_ = lean_box(v_res_2356_);
return v_r_2357_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(lean_object* v___x_2358_, lean_object* v___x_2359_, lean_object* v_a_2360_, lean_object* v_b_2361_){
_start:
{
lean_object* v_it_2363_; 
if (lean_obj_tag(v_a_2360_) == 0)
{
lean_object* v_currPos_2367_; lean_object* v_searcher_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2394_; 
v_currPos_2367_ = lean_ctor_get(v_a_2360_, 0);
v_searcher_2368_ = lean_ctor_get(v_a_2360_, 1);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_a_2360_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2370_ = v_a_2360_;
v_isShared_2371_ = v_isSharedCheck_2394_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_searcher_2368_);
lean_inc(v_currPos_2367_);
lean_dec(v_a_2360_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2394_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v_str_2372_; lean_object* v_startInclusive_2373_; lean_object* v_endExclusive_2374_; lean_object* v___x_2375_; uint8_t v_decide_2376_; 
v_str_2372_ = lean_ctor_get(v___x_2358_, 0);
v_startInclusive_2373_ = lean_ctor_get(v___x_2358_, 1);
v_endExclusive_2374_ = lean_ctor_get(v___x_2358_, 2);
v___x_2375_ = lean_nat_sub(v_endExclusive_2374_, v_startInclusive_2373_);
v_decide_2376_ = lean_nat_dec_eq(v_searcher_2368_, v___x_2375_);
lean_dec(v___x_2375_);
if (v_decide_2376_ == 0)
{
uint32_t v___x_2377_; lean_object* v___x_2378_; uint32_t v___x_2379_; uint8_t v___x_2380_; 
v___x_2377_ = 38;
v___x_2378_ = lean_nat_add(v_startInclusive_2373_, v_searcher_2368_);
v___x_2379_ = lean_string_utf8_get_fast(v_str_2372_, v___x_2378_);
v___x_2380_ = lean_uint32_dec_eq(v___x_2379_, v___x_2377_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2384_; 
lean_dec(v_searcher_2368_);
v___x_2381_ = lean_string_utf8_next_fast(v_str_2372_, v___x_2378_);
lean_dec(v___x_2378_);
v___x_2382_ = lean_nat_sub(v___x_2381_, v_startInclusive_2373_);
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 1, v___x_2382_);
v___x_2384_ = v___x_2370_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_currPos_2367_);
lean_ctor_set(v_reuseFailAlloc_2386_, 1, v___x_2382_);
v___x_2384_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
v_a_2360_ = v___x_2384_;
goto _start;
}
}
else
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v_nextIt_2391_; 
lean_dec(v_currPos_2367_);
v___x_2387_ = lean_string_utf8_next_fast(v_str_2372_, v___x_2378_);
v___x_2388_ = lean_nat_sub(v___x_2387_, v___x_2378_);
lean_dec(v___x_2378_);
v___x_2389_ = lean_nat_add(v_searcher_2368_, v___x_2388_);
lean_dec(v___x_2388_);
lean_dec(v_searcher_2368_);
lean_inc(v___x_2389_);
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 1, v___x_2389_);
lean_ctor_set(v___x_2370_, 0, v___x_2389_);
v_nextIt_2391_ = v___x_2370_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2389_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v___x_2389_);
v_nextIt_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
v_it_2363_ = v_nextIt_2391_;
goto v___jp_2362_;
}
}
}
else
{
lean_object* v___x_2393_; 
lean_del_object(v___x_2370_);
lean_dec(v_searcher_2368_);
lean_dec(v_currPos_2367_);
v___x_2393_ = lean_box(1);
v_it_2363_ = v___x_2393_;
goto v___jp_2362_;
}
}
}
else
{
return v_b_2361_;
}
v___jp_2362_:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = lean_unsigned_to_nat(1u);
v___x_2365_ = lean_nat_add(v_b_2361_, v___x_2364_);
lean_dec(v_b_2361_);
v_a_2360_ = v_it_2363_;
v_b_2361_ = v___x_2365_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg___boxed(lean_object* v___x_2395_, lean_object* v___x_2396_, lean_object* v_a_2397_, lean_object* v_b_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2395_, v___x_2396_, v_a_2397_, v_b_2398_);
lean_dec(v___x_2396_);
lean_dec_ref(v___x_2395_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(lean_object* v___x_2400_, lean_object* v___x_2401_, lean_object* v___x_2402_, lean_object* v_a_2403_, lean_object* v_b_2404_){
_start:
{
lean_object* v_it_2406_; 
if (lean_obj_tag(v_a_2403_) == 0)
{
lean_object* v_currPos_2410_; lean_object* v_searcher_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2437_; 
v_currPos_2410_ = lean_ctor_get(v_a_2403_, 0);
v_searcher_2411_ = lean_ctor_get(v_a_2403_, 1);
v_isSharedCheck_2437_ = !lean_is_exclusive(v_a_2403_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2413_ = v_a_2403_;
v_isShared_2414_ = v_isSharedCheck_2437_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_searcher_2411_);
lean_inc(v_currPos_2410_);
lean_dec(v_a_2403_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2437_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v_str_2415_; lean_object* v_startInclusive_2416_; lean_object* v_endExclusive_2417_; lean_object* v___x_2418_; uint8_t v_decide_2419_; 
v_str_2415_ = lean_ctor_get(v___x_2401_, 0);
v_startInclusive_2416_ = lean_ctor_get(v___x_2401_, 1);
v_endExclusive_2417_ = lean_ctor_get(v___x_2401_, 2);
v___x_2418_ = lean_nat_sub(v_endExclusive_2417_, v_startInclusive_2416_);
v_decide_2419_ = lean_nat_dec_eq(v_searcher_2411_, v___x_2418_);
lean_dec(v___x_2418_);
if (v_decide_2419_ == 0)
{
lean_object* v___x_2420_; uint32_t v___x_2421_; uint32_t v___x_2422_; uint8_t v___x_2423_; 
v___x_2420_ = lean_nat_add(v_startInclusive_2416_, v_searcher_2411_);
v___x_2421_ = lean_string_utf8_get_fast(v_str_2415_, v___x_2420_);
v___x_2422_ = 38;
v___x_2423_ = lean_uint32_dec_eq(v___x_2421_, v___x_2422_);
if (v___x_2423_ == 0)
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2427_; 
lean_dec(v_searcher_2411_);
v___x_2424_ = lean_string_utf8_next_fast(v_str_2415_, v___x_2420_);
lean_dec(v___x_2420_);
v___x_2425_ = lean_nat_sub(v___x_2424_, v_startInclusive_2416_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 1, v___x_2425_);
v___x_2427_ = v___x_2413_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_currPos_2410_);
lean_ctor_set(v_reuseFailAlloc_2429_, 1, v___x_2425_);
v___x_2427_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
lean_object* v___x_2428_; 
v___x_2428_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2401_, v___x_2402_, v___x_2427_, v_b_2404_);
return v___x_2428_;
}
}
else
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v_nextIt_2434_; 
lean_dec(v_currPos_2410_);
v___x_2430_ = lean_string_utf8_next_fast(v_str_2415_, v___x_2420_);
v___x_2431_ = lean_nat_sub(v___x_2430_, v___x_2420_);
lean_dec(v___x_2420_);
v___x_2432_ = lean_nat_add(v_searcher_2411_, v___x_2431_);
lean_dec(v___x_2431_);
lean_dec(v_searcher_2411_);
lean_inc(v___x_2432_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 1, v___x_2432_);
lean_ctor_set(v___x_2413_, 0, v___x_2432_);
v_nextIt_2434_ = v___x_2413_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2435_, 1, v___x_2432_);
v_nextIt_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
v_it_2406_ = v_nextIt_2434_;
goto v___jp_2405_;
}
}
}
else
{
lean_object* v___x_2436_; 
lean_del_object(v___x_2413_);
lean_dec(v_searcher_2411_);
lean_dec(v_currPos_2410_);
v___x_2436_ = lean_box(1);
v_it_2406_ = v___x_2436_;
goto v___jp_2405_;
}
}
}
else
{
return v_b_2404_;
}
v___jp_2405_:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2407_ = lean_unsigned_to_nat(1u);
v___x_2408_ = lean_nat_add(v_b_2404_, v___x_2407_);
lean_dec(v_b_2404_);
v___x_2409_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2401_, v___x_2402_, v_it_2406_, v___x_2408_);
return v___x_2409_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg___boxed(lean_object* v___x_2438_, lean_object* v___x_2439_, lean_object* v___x_2440_, lean_object* v_a_2441_, lean_object* v_b_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2438_, v___x_2439_, v___x_2440_, v_a_2441_, v_b_2442_);
lean_dec(v___x_2440_);
lean_dec_ref(v___x_2439_);
lean_dec_ref(v___x_2438_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(lean_object* v_out_2444_, lean_object* v_a_2445_, lean_object* v_b_2446_){
_start:
{
if (lean_obj_tag(v_a_2445_) == 0)
{
lean_object* v_currPos_2447_; lean_object* v_searcher_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2487_; 
v_currPos_2447_ = lean_ctor_get(v_a_2445_, 0);
v_searcher_2448_ = lean_ctor_get(v_a_2445_, 1);
v_isSharedCheck_2487_ = !lean_is_exclusive(v_a_2445_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2450_ = v_a_2445_;
v_isShared_2451_ = v_isSharedCheck_2487_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_searcher_2448_);
lean_inc(v_currPos_2447_);
lean_dec(v_a_2445_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2487_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v_str_2452_; lean_object* v_startInclusive_2453_; lean_object* v_endExclusive_2454_; lean_object* v_it_2456_; lean_object* v_startInclusive_2457_; lean_object* v_endExclusive_2458_; lean_object* v___x_2465_; uint8_t v_decide_2466_; 
v_str_2452_ = lean_ctor_get(v_out_2444_, 0);
v_startInclusive_2453_ = lean_ctor_get(v_out_2444_, 1);
v_endExclusive_2454_ = lean_ctor_get(v_out_2444_, 2);
v___x_2465_ = lean_nat_sub(v_endExclusive_2454_, v_startInclusive_2453_);
v_decide_2466_ = lean_nat_dec_eq(v_searcher_2448_, v___x_2465_);
if (v_decide_2466_ == 0)
{
uint32_t v___x_2467_; lean_object* v___x_2468_; uint32_t v___x_2469_; uint8_t v___x_2470_; 
lean_dec(v___x_2465_);
v___x_2467_ = 61;
v___x_2468_ = lean_nat_add(v_startInclusive_2453_, v_searcher_2448_);
v___x_2469_ = lean_string_utf8_get_fast(v_str_2452_, v___x_2468_);
v___x_2470_ = lean_uint32_dec_eq(v___x_2469_, v___x_2467_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2474_; 
lean_dec(v_searcher_2448_);
v___x_2471_ = lean_string_utf8_next_fast(v_str_2452_, v___x_2468_);
lean_dec(v___x_2468_);
v___x_2472_ = lean_nat_sub(v___x_2471_, v_startInclusive_2453_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 1, v___x_2472_);
v___x_2474_ = v___x_2450_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_currPos_2447_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
v_a_2445_ = v___x_2474_;
goto _start;
}
}
else
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v_slice_2480_; lean_object* v_nextIt_2482_; 
v___x_2477_ = lean_string_utf8_next_fast(v_str_2452_, v___x_2468_);
v___x_2478_ = lean_nat_sub(v___x_2477_, v___x_2468_);
lean_dec(v___x_2468_);
v___x_2479_ = lean_nat_add(v_searcher_2448_, v___x_2478_);
lean_dec(v___x_2478_);
v_slice_2480_ = l_String_Slice_subslice_x21(v_out_2444_, v_currPos_2447_, v_searcher_2448_);
lean_inc(v___x_2479_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 1, v___x_2479_);
lean_ctor_set(v___x_2450_, 0, v___x_2479_);
v_nextIt_2482_ = v___x_2450_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2479_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v___x_2479_);
v_nextIt_2482_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
lean_object* v_startInclusive_2483_; lean_object* v_endExclusive_2484_; 
v_startInclusive_2483_ = lean_ctor_get(v_slice_2480_, 0);
lean_inc(v_startInclusive_2483_);
v_endExclusive_2484_ = lean_ctor_get(v_slice_2480_, 1);
lean_inc(v_endExclusive_2484_);
lean_dec_ref(v_slice_2480_);
v_it_2456_ = v_nextIt_2482_;
v_startInclusive_2457_ = v_startInclusive_2483_;
v_endExclusive_2458_ = v_endExclusive_2484_;
goto v___jp_2455_;
}
}
}
else
{
lean_object* v___x_2486_; 
lean_del_object(v___x_2450_);
lean_dec(v_searcher_2448_);
v___x_2486_ = lean_box(1);
v_it_2456_ = v___x_2486_;
v_startInclusive_2457_ = v_currPos_2447_;
v_endExclusive_2458_ = v___x_2465_;
goto v___jp_2455_;
}
v___jp_2455_:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2459_ = lean_nat_add(v_startInclusive_2453_, v_startInclusive_2457_);
lean_dec(v_startInclusive_2457_);
v___x_2460_ = lean_nat_add(v_startInclusive_2453_, v_endExclusive_2458_);
lean_dec(v_endExclusive_2458_);
lean_inc_ref(v_str_2452_);
v___x_2461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2461_, 0, v_str_2452_);
lean_ctor_set(v___x_2461_, 1, v___x_2459_);
lean_ctor_set(v___x_2461_, 2, v___x_2460_);
v___x_2462_ = l_String_Slice_toString(v___x_2461_);
lean_dec_ref_known(v___x_2461_, 3);
v___x_2463_ = lean_array_push(v_b_2446_, v___x_2462_);
v_a_2445_ = v_it_2456_;
v_b_2446_ = v___x_2463_;
goto _start;
}
}
}
else
{
return v_b_2446_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg___boxed(lean_object* v_out_2488_, lean_object* v_a_2489_, lean_object* v_b_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2488_, v_a_2489_, v_b_2490_);
lean_dec_ref(v_out_2488_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(lean_object* v___x_2495_, lean_object* v___x_2496_, lean_object* v___x_2497_, lean_object* v_a_2498_, lean_object* v_b_2499_){
_start:
{
lean_object* v_it_2501_; lean_object* v_startInclusive_2502_; lean_object* v_endExclusive_2503_; 
if (lean_obj_tag(v_a_2498_) == 0)
{
lean_object* v_currPos_2528_; lean_object* v_searcher_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2558_; 
v_currPos_2528_ = lean_ctor_get(v_a_2498_, 0);
v_searcher_2529_ = lean_ctor_get(v_a_2498_, 1);
v_isSharedCheck_2558_ = !lean_is_exclusive(v_a_2498_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2531_ = v_a_2498_;
v_isShared_2532_ = v_isSharedCheck_2558_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_searcher_2529_);
lean_inc(v_currPos_2528_);
lean_dec(v_a_2498_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2558_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v_str_2533_; lean_object* v_startInclusive_2534_; lean_object* v_endExclusive_2535_; lean_object* v___x_2536_; uint8_t v_decide_2537_; 
v_str_2533_ = lean_ctor_get(v___x_2496_, 0);
v_startInclusive_2534_ = lean_ctor_get(v___x_2496_, 1);
v_endExclusive_2535_ = lean_ctor_get(v___x_2496_, 2);
v___x_2536_ = lean_nat_sub(v_endExclusive_2535_, v_startInclusive_2534_);
v_decide_2537_ = lean_nat_dec_eq(v_searcher_2529_, v___x_2536_);
lean_dec(v___x_2536_);
if (v_decide_2537_ == 0)
{
uint32_t v___x_2538_; lean_object* v___x_2539_; uint32_t v___x_2540_; uint8_t v___x_2541_; 
v___x_2538_ = 38;
v___x_2539_ = lean_nat_add(v_startInclusive_2534_, v_searcher_2529_);
v___x_2540_ = lean_string_utf8_get_fast(v_str_2533_, v___x_2539_);
v___x_2541_ = lean_uint32_dec_eq(v___x_2540_, v___x_2538_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2545_; 
lean_dec(v_searcher_2529_);
v___x_2542_ = lean_string_utf8_next_fast(v_str_2533_, v___x_2539_);
lean_dec(v___x_2539_);
v___x_2543_ = lean_nat_sub(v___x_2542_, v_startInclusive_2534_);
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 1, v___x_2543_);
v___x_2545_ = v___x_2531_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_currPos_2528_);
lean_ctor_set(v_reuseFailAlloc_2547_, 1, v___x_2543_);
v___x_2545_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
v_a_2498_ = v___x_2545_;
goto _start;
}
}
else
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v_slice_2551_; lean_object* v_nextIt_2553_; 
v___x_2548_ = lean_string_utf8_next_fast(v_str_2533_, v___x_2539_);
v___x_2549_ = lean_nat_sub(v___x_2548_, v___x_2539_);
lean_dec(v___x_2539_);
v___x_2550_ = lean_nat_add(v_searcher_2529_, v___x_2549_);
lean_dec(v___x_2549_);
v_slice_2551_ = l_String_Slice_subslice_x21(v___x_2496_, v_currPos_2528_, v_searcher_2529_);
lean_inc(v___x_2550_);
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 1, v___x_2550_);
lean_ctor_set(v___x_2531_, 0, v___x_2550_);
v_nextIt_2553_ = v___x_2531_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2550_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v___x_2550_);
v_nextIt_2553_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
lean_object* v_startInclusive_2554_; lean_object* v_endExclusive_2555_; 
v_startInclusive_2554_ = lean_ctor_get(v_slice_2551_, 0);
lean_inc(v_startInclusive_2554_);
v_endExclusive_2555_ = lean_ctor_get(v_slice_2551_, 1);
lean_inc(v_endExclusive_2555_);
lean_dec_ref(v_slice_2551_);
v_it_2501_ = v_nextIt_2553_;
v_startInclusive_2502_ = v_startInclusive_2554_;
v_endExclusive_2503_ = v_endExclusive_2555_;
goto v___jp_2500_;
}
}
}
else
{
lean_object* v___x_2557_; 
lean_del_object(v___x_2531_);
lean_dec(v_searcher_2529_);
v___x_2557_ = lean_box(1);
lean_inc(v___x_2497_);
v_it_2501_ = v___x_2557_;
v_startInclusive_2502_ = v_currPos_2528_;
v_endExclusive_2503_ = v___x_2497_;
goto v___jp_2500_;
}
}
}
else
{
lean_object* v___x_2559_; 
lean_dec(v___x_2497_);
lean_dec_ref(v___x_2495_);
v___x_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2559_, 0, v_b_2499_);
return v___x_2559_;
}
v___jp_2500_:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
lean_inc_ref(v___x_2495_);
v___x_2504_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2495_);
lean_ctor_set(v___x_2504_, 1, v_startInclusive_2502_);
lean_ctor_set(v___x_2504_, 2, v_endExclusive_2503_);
v___x_2505_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
v___x_2506_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2507_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2504_, v___x_2505_, v___x_2506_);
lean_dec_ref_known(v___x_2504_, 3);
v___x_2508_ = lean_array_to_list(v___x_2507_);
if (lean_obj_tag(v___x_2508_) == 0)
{
v_a_2498_ = v_it_2501_;
goto _start;
}
else
{
lean_object* v_tail_2510_; 
v_tail_2510_ = lean_ctor_get(v___x_2508_, 1);
lean_inc(v_tail_2510_);
if (lean_obj_tag(v_tail_2510_) == 0)
{
lean_object* v_head_2511_; lean_object* v___x_2512_; 
v_head_2511_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_head_2511_);
lean_dec_ref_known(v___x_2508_, 2);
v___x_2512_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2511_);
lean_dec(v_head_2511_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v___x_2513_; 
lean_dec(v_it_2501_);
lean_dec_ref(v_b_2499_);
lean_dec(v___x_2497_);
lean_dec_ref(v___x_2495_);
v___x_2513_ = lean_box(0);
return v___x_2513_;
}
else
{
lean_object* v_val_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v_val_2514_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_val_2514_);
lean_dec_ref_known(v___x_2512_, 1);
v___x_2515_ = lean_box(0);
v___x_2516_ = l_Std_Http_URI_Query_insertEncoded(v_b_2499_, v_val_2514_, v___x_2515_);
v_a_2498_ = v_it_2501_;
v_b_2499_ = v___x_2516_;
goto _start;
}
}
else
{
lean_object* v_head_2518_; lean_object* v___x_2519_; 
v_head_2518_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_head_2518_);
lean_dec_ref_known(v___x_2508_, 2);
v___x_2519_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2518_);
lean_dec(v_head_2518_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v___x_2520_; 
lean_dec(v_tail_2510_);
lean_dec(v_it_2501_);
lean_dec_ref(v_b_2499_);
lean_dec(v___x_2497_);
lean_dec_ref(v___x_2495_);
v___x_2520_ = lean_box(0);
return v___x_2520_;
}
else
{
lean_object* v_val_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v_val_2521_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_val_2521_);
lean_dec_ref_known(v___x_2519_, 1);
v___x_2522_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2523_ = l_String_intercalate(v___x_2522_, v_tail_2510_);
v___x_2524_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2523_);
lean_dec_ref(v___x_2523_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v___x_2525_; 
lean_dec(v_val_2521_);
lean_dec(v_it_2501_);
lean_dec_ref(v_b_2499_);
lean_dec(v___x_2497_);
lean_dec_ref(v___x_2495_);
v___x_2525_ = lean_box(0);
return v___x_2525_;
}
else
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Std_Http_URI_Query_insertEncoded(v_b_2499_, v_val_2521_, v___x_2524_);
v_a_2498_ = v_it_2501_;
v_b_2499_ = v___x_2526_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___boxed(lean_object* v___x_2560_, lean_object* v___x_2561_, lean_object* v___x_2562_, lean_object* v_a_2563_, lean_object* v_b_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2560_, v___x_2561_, v___x_2562_, v_a_2563_, v_b_2564_);
lean_dec_ref(v___x_2561_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(lean_object* v___x_2566_, lean_object* v___x_2567_, lean_object* v___x_2568_, lean_object* v_a_2569_, lean_object* v_b_2570_){
_start:
{
lean_object* v_it_2572_; lean_object* v_startInclusive_2573_; lean_object* v_endExclusive_2574_; 
if (lean_obj_tag(v_a_2569_) == 0)
{
lean_object* v_currPos_2599_; lean_object* v_searcher_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2629_; 
v_currPos_2599_ = lean_ctor_get(v_a_2569_, 0);
v_searcher_2600_ = lean_ctor_get(v_a_2569_, 1);
v_isSharedCheck_2629_ = !lean_is_exclusive(v_a_2569_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2602_ = v_a_2569_;
v_isShared_2603_ = v_isSharedCheck_2629_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_searcher_2600_);
lean_inc(v_currPos_2599_);
lean_dec(v_a_2569_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2629_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v_str_2604_; lean_object* v_startInclusive_2605_; lean_object* v_endExclusive_2606_; lean_object* v___x_2607_; uint8_t v_decide_2608_; 
v_str_2604_ = lean_ctor_get(v___x_2567_, 0);
v_startInclusive_2605_ = lean_ctor_get(v___x_2567_, 1);
v_endExclusive_2606_ = lean_ctor_get(v___x_2567_, 2);
v___x_2607_ = lean_nat_sub(v_endExclusive_2606_, v_startInclusive_2605_);
v_decide_2608_ = lean_nat_dec_eq(v_searcher_2600_, v___x_2607_);
lean_dec(v___x_2607_);
if (v_decide_2608_ == 0)
{
lean_object* v___x_2609_; uint32_t v___x_2610_; uint32_t v___x_2611_; uint8_t v___x_2612_; 
v___x_2609_ = lean_nat_add(v_startInclusive_2605_, v_searcher_2600_);
v___x_2610_ = lean_string_utf8_get_fast(v_str_2604_, v___x_2609_);
v___x_2611_ = 38;
v___x_2612_ = lean_uint32_dec_eq(v___x_2610_, v___x_2611_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2616_; 
lean_dec(v_searcher_2600_);
v___x_2613_ = lean_string_utf8_next_fast(v_str_2604_, v___x_2609_);
lean_dec(v___x_2609_);
v___x_2614_ = lean_nat_sub(v___x_2613_, v_startInclusive_2605_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 1, v___x_2614_);
v___x_2616_ = v___x_2602_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_currPos_2599_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v___x_2614_);
v___x_2616_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
lean_object* v___x_2617_; 
v___x_2617_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2566_, v___x_2567_, v___x_2568_, v___x_2616_, v_b_2570_);
return v___x_2617_;
}
}
else
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v_slice_2622_; lean_object* v_nextIt_2624_; 
v___x_2619_ = lean_string_utf8_next_fast(v_str_2604_, v___x_2609_);
v___x_2620_ = lean_nat_sub(v___x_2619_, v___x_2609_);
lean_dec(v___x_2609_);
v___x_2621_ = lean_nat_add(v_searcher_2600_, v___x_2620_);
lean_dec(v___x_2620_);
v_slice_2622_ = l_String_Slice_subslice_x21(v___x_2567_, v_currPos_2599_, v_searcher_2600_);
lean_inc(v___x_2621_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 1, v___x_2621_);
lean_ctor_set(v___x_2602_, 0, v___x_2621_);
v_nextIt_2624_ = v___x_2602_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2621_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v___x_2621_);
v_nextIt_2624_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
lean_object* v_startInclusive_2625_; lean_object* v_endExclusive_2626_; 
v_startInclusive_2625_ = lean_ctor_get(v_slice_2622_, 0);
lean_inc(v_startInclusive_2625_);
v_endExclusive_2626_ = lean_ctor_get(v_slice_2622_, 1);
lean_inc(v_endExclusive_2626_);
lean_dec_ref(v_slice_2622_);
v_it_2572_ = v_nextIt_2624_;
v_startInclusive_2573_ = v_startInclusive_2625_;
v_endExclusive_2574_ = v_endExclusive_2626_;
goto v___jp_2571_;
}
}
}
else
{
lean_object* v___x_2628_; 
lean_del_object(v___x_2602_);
lean_dec(v_searcher_2600_);
v___x_2628_ = lean_box(1);
lean_inc(v___x_2568_);
v_it_2572_ = v___x_2628_;
v_startInclusive_2573_ = v_currPos_2599_;
v_endExclusive_2574_ = v___x_2568_;
goto v___jp_2571_;
}
}
}
else
{
lean_object* v___x_2630_; 
lean_dec(v___x_2568_);
lean_dec_ref(v___x_2566_);
v___x_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2630_, 0, v_b_2570_);
return v___x_2630_;
}
v___jp_2571_:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
lean_inc_ref(v___x_2566_);
v___x_2575_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2566_);
lean_ctor_set(v___x_2575_, 1, v_startInclusive_2573_);
lean_ctor_set(v___x_2575_, 2, v_endExclusive_2574_);
v___x_2576_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
v___x_2577_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2578_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2575_, v___x_2576_, v___x_2577_);
lean_dec_ref_known(v___x_2575_, 3);
v___x_2579_ = lean_array_to_list(v___x_2578_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v___x_2580_; 
v___x_2580_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2566_, v___x_2567_, v___x_2568_, v_it_2572_, v_b_2570_);
return v___x_2580_;
}
else
{
lean_object* v_tail_2581_; 
v_tail_2581_ = lean_ctor_get(v___x_2579_, 1);
lean_inc(v_tail_2581_);
if (lean_obj_tag(v_tail_2581_) == 0)
{
lean_object* v_head_2582_; lean_object* v___x_2583_; 
v_head_2582_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_head_2582_);
lean_dec_ref_known(v___x_2579_, 2);
v___x_2583_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2582_);
lean_dec(v_head_2582_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v___x_2584_; 
lean_dec(v_it_2572_);
lean_dec_ref(v_b_2570_);
lean_dec(v___x_2568_);
lean_dec_ref(v___x_2566_);
v___x_2584_ = lean_box(0);
return v___x_2584_;
}
else
{
lean_object* v_val_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v_val_2585_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_val_2585_);
lean_dec_ref_known(v___x_2583_, 1);
v___x_2586_ = lean_box(0);
v___x_2587_ = l_Std_Http_URI_Query_insertEncoded(v_b_2570_, v_val_2585_, v___x_2586_);
v___x_2588_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2566_, v___x_2567_, v___x_2568_, v_it_2572_, v___x_2587_);
return v___x_2588_;
}
}
else
{
lean_object* v_head_2589_; lean_object* v___x_2590_; 
v_head_2589_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_head_2589_);
lean_dec_ref_known(v___x_2579_, 2);
v___x_2590_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2589_);
lean_dec(v_head_2589_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v___x_2591_; 
lean_dec(v_tail_2581_);
lean_dec(v_it_2572_);
lean_dec_ref(v_b_2570_);
lean_dec(v___x_2568_);
lean_dec_ref(v___x_2566_);
v___x_2591_ = lean_box(0);
return v___x_2591_;
}
else
{
lean_object* v_val_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v_val_2592_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_val_2592_);
lean_dec_ref_known(v___x_2590_, 1);
v___x_2593_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2594_ = l_String_intercalate(v___x_2593_, v_tail_2581_);
v___x_2595_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2594_);
lean_dec_ref(v___x_2594_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v___x_2596_; 
lean_dec(v_val_2592_);
lean_dec(v_it_2572_);
lean_dec_ref(v_b_2570_);
lean_dec(v___x_2568_);
lean_dec_ref(v___x_2566_);
v___x_2596_ = lean_box(0);
return v___x_2596_;
}
else
{
lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2597_ = l_Std_Http_URI_Query_insertEncoded(v_b_2570_, v_val_2592_, v___x_2595_);
v___x_2598_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2566_, v___x_2567_, v___x_2568_, v_it_2572_, v___x_2597_);
return v___x_2598_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg___boxed(lean_object* v___x_2631_, lean_object* v___x_2632_, lean_object* v___x_2633_, lean_object* v_a_2634_, lean_object* v_b_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2631_, v___x_2632_, v___x_2633_, v_a_2634_, v_b_2635_);
lean_dec_ref(v___x_2632_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(lean_object* v_config_2642_, lean_object* v_a_2643_){
_start:
{
lean_object* v_maxQueryLength_2644_; lean_object* v_maxQueryParams_2645_; lean_object* v___f_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v_snd_2649_; lean_object* v_fst_2650_; lean_object* v_fst_2651_; lean_object* v_array_2652_; lean_object* v_idx_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2703_; 
v_maxQueryLength_2644_ = lean_ctor_get(v_config_2642_, 4);
lean_inc(v_maxQueryLength_2644_);
v_maxQueryParams_2645_ = lean_ctor_get(v_config_2642_, 8);
lean_inc(v_maxQueryParams_2645_);
lean_dec_ref(v_config_2642_);
v___f_2646_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2647_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2643_);
v___x_2648_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2646_, v_maxQueryLength_2644_, v___x_2647_, v_a_2643_);
lean_dec(v_maxQueryLength_2644_);
v_snd_2649_ = lean_ctor_get(v___x_2648_, 1);
lean_inc(v_snd_2649_);
v_fst_2650_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_fst_2650_);
lean_dec_ref(v___x_2648_);
v_fst_2651_ = lean_ctor_get(v_snd_2649_, 0);
lean_inc(v_fst_2651_);
lean_dec(v_snd_2649_);
v_array_2652_ = lean_ctor_get(v_a_2643_, 0);
v_idx_2653_ = lean_ctor_get(v_a_2643_, 1);
v_isSharedCheck_2703_ = !lean_is_exclusive(v_a_2643_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2655_ = v_a_2643_;
v_isShared_2656_ = v_isSharedCheck_2703_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_idx_2653_);
lean_inc(v_array_2652_);
lean_dec(v_a_2643_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2703_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v_lower_2658_; lean_object* v_upper_2659_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___y_2700_; uint8_t v___x_2702_; 
v___x_2697_ = lean_nat_add(v_idx_2653_, v_fst_2650_);
lean_dec(v_fst_2650_);
v___x_2698_ = lean_byte_array_size(v_array_2652_);
v___x_2702_ = lean_nat_dec_le(v_idx_2653_, v___x_2647_);
if (v___x_2702_ == 0)
{
v___y_2700_ = v_idx_2653_;
goto v___jp_2699_;
}
else
{
lean_dec(v_idx_2653_);
v___y_2700_ = v___x_2647_;
goto v___jp_2699_;
}
v___jp_2657_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; uint8_t v___x_2662_; 
v___x_2660_ = l_ByteArray_toByteSlice(v_array_2652_, v_lower_2658_, v_upper_2659_);
v___x_2661_ = l_ByteSlice_toByteArray(v___x_2660_);
v___x_2662_ = lean_string_validate_utf8(v___x_2661_);
if (v___x_2662_ == 0)
{
lean_object* v___x_2663_; lean_object* v___x_2665_; 
lean_dec_ref(v___x_2661_);
lean_dec(v_maxQueryParams_2645_);
v___x_2663_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2656_ == 0)
{
lean_ctor_set_tag(v___x_2655_, 1);
lean_ctor_set(v___x_2655_, 1, v___x_2663_);
lean_ctor_set(v___x_2655_, 0, v_fst_2651_);
v___x_2665_ = v___x_2655_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_fst_2651_);
lean_ctor_set(v_reuseFailAlloc_2666_, 1, v___x_2663_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
else
{
lean_object* v___x_2667_; lean_object* v___x_2668_; uint8_t v___x_2669_; 
v___x_2667_ = lean_string_from_utf8_unchecked(v___x_2661_);
v___x_2668_ = lean_string_utf8_byte_size(v___x_2667_);
v___x_2669_ = lean_nat_dec_eq(v___x_2668_, v___x_2647_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; uint8_t v___x_2673_; 
lean_inc_ref(v___x_2667_);
v___x_2670_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2667_);
lean_ctor_set(v___x_2670_, 1, v___x_2647_);
lean_ctor_set(v___x_2670_, 2, v___x_2668_);
v___x_2671_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0);
v___x_2672_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2667_, v___x_2670_, v___x_2668_, v___x_2671_, v___x_2647_);
v___x_2673_ = lean_nat_dec_lt(v_maxQueryParams_2645_, v___x_2672_);
lean_dec(v___x_2672_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
lean_dec(v_maxQueryParams_2645_);
v___x_2674_ = l_Std_Http_URI_Query_empty;
v___x_2675_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2667_, v___x_2670_, v___x_2668_, v___x_2671_, v___x_2674_);
lean_dec_ref_known(v___x_2670_, 3);
if (lean_obj_tag(v___x_2675_) == 1)
{
lean_object* v_val_2676_; lean_object* v___x_2678_; 
v_val_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_val_2676_);
lean_dec_ref_known(v___x_2675_, 1);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 1, v_val_2676_);
lean_ctor_set(v___x_2655_, 0, v_fst_2651_);
v___x_2678_ = v___x_2655_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_fst_2651_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v_val_2676_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
else
{
lean_object* v___x_2680_; lean_object* v___x_2682_; 
lean_dec(v___x_2675_);
v___x_2680_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2656_ == 0)
{
lean_ctor_set_tag(v___x_2655_, 1);
lean_ctor_set(v___x_2655_, 1, v___x_2680_);
lean_ctor_set(v___x_2655_, 0, v_fst_2651_);
v___x_2682_ = v___x_2655_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_fst_2651_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
else
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2691_; 
lean_dec_ref_known(v___x_2670_, 3);
lean_dec_ref(v___x_2667_);
v___x_2684_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3));
v___x_2685_ = l_Nat_reprFast(v_maxQueryParams_2645_);
v___x_2686_ = lean_string_append(v___x_2684_, v___x_2685_);
lean_dec_ref(v___x_2685_);
v___x_2687_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_2688_ = lean_string_append(v___x_2686_, v___x_2687_);
v___x_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2688_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set_tag(v___x_2655_, 1);
lean_ctor_set(v___x_2655_, 1, v___x_2689_);
lean_ctor_set(v___x_2655_, 0, v_fst_2651_);
v___x_2691_ = v___x_2655_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_fst_2651_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v___x_2689_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
else
{
lean_object* v___x_2693_; lean_object* v___x_2695_; 
lean_dec_ref(v___x_2667_);
lean_dec(v_maxQueryParams_2645_);
v___x_2693_ = l_Std_Http_URI_Query_empty;
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 1, v___x_2693_);
lean_ctor_set(v___x_2655_, 0, v_fst_2651_);
v___x_2695_ = v___x_2655_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_fst_2651_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v___x_2693_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
v___jp_2699_:
{
uint8_t v___x_2701_; 
v___x_2701_ = lean_nat_dec_le(v___x_2697_, v___x_2698_);
if (v___x_2701_ == 0)
{
lean_dec(v___x_2697_);
v_lower_2658_ = v___y_2700_;
v_upper_2659_ = v___x_2698_;
goto v___jp_2657_;
}
else
{
v_lower_2658_ = v___y_2700_;
v_upper_2659_ = v___x_2697_;
goto v___jp_2657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(lean_object* v___x_2704_, lean_object* v___x_2705_, lean_object* v___x_2706_, lean_object* v_inst_2707_, lean_object* v_R_2708_, lean_object* v_a_2709_, lean_object* v_b_2710_, lean_object* v_c_2711_){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2704_, v___x_2705_, v___x_2706_, v_a_2709_, v_b_2710_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___boxed(lean_object* v___x_2713_, lean_object* v___x_2714_, lean_object* v___x_2715_, lean_object* v_inst_2716_, lean_object* v_R_2717_, lean_object* v_a_2718_, lean_object* v_b_2719_, lean_object* v_c_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(v___x_2713_, v___x_2714_, v___x_2715_, v_inst_2716_, v_R_2717_, v_a_2718_, v_b_2719_, v_c_2720_);
lean_dec(v___x_2715_);
lean_dec_ref(v___x_2714_);
lean_dec_ref(v___x_2713_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(lean_object* v_out_2722_, lean_object* v_inst_2723_, lean_object* v_R_2724_, lean_object* v_a_2725_, lean_object* v_b_2726_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2722_, v_a_2725_, v_b_2726_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___boxed(lean_object* v_out_2728_, lean_object* v_inst_2729_, lean_object* v_R_2730_, lean_object* v_a_2731_, lean_object* v_b_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(v_out_2728_, v_inst_2729_, v_R_2730_, v_a_2731_, v_b_2732_);
lean_dec_ref(v_out_2728_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(lean_object* v___x_2734_, lean_object* v___x_2735_, lean_object* v___x_2736_, lean_object* v_inst_2737_, lean_object* v_R_2738_, lean_object* v_a_2739_, lean_object* v_b_2740_, lean_object* v_c_2741_){
_start:
{
lean_object* v___x_2742_; 
v___x_2742_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2734_, v___x_2735_, v___x_2736_, v_a_2739_, v_b_2740_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___boxed(lean_object* v___x_2743_, lean_object* v___x_2744_, lean_object* v___x_2745_, lean_object* v_inst_2746_, lean_object* v_R_2747_, lean_object* v_a_2748_, lean_object* v_b_2749_, lean_object* v_c_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(v___x_2743_, v___x_2744_, v___x_2745_, v_inst_2746_, v_R_2747_, v_a_2748_, v_b_2749_, v_c_2750_);
lean_dec_ref(v___x_2744_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(lean_object* v___x_2752_, lean_object* v___x_2753_, lean_object* v___x_2754_, lean_object* v_inst_2755_, lean_object* v_R_2756_, lean_object* v_a_2757_, lean_object* v_b_2758_, lean_object* v_c_2759_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2753_, v___x_2754_, v_a_2757_, v_b_2758_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___boxed(lean_object* v___x_2761_, lean_object* v___x_2762_, lean_object* v___x_2763_, lean_object* v_inst_2764_, lean_object* v_R_2765_, lean_object* v_a_2766_, lean_object* v_b_2767_, lean_object* v_c_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(v___x_2761_, v___x_2762_, v___x_2763_, v_inst_2764_, v_R_2765_, v_a_2766_, v_b_2767_, v_c_2768_);
lean_dec(v___x_2763_);
lean_dec_ref(v___x_2762_);
lean_dec_ref(v___x_2761_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(lean_object* v___x_2770_, lean_object* v___x_2771_, lean_object* v___x_2772_, lean_object* v_inst_2773_, lean_object* v_R_2774_, lean_object* v_a_2775_, lean_object* v_b_2776_, lean_object* v_c_2777_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2770_, v___x_2771_, v___x_2772_, v_a_2775_, v_b_2776_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___boxed(lean_object* v___x_2779_, lean_object* v___x_2780_, lean_object* v___x_2781_, lean_object* v_inst_2782_, lean_object* v_R_2783_, lean_object* v_a_2784_, lean_object* v_b_2785_, lean_object* v_c_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(v___x_2779_, v___x_2780_, v___x_2781_, v_inst_2782_, v_R_2783_, v_a_2784_, v_b_2785_, v_c_2786_);
lean_dec_ref(v___x_2780_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(lean_object* v_config_2791_, lean_object* v_a_2792_){
_start:
{
lean_object* v_maxFragmentLength_2793_; lean_object* v___f_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v_snd_2797_; lean_object* v_fst_2798_; lean_object* v_fst_2799_; lean_object* v_array_2800_; lean_object* v_idx_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2825_; 
v_maxFragmentLength_2793_ = lean_ctor_get(v_config_2791_, 5);
v___f_2794_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2795_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2792_);
v___x_2796_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2794_, v_maxFragmentLength_2793_, v___x_2795_, v_a_2792_);
v_snd_2797_ = lean_ctor_get(v___x_2796_, 1);
lean_inc(v_snd_2797_);
v_fst_2798_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_fst_2798_);
lean_dec_ref(v___x_2796_);
v_fst_2799_ = lean_ctor_get(v_snd_2797_, 0);
lean_inc(v_fst_2799_);
lean_dec(v_snd_2797_);
v_array_2800_ = lean_ctor_get(v_a_2792_, 0);
v_idx_2801_ = lean_ctor_get(v_a_2792_, 1);
v_isSharedCheck_2825_ = !lean_is_exclusive(v_a_2792_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2803_ = v_a_2792_;
v_isShared_2804_ = v_isSharedCheck_2825_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_idx_2801_);
lean_inc(v_array_2800_);
lean_dec(v_a_2792_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2825_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v_lower_2806_; lean_object* v_upper_2807_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___y_2822_; uint8_t v___x_2824_; 
v___x_2819_ = lean_nat_add(v_idx_2801_, v_fst_2798_);
lean_dec(v_fst_2798_);
v___x_2820_ = lean_byte_array_size(v_array_2800_);
v___x_2824_ = lean_nat_dec_le(v_idx_2801_, v___x_2795_);
if (v___x_2824_ == 0)
{
v___y_2822_ = v_idx_2801_;
goto v___jp_2821_;
}
else
{
lean_dec(v_idx_2801_);
v___y_2822_ = v___x_2795_;
goto v___jp_2821_;
}
v___jp_2805_:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2808_ = l_ByteArray_toByteSlice(v_array_2800_, v_lower_2806_, v_upper_2807_);
v___x_2809_ = l_ByteSlice_toByteArray(v___x_2808_);
v___x_2810_ = l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(v___x_2809_);
if (lean_obj_tag(v___x_2810_) == 1)
{
lean_object* v_val_2811_; lean_object* v___x_2813_; 
v_val_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_val_2811_);
lean_dec_ref_known(v___x_2810_, 1);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 1, v_val_2811_);
lean_ctor_set(v___x_2803_, 0, v_fst_2799_);
v___x_2813_ = v___x_2803_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_fst_2799_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v_val_2811_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
else
{
lean_object* v___x_2815_; lean_object* v___x_2817_; 
lean_dec(v___x_2810_);
v___x_2815_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1));
if (v_isShared_2804_ == 0)
{
lean_ctor_set_tag(v___x_2803_, 1);
lean_ctor_set(v___x_2803_, 1, v___x_2815_);
lean_ctor_set(v___x_2803_, 0, v_fst_2799_);
v___x_2817_ = v___x_2803_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_fst_2799_);
lean_ctor_set(v_reuseFailAlloc_2818_, 1, v___x_2815_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
v___jp_2821_:
{
uint8_t v___x_2823_; 
v___x_2823_ = lean_nat_dec_le(v___x_2819_, v___x_2820_);
if (v___x_2823_ == 0)
{
lean_dec(v___x_2819_);
v_lower_2806_ = v___y_2822_;
v_upper_2807_ = v___x_2820_;
goto v___jp_2805_;
}
else
{
v_lower_2806_ = v___y_2822_;
v_upper_2807_ = v___x_2819_;
goto v___jp_2805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___boxed(lean_object* v_config_2826_, lean_object* v_a_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2826_, v_a_2827_);
lean_dec_ref(v_config_2826_);
return v_res_2828_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1(void){
_start:
{
lean_object* v___x_2830_; lean_object* v_utf8_2831_; 
v___x_2830_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0));
v_utf8_2831_ = lean_string_to_utf8(v___x_2830_);
return v_utf8_2831_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(lean_object* v_config_2832_, lean_object* v_a_2833_){
_start:
{
uint8_t v___y_2835_; lean_object* v_pos_2836_; lean_object* v_res_2837_; uint8_t v___y_2859_; lean_object* v___y_2860_; lean_object* v_err_2861_; lean_object* v_pos_2867_; lean_object* v_utf8_2875_; lean_object* v___x_2876_; 
v_utf8_2875_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_2833_);
v___x_2876_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_2875_, v_a_2833_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_pos_2877_; 
lean_dec_ref(v_a_2833_);
v_pos_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_pos_2877_);
lean_dec_ref_known(v___x_2876_, 2);
v_pos_2867_ = v_pos_2877_;
goto v___jp_2866_;
}
else
{
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_pos_2878_; 
lean_dec_ref(v_a_2833_);
v_pos_2878_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_pos_2878_);
lean_dec_ref_known(v___x_2876_, 2);
v_pos_2867_ = v_pos_2878_;
goto v___jp_2866_;
}
else
{
lean_object* v_err_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2910_; 
v_err_2879_ = lean_ctor_get(v___x_2876_, 1);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2910_ == 0)
{
lean_object* v_unused_2911_; 
v_unused_2911_ = lean_ctor_get(v___x_2876_, 0);
lean_dec(v_unused_2911_);
v___x_2881_ = v___x_2876_;
v_isShared_2882_ = v_isSharedCheck_2910_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_err_2879_);
lean_dec(v___x_2876_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2910_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v_idx_2883_; uint8_t v___x_2884_; 
v_idx_2883_ = lean_ctor_get(v_a_2833_, 1);
v___x_2884_ = lean_nat_dec_eq(v_idx_2883_, v_idx_2883_);
if (v___x_2884_ == 0)
{
lean_object* v___x_2886_; 
lean_dec_ref(v_config_2832_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 0, v_a_2833_);
v___x_2886_ = v___x_2881_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2833_);
lean_ctor_set(v_reuseFailAlloc_2887_, 1, v_err_2879_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
else
{
uint8_t v___x_2888_; lean_object* v___x_2889_; 
lean_del_object(v___x_2881_);
lean_dec(v_err_2879_);
v___x_2888_ = 0;
v___x_2889_ = l_Std_Http_URI_Parser_parsePath(v_config_2832_, v___x_2888_, v___x_2884_, v_a_2833_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_pos_2890_; lean_object* v_res_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2900_; 
v_pos_2890_ = lean_ctor_get(v___x_2889_, 0);
v_res_2891_ = lean_ctor_get(v___x_2889_, 1);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2893_ = v___x_2889_;
v_isShared_2894_ = v_isSharedCheck_2900_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_res_2891_);
lean_inc(v_pos_2890_);
lean_dec(v___x_2889_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2900_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2898_; 
v___x_2895_ = lean_box(0);
v___x_2896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
lean_ctor_set(v___x_2896_, 1, v_res_2891_);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 1, v___x_2896_);
v___x_2898_ = v___x_2893_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_pos_2890_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v___x_2896_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
else
{
lean_object* v_pos_2901_; lean_object* v_err_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2909_; 
v_pos_2901_ = lean_ctor_get(v___x_2889_, 0);
v_err_2902_ = lean_ctor_get(v___x_2889_, 1);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2904_ = v___x_2889_;
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_err_2902_);
lean_inc(v_pos_2901_);
lean_dec(v___x_2889_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2907_; 
if (v_isShared_2905_ == 0)
{
v___x_2907_ = v___x_2904_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_pos_2901_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v_err_2902_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
}
}
}
v___jp_2834_:
{
lean_object* v___x_2838_; 
v___x_2838_ = l_Std_Http_URI_Parser_parsePath(v_config_2832_, v___y_2835_, v___y_2835_, v_pos_2836_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_pos_2839_; lean_object* v_res_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2848_; 
v_pos_2839_ = lean_ctor_get(v___x_2838_, 0);
v_res_2840_ = lean_ctor_get(v___x_2838_, 1);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2842_ = v___x_2838_;
v_isShared_2843_ = v_isSharedCheck_2848_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_res_2840_);
lean_inc(v_pos_2839_);
lean_dec(v___x_2838_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2848_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2844_; lean_object* v___x_2846_; 
v___x_2844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2844_, 0, v_res_2837_);
lean_ctor_set(v___x_2844_, 1, v_res_2840_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 1, v___x_2844_);
v___x_2846_ = v___x_2842_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_pos_2839_);
lean_ctor_set(v_reuseFailAlloc_2847_, 1, v___x_2844_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
else
{
lean_object* v_pos_2849_; lean_object* v_err_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
lean_dec(v_res_2837_);
v_pos_2849_ = lean_ctor_get(v___x_2838_, 0);
v_err_2850_ = lean_ctor_get(v___x_2838_, 1);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2838_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_err_2850_);
lean_inc(v_pos_2849_);
lean_dec(v___x_2838_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_pos_2849_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_err_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
v___jp_2858_:
{
lean_object* v_idx_2862_; uint8_t v___x_2863_; 
v_idx_2862_ = lean_ctor_get(v___y_2860_, 1);
v___x_2863_ = lean_nat_dec_eq(v_idx_2862_, v_idx_2862_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; 
lean_dec_ref(v_config_2832_);
v___x_2864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___y_2860_);
lean_ctor_set(v___x_2864_, 1, v_err_2861_);
return v___x_2864_;
}
else
{
lean_object* v___x_2865_; 
lean_dec(v_err_2861_);
v___x_2865_ = lean_box(0);
v___y_2835_ = v___y_2859_;
v_pos_2836_ = v___y_2860_;
v_res_2837_ = v___x_2865_;
goto v___jp_2834_;
}
}
v___jp_2866_:
{
uint8_t v___x_2868_; lean_object* v___x_2869_; 
v___x_2868_ = 1;
lean_inc_ref(v_pos_2867_);
v___x_2869_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_2832_, v_pos_2867_);
if (lean_obj_tag(v___x_2869_) == 0)
{
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_pos_2870_; lean_object* v_res_2871_; lean_object* v___x_2872_; 
lean_dec_ref(v_pos_2867_);
v_pos_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_pos_2870_);
v_res_2871_ = lean_ctor_get(v___x_2869_, 1);
lean_inc(v_res_2871_);
lean_dec_ref_known(v___x_2869_, 2);
v___x_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2872_, 0, v_res_2871_);
v___y_2835_ = v___x_2868_;
v_pos_2836_ = v_pos_2870_;
v_res_2837_ = v___x_2872_;
goto v___jp_2834_;
}
else
{
lean_object* v_err_2873_; 
v_err_2873_ = lean_ctor_get(v___x_2869_, 1);
lean_inc(v_err_2873_);
lean_dec_ref_known(v___x_2869_, 2);
v___y_2859_ = v___x_2868_;
v___y_2860_ = v_pos_2867_;
v_err_2861_ = v_err_2873_;
goto v___jp_2858_;
}
}
else
{
lean_object* v_err_2874_; 
v_err_2874_ = lean_ctor_get(v___x_2869_, 1);
lean_inc(v_err_2874_);
lean_dec_ref_known(v___x_2869_, 2);
v___y_2859_ = v___x_2868_;
v___y_2860_ = v_pos_2867_;
v_err_2861_ = v_err_2874_;
goto v___jp_2858_;
}
}
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__0(void){
_start:
{
uint8_t v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v___x_2913_ = lean_uint8_to_nat(v___x_2912_);
return v___x_2913_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__1(void){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__0, &l_Std_Http_URI_Parser_parseURI___closed__0_once, _init_l_Std_Http_URI_Parser_parseURI___closed__0);
v___x_2915_ = l_Nat_reprFast(v___x_2914_);
return v___x_2915_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__2(void){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2916_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__1, &l_Std_Http_URI_Parser_parseURI___closed__1_once, _init_l_Std_Http_URI_Parser_parseURI___closed__1);
v___x_2917_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_2918_ = lean_string_append(v___x_2917_, v___x_2916_);
return v___x_2918_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__3(void){
_start:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2919_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_2920_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__2, &l_Std_Http_URI_Parser_parseURI___closed__2_once, _init_l_Std_Http_URI_Parser_parseURI___closed__2);
v___x_2921_ = lean_string_append(v___x_2920_, v___x_2919_);
return v___x_2921_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__4(void){
_start:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2922_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__3, &l_Std_Http_URI_Parser_parseURI___closed__3_once, _init_l_Std_Http_URI_Parser_parseURI___closed__3);
v___x_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2922_);
return v___x_2923_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__7(void){
_start:
{
uint8_t v___x_2927_; lean_object* v___x_2928_; 
v___x_2927_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_2928_ = lean_uint8_to_nat(v___x_2927_);
return v___x_2928_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__8(void){
_start:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2929_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__7, &l_Std_Http_URI_Parser_parseURI___closed__7_once, _init_l_Std_Http_URI_Parser_parseURI___closed__7);
v___x_2930_ = l_Nat_reprFast(v___x_2929_);
return v___x_2930_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__9(void){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2931_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__8, &l_Std_Http_URI_Parser_parseURI___closed__8_once, _init_l_Std_Http_URI_Parser_parseURI___closed__8);
v___x_2932_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_2933_ = lean_string_append(v___x_2932_, v___x_2931_);
return v___x_2933_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__10(void){
_start:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2934_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_2935_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__9, &l_Std_Http_URI_Parser_parseURI___closed__9_once, _init_l_Std_Http_URI_Parser_parseURI___closed__9);
v___x_2936_ = lean_string_append(v___x_2935_, v___x_2934_);
return v___x_2936_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__11(void){
_start:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2937_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__10, &l_Std_Http_URI_Parser_parseURI___closed__10_once, _init_l_Std_Http_URI_Parser_parseURI___closed__10);
v___x_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURI(lean_object* v_config_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_2939_, v_a_2940_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_pos_2942_; lean_object* v_res_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_3074_; 
v_pos_2942_ = lean_ctor_get(v___x_2941_, 0);
v_res_2943_ = lean_ctor_get(v___x_2941_, 1);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_2945_ = v___x_2941_;
v_isShared_2946_ = v_isSharedCheck_3074_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_res_2943_);
lean_inc(v_pos_2942_);
lean_dec(v___x_2941_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_3074_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v_array_2947_; lean_object* v_idx_2948_; lean_object* v___x_2949_; uint8_t v___x_2950_; 
v_array_2947_ = lean_ctor_get(v_pos_2942_, 0);
v_idx_2948_ = lean_ctor_get(v_pos_2942_, 1);
v___x_2949_ = lean_byte_array_size(v_array_2947_);
v___x_2950_ = lean_nat_dec_lt(v_idx_2948_, v___x_2949_);
if (v___x_2950_ == 0)
{
lean_object* v___x_2951_; lean_object* v___x_2953_; 
lean_dec(v_res_2943_);
lean_dec_ref(v_config_2939_);
v___x_2951_ = lean_box(0);
if (v_isShared_2946_ == 0)
{
lean_ctor_set_tag(v___x_2945_, 1);
lean_ctor_set(v___x_2945_, 1, v___x_2951_);
v___x_2953_ = v___x_2945_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_pos_2942_);
lean_ctor_set(v_reuseFailAlloc_2954_, 1, v___x_2951_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
else
{
uint8_t v___x_2955_; uint8_t v_got_2956_; uint8_t v___x_2957_; 
v___x_2955_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v_got_2956_ = lean_byte_array_fget(v_array_2947_, v_idx_2948_);
v___x_2957_ = lean_uint8_dec_eq(v_got_2956_, v___x_2955_);
if (v___x_2957_ == 0)
{
lean_object* v___x_2958_; lean_object* v___x_2960_; 
lean_dec(v_res_2943_);
lean_dec_ref(v_config_2939_);
v___x_2958_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
if (v_isShared_2946_ == 0)
{
lean_ctor_set_tag(v___x_2945_, 1);
lean_ctor_set(v___x_2945_, 1, v___x_2958_);
v___x_2960_ = v___x_2945_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_pos_2942_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v___x_2958_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
else
{
lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_3071_; 
lean_inc(v_idx_2948_);
lean_inc_ref(v_array_2947_);
v_isSharedCheck_3071_ = !lean_is_exclusive(v_pos_2942_);
if (v_isSharedCheck_3071_ == 0)
{
lean_object* v_unused_3072_; lean_object* v_unused_3073_; 
v_unused_3072_ = lean_ctor_get(v_pos_2942_, 1);
lean_dec(v_unused_3072_);
v_unused_3073_ = lean_ctor_get(v_pos_2942_, 0);
lean_dec(v_unused_3073_);
v___x_2963_ = v_pos_2942_;
v_isShared_2964_ = v_isSharedCheck_3071_;
goto v_resetjp_2962_;
}
else
{
lean_dec(v_pos_2942_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_3071_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2968_; 
v___x_2965_ = lean_unsigned_to_nat(1u);
v___x_2966_ = lean_nat_add(v_idx_2948_, v___x_2965_);
lean_dec(v_idx_2948_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 1, v___x_2966_);
v___x_2968_ = v___x_2963_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_array_2947_);
lean_ctor_set(v_reuseFailAlloc_3070_, 1, v___x_2966_);
v___x_2968_ = v_reuseFailAlloc_3070_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
lean_object* v___x_2969_; 
lean_inc_ref(v_config_2939_);
v___x_2969_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2939_, v___x_2968_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_res_2970_; lean_object* v_pos_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_3060_; 
v_res_2970_ = lean_ctor_get(v___x_2969_, 1);
v_pos_2971_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_2973_ = v___x_2969_;
v_isShared_2974_ = v_isSharedCheck_3060_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_res_2970_);
lean_inc(v_pos_2971_);
lean_dec(v___x_2969_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_3060_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v_fst_2975_; lean_object* v_snd_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_3059_; 
v_fst_2975_ = lean_ctor_get(v_res_2970_, 0);
v_snd_2976_ = lean_ctor_get(v_res_2970_, 1);
v_isSharedCheck_3059_ = !lean_is_exclusive(v_res_2970_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_2978_ = v_res_2970_;
v_isShared_2979_ = v_isSharedCheck_3059_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_snd_2976_);
lean_inc(v_fst_2975_);
lean_dec(v_res_2970_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_3059_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___y_2981_; lean_object* v_pos_2982_; lean_object* v_res_2983_; lean_object* v_idx_2989_; lean_object* v___y_2990_; lean_object* v_pos_2991_; lean_object* v_err_2992_; lean_object* v_pos_3000_; lean_object* v_array_3001_; lean_object* v_idx_3002_; lean_object* v_res_3003_; lean_object* v_array_3022_; lean_object* v_idx_3023_; lean_object* v_pos_3025_; lean_object* v_array_3026_; lean_object* v_idx_3027_; lean_object* v_err_3028_; lean_object* v___x_3032_; uint8_t v___x_3033_; 
v_array_3022_ = lean_ctor_get(v_pos_2971_, 0);
lean_inc_ref(v_array_3022_);
v_idx_3023_ = lean_ctor_get(v_pos_2971_, 1);
lean_inc(v_idx_3023_);
v___x_3032_ = lean_byte_array_size(v_array_3022_);
v___x_3033_ = lean_nat_dec_lt(v_idx_3023_, v___x_3032_);
if (v___x_3033_ == 0)
{
lean_object* v___x_3034_; 
v___x_3034_ = lean_box(0);
lean_inc(v_idx_3023_);
v_pos_3025_ = v_pos_2971_;
v_array_3026_ = v_array_3022_;
v_idx_3027_ = v_idx_3023_;
v_err_3028_ = v___x_3034_;
goto v___jp_3024_;
}
else
{
uint8_t v___x_3035_; uint8_t v_got_3036_; uint8_t v___x_3037_; 
v___x_3035_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3036_ = lean_byte_array_fget(v_array_3022_, v_idx_3023_);
v___x_3037_ = lean_uint8_dec_eq(v_got_3036_, v___x_3035_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; 
v___x_3038_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3023_);
v_pos_3025_ = v_pos_2971_;
v_array_3026_ = v_array_3022_;
v_idx_3027_ = v_idx_3023_;
v_err_3028_ = v___x_3038_;
goto v___jp_3024_;
}
else
{
lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3056_; 
v_isSharedCheck_3056_ = !lean_is_exclusive(v_pos_2971_);
if (v_isSharedCheck_3056_ == 0)
{
lean_object* v_unused_3057_; lean_object* v_unused_3058_; 
v_unused_3057_ = lean_ctor_get(v_pos_2971_, 1);
lean_dec(v_unused_3057_);
v_unused_3058_ = lean_ctor_get(v_pos_2971_, 0);
lean_dec(v_unused_3058_);
v___x_3040_ = v_pos_2971_;
v_isShared_3041_ = v_isSharedCheck_3056_;
goto v_resetjp_3039_;
}
else
{
lean_dec(v_pos_2971_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3056_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3042_; lean_object* v___x_3044_; 
v___x_3042_ = lean_nat_add(v_idx_3023_, v___x_2965_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 1, v___x_3042_);
v___x_3044_ = v___x_3040_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_array_3022_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v___x_3042_);
v___x_3044_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
lean_object* v___x_3045_; 
lean_inc_ref(v_config_2939_);
v___x_3045_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2939_, v___x_3044_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v_pos_3046_; lean_object* v_res_3047_; lean_object* v_array_3048_; lean_object* v_idx_3049_; lean_object* v___x_3050_; 
lean_dec(v_idx_3023_);
v_pos_3046_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_pos_3046_);
v_res_3047_ = lean_ctor_get(v___x_3045_, 1);
lean_inc(v_res_3047_);
lean_dec_ref_known(v___x_3045_, 2);
v_array_3048_ = lean_ctor_get(v_pos_3046_, 0);
lean_inc_ref(v_array_3048_);
v_idx_3049_ = lean_ctor_get(v_pos_3046_, 1);
lean_inc(v_idx_3049_);
v___x_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3050_, 0, v_res_3047_);
v_pos_3000_ = v_pos_3046_;
v_array_3001_ = v_array_3048_;
v_idx_3002_ = v_idx_3049_;
v_res_3003_ = v___x_3050_;
goto v___jp_2999_;
}
else
{
lean_object* v_pos_3051_; lean_object* v_err_3052_; lean_object* v_array_3053_; lean_object* v_idx_3054_; 
v_pos_3051_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_pos_3051_);
v_err_3052_ = lean_ctor_get(v___x_3045_, 1);
lean_inc(v_err_3052_);
lean_dec_ref_known(v___x_3045_, 2);
v_array_3053_ = lean_ctor_get(v_pos_3051_, 0);
lean_inc_ref(v_array_3053_);
v_idx_3054_ = lean_ctor_get(v_pos_3051_, 1);
lean_inc(v_idx_3054_);
v_pos_3025_ = v_pos_3051_;
v_array_3026_ = v_array_3053_;
v_idx_3027_ = v_idx_3054_;
v_err_3028_ = v_err_3052_;
goto v___jp_3024_;
}
}
}
}
}
v___jp_2980_:
{
lean_object* v___x_2984_; lean_object* v___x_2986_; 
v___x_2984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2984_, 0, v_res_2943_);
lean_ctor_set(v___x_2984_, 1, v_fst_2975_);
lean_ctor_set(v___x_2984_, 2, v_snd_2976_);
lean_ctor_set(v___x_2984_, 3, v___y_2981_);
lean_ctor_set(v___x_2984_, 4, v_res_2983_);
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 1, v___x_2984_);
lean_ctor_set(v___x_2973_, 0, v_pos_2982_);
v___x_2986_ = v___x_2973_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_pos_2982_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v___x_2984_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
v___jp_2988_:
{
lean_object* v_idx_2993_; uint8_t v___x_2994_; 
v_idx_2993_ = lean_ctor_get(v_pos_2991_, 1);
v___x_2994_ = lean_nat_dec_eq(v_idx_2989_, v_idx_2993_);
lean_dec(v_idx_2989_);
if (v___x_2994_ == 0)
{
lean_object* v___x_2996_; 
lean_dec(v___y_2990_);
lean_dec(v_snd_2976_);
lean_dec(v_fst_2975_);
lean_del_object(v___x_2973_);
lean_dec(v_res_2943_);
if (v_isShared_2946_ == 0)
{
lean_ctor_set_tag(v___x_2945_, 1);
lean_ctor_set(v___x_2945_, 1, v_err_2992_);
lean_ctor_set(v___x_2945_, 0, v_pos_2991_);
v___x_2996_ = v___x_2945_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_pos_2991_);
lean_ctor_set(v_reuseFailAlloc_2997_, 1, v_err_2992_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
else
{
lean_object* v___x_2998_; 
lean_dec(v_err_2992_);
lean_del_object(v___x_2945_);
v___x_2998_ = lean_box(0);
v___y_2981_ = v___y_2990_;
v_pos_2982_ = v_pos_2991_;
v_res_2983_ = v___x_2998_;
goto v___jp_2980_;
}
}
v___jp_2999_:
{
lean_object* v___x_3004_; uint8_t v___x_3005_; 
v___x_3004_ = lean_byte_array_size(v_array_3001_);
v___x_3005_ = lean_nat_dec_lt(v_idx_3002_, v___x_3004_);
if (v___x_3005_ == 0)
{
lean_object* v___x_3006_; 
lean_dec_ref(v_array_3001_);
lean_del_object(v___x_2978_);
lean_dec_ref(v_config_2939_);
v___x_3006_ = lean_box(0);
v_idx_2989_ = v_idx_3002_;
v___y_2990_ = v_res_3003_;
v_pos_2991_ = v_pos_3000_;
v_err_2992_ = v___x_3006_;
goto v___jp_2988_;
}
else
{
uint8_t v___x_3007_; uint8_t v_got_3008_; uint8_t v___x_3009_; 
v___x_3007_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v_got_3008_ = lean_byte_array_fget(v_array_3001_, v_idx_3002_);
v___x_3009_ = lean_uint8_dec_eq(v_got_3008_, v___x_3007_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; 
lean_dec_ref(v_array_3001_);
lean_del_object(v___x_2978_);
lean_dec_ref(v_config_2939_);
v___x_3010_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__4, &l_Std_Http_URI_Parser_parseURI___closed__4_once, _init_l_Std_Http_URI_Parser_parseURI___closed__4);
v_idx_2989_ = v_idx_3002_;
v___y_2990_ = v_res_3003_;
v_pos_2991_ = v_pos_3000_;
v_err_2992_ = v___x_3010_;
goto v___jp_2988_;
}
else
{
lean_object* v___x_3011_; lean_object* v___x_3013_; 
lean_dec_ref(v_pos_3000_);
v___x_3011_ = lean_nat_add(v_idx_3002_, v___x_2965_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 1, v___x_3011_);
lean_ctor_set(v___x_2978_, 0, v_array_3001_);
v___x_3013_ = v___x_2978_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_array_3001_);
lean_ctor_set(v_reuseFailAlloc_3021_, 1, v___x_3011_);
v___x_3013_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
lean_object* v___x_3014_; 
v___x_3014_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2939_, v___x_3013_);
lean_dec_ref(v_config_2939_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_pos_3015_; lean_object* v_res_3016_; lean_object* v___x_3017_; 
v_pos_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_pos_3015_);
v_res_3016_ = lean_ctor_get(v___x_3014_, 1);
lean_inc(v_res_3016_);
lean_dec_ref_known(v___x_3014_, 2);
v___x_3017_ = l_Std_Http_URI_EncodedFragment_decode(v_res_3016_);
lean_dec(v_res_3016_);
if (lean_obj_tag(v___x_3017_) == 1)
{
lean_dec(v_idx_3002_);
lean_del_object(v___x_2945_);
v___y_2981_ = v_res_3003_;
v_pos_2982_ = v_pos_3015_;
v_res_2983_ = v___x_3017_;
goto v___jp_2980_;
}
else
{
lean_object* v___x_3018_; 
lean_dec(v___x_3017_);
v___x_3018_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__6));
v_idx_2989_ = v_idx_3002_;
v___y_2990_ = v_res_3003_;
v_pos_2991_ = v_pos_3015_;
v_err_2992_ = v___x_3018_;
goto v___jp_2988_;
}
}
else
{
lean_object* v_pos_3019_; lean_object* v_err_3020_; 
v_pos_3019_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_pos_3019_);
v_err_3020_ = lean_ctor_get(v___x_3014_, 1);
lean_inc(v_err_3020_);
lean_dec_ref_known(v___x_3014_, 2);
v_idx_2989_ = v_idx_3002_;
v___y_2990_ = v_res_3003_;
v_pos_2991_ = v_pos_3019_;
v_err_2992_ = v_err_3020_;
goto v___jp_2988_;
}
}
}
}
}
v___jp_3024_:
{
uint8_t v___x_3029_; 
v___x_3029_ = lean_nat_dec_eq(v_idx_3023_, v_idx_3027_);
lean_dec(v_idx_3023_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; 
lean_dec(v_idx_3027_);
lean_dec_ref(v_array_3026_);
lean_del_object(v___x_2978_);
lean_dec(v_snd_2976_);
lean_dec(v_fst_2975_);
lean_del_object(v___x_2973_);
lean_del_object(v___x_2945_);
lean_dec(v_res_2943_);
lean_dec_ref(v_config_2939_);
v___x_3030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3030_, 0, v_pos_3025_);
lean_ctor_set(v___x_3030_, 1, v_err_3028_);
return v___x_3030_;
}
else
{
lean_object* v___x_3031_; 
lean_dec(v_err_3028_);
v___x_3031_ = lean_box(0);
v_pos_3000_ = v_pos_3025_;
v_array_3001_ = v_array_3026_;
v_idx_3002_ = v_idx_3027_;
v_res_3003_ = v___x_3031_;
goto v___jp_2999_;
}
}
}
}
}
else
{
lean_object* v_pos_3061_; lean_object* v_err_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
lean_del_object(v___x_2945_);
lean_dec(v_res_2943_);
lean_dec_ref(v_config_2939_);
v_pos_3061_ = lean_ctor_get(v___x_2969_, 0);
v_err_3062_ = lean_ctor_get(v___x_2969_, 1);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_2969_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_err_3062_);
lean_inc(v_pos_3061_);
lean_dec(v___x_2969_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3067_; 
if (v_isShared_3065_ == 0)
{
v___x_3067_ = v___x_3064_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_pos_3061_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v_err_3062_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
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
lean_object* v_pos_3075_; lean_object* v_err_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec_ref(v_config_2939_);
v_pos_3075_ = lean_ctor_get(v___x_2941_, 0);
v_err_3076_ = lean_ctor_get(v___x_2941_, 1);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_2941_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_err_3076_);
lean_inc(v_pos_3075_);
lean_dec(v___x_2941_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_pos_3075_);
lean_ctor_set(v_reuseFailAlloc_3082_, 1, v_err_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0(void){
_start:
{
uint8_t v___x_3084_; lean_object* v___x_3085_; 
v___x_3084_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_3085_ = lean_uint8_to_nat(v___x_3084_);
return v___x_3085_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1(void){
_start:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3086_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0);
v___x_3087_ = l_Nat_reprFast(v___x_3086_);
return v___x_3087_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2(void){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3088_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1);
v___x_3089_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_3090_ = lean_string_append(v___x_3089_, v___x_3088_);
return v___x_3090_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3(void){
_start:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3091_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_3092_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2);
v___x_3093_ = lean_string_append(v___x_3092_, v___x_3091_);
return v___x_3093_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4(void){
_start:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3094_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3);
v___x_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(lean_object* v_a_3096_){
_start:
{
lean_object* v_array_3097_; lean_object* v_idx_3098_; lean_object* v___x_3099_; uint8_t v___x_3100_; 
v_array_3097_ = lean_ctor_get(v_a_3096_, 0);
v_idx_3098_ = lean_ctor_get(v_a_3096_, 1);
v___x_3099_ = lean_byte_array_size(v_array_3097_);
v___x_3100_ = lean_nat_dec_lt(v_idx_3098_, v___x_3099_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3101_ = lean_box(0);
v___x_3102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3102_, 0, v_a_3096_);
lean_ctor_set(v___x_3102_, 1, v___x_3101_);
return v___x_3102_;
}
else
{
uint8_t v___x_3103_; uint8_t v_got_3104_; uint8_t v___x_3105_; 
v___x_3103_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v_got_3104_ = lean_byte_array_fget(v_array_3097_, v_idx_3098_);
v___x_3105_ = lean_uint8_dec_eq(v_got_3104_, v___x_3103_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3106_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4);
v___x_3107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3107_, 0, v_a_3096_);
lean_ctor_set(v___x_3107_, 1, v___x_3106_);
return v___x_3107_;
}
else
{
lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3118_; 
lean_inc(v_idx_3098_);
lean_inc_ref(v_array_3097_);
v_isSharedCheck_3118_ = !lean_is_exclusive(v_a_3096_);
if (v_isSharedCheck_3118_ == 0)
{
lean_object* v_unused_3119_; lean_object* v_unused_3120_; 
v_unused_3119_ = lean_ctor_get(v_a_3096_, 1);
lean_dec(v_unused_3119_);
v_unused_3120_ = lean_ctor_get(v_a_3096_, 0);
lean_dec(v_unused_3120_);
v___x_3109_ = v_a_3096_;
v_isShared_3110_ = v_isSharedCheck_3118_;
goto v_resetjp_3108_;
}
else
{
lean_dec(v_a_3096_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3118_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3114_; 
v___x_3111_ = lean_unsigned_to_nat(1u);
v___x_3112_ = lean_nat_add(v_idx_3098_, v___x_3111_);
lean_dec(v_idx_3098_);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 1, v___x_3112_);
v___x_3114_ = v___x_3109_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_array_3097_);
lean_ctor_set(v_reuseFailAlloc_3117_, 1, v___x_3112_);
v___x_3114_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = lean_box(3);
v___x_3116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3114_);
lean_ctor_set(v___x_3116_, 1, v___x_3115_);
return v___x_3116_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(lean_object* v_config_3124_, lean_object* v_a_3125_){
_start:
{
lean_object* v_array_3129_; lean_object* v_idx_3130_; lean_object* v___x_3131_; uint8_t v___x_3132_; 
v_array_3129_ = lean_ctor_get(v_a_3125_, 0);
v_idx_3130_ = lean_ctor_get(v_a_3125_, 1);
v___x_3131_ = lean_byte_array_size(v_array_3129_);
v___x_3132_ = lean_nat_dec_lt(v_idx_3130_, v___x_3131_);
if (v___x_3132_ == 0)
{
lean_dec_ref(v_config_3124_);
goto v___jp_3126_;
}
else
{
uint8_t v___x_3133_; uint8_t v___x_3134_; uint8_t v___x_3135_; 
v___x_3133_ = lean_byte_array_fget(v_array_3129_, v_idx_3130_);
v___x_3134_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_3135_ = lean_uint8_dec_eq(v___x_3133_, v___x_3134_);
if (v___x_3135_ == 0)
{
lean_dec_ref(v_config_3124_);
goto v___jp_3126_;
}
else
{
lean_object* v___x_3136_; 
lean_inc_ref(v_a_3125_);
lean_inc_ref(v_config_3124_);
v___x_3136_ = l_Std_Http_URI_Parser_parsePath(v_config_3124_, v___x_3135_, v___x_3135_, v_a_3125_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_pos_3137_; lean_object* v_res_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3183_; 
v_pos_3137_ = lean_ctor_get(v___x_3136_, 0);
v_res_3138_ = lean_ctor_get(v___x_3136_, 1);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3140_ = v___x_3136_;
v_isShared_3141_ = v_isSharedCheck_3183_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_res_3138_);
lean_inc(v_pos_3137_);
lean_dec(v___x_3136_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3183_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v_pos_3143_; lean_object* v_res_3144_; lean_object* v_array_3149_; lean_object* v_idx_3150_; lean_object* v_pos_3152_; lean_object* v_idx_3153_; lean_object* v_err_3154_; lean_object* v___x_3158_; uint8_t v___x_3159_; 
v_array_3149_ = lean_ctor_get(v_pos_3137_, 0);
v_idx_3150_ = lean_ctor_get(v_pos_3137_, 1);
lean_inc(v_idx_3150_);
v___x_3158_ = lean_byte_array_size(v_array_3149_);
v___x_3159_ = lean_nat_dec_lt(v_idx_3150_, v___x_3158_);
if (v___x_3159_ == 0)
{
lean_object* v___x_3160_; 
lean_dec_ref(v_config_3124_);
v___x_3160_ = lean_box(0);
lean_inc(v_idx_3150_);
v_pos_3152_ = v_pos_3137_;
v_idx_3153_ = v_idx_3150_;
v_err_3154_ = v___x_3160_;
goto v___jp_3151_;
}
else
{
uint8_t v___x_3161_; uint8_t v_got_3162_; uint8_t v___x_3163_; 
v___x_3161_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3162_ = lean_byte_array_fget(v_array_3149_, v_idx_3150_);
v___x_3163_ = lean_uint8_dec_eq(v_got_3162_, v___x_3161_);
if (v___x_3163_ == 0)
{
lean_object* v___x_3164_; 
lean_dec_ref(v_config_3124_);
v___x_3164_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3150_);
v_pos_3152_ = v_pos_3137_;
v_idx_3153_ = v_idx_3150_;
v_err_3154_ = v___x_3164_;
goto v___jp_3151_;
}
else
{
lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3180_; 
lean_inc_ref(v_array_3149_);
v_isSharedCheck_3180_ = !lean_is_exclusive(v_pos_3137_);
if (v_isSharedCheck_3180_ == 0)
{
lean_object* v_unused_3181_; lean_object* v_unused_3182_; 
v_unused_3181_ = lean_ctor_get(v_pos_3137_, 1);
lean_dec(v_unused_3181_);
v_unused_3182_ = lean_ctor_get(v_pos_3137_, 0);
lean_dec(v_unused_3182_);
v___x_3166_ = v_pos_3137_;
v_isShared_3167_ = v_isSharedCheck_3180_;
goto v_resetjp_3165_;
}
else
{
lean_dec(v_pos_3137_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3180_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3171_; 
v___x_3168_ = lean_unsigned_to_nat(1u);
v___x_3169_ = lean_nat_add(v_idx_3150_, v___x_3168_);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 1, v___x_3169_);
v___x_3171_ = v___x_3166_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_array_3149_);
lean_ctor_set(v_reuseFailAlloc_3179_, 1, v___x_3169_);
v___x_3171_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
lean_object* v___x_3172_; 
v___x_3172_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3124_, v___x_3171_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v_pos_3173_; lean_object* v_res_3174_; lean_object* v___x_3175_; 
lean_dec(v_idx_3150_);
lean_dec_ref(v_a_3125_);
v_pos_3173_ = lean_ctor_get(v___x_3172_, 0);
lean_inc(v_pos_3173_);
v_res_3174_ = lean_ctor_get(v___x_3172_, 1);
lean_inc(v_res_3174_);
lean_dec_ref_known(v___x_3172_, 2);
v___x_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3175_, 0, v_res_3174_);
v_pos_3143_ = v_pos_3173_;
v_res_3144_ = v___x_3175_;
goto v___jp_3142_;
}
else
{
lean_object* v_pos_3176_; lean_object* v_err_3177_; lean_object* v_idx_3178_; 
v_pos_3176_ = lean_ctor_get(v___x_3172_, 0);
lean_inc(v_pos_3176_);
v_err_3177_ = lean_ctor_get(v___x_3172_, 1);
lean_inc(v_err_3177_);
lean_dec_ref_known(v___x_3172_, 2);
v_idx_3178_ = lean_ctor_get(v_pos_3176_, 1);
lean_inc(v_idx_3178_);
v_pos_3152_ = v_pos_3176_;
v_idx_3153_ = v_idx_3178_;
v_err_3154_ = v_err_3177_;
goto v___jp_3151_;
}
}
}
}
}
v___jp_3142_:
{
lean_object* v___x_3145_; lean_object* v___x_3147_; 
v___x_3145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3145_, 0, v_res_3138_);
lean_ctor_set(v___x_3145_, 1, v_res_3144_);
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 1, v___x_3145_);
lean_ctor_set(v___x_3140_, 0, v_pos_3143_);
v___x_3147_ = v___x_3140_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_pos_3143_);
lean_ctor_set(v_reuseFailAlloc_3148_, 1, v___x_3145_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
v___jp_3151_:
{
uint8_t v___x_3155_; 
v___x_3155_ = lean_nat_dec_eq(v_idx_3150_, v_idx_3153_);
lean_dec(v_idx_3153_);
lean_dec(v_idx_3150_);
if (v___x_3155_ == 0)
{
lean_object* v___x_3156_; 
lean_dec_ref(v_pos_3152_);
lean_del_object(v___x_3140_);
lean_dec(v_res_3138_);
v___x_3156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3156_, 0, v_a_3125_);
lean_ctor_set(v___x_3156_, 1, v_err_3154_);
return v___x_3156_;
}
else
{
lean_object* v___x_3157_; 
lean_dec(v_err_3154_);
lean_dec_ref(v_a_3125_);
v___x_3157_ = lean_box(0);
v_pos_3143_ = v_pos_3152_;
v_res_3144_ = v___x_3157_;
goto v___jp_3142_;
}
}
}
}
else
{
lean_object* v_err_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3191_; 
lean_dec_ref(v_config_3124_);
v_err_3184_ = lean_ctor_get(v___x_3136_, 1);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3191_ == 0)
{
lean_object* v_unused_3192_; 
v_unused_3192_ = lean_ctor_get(v___x_3136_, 0);
lean_dec(v_unused_3192_);
v___x_3186_ = v___x_3136_;
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_err_3184_);
lean_dec(v___x_3136_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3189_; 
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 0, v_a_3125_);
v___x_3189_ = v___x_3186_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_a_3125_);
lean_ctor_set(v_reuseFailAlloc_3190_, 1, v_err_3184_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
}
v___jp_3126_:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3127_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1));
v___x_3128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3128_, 0, v_a_3125_);
lean_ctor_set(v___x_3128_, 1, v___x_3127_);
return v___x_3128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(lean_object* v_config_3193_, lean_object* v_scheme_3194_, lean_object* v_a_3195_){
_start:
{
lean_object* v_array_3196_; lean_object* v_idx_3197_; lean_object* v___x_3198_; uint8_t v___x_3199_; 
v_array_3196_ = lean_ctor_get(v_a_3195_, 0);
v_idx_3197_ = lean_ctor_get(v_a_3195_, 1);
v___x_3198_ = lean_byte_array_size(v_array_3196_);
v___x_3199_ = lean_nat_dec_lt(v_idx_3197_, v___x_3198_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
lean_dec_ref(v_scheme_3194_);
lean_dec_ref(v_config_3193_);
v___x_3200_ = lean_box(0);
v___x_3201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3201_, 0, v_a_3195_);
lean_ctor_set(v___x_3201_, 1, v___x_3200_);
return v___x_3201_;
}
else
{
uint8_t v___x_3202_; uint8_t v_got_3203_; uint8_t v___x_3204_; 
v___x_3202_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v_got_3203_ = lean_byte_array_fget(v_array_3196_, v_idx_3197_);
v___x_3204_ = lean_uint8_dec_eq(v_got_3203_, v___x_3202_);
if (v___x_3204_ == 0)
{
lean_object* v___x_3205_; lean_object* v___x_3206_; 
lean_dec_ref(v_scheme_3194_);
lean_dec_ref(v_config_3193_);
v___x_3205_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
v___x_3206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3206_, 0, v_a_3195_);
lean_ctor_set(v___x_3206_, 1, v___x_3205_);
return v___x_3206_;
}
else
{
lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3281_; 
lean_inc(v_idx_3197_);
lean_inc_ref(v_array_3196_);
v_isSharedCheck_3281_ = !lean_is_exclusive(v_a_3195_);
if (v_isSharedCheck_3281_ == 0)
{
lean_object* v_unused_3282_; lean_object* v_unused_3283_; 
v_unused_3282_ = lean_ctor_get(v_a_3195_, 1);
lean_dec(v_unused_3282_);
v_unused_3283_ = lean_ctor_get(v_a_3195_, 0);
lean_dec(v_unused_3283_);
v___x_3208_ = v_a_3195_;
v_isShared_3209_ = v_isSharedCheck_3281_;
goto v_resetjp_3207_;
}
else
{
lean_dec(v_a_3195_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3281_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3213_; 
v___x_3210_ = lean_unsigned_to_nat(1u);
v___x_3211_ = lean_nat_add(v_idx_3197_, v___x_3210_);
lean_dec(v_idx_3197_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 1, v___x_3211_);
v___x_3213_ = v___x_3208_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_array_3196_);
lean_ctor_set(v_reuseFailAlloc_3280_, 1, v___x_3211_);
v___x_3213_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
lean_object* v___x_3214_; 
lean_inc_ref(v_config_3193_);
v___x_3214_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3193_, v___x_3213_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v_res_3215_; lean_object* v_pos_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3270_; 
v_res_3215_ = lean_ctor_get(v___x_3214_, 1);
v_pos_3216_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3218_ = v___x_3214_;
v_isShared_3219_ = v_isSharedCheck_3270_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_res_3215_);
lean_inc(v_pos_3216_);
lean_dec(v___x_3214_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3270_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v_fst_3220_; lean_object* v_snd_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3269_; 
v_fst_3220_ = lean_ctor_get(v_res_3215_, 0);
v_snd_3221_ = lean_ctor_get(v_res_3215_, 1);
v_isSharedCheck_3269_ = !lean_is_exclusive(v_res_3215_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3223_ = v_res_3215_;
v_isShared_3224_ = v_isSharedCheck_3269_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_snd_3221_);
lean_inc(v_fst_3220_);
lean_dec(v_res_3215_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3269_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v_pos_3226_; lean_object* v_res_3227_; lean_object* v_array_3234_; lean_object* v_idx_3235_; lean_object* v_pos_3237_; lean_object* v_idx_3238_; lean_object* v_err_3239_; lean_object* v___x_3245_; uint8_t v___x_3246_; 
v_array_3234_ = lean_ctor_get(v_pos_3216_, 0);
v_idx_3235_ = lean_ctor_get(v_pos_3216_, 1);
lean_inc(v_idx_3235_);
v___x_3245_ = lean_byte_array_size(v_array_3234_);
v___x_3246_ = lean_nat_dec_lt(v_idx_3235_, v___x_3245_);
if (v___x_3246_ == 0)
{
lean_object* v___x_3247_; 
lean_dec_ref(v_config_3193_);
v___x_3247_ = lean_box(0);
lean_inc(v_idx_3235_);
v_pos_3237_ = v_pos_3216_;
v_idx_3238_ = v_idx_3235_;
v_err_3239_ = v___x_3247_;
goto v___jp_3236_;
}
else
{
uint8_t v___x_3248_; uint8_t v_got_3249_; uint8_t v___x_3250_; 
v___x_3248_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3249_ = lean_byte_array_fget(v_array_3234_, v_idx_3235_);
v___x_3250_ = lean_uint8_dec_eq(v_got_3249_, v___x_3248_);
if (v___x_3250_ == 0)
{
lean_object* v___x_3251_; 
lean_dec_ref(v_config_3193_);
v___x_3251_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3235_);
v_pos_3237_ = v_pos_3216_;
v_idx_3238_ = v_idx_3235_;
v_err_3239_ = v___x_3251_;
goto v___jp_3236_;
}
else
{
lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3266_; 
lean_inc_ref(v_array_3234_);
v_isSharedCheck_3266_ = !lean_is_exclusive(v_pos_3216_);
if (v_isSharedCheck_3266_ == 0)
{
lean_object* v_unused_3267_; lean_object* v_unused_3268_; 
v_unused_3267_ = lean_ctor_get(v_pos_3216_, 1);
lean_dec(v_unused_3267_);
v_unused_3268_ = lean_ctor_get(v_pos_3216_, 0);
lean_dec(v_unused_3268_);
v___x_3253_ = v_pos_3216_;
v_isShared_3254_ = v_isSharedCheck_3266_;
goto v_resetjp_3252_;
}
else
{
lean_dec(v_pos_3216_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3266_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3255_; lean_object* v___x_3257_; 
v___x_3255_ = lean_nat_add(v_idx_3235_, v___x_3210_);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 1, v___x_3255_);
v___x_3257_ = v___x_3253_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_array_3234_);
lean_ctor_set(v_reuseFailAlloc_3265_, 1, v___x_3255_);
v___x_3257_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
lean_object* v___x_3258_; 
v___x_3258_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3193_, v___x_3257_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_pos_3259_; lean_object* v_res_3260_; lean_object* v___x_3261_; 
lean_dec(v_idx_3235_);
lean_del_object(v___x_3223_);
v_pos_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_pos_3259_);
v_res_3260_ = lean_ctor_get(v___x_3258_, 1);
lean_inc(v_res_3260_);
lean_dec_ref_known(v___x_3258_, 2);
v___x_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3261_, 0, v_res_3260_);
v_pos_3226_ = v_pos_3259_;
v_res_3227_ = v___x_3261_;
goto v___jp_3225_;
}
else
{
lean_object* v_pos_3262_; lean_object* v_err_3263_; lean_object* v_idx_3264_; 
v_pos_3262_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_pos_3262_);
v_err_3263_ = lean_ctor_get(v___x_3258_, 1);
lean_inc(v_err_3263_);
lean_dec_ref_known(v___x_3258_, 2);
v_idx_3264_ = lean_ctor_get(v_pos_3262_, 1);
lean_inc(v_idx_3264_);
v_pos_3237_ = v_pos_3262_;
v_idx_3238_ = v_idx_3264_;
v_err_3239_ = v_err_3263_;
goto v___jp_3236_;
}
}
}
}
}
v___jp_3225_:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3232_; 
v___x_3228_ = lean_box(0);
v___x_3229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3229_, 0, v_scheme_3194_);
lean_ctor_set(v___x_3229_, 1, v_fst_3220_);
lean_ctor_set(v___x_3229_, 2, v_snd_3221_);
lean_ctor_set(v___x_3229_, 3, v_res_3227_);
lean_ctor_set(v___x_3229_, 4, v___x_3228_);
v___x_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3229_);
if (v_isShared_3219_ == 0)
{
lean_ctor_set(v___x_3218_, 1, v___x_3230_);
lean_ctor_set(v___x_3218_, 0, v_pos_3226_);
v___x_3232_ = v___x_3218_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_pos_3226_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v___x_3230_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
v___jp_3236_:
{
uint8_t v___x_3240_; 
v___x_3240_ = lean_nat_dec_eq(v_idx_3235_, v_idx_3238_);
lean_dec(v_idx_3238_);
lean_dec(v_idx_3235_);
if (v___x_3240_ == 0)
{
lean_object* v___x_3242_; 
lean_dec(v_snd_3221_);
lean_dec(v_fst_3220_);
lean_del_object(v___x_3218_);
lean_dec_ref(v_scheme_3194_);
if (v_isShared_3224_ == 0)
{
lean_ctor_set_tag(v___x_3223_, 1);
lean_ctor_set(v___x_3223_, 1, v_err_3239_);
lean_ctor_set(v___x_3223_, 0, v_pos_3237_);
v___x_3242_ = v___x_3223_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_pos_3237_);
lean_ctor_set(v_reuseFailAlloc_3243_, 1, v_err_3239_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
else
{
lean_object* v___x_3244_; 
lean_dec(v_err_3239_);
lean_del_object(v___x_3223_);
v___x_3244_ = lean_box(0);
v_pos_3226_ = v_pos_3237_;
v_res_3227_ = v___x_3244_;
goto v___jp_3225_;
}
}
}
}
}
else
{
lean_object* v_pos_3271_; lean_object* v_err_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3279_; 
lean_dec_ref(v_scheme_3194_);
lean_dec_ref(v_config_3193_);
v_pos_3271_ = lean_ctor_get(v___x_3214_, 0);
v_err_3272_ = lean_ctor_get(v___x_3214_, 1);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3274_ = v___x_3214_;
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_err_3272_);
lean_inc(v_pos_3271_);
lean_dec(v___x_3214_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3277_; 
if (v_isShared_3275_ == 0)
{
v___x_3277_ = v___x_3274_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_pos_3271_);
lean_ctor_set(v_reuseFailAlloc_3278_, 1, v_err_3272_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(lean_object* v_config_3292_, lean_object* v_a_3293_){
_start:
{
lean_object* v___x_3297_; 
lean_inc_ref(v_a_3293_);
v___x_3297_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3292_, v_a_3293_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_pos_3298_; lean_object* v_res_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3395_; 
v_pos_3298_ = lean_ctor_get(v___x_3297_, 0);
v_res_3299_ = lean_ctor_get(v___x_3297_, 1);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3301_ = v___x_3297_;
v_isShared_3302_ = v_isSharedCheck_3395_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_res_3299_);
lean_inc(v_pos_3298_);
lean_dec(v___x_3297_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3395_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v_pos_3306_; lean_object* v_res_3307_; lean_object* v_idx_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v_pos_3318_; lean_object* v_idx_3319_; lean_object* v_err_3320_; lean_object* v___x_3389_; uint8_t v___x_3390_; 
v___x_3389_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2));
v___x_3390_ = lean_string_dec_eq(v_res_3299_, v___x_3389_);
if (v___x_3390_ == 0)
{
lean_object* v___x_3391_; uint8_t v___x_3392_; 
v___x_3391_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3));
v___x_3392_ = lean_string_dec_eq(v_res_3299_, v___x_3391_);
if (v___x_3392_ == 0)
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
lean_del_object(v___x_3301_);
lean_dec(v_res_3299_);
lean_dec(v_pos_3298_);
lean_dec_ref(v_config_3292_);
v___x_3393_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5));
v___x_3394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3394_, 0, v_a_3293_);
lean_ctor_set(v___x_3394_, 1, v___x_3393_);
return v___x_3394_;
}
else
{
goto v___jp_3324_;
}
}
else
{
goto v___jp_3324_;
}
v___jp_3303_:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3312_; 
v___x_3308_ = lean_box(0);
v___x_3309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3309_, 0, v_res_3299_);
lean_ctor_set(v___x_3309_, 1, v___y_3304_);
lean_ctor_set(v___x_3309_, 2, v___y_3305_);
lean_ctor_set(v___x_3309_, 3, v_res_3307_);
lean_ctor_set(v___x_3309_, 4, v___x_3308_);
v___x_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3309_);
if (v_isShared_3302_ == 0)
{
lean_ctor_set(v___x_3301_, 1, v___x_3310_);
lean_ctor_set(v___x_3301_, 0, v_pos_3306_);
v___x_3312_ = v___x_3301_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_pos_3306_);
lean_ctor_set(v_reuseFailAlloc_3313_, 1, v___x_3310_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
v___jp_3314_:
{
uint8_t v___x_3321_; 
v___x_3321_ = lean_nat_dec_eq(v_idx_3315_, v_idx_3319_);
lean_dec(v_idx_3319_);
lean_dec(v_idx_3315_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3322_; 
lean_dec_ref(v_pos_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v___y_3316_);
lean_del_object(v___x_3301_);
lean_dec(v_res_3299_);
v___x_3322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3322_, 0, v_a_3293_);
lean_ctor_set(v___x_3322_, 1, v_err_3320_);
return v___x_3322_;
}
else
{
lean_object* v___x_3323_; 
lean_dec(v_err_3320_);
lean_dec_ref(v_a_3293_);
v___x_3323_ = lean_box(0);
v___y_3304_ = v___y_3316_;
v___y_3305_ = v___y_3317_;
v_pos_3306_ = v_pos_3318_;
v_res_3307_ = v___x_3323_;
goto v___jp_3303_;
}
}
v___jp_3324_:
{
lean_object* v_array_3325_; lean_object* v_idx_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3388_; 
v_array_3325_ = lean_ctor_get(v_pos_3298_, 0);
v_idx_3326_ = lean_ctor_get(v_pos_3298_, 1);
v_isSharedCheck_3388_ = !lean_is_exclusive(v_pos_3298_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3328_ = v_pos_3298_;
v_isShared_3329_ = v_isSharedCheck_3388_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_idx_3326_);
lean_inc(v_array_3325_);
lean_dec(v_pos_3298_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3388_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3330_; uint8_t v___x_3331_; 
v___x_3330_ = lean_byte_array_size(v_array_3325_);
v___x_3331_ = lean_nat_dec_lt(v_idx_3326_, v___x_3330_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3332_; lean_object* v___x_3333_; 
lean_del_object(v___x_3328_);
lean_dec(v_idx_3326_);
lean_dec_ref(v_array_3325_);
lean_del_object(v___x_3301_);
lean_dec(v_res_3299_);
lean_dec_ref(v_config_3292_);
v___x_3332_ = lean_box(0);
v___x_3333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3333_, 0, v_a_3293_);
lean_ctor_set(v___x_3333_, 1, v___x_3332_);
return v___x_3333_;
}
else
{
uint8_t v___x_3334_; uint8_t v_got_3335_; uint8_t v___x_3336_; 
v___x_3334_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v_got_3335_ = lean_byte_array_fget(v_array_3325_, v_idx_3326_);
v___x_3336_ = lean_uint8_dec_eq(v_got_3335_, v___x_3334_);
if (v___x_3336_ == 0)
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
lean_del_object(v___x_3328_);
lean_dec(v_idx_3326_);
lean_dec_ref(v_array_3325_);
lean_del_object(v___x_3301_);
lean_dec(v_res_3299_);
lean_dec_ref(v_config_3292_);
v___x_3337_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
v___x_3338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3338_, 0, v_a_3293_);
lean_ctor_set(v___x_3338_, 1, v___x_3337_);
return v___x_3338_;
}
else
{
lean_object* v___x_3339_; lean_object* v___x_3340_; uint8_t v___x_3341_; 
v___x_3339_ = lean_unsigned_to_nat(1u);
v___x_3340_ = lean_nat_add(v_idx_3326_, v___x_3339_);
lean_dec(v_idx_3326_);
v___x_3341_ = lean_nat_dec_lt(v___x_3340_, v___x_3330_);
if (v___x_3341_ == 0)
{
lean_dec(v___x_3340_);
lean_del_object(v___x_3328_);
lean_dec_ref(v_array_3325_);
lean_del_object(v___x_3301_);
lean_dec(v_res_3299_);
lean_dec_ref(v_config_3292_);
goto v___jp_3294_;
}
else
{
uint8_t v___x_3342_; uint8_t v___x_3343_; uint8_t v___x_3344_; 
v___x_3342_ = lean_byte_array_fget(v_array_3325_, v___x_3340_);
v___x_3343_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_3344_ = lean_uint8_dec_eq(v___x_3342_, v___x_3343_);
if (v___x_3344_ == 0)
{
lean_dec(v___x_3340_);
lean_del_object(v___x_3328_);
lean_dec_ref(v_array_3325_);
lean_del_object(v___x_3301_);
lean_dec(v_res_3299_);
lean_dec_ref(v_config_3292_);
goto v___jp_3294_;
}
else
{
lean_object* v___x_3346_; 
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 1, v___x_3340_);
v___x_3346_ = v___x_3328_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_array_3325_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v___x_3340_);
v___x_3346_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
lean_object* v___x_3347_; 
lean_inc_ref(v_config_3292_);
v___x_3347_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3292_, v___x_3346_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_res_3348_; lean_object* v_pos_3349_; lean_object* v_fst_3350_; lean_object* v_snd_3351_; lean_object* v_array_3352_; lean_object* v_idx_3353_; lean_object* v___x_3354_; uint8_t v___x_3355_; 
v_res_3348_ = lean_ctor_get(v___x_3347_, 1);
lean_inc(v_res_3348_);
v_pos_3349_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_pos_3349_);
lean_dec_ref_known(v___x_3347_, 2);
v_fst_3350_ = lean_ctor_get(v_res_3348_, 0);
lean_inc(v_fst_3350_);
v_snd_3351_ = lean_ctor_get(v_res_3348_, 1);
lean_inc(v_snd_3351_);
lean_dec(v_res_3348_);
v_array_3352_ = lean_ctor_get(v_pos_3349_, 0);
v_idx_3353_ = lean_ctor_get(v_pos_3349_, 1);
lean_inc(v_idx_3353_);
v___x_3354_ = lean_byte_array_size(v_array_3352_);
v___x_3355_ = lean_nat_dec_lt(v_idx_3353_, v___x_3354_);
if (v___x_3355_ == 0)
{
lean_object* v___x_3356_; 
lean_dec_ref(v_config_3292_);
v___x_3356_ = lean_box(0);
lean_inc(v_idx_3353_);
v_idx_3315_ = v_idx_3353_;
v___y_3316_ = v_fst_3350_;
v___y_3317_ = v_snd_3351_;
v_pos_3318_ = v_pos_3349_;
v_idx_3319_ = v_idx_3353_;
v_err_3320_ = v___x_3356_;
goto v___jp_3314_;
}
else
{
uint8_t v___x_3357_; uint8_t v_got_3358_; uint8_t v___x_3359_; 
v___x_3357_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3358_ = lean_byte_array_fget(v_array_3352_, v_idx_3353_);
v___x_3359_ = lean_uint8_dec_eq(v_got_3358_, v___x_3357_);
if (v___x_3359_ == 0)
{
lean_object* v___x_3360_; 
lean_dec_ref(v_config_3292_);
v___x_3360_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3353_);
v_idx_3315_ = v_idx_3353_;
v___y_3316_ = v_fst_3350_;
v___y_3317_ = v_snd_3351_;
v_pos_3318_ = v_pos_3349_;
v_idx_3319_ = v_idx_3353_;
v_err_3320_ = v___x_3360_;
goto v___jp_3314_;
}
else
{
lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3375_; 
lean_inc_ref(v_array_3352_);
v_isSharedCheck_3375_ = !lean_is_exclusive(v_pos_3349_);
if (v_isSharedCheck_3375_ == 0)
{
lean_object* v_unused_3376_; lean_object* v_unused_3377_; 
v_unused_3376_ = lean_ctor_get(v_pos_3349_, 1);
lean_dec(v_unused_3376_);
v_unused_3377_ = lean_ctor_get(v_pos_3349_, 0);
lean_dec(v_unused_3377_);
v___x_3362_ = v_pos_3349_;
v_isShared_3363_ = v_isSharedCheck_3375_;
goto v_resetjp_3361_;
}
else
{
lean_dec(v_pos_3349_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3375_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3364_; lean_object* v___x_3366_; 
v___x_3364_ = lean_nat_add(v_idx_3353_, v___x_3339_);
if (v_isShared_3363_ == 0)
{
lean_ctor_set(v___x_3362_, 1, v___x_3364_);
v___x_3366_ = v___x_3362_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_array_3352_);
lean_ctor_set(v_reuseFailAlloc_3374_, 1, v___x_3364_);
v___x_3366_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
lean_object* v___x_3367_; 
v___x_3367_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3292_, v___x_3366_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_pos_3368_; lean_object* v_res_3369_; lean_object* v___x_3370_; 
lean_dec(v_idx_3353_);
lean_dec_ref(v_a_3293_);
v_pos_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_pos_3368_);
v_res_3369_ = lean_ctor_get(v___x_3367_, 1);
lean_inc(v_res_3369_);
lean_dec_ref_known(v___x_3367_, 2);
v___x_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3370_, 0, v_res_3369_);
v___y_3304_ = v_fst_3350_;
v___y_3305_ = v_snd_3351_;
v_pos_3306_ = v_pos_3368_;
v_res_3307_ = v___x_3370_;
goto v___jp_3303_;
}
else
{
lean_object* v_pos_3371_; lean_object* v_err_3372_; lean_object* v_idx_3373_; 
v_pos_3371_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_pos_3371_);
v_err_3372_ = lean_ctor_get(v___x_3367_, 1);
lean_inc(v_err_3372_);
lean_dec_ref_known(v___x_3367_, 2);
v_idx_3373_ = lean_ctor_get(v_pos_3371_, 1);
lean_inc(v_idx_3373_);
v_idx_3315_ = v_idx_3353_;
v___y_3316_ = v_fst_3350_;
v___y_3317_ = v_snd_3351_;
v_pos_3318_ = v_pos_3371_;
v_idx_3319_ = v_idx_3373_;
v_err_3320_ = v_err_3372_;
goto v___jp_3314_;
}
}
}
}
}
}
else
{
lean_object* v_err_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3385_; 
lean_del_object(v___x_3301_);
lean_dec(v_res_3299_);
lean_dec_ref(v_config_3292_);
v_err_3378_ = lean_ctor_get(v___x_3347_, 1);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3385_ == 0)
{
lean_object* v_unused_3386_; 
v_unused_3386_ = lean_ctor_get(v___x_3347_, 0);
lean_dec(v_unused_3386_);
v___x_3380_ = v___x_3347_;
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_err_3378_);
lean_dec(v___x_3347_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3383_; 
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 0, v_a_3293_);
v___x_3383_ = v___x_3380_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_a_3293_);
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
lean_object* v_err_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
lean_dec_ref(v_config_3292_);
v_err_3396_ = lean_ctor_get(v___x_3297_, 1);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3403_ == 0)
{
lean_object* v_unused_3404_; 
v_unused_3404_ = lean_ctor_get(v___x_3297_, 0);
lean_dec(v_unused_3404_);
v___x_3398_ = v___x_3297_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_err_3396_);
lean_dec(v___x_3297_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 0, v_a_3293_);
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3293_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v_err_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
v___jp_3294_:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1));
v___x_3296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3296_, 0, v_a_3293_);
lean_ctor_set(v___x_3296_, 1, v___x_3295_);
return v___x_3296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(lean_object* v_config_3405_, lean_object* v_a_3406_){
_start:
{
lean_object* v___x_3407_; 
lean_inc_ref(v_a_3406_);
v___x_3407_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3405_, v_a_3406_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_pos_3408_; lean_object* v_res_3409_; lean_object* v___x_3410_; 
v_pos_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_pos_3408_);
v_res_3409_ = lean_ctor_get(v___x_3407_, 1);
lean_inc(v_res_3409_);
lean_dec_ref_known(v___x_3407_, 2);
v___x_3410_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(v_config_3405_, v_res_3409_, v_pos_3408_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_dec_ref(v_a_3406_);
return v___x_3410_;
}
else
{
lean_object* v_err_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
v_err_3411_ = lean_ctor_get(v___x_3410_, 1);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3418_ == 0)
{
lean_object* v_unused_3419_; 
v_unused_3419_ = lean_ctor_get(v___x_3410_, 0);
lean_dec(v_unused_3419_);
v___x_3413_ = v___x_3410_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_err_3411_);
lean_dec(v___x_3410_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 0, v_a_3406_);
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3406_);
lean_ctor_set(v_reuseFailAlloc_3417_, 1, v_err_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
else
{
lean_object* v_err_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3427_; 
lean_dec_ref(v_config_3405_);
v_err_3420_ = lean_ctor_get(v___x_3407_, 1);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3427_ == 0)
{
lean_object* v_unused_3428_; 
v_unused_3428_ = lean_ctor_get(v___x_3407_, 0);
lean_dec(v_unused_3428_);
v___x_3422_ = v___x_3407_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_err_3420_);
lean_dec(v___x_3407_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 0, v_a_3406_);
v___x_3425_ = v___x_3422_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3406_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(lean_object* v_config_3429_, lean_object* v_a_3430_){
_start:
{
lean_object* v___x_3431_; 
lean_inc_ref(v_a_3430_);
v___x_3431_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3429_, v_a_3430_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_pos_3432_; lean_object* v_res_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3485_; 
v_pos_3432_ = lean_ctor_get(v___x_3431_, 0);
v_res_3433_ = lean_ctor_get(v___x_3431_, 1);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3435_ = v___x_3431_;
v_isShared_3436_ = v_isSharedCheck_3485_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_res_3433_);
lean_inc(v_pos_3432_);
lean_dec(v___x_3431_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3485_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v_array_3437_; lean_object* v_idx_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3484_; 
v_array_3437_ = lean_ctor_get(v_pos_3432_, 0);
v_idx_3438_ = lean_ctor_get(v_pos_3432_, 1);
v_isSharedCheck_3484_ = !lean_is_exclusive(v_pos_3432_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3440_ = v_pos_3432_;
v_isShared_3441_ = v_isSharedCheck_3484_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_idx_3438_);
lean_inc(v_array_3437_);
lean_dec(v_pos_3432_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3484_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3442_; uint8_t v___x_3443_; 
v___x_3442_ = lean_byte_array_size(v_array_3437_);
v___x_3443_ = lean_nat_dec_lt(v_idx_3438_, v___x_3442_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3444_; lean_object* v___x_3446_; 
lean_del_object(v___x_3440_);
lean_dec(v_idx_3438_);
lean_dec_ref(v_array_3437_);
lean_dec(v_res_3433_);
v___x_3444_ = lean_box(0);
if (v_isShared_3436_ == 0)
{
lean_ctor_set_tag(v___x_3435_, 1);
lean_ctor_set(v___x_3435_, 1, v___x_3444_);
lean_ctor_set(v___x_3435_, 0, v_a_3430_);
v___x_3446_ = v___x_3435_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_a_3430_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v___x_3444_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
else
{
uint8_t v___x_3448_; uint8_t v_got_3449_; uint8_t v___x_3450_; 
v___x_3448_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v_got_3449_ = lean_byte_array_fget(v_array_3437_, v_idx_3438_);
v___x_3450_ = lean_uint8_dec_eq(v_got_3449_, v___x_3448_);
if (v___x_3450_ == 0)
{
lean_object* v___x_3451_; lean_object* v___x_3453_; 
lean_del_object(v___x_3440_);
lean_dec(v_idx_3438_);
lean_dec_ref(v_array_3437_);
lean_dec(v_res_3433_);
v___x_3451_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
if (v_isShared_3436_ == 0)
{
lean_ctor_set_tag(v___x_3435_, 1);
lean_ctor_set(v___x_3435_, 1, v___x_3451_);
lean_ctor_set(v___x_3435_, 0, v_a_3430_);
v___x_3453_ = v___x_3435_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3430_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v___x_3451_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
else
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3458_; 
lean_del_object(v___x_3435_);
v___x_3455_ = lean_unsigned_to_nat(1u);
v___x_3456_ = lean_nat_add(v_idx_3438_, v___x_3455_);
lean_dec(v_idx_3438_);
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 1, v___x_3456_);
v___x_3458_ = v___x_3440_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_array_3437_);
lean_ctor_set(v_reuseFailAlloc_3483_, 1, v___x_3456_);
v___x_3458_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
lean_object* v___x_3459_; 
v___x_3459_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_3458_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_pos_3460_; lean_object* v_res_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3473_; 
lean_dec_ref(v_a_3430_);
v_pos_3460_ = lean_ctor_get(v___x_3459_, 0);
v_res_3461_ = lean_ctor_get(v___x_3459_, 1);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3463_ = v___x_3459_;
v_isShared_3464_ = v_isSharedCheck_3473_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_res_3461_);
lean_inc(v_pos_3460_);
lean_dec(v___x_3459_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3473_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; uint16_t v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3471_; 
v___x_3465_ = lean_box(0);
v___x_3466_ = lean_alloc_ctor(2, 0, 2);
v___x_3467_ = lean_unbox(v_res_3461_);
lean_dec(v_res_3461_);
lean_ctor_set_uint16(v___x_3466_, 0, v___x_3467_);
v___x_3468_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3465_);
lean_ctor_set(v___x_3468_, 1, v_res_3433_);
lean_ctor_set(v___x_3468_, 2, v___x_3466_);
v___x_3469_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 1, v___x_3469_);
v___x_3471_ = v___x_3463_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_pos_3460_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v___x_3469_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
else
{
lean_object* v_err_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
lean_dec(v_res_3433_);
v_err_3474_ = lean_ctor_get(v___x_3459_, 1);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3481_ == 0)
{
lean_object* v_unused_3482_; 
v_unused_3482_ = lean_ctor_get(v___x_3459_, 0);
lean_dec(v_unused_3482_);
v___x_3476_ = v___x_3459_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_err_3474_);
lean_dec(v___x_3459_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 0, v_a_3430_);
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3430_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v_err_3474_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
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
lean_object* v_err_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3493_; 
v_err_3486_ = lean_ctor_get(v___x_3431_, 1);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3493_ == 0)
{
lean_object* v_unused_3494_; 
v_unused_3494_ = lean_ctor_get(v___x_3431_, 0);
lean_dec(v_unused_3494_);
v___x_3488_ = v___x_3431_;
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_err_3486_);
lean_dec(v___x_3431_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 0, v_a_3430_);
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3430_);
lean_ctor_set(v_reuseFailAlloc_3492_, 1, v_err_3486_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority___boxed(lean_object* v_config_3495_, lean_object* v_a_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3495_, v_a_3496_);
lean_dec_ref(v_config_3495_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object* v_config_3498_, lean_object* v_a_3499_){
_start:
{
lean_object* v___x_3500_; 
lean_inc_ref(v_a_3499_);
v___x_3500_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(v_a_3499_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_dec_ref(v_a_3499_);
lean_dec_ref(v_config_3498_);
return v___x_3500_;
}
else
{
lean_object* v_pos_3501_; lean_object* v_idx_3502_; lean_object* v_idx_3503_; uint8_t v___x_3504_; 
v_pos_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_pos_3501_);
v_idx_3502_ = lean_ctor_get(v_a_3499_, 1);
lean_inc(v_idx_3502_);
lean_dec_ref(v_a_3499_);
v_idx_3503_ = lean_ctor_get(v_pos_3501_, 1);
lean_inc(v_idx_3503_);
v___x_3504_ = lean_nat_dec_eq(v_idx_3502_, v_idx_3503_);
lean_dec(v_idx_3502_);
if (v___x_3504_ == 0)
{
lean_dec(v_idx_3503_);
lean_dec(v_pos_3501_);
lean_dec_ref(v_config_3498_);
return v___x_3500_;
}
else
{
lean_object* v___x_3505_; 
lean_dec_ref_known(v___x_3500_, 2);
lean_inc_ref(v_config_3498_);
v___x_3505_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(v_config_3498_, v_pos_3501_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_dec(v_idx_3503_);
lean_dec_ref(v_config_3498_);
return v___x_3505_;
}
else
{
lean_object* v_pos_3506_; lean_object* v_idx_3507_; uint8_t v___x_3508_; 
v_pos_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_pos_3506_);
v_idx_3507_ = lean_ctor_get(v_pos_3506_, 1);
lean_inc(v_idx_3507_);
v___x_3508_ = lean_nat_dec_eq(v_idx_3503_, v_idx_3507_);
lean_dec(v_idx_3503_);
if (v___x_3508_ == 0)
{
lean_dec(v_idx_3507_);
lean_dec(v_pos_3506_);
lean_dec_ref(v_config_3498_);
return v___x_3505_;
}
else
{
lean_object* v___x_3509_; 
lean_dec_ref_known(v___x_3505_, 2);
lean_inc_ref(v_config_3498_);
v___x_3509_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(v_config_3498_, v_pos_3506_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_dec(v_idx_3507_);
lean_dec_ref(v_config_3498_);
return v___x_3509_;
}
else
{
lean_object* v_pos_3510_; lean_object* v_idx_3511_; uint8_t v___x_3512_; 
v_pos_3510_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_pos_3510_);
v_idx_3511_ = lean_ctor_get(v_pos_3510_, 1);
lean_inc(v_idx_3511_);
v___x_3512_ = lean_nat_dec_eq(v_idx_3507_, v_idx_3511_);
lean_dec(v_idx_3507_);
if (v___x_3512_ == 0)
{
lean_dec(v_idx_3511_);
lean_dec(v_pos_3510_);
lean_dec_ref(v_config_3498_);
return v___x_3509_;
}
else
{
lean_object* v___x_3513_; 
lean_dec_ref_known(v___x_3509_, 2);
v___x_3513_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3498_, v_pos_3510_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_dec(v_idx_3511_);
lean_dec_ref(v_config_3498_);
return v___x_3513_;
}
else
{
lean_object* v_pos_3514_; lean_object* v_idx_3515_; uint8_t v___x_3516_; 
v_pos_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_pos_3514_);
v_idx_3515_ = lean_ctor_get(v_pos_3514_, 1);
v___x_3516_ = lean_nat_dec_eq(v_idx_3511_, v_idx_3515_);
lean_dec(v_idx_3511_);
if (v___x_3516_ == 0)
{
lean_dec(v_pos_3514_);
lean_dec_ref(v_config_3498_);
return v___x_3513_;
}
else
{
lean_object* v___x_3517_; 
lean_dec_ref_known(v___x_3513_, 2);
v___x_3517_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(v_config_3498_, v_pos_3514_);
return v___x_3517_;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(lean_object* v_config_3521_, lean_object* v_a_3522_){
_start:
{
lean_object* v___x_3523_; 
v___x_3523_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_3521_, v_a_3522_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_pos_3524_; lean_object* v_res_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3538_; 
v_pos_3524_ = lean_ctor_get(v___x_3523_, 0);
v_res_3525_ = lean_ctor_get(v___x_3523_, 1);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3527_ = v___x_3523_;
v_isShared_3528_ = v_isSharedCheck_3538_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_res_3525_);
lean_inc(v_pos_3524_);
lean_dec(v___x_3523_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3538_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3529_; 
v___x_3529_ = l_Std_Http_URI_EncodedFragment_decode(v_res_3525_);
lean_dec(v_res_3525_);
if (lean_obj_tag(v___x_3529_) == 1)
{
lean_object* v_val_3530_; lean_object* v___x_3532_; 
v_val_3530_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_val_3530_);
lean_dec_ref_known(v___x_3529_, 1);
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 1, v_val_3530_);
v___x_3532_ = v___x_3527_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_pos_3524_);
lean_ctor_set(v_reuseFailAlloc_3533_, 1, v_val_3530_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
else
{
lean_object* v___x_3534_; lean_object* v___x_3536_; 
lean_dec(v___x_3529_);
v___x_3534_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___closed__1));
if (v_isShared_3528_ == 0)
{
lean_ctor_set_tag(v___x_3527_, 1);
lean_ctor_set(v___x_3527_, 1, v___x_3534_);
v___x_3536_ = v___x_3527_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_pos_3524_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v___x_3534_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
else
{
lean_object* v_pos_3539_; lean_object* v_err_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
v_pos_3539_ = lean_ctor_get(v___x_3523_, 0);
v_err_3540_ = lean_ctor_get(v___x_3523_, 1);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3523_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_err_3540_);
lean_inc(v_pos_3539_);
lean_dec(v___x_3523_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_pos_3539_);
lean_ctor_set(v_reuseFailAlloc_3546_, 1, v_err_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___boxed(lean_object* v_config_3548_, lean_object* v_a_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3548_, v_a_3549_);
lean_dec_ref(v_config_3548_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_uri(lean_object* v_config_3551_, lean_object* v_a_3552_){
_start:
{
lean_object* v___x_3553_; 
lean_inc_ref(v_a_3552_);
v___x_3553_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3551_, v_a_3552_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_pos_3554_; lean_object* v_res_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3684_; 
v_pos_3554_ = lean_ctor_get(v___x_3553_, 0);
v_res_3555_ = lean_ctor_get(v___x_3553_, 1);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3557_ = v___x_3553_;
v_isShared_3558_ = v_isSharedCheck_3684_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_res_3555_);
lean_inc(v_pos_3554_);
lean_dec(v___x_3553_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3684_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v_array_3559_; lean_object* v_idx_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3683_; 
v_array_3559_ = lean_ctor_get(v_pos_3554_, 0);
v_idx_3560_ = lean_ctor_get(v_pos_3554_, 1);
v_isSharedCheck_3683_ = !lean_is_exclusive(v_pos_3554_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3562_ = v_pos_3554_;
v_isShared_3563_ = v_isSharedCheck_3683_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_idx_3560_);
lean_inc(v_array_3559_);
lean_dec(v_pos_3554_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3683_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3564_; uint8_t v___x_3565_; 
v___x_3564_ = lean_byte_array_size(v_array_3559_);
v___x_3565_ = lean_nat_dec_lt(v_idx_3560_, v___x_3564_);
if (v___x_3565_ == 0)
{
lean_object* v___x_3566_; lean_object* v___x_3568_; 
lean_del_object(v___x_3562_);
lean_dec(v_idx_3560_);
lean_dec_ref(v_array_3559_);
lean_dec(v_res_3555_);
lean_dec_ref(v_config_3551_);
v___x_3566_ = lean_box(0);
if (v_isShared_3558_ == 0)
{
lean_ctor_set_tag(v___x_3557_, 1);
lean_ctor_set(v___x_3557_, 1, v___x_3566_);
lean_ctor_set(v___x_3557_, 0, v_a_3552_);
v___x_3568_ = v___x_3557_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3552_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v___x_3566_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
else
{
uint8_t v___x_3570_; uint8_t v_got_3571_; uint8_t v___x_3572_; 
v___x_3570_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v_got_3571_ = lean_byte_array_fget(v_array_3559_, v_idx_3560_);
v___x_3572_ = lean_uint8_dec_eq(v_got_3571_, v___x_3570_);
if (v___x_3572_ == 0)
{
lean_object* v___x_3573_; lean_object* v___x_3575_; 
lean_del_object(v___x_3562_);
lean_dec(v_idx_3560_);
lean_dec_ref(v_array_3559_);
lean_dec(v_res_3555_);
lean_dec_ref(v_config_3551_);
v___x_3573_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
if (v_isShared_3558_ == 0)
{
lean_ctor_set_tag(v___x_3557_, 1);
lean_ctor_set(v___x_3557_, 1, v___x_3573_);
lean_ctor_set(v___x_3557_, 0, v_a_3552_);
v___x_3575_ = v___x_3557_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3552_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v___x_3573_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
else
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3580_; 
v___x_3577_ = lean_unsigned_to_nat(1u);
v___x_3578_ = lean_nat_add(v_idx_3560_, v___x_3577_);
lean_dec(v_idx_3560_);
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 1, v___x_3578_);
v___x_3580_ = v___x_3562_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_array_3559_);
lean_ctor_set(v_reuseFailAlloc_3682_, 1, v___x_3578_);
v___x_3580_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
lean_object* v___x_3581_; 
lean_inc_ref(v_config_3551_);
v___x_3581_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3551_, v___x_3580_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_res_3582_; lean_object* v_pos_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3672_; 
v_res_3582_ = lean_ctor_get(v___x_3581_, 1);
v_pos_3583_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3585_ = v___x_3581_;
v_isShared_3586_ = v_isSharedCheck_3672_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_res_3582_);
lean_inc(v_pos_3583_);
lean_dec(v___x_3581_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3672_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v_fst_3587_; lean_object* v_snd_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3671_; 
v_fst_3587_ = lean_ctor_get(v_res_3582_, 0);
v_snd_3588_ = lean_ctor_get(v_res_3582_, 1);
v_isSharedCheck_3671_ = !lean_is_exclusive(v_res_3582_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3590_ = v_res_3582_;
v_isShared_3591_ = v_isSharedCheck_3671_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_snd_3588_);
lean_inc(v_fst_3587_);
lean_dec(v_res_3582_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3671_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___y_3593_; lean_object* v_pos_3594_; lean_object* v_res_3595_; lean_object* v_idx_3602_; lean_object* v___y_3603_; lean_object* v_pos_3604_; lean_object* v_err_3605_; lean_object* v_pos_3613_; lean_object* v_array_3614_; lean_object* v_idx_3615_; lean_object* v_res_3616_; lean_object* v_array_3634_; lean_object* v_idx_3635_; lean_object* v_pos_3637_; lean_object* v_array_3638_; lean_object* v_idx_3639_; lean_object* v_err_3640_; lean_object* v___x_3644_; uint8_t v___x_3645_; 
v_array_3634_ = lean_ctor_get(v_pos_3583_, 0);
lean_inc_ref(v_array_3634_);
v_idx_3635_ = lean_ctor_get(v_pos_3583_, 1);
lean_inc(v_idx_3635_);
v___x_3644_ = lean_byte_array_size(v_array_3634_);
v___x_3645_ = lean_nat_dec_lt(v_idx_3635_, v___x_3644_);
if (v___x_3645_ == 0)
{
lean_object* v___x_3646_; 
v___x_3646_ = lean_box(0);
lean_inc(v_idx_3635_);
v_pos_3637_ = v_pos_3583_;
v_array_3638_ = v_array_3634_;
v_idx_3639_ = v_idx_3635_;
v_err_3640_ = v___x_3646_;
goto v___jp_3636_;
}
else
{
uint8_t v___x_3647_; uint8_t v_got_3648_; uint8_t v___x_3649_; 
v___x_3647_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3648_ = lean_byte_array_fget(v_array_3634_, v_idx_3635_);
v___x_3649_ = lean_uint8_dec_eq(v_got_3648_, v___x_3647_);
if (v___x_3649_ == 0)
{
lean_object* v___x_3650_; 
v___x_3650_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3635_);
v_pos_3637_ = v_pos_3583_;
v_array_3638_ = v_array_3634_;
v_idx_3639_ = v_idx_3635_;
v_err_3640_ = v___x_3650_;
goto v___jp_3636_;
}
else
{
lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3668_; 
v_isSharedCheck_3668_ = !lean_is_exclusive(v_pos_3583_);
if (v_isSharedCheck_3668_ == 0)
{
lean_object* v_unused_3669_; lean_object* v_unused_3670_; 
v_unused_3669_ = lean_ctor_get(v_pos_3583_, 1);
lean_dec(v_unused_3669_);
v_unused_3670_ = lean_ctor_get(v_pos_3583_, 0);
lean_dec(v_unused_3670_);
v___x_3652_ = v_pos_3583_;
v_isShared_3653_ = v_isSharedCheck_3668_;
goto v_resetjp_3651_;
}
else
{
lean_dec(v_pos_3583_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3668_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3654_; lean_object* v___x_3656_; 
v___x_3654_ = lean_nat_add(v_idx_3635_, v___x_3577_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 1, v___x_3654_);
v___x_3656_ = v___x_3652_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_array_3634_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v___x_3654_);
v___x_3656_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
lean_object* v___x_3657_; 
lean_inc_ref(v_config_3551_);
v___x_3657_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3551_, v___x_3656_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v_pos_3658_; lean_object* v_res_3659_; lean_object* v_array_3660_; lean_object* v_idx_3661_; lean_object* v___x_3662_; 
lean_dec(v_idx_3635_);
v_pos_3658_ = lean_ctor_get(v___x_3657_, 0);
lean_inc(v_pos_3658_);
v_res_3659_ = lean_ctor_get(v___x_3657_, 1);
lean_inc(v_res_3659_);
lean_dec_ref_known(v___x_3657_, 2);
v_array_3660_ = lean_ctor_get(v_pos_3658_, 0);
lean_inc_ref(v_array_3660_);
v_idx_3661_ = lean_ctor_get(v_pos_3658_, 1);
lean_inc(v_idx_3661_);
v___x_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3662_, 0, v_res_3659_);
v_pos_3613_ = v_pos_3658_;
v_array_3614_ = v_array_3660_;
v_idx_3615_ = v_idx_3661_;
v_res_3616_ = v___x_3662_;
goto v___jp_3612_;
}
else
{
lean_object* v_pos_3663_; lean_object* v_err_3664_; lean_object* v_array_3665_; lean_object* v_idx_3666_; 
v_pos_3663_ = lean_ctor_get(v___x_3657_, 0);
lean_inc(v_pos_3663_);
v_err_3664_ = lean_ctor_get(v___x_3657_, 1);
lean_inc(v_err_3664_);
lean_dec_ref_known(v___x_3657_, 2);
v_array_3665_ = lean_ctor_get(v_pos_3663_, 0);
lean_inc_ref(v_array_3665_);
v_idx_3666_ = lean_ctor_get(v_pos_3663_, 1);
lean_inc(v_idx_3666_);
v_pos_3637_ = v_pos_3663_;
v_array_3638_ = v_array_3665_;
v_idx_3639_ = v_idx_3666_;
v_err_3640_ = v_err_3664_;
goto v___jp_3636_;
}
}
}
}
}
v___jp_3592_:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3599_; 
v___x_3596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3596_, 0, v_res_3555_);
lean_ctor_set(v___x_3596_, 1, v_fst_3587_);
lean_ctor_set(v___x_3596_, 2, v_snd_3588_);
lean_ctor_set(v___x_3596_, 3, v___y_3593_);
lean_ctor_set(v___x_3596_, 4, v_res_3595_);
v___x_3597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3596_);
if (v_isShared_3586_ == 0)
{
lean_ctor_set(v___x_3585_, 1, v___x_3597_);
lean_ctor_set(v___x_3585_, 0, v_pos_3594_);
v___x_3599_ = v___x_3585_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_pos_3594_);
lean_ctor_set(v_reuseFailAlloc_3600_, 1, v___x_3597_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
v___jp_3601_:
{
lean_object* v_idx_3606_; uint8_t v___x_3607_; 
v_idx_3606_ = lean_ctor_get(v_pos_3604_, 1);
v___x_3607_ = lean_nat_dec_eq(v_idx_3602_, v_idx_3606_);
lean_dec(v_idx_3602_);
if (v___x_3607_ == 0)
{
lean_object* v___x_3609_; 
lean_dec_ref(v_pos_3604_);
lean_dec(v___y_3603_);
lean_dec(v_snd_3588_);
lean_dec(v_fst_3587_);
lean_del_object(v___x_3585_);
lean_dec(v_res_3555_);
if (v_isShared_3558_ == 0)
{
lean_ctor_set_tag(v___x_3557_, 1);
lean_ctor_set(v___x_3557_, 1, v_err_3605_);
lean_ctor_set(v___x_3557_, 0, v_a_3552_);
v___x_3609_ = v___x_3557_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_a_3552_);
lean_ctor_set(v_reuseFailAlloc_3610_, 1, v_err_3605_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
else
{
lean_object* v___x_3611_; 
lean_dec(v_err_3605_);
lean_del_object(v___x_3557_);
lean_dec_ref(v_a_3552_);
v___x_3611_ = lean_box(0);
v___y_3593_ = v___y_3603_;
v_pos_3594_ = v_pos_3604_;
v_res_3595_ = v___x_3611_;
goto v___jp_3592_;
}
}
v___jp_3612_:
{
lean_object* v___x_3617_; uint8_t v___x_3618_; 
v___x_3617_ = lean_byte_array_size(v_array_3614_);
v___x_3618_ = lean_nat_dec_lt(v_idx_3615_, v___x_3617_);
if (v___x_3618_ == 0)
{
lean_object* v___x_3619_; 
lean_dec_ref(v_array_3614_);
lean_del_object(v___x_3590_);
lean_dec_ref(v_config_3551_);
v___x_3619_ = lean_box(0);
v_idx_3602_ = v_idx_3615_;
v___y_3603_ = v_res_3616_;
v_pos_3604_ = v_pos_3613_;
v_err_3605_ = v___x_3619_;
goto v___jp_3601_;
}
else
{
uint8_t v___x_3620_; uint8_t v_got_3621_; uint8_t v___x_3622_; 
v___x_3620_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v_got_3621_ = lean_byte_array_fget(v_array_3614_, v_idx_3615_);
v___x_3622_ = lean_uint8_dec_eq(v_got_3621_, v___x_3620_);
if (v___x_3622_ == 0)
{
lean_object* v___x_3623_; 
lean_dec_ref(v_array_3614_);
lean_del_object(v___x_3590_);
lean_dec_ref(v_config_3551_);
v___x_3623_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__4, &l_Std_Http_URI_Parser_parseURI___closed__4_once, _init_l_Std_Http_URI_Parser_parseURI___closed__4);
v_idx_3602_ = v_idx_3615_;
v___y_3603_ = v_res_3616_;
v_pos_3604_ = v_pos_3613_;
v_err_3605_ = v___x_3623_;
goto v___jp_3601_;
}
else
{
lean_object* v___x_3624_; lean_object* v___x_3626_; 
lean_dec_ref(v_pos_3613_);
v___x_3624_ = lean_nat_add(v_idx_3615_, v___x_3577_);
if (v_isShared_3591_ == 0)
{
lean_ctor_set(v___x_3590_, 1, v___x_3624_);
lean_ctor_set(v___x_3590_, 0, v_array_3614_);
v___x_3626_ = v___x_3590_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_array_3614_);
lean_ctor_set(v_reuseFailAlloc_3633_, 1, v___x_3624_);
v___x_3626_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
lean_object* v___x_3627_; 
v___x_3627_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3551_, v___x_3626_);
lean_dec_ref(v_config_3551_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v_pos_3628_; lean_object* v_res_3629_; lean_object* v___x_3630_; 
lean_dec(v_idx_3615_);
lean_del_object(v___x_3557_);
lean_dec_ref(v_a_3552_);
v_pos_3628_ = lean_ctor_get(v___x_3627_, 0);
lean_inc(v_pos_3628_);
v_res_3629_ = lean_ctor_get(v___x_3627_, 1);
lean_inc(v_res_3629_);
lean_dec_ref_known(v___x_3627_, 2);
v___x_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3630_, 0, v_res_3629_);
v___y_3593_ = v_res_3616_;
v_pos_3594_ = v_pos_3628_;
v_res_3595_ = v___x_3630_;
goto v___jp_3592_;
}
else
{
lean_object* v_pos_3631_; lean_object* v_err_3632_; 
v_pos_3631_ = lean_ctor_get(v___x_3627_, 0);
lean_inc(v_pos_3631_);
v_err_3632_ = lean_ctor_get(v___x_3627_, 1);
lean_inc(v_err_3632_);
lean_dec_ref_known(v___x_3627_, 2);
v_idx_3602_ = v_idx_3615_;
v___y_3603_ = v_res_3616_;
v_pos_3604_ = v_pos_3631_;
v_err_3605_ = v_err_3632_;
goto v___jp_3601_;
}
}
}
}
}
v___jp_3636_:
{
uint8_t v___x_3641_; 
v___x_3641_ = lean_nat_dec_eq(v_idx_3635_, v_idx_3639_);
lean_dec(v_idx_3635_);
if (v___x_3641_ == 0)
{
lean_object* v___x_3642_; 
lean_dec(v_idx_3639_);
lean_dec_ref(v_array_3638_);
lean_dec_ref(v_pos_3637_);
lean_del_object(v___x_3590_);
lean_dec(v_snd_3588_);
lean_dec(v_fst_3587_);
lean_del_object(v___x_3585_);
lean_del_object(v___x_3557_);
lean_dec(v_res_3555_);
lean_dec_ref(v_config_3551_);
v___x_3642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3642_, 0, v_a_3552_);
lean_ctor_set(v___x_3642_, 1, v_err_3640_);
return v___x_3642_;
}
else
{
lean_object* v___x_3643_; 
lean_dec(v_err_3640_);
v___x_3643_ = lean_box(0);
v_pos_3613_ = v_pos_3637_;
v_array_3614_ = v_array_3638_;
v_idx_3615_ = v_idx_3639_;
v_res_3616_ = v___x_3643_;
goto v___jp_3612_;
}
}
}
}
}
else
{
lean_object* v_err_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3680_; 
lean_del_object(v___x_3557_);
lean_dec(v_res_3555_);
lean_dec_ref(v_config_3551_);
v_err_3673_ = lean_ctor_get(v___x_3581_, 1);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3680_ == 0)
{
lean_object* v_unused_3681_; 
v_unused_3681_ = lean_ctor_get(v___x_3581_, 0);
lean_dec(v_unused_3681_);
v___x_3675_ = v___x_3581_;
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_err_3673_);
lean_dec(v___x_3581_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 0, v_a_3552_);
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3552_);
lean_ctor_set(v_reuseFailAlloc_3679_, 1, v_err_3673_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
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
lean_object* v_err_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3692_; 
lean_dec_ref(v_config_3551_);
v_err_3685_ = lean_ctor_get(v___x_3553_, 1);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3692_ == 0)
{
lean_object* v_unused_3693_; 
v_unused_3693_ = lean_ctor_get(v___x_3553_, 0);
lean_dec(v_unused_3693_);
v___x_3687_ = v___x_3553_;
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_err_3685_);
lean_dec(v___x_3553_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 0, v_a_3552_);
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3552_);
lean_ctor_set(v_reuseFailAlloc_3691_, 1, v_err_3685_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withAuthority(lean_object* v_config_3694_, lean_object* v_a_3695_){
_start:
{
lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v_pos_3700_; lean_object* v_res_3701_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v_idx_3708_; lean_object* v___y_3709_; lean_object* v_pos_3710_; lean_object* v_err_3711_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v_pos_3727_; lean_object* v_array_3728_; lean_object* v_idx_3729_; lean_object* v_res_3730_; lean_object* v_idx_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v_pos_3751_; lean_object* v_array_3752_; lean_object* v_idx_3753_; lean_object* v_err_3754_; lean_object* v_pos_3759_; lean_object* v_utf8_3815_; lean_object* v___x_3816_; 
v_utf8_3815_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_3695_);
v___x_3816_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_3815_, v_a_3695_);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_object* v_pos_3817_; 
v_pos_3817_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_pos_3817_);
lean_dec_ref_known(v___x_3816_, 2);
v_pos_3759_ = v_pos_3817_;
goto v___jp_3758_;
}
else
{
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_object* v_pos_3818_; 
v_pos_3818_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_pos_3818_);
lean_dec_ref_known(v___x_3816_, 2);
v_pos_3759_ = v_pos_3818_;
goto v___jp_3758_;
}
else
{
lean_object* v_err_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3826_; 
lean_dec_ref(v_config_3694_);
v_err_3819_ = lean_ctor_get(v___x_3816_, 1);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3826_ == 0)
{
lean_object* v_unused_3827_; 
v_unused_3827_ = lean_ctor_get(v___x_3816_, 0);
lean_dec(v_unused_3827_);
v___x_3821_ = v___x_3816_;
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_err_3819_);
lean_dec(v___x_3816_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3822_ == 0)
{
lean_ctor_set(v___x_3821_, 0, v_a_3695_);
v___x_3824_ = v___x_3821_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_a_3695_);
lean_ctor_set(v_reuseFailAlloc_3825_, 1, v_err_3819_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
v___jp_3696_:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3702_, 0, v___y_3697_);
v___x_3703_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3702_);
lean_ctor_set(v___x_3703_, 1, v___y_3698_);
lean_ctor_set(v___x_3703_, 2, v___y_3699_);
lean_ctor_set(v___x_3703_, 3, v_res_3701_);
v___x_3704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3704_, 0, v_pos_3700_);
lean_ctor_set(v___x_3704_, 1, v___x_3703_);
return v___x_3704_;
}
v___jp_3705_:
{
lean_object* v_idx_3712_; uint8_t v___x_3713_; 
v_idx_3712_ = lean_ctor_get(v_pos_3710_, 1);
v___x_3713_ = lean_nat_dec_eq(v_idx_3708_, v_idx_3712_);
lean_dec(v_idx_3708_);
if (v___x_3713_ == 0)
{
lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3720_; 
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3707_);
lean_dec_ref(v___y_3706_);
v_isSharedCheck_3720_ = !lean_is_exclusive(v_pos_3710_);
if (v_isSharedCheck_3720_ == 0)
{
lean_object* v_unused_3721_; lean_object* v_unused_3722_; 
v_unused_3721_ = lean_ctor_get(v_pos_3710_, 1);
lean_dec(v_unused_3721_);
v_unused_3722_ = lean_ctor_get(v_pos_3710_, 0);
lean_dec(v_unused_3722_);
v___x_3715_ = v_pos_3710_;
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
else
{
lean_dec(v_pos_3710_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3718_; 
if (v_isShared_3716_ == 0)
{
lean_ctor_set_tag(v___x_3715_, 1);
lean_ctor_set(v___x_3715_, 1, v_err_3711_);
lean_ctor_set(v___x_3715_, 0, v_a_3695_);
v___x_3718_ = v___x_3715_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_a_3695_);
lean_ctor_set(v_reuseFailAlloc_3719_, 1, v_err_3711_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
else
{
lean_object* v___x_3723_; 
lean_dec(v_err_3711_);
lean_dec_ref(v_a_3695_);
v___x_3723_ = lean_box(0);
v___y_3697_ = v___y_3706_;
v___y_3698_ = v___y_3707_;
v___y_3699_ = v___y_3709_;
v_pos_3700_ = v_pos_3710_;
v_res_3701_ = v___x_3723_;
goto v___jp_3696_;
}
}
v___jp_3724_:
{
lean_object* v___x_3731_; uint8_t v___x_3732_; 
v___x_3731_ = lean_byte_array_size(v_array_3728_);
v___x_3732_ = lean_nat_dec_lt(v_idx_3729_, v___x_3731_);
if (v___x_3732_ == 0)
{
lean_object* v___x_3733_; 
lean_dec_ref(v_array_3728_);
lean_dec_ref(v_config_3694_);
v___x_3733_ = lean_box(0);
v___y_3706_ = v___y_3725_;
v___y_3707_ = v___y_3726_;
v_idx_3708_ = v_idx_3729_;
v___y_3709_ = v_res_3730_;
v_pos_3710_ = v_pos_3727_;
v_err_3711_ = v___x_3733_;
goto v___jp_3705_;
}
else
{
uint8_t v___x_3734_; uint8_t v_got_3735_; uint8_t v___x_3736_; 
v___x_3734_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v_got_3735_ = lean_byte_array_fget(v_array_3728_, v_idx_3729_);
v___x_3736_ = lean_uint8_dec_eq(v_got_3735_, v___x_3734_);
if (v___x_3736_ == 0)
{
lean_object* v___x_3737_; 
lean_dec_ref(v_array_3728_);
lean_dec_ref(v_config_3694_);
v___x_3737_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__4, &l_Std_Http_URI_Parser_parseURI___closed__4_once, _init_l_Std_Http_URI_Parser_parseURI___closed__4);
v___y_3706_ = v___y_3725_;
v___y_3707_ = v___y_3726_;
v_idx_3708_ = v_idx_3729_;
v___y_3709_ = v_res_3730_;
v_pos_3710_ = v_pos_3727_;
v_err_3711_ = v___x_3737_;
goto v___jp_3705_;
}
else
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
lean_dec_ref(v_pos_3727_);
v___x_3738_ = lean_unsigned_to_nat(1u);
v___x_3739_ = lean_nat_add(v_idx_3729_, v___x_3738_);
v___x_3740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3740_, 0, v_array_3728_);
lean_ctor_set(v___x_3740_, 1, v___x_3739_);
v___x_3741_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3694_, v___x_3740_);
lean_dec_ref(v_config_3694_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v_pos_3742_; lean_object* v_res_3743_; lean_object* v___x_3744_; 
lean_dec(v_idx_3729_);
lean_dec_ref(v_a_3695_);
v_pos_3742_ = lean_ctor_get(v___x_3741_, 0);
lean_inc(v_pos_3742_);
v_res_3743_ = lean_ctor_get(v___x_3741_, 1);
lean_inc(v_res_3743_);
lean_dec_ref_known(v___x_3741_, 2);
v___x_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3744_, 0, v_res_3743_);
v___y_3697_ = v___y_3725_;
v___y_3698_ = v___y_3726_;
v___y_3699_ = v_res_3730_;
v_pos_3700_ = v_pos_3742_;
v_res_3701_ = v___x_3744_;
goto v___jp_3696_;
}
else
{
lean_object* v_pos_3745_; lean_object* v_err_3746_; 
v_pos_3745_ = lean_ctor_get(v___x_3741_, 0);
lean_inc(v_pos_3745_);
v_err_3746_ = lean_ctor_get(v___x_3741_, 1);
lean_inc(v_err_3746_);
lean_dec_ref_known(v___x_3741_, 2);
v___y_3706_ = v___y_3725_;
v___y_3707_ = v___y_3726_;
v_idx_3708_ = v_idx_3729_;
v___y_3709_ = v_res_3730_;
v_pos_3710_ = v_pos_3745_;
v_err_3711_ = v_err_3746_;
goto v___jp_3705_;
}
}
}
}
v___jp_3747_:
{
uint8_t v___x_3755_; 
v___x_3755_ = lean_nat_dec_eq(v_idx_3748_, v_idx_3753_);
lean_dec(v_idx_3748_);
if (v___x_3755_ == 0)
{
lean_object* v___x_3756_; 
lean_dec(v_idx_3753_);
lean_dec_ref(v_array_3752_);
lean_dec_ref(v_pos_3751_);
lean_dec_ref(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec_ref(v_config_3694_);
v___x_3756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3756_, 0, v_a_3695_);
lean_ctor_set(v___x_3756_, 1, v_err_3754_);
return v___x_3756_;
}
else
{
lean_object* v___x_3757_; 
lean_dec(v_err_3754_);
v___x_3757_ = lean_box(0);
v___y_3725_ = v___y_3749_;
v___y_3726_ = v___y_3750_;
v_pos_3727_ = v_pos_3751_;
v_array_3728_ = v_array_3752_;
v_idx_3729_ = v_idx_3753_;
v_res_3730_ = v___x_3757_;
goto v___jp_3724_;
}
}
v___jp_3758_:
{
lean_object* v___x_3760_; 
v___x_3760_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_3694_, v_pos_3759_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_pos_3761_; lean_object* v_res_3762_; uint8_t v___x_3763_; lean_object* v___x_3764_; 
v_pos_3761_ = lean_ctor_get(v___x_3760_, 0);
lean_inc(v_pos_3761_);
v_res_3762_ = lean_ctor_get(v___x_3760_, 1);
lean_inc(v_res_3762_);
lean_dec_ref_known(v___x_3760_, 2);
v___x_3763_ = 1;
lean_inc_ref(v_config_3694_);
v___x_3764_ = l_Std_Http_URI_Parser_parsePath(v_config_3694_, v___x_3763_, v___x_3763_, v_pos_3761_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_pos_3765_; lean_object* v_res_3766_; lean_object* v_array_3767_; lean_object* v_idx_3768_; lean_object* v___x_3769_; uint8_t v___x_3770_; 
v_pos_3765_ = lean_ctor_get(v___x_3764_, 0);
lean_inc(v_pos_3765_);
v_res_3766_ = lean_ctor_get(v___x_3764_, 1);
lean_inc(v_res_3766_);
lean_dec_ref_known(v___x_3764_, 2);
v_array_3767_ = lean_ctor_get(v_pos_3765_, 0);
lean_inc_ref(v_array_3767_);
v_idx_3768_ = lean_ctor_get(v_pos_3765_, 1);
lean_inc(v_idx_3768_);
v___x_3769_ = lean_byte_array_size(v_array_3767_);
v___x_3770_ = lean_nat_dec_lt(v_idx_3768_, v___x_3769_);
if (v___x_3770_ == 0)
{
lean_object* v___x_3771_; 
v___x_3771_ = lean_box(0);
lean_inc(v_idx_3768_);
v_idx_3748_ = v_idx_3768_;
v___y_3749_ = v_res_3762_;
v___y_3750_ = v_res_3766_;
v_pos_3751_ = v_pos_3765_;
v_array_3752_ = v_array_3767_;
v_idx_3753_ = v_idx_3768_;
v_err_3754_ = v___x_3771_;
goto v___jp_3747_;
}
else
{
uint8_t v___x_3772_; uint8_t v_got_3773_; uint8_t v___x_3774_; 
v___x_3772_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3773_ = lean_byte_array_fget(v_array_3767_, v_idx_3768_);
v___x_3774_ = lean_uint8_dec_eq(v_got_3773_, v___x_3772_);
if (v___x_3774_ == 0)
{
lean_object* v___x_3775_; 
v___x_3775_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3768_);
v_idx_3748_ = v_idx_3768_;
v___y_3749_ = v_res_3762_;
v___y_3750_ = v_res_3766_;
v_pos_3751_ = v_pos_3765_;
v_array_3752_ = v_array_3767_;
v_idx_3753_ = v_idx_3768_;
v_err_3754_ = v___x_3775_;
goto v___jp_3747_;
}
else
{
lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3794_; 
v_isSharedCheck_3794_ = !lean_is_exclusive(v_pos_3765_);
if (v_isSharedCheck_3794_ == 0)
{
lean_object* v_unused_3795_; lean_object* v_unused_3796_; 
v_unused_3795_ = lean_ctor_get(v_pos_3765_, 1);
lean_dec(v_unused_3795_);
v_unused_3796_ = lean_ctor_get(v_pos_3765_, 0);
lean_dec(v_unused_3796_);
v___x_3777_ = v_pos_3765_;
v_isShared_3778_ = v_isSharedCheck_3794_;
goto v_resetjp_3776_;
}
else
{
lean_dec(v_pos_3765_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3794_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3782_; 
v___x_3779_ = lean_unsigned_to_nat(1u);
v___x_3780_ = lean_nat_add(v_idx_3768_, v___x_3779_);
if (v_isShared_3778_ == 0)
{
lean_ctor_set(v___x_3777_, 1, v___x_3780_);
v___x_3782_ = v___x_3777_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_array_3767_);
lean_ctor_set(v_reuseFailAlloc_3793_, 1, v___x_3780_);
v___x_3782_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
lean_object* v___x_3783_; 
lean_inc_ref(v_config_3694_);
v___x_3783_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3694_, v___x_3782_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v_pos_3784_; lean_object* v_res_3785_; lean_object* v_array_3786_; lean_object* v_idx_3787_; lean_object* v___x_3788_; 
lean_dec(v_idx_3768_);
v_pos_3784_ = lean_ctor_get(v___x_3783_, 0);
lean_inc(v_pos_3784_);
v_res_3785_ = lean_ctor_get(v___x_3783_, 1);
lean_inc(v_res_3785_);
lean_dec_ref_known(v___x_3783_, 2);
v_array_3786_ = lean_ctor_get(v_pos_3784_, 0);
lean_inc_ref(v_array_3786_);
v_idx_3787_ = lean_ctor_get(v_pos_3784_, 1);
lean_inc(v_idx_3787_);
v___x_3788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3788_, 0, v_res_3785_);
v___y_3725_ = v_res_3762_;
v___y_3726_ = v_res_3766_;
v_pos_3727_ = v_pos_3784_;
v_array_3728_ = v_array_3786_;
v_idx_3729_ = v_idx_3787_;
v_res_3730_ = v___x_3788_;
goto v___jp_3724_;
}
else
{
lean_object* v_pos_3789_; lean_object* v_err_3790_; lean_object* v_array_3791_; lean_object* v_idx_3792_; 
v_pos_3789_ = lean_ctor_get(v___x_3783_, 0);
lean_inc(v_pos_3789_);
v_err_3790_ = lean_ctor_get(v___x_3783_, 1);
lean_inc(v_err_3790_);
lean_dec_ref_known(v___x_3783_, 2);
v_array_3791_ = lean_ctor_get(v_pos_3789_, 0);
lean_inc_ref(v_array_3791_);
v_idx_3792_ = lean_ctor_get(v_pos_3789_, 1);
lean_inc(v_idx_3792_);
v_idx_3748_ = v_idx_3768_;
v___y_3749_ = v_res_3762_;
v___y_3750_ = v_res_3766_;
v_pos_3751_ = v_pos_3789_;
v_array_3752_ = v_array_3791_;
v_idx_3753_ = v_idx_3792_;
v_err_3754_ = v_err_3790_;
goto v___jp_3747_;
}
}
}
}
}
}
else
{
lean_object* v_err_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_dec(v_res_3762_);
lean_dec_ref(v_config_3694_);
v_err_3797_ = lean_ctor_get(v___x_3764_, 1);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3804_ == 0)
{
lean_object* v_unused_3805_; 
v_unused_3805_ = lean_ctor_get(v___x_3764_, 0);
lean_dec(v_unused_3805_);
v___x_3799_ = v___x_3764_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_err_3797_);
lean_dec(v___x_3764_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
lean_ctor_set(v___x_3799_, 0, v_a_3695_);
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3695_);
lean_ctor_set(v_reuseFailAlloc_3803_, 1, v_err_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
else
{
lean_object* v_err_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
lean_dec_ref(v_config_3694_);
v_err_3806_ = lean_ctor_get(v___x_3760_, 1);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3813_ == 0)
{
lean_object* v_unused_3814_; 
v_unused_3814_ = lean_ctor_get(v___x_3760_, 0);
lean_dec(v_unused_3814_);
v___x_3808_ = v___x_3760_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_err_3806_);
lean_dec(v___x_3760_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
lean_ctor_set(v___x_3808_, 0, v_a_3695_);
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3695_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v_err_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath(lean_object* v_config_3828_, lean_object* v_a_3829_){
_start:
{
uint8_t v___x_3830_; uint8_t v___x_3831_; lean_object* v___x_3832_; 
v___x_3830_ = 0;
v___x_3831_ = 1;
lean_inc_ref(v_config_3828_);
v___x_3832_ = l_Std_Http_URI_Parser_parsePath(v_config_3828_, v___x_3830_, v___x_3831_, v_a_3829_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v_pos_3833_; lean_object* v_res_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3915_; 
v_pos_3833_ = lean_ctor_get(v___x_3832_, 0);
v_res_3834_ = lean_ctor_get(v___x_3832_, 1);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3836_ = v___x_3832_;
v_isShared_3837_ = v_isSharedCheck_3915_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_res_3834_);
lean_inc(v_pos_3833_);
lean_dec(v___x_3832_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3915_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___y_3839_; lean_object* v_pos_3840_; lean_object* v_res_3841_; lean_object* v_idx_3848_; lean_object* v___y_3849_; lean_object* v_pos_3850_; lean_object* v_err_3851_; lean_object* v_pos_3857_; lean_object* v_array_3858_; lean_object* v_idx_3859_; lean_object* v_res_3860_; lean_object* v_array_3877_; lean_object* v_idx_3878_; lean_object* v_pos_3880_; lean_object* v_array_3881_; lean_object* v_idx_3882_; lean_object* v_err_3883_; lean_object* v___x_3887_; uint8_t v___x_3888_; 
v_array_3877_ = lean_ctor_get(v_pos_3833_, 0);
lean_inc_ref(v_array_3877_);
v_idx_3878_ = lean_ctor_get(v_pos_3833_, 1);
lean_inc(v_idx_3878_);
v___x_3887_ = lean_byte_array_size(v_array_3877_);
v___x_3888_ = lean_nat_dec_lt(v_idx_3878_, v___x_3887_);
if (v___x_3888_ == 0)
{
lean_object* v___x_3889_; 
v___x_3889_ = lean_box(0);
lean_inc(v_idx_3878_);
v_pos_3880_ = v_pos_3833_;
v_array_3881_ = v_array_3877_;
v_idx_3882_ = v_idx_3878_;
v_err_3883_ = v___x_3889_;
goto v___jp_3879_;
}
else
{
uint8_t v___x_3890_; uint8_t v_got_3891_; uint8_t v___x_3892_; 
v___x_3890_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3891_ = lean_byte_array_fget(v_array_3877_, v_idx_3878_);
v___x_3892_ = lean_uint8_dec_eq(v_got_3891_, v___x_3890_);
if (v___x_3892_ == 0)
{
lean_object* v___x_3893_; 
v___x_3893_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3878_);
v_pos_3880_ = v_pos_3833_;
v_array_3881_ = v_array_3877_;
v_idx_3882_ = v_idx_3878_;
v_err_3883_ = v___x_3893_;
goto v___jp_3879_;
}
else
{
lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3912_; 
v_isSharedCheck_3912_ = !lean_is_exclusive(v_pos_3833_);
if (v_isSharedCheck_3912_ == 0)
{
lean_object* v_unused_3913_; lean_object* v_unused_3914_; 
v_unused_3913_ = lean_ctor_get(v_pos_3833_, 1);
lean_dec(v_unused_3913_);
v_unused_3914_ = lean_ctor_get(v_pos_3833_, 0);
lean_dec(v_unused_3914_);
v___x_3895_ = v_pos_3833_;
v_isShared_3896_ = v_isSharedCheck_3912_;
goto v_resetjp_3894_;
}
else
{
lean_dec(v_pos_3833_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3912_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3900_; 
v___x_3897_ = lean_unsigned_to_nat(1u);
v___x_3898_ = lean_nat_add(v_idx_3878_, v___x_3897_);
if (v_isShared_3896_ == 0)
{
lean_ctor_set(v___x_3895_, 1, v___x_3898_);
v___x_3900_ = v___x_3895_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_array_3877_);
lean_ctor_set(v_reuseFailAlloc_3911_, 1, v___x_3898_);
v___x_3900_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
lean_object* v___x_3901_; 
lean_inc_ref(v_config_3828_);
v___x_3901_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3828_, v___x_3900_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v_pos_3902_; lean_object* v_res_3903_; lean_object* v_array_3904_; lean_object* v_idx_3905_; lean_object* v___x_3906_; 
lean_dec(v_idx_3878_);
v_pos_3902_ = lean_ctor_get(v___x_3901_, 0);
lean_inc(v_pos_3902_);
v_res_3903_ = lean_ctor_get(v___x_3901_, 1);
lean_inc(v_res_3903_);
lean_dec_ref_known(v___x_3901_, 2);
v_array_3904_ = lean_ctor_get(v_pos_3902_, 0);
lean_inc_ref(v_array_3904_);
v_idx_3905_ = lean_ctor_get(v_pos_3902_, 1);
lean_inc(v_idx_3905_);
v___x_3906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3906_, 0, v_res_3903_);
v_pos_3857_ = v_pos_3902_;
v_array_3858_ = v_array_3904_;
v_idx_3859_ = v_idx_3905_;
v_res_3860_ = v___x_3906_;
goto v___jp_3856_;
}
else
{
lean_object* v_pos_3907_; lean_object* v_err_3908_; lean_object* v_array_3909_; lean_object* v_idx_3910_; 
v_pos_3907_ = lean_ctor_get(v___x_3901_, 0);
lean_inc(v_pos_3907_);
v_err_3908_ = lean_ctor_get(v___x_3901_, 1);
lean_inc(v_err_3908_);
lean_dec_ref_known(v___x_3901_, 2);
v_array_3909_ = lean_ctor_get(v_pos_3907_, 0);
lean_inc_ref(v_array_3909_);
v_idx_3910_ = lean_ctor_get(v_pos_3907_, 1);
lean_inc(v_idx_3910_);
v_pos_3880_ = v_pos_3907_;
v_array_3881_ = v_array_3909_;
v_idx_3882_ = v_idx_3910_;
v_err_3883_ = v_err_3908_;
goto v___jp_3879_;
}
}
}
}
}
v___jp_3838_:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3845_; 
v___x_3842_ = lean_box(0);
v___x_3843_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3842_);
lean_ctor_set(v___x_3843_, 1, v_res_3834_);
lean_ctor_set(v___x_3843_, 2, v___y_3839_);
lean_ctor_set(v___x_3843_, 3, v_res_3841_);
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 1, v___x_3843_);
lean_ctor_set(v___x_3836_, 0, v_pos_3840_);
v___x_3845_ = v___x_3836_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_pos_3840_);
lean_ctor_set(v_reuseFailAlloc_3846_, 1, v___x_3843_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
v___jp_3847_:
{
lean_object* v_idx_3852_; uint8_t v___x_3853_; 
v_idx_3852_ = lean_ctor_get(v_pos_3850_, 1);
v___x_3853_ = lean_nat_dec_eq(v_idx_3848_, v_idx_3852_);
lean_dec(v_idx_3848_);
if (v___x_3853_ == 0)
{
lean_object* v___x_3854_; 
lean_dec(v___y_3849_);
lean_del_object(v___x_3836_);
lean_dec(v_res_3834_);
v___x_3854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3854_, 0, v_pos_3850_);
lean_ctor_set(v___x_3854_, 1, v_err_3851_);
return v___x_3854_;
}
else
{
lean_object* v___x_3855_; 
lean_dec(v_err_3851_);
v___x_3855_ = lean_box(0);
v___y_3839_ = v___y_3849_;
v_pos_3840_ = v_pos_3850_;
v_res_3841_ = v___x_3855_;
goto v___jp_3838_;
}
}
v___jp_3856_:
{
lean_object* v___x_3861_; uint8_t v___x_3862_; 
v___x_3861_ = lean_byte_array_size(v_array_3858_);
v___x_3862_ = lean_nat_dec_lt(v_idx_3859_, v___x_3861_);
if (v___x_3862_ == 0)
{
lean_object* v___x_3863_; 
lean_dec_ref(v_array_3858_);
lean_dec_ref(v_config_3828_);
v___x_3863_ = lean_box(0);
v_idx_3848_ = v_idx_3859_;
v___y_3849_ = v_res_3860_;
v_pos_3850_ = v_pos_3857_;
v_err_3851_ = v___x_3863_;
goto v___jp_3847_;
}
else
{
uint8_t v___x_3864_; uint8_t v_got_3865_; uint8_t v___x_3866_; 
v___x_3864_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v_got_3865_ = lean_byte_array_fget(v_array_3858_, v_idx_3859_);
v___x_3866_ = lean_uint8_dec_eq(v_got_3865_, v___x_3864_);
if (v___x_3866_ == 0)
{
lean_object* v___x_3867_; 
lean_dec_ref(v_array_3858_);
lean_dec_ref(v_config_3828_);
v___x_3867_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__4, &l_Std_Http_URI_Parser_parseURI___closed__4_once, _init_l_Std_Http_URI_Parser_parseURI___closed__4);
v_idx_3848_ = v_idx_3859_;
v___y_3849_ = v_res_3860_;
v_pos_3850_ = v_pos_3857_;
v_err_3851_ = v___x_3867_;
goto v___jp_3847_;
}
else
{
lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
lean_dec_ref(v_pos_3857_);
v___x_3868_ = lean_unsigned_to_nat(1u);
v___x_3869_ = lean_nat_add(v_idx_3859_, v___x_3868_);
v___x_3870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3870_, 0, v_array_3858_);
lean_ctor_set(v___x_3870_, 1, v___x_3869_);
v___x_3871_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3828_, v___x_3870_);
lean_dec_ref(v_config_3828_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v_pos_3872_; lean_object* v_res_3873_; lean_object* v___x_3874_; 
lean_dec(v_idx_3859_);
v_pos_3872_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_pos_3872_);
v_res_3873_ = lean_ctor_get(v___x_3871_, 1);
lean_inc(v_res_3873_);
lean_dec_ref_known(v___x_3871_, 2);
v___x_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3874_, 0, v_res_3873_);
v___y_3839_ = v_res_3860_;
v_pos_3840_ = v_pos_3872_;
v_res_3841_ = v___x_3874_;
goto v___jp_3838_;
}
else
{
lean_object* v_pos_3875_; lean_object* v_err_3876_; 
v_pos_3875_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_pos_3875_);
v_err_3876_ = lean_ctor_get(v___x_3871_, 1);
lean_inc(v_err_3876_);
lean_dec_ref_known(v___x_3871_, 2);
v_idx_3848_ = v_idx_3859_;
v___y_3849_ = v_res_3860_;
v_pos_3850_ = v_pos_3875_;
v_err_3851_ = v_err_3876_;
goto v___jp_3847_;
}
}
}
}
v___jp_3879_:
{
uint8_t v___x_3884_; 
v___x_3884_ = lean_nat_dec_eq(v_idx_3878_, v_idx_3882_);
lean_dec(v_idx_3878_);
if (v___x_3884_ == 0)
{
lean_object* v___x_3885_; 
lean_dec(v_idx_3882_);
lean_dec_ref(v_array_3881_);
lean_del_object(v___x_3836_);
lean_dec(v_res_3834_);
lean_dec_ref(v_config_3828_);
v___x_3885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3885_, 0, v_pos_3880_);
lean_ctor_set(v___x_3885_, 1, v_err_3883_);
return v___x_3885_;
}
else
{
lean_object* v___x_3886_; 
lean_dec(v_err_3883_);
v___x_3886_ = lean_box(0);
v_pos_3857_ = v_pos_3880_;
v_array_3858_ = v_array_3881_;
v_idx_3859_ = v_idx_3882_;
v_res_3860_ = v___x_3886_;
goto v___jp_3856_;
}
}
}
}
else
{
lean_object* v_pos_3916_; lean_object* v_err_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3924_; 
lean_dec_ref(v_config_3828_);
v_pos_3916_ = lean_ctor_get(v___x_3832_, 0);
v_err_3917_ = lean_ctor_get(v___x_3832_, 1);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3919_ = v___x_3832_;
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_err_3917_);
lean_inc(v_pos_3916_);
lean_dec(v___x_3832_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3922_; 
if (v_isShared_3920_ == 0)
{
v___x_3922_ = v___x_3919_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_pos_3916_);
lean_ctor_set(v_reuseFailAlloc_3923_, 1, v_err_3917_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_relative(lean_object* v_config_3925_, lean_object* v_a_3926_){
_start:
{
lean_object* v___y_3928_; lean_object* v___x_3948_; 
lean_inc_ref(v_a_3926_);
lean_inc_ref(v_config_3925_);
v___x_3948_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withAuthority(v_config_3925_, v_a_3926_);
if (lean_obj_tag(v___x_3948_) == 0)
{
lean_dec_ref(v_a_3926_);
lean_dec_ref(v_config_3925_);
v___y_3928_ = v___x_3948_;
goto v___jp_3927_;
}
else
{
lean_object* v_pos_3949_; lean_object* v_idx_3950_; lean_object* v_idx_3951_; uint8_t v___x_3952_; 
v_pos_3949_ = lean_ctor_get(v___x_3948_, 0);
lean_inc(v_pos_3949_);
v_idx_3950_ = lean_ctor_get(v_a_3926_, 1);
lean_inc(v_idx_3950_);
lean_dec_ref(v_a_3926_);
v_idx_3951_ = lean_ctor_get(v_pos_3949_, 1);
v___x_3952_ = lean_nat_dec_eq(v_idx_3950_, v_idx_3951_);
lean_dec(v_idx_3950_);
if (v___x_3952_ == 0)
{
lean_dec(v_pos_3949_);
lean_dec_ref(v_config_3925_);
v___y_3928_ = v___x_3948_;
goto v___jp_3927_;
}
else
{
lean_object* v___x_3953_; 
lean_dec_ref_known(v___x_3948_, 2);
v___x_3953_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath(v_config_3925_, v_pos_3949_);
v___y_3928_ = v___x_3953_;
goto v___jp_3927_;
}
}
v___jp_3927_:
{
if (lean_obj_tag(v___y_3928_) == 0)
{
lean_object* v_pos_3929_; lean_object* v_res_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3938_; 
v_pos_3929_ = lean_ctor_get(v___y_3928_, 0);
v_res_3930_ = lean_ctor_get(v___y_3928_, 1);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___y_3928_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3932_ = v___y_3928_;
v_isShared_3933_ = v_isSharedCheck_3938_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_res_3930_);
lean_inc(v_pos_3929_);
lean_dec(v___y_3928_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3938_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3934_; lean_object* v___x_3936_; 
v___x_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3934_, 0, v_res_3930_);
if (v_isShared_3933_ == 0)
{
lean_ctor_set(v___x_3932_, 1, v___x_3934_);
v___x_3936_ = v___x_3932_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_pos_3929_);
lean_ctor_set(v_reuseFailAlloc_3937_, 1, v___x_3934_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
else
{
lean_object* v_pos_3939_; lean_object* v_err_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3947_; 
v_pos_3939_ = lean_ctor_get(v___y_3928_, 0);
v_err_3940_ = lean_ctor_get(v___y_3928_, 1);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___y_3928_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3942_ = v___y_3928_;
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_err_3940_);
lean_inc(v_pos_3939_);
lean_dec(v___y_3928_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3945_; 
if (v_isShared_3943_ == 0)
{
v___x_3945_ = v___x_3942_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_pos_3939_);
lean_ctor_set(v_reuseFailAlloc_3946_, 1, v_err_3940_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURIReference(lean_object* v_config_3954_, lean_object* v_a_3955_){
_start:
{
lean_object* v___y_3957_; lean_object* v_pos_3958_; lean_object* v___x_3963_; 
lean_inc_ref(v_a_3955_);
lean_inc_ref(v_config_3954_);
v___x_3963_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_uri(v_config_3954_, v_a_3955_);
if (lean_obj_tag(v___x_3963_) == 0)
{
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_dec_ref(v_a_3955_);
lean_dec_ref(v_config_3954_);
return v___x_3963_;
}
else
{
lean_object* v_pos_3964_; 
v_pos_3964_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_pos_3964_);
v___y_3957_ = v___x_3963_;
v_pos_3958_ = v_pos_3964_;
goto v___jp_3956_;
}
}
else
{
lean_object* v_err_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
v_err_3965_ = lean_ctor_get(v___x_3963_, 1);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3972_ == 0)
{
lean_object* v_unused_3973_; 
v_unused_3973_ = lean_ctor_get(v___x_3963_, 0);
lean_dec(v_unused_3973_);
v___x_3967_ = v___x_3963_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_err_3965_);
lean_dec(v___x_3963_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
lean_inc_ref(v_a_3955_);
if (v_isShared_3968_ == 0)
{
lean_ctor_set(v___x_3967_, 0, v_a_3955_);
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3955_);
lean_ctor_set(v_reuseFailAlloc_3971_, 1, v_err_3965_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
lean_inc_ref(v_a_3955_);
v___y_3957_ = v___x_3970_;
v_pos_3958_ = v_a_3955_;
goto v___jp_3956_;
}
}
}
v___jp_3956_:
{
lean_object* v_idx_3959_; lean_object* v_idx_3960_; uint8_t v___x_3961_; 
v_idx_3959_ = lean_ctor_get(v_a_3955_, 1);
lean_inc(v_idx_3959_);
lean_dec_ref(v_a_3955_);
v_idx_3960_ = lean_ctor_get(v_pos_3958_, 1);
v___x_3961_ = lean_nat_dec_eq(v_idx_3959_, v_idx_3960_);
lean_dec(v_idx_3959_);
if (v___x_3961_ == 0)
{
lean_dec_ref(v_pos_3958_);
lean_dec_ref(v_config_3954_);
return v___y_3957_;
}
else
{
lean_object* v___x_3962_; 
lean_dec_ref(v___y_3957_);
v___x_3962_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_relative(v_config_3954_, v_pos_3958_);
return v___x_3962_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader(lean_object* v_config_3980_, lean_object* v_a_3981_){
_start:
{
lean_object* v___x_3982_; 
v___x_3982_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3980_, v_a_3981_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v_pos_3983_; lean_object* v_res_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_4057_; 
v_pos_3983_ = lean_ctor_get(v___x_3982_, 0);
v_res_3984_ = lean_ctor_get(v___x_3982_, 1);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_3986_ = v___x_3982_;
v_isShared_3987_ = v_isSharedCheck_4057_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_res_3984_);
lean_inc(v_pos_3983_);
lean_dec(v___x_3982_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_4057_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v_port_3989_; lean_object* v___y_3990_; lean_object* v_pos_4004_; lean_object* v_pos_4007_; lean_object* v_array_4008_; lean_object* v_idx_4009_; lean_object* v_array_4015_; lean_object* v_idx_4016_; lean_object* v___x_4017_; uint8_t v___x_4018_; 
v_array_4015_ = lean_ctor_get(v_pos_3983_, 0);
v_idx_4016_ = lean_ctor_get(v_pos_3983_, 1);
v___x_4017_ = lean_byte_array_size(v_array_4015_);
v___x_4018_ = lean_nat_dec_lt(v_idx_4016_, v___x_4017_);
if (v___x_4018_ == 0)
{
v_pos_4004_ = v_pos_3983_;
goto v___jp_4003_;
}
else
{
uint8_t v___x_4019_; uint8_t v___x_4020_; uint8_t v___x_4021_; 
v___x_4019_ = lean_byte_array_fget(v_array_4015_, v_idx_4016_);
v___x_4020_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_4021_ = lean_uint8_dec_eq(v___x_4019_, v___x_4020_);
if (v___x_4021_ == 0)
{
v_pos_4004_ = v_pos_3983_;
goto v___jp_4003_;
}
else
{
if (v___x_4018_ == 0)
{
lean_object* v___x_4022_; lean_object* v___x_4023_; 
lean_del_object(v___x_3986_);
lean_dec(v_res_3984_);
v___x_4022_ = lean_box(0);
v___x_4023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4023_, 0, v_pos_3983_);
lean_ctor_set(v___x_4023_, 1, v___x_4022_);
return v___x_4023_;
}
else
{
if (v___x_4021_ == 0)
{
lean_object* v___x_4024_; lean_object* v___x_4025_; 
lean_del_object(v___x_3986_);
lean_dec(v_res_3984_);
v___x_4024_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
v___x_4025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4025_, 0, v_pos_3983_);
lean_ctor_set(v___x_4025_, 1, v___x_4024_);
return v___x_4025_;
}
else
{
lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4054_; 
lean_inc(v_idx_4016_);
lean_inc_ref(v_array_4015_);
v_isSharedCheck_4054_ = !lean_is_exclusive(v_pos_3983_);
if (v_isSharedCheck_4054_ == 0)
{
lean_object* v_unused_4055_; lean_object* v_unused_4056_; 
v_unused_4055_ = lean_ctor_get(v_pos_3983_, 1);
lean_dec(v_unused_4055_);
v_unused_4056_ = lean_ctor_get(v_pos_3983_, 0);
lean_dec(v_unused_4056_);
v___x_4027_ = v_pos_3983_;
v_isShared_4028_ = v_isSharedCheck_4054_;
goto v_resetjp_4026_;
}
else
{
lean_dec(v_pos_3983_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4054_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4032_; 
v___x_4029_ = lean_unsigned_to_nat(1u);
v___x_4030_ = lean_nat_add(v_idx_4016_, v___x_4029_);
lean_dec(v_idx_4016_);
lean_inc(v___x_4030_);
lean_inc_ref(v_array_4015_);
if (v_isShared_4028_ == 0)
{
lean_ctor_set(v___x_4027_, 1, v___x_4030_);
v___x_4032_ = v___x_4027_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_array_4015_);
lean_ctor_set(v_reuseFailAlloc_4053_, 1, v___x_4030_);
v___x_4032_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
uint8_t v___x_4033_; 
v___x_4033_ = lean_nat_dec_lt(v___x_4030_, v___x_4017_);
if (v___x_4033_ == 0)
{
v_pos_4007_ = v___x_4032_;
v_array_4008_ = v_array_4015_;
v_idx_4009_ = v___x_4030_;
goto v___jp_4006_;
}
else
{
uint8_t v___x_4034_; uint8_t v___x_4035_; uint8_t v___x_4036_; 
v___x_4034_ = lean_byte_array_fget(v_array_4015_, v___x_4030_);
v___x_4035_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_4036_ = lean_uint8_dec_le(v___x_4035_, v___x_4034_);
if (v___x_4036_ == 0)
{
v_pos_4007_ = v___x_4032_;
v_array_4008_ = v_array_4015_;
v_idx_4009_ = v___x_4030_;
goto v___jp_4006_;
}
else
{
uint8_t v___x_4037_; uint8_t v___x_4038_; 
v___x_4037_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_4038_ = lean_uint8_dec_le(v___x_4034_, v___x_4037_);
if (v___x_4038_ == 0)
{
v_pos_4007_ = v___x_4032_;
v_array_4008_ = v_array_4015_;
v_idx_4009_ = v___x_4030_;
goto v___jp_4006_;
}
else
{
lean_object* v___x_4039_; 
lean_dec(v___x_4030_);
lean_dec_ref(v_array_4015_);
v___x_4039_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_4032_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v_pos_4040_; lean_object* v_res_4041_; lean_object* v___x_4042_; uint16_t v___x_4043_; 
v_pos_4040_ = lean_ctor_get(v___x_4039_, 0);
lean_inc(v_pos_4040_);
v_res_4041_ = lean_ctor_get(v___x_4039_, 1);
lean_inc(v_res_4041_);
lean_dec_ref_known(v___x_4039_, 2);
v___x_4042_ = lean_alloc_ctor(2, 0, 2);
v___x_4043_ = lean_unbox(v_res_4041_);
lean_dec(v_res_4041_);
lean_ctor_set_uint16(v___x_4042_, 0, v___x_4043_);
v_port_3989_ = v___x_4042_;
v___y_3990_ = v_pos_4040_;
goto v___jp_3988_;
}
else
{
lean_object* v_pos_4044_; lean_object* v_err_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
lean_del_object(v___x_3986_);
lean_dec(v_res_3984_);
v_pos_4044_ = lean_ctor_get(v___x_4039_, 0);
v_err_4045_ = lean_ctor_get(v___x_4039_, 1);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4047_ = v___x_4039_;
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_err_4045_);
lean_inc(v_pos_4044_);
lean_dec(v___x_4039_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_pos_4044_);
lean_ctor_set(v_reuseFailAlloc_4051_, 1, v_err_4045_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
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
v___jp_3988_:
{
lean_object* v_array_3991_; lean_object* v_idx_3992_; lean_object* v___x_3993_; uint8_t v___x_3994_; 
v_array_3991_ = lean_ctor_get(v___y_3990_, 0);
v_idx_3992_ = lean_ctor_get(v___y_3990_, 1);
v___x_3993_ = lean_byte_array_size(v_array_3991_);
v___x_3994_ = lean_nat_dec_lt(v_idx_3992_, v___x_3993_);
if (v___x_3994_ == 0)
{
lean_object* v___x_3995_; lean_object* v___x_3997_; 
v___x_3995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3995_, 0, v_res_3984_);
lean_ctor_set(v___x_3995_, 1, v_port_3989_);
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 1, v___x_3995_);
lean_ctor_set(v___x_3986_, 0, v___y_3990_);
v___x_3997_ = v___x_3986_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___y_3990_);
lean_ctor_set(v_reuseFailAlloc_3998_, 1, v___x_3995_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
else
{
lean_object* v___x_3999_; lean_object* v___x_4001_; 
lean_dec(v_port_3989_);
lean_dec(v_res_3984_);
v___x_3999_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__1));
if (v_isShared_3987_ == 0)
{
lean_ctor_set_tag(v___x_3986_, 1);
lean_ctor_set(v___x_3986_, 1, v___x_3999_);
lean_ctor_set(v___x_3986_, 0, v___y_3990_);
v___x_4001_ = v___x_3986_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___y_3990_);
lean_ctor_set(v_reuseFailAlloc_4002_, 1, v___x_3999_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
v___jp_4003_:
{
lean_object* v___x_4005_; 
v___x_4005_ = lean_box(0);
v_port_3989_ = v___x_4005_;
v___y_3990_ = v_pos_4004_;
goto v___jp_3988_;
}
v___jp_4006_:
{
lean_object* v___x_4010_; uint8_t v___x_4011_; 
v___x_4010_ = lean_byte_array_size(v_array_4008_);
lean_dec_ref(v_array_4008_);
v___x_4011_ = lean_nat_dec_lt(v_idx_4009_, v___x_4010_);
lean_dec(v_idx_4009_);
if (v___x_4011_ == 0)
{
lean_object* v___x_4012_; 
v___x_4012_ = lean_box(1);
v_port_3989_ = v___x_4012_;
v___y_3990_ = v_pos_4007_;
goto v___jp_3988_;
}
else
{
lean_object* v___x_4013_; lean_object* v___x_4014_; 
lean_del_object(v___x_3986_);
lean_dec(v_res_3984_);
v___x_4013_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__3));
v___x_4014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4014_, 0, v_pos_4007_);
lean_ctor_set(v___x_4014_, 1, v___x_4013_);
return v___x_4014_;
}
}
}
}
else
{
lean_object* v_pos_4058_; lean_object* v_err_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4066_; 
v_pos_4058_ = lean_ctor_get(v___x_3982_, 0);
v_err_4059_ = lean_ctor_get(v___x_3982_, 1);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4061_ = v___x_3982_;
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_err_4059_);
lean_inc(v_pos_4058_);
lean_dec(v___x_3982_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4064_; 
if (v_isShared_4062_ == 0)
{
v___x_4064_ = v___x_4061_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_pos_4058_);
lean_ctor_set(v_reuseFailAlloc_4065_, 1, v_err_4059_);
v___x_4064_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
return v___x_4064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader___boxed(lean_object* v_config_4067_, lean_object* v_a_4068_){
_start:
{
lean_object* v_res_4069_; 
v_res_4069_ = l_Std_Http_URI_Parser_parseHostHeader(v_config_4067_, v_a_4068_);
lean_dec_ref(v_config_4067_);
return v_res_4069_;
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
