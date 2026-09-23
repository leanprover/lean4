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
lean_ctor_set(v___x_1679_, 1, v___y_1677_);
v___x_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___y_1676_);
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
v___y_1676_ = v_pos_1707_;
v___y_1677_ = v___x_1719_;
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
v___y_1676_ = v_pos_1707_;
v___y_1677_ = v___x_1719_;
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
v___x_1869_ = lean_array_get_size(v___y_1866_);
v___x_1870_ = lean_nat_dec_le(v___y_1867_, v___x_1869_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
lean_dec(v___y_1867_);
v___x_1871_ = l_ByteArray_empty;
v___x_1872_ = lean_array_push(v___y_1866_, v___x_1871_);
v___x_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
lean_ctor_set(v___x_1873_, 1, v___y_1868_);
v___x_1874_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_1861_, v___x_1873_, v___y_1865_);
return v___x_1874_;
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1866_);
lean_dec_ref(v_config_1861_);
v___x_1875_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__0));
v___x_1876_ = l_Nat_reprFast(v___y_1867_);
v___x_1877_ = lean_string_append(v___x_1875_, v___x_1876_);
lean_dec_ref(v___x_1876_);
v___x_1878_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_1879_ = lean_string_append(v___x_1877_, v___x_1878_);
v___x_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
v___x_1881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___y_1865_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
return v___x_1881_;
}
}
v___jp_1882_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___y_1883_);
lean_ctor_set(v___x_1886_, 1, v___y_1884_);
v___x_1887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1887_, 0, v___y_1885_);
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
v___y_1883_ = v___x_1930_;
v___y_1884_ = v___x_1926_;
v___y_1885_ = v_pos_1914_;
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
v___y_1883_ = v___x_1930_;
v___y_1884_ = v___x_1926_;
v___y_1885_ = v_pos_1914_;
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
v___y_1865_ = v___x_1947_;
v___y_1866_ = v___x_1930_;
v___y_1867_ = v_maxPathSegments_1909_;
v___y_1868_ = v___x_1936_;
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
v___y_1865_ = v___x_1947_;
v___y_1866_ = v___x_1930_;
v___y_1867_ = v_maxPathSegments_1909_;
v___y_1868_ = v___x_1936_;
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
lean_object* v___y_2084_; lean_object* v_array_2087_; lean_object* v_idx_2088_; uint8_t v_isAbsolute_2089_; lean_object* v___x_2090_; lean_object* v_segments_2091_; uint8_t v_isAbsolute_2093_; lean_object* v_totalLength_2094_; lean_object* v___y_2095_; lean_object* v___y_2119_; uint8_t v___y_2120_; lean_object* v___y_2124_; uint8_t v___y_2125_; uint8_t v___y_2126_; uint8_t v___y_2128_; lean_object* v_pos_2129_; uint8_t v_res_2130_; uint8_t v___y_2133_; lean_object* v_pos_2134_; uint8_t v_res_2135_; uint8_t v___y_2141_; lean_object* v___y_2142_; uint8_t v___y_2143_; uint8_t v___y_2165_; uint8_t v___y_2166_; lean_object* v___y_2167_; uint8_t v___y_2168_; uint8_t v___y_2172_; uint8_t v___y_2173_; uint8_t v___y_2174_; lean_object* v___y_2175_; uint8_t v___y_2176_; uint8_t v___y_2178_; uint8_t v___y_2179_; lean_object* v___y_2180_; uint8_t v___y_2181_; uint8_t v___y_2184_; lean_object* v_pos_2185_; uint8_t v_res_2186_; lean_object* v_pos_2189_; lean_object* v_array_2190_; lean_object* v_idx_2191_; uint8_t v_res_2192_; uint8_t v___y_2197_; uint8_t v___y_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; 
v_array_2087_ = lean_ctor_get(v_a_2082_, 0);
lean_inc_ref(v_array_2087_);
v_idx_2088_ = lean_ctor_get(v_a_2082_, 1);
lean_inc(v_idx_2088_);
v_isAbsolute_2089_ = 0;
v___x_2090_ = lean_unsigned_to_nat(0u);
v_segments_2091_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__2));
v___x_2199_ = lean_byte_array_size(v_array_2087_);
v___x_2200_ = lean_nat_dec_lt(v_idx_2088_, v___x_2199_);
if (v___x_2200_ == 0)
{
v_pos_2189_ = v_a_2082_;
v_array_2190_ = v_array_2087_;
v_idx_2191_ = v_idx_2088_;
v_res_2192_ = v_isAbsolute_2089_;
goto v___jp_2188_;
}
else
{
uint8_t v___x_2201_; uint8_t v___y_2203_; uint8_t v___x_2253_; uint8_t v___x_2254_; 
v___x_2201_ = lean_byte_array_fget(v_array_2087_, v_idx_2088_);
v___x_2253_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_2254_ = lean_uint8_dec_le(v___x_2253_, v___x_2201_);
if (v___x_2254_ == 0)
{
goto v___jp_2248_;
}
else
{
uint8_t v___x_2255_; uint8_t v___x_2256_; 
v___x_2255_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_2256_ = lean_uint8_dec_le(v___x_2201_, v___x_2255_);
if (v___x_2256_ == 0)
{
goto v___jp_2248_;
}
else
{
v___y_2203_ = v___x_2256_;
goto v___jp_2202_;
}
}
v___jp_2202_:
{
uint8_t v___x_2204_; uint8_t v___x_2205_; 
v___x_2204_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_2205_ = lean_uint8_dec_eq(v___x_2201_, v___x_2204_);
if (v___x_2205_ == 0)
{
uint8_t v___x_2206_; uint8_t v___x_2207_; 
v___x_2206_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2207_ = lean_uint8_dec_eq(v___x_2201_, v___x_2206_);
v___y_2197_ = v___y_2203_;
v___y_2198_ = v___x_2207_;
goto v___jp_2196_;
}
else
{
v___y_2197_ = v___y_2203_;
v___y_2198_ = v___x_2205_;
goto v___jp_2196_;
}
}
v___jp_2208_:
{
uint8_t v___x_2209_; uint8_t v___x_2210_; 
v___x_2209_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_2210_ = lean_uint8_dec_eq(v___x_2201_, v___x_2209_);
if (v___x_2210_ == 0)
{
uint8_t v___x_2211_; uint8_t v___x_2212_; 
v___x_2211_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_2212_ = lean_uint8_dec_eq(v___x_2201_, v___x_2211_);
if (v___x_2212_ == 0)
{
uint8_t v___x_2213_; uint8_t v___x_2214_; 
v___x_2213_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_2214_ = lean_uint8_dec_eq(v___x_2201_, v___x_2213_);
if (v___x_2214_ == 0)
{
uint8_t v___x_2215_; uint8_t v___x_2216_; 
v___x_2215_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_2216_ = lean_uint8_dec_eq(v___x_2201_, v___x_2215_);
if (v___x_2216_ == 0)
{
uint8_t v___x_2217_; uint8_t v___x_2218_; 
v___x_2217_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_2218_ = lean_uint8_dec_eq(v___x_2201_, v___x_2217_);
if (v___x_2218_ == 0)
{
uint8_t v___x_2219_; uint8_t v___x_2220_; 
v___x_2219_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_2220_ = lean_uint8_dec_eq(v___x_2201_, v___x_2219_);
if (v___x_2220_ == 0)
{
uint8_t v___x_2221_; uint8_t v___x_2222_; 
v___x_2221_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_2222_ = lean_uint8_dec_eq(v___x_2201_, v___x_2221_);
if (v___x_2222_ == 0)
{
uint8_t v___x_2223_; uint8_t v___x_2224_; 
v___x_2223_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_2224_ = lean_uint8_dec_eq(v___x_2201_, v___x_2223_);
if (v___x_2224_ == 0)
{
uint8_t v___x_2225_; uint8_t v___x_2226_; 
v___x_2225_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_2226_ = lean_uint8_dec_eq(v___x_2201_, v___x_2225_);
if (v___x_2226_ == 0)
{
uint8_t v___x_2227_; uint8_t v___x_2228_; 
v___x_2227_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_2228_ = lean_uint8_dec_eq(v___x_2201_, v___x_2227_);
if (v___x_2228_ == 0)
{
uint8_t v___x_2229_; uint8_t v___x_2230_; 
v___x_2229_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_2230_ = lean_uint8_dec_eq(v___x_2201_, v___x_2229_);
if (v___x_2230_ == 0)
{
uint8_t v___x_2231_; uint8_t v___x_2232_; 
v___x_2231_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_2232_ = lean_uint8_dec_eq(v___x_2201_, v___x_2231_);
if (v___x_2232_ == 0)
{
uint8_t v___x_2233_; uint8_t v___x_2234_; 
v___x_2233_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_2234_ = lean_uint8_dec_eq(v___x_2201_, v___x_2233_);
if (v___x_2234_ == 0)
{
uint8_t v___x_2235_; uint8_t v___x_2236_; 
v___x_2235_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_2236_ = lean_uint8_dec_eq(v___x_2201_, v___x_2235_);
if (v___x_2236_ == 0)
{
uint8_t v___x_2237_; uint8_t v___x_2238_; 
v___x_2237_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_2238_ = lean_uint8_dec_eq(v___x_2201_, v___x_2237_);
if (v___x_2238_ == 0)
{
uint8_t v___x_2239_; uint8_t v___x_2240_; 
v___x_2239_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_2240_ = lean_uint8_dec_eq(v___x_2201_, v___x_2239_);
if (v___x_2240_ == 0)
{
uint8_t v___x_2241_; uint8_t v___x_2242_; 
v___x_2241_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_2242_ = lean_uint8_dec_eq(v___x_2201_, v___x_2241_);
v___y_2203_ = v___x_2242_;
goto v___jp_2202_;
}
else
{
v___y_2203_ = v___x_2240_;
goto v___jp_2202_;
}
}
else
{
v___y_2203_ = v___x_2238_;
goto v___jp_2202_;
}
}
else
{
v___y_2203_ = v___x_2236_;
goto v___jp_2202_;
}
}
else
{
v___y_2203_ = v___x_2234_;
goto v___jp_2202_;
}
}
else
{
v___y_2203_ = v___x_2232_;
goto v___jp_2202_;
}
}
else
{
v___y_2203_ = v___x_2230_;
goto v___jp_2202_;
}
}
else
{
v___y_2203_ = v___x_2228_;
goto v___jp_2202_;
}
}
else
{
v___y_2203_ = v___x_2226_;
goto v___jp_2202_;
}
}
else
{
v___y_2203_ = v___x_2224_;
goto v___jp_2202_;
}
}
else
{
v___y_2203_ = v___x_2222_;
goto v___jp_2202_;
}
}
else
{
v___y_2203_ = v___x_2220_;
goto v___jp_2202_;
}
}
else
{
v___y_2203_ = v___x_2218_;
goto v___jp_2202_;
}
}
else
{
v___y_2203_ = v___x_2216_;
goto v___jp_2202_;
}
}
else
{
v___y_2203_ = v___x_2214_;
goto v___jp_2202_;
}
}
else
{
v___y_2203_ = v___x_2212_;
goto v___jp_2202_;
}
}
else
{
v___y_2203_ = v___x_2210_;
goto v___jp_2202_;
}
}
v___jp_2243_:
{
uint8_t v___x_2244_; uint8_t v___x_2245_; 
v___x_2244_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_2245_ = lean_uint8_dec_le(v___x_2244_, v___x_2201_);
if (v___x_2245_ == 0)
{
goto v___jp_2208_;
}
else
{
uint8_t v___x_2246_; uint8_t v___x_2247_; 
v___x_2246_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_2247_ = lean_uint8_dec_le(v___x_2201_, v___x_2246_);
if (v___x_2247_ == 0)
{
goto v___jp_2208_;
}
else
{
v___y_2203_ = v___x_2247_;
goto v___jp_2202_;
}
}
}
v___jp_2248_:
{
uint8_t v___x_2249_; uint8_t v___x_2250_; 
v___x_2249_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_2250_ = lean_uint8_dec_le(v___x_2249_, v___x_2201_);
if (v___x_2250_ == 0)
{
goto v___jp_2243_;
}
else
{
uint8_t v___x_2251_; uint8_t v___x_2252_; 
v___x_2251_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_2252_ = lean_uint8_dec_le(v___x_2201_, v___x_2251_);
if (v___x_2252_ == 0)
{
goto v___jp_2243_;
}
else
{
v___y_2203_ = v___x_2252_;
goto v___jp_2202_;
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
v___jp_2140_:
{
lean_object* v_array_2144_; lean_object* v_idx_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; 
v_array_2144_ = lean_ctor_get(v___y_2142_, 0);
v_idx_2145_ = lean_ctor_get(v___y_2142_, 1);
v___x_2146_ = lean_byte_array_size(v_array_2144_);
v___x_2147_ = lean_nat_dec_lt(v_idx_2145_, v___x_2146_);
if (v___x_2147_ == 0)
{
v___y_2133_ = v___y_2141_;
v_pos_2134_ = v___y_2142_;
v_res_2135_ = v___y_2143_;
goto v___jp_2132_;
}
else
{
uint8_t v___x_2148_; uint8_t v___x_2149_; uint8_t v___x_2150_; 
v___x_2148_ = lean_byte_array_fget(v_array_2144_, v_idx_2145_);
v___x_2149_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2150_ = lean_uint8_dec_eq(v___x_2148_, v___x_2149_);
if (v___x_2150_ == 0)
{
v___y_2133_ = v___y_2141_;
v_pos_2134_ = v___y_2142_;
v_res_2135_ = v___y_2143_;
goto v___jp_2132_;
}
else
{
if (v___x_2147_ == 0)
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
lean_dec_ref(v_config_2079_);
v___x_2151_ = lean_box(0);
v___x_2152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___y_2142_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
return v___x_2152_;
}
else
{
lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2161_; 
lean_inc(v_idx_2145_);
lean_inc_ref(v_array_2144_);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___y_2142_);
if (v_isSharedCheck_2161_ == 0)
{
lean_object* v_unused_2162_; lean_object* v_unused_2163_; 
v_unused_2162_ = lean_ctor_get(v___y_2142_, 1);
lean_dec(v_unused_2162_);
v_unused_2163_ = lean_ctor_get(v___y_2142_, 0);
lean_dec(v_unused_2163_);
v___x_2154_ = v___y_2142_;
v_isShared_2155_ = v_isSharedCheck_2161_;
goto v_resetjp_2153_;
}
else
{
lean_dec(v___y_2142_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2161_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2156_ = lean_unsigned_to_nat(1u);
v___x_2157_ = lean_nat_add(v_idx_2145_, v___x_2156_);
lean_dec(v_idx_2145_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 1, v___x_2157_);
v___x_2159_ = v___x_2154_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_array_2144_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
v_isAbsolute_2093_ = v___x_2147_;
v_totalLength_2094_ = v___x_2156_;
v___y_2095_ = v___x_2159_;
goto v___jp_2092_;
}
}
}
}
}
}
v___jp_2164_:
{
if (v___y_2166_ == 0)
{
v___y_2141_ = v___y_2165_;
v___y_2142_ = v___y_2167_;
v___y_2143_ = v___y_2166_;
goto v___jp_2140_;
}
else
{
if (v___y_2168_ == 0)
{
v___y_2141_ = v___y_2165_;
v___y_2142_ = v___y_2167_;
v___y_2143_ = v___y_2168_;
goto v___jp_2140_;
}
else
{
lean_object* v___x_2169_; lean_object* v___x_2170_; 
lean_dec_ref(v_config_2079_);
v___x_2169_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__5));
v___x_2170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___y_2167_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
return v___x_2170_;
}
}
}
v___jp_2171_:
{
if (v___y_2172_ == 0)
{
v___y_2165_ = v___y_2173_;
v___y_2166_ = v___y_2174_;
v___y_2167_ = v___y_2175_;
v___y_2168_ = v___y_2176_;
goto v___jp_2164_;
}
else
{
v___y_2165_ = v___y_2173_;
v___y_2166_ = v___y_2174_;
v___y_2167_ = v___y_2175_;
v___y_2168_ = v___y_2172_;
goto v___jp_2164_;
}
}
v___jp_2177_:
{
if (v___y_2179_ == 0)
{
uint8_t v___x_2182_; 
v___x_2182_ = 1;
v___y_2172_ = v___y_2178_;
v___y_2173_ = v___y_2179_;
v___y_2174_ = v___y_2181_;
v___y_2175_ = v___y_2180_;
v___y_2176_ = v___x_2182_;
goto v___jp_2171_;
}
else
{
v___y_2172_ = v___y_2178_;
v___y_2173_ = v___y_2179_;
v___y_2174_ = v___y_2181_;
v___y_2175_ = v___y_2180_;
v___y_2176_ = v_isAbsolute_2089_;
goto v___jp_2171_;
}
}
v___jp_2183_:
{
if (v_allowEmpty_2081_ == 0)
{
uint8_t v___x_2187_; 
v___x_2187_ = 1;
v___y_2178_ = v_res_2186_;
v___y_2179_ = v___y_2184_;
v___y_2180_ = v_pos_2185_;
v___y_2181_ = v___x_2187_;
goto v___jp_2177_;
}
else
{
v___y_2178_ = v_res_2186_;
v___y_2179_ = v___y_2184_;
v___y_2180_ = v_pos_2185_;
v___y_2181_ = v_isAbsolute_2089_;
goto v___jp_2177_;
}
}
v___jp_2188_:
{
lean_object* v___x_2193_; uint8_t v___x_2194_; 
v___x_2193_ = lean_byte_array_size(v_array_2190_);
lean_dec_ref(v_array_2190_);
v___x_2194_ = lean_nat_dec_lt(v_idx_2191_, v___x_2193_);
lean_dec(v_idx_2191_);
if (v___x_2194_ == 0)
{
uint8_t v___x_2195_; 
v___x_2195_ = 1;
v___y_2184_ = v_res_2192_;
v_pos_2185_ = v_pos_2189_;
v_res_2186_ = v___x_2195_;
goto v___jp_2183_;
}
else
{
v___y_2184_ = v_res_2192_;
v_pos_2185_ = v_pos_2189_;
v_res_2186_ = v_isAbsolute_2089_;
goto v___jp_2183_;
}
}
v___jp_2196_:
{
if (v___y_2197_ == 0)
{
if (v___y_2198_ == 0)
{
v_pos_2189_ = v_a_2082_;
v_array_2190_ = v_array_2087_;
v_idx_2191_ = v_idx_2088_;
v_res_2192_ = v_isAbsolute_2089_;
goto v___jp_2188_;
}
else
{
v_pos_2189_ = v_a_2082_;
v_array_2190_ = v_array_2087_;
v_idx_2191_ = v_idx_2088_;
v_res_2192_ = v___y_2198_;
goto v___jp_2188_;
}
}
else
{
v_pos_2189_ = v_a_2082_;
v_array_2190_ = v_array_2087_;
v_idx_2191_ = v_idx_2088_;
v_res_2192_ = v___y_2197_;
goto v___jp_2188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath___boxed(lean_object* v_config_2257_, lean_object* v_forceAbsolute_2258_, lean_object* v_allowEmpty_2259_, lean_object* v_a_2260_){
_start:
{
uint8_t v_forceAbsolute_boxed_2261_; uint8_t v_allowEmpty_boxed_2262_; lean_object* v_res_2263_; 
v_forceAbsolute_boxed_2261_ = lean_unbox(v_forceAbsolute_2258_);
v_allowEmpty_boxed_2262_ = lean_unbox(v_allowEmpty_2259_);
v_res_2263_ = l_Std_Http_URI_Parser_parsePath(v_config_2257_, v_forceAbsolute_boxed_2261_, v_allowEmpty_boxed_2262_, v_a_2260_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0(lean_object* v_config_2264_, lean_object* v_inst_2265_, lean_object* v_a_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l___private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0___redArg(v_config_2264_, v_a_2266_, v___y_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(lean_object* v_config_2269_, lean_object* v_inst_2270_, lean_object* v_a_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg(v_config_2269_, v_a_2271_, v___y_2272_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg(){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg___boxed(lean_object* v___dummy_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg();
return v_res_2277_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___redArg();
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(lean_object* v_s_2279_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___boxed(lean_object* v_s_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(v_s_2281_);
lean_dec_ref(v_s_2281_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg(){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___redArg___closed__0));
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg___boxed(lean_object* v___dummy_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg();
return v_res_2286_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2287_; 
v___x_2287_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___redArg();
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(lean_object* v_s_2288_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___boxed(lean_object* v_s_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v_s_2290_);
lean_dec_ref(v_s_2290_);
return v_res_2291_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(uint8_t v_c_2292_){
_start:
{
uint8_t v___y_2294_; uint8_t v___x_2346_; uint8_t v___x_2347_; 
v___x_2346_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_2347_ = lean_uint8_dec_le(v___x_2346_, v_c_2292_);
if (v___x_2347_ == 0)
{
goto v___jp_2341_;
}
else
{
uint8_t v___x_2348_; uint8_t v___x_2349_; 
v___x_2348_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_2349_ = lean_uint8_dec_le(v_c_2292_, v___x_2348_);
if (v___x_2349_ == 0)
{
goto v___jp_2341_;
}
else
{
v___y_2294_ = v___x_2349_;
goto v___jp_2293_;
}
}
v___jp_2293_:
{
if (v___y_2294_ == 0)
{
uint8_t v___x_2295_; uint8_t v___x_2296_; 
v___x_2295_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_2296_ = lean_uint8_dec_eq(v_c_2292_, v___x_2295_);
return v___x_2296_;
}
else
{
return v___y_2294_;
}
}
v___jp_2297_:
{
uint8_t v___x_2298_; uint8_t v___x_2299_; 
v___x_2298_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_2299_ = lean_uint8_dec_eq(v_c_2292_, v___x_2298_);
if (v___x_2299_ == 0)
{
uint8_t v___x_2300_; uint8_t v___x_2301_; 
v___x_2300_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_2301_ = lean_uint8_dec_eq(v_c_2292_, v___x_2300_);
if (v___x_2301_ == 0)
{
uint8_t v___x_2302_; uint8_t v___x_2303_; 
v___x_2302_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_2303_ = lean_uint8_dec_eq(v_c_2292_, v___x_2302_);
if (v___x_2303_ == 0)
{
uint8_t v___x_2304_; uint8_t v___x_2305_; 
v___x_2304_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_2305_ = lean_uint8_dec_eq(v_c_2292_, v___x_2304_);
if (v___x_2305_ == 0)
{
uint8_t v___x_2306_; uint8_t v___x_2307_; 
v___x_2306_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_2307_ = lean_uint8_dec_eq(v_c_2292_, v___x_2306_);
if (v___x_2307_ == 0)
{
uint8_t v___x_2308_; uint8_t v___x_2309_; 
v___x_2308_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_2309_ = lean_uint8_dec_eq(v_c_2292_, v___x_2308_);
if (v___x_2309_ == 0)
{
uint8_t v___x_2310_; uint8_t v___x_2311_; 
v___x_2310_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_2311_ = lean_uint8_dec_eq(v_c_2292_, v___x_2310_);
if (v___x_2311_ == 0)
{
uint8_t v___x_2312_; uint8_t v___x_2313_; 
v___x_2312_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_2313_ = lean_uint8_dec_eq(v_c_2292_, v___x_2312_);
if (v___x_2313_ == 0)
{
uint8_t v___x_2314_; uint8_t v___x_2315_; 
v___x_2314_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_2315_ = lean_uint8_dec_eq(v_c_2292_, v___x_2314_);
if (v___x_2315_ == 0)
{
uint8_t v___x_2316_; uint8_t v___x_2317_; 
v___x_2316_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_2317_ = lean_uint8_dec_eq(v_c_2292_, v___x_2316_);
if (v___x_2317_ == 0)
{
uint8_t v___x_2318_; uint8_t v___x_2319_; 
v___x_2318_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_2319_ = lean_uint8_dec_eq(v_c_2292_, v___x_2318_);
if (v___x_2319_ == 0)
{
uint8_t v___x_2320_; uint8_t v___x_2321_; 
v___x_2320_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_2321_ = lean_uint8_dec_eq(v_c_2292_, v___x_2320_);
if (v___x_2321_ == 0)
{
uint8_t v___x_2322_; uint8_t v___x_2323_; 
v___x_2322_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_2323_ = lean_uint8_dec_eq(v_c_2292_, v___x_2322_);
if (v___x_2323_ == 0)
{
uint8_t v___x_2324_; uint8_t v___x_2325_; 
v___x_2324_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_2325_ = lean_uint8_dec_eq(v_c_2292_, v___x_2324_);
if (v___x_2325_ == 0)
{
uint8_t v___x_2326_; uint8_t v___x_2327_; 
v___x_2326_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_2327_ = lean_uint8_dec_eq(v_c_2292_, v___x_2326_);
if (v___x_2327_ == 0)
{
uint8_t v___x_2328_; uint8_t v___x_2329_; 
v___x_2328_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_2329_ = lean_uint8_dec_eq(v_c_2292_, v___x_2328_);
if (v___x_2329_ == 0)
{
uint8_t v___x_2330_; uint8_t v___x_2331_; 
v___x_2330_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_2331_ = lean_uint8_dec_eq(v_c_2292_, v___x_2330_);
if (v___x_2331_ == 0)
{
uint8_t v___x_2332_; uint8_t v___x_2333_; 
v___x_2332_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2333_ = lean_uint8_dec_eq(v_c_2292_, v___x_2332_);
if (v___x_2333_ == 0)
{
uint8_t v___x_2334_; uint8_t v___x_2335_; 
v___x_2334_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_2335_ = lean_uint8_dec_eq(v_c_2292_, v___x_2334_);
v___y_2294_ = v___x_2335_;
goto v___jp_2293_;
}
else
{
v___y_2294_ = v___x_2333_;
goto v___jp_2293_;
}
}
else
{
v___y_2294_ = v___x_2331_;
goto v___jp_2293_;
}
}
else
{
v___y_2294_ = v___x_2329_;
goto v___jp_2293_;
}
}
else
{
v___y_2294_ = v___x_2327_;
goto v___jp_2293_;
}
}
else
{
v___y_2294_ = v___x_2325_;
goto v___jp_2293_;
}
}
else
{
v___y_2294_ = v___x_2323_;
goto v___jp_2293_;
}
}
else
{
v___y_2294_ = v___x_2321_;
goto v___jp_2293_;
}
}
else
{
v___y_2294_ = v___x_2319_;
goto v___jp_2293_;
}
}
else
{
v___y_2294_ = v___x_2317_;
goto v___jp_2293_;
}
}
else
{
v___y_2294_ = v___x_2315_;
goto v___jp_2293_;
}
}
else
{
v___y_2294_ = v___x_2313_;
goto v___jp_2293_;
}
}
else
{
v___y_2294_ = v___x_2311_;
goto v___jp_2293_;
}
}
else
{
v___y_2294_ = v___x_2309_;
goto v___jp_2293_;
}
}
else
{
v___y_2294_ = v___x_2307_;
goto v___jp_2293_;
}
}
else
{
v___y_2294_ = v___x_2305_;
goto v___jp_2293_;
}
}
else
{
v___y_2294_ = v___x_2303_;
goto v___jp_2293_;
}
}
else
{
v___y_2294_ = v___x_2301_;
goto v___jp_2293_;
}
}
else
{
v___y_2294_ = v___x_2299_;
goto v___jp_2293_;
}
}
v___jp_2336_:
{
uint8_t v___x_2337_; uint8_t v___x_2338_; 
v___x_2337_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_2338_ = lean_uint8_dec_le(v___x_2337_, v_c_2292_);
if (v___x_2338_ == 0)
{
goto v___jp_2297_;
}
else
{
uint8_t v___x_2339_; uint8_t v___x_2340_; 
v___x_2339_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__4);
v___x_2340_ = lean_uint8_dec_le(v_c_2292_, v___x_2339_);
if (v___x_2340_ == 0)
{
goto v___jp_2297_;
}
else
{
v___y_2294_ = v___x_2340_;
goto v___jp_2293_;
}
}
}
v___jp_2341_:
{
uint8_t v___x_2342_; uint8_t v___x_2343_; 
v___x_2342_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__5);
v___x_2343_ = lean_uint8_dec_le(v___x_2342_, v_c_2292_);
if (v___x_2343_ == 0)
{
goto v___jp_2336_;
}
else
{
uint8_t v___x_2344_; uint8_t v___x_2345_; 
v___x_2344_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__6);
v___x_2345_ = lean_uint8_dec_le(v_c_2292_, v___x_2344_);
if (v___x_2345_ == 0)
{
goto v___jp_2336_;
}
else
{
v___y_2294_ = v___x_2345_;
goto v___jp_2293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed(lean_object* v_c_2350_){
_start:
{
uint8_t v_c_boxed_2351_; uint8_t v_res_2352_; lean_object* v_r_2353_; 
v_c_boxed_2351_ = lean_unbox(v_c_2350_);
v_res_2352_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(v_c_boxed_2351_);
v_r_2353_ = lean_box(v_res_2352_);
return v_r_2353_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(lean_object* v___x_2354_, lean_object* v___x_2355_, lean_object* v_a_2356_, lean_object* v_b_2357_){
_start:
{
lean_object* v_it_2359_; 
if (lean_obj_tag(v_a_2356_) == 0)
{
lean_object* v_currPos_2363_; lean_object* v_searcher_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2390_; 
v_currPos_2363_ = lean_ctor_get(v_a_2356_, 0);
v_searcher_2364_ = lean_ctor_get(v_a_2356_, 1);
v_isSharedCheck_2390_ = !lean_is_exclusive(v_a_2356_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2366_ = v_a_2356_;
v_isShared_2367_ = v_isSharedCheck_2390_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_searcher_2364_);
lean_inc(v_currPos_2363_);
lean_dec(v_a_2356_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2390_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v_str_2368_; lean_object* v_startInclusive_2369_; lean_object* v_endExclusive_2370_; lean_object* v___x_2371_; uint8_t v_decide_2372_; 
v_str_2368_ = lean_ctor_get(v___x_2354_, 0);
v_startInclusive_2369_ = lean_ctor_get(v___x_2354_, 1);
v_endExclusive_2370_ = lean_ctor_get(v___x_2354_, 2);
v___x_2371_ = lean_nat_sub(v_endExclusive_2370_, v_startInclusive_2369_);
v_decide_2372_ = lean_nat_dec_eq(v_searcher_2364_, v___x_2371_);
lean_dec(v___x_2371_);
if (v_decide_2372_ == 0)
{
uint32_t v___x_2373_; lean_object* v___x_2374_; uint32_t v___x_2375_; uint8_t v___x_2376_; 
v___x_2373_ = 38;
v___x_2374_ = lean_nat_add(v_startInclusive_2369_, v_searcher_2364_);
v___x_2375_ = lean_string_utf8_get_fast(v_str_2368_, v___x_2374_);
v___x_2376_ = lean_uint32_dec_eq(v___x_2375_, v___x_2373_);
if (v___x_2376_ == 0)
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2380_; 
lean_dec(v_searcher_2364_);
v___x_2377_ = lean_string_utf8_next_fast(v_str_2368_, v___x_2374_);
lean_dec(v___x_2374_);
v___x_2378_ = lean_nat_sub(v___x_2377_, v_startInclusive_2369_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 1, v___x_2378_);
v___x_2380_ = v___x_2366_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_currPos_2363_);
lean_ctor_set(v_reuseFailAlloc_2382_, 1, v___x_2378_);
v___x_2380_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
v_a_2356_ = v___x_2380_;
goto _start;
}
}
else
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v_nextIt_2387_; 
lean_dec(v_currPos_2363_);
v___x_2383_ = lean_string_utf8_next_fast(v_str_2368_, v___x_2374_);
v___x_2384_ = lean_nat_sub(v___x_2383_, v___x_2374_);
lean_dec(v___x_2374_);
v___x_2385_ = lean_nat_add(v_searcher_2364_, v___x_2384_);
lean_dec(v___x_2384_);
lean_dec(v_searcher_2364_);
lean_inc(v___x_2385_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 1, v___x_2385_);
lean_ctor_set(v___x_2366_, 0, v___x_2385_);
v_nextIt_2387_ = v___x_2366_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v___x_2385_);
v_nextIt_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
v_it_2359_ = v_nextIt_2387_;
goto v___jp_2358_;
}
}
}
else
{
lean_object* v___x_2389_; 
lean_del_object(v___x_2366_);
lean_dec(v_searcher_2364_);
lean_dec(v_currPos_2363_);
v___x_2389_ = lean_box(1);
v_it_2359_ = v___x_2389_;
goto v___jp_2358_;
}
}
}
else
{
return v_b_2357_;
}
v___jp_2358_:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = lean_unsigned_to_nat(1u);
v___x_2361_ = lean_nat_add(v_b_2357_, v___x_2360_);
lean_dec(v_b_2357_);
v_a_2356_ = v_it_2359_;
v_b_2357_ = v___x_2361_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg___boxed(lean_object* v___x_2391_, lean_object* v___x_2392_, lean_object* v_a_2393_, lean_object* v_b_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2391_, v___x_2392_, v_a_2393_, v_b_2394_);
lean_dec(v___x_2392_);
lean_dec_ref(v___x_2391_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(lean_object* v___x_2396_, lean_object* v___x_2397_, lean_object* v___x_2398_, lean_object* v_a_2399_, lean_object* v_b_2400_){
_start:
{
lean_object* v_it_2402_; 
if (lean_obj_tag(v_a_2399_) == 0)
{
lean_object* v_currPos_2406_; lean_object* v_searcher_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2433_; 
v_currPos_2406_ = lean_ctor_get(v_a_2399_, 0);
v_searcher_2407_ = lean_ctor_get(v_a_2399_, 1);
v_isSharedCheck_2433_ = !lean_is_exclusive(v_a_2399_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2409_ = v_a_2399_;
v_isShared_2410_ = v_isSharedCheck_2433_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_searcher_2407_);
lean_inc(v_currPos_2406_);
lean_dec(v_a_2399_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2433_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v_str_2411_; lean_object* v_startInclusive_2412_; lean_object* v_endExclusive_2413_; lean_object* v___x_2414_; uint8_t v_decide_2415_; 
v_str_2411_ = lean_ctor_get(v___x_2397_, 0);
v_startInclusive_2412_ = lean_ctor_get(v___x_2397_, 1);
v_endExclusive_2413_ = lean_ctor_get(v___x_2397_, 2);
v___x_2414_ = lean_nat_sub(v_endExclusive_2413_, v_startInclusive_2412_);
v_decide_2415_ = lean_nat_dec_eq(v_searcher_2407_, v___x_2414_);
lean_dec(v___x_2414_);
if (v_decide_2415_ == 0)
{
lean_object* v___x_2416_; uint32_t v___x_2417_; uint32_t v___x_2418_; uint8_t v___x_2419_; 
v___x_2416_ = lean_nat_add(v_startInclusive_2412_, v_searcher_2407_);
v___x_2417_ = lean_string_utf8_get_fast(v_str_2411_, v___x_2416_);
v___x_2418_ = 38;
v___x_2419_ = lean_uint32_dec_eq(v___x_2417_, v___x_2418_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2423_; 
lean_dec(v_searcher_2407_);
v___x_2420_ = lean_string_utf8_next_fast(v_str_2411_, v___x_2416_);
lean_dec(v___x_2416_);
v___x_2421_ = lean_nat_sub(v___x_2420_, v_startInclusive_2412_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 1, v___x_2421_);
v___x_2423_ = v___x_2409_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_currPos_2406_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v___x_2421_);
v___x_2423_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2397_, v___x_2398_, v___x_2423_, v_b_2400_);
return v___x_2424_;
}
}
else
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v_nextIt_2430_; 
lean_dec(v_currPos_2406_);
v___x_2426_ = lean_string_utf8_next_fast(v_str_2411_, v___x_2416_);
v___x_2427_ = lean_nat_sub(v___x_2426_, v___x_2416_);
lean_dec(v___x_2416_);
v___x_2428_ = lean_nat_add(v_searcher_2407_, v___x_2427_);
lean_dec(v___x_2427_);
lean_dec(v_searcher_2407_);
lean_inc(v___x_2428_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 1, v___x_2428_);
lean_ctor_set(v___x_2409_, 0, v___x_2428_);
v_nextIt_2430_ = v___x_2409_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
lean_ctor_set(v_reuseFailAlloc_2431_, 1, v___x_2428_);
v_nextIt_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
v_it_2402_ = v_nextIt_2430_;
goto v___jp_2401_;
}
}
}
else
{
lean_object* v___x_2432_; 
lean_del_object(v___x_2409_);
lean_dec(v_searcher_2407_);
lean_dec(v_currPos_2406_);
v___x_2432_ = lean_box(1);
v_it_2402_ = v___x_2432_;
goto v___jp_2401_;
}
}
}
else
{
return v_b_2400_;
}
v___jp_2401_:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2403_ = lean_unsigned_to_nat(1u);
v___x_2404_ = lean_nat_add(v_b_2400_, v___x_2403_);
lean_dec(v_b_2400_);
v___x_2405_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2397_, v___x_2398_, v_it_2402_, v___x_2404_);
return v___x_2405_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg___boxed(lean_object* v___x_2434_, lean_object* v___x_2435_, lean_object* v___x_2436_, lean_object* v_a_2437_, lean_object* v_b_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2434_, v___x_2435_, v___x_2436_, v_a_2437_, v_b_2438_);
lean_dec(v___x_2436_);
lean_dec_ref(v___x_2435_);
lean_dec_ref(v___x_2434_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(lean_object* v_out_2440_, lean_object* v_a_2441_, lean_object* v_b_2442_){
_start:
{
if (lean_obj_tag(v_a_2441_) == 0)
{
lean_object* v_currPos_2443_; lean_object* v_searcher_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2483_; 
v_currPos_2443_ = lean_ctor_get(v_a_2441_, 0);
v_searcher_2444_ = lean_ctor_get(v_a_2441_, 1);
v_isSharedCheck_2483_ = !lean_is_exclusive(v_a_2441_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2446_ = v_a_2441_;
v_isShared_2447_ = v_isSharedCheck_2483_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_searcher_2444_);
lean_inc(v_currPos_2443_);
lean_dec(v_a_2441_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2483_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v_str_2448_; lean_object* v_startInclusive_2449_; lean_object* v_endExclusive_2450_; lean_object* v_it_2452_; lean_object* v_startInclusive_2453_; lean_object* v_endExclusive_2454_; lean_object* v___x_2461_; uint8_t v_decide_2462_; 
v_str_2448_ = lean_ctor_get(v_out_2440_, 0);
v_startInclusive_2449_ = lean_ctor_get(v_out_2440_, 1);
v_endExclusive_2450_ = lean_ctor_get(v_out_2440_, 2);
v___x_2461_ = lean_nat_sub(v_endExclusive_2450_, v_startInclusive_2449_);
v_decide_2462_ = lean_nat_dec_eq(v_searcher_2444_, v___x_2461_);
if (v_decide_2462_ == 0)
{
uint32_t v___x_2463_; lean_object* v___x_2464_; uint32_t v___x_2465_; uint8_t v___x_2466_; 
lean_dec(v___x_2461_);
v___x_2463_ = 61;
v___x_2464_ = lean_nat_add(v_startInclusive_2449_, v_searcher_2444_);
v___x_2465_ = lean_string_utf8_get_fast(v_str_2448_, v___x_2464_);
v___x_2466_ = lean_uint32_dec_eq(v___x_2465_, v___x_2463_);
if (v___x_2466_ == 0)
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2470_; 
lean_dec(v_searcher_2444_);
v___x_2467_ = lean_string_utf8_next_fast(v_str_2448_, v___x_2464_);
lean_dec(v___x_2464_);
v___x_2468_ = lean_nat_sub(v___x_2467_, v_startInclusive_2449_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 1, v___x_2468_);
v___x_2470_ = v___x_2446_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_currPos_2443_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
v_a_2441_ = v___x_2470_;
goto _start;
}
}
else
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v_slice_2476_; lean_object* v_nextIt_2478_; 
v___x_2473_ = lean_string_utf8_next_fast(v_str_2448_, v___x_2464_);
v___x_2474_ = lean_nat_sub(v___x_2473_, v___x_2464_);
lean_dec(v___x_2464_);
v___x_2475_ = lean_nat_add(v_searcher_2444_, v___x_2474_);
lean_dec(v___x_2474_);
v_slice_2476_ = l_String_Slice_subslice_x21(v_out_2440_, v_currPos_2443_, v_searcher_2444_);
lean_inc(v___x_2475_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 1, v___x_2475_);
lean_ctor_set(v___x_2446_, 0, v___x_2475_);
v_nextIt_2478_ = v___x_2446_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2481_, 1, v___x_2475_);
v_nextIt_2478_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
lean_object* v_startInclusive_2479_; lean_object* v_endExclusive_2480_; 
v_startInclusive_2479_ = lean_ctor_get(v_slice_2476_, 0);
lean_inc(v_startInclusive_2479_);
v_endExclusive_2480_ = lean_ctor_get(v_slice_2476_, 1);
lean_inc(v_endExclusive_2480_);
lean_dec_ref(v_slice_2476_);
v_it_2452_ = v_nextIt_2478_;
v_startInclusive_2453_ = v_startInclusive_2479_;
v_endExclusive_2454_ = v_endExclusive_2480_;
goto v___jp_2451_;
}
}
}
else
{
lean_object* v___x_2482_; 
lean_del_object(v___x_2446_);
lean_dec(v_searcher_2444_);
v___x_2482_ = lean_box(1);
v_it_2452_ = v___x_2482_;
v_startInclusive_2453_ = v_currPos_2443_;
v_endExclusive_2454_ = v___x_2461_;
goto v___jp_2451_;
}
v___jp_2451_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2455_ = lean_nat_add(v_startInclusive_2449_, v_startInclusive_2453_);
lean_dec(v_startInclusive_2453_);
v___x_2456_ = lean_nat_add(v_startInclusive_2449_, v_endExclusive_2454_);
lean_dec(v_endExclusive_2454_);
lean_inc_ref(v_str_2448_);
v___x_2457_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2457_, 0, v_str_2448_);
lean_ctor_set(v___x_2457_, 1, v___x_2455_);
lean_ctor_set(v___x_2457_, 2, v___x_2456_);
v___x_2458_ = l_String_Slice_toString(v___x_2457_);
lean_dec_ref_known(v___x_2457_, 3);
v___x_2459_ = lean_array_push(v_b_2442_, v___x_2458_);
v_a_2441_ = v_it_2452_;
v_b_2442_ = v___x_2459_;
goto _start;
}
}
}
else
{
return v_b_2442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg___boxed(lean_object* v_out_2484_, lean_object* v_a_2485_, lean_object* v_b_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2484_, v_a_2485_, v_b_2486_);
lean_dec_ref(v_out_2484_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(lean_object* v___x_2491_, lean_object* v___x_2492_, lean_object* v___x_2493_, lean_object* v_a_2494_, lean_object* v_b_2495_){
_start:
{
lean_object* v_it_2497_; lean_object* v_startInclusive_2498_; lean_object* v_endExclusive_2499_; 
if (lean_obj_tag(v_a_2494_) == 0)
{
lean_object* v_currPos_2524_; lean_object* v_searcher_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2554_; 
v_currPos_2524_ = lean_ctor_get(v_a_2494_, 0);
v_searcher_2525_ = lean_ctor_get(v_a_2494_, 1);
v_isSharedCheck_2554_ = !lean_is_exclusive(v_a_2494_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2527_ = v_a_2494_;
v_isShared_2528_ = v_isSharedCheck_2554_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_searcher_2525_);
lean_inc(v_currPos_2524_);
lean_dec(v_a_2494_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2554_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v_str_2529_; lean_object* v_startInclusive_2530_; lean_object* v_endExclusive_2531_; lean_object* v___x_2532_; uint8_t v_decide_2533_; 
v_str_2529_ = lean_ctor_get(v___x_2492_, 0);
v_startInclusive_2530_ = lean_ctor_get(v___x_2492_, 1);
v_endExclusive_2531_ = lean_ctor_get(v___x_2492_, 2);
v___x_2532_ = lean_nat_sub(v_endExclusive_2531_, v_startInclusive_2530_);
v_decide_2533_ = lean_nat_dec_eq(v_searcher_2525_, v___x_2532_);
lean_dec(v___x_2532_);
if (v_decide_2533_ == 0)
{
uint32_t v___x_2534_; lean_object* v___x_2535_; uint32_t v___x_2536_; uint8_t v___x_2537_; 
v___x_2534_ = 38;
v___x_2535_ = lean_nat_add(v_startInclusive_2530_, v_searcher_2525_);
v___x_2536_ = lean_string_utf8_get_fast(v_str_2529_, v___x_2535_);
v___x_2537_ = lean_uint32_dec_eq(v___x_2536_, v___x_2534_);
if (v___x_2537_ == 0)
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2541_; 
lean_dec(v_searcher_2525_);
v___x_2538_ = lean_string_utf8_next_fast(v_str_2529_, v___x_2535_);
lean_dec(v___x_2535_);
v___x_2539_ = lean_nat_sub(v___x_2538_, v_startInclusive_2530_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 1, v___x_2539_);
v___x_2541_ = v___x_2527_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_currPos_2524_);
lean_ctor_set(v_reuseFailAlloc_2543_, 1, v___x_2539_);
v___x_2541_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
v_a_2494_ = v___x_2541_;
goto _start;
}
}
else
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v_slice_2547_; lean_object* v_nextIt_2549_; 
v___x_2544_ = lean_string_utf8_next_fast(v_str_2529_, v___x_2535_);
v___x_2545_ = lean_nat_sub(v___x_2544_, v___x_2535_);
lean_dec(v___x_2535_);
v___x_2546_ = lean_nat_add(v_searcher_2525_, v___x_2545_);
lean_dec(v___x_2545_);
v_slice_2547_ = l_String_Slice_subslice_x21(v___x_2492_, v_currPos_2524_, v_searcher_2525_);
lean_inc(v___x_2546_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 1, v___x_2546_);
lean_ctor_set(v___x_2527_, 0, v___x_2546_);
v_nextIt_2549_ = v___x_2527_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2546_);
lean_ctor_set(v_reuseFailAlloc_2552_, 1, v___x_2546_);
v_nextIt_2549_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v_startInclusive_2550_; lean_object* v_endExclusive_2551_; 
v_startInclusive_2550_ = lean_ctor_get(v_slice_2547_, 0);
lean_inc(v_startInclusive_2550_);
v_endExclusive_2551_ = lean_ctor_get(v_slice_2547_, 1);
lean_inc(v_endExclusive_2551_);
lean_dec_ref(v_slice_2547_);
v_it_2497_ = v_nextIt_2549_;
v_startInclusive_2498_ = v_startInclusive_2550_;
v_endExclusive_2499_ = v_endExclusive_2551_;
goto v___jp_2496_;
}
}
}
else
{
lean_object* v___x_2553_; 
lean_del_object(v___x_2527_);
lean_dec(v_searcher_2525_);
v___x_2553_ = lean_box(1);
lean_inc(v___x_2493_);
v_it_2497_ = v___x_2553_;
v_startInclusive_2498_ = v_currPos_2524_;
v_endExclusive_2499_ = v___x_2493_;
goto v___jp_2496_;
}
}
}
else
{
lean_object* v___x_2555_; 
lean_dec(v___x_2493_);
lean_dec_ref(v___x_2491_);
v___x_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2555_, 0, v_b_2495_);
return v___x_2555_;
}
v___jp_2496_:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
lean_inc_ref(v___x_2491_);
v___x_2500_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2491_);
lean_ctor_set(v___x_2500_, 1, v_startInclusive_2498_);
lean_ctor_set(v___x_2500_, 2, v_endExclusive_2499_);
v___x_2501_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
v___x_2502_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2503_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2500_, v___x_2501_, v___x_2502_);
lean_dec_ref_known(v___x_2500_, 3);
v___x_2504_ = lean_array_to_list(v___x_2503_);
if (lean_obj_tag(v___x_2504_) == 0)
{
v_a_2494_ = v_it_2497_;
goto _start;
}
else
{
lean_object* v_tail_2506_; 
v_tail_2506_ = lean_ctor_get(v___x_2504_, 1);
lean_inc(v_tail_2506_);
if (lean_obj_tag(v_tail_2506_) == 0)
{
lean_object* v_head_2507_; lean_object* v___x_2508_; 
v_head_2507_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_head_2507_);
lean_dec_ref_known(v___x_2504_, 2);
v___x_2508_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2507_);
lean_dec(v_head_2507_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v___x_2509_; 
lean_dec(v_it_2497_);
lean_dec_ref(v_b_2495_);
lean_dec(v___x_2493_);
lean_dec_ref(v___x_2491_);
v___x_2509_ = lean_box(0);
return v___x_2509_;
}
else
{
lean_object* v_val_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v_val_2510_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_val_2510_);
lean_dec_ref_known(v___x_2508_, 1);
v___x_2511_ = lean_box(0);
v___x_2512_ = l_Std_Http_URI_Query_insertEncoded(v_b_2495_, v_val_2510_, v___x_2511_);
v_a_2494_ = v_it_2497_;
v_b_2495_ = v___x_2512_;
goto _start;
}
}
else
{
lean_object* v_head_2514_; lean_object* v___x_2515_; 
v_head_2514_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_head_2514_);
lean_dec_ref_known(v___x_2504_, 2);
v___x_2515_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2514_);
lean_dec(v_head_2514_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v___x_2516_; 
lean_dec(v_tail_2506_);
lean_dec(v_it_2497_);
lean_dec_ref(v_b_2495_);
lean_dec(v___x_2493_);
lean_dec_ref(v___x_2491_);
v___x_2516_ = lean_box(0);
return v___x_2516_;
}
else
{
lean_object* v_val_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v_val_2517_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_val_2517_);
lean_dec_ref_known(v___x_2515_, 1);
v___x_2518_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2519_ = l_String_intercalate(v___x_2518_, v_tail_2506_);
v___x_2520_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2519_);
lean_dec_ref(v___x_2519_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v___x_2521_; 
lean_dec(v_val_2517_);
lean_dec(v_it_2497_);
lean_dec_ref(v_b_2495_);
lean_dec(v___x_2493_);
lean_dec_ref(v___x_2491_);
v___x_2521_ = lean_box(0);
return v___x_2521_;
}
else
{
lean_object* v___x_2522_; 
v___x_2522_ = l_Std_Http_URI_Query_insertEncoded(v_b_2495_, v_val_2517_, v___x_2520_);
v_a_2494_ = v_it_2497_;
v_b_2495_ = v___x_2522_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___boxed(lean_object* v___x_2556_, lean_object* v___x_2557_, lean_object* v___x_2558_, lean_object* v_a_2559_, lean_object* v_b_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2556_, v___x_2557_, v___x_2558_, v_a_2559_, v_b_2560_);
lean_dec_ref(v___x_2557_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(lean_object* v___x_2562_, lean_object* v___x_2563_, lean_object* v___x_2564_, lean_object* v_a_2565_, lean_object* v_b_2566_){
_start:
{
lean_object* v_it_2568_; lean_object* v_startInclusive_2569_; lean_object* v_endExclusive_2570_; 
if (lean_obj_tag(v_a_2565_) == 0)
{
lean_object* v_currPos_2595_; lean_object* v_searcher_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2625_; 
v_currPos_2595_ = lean_ctor_get(v_a_2565_, 0);
v_searcher_2596_ = lean_ctor_get(v_a_2565_, 1);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_a_2565_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2598_ = v_a_2565_;
v_isShared_2599_ = v_isSharedCheck_2625_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_searcher_2596_);
lean_inc(v_currPos_2595_);
lean_dec(v_a_2565_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2625_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v_str_2600_; lean_object* v_startInclusive_2601_; lean_object* v_endExclusive_2602_; lean_object* v___x_2603_; uint8_t v_decide_2604_; 
v_str_2600_ = lean_ctor_get(v___x_2563_, 0);
v_startInclusive_2601_ = lean_ctor_get(v___x_2563_, 1);
v_endExclusive_2602_ = lean_ctor_get(v___x_2563_, 2);
v___x_2603_ = lean_nat_sub(v_endExclusive_2602_, v_startInclusive_2601_);
v_decide_2604_ = lean_nat_dec_eq(v_searcher_2596_, v___x_2603_);
lean_dec(v___x_2603_);
if (v_decide_2604_ == 0)
{
lean_object* v___x_2605_; uint32_t v___x_2606_; uint32_t v___x_2607_; uint8_t v___x_2608_; 
v___x_2605_ = lean_nat_add(v_startInclusive_2601_, v_searcher_2596_);
v___x_2606_ = lean_string_utf8_get_fast(v_str_2600_, v___x_2605_);
v___x_2607_ = 38;
v___x_2608_ = lean_uint32_dec_eq(v___x_2606_, v___x_2607_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2612_; 
lean_dec(v_searcher_2596_);
v___x_2609_ = lean_string_utf8_next_fast(v_str_2600_, v___x_2605_);
lean_dec(v___x_2605_);
v___x_2610_ = lean_nat_sub(v___x_2609_, v_startInclusive_2601_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 1, v___x_2610_);
v___x_2612_ = v___x_2598_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_currPos_2595_);
lean_ctor_set(v_reuseFailAlloc_2614_, 1, v___x_2610_);
v___x_2612_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
lean_object* v___x_2613_; 
v___x_2613_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2562_, v___x_2563_, v___x_2564_, v___x_2612_, v_b_2566_);
return v___x_2613_;
}
}
else
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v_slice_2618_; lean_object* v_nextIt_2620_; 
v___x_2615_ = lean_string_utf8_next_fast(v_str_2600_, v___x_2605_);
v___x_2616_ = lean_nat_sub(v___x_2615_, v___x_2605_);
lean_dec(v___x_2605_);
v___x_2617_ = lean_nat_add(v_searcher_2596_, v___x_2616_);
lean_dec(v___x_2616_);
v_slice_2618_ = l_String_Slice_subslice_x21(v___x_2563_, v_currPos_2595_, v_searcher_2596_);
lean_inc(v___x_2617_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 1, v___x_2617_);
lean_ctor_set(v___x_2598_, 0, v___x_2617_);
v_nextIt_2620_ = v___x_2598_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2617_);
lean_ctor_set(v_reuseFailAlloc_2623_, 1, v___x_2617_);
v_nextIt_2620_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
lean_object* v_startInclusive_2621_; lean_object* v_endExclusive_2622_; 
v_startInclusive_2621_ = lean_ctor_get(v_slice_2618_, 0);
lean_inc(v_startInclusive_2621_);
v_endExclusive_2622_ = lean_ctor_get(v_slice_2618_, 1);
lean_inc(v_endExclusive_2622_);
lean_dec_ref(v_slice_2618_);
v_it_2568_ = v_nextIt_2620_;
v_startInclusive_2569_ = v_startInclusive_2621_;
v_endExclusive_2570_ = v_endExclusive_2622_;
goto v___jp_2567_;
}
}
}
else
{
lean_object* v___x_2624_; 
lean_del_object(v___x_2598_);
lean_dec(v_searcher_2596_);
v___x_2624_ = lean_box(1);
lean_inc(v___x_2564_);
v_it_2568_ = v___x_2624_;
v_startInclusive_2569_ = v_currPos_2595_;
v_endExclusive_2570_ = v___x_2564_;
goto v___jp_2567_;
}
}
}
else
{
lean_object* v___x_2626_; 
lean_dec(v___x_2564_);
lean_dec_ref(v___x_2562_);
v___x_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2626_, 0, v_b_2566_);
return v___x_2626_;
}
v___jp_2567_:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
lean_inc_ref(v___x_2562_);
v___x_2571_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2562_);
lean_ctor_set(v___x_2571_, 1, v_startInclusive_2569_);
lean_ctor_set(v___x_2571_, 2, v_endExclusive_2570_);
v___x_2572_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___closed__0);
v___x_2573_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2574_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2571_, v___x_2572_, v___x_2573_);
lean_dec_ref_known(v___x_2571_, 3);
v___x_2575_ = lean_array_to_list(v___x_2574_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v___x_2576_; 
v___x_2576_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2562_, v___x_2563_, v___x_2564_, v_it_2568_, v_b_2566_);
return v___x_2576_;
}
else
{
lean_object* v_tail_2577_; 
v_tail_2577_ = lean_ctor_get(v___x_2575_, 1);
lean_inc(v_tail_2577_);
if (lean_obj_tag(v_tail_2577_) == 0)
{
lean_object* v_head_2578_; lean_object* v___x_2579_; 
v_head_2578_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_head_2578_);
lean_dec_ref_known(v___x_2575_, 2);
v___x_2579_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2578_);
lean_dec(v_head_2578_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v___x_2580_; 
lean_dec(v_it_2568_);
lean_dec_ref(v_b_2566_);
lean_dec(v___x_2564_);
lean_dec_ref(v___x_2562_);
v___x_2580_ = lean_box(0);
return v___x_2580_;
}
else
{
lean_object* v_val_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v_val_2581_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_val_2581_);
lean_dec_ref_known(v___x_2579_, 1);
v___x_2582_ = lean_box(0);
v___x_2583_ = l_Std_Http_URI_Query_insertEncoded(v_b_2566_, v_val_2581_, v___x_2582_);
v___x_2584_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2562_, v___x_2563_, v___x_2564_, v_it_2568_, v___x_2583_);
return v___x_2584_;
}
}
else
{
lean_object* v_head_2585_; lean_object* v___x_2586_; 
v_head_2585_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_head_2585_);
lean_dec_ref_known(v___x_2575_, 2);
v___x_2586_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2585_);
lean_dec(v_head_2585_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v___x_2587_; 
lean_dec(v_tail_2577_);
lean_dec(v_it_2568_);
lean_dec_ref(v_b_2566_);
lean_dec(v___x_2564_);
lean_dec_ref(v___x_2562_);
v___x_2587_ = lean_box(0);
return v___x_2587_;
}
else
{
lean_object* v_val_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v_val_2588_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_val_2588_);
lean_dec_ref_known(v___x_2586_, 1);
v___x_2589_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2590_ = l_String_intercalate(v___x_2589_, v_tail_2577_);
v___x_2591_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2590_);
lean_dec_ref(v___x_2590_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v___x_2592_; 
lean_dec(v_val_2588_);
lean_dec(v_it_2568_);
lean_dec_ref(v_b_2566_);
lean_dec(v___x_2564_);
lean_dec_ref(v___x_2562_);
v___x_2592_ = lean_box(0);
return v___x_2592_;
}
else
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = l_Std_Http_URI_Query_insertEncoded(v_b_2566_, v_val_2588_, v___x_2591_);
v___x_2594_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2562_, v___x_2563_, v___x_2564_, v_it_2568_, v___x_2593_);
return v___x_2594_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg___boxed(lean_object* v___x_2627_, lean_object* v___x_2628_, lean_object* v___x_2629_, lean_object* v_a_2630_, lean_object* v_b_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2627_, v___x_2628_, v___x_2629_, v_a_2630_, v_b_2631_);
lean_dec_ref(v___x_2628_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(lean_object* v_config_2638_, lean_object* v_a_2639_){
_start:
{
lean_object* v_maxQueryLength_2640_; lean_object* v_maxQueryParams_2641_; lean_object* v___f_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v_snd_2645_; lean_object* v_fst_2646_; lean_object* v_fst_2647_; lean_object* v_array_2648_; lean_object* v_idx_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2699_; 
v_maxQueryLength_2640_ = lean_ctor_get(v_config_2638_, 4);
lean_inc(v_maxQueryLength_2640_);
v_maxQueryParams_2641_ = lean_ctor_get(v_config_2638_, 8);
lean_inc(v_maxQueryParams_2641_);
lean_dec_ref(v_config_2638_);
v___f_2642_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2643_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2639_);
v___x_2644_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2642_, v_maxQueryLength_2640_, v___x_2643_, v_a_2639_);
lean_dec(v_maxQueryLength_2640_);
v_snd_2645_ = lean_ctor_get(v___x_2644_, 1);
lean_inc(v_snd_2645_);
v_fst_2646_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_fst_2646_);
lean_dec_ref(v___x_2644_);
v_fst_2647_ = lean_ctor_get(v_snd_2645_, 0);
lean_inc(v_fst_2647_);
lean_dec(v_snd_2645_);
v_array_2648_ = lean_ctor_get(v_a_2639_, 0);
v_idx_2649_ = lean_ctor_get(v_a_2639_, 1);
v_isSharedCheck_2699_ = !lean_is_exclusive(v_a_2639_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2651_ = v_a_2639_;
v_isShared_2652_ = v_isSharedCheck_2699_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_idx_2649_);
lean_inc(v_array_2648_);
lean_dec(v_a_2639_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2699_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v_lower_2654_; lean_object* v_upper_2655_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___y_2696_; uint8_t v___x_2698_; 
v___x_2693_ = lean_nat_add(v_idx_2649_, v_fst_2646_);
lean_dec(v_fst_2646_);
v___x_2694_ = lean_byte_array_size(v_array_2648_);
v___x_2698_ = lean_nat_dec_le(v_idx_2649_, v___x_2643_);
if (v___x_2698_ == 0)
{
v___y_2696_ = v_idx_2649_;
goto v___jp_2695_;
}
else
{
lean_dec(v_idx_2649_);
v___y_2696_ = v___x_2643_;
goto v___jp_2695_;
}
v___jp_2653_:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; 
v___x_2656_ = l_ByteArray_toByteSlice(v_array_2648_, v_lower_2654_, v_upper_2655_);
v___x_2657_ = l_ByteSlice_toByteArray(v___x_2656_);
v___x_2658_ = lean_string_validate_utf8(v___x_2657_);
if (v___x_2658_ == 0)
{
lean_object* v___x_2659_; lean_object* v___x_2661_; 
lean_dec_ref(v___x_2657_);
lean_dec(v_maxQueryParams_2641_);
v___x_2659_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2652_ == 0)
{
lean_ctor_set_tag(v___x_2651_, 1);
lean_ctor_set(v___x_2651_, 1, v___x_2659_);
lean_ctor_set(v___x_2651_, 0, v_fst_2647_);
v___x_2661_ = v___x_2651_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_fst_2647_);
lean_ctor_set(v_reuseFailAlloc_2662_, 1, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
else
{
lean_object* v___x_2663_; lean_object* v___x_2664_; uint8_t v___x_2665_; 
v___x_2663_ = lean_string_from_utf8_unchecked(v___x_2657_);
v___x_2664_ = lean_string_utf8_byte_size(v___x_2663_);
v___x_2665_ = lean_nat_dec_eq(v___x_2664_, v___x_2643_);
if (v___x_2665_ == 0)
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; uint8_t v___x_2669_; 
lean_inc_ref(v___x_2663_);
v___x_2666_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2663_);
lean_ctor_set(v___x_2666_, 1, v___x_2643_);
lean_ctor_set(v___x_2666_, 2, v___x_2664_);
v___x_2667_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0);
v___x_2668_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2663_, v___x_2666_, v___x_2664_, v___x_2667_, v___x_2643_);
v___x_2669_ = lean_nat_dec_lt(v_maxQueryParams_2641_, v___x_2668_);
lean_dec(v___x_2668_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
lean_dec(v_maxQueryParams_2641_);
v___x_2670_ = l_Std_Http_URI_Query_empty;
v___x_2671_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2663_, v___x_2666_, v___x_2664_, v___x_2667_, v___x_2670_);
lean_dec_ref_known(v___x_2666_, 3);
if (lean_obj_tag(v___x_2671_) == 1)
{
lean_object* v_val_2672_; lean_object* v___x_2674_; 
v_val_2672_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_val_2672_);
lean_dec_ref_known(v___x_2671_, 1);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 1, v_val_2672_);
lean_ctor_set(v___x_2651_, 0, v_fst_2647_);
v___x_2674_ = v___x_2651_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_fst_2647_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v_val_2672_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
else
{
lean_object* v___x_2676_; lean_object* v___x_2678_; 
lean_dec(v___x_2671_);
v___x_2676_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2652_ == 0)
{
lean_ctor_set_tag(v___x_2651_, 1);
lean_ctor_set(v___x_2651_, 1, v___x_2676_);
lean_ctor_set(v___x_2651_, 0, v_fst_2647_);
v___x_2678_ = v___x_2651_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_fst_2647_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v___x_2676_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
else
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2687_; 
lean_dec_ref_known(v___x_2666_, 3);
lean_dec_ref(v___x_2663_);
v___x_2680_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3));
v___x_2681_ = l_Nat_reprFast(v_maxQueryParams_2641_);
v___x_2682_ = lean_string_append(v___x_2680_, v___x_2681_);
lean_dec_ref(v___x_2681_);
v___x_2683_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___redArg___closed__1));
v___x_2684_ = lean_string_append(v___x_2682_, v___x_2683_);
v___x_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set_tag(v___x_2651_, 1);
lean_ctor_set(v___x_2651_, 1, v___x_2685_);
lean_ctor_set(v___x_2651_, 0, v_fst_2647_);
v___x_2687_ = v___x_2651_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_fst_2647_);
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
lean_object* v___x_2689_; lean_object* v___x_2691_; 
lean_dec_ref(v___x_2663_);
lean_dec(v_maxQueryParams_2641_);
v___x_2689_ = l_Std_Http_URI_Query_empty;
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 1, v___x_2689_);
lean_ctor_set(v___x_2651_, 0, v_fst_2647_);
v___x_2691_ = v___x_2651_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_fst_2647_);
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
}
v___jp_2695_:
{
uint8_t v___x_2697_; 
v___x_2697_ = lean_nat_dec_le(v___x_2693_, v___x_2694_);
if (v___x_2697_ == 0)
{
lean_dec(v___x_2693_);
v_lower_2654_ = v___y_2696_;
v_upper_2655_ = v___x_2694_;
goto v___jp_2653_;
}
else
{
v_lower_2654_ = v___y_2696_;
v_upper_2655_ = v___x_2693_;
goto v___jp_2653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(lean_object* v___x_2700_, lean_object* v___x_2701_, lean_object* v___x_2702_, lean_object* v_inst_2703_, lean_object* v_R_2704_, lean_object* v_a_2705_, lean_object* v_b_2706_, lean_object* v_c_2707_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2700_, v___x_2701_, v___x_2702_, v_a_2705_, v_b_2706_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___boxed(lean_object* v___x_2709_, lean_object* v___x_2710_, lean_object* v___x_2711_, lean_object* v_inst_2712_, lean_object* v_R_2713_, lean_object* v_a_2714_, lean_object* v_b_2715_, lean_object* v_c_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(v___x_2709_, v___x_2710_, v___x_2711_, v_inst_2712_, v_R_2713_, v_a_2714_, v_b_2715_, v_c_2716_);
lean_dec(v___x_2711_);
lean_dec_ref(v___x_2710_);
lean_dec_ref(v___x_2709_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(lean_object* v_out_2718_, lean_object* v_inst_2719_, lean_object* v_R_2720_, lean_object* v_a_2721_, lean_object* v_b_2722_){
_start:
{
lean_object* v___x_2723_; 
v___x_2723_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2718_, v_a_2721_, v_b_2722_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___boxed(lean_object* v_out_2724_, lean_object* v_inst_2725_, lean_object* v_R_2726_, lean_object* v_a_2727_, lean_object* v_b_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(v_out_2724_, v_inst_2725_, v_R_2726_, v_a_2727_, v_b_2728_);
lean_dec_ref(v_out_2724_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(lean_object* v___x_2730_, lean_object* v___x_2731_, lean_object* v___x_2732_, lean_object* v_inst_2733_, lean_object* v_R_2734_, lean_object* v_a_2735_, lean_object* v_b_2736_, lean_object* v_c_2737_){
_start:
{
lean_object* v___x_2738_; 
v___x_2738_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2730_, v___x_2731_, v___x_2732_, v_a_2735_, v_b_2736_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___boxed(lean_object* v___x_2739_, lean_object* v___x_2740_, lean_object* v___x_2741_, lean_object* v_inst_2742_, lean_object* v_R_2743_, lean_object* v_a_2744_, lean_object* v_b_2745_, lean_object* v_c_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(v___x_2739_, v___x_2740_, v___x_2741_, v_inst_2742_, v_R_2743_, v_a_2744_, v_b_2745_, v_c_2746_);
lean_dec_ref(v___x_2740_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(lean_object* v___x_2748_, lean_object* v___x_2749_, lean_object* v___x_2750_, lean_object* v_inst_2751_, lean_object* v_R_2752_, lean_object* v_a_2753_, lean_object* v_b_2754_, lean_object* v_c_2755_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2749_, v___x_2750_, v_a_2753_, v_b_2754_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___boxed(lean_object* v___x_2757_, lean_object* v___x_2758_, lean_object* v___x_2759_, lean_object* v_inst_2760_, lean_object* v_R_2761_, lean_object* v_a_2762_, lean_object* v_b_2763_, lean_object* v_c_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(v___x_2757_, v___x_2758_, v___x_2759_, v_inst_2760_, v_R_2761_, v_a_2762_, v_b_2763_, v_c_2764_);
lean_dec(v___x_2759_);
lean_dec_ref(v___x_2758_);
lean_dec_ref(v___x_2757_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(lean_object* v___x_2766_, lean_object* v___x_2767_, lean_object* v___x_2768_, lean_object* v_inst_2769_, lean_object* v_R_2770_, lean_object* v_a_2771_, lean_object* v_b_2772_, lean_object* v_c_2773_){
_start:
{
lean_object* v___x_2774_; 
v___x_2774_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2766_, v___x_2767_, v___x_2768_, v_a_2771_, v_b_2772_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___boxed(lean_object* v___x_2775_, lean_object* v___x_2776_, lean_object* v___x_2777_, lean_object* v_inst_2778_, lean_object* v_R_2779_, lean_object* v_a_2780_, lean_object* v_b_2781_, lean_object* v_c_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(v___x_2775_, v___x_2776_, v___x_2777_, v_inst_2778_, v_R_2779_, v_a_2780_, v_b_2781_, v_c_2782_);
lean_dec_ref(v___x_2776_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(lean_object* v_config_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v_maxFragmentLength_2789_; lean_object* v___f_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v_snd_2793_; lean_object* v_fst_2794_; lean_object* v_fst_2795_; lean_object* v_array_2796_; lean_object* v_idx_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2821_; 
v_maxFragmentLength_2789_ = lean_ctor_get(v_config_2787_, 5);
v___f_2790_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2791_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2788_);
v___x_2792_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2790_, v_maxFragmentLength_2789_, v___x_2791_, v_a_2788_);
v_snd_2793_ = lean_ctor_get(v___x_2792_, 1);
lean_inc(v_snd_2793_);
v_fst_2794_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_fst_2794_);
lean_dec_ref(v___x_2792_);
v_fst_2795_ = lean_ctor_get(v_snd_2793_, 0);
lean_inc(v_fst_2795_);
lean_dec(v_snd_2793_);
v_array_2796_ = lean_ctor_get(v_a_2788_, 0);
v_idx_2797_ = lean_ctor_get(v_a_2788_, 1);
v_isSharedCheck_2821_ = !lean_is_exclusive(v_a_2788_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2799_ = v_a_2788_;
v_isShared_2800_ = v_isSharedCheck_2821_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_idx_2797_);
lean_inc(v_array_2796_);
lean_dec(v_a_2788_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2821_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v_lower_2802_; lean_object* v_upper_2803_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___y_2818_; uint8_t v___x_2820_; 
v___x_2815_ = lean_nat_add(v_idx_2797_, v_fst_2794_);
lean_dec(v_fst_2794_);
v___x_2816_ = lean_byte_array_size(v_array_2796_);
v___x_2820_ = lean_nat_dec_le(v_idx_2797_, v___x_2791_);
if (v___x_2820_ == 0)
{
v___y_2818_ = v_idx_2797_;
goto v___jp_2817_;
}
else
{
lean_dec(v_idx_2797_);
v___y_2818_ = v___x_2791_;
goto v___jp_2817_;
}
v___jp_2801_:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2804_ = l_ByteArray_toByteSlice(v_array_2796_, v_lower_2802_, v_upper_2803_);
v___x_2805_ = l_ByteSlice_toByteArray(v___x_2804_);
v___x_2806_ = l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(v___x_2805_);
if (lean_obj_tag(v___x_2806_) == 1)
{
lean_object* v_val_2807_; lean_object* v___x_2809_; 
v_val_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_val_2807_);
lean_dec_ref_known(v___x_2806_, 1);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 1, v_val_2807_);
lean_ctor_set(v___x_2799_, 0, v_fst_2795_);
v___x_2809_ = v___x_2799_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_fst_2795_);
lean_ctor_set(v_reuseFailAlloc_2810_, 1, v_val_2807_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
else
{
lean_object* v___x_2811_; lean_object* v___x_2813_; 
lean_dec(v___x_2806_);
v___x_2811_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1));
if (v_isShared_2800_ == 0)
{
lean_ctor_set_tag(v___x_2799_, 1);
lean_ctor_set(v___x_2799_, 1, v___x_2811_);
lean_ctor_set(v___x_2799_, 0, v_fst_2795_);
v___x_2813_ = v___x_2799_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_fst_2795_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v___x_2811_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
v___jp_2817_:
{
uint8_t v___x_2819_; 
v___x_2819_ = lean_nat_dec_le(v___x_2815_, v___x_2816_);
if (v___x_2819_ == 0)
{
lean_dec(v___x_2815_);
v_lower_2802_ = v___y_2818_;
v_upper_2803_ = v___x_2816_;
goto v___jp_2801_;
}
else
{
v_lower_2802_ = v___y_2818_;
v_upper_2803_ = v___x_2815_;
goto v___jp_2801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___boxed(lean_object* v_config_2822_, lean_object* v_a_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2822_, v_a_2823_);
lean_dec_ref(v_config_2822_);
return v_res_2824_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1(void){
_start:
{
lean_object* v___x_2826_; lean_object* v_utf8_2827_; 
v___x_2826_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0));
v_utf8_2827_ = lean_string_to_utf8(v___x_2826_);
return v_utf8_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(lean_object* v_config_2828_, lean_object* v_a_2829_){
_start:
{
uint8_t v___y_2831_; lean_object* v_pos_2832_; lean_object* v_res_2833_; uint8_t v___y_2855_; lean_object* v___y_2856_; lean_object* v_err_2857_; lean_object* v_pos_2863_; lean_object* v_utf8_2871_; lean_object* v___x_2872_; 
v_utf8_2871_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_2829_);
v___x_2872_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_2871_, v_a_2829_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_pos_2873_; 
lean_dec_ref(v_a_2829_);
v_pos_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_pos_2873_);
lean_dec_ref_known(v___x_2872_, 2);
v_pos_2863_ = v_pos_2873_;
goto v___jp_2862_;
}
else
{
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_pos_2874_; 
lean_dec_ref(v_a_2829_);
v_pos_2874_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_pos_2874_);
lean_dec_ref_known(v___x_2872_, 2);
v_pos_2863_ = v_pos_2874_;
goto v___jp_2862_;
}
else
{
lean_object* v_err_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2906_; 
v_err_2875_ = lean_ctor_get(v___x_2872_, 1);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2906_ == 0)
{
lean_object* v_unused_2907_; 
v_unused_2907_ = lean_ctor_get(v___x_2872_, 0);
lean_dec(v_unused_2907_);
v___x_2877_ = v___x_2872_;
v_isShared_2878_ = v_isSharedCheck_2906_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_err_2875_);
lean_dec(v___x_2872_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2906_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v_idx_2879_; uint8_t v___x_2880_; 
v_idx_2879_ = lean_ctor_get(v_a_2829_, 1);
v___x_2880_ = lean_nat_dec_eq(v_idx_2879_, v_idx_2879_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2882_; 
lean_dec_ref(v_config_2828_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 0, v_a_2829_);
v___x_2882_ = v___x_2877_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2829_);
lean_ctor_set(v_reuseFailAlloc_2883_, 1, v_err_2875_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
else
{
uint8_t v___x_2884_; lean_object* v___x_2885_; 
lean_del_object(v___x_2877_);
lean_dec(v_err_2875_);
v___x_2884_ = 0;
v___x_2885_ = l_Std_Http_URI_Parser_parsePath(v_config_2828_, v___x_2884_, v___x_2880_, v_a_2829_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_pos_2886_; lean_object* v_res_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2896_; 
v_pos_2886_ = lean_ctor_get(v___x_2885_, 0);
v_res_2887_ = lean_ctor_get(v___x_2885_, 1);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2889_ = v___x_2885_;
v_isShared_2890_ = v_isSharedCheck_2896_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_res_2887_);
lean_inc(v_pos_2886_);
lean_dec(v___x_2885_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2896_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2894_; 
v___x_2891_ = lean_box(0);
v___x_2892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
lean_ctor_set(v___x_2892_, 1, v_res_2887_);
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 1, v___x_2892_);
v___x_2894_ = v___x_2889_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_pos_2886_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v___x_2892_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
else
{
lean_object* v_pos_2897_; lean_object* v_err_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
v_pos_2897_ = lean_ctor_get(v___x_2885_, 0);
v_err_2898_ = lean_ctor_get(v___x_2885_, 1);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2885_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_err_2898_);
lean_inc(v_pos_2897_);
lean_dec(v___x_2885_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_pos_2897_);
lean_ctor_set(v_reuseFailAlloc_2904_, 1, v_err_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
}
}
}
v___jp_2830_:
{
lean_object* v___x_2834_; 
v___x_2834_ = l_Std_Http_URI_Parser_parsePath(v_config_2828_, v___y_2831_, v___y_2831_, v_pos_2832_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_pos_2835_; lean_object* v_res_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2844_; 
v_pos_2835_ = lean_ctor_get(v___x_2834_, 0);
v_res_2836_ = lean_ctor_get(v___x_2834_, 1);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2838_ = v___x_2834_;
v_isShared_2839_ = v_isSharedCheck_2844_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_res_2836_);
lean_inc(v_pos_2835_);
lean_dec(v___x_2834_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2844_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2840_; lean_object* v___x_2842_; 
v___x_2840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2840_, 0, v_res_2833_);
lean_ctor_set(v___x_2840_, 1, v_res_2836_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 1, v___x_2840_);
v___x_2842_ = v___x_2838_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_pos_2835_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v___x_2840_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
else
{
lean_object* v_pos_2845_; lean_object* v_err_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_dec(v_res_2833_);
v_pos_2845_ = lean_ctor_get(v___x_2834_, 0);
v_err_2846_ = lean_ctor_get(v___x_2834_, 1);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2834_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_err_2846_);
lean_inc(v_pos_2845_);
lean_dec(v___x_2834_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_pos_2845_);
lean_ctor_set(v_reuseFailAlloc_2852_, 1, v_err_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
v___jp_2854_:
{
lean_object* v_idx_2858_; uint8_t v___x_2859_; 
v_idx_2858_ = lean_ctor_get(v___y_2856_, 1);
v___x_2859_ = lean_nat_dec_eq(v_idx_2858_, v_idx_2858_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; 
lean_dec_ref(v_config_2828_);
v___x_2860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___y_2856_);
lean_ctor_set(v___x_2860_, 1, v_err_2857_);
return v___x_2860_;
}
else
{
lean_object* v___x_2861_; 
lean_dec(v_err_2857_);
v___x_2861_ = lean_box(0);
v___y_2831_ = v___y_2855_;
v_pos_2832_ = v___y_2856_;
v_res_2833_ = v___x_2861_;
goto v___jp_2830_;
}
}
v___jp_2862_:
{
uint8_t v___x_2864_; lean_object* v___x_2865_; 
v___x_2864_ = 1;
lean_inc_ref(v_pos_2863_);
v___x_2865_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_2828_, v_pos_2863_);
if (lean_obj_tag(v___x_2865_) == 0)
{
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_pos_2866_; lean_object* v_res_2867_; lean_object* v___x_2868_; 
lean_dec_ref(v_pos_2863_);
v_pos_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_pos_2866_);
v_res_2867_ = lean_ctor_get(v___x_2865_, 1);
lean_inc(v_res_2867_);
lean_dec_ref_known(v___x_2865_, 2);
v___x_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2868_, 0, v_res_2867_);
v___y_2831_ = v___x_2864_;
v_pos_2832_ = v_pos_2866_;
v_res_2833_ = v___x_2868_;
goto v___jp_2830_;
}
else
{
lean_object* v_err_2869_; 
v_err_2869_ = lean_ctor_get(v___x_2865_, 1);
lean_inc(v_err_2869_);
lean_dec_ref_known(v___x_2865_, 2);
v___y_2855_ = v___x_2864_;
v___y_2856_ = v_pos_2863_;
v_err_2857_ = v_err_2869_;
goto v___jp_2854_;
}
}
else
{
lean_object* v_err_2870_; 
v_err_2870_ = lean_ctor_get(v___x_2865_, 1);
lean_inc(v_err_2870_);
lean_dec_ref_known(v___x_2865_, 2);
v___y_2855_ = v___x_2864_;
v___y_2856_ = v_pos_2863_;
v_err_2857_ = v_err_2870_;
goto v___jp_2854_;
}
}
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__0(void){
_start:
{
uint8_t v___x_2908_; lean_object* v___x_2909_; 
v___x_2908_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v___x_2909_ = lean_uint8_to_nat(v___x_2908_);
return v___x_2909_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__1(void){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2910_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__0, &l_Std_Http_URI_Parser_parseURI___closed__0_once, _init_l_Std_Http_URI_Parser_parseURI___closed__0);
v___x_2911_ = l_Nat_reprFast(v___x_2910_);
return v___x_2911_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__2(void){
_start:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2912_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__1, &l_Std_Http_URI_Parser_parseURI___closed__1_once, _init_l_Std_Http_URI_Parser_parseURI___closed__1);
v___x_2913_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_2914_ = lean_string_append(v___x_2913_, v___x_2912_);
return v___x_2914_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__3(void){
_start:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2915_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_2916_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__2, &l_Std_Http_URI_Parser_parseURI___closed__2_once, _init_l_Std_Http_URI_Parser_parseURI___closed__2);
v___x_2917_ = lean_string_append(v___x_2916_, v___x_2915_);
return v___x_2917_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__4(void){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__3, &l_Std_Http_URI_Parser_parseURI___closed__3_once, _init_l_Std_Http_URI_Parser_parseURI___closed__3);
v___x_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
return v___x_2919_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__7(void){
_start:
{
uint8_t v___x_2923_; lean_object* v___x_2924_; 
v___x_2923_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_2924_ = lean_uint8_to_nat(v___x_2923_);
return v___x_2924_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__8(void){
_start:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2925_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__7, &l_Std_Http_URI_Parser_parseURI___closed__7_once, _init_l_Std_Http_URI_Parser_parseURI___closed__7);
v___x_2926_ = l_Nat_reprFast(v___x_2925_);
return v___x_2926_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__9(void){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2927_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__8, &l_Std_Http_URI_Parser_parseURI___closed__8_once, _init_l_Std_Http_URI_Parser_parseURI___closed__8);
v___x_2928_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_2929_ = lean_string_append(v___x_2928_, v___x_2927_);
return v___x_2929_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__10(void){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2930_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_2931_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__9, &l_Std_Http_URI_Parser_parseURI___closed__9_once, _init_l_Std_Http_URI_Parser_parseURI___closed__9);
v___x_2932_ = lean_string_append(v___x_2931_, v___x_2930_);
return v___x_2932_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__11(void){
_start:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__10, &l_Std_Http_URI_Parser_parseURI___closed__10_once, _init_l_Std_Http_URI_Parser_parseURI___closed__10);
v___x_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURI(lean_object* v_config_2935_, lean_object* v_a_2936_){
_start:
{
lean_object* v___x_2937_; 
v___x_2937_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_2935_, v_a_2936_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_pos_2938_; lean_object* v_res_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_3070_; 
v_pos_2938_ = lean_ctor_get(v___x_2937_, 0);
v_res_2939_ = lean_ctor_get(v___x_2937_, 1);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_2941_ = v___x_2937_;
v_isShared_2942_ = v_isSharedCheck_3070_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_res_2939_);
lean_inc(v_pos_2938_);
lean_dec(v___x_2937_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_3070_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v_array_2943_; lean_object* v_idx_2944_; lean_object* v___x_2945_; uint8_t v___x_2946_; 
v_array_2943_ = lean_ctor_get(v_pos_2938_, 0);
v_idx_2944_ = lean_ctor_get(v_pos_2938_, 1);
v___x_2945_ = lean_byte_array_size(v_array_2943_);
v___x_2946_ = lean_nat_dec_lt(v_idx_2944_, v___x_2945_);
if (v___x_2946_ == 0)
{
lean_object* v___x_2947_; lean_object* v___x_2949_; 
lean_dec(v_res_2939_);
lean_dec_ref(v_config_2935_);
v___x_2947_ = lean_box(0);
if (v_isShared_2942_ == 0)
{
lean_ctor_set_tag(v___x_2941_, 1);
lean_ctor_set(v___x_2941_, 1, v___x_2947_);
v___x_2949_ = v___x_2941_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_pos_2938_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v___x_2947_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
else
{
uint8_t v___x_2951_; uint8_t v_got_2952_; uint8_t v___x_2953_; 
v___x_2951_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v_got_2952_ = lean_byte_array_fget(v_array_2943_, v_idx_2944_);
v___x_2953_ = lean_uint8_dec_eq(v_got_2952_, v___x_2951_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2954_; lean_object* v___x_2956_; 
lean_dec(v_res_2939_);
lean_dec_ref(v_config_2935_);
v___x_2954_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
if (v_isShared_2942_ == 0)
{
lean_ctor_set_tag(v___x_2941_, 1);
lean_ctor_set(v___x_2941_, 1, v___x_2954_);
v___x_2956_ = v___x_2941_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_pos_2938_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v___x_2954_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
else
{
lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_3067_; 
lean_inc(v_idx_2944_);
lean_inc_ref(v_array_2943_);
v_isSharedCheck_3067_ = !lean_is_exclusive(v_pos_2938_);
if (v_isSharedCheck_3067_ == 0)
{
lean_object* v_unused_3068_; lean_object* v_unused_3069_; 
v_unused_3068_ = lean_ctor_get(v_pos_2938_, 1);
lean_dec(v_unused_3068_);
v_unused_3069_ = lean_ctor_get(v_pos_2938_, 0);
lean_dec(v_unused_3069_);
v___x_2959_ = v_pos_2938_;
v_isShared_2960_ = v_isSharedCheck_3067_;
goto v_resetjp_2958_;
}
else
{
lean_dec(v_pos_2938_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_3067_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2964_; 
v___x_2961_ = lean_unsigned_to_nat(1u);
v___x_2962_ = lean_nat_add(v_idx_2944_, v___x_2961_);
lean_dec(v_idx_2944_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 1, v___x_2962_);
v___x_2964_ = v___x_2959_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_array_2943_);
lean_ctor_set(v_reuseFailAlloc_3066_, 1, v___x_2962_);
v___x_2964_ = v_reuseFailAlloc_3066_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
lean_object* v___x_2965_; 
lean_inc_ref(v_config_2935_);
v___x_2965_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2935_, v___x_2964_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_res_2966_; lean_object* v_pos_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_3056_; 
v_res_2966_ = lean_ctor_get(v___x_2965_, 1);
v_pos_2967_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_2969_ = v___x_2965_;
v_isShared_2970_ = v_isSharedCheck_3056_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_res_2966_);
lean_inc(v_pos_2967_);
lean_dec(v___x_2965_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_3056_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v_fst_2971_; lean_object* v_snd_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_3055_; 
v_fst_2971_ = lean_ctor_get(v_res_2966_, 0);
v_snd_2972_ = lean_ctor_get(v_res_2966_, 1);
v_isSharedCheck_3055_ = !lean_is_exclusive(v_res_2966_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_2974_ = v_res_2966_;
v_isShared_2975_ = v_isSharedCheck_3055_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_snd_2972_);
lean_inc(v_fst_2971_);
lean_dec(v_res_2966_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_3055_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___y_2977_; lean_object* v_pos_2978_; lean_object* v_res_2979_; lean_object* v_idx_2985_; lean_object* v___y_2986_; lean_object* v_pos_2987_; lean_object* v_err_2988_; lean_object* v_pos_2996_; lean_object* v_array_2997_; lean_object* v_idx_2998_; lean_object* v_res_2999_; lean_object* v_array_3018_; lean_object* v_idx_3019_; lean_object* v_pos_3021_; lean_object* v_array_3022_; lean_object* v_idx_3023_; lean_object* v_err_3024_; lean_object* v___x_3028_; uint8_t v___x_3029_; 
v_array_3018_ = lean_ctor_get(v_pos_2967_, 0);
lean_inc_ref(v_array_3018_);
v_idx_3019_ = lean_ctor_get(v_pos_2967_, 1);
lean_inc(v_idx_3019_);
v___x_3028_ = lean_byte_array_size(v_array_3018_);
v___x_3029_ = lean_nat_dec_lt(v_idx_3019_, v___x_3028_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; 
v___x_3030_ = lean_box(0);
lean_inc(v_idx_3019_);
v_pos_3021_ = v_pos_2967_;
v_array_3022_ = v_array_3018_;
v_idx_3023_ = v_idx_3019_;
v_err_3024_ = v___x_3030_;
goto v___jp_3020_;
}
else
{
uint8_t v___x_3031_; uint8_t v_got_3032_; uint8_t v___x_3033_; 
v___x_3031_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3032_ = lean_byte_array_fget(v_array_3018_, v_idx_3019_);
v___x_3033_ = lean_uint8_dec_eq(v_got_3032_, v___x_3031_);
if (v___x_3033_ == 0)
{
lean_object* v___x_3034_; 
v___x_3034_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3019_);
v_pos_3021_ = v_pos_2967_;
v_array_3022_ = v_array_3018_;
v_idx_3023_ = v_idx_3019_;
v_err_3024_ = v___x_3034_;
goto v___jp_3020_;
}
else
{
lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3052_; 
v_isSharedCheck_3052_ = !lean_is_exclusive(v_pos_2967_);
if (v_isSharedCheck_3052_ == 0)
{
lean_object* v_unused_3053_; lean_object* v_unused_3054_; 
v_unused_3053_ = lean_ctor_get(v_pos_2967_, 1);
lean_dec(v_unused_3053_);
v_unused_3054_ = lean_ctor_get(v_pos_2967_, 0);
lean_dec(v_unused_3054_);
v___x_3036_ = v_pos_2967_;
v_isShared_3037_ = v_isSharedCheck_3052_;
goto v_resetjp_3035_;
}
else
{
lean_dec(v_pos_2967_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3052_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3038_; lean_object* v___x_3040_; 
v___x_3038_ = lean_nat_add(v_idx_3019_, v___x_2961_);
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 1, v___x_3038_);
v___x_3040_ = v___x_3036_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_array_3018_);
lean_ctor_set(v_reuseFailAlloc_3051_, 1, v___x_3038_);
v___x_3040_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3041_; 
lean_inc_ref(v_config_2935_);
v___x_3041_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2935_, v___x_3040_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v_pos_3042_; lean_object* v_res_3043_; lean_object* v_array_3044_; lean_object* v_idx_3045_; lean_object* v___x_3046_; 
lean_dec(v_idx_3019_);
v_pos_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_pos_3042_);
v_res_3043_ = lean_ctor_get(v___x_3041_, 1);
lean_inc(v_res_3043_);
lean_dec_ref_known(v___x_3041_, 2);
v_array_3044_ = lean_ctor_get(v_pos_3042_, 0);
lean_inc_ref(v_array_3044_);
v_idx_3045_ = lean_ctor_get(v_pos_3042_, 1);
lean_inc(v_idx_3045_);
v___x_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3046_, 0, v_res_3043_);
v_pos_2996_ = v_pos_3042_;
v_array_2997_ = v_array_3044_;
v_idx_2998_ = v_idx_3045_;
v_res_2999_ = v___x_3046_;
goto v___jp_2995_;
}
else
{
lean_object* v_pos_3047_; lean_object* v_err_3048_; lean_object* v_array_3049_; lean_object* v_idx_3050_; 
v_pos_3047_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_pos_3047_);
v_err_3048_ = lean_ctor_get(v___x_3041_, 1);
lean_inc(v_err_3048_);
lean_dec_ref_known(v___x_3041_, 2);
v_array_3049_ = lean_ctor_get(v_pos_3047_, 0);
lean_inc_ref(v_array_3049_);
v_idx_3050_ = lean_ctor_get(v_pos_3047_, 1);
lean_inc(v_idx_3050_);
v_pos_3021_ = v_pos_3047_;
v_array_3022_ = v_array_3049_;
v_idx_3023_ = v_idx_3050_;
v_err_3024_ = v_err_3048_;
goto v___jp_3020_;
}
}
}
}
}
v___jp_2976_:
{
lean_object* v___x_2980_; lean_object* v___x_2982_; 
v___x_2980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2980_, 0, v_res_2939_);
lean_ctor_set(v___x_2980_, 1, v_fst_2971_);
lean_ctor_set(v___x_2980_, 2, v_snd_2972_);
lean_ctor_set(v___x_2980_, 3, v___y_2977_);
lean_ctor_set(v___x_2980_, 4, v_res_2979_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 1, v___x_2980_);
lean_ctor_set(v___x_2969_, 0, v_pos_2978_);
v___x_2982_ = v___x_2969_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_pos_2978_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v___x_2980_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
v___jp_2984_:
{
lean_object* v_idx_2989_; uint8_t v___x_2990_; 
v_idx_2989_ = lean_ctor_get(v_pos_2987_, 1);
v___x_2990_ = lean_nat_dec_eq(v_idx_2985_, v_idx_2989_);
lean_dec(v_idx_2985_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2992_; 
lean_dec(v___y_2986_);
lean_dec(v_snd_2972_);
lean_dec(v_fst_2971_);
lean_del_object(v___x_2969_);
lean_dec(v_res_2939_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set_tag(v___x_2941_, 1);
lean_ctor_set(v___x_2941_, 1, v_err_2988_);
lean_ctor_set(v___x_2941_, 0, v_pos_2987_);
v___x_2992_ = v___x_2941_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_pos_2987_);
lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_err_2988_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
else
{
lean_object* v___x_2994_; 
lean_dec(v_err_2988_);
lean_del_object(v___x_2941_);
v___x_2994_ = lean_box(0);
v___y_2977_ = v___y_2986_;
v_pos_2978_ = v_pos_2987_;
v_res_2979_ = v___x_2994_;
goto v___jp_2976_;
}
}
v___jp_2995_:
{
lean_object* v___x_3000_; uint8_t v___x_3001_; 
v___x_3000_ = lean_byte_array_size(v_array_2997_);
v___x_3001_ = lean_nat_dec_lt(v_idx_2998_, v___x_3000_);
if (v___x_3001_ == 0)
{
lean_object* v___x_3002_; 
lean_dec_ref(v_array_2997_);
lean_del_object(v___x_2974_);
lean_dec_ref(v_config_2935_);
v___x_3002_ = lean_box(0);
v_idx_2985_ = v_idx_2998_;
v___y_2986_ = v_res_2999_;
v_pos_2987_ = v_pos_2996_;
v_err_2988_ = v___x_3002_;
goto v___jp_2984_;
}
else
{
uint8_t v___x_3003_; uint8_t v_got_3004_; uint8_t v___x_3005_; 
v___x_3003_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v_got_3004_ = lean_byte_array_fget(v_array_2997_, v_idx_2998_);
v___x_3005_ = lean_uint8_dec_eq(v_got_3004_, v___x_3003_);
if (v___x_3005_ == 0)
{
lean_object* v___x_3006_; 
lean_dec_ref(v_array_2997_);
lean_del_object(v___x_2974_);
lean_dec_ref(v_config_2935_);
v___x_3006_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__4, &l_Std_Http_URI_Parser_parseURI___closed__4_once, _init_l_Std_Http_URI_Parser_parseURI___closed__4);
v_idx_2985_ = v_idx_2998_;
v___y_2986_ = v_res_2999_;
v_pos_2987_ = v_pos_2996_;
v_err_2988_ = v___x_3006_;
goto v___jp_2984_;
}
else
{
lean_object* v___x_3007_; lean_object* v___x_3009_; 
lean_dec_ref(v_pos_2996_);
v___x_3007_ = lean_nat_add(v_idx_2998_, v___x_2961_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 1, v___x_3007_);
lean_ctor_set(v___x_2974_, 0, v_array_2997_);
v___x_3009_ = v___x_2974_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_array_2997_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v___x_3007_);
v___x_3009_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
lean_object* v___x_3010_; 
v___x_3010_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2935_, v___x_3009_);
lean_dec_ref(v_config_2935_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_pos_3011_; lean_object* v_res_3012_; lean_object* v___x_3013_; 
v_pos_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_pos_3011_);
v_res_3012_ = lean_ctor_get(v___x_3010_, 1);
lean_inc(v_res_3012_);
lean_dec_ref_known(v___x_3010_, 2);
v___x_3013_ = l_Std_Http_URI_EncodedFragment_decode(v_res_3012_);
lean_dec(v_res_3012_);
if (lean_obj_tag(v___x_3013_) == 1)
{
lean_dec(v_idx_2998_);
lean_del_object(v___x_2941_);
v___y_2977_ = v_res_2999_;
v_pos_2978_ = v_pos_3011_;
v_res_2979_ = v___x_3013_;
goto v___jp_2976_;
}
else
{
lean_object* v___x_3014_; 
lean_dec(v___x_3013_);
v___x_3014_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__6));
v_idx_2985_ = v_idx_2998_;
v___y_2986_ = v_res_2999_;
v_pos_2987_ = v_pos_3011_;
v_err_2988_ = v___x_3014_;
goto v___jp_2984_;
}
}
else
{
lean_object* v_pos_3015_; lean_object* v_err_3016_; 
v_pos_3015_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_pos_3015_);
v_err_3016_ = lean_ctor_get(v___x_3010_, 1);
lean_inc(v_err_3016_);
lean_dec_ref_known(v___x_3010_, 2);
v_idx_2985_ = v_idx_2998_;
v___y_2986_ = v_res_2999_;
v_pos_2987_ = v_pos_3015_;
v_err_2988_ = v_err_3016_;
goto v___jp_2984_;
}
}
}
}
}
v___jp_3020_:
{
uint8_t v___x_3025_; 
v___x_3025_ = lean_nat_dec_eq(v_idx_3019_, v_idx_3023_);
lean_dec(v_idx_3019_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; 
lean_dec(v_idx_3023_);
lean_dec_ref(v_array_3022_);
lean_del_object(v___x_2974_);
lean_dec(v_snd_2972_);
lean_dec(v_fst_2971_);
lean_del_object(v___x_2969_);
lean_del_object(v___x_2941_);
lean_dec(v_res_2939_);
lean_dec_ref(v_config_2935_);
v___x_3026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3026_, 0, v_pos_3021_);
lean_ctor_set(v___x_3026_, 1, v_err_3024_);
return v___x_3026_;
}
else
{
lean_object* v___x_3027_; 
lean_dec(v_err_3024_);
v___x_3027_ = lean_box(0);
v_pos_2996_ = v_pos_3021_;
v_array_2997_ = v_array_3022_;
v_idx_2998_ = v_idx_3023_;
v_res_2999_ = v___x_3027_;
goto v___jp_2995_;
}
}
}
}
}
else
{
lean_object* v_pos_3057_; lean_object* v_err_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_del_object(v___x_2941_);
lean_dec(v_res_2939_);
lean_dec_ref(v_config_2935_);
v_pos_3057_ = lean_ctor_get(v___x_2965_, 0);
v_err_3058_ = lean_ctor_get(v___x_2965_, 1);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_2965_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_err_3058_);
lean_inc(v_pos_3057_);
lean_dec(v___x_2965_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_pos_3057_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v_err_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
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
lean_object* v_pos_3071_; lean_object* v_err_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3079_; 
lean_dec_ref(v_config_2935_);
v_pos_3071_ = lean_ctor_get(v___x_2937_, 0);
v_err_3072_ = lean_ctor_get(v___x_2937_, 1);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_2937_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_err_3072_);
lean_inc(v_pos_3071_);
lean_dec(v___x_2937_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3077_; 
if (v_isShared_3075_ == 0)
{
v___x_3077_ = v___x_3074_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_pos_3071_);
lean_ctor_set(v_reuseFailAlloc_3078_, 1, v_err_3072_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0(void){
_start:
{
uint8_t v___x_3080_; lean_object* v___x_3081_; 
v___x_3080_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_3081_ = lean_uint8_to_nat(v___x_3080_);
return v___x_3081_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1(void){
_start:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0);
v___x_3083_ = l_Nat_reprFast(v___x_3082_);
return v___x_3083_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2(void){
_start:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3084_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1);
v___x_3085_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_3086_ = lean_string_append(v___x_3085_, v___x_3084_);
return v___x_3086_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3(void){
_start:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3087_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_3088_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2);
v___x_3089_ = lean_string_append(v___x_3088_, v___x_3087_);
return v___x_3089_;
}
}
static lean_object* _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4(void){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3);
v___x_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(lean_object* v_a_3092_){
_start:
{
lean_object* v_array_3093_; lean_object* v_idx_3094_; lean_object* v___x_3095_; uint8_t v___x_3096_; 
v_array_3093_ = lean_ctor_get(v_a_3092_, 0);
v_idx_3094_ = lean_ctor_get(v_a_3092_, 1);
v___x_3095_ = lean_byte_array_size(v_array_3093_);
v___x_3096_ = lean_nat_dec_lt(v_idx_3094_, v___x_3095_);
if (v___x_3096_ == 0)
{
lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3097_ = lean_box(0);
v___x_3098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3098_, 0, v_a_3092_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
return v___x_3098_;
}
else
{
uint8_t v___x_3099_; uint8_t v_got_3100_; uint8_t v___x_3101_; 
v___x_3099_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v_got_3100_ = lean_byte_array_fget(v_array_3093_, v_idx_3094_);
v___x_3101_ = lean_uint8_dec_eq(v_got_3100_, v___x_3099_);
if (v___x_3101_ == 0)
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4);
v___x_3103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3103_, 0, v_a_3092_);
lean_ctor_set(v___x_3103_, 1, v___x_3102_);
return v___x_3103_;
}
else
{
lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3114_; 
lean_inc(v_idx_3094_);
lean_inc_ref(v_array_3093_);
v_isSharedCheck_3114_ = !lean_is_exclusive(v_a_3092_);
if (v_isSharedCheck_3114_ == 0)
{
lean_object* v_unused_3115_; lean_object* v_unused_3116_; 
v_unused_3115_ = lean_ctor_get(v_a_3092_, 1);
lean_dec(v_unused_3115_);
v_unused_3116_ = lean_ctor_get(v_a_3092_, 0);
lean_dec(v_unused_3116_);
v___x_3105_ = v_a_3092_;
v_isShared_3106_ = v_isSharedCheck_3114_;
goto v_resetjp_3104_;
}
else
{
lean_dec(v_a_3092_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3114_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3110_; 
v___x_3107_ = lean_unsigned_to_nat(1u);
v___x_3108_ = lean_nat_add(v_idx_3094_, v___x_3107_);
lean_dec(v_idx_3094_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 1, v___x_3108_);
v___x_3110_ = v___x_3105_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_array_3093_);
lean_ctor_set(v_reuseFailAlloc_3113_, 1, v___x_3108_);
v___x_3110_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3111_ = lean_box(3);
v___x_3112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3110_);
lean_ctor_set(v___x_3112_, 1, v___x_3111_);
return v___x_3112_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(lean_object* v_config_3120_, lean_object* v_a_3121_){
_start:
{
lean_object* v_array_3125_; lean_object* v_idx_3126_; lean_object* v___x_3127_; uint8_t v___x_3128_; 
v_array_3125_ = lean_ctor_get(v_a_3121_, 0);
v_idx_3126_ = lean_ctor_get(v_a_3121_, 1);
v___x_3127_ = lean_byte_array_size(v_array_3125_);
v___x_3128_ = lean_nat_dec_lt(v_idx_3126_, v___x_3127_);
if (v___x_3128_ == 0)
{
lean_dec_ref(v_config_3120_);
goto v___jp_3122_;
}
else
{
uint8_t v___x_3129_; uint8_t v___x_3130_; uint8_t v___x_3131_; 
v___x_3129_ = lean_byte_array_fget(v_array_3125_, v_idx_3126_);
v___x_3130_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_3131_ = lean_uint8_dec_eq(v___x_3129_, v___x_3130_);
if (v___x_3131_ == 0)
{
lean_dec_ref(v_config_3120_);
goto v___jp_3122_;
}
else
{
lean_object* v___x_3132_; 
lean_inc_ref(v_a_3121_);
lean_inc_ref(v_config_3120_);
v___x_3132_ = l_Std_Http_URI_Parser_parsePath(v_config_3120_, v___x_3131_, v___x_3131_, v_a_3121_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_pos_3133_; lean_object* v_res_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3179_; 
v_pos_3133_ = lean_ctor_get(v___x_3132_, 0);
v_res_3134_ = lean_ctor_get(v___x_3132_, 1);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3136_ = v___x_3132_;
v_isShared_3137_ = v_isSharedCheck_3179_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_res_3134_);
lean_inc(v_pos_3133_);
lean_dec(v___x_3132_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3179_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v_pos_3139_; lean_object* v_res_3140_; lean_object* v_array_3145_; lean_object* v_idx_3146_; lean_object* v_pos_3148_; lean_object* v_idx_3149_; lean_object* v_err_3150_; lean_object* v___x_3154_; uint8_t v___x_3155_; 
v_array_3145_ = lean_ctor_get(v_pos_3133_, 0);
v_idx_3146_ = lean_ctor_get(v_pos_3133_, 1);
lean_inc(v_idx_3146_);
v___x_3154_ = lean_byte_array_size(v_array_3145_);
v___x_3155_ = lean_nat_dec_lt(v_idx_3146_, v___x_3154_);
if (v___x_3155_ == 0)
{
lean_object* v___x_3156_; 
lean_dec_ref(v_config_3120_);
v___x_3156_ = lean_box(0);
lean_inc(v_idx_3146_);
v_pos_3148_ = v_pos_3133_;
v_idx_3149_ = v_idx_3146_;
v_err_3150_ = v___x_3156_;
goto v___jp_3147_;
}
else
{
uint8_t v___x_3157_; uint8_t v_got_3158_; uint8_t v___x_3159_; 
v___x_3157_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3158_ = lean_byte_array_fget(v_array_3145_, v_idx_3146_);
v___x_3159_ = lean_uint8_dec_eq(v_got_3158_, v___x_3157_);
if (v___x_3159_ == 0)
{
lean_object* v___x_3160_; 
lean_dec_ref(v_config_3120_);
v___x_3160_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3146_);
v_pos_3148_ = v_pos_3133_;
v_idx_3149_ = v_idx_3146_;
v_err_3150_ = v___x_3160_;
goto v___jp_3147_;
}
else
{
lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3176_; 
lean_inc_ref(v_array_3145_);
v_isSharedCheck_3176_ = !lean_is_exclusive(v_pos_3133_);
if (v_isSharedCheck_3176_ == 0)
{
lean_object* v_unused_3177_; lean_object* v_unused_3178_; 
v_unused_3177_ = lean_ctor_get(v_pos_3133_, 1);
lean_dec(v_unused_3177_);
v_unused_3178_ = lean_ctor_get(v_pos_3133_, 0);
lean_dec(v_unused_3178_);
v___x_3162_ = v_pos_3133_;
v_isShared_3163_ = v_isSharedCheck_3176_;
goto v_resetjp_3161_;
}
else
{
lean_dec(v_pos_3133_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3176_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3167_; 
v___x_3164_ = lean_unsigned_to_nat(1u);
v___x_3165_ = lean_nat_add(v_idx_3146_, v___x_3164_);
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 1, v___x_3165_);
v___x_3167_ = v___x_3162_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_array_3145_);
lean_ctor_set(v_reuseFailAlloc_3175_, 1, v___x_3165_);
v___x_3167_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
lean_object* v___x_3168_; 
v___x_3168_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3120_, v___x_3167_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_pos_3169_; lean_object* v_res_3170_; lean_object* v___x_3171_; 
lean_dec(v_idx_3146_);
lean_dec_ref(v_a_3121_);
v_pos_3169_ = lean_ctor_get(v___x_3168_, 0);
lean_inc(v_pos_3169_);
v_res_3170_ = lean_ctor_get(v___x_3168_, 1);
lean_inc(v_res_3170_);
lean_dec_ref_known(v___x_3168_, 2);
v___x_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3171_, 0, v_res_3170_);
v_pos_3139_ = v_pos_3169_;
v_res_3140_ = v___x_3171_;
goto v___jp_3138_;
}
else
{
lean_object* v_pos_3172_; lean_object* v_err_3173_; lean_object* v_idx_3174_; 
v_pos_3172_ = lean_ctor_get(v___x_3168_, 0);
lean_inc(v_pos_3172_);
v_err_3173_ = lean_ctor_get(v___x_3168_, 1);
lean_inc(v_err_3173_);
lean_dec_ref_known(v___x_3168_, 2);
v_idx_3174_ = lean_ctor_get(v_pos_3172_, 1);
lean_inc(v_idx_3174_);
v_pos_3148_ = v_pos_3172_;
v_idx_3149_ = v_idx_3174_;
v_err_3150_ = v_err_3173_;
goto v___jp_3147_;
}
}
}
}
}
v___jp_3138_:
{
lean_object* v___x_3141_; lean_object* v___x_3143_; 
v___x_3141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3141_, 0, v_res_3134_);
lean_ctor_set(v___x_3141_, 1, v_res_3140_);
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 1, v___x_3141_);
lean_ctor_set(v___x_3136_, 0, v_pos_3139_);
v___x_3143_ = v___x_3136_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_pos_3139_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v___x_3141_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
v___jp_3147_:
{
uint8_t v___x_3151_; 
v___x_3151_ = lean_nat_dec_eq(v_idx_3146_, v_idx_3149_);
lean_dec(v_idx_3149_);
lean_dec(v_idx_3146_);
if (v___x_3151_ == 0)
{
lean_object* v___x_3152_; 
lean_dec_ref(v_pos_3148_);
lean_del_object(v___x_3136_);
lean_dec(v_res_3134_);
v___x_3152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3152_, 0, v_a_3121_);
lean_ctor_set(v___x_3152_, 1, v_err_3150_);
return v___x_3152_;
}
else
{
lean_object* v___x_3153_; 
lean_dec(v_err_3150_);
lean_dec_ref(v_a_3121_);
v___x_3153_ = lean_box(0);
v_pos_3139_ = v_pos_3148_;
v_res_3140_ = v___x_3153_;
goto v___jp_3138_;
}
}
}
}
else
{
lean_object* v_err_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3187_; 
lean_dec_ref(v_config_3120_);
v_err_3180_ = lean_ctor_get(v___x_3132_, 1);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3187_ == 0)
{
lean_object* v_unused_3188_; 
v_unused_3188_ = lean_ctor_get(v___x_3132_, 0);
lean_dec(v_unused_3188_);
v___x_3182_ = v___x_3132_;
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_err_3180_);
lean_dec(v___x_3132_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3185_; 
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 0, v_a_3121_);
v___x_3185_ = v___x_3182_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_3121_);
lean_ctor_set(v_reuseFailAlloc_3186_, 1, v_err_3180_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
}
}
v___jp_3122_:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3123_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1));
v___x_3124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3124_, 0, v_a_3121_);
lean_ctor_set(v___x_3124_, 1, v___x_3123_);
return v___x_3124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(lean_object* v_config_3189_, lean_object* v_scheme_3190_, lean_object* v_a_3191_){
_start:
{
lean_object* v_array_3192_; lean_object* v_idx_3193_; lean_object* v___x_3194_; uint8_t v___x_3195_; 
v_array_3192_ = lean_ctor_get(v_a_3191_, 0);
v_idx_3193_ = lean_ctor_get(v_a_3191_, 1);
v___x_3194_ = lean_byte_array_size(v_array_3192_);
v___x_3195_ = lean_nat_dec_lt(v_idx_3193_, v___x_3194_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; lean_object* v___x_3197_; 
lean_dec_ref(v_scheme_3190_);
lean_dec_ref(v_config_3189_);
v___x_3196_ = lean_box(0);
v___x_3197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3197_, 0, v_a_3191_);
lean_ctor_set(v___x_3197_, 1, v___x_3196_);
return v___x_3197_;
}
else
{
uint8_t v___x_3198_; uint8_t v_got_3199_; uint8_t v___x_3200_; 
v___x_3198_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v_got_3199_ = lean_byte_array_fget(v_array_3192_, v_idx_3193_);
v___x_3200_ = lean_uint8_dec_eq(v_got_3199_, v___x_3198_);
if (v___x_3200_ == 0)
{
lean_object* v___x_3201_; lean_object* v___x_3202_; 
lean_dec_ref(v_scheme_3190_);
lean_dec_ref(v_config_3189_);
v___x_3201_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
v___x_3202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3202_, 0, v_a_3191_);
lean_ctor_set(v___x_3202_, 1, v___x_3201_);
return v___x_3202_;
}
else
{
lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3277_; 
lean_inc(v_idx_3193_);
lean_inc_ref(v_array_3192_);
v_isSharedCheck_3277_ = !lean_is_exclusive(v_a_3191_);
if (v_isSharedCheck_3277_ == 0)
{
lean_object* v_unused_3278_; lean_object* v_unused_3279_; 
v_unused_3278_ = lean_ctor_get(v_a_3191_, 1);
lean_dec(v_unused_3278_);
v_unused_3279_ = lean_ctor_get(v_a_3191_, 0);
lean_dec(v_unused_3279_);
v___x_3204_ = v_a_3191_;
v_isShared_3205_ = v_isSharedCheck_3277_;
goto v_resetjp_3203_;
}
else
{
lean_dec(v_a_3191_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3277_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3209_; 
v___x_3206_ = lean_unsigned_to_nat(1u);
v___x_3207_ = lean_nat_add(v_idx_3193_, v___x_3206_);
lean_dec(v_idx_3193_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 1, v___x_3207_);
v___x_3209_ = v___x_3204_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_array_3192_);
lean_ctor_set(v_reuseFailAlloc_3276_, 1, v___x_3207_);
v___x_3209_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
lean_object* v___x_3210_; 
lean_inc_ref(v_config_3189_);
v___x_3210_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3189_, v___x_3209_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_res_3211_; lean_object* v_pos_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3266_; 
v_res_3211_ = lean_ctor_get(v___x_3210_, 1);
v_pos_3212_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3214_ = v___x_3210_;
v_isShared_3215_ = v_isSharedCheck_3266_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_res_3211_);
lean_inc(v_pos_3212_);
lean_dec(v___x_3210_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3266_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v_fst_3216_; lean_object* v_snd_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3265_; 
v_fst_3216_ = lean_ctor_get(v_res_3211_, 0);
v_snd_3217_ = lean_ctor_get(v_res_3211_, 1);
v_isSharedCheck_3265_ = !lean_is_exclusive(v_res_3211_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3219_ = v_res_3211_;
v_isShared_3220_ = v_isSharedCheck_3265_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_snd_3217_);
lean_inc(v_fst_3216_);
lean_dec(v_res_3211_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3265_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v_pos_3222_; lean_object* v_res_3223_; lean_object* v_array_3230_; lean_object* v_idx_3231_; lean_object* v_pos_3233_; lean_object* v_idx_3234_; lean_object* v_err_3235_; lean_object* v___x_3241_; uint8_t v___x_3242_; 
v_array_3230_ = lean_ctor_get(v_pos_3212_, 0);
v_idx_3231_ = lean_ctor_get(v_pos_3212_, 1);
lean_inc(v_idx_3231_);
v___x_3241_ = lean_byte_array_size(v_array_3230_);
v___x_3242_ = lean_nat_dec_lt(v_idx_3231_, v___x_3241_);
if (v___x_3242_ == 0)
{
lean_object* v___x_3243_; 
lean_dec_ref(v_config_3189_);
v___x_3243_ = lean_box(0);
lean_inc(v_idx_3231_);
v_pos_3233_ = v_pos_3212_;
v_idx_3234_ = v_idx_3231_;
v_err_3235_ = v___x_3243_;
goto v___jp_3232_;
}
else
{
uint8_t v___x_3244_; uint8_t v_got_3245_; uint8_t v___x_3246_; 
v___x_3244_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3245_ = lean_byte_array_fget(v_array_3230_, v_idx_3231_);
v___x_3246_ = lean_uint8_dec_eq(v_got_3245_, v___x_3244_);
if (v___x_3246_ == 0)
{
lean_object* v___x_3247_; 
lean_dec_ref(v_config_3189_);
v___x_3247_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3231_);
v_pos_3233_ = v_pos_3212_;
v_idx_3234_ = v_idx_3231_;
v_err_3235_ = v___x_3247_;
goto v___jp_3232_;
}
else
{
lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3262_; 
lean_inc_ref(v_array_3230_);
v_isSharedCheck_3262_ = !lean_is_exclusive(v_pos_3212_);
if (v_isSharedCheck_3262_ == 0)
{
lean_object* v_unused_3263_; lean_object* v_unused_3264_; 
v_unused_3263_ = lean_ctor_get(v_pos_3212_, 1);
lean_dec(v_unused_3263_);
v_unused_3264_ = lean_ctor_get(v_pos_3212_, 0);
lean_dec(v_unused_3264_);
v___x_3249_ = v_pos_3212_;
v_isShared_3250_ = v_isSharedCheck_3262_;
goto v_resetjp_3248_;
}
else
{
lean_dec(v_pos_3212_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3262_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3251_; lean_object* v___x_3253_; 
v___x_3251_ = lean_nat_add(v_idx_3231_, v___x_3206_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 1, v___x_3251_);
v___x_3253_ = v___x_3249_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_array_3230_);
lean_ctor_set(v_reuseFailAlloc_3261_, 1, v___x_3251_);
v___x_3253_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
lean_object* v___x_3254_; 
v___x_3254_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3189_, v___x_3253_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_pos_3255_; lean_object* v_res_3256_; lean_object* v___x_3257_; 
lean_dec(v_idx_3231_);
lean_del_object(v___x_3219_);
v_pos_3255_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_pos_3255_);
v_res_3256_ = lean_ctor_get(v___x_3254_, 1);
lean_inc(v_res_3256_);
lean_dec_ref_known(v___x_3254_, 2);
v___x_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3257_, 0, v_res_3256_);
v_pos_3222_ = v_pos_3255_;
v_res_3223_ = v___x_3257_;
goto v___jp_3221_;
}
else
{
lean_object* v_pos_3258_; lean_object* v_err_3259_; lean_object* v_idx_3260_; 
v_pos_3258_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_pos_3258_);
v_err_3259_ = lean_ctor_get(v___x_3254_, 1);
lean_inc(v_err_3259_);
lean_dec_ref_known(v___x_3254_, 2);
v_idx_3260_ = lean_ctor_get(v_pos_3258_, 1);
lean_inc(v_idx_3260_);
v_pos_3233_ = v_pos_3258_;
v_idx_3234_ = v_idx_3260_;
v_err_3235_ = v_err_3259_;
goto v___jp_3232_;
}
}
}
}
}
v___jp_3221_:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3228_; 
v___x_3224_ = lean_box(0);
v___x_3225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3225_, 0, v_scheme_3190_);
lean_ctor_set(v___x_3225_, 1, v_fst_3216_);
lean_ctor_set(v___x_3225_, 2, v_snd_3217_);
lean_ctor_set(v___x_3225_, 3, v_res_3223_);
lean_ctor_set(v___x_3225_, 4, v___x_3224_);
v___x_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3225_);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 1, v___x_3226_);
lean_ctor_set(v___x_3214_, 0, v_pos_3222_);
v___x_3228_ = v___x_3214_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_pos_3222_);
lean_ctor_set(v_reuseFailAlloc_3229_, 1, v___x_3226_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
v___jp_3232_:
{
uint8_t v___x_3236_; 
v___x_3236_ = lean_nat_dec_eq(v_idx_3231_, v_idx_3234_);
lean_dec(v_idx_3234_);
lean_dec(v_idx_3231_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3238_; 
lean_dec(v_snd_3217_);
lean_dec(v_fst_3216_);
lean_del_object(v___x_3214_);
lean_dec_ref(v_scheme_3190_);
if (v_isShared_3220_ == 0)
{
lean_ctor_set_tag(v___x_3219_, 1);
lean_ctor_set(v___x_3219_, 1, v_err_3235_);
lean_ctor_set(v___x_3219_, 0, v_pos_3233_);
v___x_3238_ = v___x_3219_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_pos_3233_);
lean_ctor_set(v_reuseFailAlloc_3239_, 1, v_err_3235_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
else
{
lean_object* v___x_3240_; 
lean_dec(v_err_3235_);
lean_del_object(v___x_3219_);
v___x_3240_ = lean_box(0);
v_pos_3222_ = v_pos_3233_;
v_res_3223_ = v___x_3240_;
goto v___jp_3221_;
}
}
}
}
}
else
{
lean_object* v_pos_3267_; lean_object* v_err_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3275_; 
lean_dec_ref(v_scheme_3190_);
lean_dec_ref(v_config_3189_);
v_pos_3267_ = lean_ctor_get(v___x_3210_, 0);
v_err_3268_ = lean_ctor_get(v___x_3210_, 1);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3270_ = v___x_3210_;
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_err_3268_);
lean_inc(v_pos_3267_);
lean_dec(v___x_3210_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3273_; 
if (v_isShared_3271_ == 0)
{
v___x_3273_ = v___x_3270_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_pos_3267_);
lean_ctor_set(v_reuseFailAlloc_3274_, 1, v_err_3268_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(lean_object* v_config_3288_, lean_object* v_a_3289_){
_start:
{
lean_object* v___x_3293_; 
lean_inc_ref(v_a_3289_);
v___x_3293_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3288_, v_a_3289_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v_pos_3294_; lean_object* v_res_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3391_; 
v_pos_3294_ = lean_ctor_get(v___x_3293_, 0);
v_res_3295_ = lean_ctor_get(v___x_3293_, 1);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3297_ = v___x_3293_;
v_isShared_3298_ = v_isSharedCheck_3391_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_res_3295_);
lean_inc(v_pos_3294_);
lean_dec(v___x_3293_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3391_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v_pos_3302_; lean_object* v_res_3303_; lean_object* v_idx_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v_pos_3314_; lean_object* v_idx_3315_; lean_object* v_err_3316_; lean_object* v___x_3385_; uint8_t v___x_3386_; 
v___x_3385_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2));
v___x_3386_ = lean_string_dec_eq(v_res_3295_, v___x_3385_);
if (v___x_3386_ == 0)
{
lean_object* v___x_3387_; uint8_t v___x_3388_; 
v___x_3387_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3));
v___x_3388_ = lean_string_dec_eq(v_res_3295_, v___x_3387_);
if (v___x_3388_ == 0)
{
lean_object* v___x_3389_; lean_object* v___x_3390_; 
lean_del_object(v___x_3297_);
lean_dec(v_res_3295_);
lean_dec(v_pos_3294_);
lean_dec_ref(v_config_3288_);
v___x_3389_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5));
v___x_3390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3390_, 0, v_a_3289_);
lean_ctor_set(v___x_3390_, 1, v___x_3389_);
return v___x_3390_;
}
else
{
goto v___jp_3320_;
}
}
else
{
goto v___jp_3320_;
}
v___jp_3299_:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3308_; 
v___x_3304_ = lean_box(0);
v___x_3305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3305_, 0, v_res_3295_);
lean_ctor_set(v___x_3305_, 1, v___y_3300_);
lean_ctor_set(v___x_3305_, 2, v___y_3301_);
lean_ctor_set(v___x_3305_, 3, v_res_3303_);
lean_ctor_set(v___x_3305_, 4, v___x_3304_);
v___x_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3305_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 1, v___x_3306_);
lean_ctor_set(v___x_3297_, 0, v_pos_3302_);
v___x_3308_ = v___x_3297_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_pos_3302_);
lean_ctor_set(v_reuseFailAlloc_3309_, 1, v___x_3306_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
v___jp_3310_:
{
uint8_t v___x_3317_; 
v___x_3317_ = lean_nat_dec_eq(v_idx_3311_, v_idx_3315_);
lean_dec(v_idx_3315_);
lean_dec(v_idx_3311_);
if (v___x_3317_ == 0)
{
lean_object* v___x_3318_; 
lean_dec_ref(v_pos_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_del_object(v___x_3297_);
lean_dec(v_res_3295_);
v___x_3318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3318_, 0, v_a_3289_);
lean_ctor_set(v___x_3318_, 1, v_err_3316_);
return v___x_3318_;
}
else
{
lean_object* v___x_3319_; 
lean_dec(v_err_3316_);
lean_dec_ref(v_a_3289_);
v___x_3319_ = lean_box(0);
v___y_3300_ = v___y_3312_;
v___y_3301_ = v___y_3313_;
v_pos_3302_ = v_pos_3314_;
v_res_3303_ = v___x_3319_;
goto v___jp_3299_;
}
}
v___jp_3320_:
{
lean_object* v_array_3321_; lean_object* v_idx_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3384_; 
v_array_3321_ = lean_ctor_get(v_pos_3294_, 0);
v_idx_3322_ = lean_ctor_get(v_pos_3294_, 1);
v_isSharedCheck_3384_ = !lean_is_exclusive(v_pos_3294_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3324_ = v_pos_3294_;
v_isShared_3325_ = v_isSharedCheck_3384_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_idx_3322_);
lean_inc(v_array_3321_);
lean_dec(v_pos_3294_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3384_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3326_; uint8_t v___x_3327_; 
v___x_3326_ = lean_byte_array_size(v_array_3321_);
v___x_3327_ = lean_nat_dec_lt(v_idx_3322_, v___x_3326_);
if (v___x_3327_ == 0)
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
lean_del_object(v___x_3324_);
lean_dec(v_idx_3322_);
lean_dec_ref(v_array_3321_);
lean_del_object(v___x_3297_);
lean_dec(v_res_3295_);
lean_dec_ref(v_config_3288_);
v___x_3328_ = lean_box(0);
v___x_3329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3329_, 0, v_a_3289_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
return v___x_3329_;
}
else
{
uint8_t v___x_3330_; uint8_t v_got_3331_; uint8_t v___x_3332_; 
v___x_3330_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v_got_3331_ = lean_byte_array_fget(v_array_3321_, v_idx_3322_);
v___x_3332_ = lean_uint8_dec_eq(v_got_3331_, v___x_3330_);
if (v___x_3332_ == 0)
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
lean_del_object(v___x_3324_);
lean_dec(v_idx_3322_);
lean_dec_ref(v_array_3321_);
lean_del_object(v___x_3297_);
lean_dec(v_res_3295_);
lean_dec_ref(v_config_3288_);
v___x_3333_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
v___x_3334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3334_, 0, v_a_3289_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
return v___x_3334_;
}
else
{
lean_object* v___x_3335_; lean_object* v___x_3336_; uint8_t v___x_3337_; 
v___x_3335_ = lean_unsigned_to_nat(1u);
v___x_3336_ = lean_nat_add(v_idx_3322_, v___x_3335_);
lean_dec(v_idx_3322_);
v___x_3337_ = lean_nat_dec_lt(v___x_3336_, v___x_3326_);
if (v___x_3337_ == 0)
{
lean_dec(v___x_3336_);
lean_del_object(v___x_3324_);
lean_dec_ref(v_array_3321_);
lean_del_object(v___x_3297_);
lean_dec(v_res_3295_);
lean_dec_ref(v_config_3288_);
goto v___jp_3290_;
}
else
{
uint8_t v___x_3338_; uint8_t v___x_3339_; uint8_t v___x_3340_; 
v___x_3338_ = lean_byte_array_fget(v_array_3321_, v___x_3336_);
v___x_3339_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_3340_ = lean_uint8_dec_eq(v___x_3338_, v___x_3339_);
if (v___x_3340_ == 0)
{
lean_dec(v___x_3336_);
lean_del_object(v___x_3324_);
lean_dec_ref(v_array_3321_);
lean_del_object(v___x_3297_);
lean_dec(v_res_3295_);
lean_dec_ref(v_config_3288_);
goto v___jp_3290_;
}
else
{
lean_object* v___x_3342_; 
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 1, v___x_3336_);
v___x_3342_ = v___x_3324_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_array_3321_);
lean_ctor_set(v_reuseFailAlloc_3383_, 1, v___x_3336_);
v___x_3342_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
lean_object* v___x_3343_; 
lean_inc_ref(v_config_3288_);
v___x_3343_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3288_, v___x_3342_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_res_3344_; lean_object* v_pos_3345_; lean_object* v_fst_3346_; lean_object* v_snd_3347_; lean_object* v_array_3348_; lean_object* v_idx_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; 
v_res_3344_ = lean_ctor_get(v___x_3343_, 1);
lean_inc(v_res_3344_);
v_pos_3345_ = lean_ctor_get(v___x_3343_, 0);
lean_inc(v_pos_3345_);
lean_dec_ref_known(v___x_3343_, 2);
v_fst_3346_ = lean_ctor_get(v_res_3344_, 0);
lean_inc(v_fst_3346_);
v_snd_3347_ = lean_ctor_get(v_res_3344_, 1);
lean_inc(v_snd_3347_);
lean_dec(v_res_3344_);
v_array_3348_ = lean_ctor_get(v_pos_3345_, 0);
v_idx_3349_ = lean_ctor_get(v_pos_3345_, 1);
lean_inc(v_idx_3349_);
v___x_3350_ = lean_byte_array_size(v_array_3348_);
v___x_3351_ = lean_nat_dec_lt(v_idx_3349_, v___x_3350_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3352_; 
lean_dec_ref(v_config_3288_);
v___x_3352_ = lean_box(0);
lean_inc(v_idx_3349_);
v_idx_3311_ = v_idx_3349_;
v___y_3312_ = v_fst_3346_;
v___y_3313_ = v_snd_3347_;
v_pos_3314_ = v_pos_3345_;
v_idx_3315_ = v_idx_3349_;
v_err_3316_ = v___x_3352_;
goto v___jp_3310_;
}
else
{
uint8_t v___x_3353_; uint8_t v_got_3354_; uint8_t v___x_3355_; 
v___x_3353_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3354_ = lean_byte_array_fget(v_array_3348_, v_idx_3349_);
v___x_3355_ = lean_uint8_dec_eq(v_got_3354_, v___x_3353_);
if (v___x_3355_ == 0)
{
lean_object* v___x_3356_; 
lean_dec_ref(v_config_3288_);
v___x_3356_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3349_);
v_idx_3311_ = v_idx_3349_;
v___y_3312_ = v_fst_3346_;
v___y_3313_ = v_snd_3347_;
v_pos_3314_ = v_pos_3345_;
v_idx_3315_ = v_idx_3349_;
v_err_3316_ = v___x_3356_;
goto v___jp_3310_;
}
else
{
lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3371_; 
lean_inc_ref(v_array_3348_);
v_isSharedCheck_3371_ = !lean_is_exclusive(v_pos_3345_);
if (v_isSharedCheck_3371_ == 0)
{
lean_object* v_unused_3372_; lean_object* v_unused_3373_; 
v_unused_3372_ = lean_ctor_get(v_pos_3345_, 1);
lean_dec(v_unused_3372_);
v_unused_3373_ = lean_ctor_get(v_pos_3345_, 0);
lean_dec(v_unused_3373_);
v___x_3358_ = v_pos_3345_;
v_isShared_3359_ = v_isSharedCheck_3371_;
goto v_resetjp_3357_;
}
else
{
lean_dec(v_pos_3345_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3371_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3360_; lean_object* v___x_3362_; 
v___x_3360_ = lean_nat_add(v_idx_3349_, v___x_3335_);
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 1, v___x_3360_);
v___x_3362_ = v___x_3358_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_array_3348_);
lean_ctor_set(v_reuseFailAlloc_3370_, 1, v___x_3360_);
v___x_3362_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
lean_object* v___x_3363_; 
v___x_3363_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3288_, v___x_3362_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_pos_3364_; lean_object* v_res_3365_; lean_object* v___x_3366_; 
lean_dec(v_idx_3349_);
lean_dec_ref(v_a_3289_);
v_pos_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_pos_3364_);
v_res_3365_ = lean_ctor_get(v___x_3363_, 1);
lean_inc(v_res_3365_);
lean_dec_ref_known(v___x_3363_, 2);
v___x_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3366_, 0, v_res_3365_);
v___y_3300_ = v_fst_3346_;
v___y_3301_ = v_snd_3347_;
v_pos_3302_ = v_pos_3364_;
v_res_3303_ = v___x_3366_;
goto v___jp_3299_;
}
else
{
lean_object* v_pos_3367_; lean_object* v_err_3368_; lean_object* v_idx_3369_; 
v_pos_3367_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_pos_3367_);
v_err_3368_ = lean_ctor_get(v___x_3363_, 1);
lean_inc(v_err_3368_);
lean_dec_ref_known(v___x_3363_, 2);
v_idx_3369_ = lean_ctor_get(v_pos_3367_, 1);
lean_inc(v_idx_3369_);
v_idx_3311_ = v_idx_3349_;
v___y_3312_ = v_fst_3346_;
v___y_3313_ = v_snd_3347_;
v_pos_3314_ = v_pos_3367_;
v_idx_3315_ = v_idx_3369_;
v_err_3316_ = v_err_3368_;
goto v___jp_3310_;
}
}
}
}
}
}
else
{
lean_object* v_err_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
lean_del_object(v___x_3297_);
lean_dec(v_res_3295_);
lean_dec_ref(v_config_3288_);
v_err_3374_ = lean_ctor_get(v___x_3343_, 1);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3381_ == 0)
{
lean_object* v_unused_3382_; 
v_unused_3382_ = lean_ctor_get(v___x_3343_, 0);
lean_dec(v_unused_3382_);
v___x_3376_ = v___x_3343_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_err_3374_);
lean_dec(v___x_3343_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3379_; 
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 0, v_a_3289_);
v___x_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3289_);
lean_ctor_set(v_reuseFailAlloc_3380_, 1, v_err_3374_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
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
lean_object* v_err_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
lean_dec_ref(v_config_3288_);
v_err_3392_ = lean_ctor_get(v___x_3293_, 1);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3399_ == 0)
{
lean_object* v_unused_3400_; 
v_unused_3400_ = lean_ctor_get(v___x_3293_, 0);
lean_dec(v_unused_3400_);
v___x_3394_ = v___x_3293_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_err_3392_);
lean_dec(v___x_3293_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
lean_ctor_set(v___x_3394_, 0, v_a_3289_);
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3289_);
lean_ctor_set(v_reuseFailAlloc_3398_, 1, v_err_3392_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
v___jp_3290_:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3291_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1));
v___x_3292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3292_, 0, v_a_3289_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
return v___x_3292_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(lean_object* v_config_3401_, lean_object* v_a_3402_){
_start:
{
lean_object* v___x_3403_; 
lean_inc_ref(v_a_3402_);
v___x_3403_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_object* v_pos_3404_; lean_object* v_res_3405_; lean_object* v___x_3406_; 
v_pos_3404_ = lean_ctor_get(v___x_3403_, 0);
lean_inc(v_pos_3404_);
v_res_3405_ = lean_ctor_get(v___x_3403_, 1);
lean_inc(v_res_3405_);
lean_dec_ref_known(v___x_3403_, 2);
v___x_3406_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(v_config_3401_, v_res_3405_, v_pos_3404_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_dec_ref(v_a_3402_);
return v___x_3406_;
}
else
{
lean_object* v_err_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
v_err_3407_ = lean_ctor_get(v___x_3406_, 1);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3414_ == 0)
{
lean_object* v_unused_3415_; 
v_unused_3415_ = lean_ctor_get(v___x_3406_, 0);
lean_dec(v_unused_3415_);
v___x_3409_ = v___x_3406_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_err_3407_);
lean_dec(v___x_3406_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v_a_3402_);
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3402_);
lean_ctor_set(v_reuseFailAlloc_3413_, 1, v_err_3407_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
else
{
lean_object* v_err_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
lean_dec_ref(v_config_3401_);
v_err_3416_ = lean_ctor_get(v___x_3403_, 1);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3423_ == 0)
{
lean_object* v_unused_3424_; 
v_unused_3424_ = lean_ctor_get(v___x_3403_, 0);
lean_dec(v_unused_3424_);
v___x_3418_ = v___x_3403_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_err_3416_);
lean_dec(v___x_3403_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v_a_3402_);
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3402_);
lean_ctor_set(v_reuseFailAlloc_3422_, 1, v_err_3416_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(lean_object* v_config_3425_, lean_object* v_a_3426_){
_start:
{
lean_object* v___x_3427_; 
lean_inc_ref(v_a_3426_);
v___x_3427_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3425_, v_a_3426_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_pos_3428_; lean_object* v_res_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3481_; 
v_pos_3428_ = lean_ctor_get(v___x_3427_, 0);
v_res_3429_ = lean_ctor_get(v___x_3427_, 1);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3431_ = v___x_3427_;
v_isShared_3432_ = v_isSharedCheck_3481_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_res_3429_);
lean_inc(v_pos_3428_);
lean_dec(v___x_3427_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3481_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v_array_3433_; lean_object* v_idx_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3480_; 
v_array_3433_ = lean_ctor_get(v_pos_3428_, 0);
v_idx_3434_ = lean_ctor_get(v_pos_3428_, 1);
v_isSharedCheck_3480_ = !lean_is_exclusive(v_pos_3428_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3436_ = v_pos_3428_;
v_isShared_3437_ = v_isSharedCheck_3480_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_idx_3434_);
lean_inc(v_array_3433_);
lean_dec(v_pos_3428_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3480_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3438_; uint8_t v___x_3439_; 
v___x_3438_ = lean_byte_array_size(v_array_3433_);
v___x_3439_ = lean_nat_dec_lt(v_idx_3434_, v___x_3438_);
if (v___x_3439_ == 0)
{
lean_object* v___x_3440_; lean_object* v___x_3442_; 
lean_del_object(v___x_3436_);
lean_dec(v_idx_3434_);
lean_dec_ref(v_array_3433_);
lean_dec(v_res_3429_);
v___x_3440_ = lean_box(0);
if (v_isShared_3432_ == 0)
{
lean_ctor_set_tag(v___x_3431_, 1);
lean_ctor_set(v___x_3431_, 1, v___x_3440_);
lean_ctor_set(v___x_3431_, 0, v_a_3426_);
v___x_3442_ = v___x_3431_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3426_);
lean_ctor_set(v_reuseFailAlloc_3443_, 1, v___x_3440_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
else
{
uint8_t v___x_3444_; uint8_t v_got_3445_; uint8_t v___x_3446_; 
v___x_3444_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v_got_3445_ = lean_byte_array_fget(v_array_3433_, v_idx_3434_);
v___x_3446_ = lean_uint8_dec_eq(v_got_3445_, v___x_3444_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; lean_object* v___x_3449_; 
lean_del_object(v___x_3436_);
lean_dec(v_idx_3434_);
lean_dec_ref(v_array_3433_);
lean_dec(v_res_3429_);
v___x_3447_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
if (v_isShared_3432_ == 0)
{
lean_ctor_set_tag(v___x_3431_, 1);
lean_ctor_set(v___x_3431_, 1, v___x_3447_);
lean_ctor_set(v___x_3431_, 0, v_a_3426_);
v___x_3449_ = v___x_3431_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3426_);
lean_ctor_set(v_reuseFailAlloc_3450_, 1, v___x_3447_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
else
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3454_; 
lean_del_object(v___x_3431_);
v___x_3451_ = lean_unsigned_to_nat(1u);
v___x_3452_ = lean_nat_add(v_idx_3434_, v___x_3451_);
lean_dec(v_idx_3434_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 1, v___x_3452_);
v___x_3454_ = v___x_3436_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_array_3433_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v___x_3452_);
v___x_3454_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
lean_object* v___x_3455_; 
v___x_3455_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_3454_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_pos_3456_; lean_object* v_res_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3469_; 
lean_dec_ref(v_a_3426_);
v_pos_3456_ = lean_ctor_get(v___x_3455_, 0);
v_res_3457_ = lean_ctor_get(v___x_3455_, 1);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3459_ = v___x_3455_;
v_isShared_3460_ = v_isSharedCheck_3469_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_res_3457_);
lean_inc(v_pos_3456_);
lean_dec(v___x_3455_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3469_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3461_; lean_object* v___x_3462_; uint16_t v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3467_; 
v___x_3461_ = lean_box(0);
v___x_3462_ = lean_alloc_ctor(2, 0, 2);
v___x_3463_ = lean_unbox(v_res_3457_);
lean_dec(v_res_3457_);
lean_ctor_set_uint16(v___x_3462_, 0, v___x_3463_);
v___x_3464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3461_);
lean_ctor_set(v___x_3464_, 1, v_res_3429_);
lean_ctor_set(v___x_3464_, 2, v___x_3462_);
v___x_3465_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3464_);
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 1, v___x_3465_);
v___x_3467_ = v___x_3459_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_pos_3456_);
lean_ctor_set(v_reuseFailAlloc_3468_, 1, v___x_3465_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
else
{
lean_object* v_err_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3477_; 
lean_dec(v_res_3429_);
v_err_3470_ = lean_ctor_get(v___x_3455_, 1);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3477_ == 0)
{
lean_object* v_unused_3478_; 
v_unused_3478_ = lean_ctor_get(v___x_3455_, 0);
lean_dec(v_unused_3478_);
v___x_3472_ = v___x_3455_;
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_err_3470_);
lean_dec(v___x_3455_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3475_; 
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 0, v_a_3426_);
v___x_3475_ = v___x_3472_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3426_);
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
}
}
}
else
{
lean_object* v_err_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
v_err_3482_ = lean_ctor_get(v___x_3427_, 1);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3489_ == 0)
{
lean_object* v_unused_3490_; 
v_unused_3490_ = lean_ctor_get(v___x_3427_, 0);
lean_dec(v_unused_3490_);
v___x_3484_ = v___x_3427_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_err_3482_);
lean_dec(v___x_3427_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 0, v_a_3426_);
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3426_);
lean_ctor_set(v_reuseFailAlloc_3488_, 1, v_err_3482_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority___boxed(lean_object* v_config_3491_, lean_object* v_a_3492_){
_start:
{
lean_object* v_res_3493_; 
v_res_3493_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3491_, v_a_3492_);
lean_dec_ref(v_config_3491_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object* v_config_3494_, lean_object* v_a_3495_){
_start:
{
lean_object* v___x_3496_; 
lean_inc_ref(v_a_3495_);
v___x_3496_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(v_a_3495_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_dec_ref(v_a_3495_);
lean_dec_ref(v_config_3494_);
return v___x_3496_;
}
else
{
lean_object* v_pos_3497_; lean_object* v_idx_3498_; lean_object* v_idx_3499_; uint8_t v___x_3500_; 
v_pos_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_pos_3497_);
v_idx_3498_ = lean_ctor_get(v_a_3495_, 1);
lean_inc(v_idx_3498_);
lean_dec_ref(v_a_3495_);
v_idx_3499_ = lean_ctor_get(v_pos_3497_, 1);
lean_inc(v_idx_3499_);
v___x_3500_ = lean_nat_dec_eq(v_idx_3498_, v_idx_3499_);
lean_dec(v_idx_3498_);
if (v___x_3500_ == 0)
{
lean_dec(v_idx_3499_);
lean_dec(v_pos_3497_);
lean_dec_ref(v_config_3494_);
return v___x_3496_;
}
else
{
lean_object* v___x_3501_; 
lean_dec_ref_known(v___x_3496_, 2);
lean_inc_ref(v_config_3494_);
v___x_3501_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(v_config_3494_, v_pos_3497_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_dec(v_idx_3499_);
lean_dec_ref(v_config_3494_);
return v___x_3501_;
}
else
{
lean_object* v_pos_3502_; lean_object* v_idx_3503_; uint8_t v___x_3504_; 
v_pos_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_pos_3502_);
v_idx_3503_ = lean_ctor_get(v_pos_3502_, 1);
lean_inc(v_idx_3503_);
v___x_3504_ = lean_nat_dec_eq(v_idx_3499_, v_idx_3503_);
lean_dec(v_idx_3499_);
if (v___x_3504_ == 0)
{
lean_dec(v_idx_3503_);
lean_dec(v_pos_3502_);
lean_dec_ref(v_config_3494_);
return v___x_3501_;
}
else
{
lean_object* v___x_3505_; 
lean_dec_ref_known(v___x_3501_, 2);
lean_inc_ref(v_config_3494_);
v___x_3505_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(v_config_3494_, v_pos_3502_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_dec(v_idx_3503_);
lean_dec_ref(v_config_3494_);
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
lean_dec_ref(v_config_3494_);
return v___x_3505_;
}
else
{
lean_object* v___x_3509_; 
lean_dec_ref_known(v___x_3505_, 2);
v___x_3509_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3494_, v_pos_3506_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_dec(v_idx_3507_);
lean_dec_ref(v_config_3494_);
return v___x_3509_;
}
else
{
lean_object* v_pos_3510_; lean_object* v_idx_3511_; uint8_t v___x_3512_; 
v_pos_3510_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_pos_3510_);
v_idx_3511_ = lean_ctor_get(v_pos_3510_, 1);
v___x_3512_ = lean_nat_dec_eq(v_idx_3507_, v_idx_3511_);
lean_dec(v_idx_3507_);
if (v___x_3512_ == 0)
{
lean_dec(v_pos_3510_);
lean_dec_ref(v_config_3494_);
return v___x_3509_;
}
else
{
lean_object* v___x_3513_; 
lean_dec_ref_known(v___x_3509_, 2);
v___x_3513_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(v_config_3494_, v_pos_3510_);
return v___x_3513_;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(lean_object* v_config_3517_, lean_object* v_a_3518_){
_start:
{
lean_object* v___x_3519_; 
v___x_3519_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_3517_, v_a_3518_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_pos_3520_; lean_object* v_res_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3534_; 
v_pos_3520_ = lean_ctor_get(v___x_3519_, 0);
v_res_3521_ = lean_ctor_get(v___x_3519_, 1);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3523_ = v___x_3519_;
v_isShared_3524_ = v_isSharedCheck_3534_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_res_3521_);
lean_inc(v_pos_3520_);
lean_dec(v___x_3519_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3534_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3525_; 
v___x_3525_ = l_Std_Http_URI_EncodedFragment_decode(v_res_3521_);
lean_dec(v_res_3521_);
if (lean_obj_tag(v___x_3525_) == 1)
{
lean_object* v_val_3526_; lean_object* v___x_3528_; 
v_val_3526_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_val_3526_);
lean_dec_ref_known(v___x_3525_, 1);
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 1, v_val_3526_);
v___x_3528_ = v___x_3523_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_pos_3520_);
lean_ctor_set(v_reuseFailAlloc_3529_, 1, v_val_3526_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
else
{
lean_object* v___x_3530_; lean_object* v___x_3532_; 
lean_dec(v___x_3525_);
v___x_3530_ = ((lean_object*)(l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___closed__1));
if (v_isShared_3524_ == 0)
{
lean_ctor_set_tag(v___x_3523_, 1);
lean_ctor_set(v___x_3523_, 1, v___x_3530_);
v___x_3532_ = v___x_3523_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_pos_3520_);
lean_ctor_set(v_reuseFailAlloc_3533_, 1, v___x_3530_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
else
{
lean_object* v_pos_3535_; lean_object* v_err_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
v_pos_3535_ = lean_ctor_get(v___x_3519_, 0);
v_err_3536_ = lean_ctor_get(v___x_3519_, 1);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3538_ = v___x_3519_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_err_3536_);
lean_inc(v_pos_3535_);
lean_dec(v___x_3519_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_pos_3535_);
lean_ctor_set(v_reuseFailAlloc_3542_, 1, v_err_3536_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment___boxed(lean_object* v_config_3544_, lean_object* v_a_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3544_, v_a_3545_);
lean_dec_ref(v_config_3544_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_uri(lean_object* v_config_3547_, lean_object* v_a_3548_){
_start:
{
lean_object* v___x_3549_; 
lean_inc_ref(v_a_3548_);
v___x_3549_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3547_, v_a_3548_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v_pos_3550_; lean_object* v_res_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3680_; 
v_pos_3550_ = lean_ctor_get(v___x_3549_, 0);
v_res_3551_ = lean_ctor_get(v___x_3549_, 1);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3553_ = v___x_3549_;
v_isShared_3554_ = v_isSharedCheck_3680_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_res_3551_);
lean_inc(v_pos_3550_);
lean_dec(v___x_3549_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3680_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v_array_3555_; lean_object* v_idx_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3679_; 
v_array_3555_ = lean_ctor_get(v_pos_3550_, 0);
v_idx_3556_ = lean_ctor_get(v_pos_3550_, 1);
v_isSharedCheck_3679_ = !lean_is_exclusive(v_pos_3550_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3558_ = v_pos_3550_;
v_isShared_3559_ = v_isSharedCheck_3679_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_idx_3556_);
lean_inc(v_array_3555_);
lean_dec(v_pos_3550_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3679_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3560_; uint8_t v___x_3561_; 
v___x_3560_ = lean_byte_array_size(v_array_3555_);
v___x_3561_ = lean_nat_dec_lt(v_idx_3556_, v___x_3560_);
if (v___x_3561_ == 0)
{
lean_object* v___x_3562_; lean_object* v___x_3564_; 
lean_del_object(v___x_3558_);
lean_dec(v_idx_3556_);
lean_dec_ref(v_array_3555_);
lean_dec(v_res_3551_);
lean_dec_ref(v_config_3547_);
v___x_3562_ = lean_box(0);
if (v_isShared_3554_ == 0)
{
lean_ctor_set_tag(v___x_3553_, 1);
lean_ctor_set(v___x_3553_, 1, v___x_3562_);
lean_ctor_set(v___x_3553_, 0, v_a_3548_);
v___x_3564_ = v___x_3553_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3548_);
lean_ctor_set(v_reuseFailAlloc_3565_, 1, v___x_3562_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
else
{
uint8_t v___x_3566_; uint8_t v_got_3567_; uint8_t v___x_3568_; 
v___x_3566_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v_got_3567_ = lean_byte_array_fget(v_array_3555_, v_idx_3556_);
v___x_3568_ = lean_uint8_dec_eq(v_got_3567_, v___x_3566_);
if (v___x_3568_ == 0)
{
lean_object* v___x_3569_; lean_object* v___x_3571_; 
lean_del_object(v___x_3558_);
lean_dec(v_idx_3556_);
lean_dec_ref(v_array_3555_);
lean_dec(v_res_3551_);
lean_dec_ref(v_config_3547_);
v___x_3569_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
if (v_isShared_3554_ == 0)
{
lean_ctor_set_tag(v___x_3553_, 1);
lean_ctor_set(v___x_3553_, 1, v___x_3569_);
lean_ctor_set(v___x_3553_, 0, v_a_3548_);
v___x_3571_ = v___x_3553_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_a_3548_);
lean_ctor_set(v_reuseFailAlloc_3572_, 1, v___x_3569_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
else
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3576_; 
v___x_3573_ = lean_unsigned_to_nat(1u);
v___x_3574_ = lean_nat_add(v_idx_3556_, v___x_3573_);
lean_dec(v_idx_3556_);
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 1, v___x_3574_);
v___x_3576_ = v___x_3558_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_array_3555_);
lean_ctor_set(v_reuseFailAlloc_3678_, 1, v___x_3574_);
v___x_3576_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
lean_object* v___x_3577_; 
lean_inc_ref(v_config_3547_);
v___x_3577_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3547_, v___x_3576_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v_res_3578_; lean_object* v_pos_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3668_; 
v_res_3578_ = lean_ctor_get(v___x_3577_, 1);
v_pos_3579_ = lean_ctor_get(v___x_3577_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3581_ = v___x_3577_;
v_isShared_3582_ = v_isSharedCheck_3668_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_res_3578_);
lean_inc(v_pos_3579_);
lean_dec(v___x_3577_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3668_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v_fst_3583_; lean_object* v_snd_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3667_; 
v_fst_3583_ = lean_ctor_get(v_res_3578_, 0);
v_snd_3584_ = lean_ctor_get(v_res_3578_, 1);
v_isSharedCheck_3667_ = !lean_is_exclusive(v_res_3578_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3586_ = v_res_3578_;
v_isShared_3587_ = v_isSharedCheck_3667_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_snd_3584_);
lean_inc(v_fst_3583_);
lean_dec(v_res_3578_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3667_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___y_3589_; lean_object* v_pos_3590_; lean_object* v_res_3591_; lean_object* v_idx_3598_; lean_object* v___y_3599_; lean_object* v_pos_3600_; lean_object* v_err_3601_; lean_object* v_pos_3609_; lean_object* v_array_3610_; lean_object* v_idx_3611_; lean_object* v_res_3612_; lean_object* v_array_3630_; lean_object* v_idx_3631_; lean_object* v_pos_3633_; lean_object* v_array_3634_; lean_object* v_idx_3635_; lean_object* v_err_3636_; lean_object* v___x_3640_; uint8_t v___x_3641_; 
v_array_3630_ = lean_ctor_get(v_pos_3579_, 0);
lean_inc_ref(v_array_3630_);
v_idx_3631_ = lean_ctor_get(v_pos_3579_, 1);
lean_inc(v_idx_3631_);
v___x_3640_ = lean_byte_array_size(v_array_3630_);
v___x_3641_ = lean_nat_dec_lt(v_idx_3631_, v___x_3640_);
if (v___x_3641_ == 0)
{
lean_object* v___x_3642_; 
v___x_3642_ = lean_box(0);
lean_inc(v_idx_3631_);
v_pos_3633_ = v_pos_3579_;
v_array_3634_ = v_array_3630_;
v_idx_3635_ = v_idx_3631_;
v_err_3636_ = v___x_3642_;
goto v___jp_3632_;
}
else
{
uint8_t v___x_3643_; uint8_t v_got_3644_; uint8_t v___x_3645_; 
v___x_3643_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3644_ = lean_byte_array_fget(v_array_3630_, v_idx_3631_);
v___x_3645_ = lean_uint8_dec_eq(v_got_3644_, v___x_3643_);
if (v___x_3645_ == 0)
{
lean_object* v___x_3646_; 
v___x_3646_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3631_);
v_pos_3633_ = v_pos_3579_;
v_array_3634_ = v_array_3630_;
v_idx_3635_ = v_idx_3631_;
v_err_3636_ = v___x_3646_;
goto v___jp_3632_;
}
else
{
lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3664_; 
v_isSharedCheck_3664_ = !lean_is_exclusive(v_pos_3579_);
if (v_isSharedCheck_3664_ == 0)
{
lean_object* v_unused_3665_; lean_object* v_unused_3666_; 
v_unused_3665_ = lean_ctor_get(v_pos_3579_, 1);
lean_dec(v_unused_3665_);
v_unused_3666_ = lean_ctor_get(v_pos_3579_, 0);
lean_dec(v_unused_3666_);
v___x_3648_ = v_pos_3579_;
v_isShared_3649_ = v_isSharedCheck_3664_;
goto v_resetjp_3647_;
}
else
{
lean_dec(v_pos_3579_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3664_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3650_; lean_object* v___x_3652_; 
v___x_3650_ = lean_nat_add(v_idx_3631_, v___x_3573_);
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 1, v___x_3650_);
v___x_3652_ = v___x_3648_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_array_3630_);
lean_ctor_set(v_reuseFailAlloc_3663_, 1, v___x_3650_);
v___x_3652_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
lean_object* v___x_3653_; 
lean_inc_ref(v_config_3547_);
v___x_3653_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3547_, v___x_3652_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_pos_3654_; lean_object* v_res_3655_; lean_object* v_array_3656_; lean_object* v_idx_3657_; lean_object* v___x_3658_; 
lean_dec(v_idx_3631_);
v_pos_3654_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_pos_3654_);
v_res_3655_ = lean_ctor_get(v___x_3653_, 1);
lean_inc(v_res_3655_);
lean_dec_ref_known(v___x_3653_, 2);
v_array_3656_ = lean_ctor_get(v_pos_3654_, 0);
lean_inc_ref(v_array_3656_);
v_idx_3657_ = lean_ctor_get(v_pos_3654_, 1);
lean_inc(v_idx_3657_);
v___x_3658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3658_, 0, v_res_3655_);
v_pos_3609_ = v_pos_3654_;
v_array_3610_ = v_array_3656_;
v_idx_3611_ = v_idx_3657_;
v_res_3612_ = v___x_3658_;
goto v___jp_3608_;
}
else
{
lean_object* v_pos_3659_; lean_object* v_err_3660_; lean_object* v_array_3661_; lean_object* v_idx_3662_; 
v_pos_3659_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_pos_3659_);
v_err_3660_ = lean_ctor_get(v___x_3653_, 1);
lean_inc(v_err_3660_);
lean_dec_ref_known(v___x_3653_, 2);
v_array_3661_ = lean_ctor_get(v_pos_3659_, 0);
lean_inc_ref(v_array_3661_);
v_idx_3662_ = lean_ctor_get(v_pos_3659_, 1);
lean_inc(v_idx_3662_);
v_pos_3633_ = v_pos_3659_;
v_array_3634_ = v_array_3661_;
v_idx_3635_ = v_idx_3662_;
v_err_3636_ = v_err_3660_;
goto v___jp_3632_;
}
}
}
}
}
v___jp_3588_:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3595_; 
v___x_3592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3592_, 0, v_res_3551_);
lean_ctor_set(v___x_3592_, 1, v_fst_3583_);
lean_ctor_set(v___x_3592_, 2, v_snd_3584_);
lean_ctor_set(v___x_3592_, 3, v___y_3589_);
lean_ctor_set(v___x_3592_, 4, v_res_3591_);
v___x_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 1, v___x_3593_);
lean_ctor_set(v___x_3581_, 0, v_pos_3590_);
v___x_3595_ = v___x_3581_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_pos_3590_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v___x_3593_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
v___jp_3597_:
{
lean_object* v_idx_3602_; uint8_t v___x_3603_; 
v_idx_3602_ = lean_ctor_get(v_pos_3600_, 1);
v___x_3603_ = lean_nat_dec_eq(v_idx_3598_, v_idx_3602_);
lean_dec(v_idx_3598_);
if (v___x_3603_ == 0)
{
lean_object* v___x_3605_; 
lean_dec_ref(v_pos_3600_);
lean_dec(v___y_3599_);
lean_dec(v_snd_3584_);
lean_dec(v_fst_3583_);
lean_del_object(v___x_3581_);
lean_dec(v_res_3551_);
if (v_isShared_3554_ == 0)
{
lean_ctor_set_tag(v___x_3553_, 1);
lean_ctor_set(v___x_3553_, 1, v_err_3601_);
lean_ctor_set(v___x_3553_, 0, v_a_3548_);
v___x_3605_ = v___x_3553_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3548_);
lean_ctor_set(v_reuseFailAlloc_3606_, 1, v_err_3601_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
else
{
lean_object* v___x_3607_; 
lean_dec(v_err_3601_);
lean_del_object(v___x_3553_);
lean_dec_ref(v_a_3548_);
v___x_3607_ = lean_box(0);
v___y_3589_ = v___y_3599_;
v_pos_3590_ = v_pos_3600_;
v_res_3591_ = v___x_3607_;
goto v___jp_3588_;
}
}
v___jp_3608_:
{
lean_object* v___x_3613_; uint8_t v___x_3614_; 
v___x_3613_ = lean_byte_array_size(v_array_3610_);
v___x_3614_ = lean_nat_dec_lt(v_idx_3611_, v___x_3613_);
if (v___x_3614_ == 0)
{
lean_object* v___x_3615_; 
lean_dec_ref(v_array_3610_);
lean_del_object(v___x_3586_);
lean_dec_ref(v_config_3547_);
v___x_3615_ = lean_box(0);
v_idx_3598_ = v_idx_3611_;
v___y_3599_ = v_res_3612_;
v_pos_3600_ = v_pos_3609_;
v_err_3601_ = v___x_3615_;
goto v___jp_3597_;
}
else
{
uint8_t v___x_3616_; uint8_t v_got_3617_; uint8_t v___x_3618_; 
v___x_3616_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v_got_3617_ = lean_byte_array_fget(v_array_3610_, v_idx_3611_);
v___x_3618_ = lean_uint8_dec_eq(v_got_3617_, v___x_3616_);
if (v___x_3618_ == 0)
{
lean_object* v___x_3619_; 
lean_dec_ref(v_array_3610_);
lean_del_object(v___x_3586_);
lean_dec_ref(v_config_3547_);
v___x_3619_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__4, &l_Std_Http_URI_Parser_parseURI___closed__4_once, _init_l_Std_Http_URI_Parser_parseURI___closed__4);
v_idx_3598_ = v_idx_3611_;
v___y_3599_ = v_res_3612_;
v_pos_3600_ = v_pos_3609_;
v_err_3601_ = v___x_3619_;
goto v___jp_3597_;
}
else
{
lean_object* v___x_3620_; lean_object* v___x_3622_; 
lean_dec_ref(v_pos_3609_);
v___x_3620_ = lean_nat_add(v_idx_3611_, v___x_3573_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 1, v___x_3620_);
lean_ctor_set(v___x_3586_, 0, v_array_3610_);
v___x_3622_ = v___x_3586_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_array_3610_);
lean_ctor_set(v_reuseFailAlloc_3629_, 1, v___x_3620_);
v___x_3622_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
lean_object* v___x_3623_; 
v___x_3623_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3547_, v___x_3622_);
lean_dec_ref(v_config_3547_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_pos_3624_; lean_object* v_res_3625_; lean_object* v___x_3626_; 
lean_dec(v_idx_3611_);
lean_del_object(v___x_3553_);
lean_dec_ref(v_a_3548_);
v_pos_3624_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_pos_3624_);
v_res_3625_ = lean_ctor_get(v___x_3623_, 1);
lean_inc(v_res_3625_);
lean_dec_ref_known(v___x_3623_, 2);
v___x_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3626_, 0, v_res_3625_);
v___y_3589_ = v_res_3612_;
v_pos_3590_ = v_pos_3624_;
v_res_3591_ = v___x_3626_;
goto v___jp_3588_;
}
else
{
lean_object* v_pos_3627_; lean_object* v_err_3628_; 
v_pos_3627_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_pos_3627_);
v_err_3628_ = lean_ctor_get(v___x_3623_, 1);
lean_inc(v_err_3628_);
lean_dec_ref_known(v___x_3623_, 2);
v_idx_3598_ = v_idx_3611_;
v___y_3599_ = v_res_3612_;
v_pos_3600_ = v_pos_3627_;
v_err_3601_ = v_err_3628_;
goto v___jp_3597_;
}
}
}
}
}
v___jp_3632_:
{
uint8_t v___x_3637_; 
v___x_3637_ = lean_nat_dec_eq(v_idx_3631_, v_idx_3635_);
lean_dec(v_idx_3631_);
if (v___x_3637_ == 0)
{
lean_object* v___x_3638_; 
lean_dec(v_idx_3635_);
lean_dec_ref(v_array_3634_);
lean_dec_ref(v_pos_3633_);
lean_del_object(v___x_3586_);
lean_dec(v_snd_3584_);
lean_dec(v_fst_3583_);
lean_del_object(v___x_3581_);
lean_del_object(v___x_3553_);
lean_dec(v_res_3551_);
lean_dec_ref(v_config_3547_);
v___x_3638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3638_, 0, v_a_3548_);
lean_ctor_set(v___x_3638_, 1, v_err_3636_);
return v___x_3638_;
}
else
{
lean_object* v___x_3639_; 
lean_dec(v_err_3636_);
v___x_3639_ = lean_box(0);
v_pos_3609_ = v_pos_3633_;
v_array_3610_ = v_array_3634_;
v_idx_3611_ = v_idx_3635_;
v_res_3612_ = v___x_3639_;
goto v___jp_3608_;
}
}
}
}
}
else
{
lean_object* v_err_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3676_; 
lean_del_object(v___x_3553_);
lean_dec(v_res_3551_);
lean_dec_ref(v_config_3547_);
v_err_3669_ = lean_ctor_get(v___x_3577_, 1);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3676_ == 0)
{
lean_object* v_unused_3677_; 
v_unused_3677_ = lean_ctor_get(v___x_3577_, 0);
lean_dec(v_unused_3677_);
v___x_3671_ = v___x_3577_;
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_err_3669_);
lean_dec(v___x_3577_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3674_; 
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 0, v_a_3548_);
v___x_3674_ = v___x_3671_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3548_);
lean_ctor_set(v_reuseFailAlloc_3675_, 1, v_err_3669_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
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
lean_object* v_err_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_dec_ref(v_config_3547_);
v_err_3681_ = lean_ctor_get(v___x_3549_, 1);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3688_ == 0)
{
lean_object* v_unused_3689_; 
v_unused_3689_ = lean_ctor_get(v___x_3549_, 0);
lean_dec(v_unused_3689_);
v___x_3683_ = v___x_3549_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_err_3681_);
lean_dec(v___x_3549_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 0, v_a_3548_);
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3548_);
lean_ctor_set(v_reuseFailAlloc_3687_, 1, v_err_3681_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withAuthority(lean_object* v_config_3690_, lean_object* v_a_3691_){
_start:
{
lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v_pos_3696_; lean_object* v_res_3697_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v_idx_3704_; lean_object* v___y_3705_; lean_object* v_pos_3706_; lean_object* v_err_3707_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v_pos_3723_; lean_object* v_array_3724_; lean_object* v_idx_3725_; lean_object* v_res_3726_; lean_object* v_idx_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v_pos_3747_; lean_object* v_array_3748_; lean_object* v_idx_3749_; lean_object* v_err_3750_; lean_object* v_pos_3755_; lean_object* v_utf8_3811_; lean_object* v___x_3812_; 
v_utf8_3811_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_3691_);
v___x_3812_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_3811_, v_a_3691_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v_pos_3813_; 
v_pos_3813_ = lean_ctor_get(v___x_3812_, 0);
lean_inc(v_pos_3813_);
lean_dec_ref_known(v___x_3812_, 2);
v_pos_3755_ = v_pos_3813_;
goto v___jp_3754_;
}
else
{
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v_pos_3814_; 
v_pos_3814_ = lean_ctor_get(v___x_3812_, 0);
lean_inc(v_pos_3814_);
lean_dec_ref_known(v___x_3812_, 2);
v_pos_3755_ = v_pos_3814_;
goto v___jp_3754_;
}
else
{
lean_object* v_err_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3822_; 
lean_dec_ref(v_config_3690_);
v_err_3815_ = lean_ctor_get(v___x_3812_, 1);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3822_ == 0)
{
lean_object* v_unused_3823_; 
v_unused_3823_ = lean_ctor_get(v___x_3812_, 0);
lean_dec(v_unused_3823_);
v___x_3817_ = v___x_3812_;
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_err_3815_);
lean_dec(v___x_3812_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3820_; 
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 0, v_a_3691_);
v___x_3820_ = v___x_3817_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3691_);
lean_ctor_set(v_reuseFailAlloc_3821_, 1, v_err_3815_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
}
}
v___jp_3692_:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3698_, 0, v___y_3693_);
v___x_3699_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
lean_ctor_set(v___x_3699_, 1, v___y_3694_);
lean_ctor_set(v___x_3699_, 2, v___y_3695_);
lean_ctor_set(v___x_3699_, 3, v_res_3697_);
v___x_3700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3700_, 0, v_pos_3696_);
lean_ctor_set(v___x_3700_, 1, v___x_3699_);
return v___x_3700_;
}
v___jp_3701_:
{
lean_object* v_idx_3708_; uint8_t v___x_3709_; 
v_idx_3708_ = lean_ctor_get(v_pos_3706_, 1);
v___x_3709_ = lean_nat_dec_eq(v_idx_3704_, v_idx_3708_);
lean_dec(v_idx_3704_);
if (v___x_3709_ == 0)
{
lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3703_);
lean_dec_ref(v___y_3702_);
v_isSharedCheck_3716_ = !lean_is_exclusive(v_pos_3706_);
if (v_isSharedCheck_3716_ == 0)
{
lean_object* v_unused_3717_; lean_object* v_unused_3718_; 
v_unused_3717_ = lean_ctor_get(v_pos_3706_, 1);
lean_dec(v_unused_3717_);
v_unused_3718_ = lean_ctor_get(v_pos_3706_, 0);
lean_dec(v_unused_3718_);
v___x_3711_ = v_pos_3706_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_dec(v_pos_3706_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
lean_ctor_set_tag(v___x_3711_, 1);
lean_ctor_set(v___x_3711_, 1, v_err_3707_);
lean_ctor_set(v___x_3711_, 0, v_a_3691_);
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3691_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v_err_3707_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
else
{
lean_object* v___x_3719_; 
lean_dec(v_err_3707_);
lean_dec_ref(v_a_3691_);
v___x_3719_ = lean_box(0);
v___y_3693_ = v___y_3702_;
v___y_3694_ = v___y_3703_;
v___y_3695_ = v___y_3705_;
v_pos_3696_ = v_pos_3706_;
v_res_3697_ = v___x_3719_;
goto v___jp_3692_;
}
}
v___jp_3720_:
{
lean_object* v___x_3727_; uint8_t v___x_3728_; 
v___x_3727_ = lean_byte_array_size(v_array_3724_);
v___x_3728_ = lean_nat_dec_lt(v_idx_3725_, v___x_3727_);
if (v___x_3728_ == 0)
{
lean_object* v___x_3729_; 
lean_dec_ref(v_array_3724_);
lean_dec_ref(v_config_3690_);
v___x_3729_ = lean_box(0);
v___y_3702_ = v___y_3721_;
v___y_3703_ = v___y_3722_;
v_idx_3704_ = v_idx_3725_;
v___y_3705_ = v_res_3726_;
v_pos_3706_ = v_pos_3723_;
v_err_3707_ = v___x_3729_;
goto v___jp_3701_;
}
else
{
uint8_t v___x_3730_; uint8_t v_got_3731_; uint8_t v___x_3732_; 
v___x_3730_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v_got_3731_ = lean_byte_array_fget(v_array_3724_, v_idx_3725_);
v___x_3732_ = lean_uint8_dec_eq(v_got_3731_, v___x_3730_);
if (v___x_3732_ == 0)
{
lean_object* v___x_3733_; 
lean_dec_ref(v_array_3724_);
lean_dec_ref(v_config_3690_);
v___x_3733_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__4, &l_Std_Http_URI_Parser_parseURI___closed__4_once, _init_l_Std_Http_URI_Parser_parseURI___closed__4);
v___y_3702_ = v___y_3721_;
v___y_3703_ = v___y_3722_;
v_idx_3704_ = v_idx_3725_;
v___y_3705_ = v_res_3726_;
v_pos_3706_ = v_pos_3723_;
v_err_3707_ = v___x_3733_;
goto v___jp_3701_;
}
else
{
lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
lean_dec_ref(v_pos_3723_);
v___x_3734_ = lean_unsigned_to_nat(1u);
v___x_3735_ = lean_nat_add(v_idx_3725_, v___x_3734_);
v___x_3736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3736_, 0, v_array_3724_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___x_3737_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3690_, v___x_3736_);
lean_dec_ref(v_config_3690_);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_object* v_pos_3738_; lean_object* v_res_3739_; lean_object* v___x_3740_; 
lean_dec(v_idx_3725_);
lean_dec_ref(v_a_3691_);
v_pos_3738_ = lean_ctor_get(v___x_3737_, 0);
lean_inc(v_pos_3738_);
v_res_3739_ = lean_ctor_get(v___x_3737_, 1);
lean_inc(v_res_3739_);
lean_dec_ref_known(v___x_3737_, 2);
v___x_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3740_, 0, v_res_3739_);
v___y_3693_ = v___y_3721_;
v___y_3694_ = v___y_3722_;
v___y_3695_ = v_res_3726_;
v_pos_3696_ = v_pos_3738_;
v_res_3697_ = v___x_3740_;
goto v___jp_3692_;
}
else
{
lean_object* v_pos_3741_; lean_object* v_err_3742_; 
v_pos_3741_ = lean_ctor_get(v___x_3737_, 0);
lean_inc(v_pos_3741_);
v_err_3742_ = lean_ctor_get(v___x_3737_, 1);
lean_inc(v_err_3742_);
lean_dec_ref_known(v___x_3737_, 2);
v___y_3702_ = v___y_3721_;
v___y_3703_ = v___y_3722_;
v_idx_3704_ = v_idx_3725_;
v___y_3705_ = v_res_3726_;
v_pos_3706_ = v_pos_3741_;
v_err_3707_ = v_err_3742_;
goto v___jp_3701_;
}
}
}
}
v___jp_3743_:
{
uint8_t v___x_3751_; 
v___x_3751_ = lean_nat_dec_eq(v_idx_3744_, v_idx_3749_);
lean_dec(v_idx_3744_);
if (v___x_3751_ == 0)
{
lean_object* v___x_3752_; 
lean_dec(v_idx_3749_);
lean_dec_ref(v_array_3748_);
lean_dec_ref(v_pos_3747_);
lean_dec_ref(v___y_3746_);
lean_dec_ref(v___y_3745_);
lean_dec_ref(v_config_3690_);
v___x_3752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3752_, 0, v_a_3691_);
lean_ctor_set(v___x_3752_, 1, v_err_3750_);
return v___x_3752_;
}
else
{
lean_object* v___x_3753_; 
lean_dec(v_err_3750_);
v___x_3753_ = lean_box(0);
v___y_3721_ = v___y_3745_;
v___y_3722_ = v___y_3746_;
v_pos_3723_ = v_pos_3747_;
v_array_3724_ = v_array_3748_;
v_idx_3725_ = v_idx_3749_;
v_res_3726_ = v___x_3753_;
goto v___jp_3720_;
}
}
v___jp_3754_:
{
lean_object* v___x_3756_; 
v___x_3756_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_3690_, v_pos_3755_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v_pos_3757_; lean_object* v_res_3758_; uint8_t v___x_3759_; lean_object* v___x_3760_; 
v_pos_3757_ = lean_ctor_get(v___x_3756_, 0);
lean_inc(v_pos_3757_);
v_res_3758_ = lean_ctor_get(v___x_3756_, 1);
lean_inc(v_res_3758_);
lean_dec_ref_known(v___x_3756_, 2);
v___x_3759_ = 1;
lean_inc_ref(v_config_3690_);
v___x_3760_ = l_Std_Http_URI_Parser_parsePath(v_config_3690_, v___x_3759_, v___x_3759_, v_pos_3757_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_pos_3761_; lean_object* v_res_3762_; lean_object* v_array_3763_; lean_object* v_idx_3764_; lean_object* v___x_3765_; uint8_t v___x_3766_; 
v_pos_3761_ = lean_ctor_get(v___x_3760_, 0);
lean_inc(v_pos_3761_);
v_res_3762_ = lean_ctor_get(v___x_3760_, 1);
lean_inc(v_res_3762_);
lean_dec_ref_known(v___x_3760_, 2);
v_array_3763_ = lean_ctor_get(v_pos_3761_, 0);
lean_inc_ref(v_array_3763_);
v_idx_3764_ = lean_ctor_get(v_pos_3761_, 1);
lean_inc(v_idx_3764_);
v___x_3765_ = lean_byte_array_size(v_array_3763_);
v___x_3766_ = lean_nat_dec_lt(v_idx_3764_, v___x_3765_);
if (v___x_3766_ == 0)
{
lean_object* v___x_3767_; 
v___x_3767_ = lean_box(0);
lean_inc(v_idx_3764_);
v_idx_3744_ = v_idx_3764_;
v___y_3745_ = v_res_3758_;
v___y_3746_ = v_res_3762_;
v_pos_3747_ = v_pos_3761_;
v_array_3748_ = v_array_3763_;
v_idx_3749_ = v_idx_3764_;
v_err_3750_ = v___x_3767_;
goto v___jp_3743_;
}
else
{
uint8_t v___x_3768_; uint8_t v_got_3769_; uint8_t v___x_3770_; 
v___x_3768_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3769_ = lean_byte_array_fget(v_array_3763_, v_idx_3764_);
v___x_3770_ = lean_uint8_dec_eq(v_got_3769_, v___x_3768_);
if (v___x_3770_ == 0)
{
lean_object* v___x_3771_; 
v___x_3771_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3764_);
v_idx_3744_ = v_idx_3764_;
v___y_3745_ = v_res_3758_;
v___y_3746_ = v_res_3762_;
v_pos_3747_ = v_pos_3761_;
v_array_3748_ = v_array_3763_;
v_idx_3749_ = v_idx_3764_;
v_err_3750_ = v___x_3771_;
goto v___jp_3743_;
}
else
{
lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3790_; 
v_isSharedCheck_3790_ = !lean_is_exclusive(v_pos_3761_);
if (v_isSharedCheck_3790_ == 0)
{
lean_object* v_unused_3791_; lean_object* v_unused_3792_; 
v_unused_3791_ = lean_ctor_get(v_pos_3761_, 1);
lean_dec(v_unused_3791_);
v_unused_3792_ = lean_ctor_get(v_pos_3761_, 0);
lean_dec(v_unused_3792_);
v___x_3773_ = v_pos_3761_;
v_isShared_3774_ = v_isSharedCheck_3790_;
goto v_resetjp_3772_;
}
else
{
lean_dec(v_pos_3761_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3790_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3778_; 
v___x_3775_ = lean_unsigned_to_nat(1u);
v___x_3776_ = lean_nat_add(v_idx_3764_, v___x_3775_);
if (v_isShared_3774_ == 0)
{
lean_ctor_set(v___x_3773_, 1, v___x_3776_);
v___x_3778_ = v___x_3773_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_array_3763_);
lean_ctor_set(v_reuseFailAlloc_3789_, 1, v___x_3776_);
v___x_3778_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
lean_object* v___x_3779_; 
lean_inc_ref(v_config_3690_);
v___x_3779_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3690_, v___x_3778_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_pos_3780_; lean_object* v_res_3781_; lean_object* v_array_3782_; lean_object* v_idx_3783_; lean_object* v___x_3784_; 
lean_dec(v_idx_3764_);
v_pos_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_pos_3780_);
v_res_3781_ = lean_ctor_get(v___x_3779_, 1);
lean_inc(v_res_3781_);
lean_dec_ref_known(v___x_3779_, 2);
v_array_3782_ = lean_ctor_get(v_pos_3780_, 0);
lean_inc_ref(v_array_3782_);
v_idx_3783_ = lean_ctor_get(v_pos_3780_, 1);
lean_inc(v_idx_3783_);
v___x_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3784_, 0, v_res_3781_);
v___y_3721_ = v_res_3758_;
v___y_3722_ = v_res_3762_;
v_pos_3723_ = v_pos_3780_;
v_array_3724_ = v_array_3782_;
v_idx_3725_ = v_idx_3783_;
v_res_3726_ = v___x_3784_;
goto v___jp_3720_;
}
else
{
lean_object* v_pos_3785_; lean_object* v_err_3786_; lean_object* v_array_3787_; lean_object* v_idx_3788_; 
v_pos_3785_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_pos_3785_);
v_err_3786_ = lean_ctor_get(v___x_3779_, 1);
lean_inc(v_err_3786_);
lean_dec_ref_known(v___x_3779_, 2);
v_array_3787_ = lean_ctor_get(v_pos_3785_, 0);
lean_inc_ref(v_array_3787_);
v_idx_3788_ = lean_ctor_get(v_pos_3785_, 1);
lean_inc(v_idx_3788_);
v_idx_3744_ = v_idx_3764_;
v___y_3745_ = v_res_3758_;
v___y_3746_ = v_res_3762_;
v_pos_3747_ = v_pos_3785_;
v_array_3748_ = v_array_3787_;
v_idx_3749_ = v_idx_3788_;
v_err_3750_ = v_err_3786_;
goto v___jp_3743_;
}
}
}
}
}
}
else
{
lean_object* v_err_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3800_; 
lean_dec(v_res_3758_);
lean_dec_ref(v_config_3690_);
v_err_3793_ = lean_ctor_get(v___x_3760_, 1);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3800_ == 0)
{
lean_object* v_unused_3801_; 
v_unused_3801_ = lean_ctor_get(v___x_3760_, 0);
lean_dec(v_unused_3801_);
v___x_3795_ = v___x_3760_;
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_err_3793_);
lean_dec(v___x_3760_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3798_; 
if (v_isShared_3796_ == 0)
{
lean_ctor_set(v___x_3795_, 0, v_a_3691_);
v___x_3798_ = v___x_3795_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_a_3691_);
lean_ctor_set(v_reuseFailAlloc_3799_, 1, v_err_3793_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
}
else
{
lean_object* v_err_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
lean_dec_ref(v_config_3690_);
v_err_3802_ = lean_ctor_get(v___x_3756_, 1);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3809_ == 0)
{
lean_object* v_unused_3810_; 
v_unused_3810_ = lean_ctor_get(v___x_3756_, 0);
lean_dec(v_unused_3810_);
v___x_3804_ = v___x_3756_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_err_3802_);
lean_dec(v___x_3756_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 0, v_a_3691_);
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3691_);
lean_ctor_set(v_reuseFailAlloc_3808_, 1, v_err_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath(lean_object* v_config_3824_, lean_object* v_a_3825_){
_start:
{
uint8_t v___x_3826_; uint8_t v___x_3827_; lean_object* v___x_3828_; 
v___x_3826_ = 0;
v___x_3827_ = 1;
lean_inc_ref(v_config_3824_);
v___x_3828_ = l_Std_Http_URI_Parser_parsePath(v_config_3824_, v___x_3826_, v___x_3827_, v_a_3825_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_pos_3829_; lean_object* v_res_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3911_; 
v_pos_3829_ = lean_ctor_get(v___x_3828_, 0);
v_res_3830_ = lean_ctor_get(v___x_3828_, 1);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3832_ = v___x_3828_;
v_isShared_3833_ = v_isSharedCheck_3911_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_res_3830_);
lean_inc(v_pos_3829_);
lean_dec(v___x_3828_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3911_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___y_3835_; lean_object* v_pos_3836_; lean_object* v_res_3837_; lean_object* v_idx_3844_; lean_object* v___y_3845_; lean_object* v_pos_3846_; lean_object* v_err_3847_; lean_object* v_pos_3853_; lean_object* v_array_3854_; lean_object* v_idx_3855_; lean_object* v_res_3856_; lean_object* v_array_3873_; lean_object* v_idx_3874_; lean_object* v_pos_3876_; lean_object* v_array_3877_; lean_object* v_idx_3878_; lean_object* v_err_3879_; lean_object* v___x_3883_; uint8_t v___x_3884_; 
v_array_3873_ = lean_ctor_get(v_pos_3829_, 0);
lean_inc_ref(v_array_3873_);
v_idx_3874_ = lean_ctor_get(v_pos_3829_, 1);
lean_inc(v_idx_3874_);
v___x_3883_ = lean_byte_array_size(v_array_3873_);
v___x_3884_ = lean_nat_dec_lt(v_idx_3874_, v___x_3883_);
if (v___x_3884_ == 0)
{
lean_object* v___x_3885_; 
v___x_3885_ = lean_box(0);
lean_inc(v_idx_3874_);
v_pos_3876_ = v_pos_3829_;
v_array_3877_ = v_array_3873_;
v_idx_3878_ = v_idx_3874_;
v_err_3879_ = v___x_3885_;
goto v___jp_3875_;
}
else
{
uint8_t v___x_3886_; uint8_t v_got_3887_; uint8_t v___x_3888_; 
v___x_3886_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_got_3887_ = lean_byte_array_fget(v_array_3873_, v_idx_3874_);
v___x_3888_ = lean_uint8_dec_eq(v_got_3887_, v___x_3886_);
if (v___x_3888_ == 0)
{
lean_object* v___x_3889_; 
v___x_3889_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3874_);
v_pos_3876_ = v_pos_3829_;
v_array_3877_ = v_array_3873_;
v_idx_3878_ = v_idx_3874_;
v_err_3879_ = v___x_3889_;
goto v___jp_3875_;
}
else
{
lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3908_; 
v_isSharedCheck_3908_ = !lean_is_exclusive(v_pos_3829_);
if (v_isSharedCheck_3908_ == 0)
{
lean_object* v_unused_3909_; lean_object* v_unused_3910_; 
v_unused_3909_ = lean_ctor_get(v_pos_3829_, 1);
lean_dec(v_unused_3909_);
v_unused_3910_ = lean_ctor_get(v_pos_3829_, 0);
lean_dec(v_unused_3910_);
v___x_3891_ = v_pos_3829_;
v_isShared_3892_ = v_isSharedCheck_3908_;
goto v_resetjp_3890_;
}
else
{
lean_dec(v_pos_3829_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3908_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3896_; 
v___x_3893_ = lean_unsigned_to_nat(1u);
v___x_3894_ = lean_nat_add(v_idx_3874_, v___x_3893_);
if (v_isShared_3892_ == 0)
{
lean_ctor_set(v___x_3891_, 1, v___x_3894_);
v___x_3896_ = v___x_3891_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_array_3873_);
lean_ctor_set(v_reuseFailAlloc_3907_, 1, v___x_3894_);
v___x_3896_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
lean_object* v___x_3897_; 
lean_inc_ref(v_config_3824_);
v___x_3897_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3824_, v___x_3896_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_pos_3898_; lean_object* v_res_3899_; lean_object* v_array_3900_; lean_object* v_idx_3901_; lean_object* v___x_3902_; 
lean_dec(v_idx_3874_);
v_pos_3898_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_pos_3898_);
v_res_3899_ = lean_ctor_get(v___x_3897_, 1);
lean_inc(v_res_3899_);
lean_dec_ref_known(v___x_3897_, 2);
v_array_3900_ = lean_ctor_get(v_pos_3898_, 0);
lean_inc_ref(v_array_3900_);
v_idx_3901_ = lean_ctor_get(v_pos_3898_, 1);
lean_inc(v_idx_3901_);
v___x_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3902_, 0, v_res_3899_);
v_pos_3853_ = v_pos_3898_;
v_array_3854_ = v_array_3900_;
v_idx_3855_ = v_idx_3901_;
v_res_3856_ = v___x_3902_;
goto v___jp_3852_;
}
else
{
lean_object* v_pos_3903_; lean_object* v_err_3904_; lean_object* v_array_3905_; lean_object* v_idx_3906_; 
v_pos_3903_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_pos_3903_);
v_err_3904_ = lean_ctor_get(v___x_3897_, 1);
lean_inc(v_err_3904_);
lean_dec_ref_known(v___x_3897_, 2);
v_array_3905_ = lean_ctor_get(v_pos_3903_, 0);
lean_inc_ref(v_array_3905_);
v_idx_3906_ = lean_ctor_get(v_pos_3903_, 1);
lean_inc(v_idx_3906_);
v_pos_3876_ = v_pos_3903_;
v_array_3877_ = v_array_3905_;
v_idx_3878_ = v_idx_3906_;
v_err_3879_ = v_err_3904_;
goto v___jp_3875_;
}
}
}
}
}
v___jp_3834_:
{
lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3841_; 
v___x_3838_ = lean_box(0);
v___x_3839_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3839_, 0, v___x_3838_);
lean_ctor_set(v___x_3839_, 1, v_res_3830_);
lean_ctor_set(v___x_3839_, 2, v___y_3835_);
lean_ctor_set(v___x_3839_, 3, v_res_3837_);
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 1, v___x_3839_);
lean_ctor_set(v___x_3832_, 0, v_pos_3836_);
v___x_3841_ = v___x_3832_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_pos_3836_);
lean_ctor_set(v_reuseFailAlloc_3842_, 1, v___x_3839_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
v___jp_3843_:
{
lean_object* v_idx_3848_; uint8_t v___x_3849_; 
v_idx_3848_ = lean_ctor_get(v_pos_3846_, 1);
v___x_3849_ = lean_nat_dec_eq(v_idx_3844_, v_idx_3848_);
lean_dec(v_idx_3844_);
if (v___x_3849_ == 0)
{
lean_object* v___x_3850_; 
lean_dec(v___y_3845_);
lean_del_object(v___x_3832_);
lean_dec(v_res_3830_);
v___x_3850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3850_, 0, v_pos_3846_);
lean_ctor_set(v___x_3850_, 1, v_err_3847_);
return v___x_3850_;
}
else
{
lean_object* v___x_3851_; 
lean_dec(v_err_3847_);
v___x_3851_ = lean_box(0);
v___y_3835_ = v___y_3845_;
v_pos_3836_ = v_pos_3846_;
v_res_3837_ = v___x_3851_;
goto v___jp_3834_;
}
}
v___jp_3852_:
{
lean_object* v___x_3857_; uint8_t v___x_3858_; 
v___x_3857_ = lean_byte_array_size(v_array_3854_);
v___x_3858_ = lean_nat_dec_lt(v_idx_3855_, v___x_3857_);
if (v___x_3858_ == 0)
{
lean_object* v___x_3859_; 
lean_dec_ref(v_array_3854_);
lean_dec_ref(v_config_3824_);
v___x_3859_ = lean_box(0);
v_idx_3844_ = v_idx_3855_;
v___y_3845_ = v_res_3856_;
v_pos_3846_ = v_pos_3853_;
v_err_3847_ = v___x_3859_;
goto v___jp_3843_;
}
else
{
uint8_t v___x_3860_; uint8_t v_got_3861_; uint8_t v___x_3862_; 
v___x_3860_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v_got_3861_ = lean_byte_array_fget(v_array_3854_, v_idx_3855_);
v___x_3862_ = lean_uint8_dec_eq(v_got_3861_, v___x_3860_);
if (v___x_3862_ == 0)
{
lean_object* v___x_3863_; 
lean_dec_ref(v_array_3854_);
lean_dec_ref(v_config_3824_);
v___x_3863_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__4, &l_Std_Http_URI_Parser_parseURI___closed__4_once, _init_l_Std_Http_URI_Parser_parseURI___closed__4);
v_idx_3844_ = v_idx_3855_;
v___y_3845_ = v_res_3856_;
v_pos_3846_ = v_pos_3853_;
v_err_3847_ = v___x_3863_;
goto v___jp_3843_;
}
else
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
lean_dec_ref(v_pos_3853_);
v___x_3864_ = lean_unsigned_to_nat(1u);
v___x_3865_ = lean_nat_add(v_idx_3855_, v___x_3864_);
v___x_3866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3866_, 0, v_array_3854_);
lean_ctor_set(v___x_3866_, 1, v___x_3865_);
v___x_3867_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_fragment(v_config_3824_, v___x_3866_);
lean_dec_ref(v_config_3824_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_pos_3868_; lean_object* v_res_3869_; lean_object* v___x_3870_; 
lean_dec(v_idx_3855_);
v_pos_3868_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_pos_3868_);
v_res_3869_ = lean_ctor_get(v___x_3867_, 1);
lean_inc(v_res_3869_);
lean_dec_ref_known(v___x_3867_, 2);
v___x_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3870_, 0, v_res_3869_);
v___y_3835_ = v_res_3856_;
v_pos_3836_ = v_pos_3868_;
v_res_3837_ = v___x_3870_;
goto v___jp_3834_;
}
else
{
lean_object* v_pos_3871_; lean_object* v_err_3872_; 
v_pos_3871_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_pos_3871_);
v_err_3872_ = lean_ctor_get(v___x_3867_, 1);
lean_inc(v_err_3872_);
lean_dec_ref_known(v___x_3867_, 2);
v_idx_3844_ = v_idx_3855_;
v___y_3845_ = v_res_3856_;
v_pos_3846_ = v_pos_3871_;
v_err_3847_ = v_err_3872_;
goto v___jp_3843_;
}
}
}
}
v___jp_3875_:
{
uint8_t v___x_3880_; 
v___x_3880_ = lean_nat_dec_eq(v_idx_3874_, v_idx_3878_);
lean_dec(v_idx_3874_);
if (v___x_3880_ == 0)
{
lean_object* v___x_3881_; 
lean_dec(v_idx_3878_);
lean_dec_ref(v_array_3877_);
lean_del_object(v___x_3832_);
lean_dec(v_res_3830_);
lean_dec_ref(v_config_3824_);
v___x_3881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3881_, 0, v_pos_3876_);
lean_ctor_set(v___x_3881_, 1, v_err_3879_);
return v___x_3881_;
}
else
{
lean_object* v___x_3882_; 
lean_dec(v_err_3879_);
v___x_3882_ = lean_box(0);
v_pos_3853_ = v_pos_3876_;
v_array_3854_ = v_array_3877_;
v_idx_3855_ = v_idx_3878_;
v_res_3856_ = v___x_3882_;
goto v___jp_3852_;
}
}
}
}
else
{
lean_object* v_pos_3912_; lean_object* v_err_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3920_; 
lean_dec_ref(v_config_3824_);
v_pos_3912_ = lean_ctor_get(v___x_3828_, 0);
v_err_3913_ = lean_ctor_get(v___x_3828_, 1);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3915_ = v___x_3828_;
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_err_3913_);
lean_inc(v_pos_3912_);
lean_dec(v___x_3828_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_pos_3912_);
lean_ctor_set(v_reuseFailAlloc_3919_, 1, v_err_3913_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_relative(lean_object* v_config_3921_, lean_object* v_a_3922_){
_start:
{
lean_object* v___y_3924_; lean_object* v___x_3944_; 
lean_inc_ref(v_a_3922_);
lean_inc_ref(v_config_3921_);
v___x_3944_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withAuthority(v_config_3921_, v_a_3922_);
if (lean_obj_tag(v___x_3944_) == 0)
{
lean_dec_ref(v_a_3922_);
lean_dec_ref(v_config_3921_);
v___y_3924_ = v___x_3944_;
goto v___jp_3923_;
}
else
{
lean_object* v_pos_3945_; lean_object* v_idx_3946_; lean_object* v_idx_3947_; uint8_t v___x_3948_; 
v_pos_3945_ = lean_ctor_get(v___x_3944_, 0);
lean_inc(v_pos_3945_);
v_idx_3946_ = lean_ctor_get(v_a_3922_, 1);
lean_inc(v_idx_3946_);
lean_dec_ref(v_a_3922_);
v_idx_3947_ = lean_ctor_get(v_pos_3945_, 1);
v___x_3948_ = lean_nat_dec_eq(v_idx_3946_, v_idx_3947_);
lean_dec(v_idx_3946_);
if (v___x_3948_ == 0)
{
lean_dec(v_pos_3945_);
lean_dec_ref(v_config_3921_);
v___y_3924_ = v___x_3944_;
goto v___jp_3923_;
}
else
{
lean_object* v___x_3949_; 
lean_dec_ref_known(v___x_3944_, 2);
v___x_3949_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_withPath(v_config_3921_, v_pos_3945_);
v___y_3924_ = v___x_3949_;
goto v___jp_3923_;
}
}
v___jp_3923_:
{
if (lean_obj_tag(v___y_3924_) == 0)
{
lean_object* v_pos_3925_; lean_object* v_res_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3934_; 
v_pos_3925_ = lean_ctor_get(v___y_3924_, 0);
v_res_3926_ = lean_ctor_get(v___y_3924_, 1);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___y_3924_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3928_ = v___y_3924_;
v_isShared_3929_ = v_isSharedCheck_3934_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_res_3926_);
lean_inc(v_pos_3925_);
lean_dec(v___y_3924_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3934_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v___x_3930_; lean_object* v___x_3932_; 
v___x_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3930_, 0, v_res_3926_);
if (v_isShared_3929_ == 0)
{
lean_ctor_set(v___x_3928_, 1, v___x_3930_);
v___x_3932_ = v___x_3928_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_pos_3925_);
lean_ctor_set(v_reuseFailAlloc_3933_, 1, v___x_3930_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
else
{
lean_object* v_pos_3935_; lean_object* v_err_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3943_; 
v_pos_3935_ = lean_ctor_get(v___y_3924_, 0);
v_err_3936_ = lean_ctor_get(v___y_3924_, 1);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___y_3924_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3938_ = v___y_3924_;
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_err_3936_);
lean_inc(v_pos_3935_);
lean_dec(v___y_3924_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3941_; 
if (v_isShared_3939_ == 0)
{
v___x_3941_ = v___x_3938_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_pos_3935_);
lean_ctor_set(v_reuseFailAlloc_3942_, 1, v_err_3936_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURIReference(lean_object* v_config_3950_, lean_object* v_a_3951_){
_start:
{
lean_object* v___y_3953_; lean_object* v_pos_3954_; lean_object* v___x_3959_; 
lean_inc_ref(v_a_3951_);
lean_inc_ref(v_config_3950_);
v___x_3959_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_uri(v_config_3950_, v_a_3951_);
if (lean_obj_tag(v___x_3959_) == 0)
{
if (lean_obj_tag(v___x_3959_) == 0)
{
lean_dec_ref(v_a_3951_);
lean_dec_ref(v_config_3950_);
return v___x_3959_;
}
else
{
lean_object* v_pos_3960_; 
v_pos_3960_ = lean_ctor_get(v___x_3959_, 0);
lean_inc(v_pos_3960_);
v___y_3953_ = v___x_3959_;
v_pos_3954_ = v_pos_3960_;
goto v___jp_3952_;
}
}
else
{
lean_object* v_err_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3968_; 
v_err_3961_ = lean_ctor_get(v___x_3959_, 1);
v_isSharedCheck_3968_ = !lean_is_exclusive(v___x_3959_);
if (v_isSharedCheck_3968_ == 0)
{
lean_object* v_unused_3969_; 
v_unused_3969_ = lean_ctor_get(v___x_3959_, 0);
lean_dec(v_unused_3969_);
v___x_3963_ = v___x_3959_;
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_err_3961_);
lean_dec(v___x_3959_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___x_3966_; 
lean_inc_ref(v_a_3951_);
if (v_isShared_3964_ == 0)
{
lean_ctor_set(v___x_3963_, 0, v_a_3951_);
v___x_3966_ = v___x_3963_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_a_3951_);
lean_ctor_set(v_reuseFailAlloc_3967_, 1, v_err_3961_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
lean_inc_ref(v_a_3951_);
v___y_3953_ = v___x_3966_;
v_pos_3954_ = v_a_3951_;
goto v___jp_3952_;
}
}
}
v___jp_3952_:
{
lean_object* v_idx_3955_; lean_object* v_idx_3956_; uint8_t v___x_3957_; 
v_idx_3955_ = lean_ctor_get(v_a_3951_, 1);
lean_inc(v_idx_3955_);
lean_dec_ref(v_a_3951_);
v_idx_3956_ = lean_ctor_get(v_pos_3954_, 1);
v___x_3957_ = lean_nat_dec_eq(v_idx_3955_, v_idx_3956_);
lean_dec(v_idx_3955_);
if (v___x_3957_ == 0)
{
lean_dec_ref(v_pos_3954_);
lean_dec_ref(v_config_3950_);
return v___y_3953_;
}
else
{
lean_object* v___x_3958_; 
lean_dec_ref(v___y_3953_);
v___x_3958_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseURIReference_relative(v_config_3950_, v_pos_3954_);
return v___x_3958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader(lean_object* v_config_3976_, lean_object* v_a_3977_){
_start:
{
lean_object* v___x_3978_; 
v___x_3978_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3976_, v_a_3977_);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v_pos_3979_; lean_object* v_res_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_4053_; 
v_pos_3979_ = lean_ctor_get(v___x_3978_, 0);
v_res_3980_ = lean_ctor_get(v___x_3978_, 1);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_3978_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_3982_ = v___x_3978_;
v_isShared_3983_ = v_isSharedCheck_4053_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_res_3980_);
lean_inc(v_pos_3979_);
lean_dec(v___x_3978_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_4053_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v_port_3985_; lean_object* v___y_3986_; lean_object* v_pos_4000_; lean_object* v_pos_4003_; lean_object* v_array_4004_; lean_object* v_idx_4005_; lean_object* v_array_4011_; lean_object* v_idx_4012_; lean_object* v___x_4013_; uint8_t v___x_4014_; 
v_array_4011_ = lean_ctor_get(v_pos_3979_, 0);
v_idx_4012_ = lean_ctor_get(v_pos_3979_, 1);
v___x_4013_ = lean_byte_array_size(v_array_4011_);
v___x_4014_ = lean_nat_dec_lt(v_idx_4012_, v___x_4013_);
if (v___x_4014_ == 0)
{
v_pos_4000_ = v_pos_3979_;
goto v___jp_3999_;
}
else
{
uint8_t v___x_4015_; uint8_t v___x_4016_; uint8_t v___x_4017_; 
v___x_4015_ = lean_byte_array_fget(v_array_4011_, v_idx_4012_);
v___x_4016_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_4017_ = lean_uint8_dec_eq(v___x_4015_, v___x_4016_);
if (v___x_4017_ == 0)
{
v_pos_4000_ = v_pos_3979_;
goto v___jp_3999_;
}
else
{
if (v___x_4014_ == 0)
{
lean_object* v___x_4018_; lean_object* v___x_4019_; 
lean_del_object(v___x_3982_);
lean_dec(v_res_3980_);
v___x_4018_ = lean_box(0);
v___x_4019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4019_, 0, v_pos_3979_);
lean_ctor_set(v___x_4019_, 1, v___x_4018_);
return v___x_4019_;
}
else
{
if (v___x_4017_ == 0)
{
lean_object* v___x_4020_; lean_object* v___x_4021_; 
lean_del_object(v___x_3982_);
lean_dec(v_res_3980_);
v___x_4020_ = lean_obj_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
v___x_4021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4021_, 0, v_pos_3979_);
lean_ctor_set(v___x_4021_, 1, v___x_4020_);
return v___x_4021_;
}
else
{
lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4050_; 
lean_inc(v_idx_4012_);
lean_inc_ref(v_array_4011_);
v_isSharedCheck_4050_ = !lean_is_exclusive(v_pos_3979_);
if (v_isSharedCheck_4050_ == 0)
{
lean_object* v_unused_4051_; lean_object* v_unused_4052_; 
v_unused_4051_ = lean_ctor_get(v_pos_3979_, 1);
lean_dec(v_unused_4051_);
v_unused_4052_ = lean_ctor_get(v_pos_3979_, 0);
lean_dec(v_unused_4052_);
v___x_4023_ = v_pos_3979_;
v_isShared_4024_ = v_isSharedCheck_4050_;
goto v_resetjp_4022_;
}
else
{
lean_dec(v_pos_3979_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4050_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4028_; 
v___x_4025_ = lean_unsigned_to_nat(1u);
v___x_4026_ = lean_nat_add(v_idx_4012_, v___x_4025_);
lean_dec(v_idx_4012_);
lean_inc(v___x_4026_);
lean_inc_ref(v_array_4011_);
if (v_isShared_4024_ == 0)
{
lean_ctor_set(v___x_4023_, 1, v___x_4026_);
v___x_4028_ = v___x_4023_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_array_4011_);
lean_ctor_set(v_reuseFailAlloc_4049_, 1, v___x_4026_);
v___x_4028_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
uint8_t v___x_4029_; 
v___x_4029_ = lean_nat_dec_lt(v___x_4026_, v___x_4013_);
if (v___x_4029_ == 0)
{
v_pos_4003_ = v___x_4028_;
v_array_4004_ = v_array_4011_;
v_idx_4005_ = v___x_4026_;
goto v___jp_4002_;
}
else
{
uint8_t v___x_4030_; uint8_t v___x_4031_; uint8_t v___x_4032_; 
v___x_4030_ = lean_byte_array_fget(v_array_4011_, v___x_4026_);
v___x_4031_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__7);
v___x_4032_ = lean_uint8_dec_le(v___x_4031_, v___x_4030_);
if (v___x_4032_ == 0)
{
v_pos_4003_ = v___x_4028_;
v_array_4004_ = v_array_4011_;
v_idx_4005_ = v___x_4026_;
goto v___jp_4002_;
}
else
{
uint8_t v___x_4033_; uint8_t v___x_4034_; 
v___x_4033_ = lean_uint8_once(&l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8, &l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8_once, _init_l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__8);
v___x_4034_ = lean_uint8_dec_le(v___x_4030_, v___x_4033_);
if (v___x_4034_ == 0)
{
v_pos_4003_ = v___x_4028_;
v_array_4004_ = v_array_4011_;
v_idx_4005_ = v___x_4026_;
goto v___jp_4002_;
}
else
{
lean_object* v___x_4035_; 
lean_dec(v___x_4026_);
lean_dec_ref(v_array_4011_);
v___x_4035_ = l___private_Std_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___x_4028_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_pos_4036_; lean_object* v_res_4037_; lean_object* v___x_4038_; uint16_t v___x_4039_; 
v_pos_4036_ = lean_ctor_get(v___x_4035_, 0);
lean_inc(v_pos_4036_);
v_res_4037_ = lean_ctor_get(v___x_4035_, 1);
lean_inc(v_res_4037_);
lean_dec_ref_known(v___x_4035_, 2);
v___x_4038_ = lean_alloc_ctor(2, 0, 2);
v___x_4039_ = lean_unbox(v_res_4037_);
lean_dec(v_res_4037_);
lean_ctor_set_uint16(v___x_4038_, 0, v___x_4039_);
v_port_3985_ = v___x_4038_;
v___y_3986_ = v_pos_4036_;
goto v___jp_3984_;
}
else
{
lean_object* v_pos_4040_; lean_object* v_err_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
lean_del_object(v___x_3982_);
lean_dec(v_res_3980_);
v_pos_4040_ = lean_ctor_get(v___x_4035_, 0);
v_err_4041_ = lean_ctor_get(v___x_4035_, 1);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___x_4035_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_err_4041_);
lean_inc(v_pos_4040_);
lean_dec(v___x_4035_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
v___x_4046_ = v___x_4043_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_pos_4040_);
lean_ctor_set(v_reuseFailAlloc_4047_, 1, v_err_4041_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
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
v___jp_3984_:
{
lean_object* v_array_3987_; lean_object* v_idx_3988_; lean_object* v___x_3989_; uint8_t v___x_3990_; 
v_array_3987_ = lean_ctor_get(v___y_3986_, 0);
v_idx_3988_ = lean_ctor_get(v___y_3986_, 1);
v___x_3989_ = lean_byte_array_size(v_array_3987_);
v___x_3990_ = lean_nat_dec_lt(v_idx_3988_, v___x_3989_);
if (v___x_3990_ == 0)
{
lean_object* v___x_3991_; lean_object* v___x_3993_; 
v___x_3991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3991_, 0, v_res_3980_);
lean_ctor_set(v___x_3991_, 1, v_port_3985_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 1, v___x_3991_);
lean_ctor_set(v___x_3982_, 0, v___y_3986_);
v___x_3993_ = v___x_3982_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v___y_3986_);
lean_ctor_set(v_reuseFailAlloc_3994_, 1, v___x_3991_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
else
{
lean_object* v___x_3995_; lean_object* v___x_3997_; 
lean_dec(v_port_3985_);
lean_dec(v_res_3980_);
v___x_3995_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__1));
if (v_isShared_3983_ == 0)
{
lean_ctor_set_tag(v___x_3982_, 1);
lean_ctor_set(v___x_3982_, 1, v___x_3995_);
lean_ctor_set(v___x_3982_, 0, v___y_3986_);
v___x_3997_ = v___x_3982_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___y_3986_);
lean_ctor_set(v_reuseFailAlloc_3998_, 1, v___x_3995_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
}
v___jp_3999_:
{
lean_object* v___x_4001_; 
v___x_4001_ = lean_box(0);
v_port_3985_ = v___x_4001_;
v___y_3986_ = v_pos_4000_;
goto v___jp_3984_;
}
v___jp_4002_:
{
lean_object* v___x_4006_; uint8_t v___x_4007_; 
v___x_4006_ = lean_byte_array_size(v_array_4004_);
lean_dec_ref(v_array_4004_);
v___x_4007_ = lean_nat_dec_lt(v_idx_4005_, v___x_4006_);
lean_dec(v_idx_4005_);
if (v___x_4007_ == 0)
{
lean_object* v___x_4008_; 
v___x_4008_ = lean_box(1);
v_port_3985_ = v___x_4008_;
v___y_3986_ = v_pos_4003_;
goto v___jp_3984_;
}
else
{
lean_object* v___x_4009_; lean_object* v___x_4010_; 
lean_del_object(v___x_3982_);
lean_dec(v_res_3980_);
v___x_4009_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__3));
v___x_4010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4010_, 0, v_pos_4003_);
lean_ctor_set(v___x_4010_, 1, v___x_4009_);
return v___x_4010_;
}
}
}
}
else
{
lean_object* v_pos_4054_; lean_object* v_err_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
v_pos_4054_ = lean_ctor_get(v___x_3978_, 0);
v_err_4055_ = lean_ctor_get(v___x_3978_, 1);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_3978_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4057_ = v___x_3978_;
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_err_4055_);
lean_inc(v_pos_4054_);
lean_dec(v___x_3978_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_pos_4054_);
lean_ctor_set(v_reuseFailAlloc_4061_, 1, v_err_4055_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader___boxed(lean_object* v_config_4063_, lean_object* v_a_4064_){
_start:
{
lean_object* v_res_4065_; 
v_res_4065_ = l_Std_Http_URI_Parser_parseHostHeader(v_config_4063_, v_a_4064_);
lean_dec_ref(v_config_4063_);
return v_res_4065_;
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
