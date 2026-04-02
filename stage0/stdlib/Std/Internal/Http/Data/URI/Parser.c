// Lean compiler output
// Module: Std.Internal.Http.Data.URI.Parser
// Imports: import Init.While public import Init.Data.String public import Std.Internal.Parsec public import Std.Internal.Parsec.ByteArray public import Std.Internal.Http.Data.URI.Basic public import Std.Internal.Http.Data.URI.Config
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
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
extern lean_object* l_Std_Http_URI_Query_empty;
lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f(lean_object*);
lean_object* l_Std_Http_URI_Query_insertEncoded(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo1_findEnd(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t l_Std_Http_Internal_instDecidableIsLowerCase(lean_object*);
lean_object* lean_string_data(lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
lean_object* l_List_head_x3f___redArg(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
lean_object* l_Std_Http_URI_isValidDomainLabel___boxed(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
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
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed(lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid domain name: "};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1_value;
static const lean_closure_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_isValidDomainLabel___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "invalid host"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__4 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__4_value;
static const lean_closure_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__5 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__5_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed(lean_object*);
static const lean_string_object l_List_foldlM___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l_List_foldlM___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0 = (const lean_object*)&l_List_foldlM___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid query string"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__1_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__1_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "&"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "too many query parameters (limit: "};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__4 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__4_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(lean_object*, lean_object*);
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
v___x_606_ = l_ByteArray_toByteSlice(v___y_603_, v_lower_604_, v_upper_605_);
v___x_607_ = l_ByteSlice_toByteArray(v___x_606_);
v___x_608_ = l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(v___x_607_);
if (lean_obj_tag(v___x_608_) == 1)
{
v___y_595_ = v___y_601_;
v_userPassEncoded_596_ = v___x_608_;
v___y_597_ = v___y_602_;
goto v___jp_594_;
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec(v___x_608_);
lean_dec_ref(v___y_601_);
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
v___x_618_ = lean_nat_dec_le(v___y_612_, v___y_613_);
if (v___x_618_ == 0)
{
lean_dec(v___y_612_);
v___y_601_ = v___y_614_;
v___y_602_ = v___y_616_;
v___y_603_ = v___y_615_;
v_lower_604_ = v___y_617_;
v_upper_605_ = v___y_613_;
goto v___jp_600_;
}
else
{
lean_dec(v___y_613_);
v___y_601_ = v___y_614_;
v___y_602_ = v___y_616_;
v___y_603_ = v___y_615_;
v_lower_604_ = v___y_617_;
v_upper_605_ = v___y_612_;
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
v___y_612_ = v___x_665_;
v___y_613_ = v___x_643_;
v___y_614_ = v_val_640_;
v___y_615_ = v_array_641_;
v___y_616_ = v_snd_664_;
v___y_617_ = v___x_659_;
goto v___jp_611_;
}
else
{
lean_dec(v___x_659_);
v___y_612_ = v___x_665_;
v___y_613_ = v___x_643_;
v___y_614_ = v_val_640_;
v___y_615_ = v_array_641_;
v___y_616_ = v_snd_664_;
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
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(uint8_t v_x_914_){
_start:
{
uint8_t v___y_916_; uint8_t v___y_922_; uint8_t v___y_928_; uint8_t v___x_933_; uint8_t v___x_934_; 
v___x_933_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_934_ = lean_uint8_dec_le(v___x_933_, v_x_914_);
if (v___x_934_ == 0)
{
v___y_928_ = v___x_934_;
goto v___jp_927_;
}
else
{
uint8_t v___x_935_; uint8_t v___x_936_; 
v___x_935_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_936_ = lean_uint8_dec_le(v_x_914_, v___x_935_);
v___y_928_ = v___x_936_;
goto v___jp_927_;
}
v___jp_915_:
{
if (v___y_916_ == 0)
{
uint8_t v___x_917_; uint8_t v___x_918_; 
v___x_917_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1);
v___x_918_ = lean_uint8_dec_eq(v_x_914_, v___x_917_);
if (v___x_918_ == 0)
{
uint8_t v___x_919_; uint8_t v___x_920_; 
v___x_919_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2);
v___x_920_ = lean_uint8_dec_eq(v_x_914_, v___x_919_);
if (v___x_920_ == 0)
{
return v___y_916_;
}
else
{
return v___x_920_;
}
}
else
{
return v___x_918_;
}
}
else
{
return v___y_916_;
}
}
v___jp_921_:
{
if (v___y_922_ == 0)
{
uint8_t v___x_923_; uint8_t v___x_924_; 
v___x_923_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_924_ = lean_uint8_dec_le(v___x_923_, v_x_914_);
if (v___x_924_ == 0)
{
v___y_916_ = v___x_924_;
goto v___jp_915_;
}
else
{
uint8_t v___x_925_; uint8_t v___x_926_; 
v___x_925_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_926_ = lean_uint8_dec_le(v_x_914_, v___x_925_);
v___y_916_ = v___x_926_;
goto v___jp_915_;
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
v___x_929_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_930_ = lean_uint8_dec_le(v___x_929_, v_x_914_);
if (v___x_930_ == 0)
{
v___y_922_ = v___x_930_;
goto v___jp_921_;
}
else
{
uint8_t v___x_931_; uint8_t v___x_932_; 
v___x_931_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_932_ = lean_uint8_dec_le(v_x_914_, v___x_931_);
v___y_922_ = v___x_932_;
goto v___jp_921_;
}
}
else
{
return v___y_928_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed(lean_object* v_x_937_){
_start:
{
uint8_t v_x_boxed_938_; uint8_t v_res_939_; lean_object* v_r_940_; 
v_x_boxed_938_ = lean_unbox(v_x_937_);
v_res_939_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(v_x_boxed_938_);
v_r_940_ = lean_box(v_res_939_);
return v_r_940_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(lean_object* v_config_948_, lean_object* v_a_949_){
_start:
{
lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; uint8_t v___y_961_; uint8_t v___y_965_; uint8_t v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; uint8_t v___y_971_; uint8_t v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v_lower_987_; lean_object* v_upper_988_; uint8_t v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v_array_1009_; lean_object* v_idx_1010_; lean_object* v___f_1011_; lean_object* v___y_1013_; lean_object* v_pos_1042_; lean_object* v_pos_1066_; lean_object* v_res_1067_; lean_object* v___y_1069_; lean_object* v___y_1070_; uint8_t v___y_1071_; lean_object* v_pos_1073_; lean_object* v_res_1074_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v_array_1009_ = lean_ctor_get(v_a_949_, 0);
v_idx_1010_ = lean_ctor_get(v_a_949_, 1);
v___f_1011_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__5));
v___x_1082_ = lean_byte_array_size(v_array_1009_);
v___x_1083_ = lean_nat_dec_lt(v_idx_1010_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; 
lean_inc(v_idx_1010_);
lean_inc_ref(v_array_1009_);
v___x_1084_ = lean_box(0);
v_pos_1073_ = v_a_949_;
v_res_1074_ = v___x_1084_;
goto v___jp_1072_;
}
else
{
uint8_t v___x_1085_; uint8_t v___x_1086_; uint8_t v___x_1087_; 
v___x_1085_ = lean_byte_array_fget(v_array_1009_, v_idx_1010_);
v___x_1086_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1);
v___x_1087_ = lean_uint8_dec_eq(v___x_1085_, v___x_1086_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; 
lean_inc(v_idx_1010_);
lean_inc_ref(v_array_1009_);
v___x_1088_ = lean_box(0);
v_pos_1073_ = v_a_949_;
v_res_1074_ = v___x_1088_;
goto v___jp_1072_;
}
else
{
lean_object* v___x_1089_; 
v___x_1089_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(v_a_949_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_pos_1090_; lean_object* v_res_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1099_; 
v_pos_1090_ = lean_ctor_get(v___x_1089_, 0);
v_res_1091_ = lean_ctor_get(v___x_1089_, 1);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1093_ = v___x_1089_;
v_isShared_1094_ = v_isSharedCheck_1099_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_res_1091_);
lean_inc(v_pos_1090_);
lean_dec(v___x_1089_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1099_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1095_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1095_, 0, v_res_1091_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 1, v___x_1095_);
v___x_1097_ = v___x_1093_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_pos_1090_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
else
{
lean_object* v_pos_1100_; lean_object* v_err_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
v_pos_1100_ = lean_ctor_get(v___x_1089_, 0);
v_err_1101_ = lean_ctor_get(v___x_1089_, 1);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1089_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_err_1101_);
lean_inc(v_pos_1100_);
lean_dec(v___x_1089_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_pos_1100_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_err_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
v___jp_950_:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_953_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0));
v___x_954_ = lean_string_append(v___x_953_, v___y_952_);
lean_dec_ref(v___y_952_);
v___x_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
v___x_956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_956_, 0, v___y_951_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
return v___x_956_;
}
v___jp_957_:
{
if (v___y_961_ == 0)
{
lean_dec_ref(v___y_959_);
v___y_951_ = v___y_958_;
v___y_952_ = v___y_960_;
goto v___jp_950_;
}
else
{
lean_object* v___x_962_; lean_object* v___x_963_; 
lean_dec_ref(v___y_960_);
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v___y_959_);
v___x_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_963_, 0, v___y_958_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
return v___x_963_;
}
}
v___jp_964_:
{
if (v___y_971_ == 0)
{
lean_dec(v___y_970_);
lean_dec_ref(v___y_968_);
v___y_951_ = v___y_967_;
v___y_952_ = v___y_969_;
goto v___jp_950_;
}
else
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_972_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1));
v___x_973_ = lean_box(0);
lean_inc_n(v___y_970_, 3);
v___x_974_ = l_String_splitOnAux(v___y_968_, v___x_972_, v___y_970_, v___y_970_, v___y_970_, v___x_973_);
v___x_975_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2));
v___x_976_ = l_List_all___redArg(v___x_974_, v___x_975_);
if (v___x_976_ == 0)
{
lean_dec(v___y_970_);
lean_dec_ref(v___y_968_);
v___y_951_ = v___y_967_;
v___y_952_ = v___y_969_;
goto v___jp_950_;
}
else
{
lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_977_ = lean_string_length(v___y_968_);
v___x_978_ = lean_unsigned_to_nat(255u);
v___x_979_ = lean_nat_dec_le(v___x_977_, v___x_978_);
if (v___x_979_ == 0)
{
lean_dec(v___y_970_);
lean_dec_ref(v___y_968_);
v___y_951_ = v___y_967_;
v___y_952_ = v___y_969_;
goto v___jp_950_;
}
else
{
lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_980_ = lean_string_utf8_byte_size(v___y_968_);
v___x_981_ = lean_nat_dec_eq(v___x_980_, v___y_970_);
lean_dec(v___y_970_);
if (v___x_981_ == 0)
{
v___y_958_ = v___y_967_;
v___y_959_ = v___y_968_;
v___y_960_ = v___y_969_;
v___y_961_ = v___y_965_;
goto v___jp_957_;
}
else
{
v___y_958_ = v___y_967_;
v___y_959_ = v___y_968_;
v___y_960_ = v___y_969_;
v___y_961_ = v___y_966_;
goto v___jp_957_;
}
}
}
}
}
v___jp_982_:
{
lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_989_ = l_ByteArray_toByteSlice(v___y_985_, v_lower_987_, v_upper_988_);
v___x_990_ = l_ByteSlice_toByteArray(v___x_989_);
v___x_991_ = lean_string_validate_utf8(v___x_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; lean_object* v___x_993_; 
lean_dec_ref(v___x_990_);
lean_dec(v___y_986_);
v___x_992_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__4));
v___x_993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_993_, 0, v___y_984_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
return v___x_993_;
}
else
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_994_ = lean_string_from_utf8_unchecked(v___x_990_);
lean_inc_n(v___y_986_, 4);
lean_inc_ref(v___x_994_);
v___x_995_ = l_String_mapAux___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___x_994_, v___y_986_);
v___x_996_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1));
v___x_997_ = lean_box(0);
v___x_998_ = l_String_splitOnAux(v___x_995_, v___x_996_, v___y_986_, v___y_986_, v___y_986_, v___x_997_);
v___x_999_ = l_List_isEmpty___redArg(v___x_998_);
lean_dec(v___x_998_);
if (v___x_999_ == 0)
{
v___y_965_ = v___x_991_;
v___y_966_ = v___y_983_;
v___y_967_ = v___y_984_;
v___y_968_ = v___x_995_;
v___y_969_ = v___x_994_;
v___y_970_ = v___y_986_;
v___y_971_ = v___x_991_;
goto v___jp_964_;
}
else
{
v___y_965_ = v___x_991_;
v___y_966_ = v___y_983_;
v___y_967_ = v___y_984_;
v___y_968_ = v___x_995_;
v___y_969_ = v___x_994_;
v___y_970_ = v___y_986_;
v___y_971_ = v___y_983_;
goto v___jp_964_;
}
}
}
v___jp_1000_:
{
uint8_t v___x_1008_; 
v___x_1008_ = lean_nat_dec_le(v___y_1005_, v___y_1003_);
if (v___x_1008_ == 0)
{
lean_dec(v___y_1005_);
v___y_983_ = v___y_1001_;
v___y_984_ = v___y_1002_;
v___y_985_ = v___y_1004_;
v___y_986_ = v___y_1006_;
v_lower_987_ = v___y_1007_;
v_upper_988_ = v___y_1003_;
goto v___jp_982_;
}
else
{
lean_dec(v___y_1003_);
v___y_983_ = v___y_1001_;
v___y_984_ = v___y_1002_;
v___y_985_ = v___y_1004_;
v___y_986_ = v___y_1006_;
v_lower_987_ = v___y_1007_;
v_upper_988_ = v___y_1005_;
goto v___jp_982_;
}
}
v___jp_1012_:
{
lean_object* v_maxHostLength_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v_fst_1017_; lean_object* v_snd_1018_; uint8_t v___x_1019_; 
v_maxHostLength_1014_ = lean_ctor_get(v_config_948_, 1);
v___x_1015_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___y_1013_);
v___x_1016_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo1_findEnd(v___f_1011_, v_maxHostLength_1014_, v___x_1015_, v___y_1013_);
v_fst_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_fst_1017_);
v_snd_1018_ = lean_ctor_get(v___x_1016_, 1);
lean_inc(v_snd_1018_);
lean_dec_ref(v___x_1016_);
v___x_1019_ = lean_nat_dec_eq(v_fst_1017_, v___x_1015_);
if (v___x_1019_ == 0)
{
lean_object* v_array_1020_; lean_object* v_idx_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v_array_1020_ = lean_ctor_get(v___y_1013_, 0);
lean_inc_ref(v_array_1020_);
v_idx_1021_ = lean_ctor_get(v___y_1013_, 1);
lean_inc(v_idx_1021_);
lean_dec_ref(v___y_1013_);
v___x_1022_ = lean_nat_add(v_idx_1021_, v_fst_1017_);
lean_dec(v_fst_1017_);
v___x_1023_ = lean_byte_array_size(v_array_1020_);
v___x_1024_ = lean_nat_dec_le(v_idx_1021_, v___x_1015_);
if (v___x_1024_ == 0)
{
v___y_1001_ = v___x_1019_;
v___y_1002_ = v_snd_1018_;
v___y_1003_ = v___x_1023_;
v___y_1004_ = v_array_1020_;
v___y_1005_ = v___x_1022_;
v___y_1006_ = v___x_1015_;
v___y_1007_ = v_idx_1021_;
goto v___jp_1000_;
}
else
{
lean_dec(v_idx_1021_);
v___y_1001_ = v___x_1019_;
v___y_1002_ = v_snd_1018_;
v___y_1003_ = v___x_1023_;
v___y_1004_ = v_array_1020_;
v___y_1005_ = v___x_1022_;
v___y_1006_ = v___x_1015_;
v___y_1007_ = v___x_1015_;
goto v___jp_1000_;
}
}
else
{
lean_object* v_array_1025_; lean_object* v_idx_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1040_; 
lean_dec(v_fst_1017_);
v_array_1025_ = lean_ctor_get(v_snd_1018_, 0);
v_idx_1026_ = lean_ctor_get(v_snd_1018_, 1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_snd_1018_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1028_ = v_snd_1018_;
v_isShared_1029_ = v_isSharedCheck_1040_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_idx_1026_);
lean_inc(v_array_1025_);
lean_dec(v_snd_1018_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1040_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; uint8_t v___x_1031_; 
v___x_1030_ = lean_byte_array_size(v_array_1025_);
lean_dec_ref(v_array_1025_);
v___x_1031_ = lean_nat_dec_le(v___x_1030_, v_idx_1026_);
lean_dec(v_idx_1026_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1032_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10));
if (v_isShared_1029_ == 0)
{
lean_ctor_set_tag(v___x_1028_, 1);
lean_ctor_set(v___x_1028_, 1, v___x_1032_);
lean_ctor_set(v___x_1028_, 0, v___y_1013_);
v___x_1034_ = v___x_1028_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___y_1013_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
else
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1036_ = lean_box(0);
if (v_isShared_1029_ == 0)
{
lean_ctor_set_tag(v___x_1028_, 1);
lean_ctor_set(v___x_1028_, 1, v___x_1036_);
lean_ctor_set(v___x_1028_, 0, v___y_1013_);
v___x_1038_ = v___x_1028_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___y_1013_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
v___jp_1041_:
{
lean_object* v___x_1043_; 
lean_inc_ref(v_pos_1042_);
v___x_1043_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(v_pos_1042_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_pos_1044_; lean_object* v_res_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1053_; 
lean_dec_ref(v_pos_1042_);
v_pos_1044_ = lean_ctor_get(v___x_1043_, 0);
v_res_1045_ = lean_ctor_get(v___x_1043_, 1);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1047_ = v___x_1043_;
v_isShared_1048_ = v_isSharedCheck_1053_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_res_1045_);
lean_inc(v_pos_1044_);
lean_dec(v___x_1043_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1053_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1049_, 0, v_res_1045_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 1, v___x_1049_);
v___x_1051_ = v___x_1047_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_pos_1044_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
else
{
lean_object* v_err_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1063_; 
v_err_1054_ = lean_ctor_get(v___x_1043_, 1);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; 
v_unused_1064_ = lean_ctor_get(v___x_1043_, 0);
lean_dec(v_unused_1064_);
v___x_1056_ = v___x_1043_;
v_isShared_1057_ = v_isSharedCheck_1063_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_err_1054_);
lean_dec(v___x_1043_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1063_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v_idx_1058_; uint8_t v___x_1059_; 
v_idx_1058_ = lean_ctor_get(v_pos_1042_, 1);
v___x_1059_ = lean_nat_dec_eq(v_idx_1058_, v_idx_1058_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1061_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v_pos_1042_);
v___x_1061_ = v___x_1056_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_pos_1042_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v_err_1054_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
else
{
lean_del_object(v___x_1056_);
lean_dec(v_err_1054_);
v___y_1013_ = v_pos_1042_;
goto v___jp_1012_;
}
}
}
}
v___jp_1065_:
{
v___y_1013_ = v_pos_1066_;
goto v___jp_1012_;
}
v___jp_1068_:
{
if (v___y_1071_ == 0)
{
v_pos_1066_ = v___y_1069_;
v_res_1067_ = v___y_1070_;
goto v___jp_1065_;
}
else
{
v_pos_1042_ = v___y_1069_;
goto v___jp_1041_;
}
}
v___jp_1072_:
{
lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1075_ = lean_byte_array_size(v_array_1009_);
v___x_1076_ = lean_nat_dec_lt(v_idx_1010_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_dec(v_idx_1010_);
lean_dec_ref(v_array_1009_);
v_pos_1066_ = v_pos_1073_;
v_res_1067_ = v_res_1074_;
goto v___jp_1065_;
}
else
{
uint8_t v___x_1077_; uint8_t v___x_1078_; uint8_t v___x_1079_; 
v___x_1077_ = lean_byte_array_fget(v_array_1009_, v_idx_1010_);
lean_dec(v_idx_1010_);
lean_dec_ref(v_array_1009_);
v___x_1078_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_1079_ = lean_uint8_dec_le(v___x_1078_, v___x_1077_);
if (v___x_1079_ == 0)
{
v___y_1069_ = v_pos_1073_;
v___y_1070_ = v_res_1074_;
v___y_1071_ = v___x_1079_;
goto v___jp_1068_;
}
else
{
uint8_t v___x_1080_; uint8_t v___x_1081_; 
v___x_1080_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_1081_ = lean_uint8_dec_le(v___x_1077_, v___x_1080_);
v___y_1069_ = v_pos_1073_;
v___y_1070_ = v_res_1074_;
v___y_1071_ = v___x_1081_;
goto v___jp_1068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___boxed(lean_object* v_config_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1109_, v_a_1110_);
lean_dec_ref(v_config_1109_);
return v_res_1111_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2(void){
_start:
{
uint32_t v___x_1115_; uint8_t v___x_1116_; 
v___x_1115_ = 47;
v___x_1116_ = lean_uint32_to_uint8(v___x_1115_);
return v___x_1116_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3(void){
_start:
{
uint32_t v___x_1117_; uint8_t v___x_1118_; 
v___x_1117_ = 63;
v___x_1118_ = lean_uint32_to_uint8(v___x_1117_);
return v___x_1118_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4(void){
_start:
{
uint32_t v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = 35;
v___x_1120_ = lean_uint32_to_uint8(v___x_1119_);
return v___x_1120_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5(void){
_start:
{
uint8_t v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1122_ = lean_uint8_to_nat(v___x_1121_);
return v___x_1122_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5);
v___x_1124_ = l_Nat_reprFast(v___x_1123_);
return v___x_1124_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1125_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6);
v___x_1126_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_1127_ = lean_string_append(v___x_1126_, v___x_1125_);
return v___x_1127_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_1129_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7);
v___x_1130_ = lean_string_append(v___x_1129_, v___x_1128_);
return v___x_1130_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8);
v___x_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
return v___x_1132_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10(void){
_start:
{
uint32_t v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = 64;
v___x_1134_ = lean_uint32_to_uint8(v___x_1133_);
return v___x_1134_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11(void){
_start:
{
uint8_t v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1136_ = lean_uint8_to_nat(v___x_1135_);
return v___x_1136_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11);
v___x_1138_ = l_Nat_reprFast(v___x_1137_);
return v___x_1138_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1139_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12);
v___x_1140_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_1141_ = lean_string_append(v___x_1140_, v___x_1139_);
return v___x_1141_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1142_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_1143_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13);
v___x_1144_ = lean_string_append(v___x_1143_, v___x_1142_);
return v___x_1144_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14);
v___x_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(lean_object* v_config_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v_port_1152_; lean_object* v___y_1153_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v_pos_1159_; lean_object* v___y_1162_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; uint8_t v___y_1174_; lean_object* v___y_1176_; lean_object* v___y_1177_; uint8_t v___y_1178_; lean_object* v___y_1179_; uint8_t v___y_1180_; lean_object* v___y_1181_; uint8_t v___y_1182_; lean_object* v___y_1194_; uint8_t v___y_1195_; lean_object* v___y_1196_; uint8_t v___y_1197_; lean_object* v___y_1198_; uint8_t v___y_1199_; lean_object* v___y_1209_; uint8_t v___y_1210_; uint8_t v___y_1211_; lean_object* v___y_1212_; lean_object* v_pos_1213_; lean_object* v___y_1216_; lean_object* v___y_1217_; uint8_t v___y_1218_; uint8_t v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; uint8_t v___y_1222_; lean_object* v_pos_1238_; lean_object* v_res_1239_; lean_object* v_pos_1291_; lean_object* v_res_1292_; lean_object* v_err_1295_; lean_object* v___x_1300_; 
lean_inc_ref(v_a_1148_);
v___x_1300_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(v_config_1147_, v_a_1148_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_pos_1301_; lean_object* v_res_1302_; lean_object* v_array_1303_; lean_object* v_idx_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1320_; 
v_pos_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_pos_1301_);
v_res_1302_ = lean_ctor_get(v___x_1300_, 1);
lean_inc(v_res_1302_);
lean_dec_ref(v___x_1300_);
v_array_1303_ = lean_ctor_get(v_pos_1301_, 0);
v_idx_1304_ = lean_ctor_get(v_pos_1301_, 1);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_pos_1301_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1306_ = v_pos_1301_;
v_isShared_1307_ = v_isSharedCheck_1320_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_idx_1304_);
lean_inc(v_array_1303_);
lean_dec(v_pos_1301_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1320_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1308_ = lean_byte_array_size(v_array_1303_);
v___x_1309_ = lean_nat_dec_lt(v_idx_1304_, v___x_1308_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; 
lean_del_object(v___x_1306_);
lean_dec(v_idx_1304_);
lean_dec_ref(v_array_1303_);
lean_dec(v_res_1302_);
v___x_1310_ = lean_box(0);
v_err_1295_ = v___x_1310_;
goto v___jp_1294_;
}
else
{
uint8_t v___x_1311_; uint8_t v_c_1312_; uint8_t v___x_1313_; 
v___x_1311_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v_c_1312_ = lean_byte_array_fget(v_array_1303_, v_idx_1304_);
v___x_1313_ = lean_uint8_dec_eq(v_c_1312_, v___x_1311_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; 
lean_del_object(v___x_1306_);
lean_dec(v_idx_1304_);
lean_dec_ref(v_array_1303_);
lean_dec(v_res_1302_);
v___x_1314_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15);
v_err_1295_ = v___x_1314_;
goto v___jp_1294_;
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v_it_x27_1318_; 
lean_dec_ref(v_a_1148_);
v___x_1315_ = lean_unsigned_to_nat(1u);
v___x_1316_ = lean_nat_add(v_idx_1304_, v___x_1315_);
lean_dec(v_idx_1304_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 1, v___x_1316_);
v_it_x27_1318_ = v___x_1306_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_array_1303_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v___x_1316_);
v_it_x27_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
v_pos_1291_ = v_it_x27_1318_;
v_res_1292_ = v_res_1302_;
goto v___jp_1290_;
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_pos_1321_; lean_object* v_res_1322_; 
lean_dec_ref(v_a_1148_);
v_pos_1321_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_pos_1321_);
v_res_1322_ = lean_ctor_get(v___x_1300_, 1);
lean_inc(v_res_1322_);
lean_dec_ref(v___x_1300_);
v_pos_1291_ = v_pos_1321_;
v_res_1292_ = v_res_1322_;
goto v___jp_1290_;
}
else
{
lean_object* v_err_1323_; 
v_err_1323_ = lean_ctor_get(v___x_1300_, 1);
lean_inc(v_err_1323_);
lean_dec_ref(v___x_1300_);
v_err_1295_ = v_err_1323_;
goto v___jp_1294_;
}
}
v___jp_1149_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1154_, 0, v___y_1150_);
lean_ctor_set(v___x_1154_, 1, v___y_1151_);
lean_ctor_set(v___x_1154_, 2, v_port_1152_);
v___x_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___y_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
return v___x_1155_;
}
v___jp_1156_:
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_box(0);
v___y_1150_ = v___y_1157_;
v___y_1151_ = v___y_1158_;
v_port_1152_ = v___x_1160_;
v___y_1153_ = v_pos_1159_;
goto v___jp_1149_;
}
v___jp_1161_:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1));
v___x_1164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___y_1162_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
return v___x_1164_;
}
v___jp_1165_:
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_box(1);
v___y_1150_ = v___y_1166_;
v___y_1151_ = v___y_1168_;
v_port_1152_ = v___x_1169_;
v___y_1153_ = v___y_1167_;
goto v___jp_1149_;
}
v___jp_1170_:
{
if (v___y_1174_ == 0)
{
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1171_);
v___y_1162_ = v___y_1172_;
goto v___jp_1161_;
}
else
{
v___y_1166_ = v___y_1171_;
v___y_1167_ = v___y_1172_;
v___y_1168_ = v___y_1173_;
goto v___jp_1165_;
}
}
v___jp_1175_:
{
if (v___y_1182_ == 0)
{
if (lean_obj_tag(v___y_1176_) == 0)
{
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1177_);
v___y_1162_ = v___y_1179_;
goto v___jp_1161_;
}
else
{
lean_object* v_val_1183_; uint8_t v___x_1184_; uint8_t v___x_1185_; uint8_t v___x_1186_; 
v_val_1183_ = lean_ctor_get(v___y_1176_, 0);
lean_inc(v_val_1183_);
lean_dec_ref(v___y_1176_);
v___x_1184_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_1185_ = lean_unbox(v_val_1183_);
v___x_1186_ = lean_uint8_dec_eq(v___x_1185_, v___x_1184_);
if (v___x_1186_ == 0)
{
uint8_t v___x_1187_; uint8_t v___x_1188_; uint8_t v___x_1189_; 
v___x_1187_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_1188_ = lean_unbox(v_val_1183_);
v___x_1189_ = lean_uint8_dec_eq(v___x_1188_, v___x_1187_);
if (v___x_1189_ == 0)
{
uint8_t v___x_1190_; uint8_t v___x_1191_; uint8_t v___x_1192_; 
v___x_1190_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v___x_1191_ = lean_unbox(v_val_1183_);
lean_dec(v_val_1183_);
v___x_1192_ = lean_uint8_dec_eq(v___x_1191_, v___x_1190_);
if (v___x_1192_ == 0)
{
v___y_1171_ = v___y_1177_;
v___y_1172_ = v___y_1179_;
v___y_1173_ = v___y_1181_;
v___y_1174_ = v___x_1192_;
goto v___jp_1170_;
}
else
{
v___y_1171_ = v___y_1177_;
v___y_1172_ = v___y_1179_;
v___y_1173_ = v___y_1181_;
v___y_1174_ = v___y_1180_;
goto v___jp_1170_;
}
}
else
{
lean_dec(v_val_1183_);
v___y_1171_ = v___y_1177_;
v___y_1172_ = v___y_1179_;
v___y_1173_ = v___y_1181_;
v___y_1174_ = v___y_1180_;
goto v___jp_1170_;
}
}
else
{
lean_dec(v_val_1183_);
v___y_1171_ = v___y_1177_;
v___y_1172_ = v___y_1179_;
v___y_1173_ = v___y_1181_;
v___y_1174_ = v___y_1178_;
goto v___jp_1170_;
}
}
}
else
{
lean_dec(v___y_1176_);
v___y_1166_ = v___y_1177_;
v___y_1167_ = v___y_1179_;
v___y_1168_ = v___y_1181_;
goto v___jp_1165_;
}
}
v___jp_1193_:
{
lean_object* v_array_1200_; lean_object* v_idx_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v_array_1200_ = lean_ctor_get(v___y_1196_, 0);
v_idx_1201_ = lean_ctor_get(v___y_1196_, 1);
v___x_1202_ = lean_byte_array_size(v_array_1200_);
v___x_1203_ = lean_nat_dec_lt(v_idx_1201_, v___x_1202_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_box(0);
v___y_1176_ = v___x_1204_;
v___y_1177_ = v___y_1194_;
v___y_1178_ = v___y_1195_;
v___y_1179_ = v___y_1196_;
v___y_1180_ = v___y_1197_;
v___y_1181_ = v___y_1198_;
v___y_1182_ = v___y_1195_;
goto v___jp_1175_;
}
else
{
uint8_t v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1205_ = lean_byte_array_fget(v_array_1200_, v_idx_1201_);
v___x_1206_ = lean_box(v___x_1205_);
v___x_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
v___y_1176_ = v___x_1207_;
v___y_1177_ = v___y_1194_;
v___y_1178_ = v___y_1195_;
v___y_1179_ = v___y_1196_;
v___y_1180_ = v___y_1197_;
v___y_1181_ = v___y_1198_;
v___y_1182_ = v___y_1199_;
goto v___jp_1175_;
}
}
v___jp_1208_:
{
uint8_t v___x_1214_; 
v___x_1214_ = 0;
v___y_1194_ = v___y_1209_;
v___y_1195_ = v___y_1210_;
v___y_1196_ = v_pos_1213_;
v___y_1197_ = v___y_1211_;
v___y_1198_ = v___y_1212_;
v___y_1199_ = v___x_1214_;
goto v___jp_1193_;
}
v___jp_1215_:
{
lean_dec(v___y_1217_);
if (v___y_1222_ == 0)
{
v___y_1209_ = v___y_1216_;
v___y_1210_ = v___y_1218_;
v___y_1211_ = v___y_1219_;
v___y_1212_ = v___y_1221_;
v_pos_1213_ = v___y_1220_;
goto v___jp_1208_;
}
else
{
if (v___y_1218_ == 0)
{
v___y_1194_ = v___y_1216_;
v___y_1195_ = v___y_1218_;
v___y_1196_ = v___y_1220_;
v___y_1197_ = v___y_1219_;
v___y_1198_ = v___y_1221_;
v___y_1199_ = v___y_1218_;
goto v___jp_1193_;
}
else
{
lean_object* v___x_1223_; 
v___x_1223_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___y_1220_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_pos_1224_; lean_object* v_res_1225_; lean_object* v___x_1226_; uint16_t v___x_1227_; 
v_pos_1224_ = lean_ctor_get(v___x_1223_, 0);
lean_inc(v_pos_1224_);
v_res_1225_ = lean_ctor_get(v___x_1223_, 1);
lean_inc(v_res_1225_);
lean_dec_ref(v___x_1223_);
v___x_1226_ = lean_alloc_ctor(2, 0, 2);
v___x_1227_ = lean_unbox(v_res_1225_);
lean_dec(v_res_1225_);
lean_ctor_set_uint16(v___x_1226_, 0, v___x_1227_);
v___y_1150_ = v___y_1216_;
v___y_1151_ = v___y_1221_;
v_port_1152_ = v___x_1226_;
v___y_1153_ = v_pos_1224_;
goto v___jp_1149_;
}
else
{
lean_object* v_pos_1228_; lean_object* v_err_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1216_);
v_pos_1228_ = lean_ctor_get(v___x_1223_, 0);
v_err_1229_ = lean_ctor_get(v___x_1223_, 1);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1223_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_err_1229_);
lean_inc(v_pos_1228_);
lean_dec(v___x_1223_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_pos_1228_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_err_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
}
v___jp_1237_:
{
lean_object* v___x_1240_; 
v___x_1240_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1147_, v_pos_1238_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_pos_1241_; lean_object* v_res_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1280_; 
v_pos_1241_ = lean_ctor_get(v___x_1240_, 0);
v_res_1242_ = lean_ctor_get(v___x_1240_, 1);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1244_ = v___x_1240_;
v_isShared_1245_ = v_isSharedCheck_1280_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_res_1242_);
lean_inc(v_pos_1241_);
lean_dec(v___x_1240_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1280_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v_array_1246_; lean_object* v_idx_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v_array_1246_ = lean_ctor_get(v_pos_1241_, 0);
v_idx_1247_ = lean_ctor_get(v_pos_1241_, 1);
v___x_1248_ = lean_byte_array_size(v_array_1246_);
v___x_1249_ = lean_nat_dec_lt(v_idx_1247_, v___x_1248_);
if (v___x_1249_ == 0)
{
lean_del_object(v___x_1244_);
v___y_1157_ = v_res_1239_;
v___y_1158_ = v_res_1242_;
v_pos_1159_ = v_pos_1241_;
goto v___jp_1156_;
}
else
{
uint8_t v___x_1250_; uint8_t v___x_1251_; uint8_t v___x_1252_; 
v___x_1250_ = lean_byte_array_fget(v_array_1246_, v_idx_1247_);
v___x_1251_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1252_ = lean_uint8_dec_eq(v___x_1250_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_del_object(v___x_1244_);
v___y_1157_ = v_res_1239_;
v___y_1158_ = v_res_1242_;
v_pos_1159_ = v_pos_1241_;
goto v___jp_1156_;
}
else
{
if (v___x_1252_ == 0)
{
lean_del_object(v___x_1244_);
v___y_1157_ = v_res_1239_;
v___y_1158_ = v_res_1242_;
v_pos_1159_ = v_pos_1241_;
goto v___jp_1156_;
}
else
{
if (v___x_1249_ == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1255_; 
lean_dec(v_res_1242_);
lean_dec(v_res_1239_);
v___x_1253_ = lean_box(0);
if (v_isShared_1245_ == 0)
{
lean_ctor_set_tag(v___x_1244_, 1);
lean_ctor_set(v___x_1244_, 1, v___x_1253_);
v___x_1255_ = v___x_1244_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_pos_1241_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
else
{
if (v___x_1252_ == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1259_; 
lean_dec(v_res_1242_);
lean_dec(v_res_1239_);
v___x_1257_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
if (v_isShared_1245_ == 0)
{
lean_ctor_set_tag(v___x_1244_, 1);
lean_ctor_set(v___x_1244_, 1, v___x_1257_);
v___x_1259_ = v___x_1244_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_pos_1241_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
else
{
lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1277_; 
lean_inc(v_idx_1247_);
lean_inc_ref(v_array_1246_);
lean_del_object(v___x_1244_);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_pos_1241_);
if (v_isSharedCheck_1277_ == 0)
{
lean_object* v_unused_1278_; lean_object* v_unused_1279_; 
v_unused_1278_ = lean_ctor_get(v_pos_1241_, 1);
lean_dec(v_unused_1278_);
v_unused_1279_ = lean_ctor_get(v_pos_1241_, 0);
lean_dec(v_unused_1279_);
v___x_1262_ = v_pos_1241_;
v_isShared_1263_ = v_isSharedCheck_1277_;
goto v_resetjp_1261_;
}
else
{
lean_dec(v_pos_1241_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1277_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v_it_x27_1267_; 
v___x_1264_ = lean_unsigned_to_nat(1u);
v___x_1265_ = lean_nat_add(v_idx_1247_, v___x_1264_);
lean_dec(v_idx_1247_);
lean_inc(v___x_1265_);
lean_inc_ref(v_array_1246_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 1, v___x_1265_);
v_it_x27_1267_ = v___x_1262_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_array_1246_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v___x_1265_);
v_it_x27_1267_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
uint8_t v___x_1268_; 
v___x_1268_ = lean_nat_dec_lt(v___x_1265_, v___x_1248_);
if (v___x_1268_ == 0)
{
lean_dec(v___x_1265_);
lean_dec_ref(v_array_1246_);
v___y_1209_ = v_res_1239_;
v___y_1210_ = v___x_1249_;
v___y_1211_ = v___x_1252_;
v___y_1212_ = v_res_1242_;
v_pos_1213_ = v_it_x27_1267_;
goto v___jp_1208_;
}
else
{
uint8_t v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; uint8_t v___x_1273_; 
v___x_1269_ = lean_byte_array_fget(v_array_1246_, v___x_1265_);
lean_dec(v___x_1265_);
lean_dec_ref(v_array_1246_);
v___x_1270_ = lean_box(v___x_1269_);
v___x_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
v___x_1272_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_1273_ = lean_uint8_dec_le(v___x_1272_, v___x_1269_);
if (v___x_1273_ == 0)
{
v___y_1216_ = v_res_1239_;
v___y_1217_ = v___x_1271_;
v___y_1218_ = v___x_1249_;
v___y_1219_ = v___x_1252_;
v___y_1220_ = v_it_x27_1267_;
v___y_1221_ = v_res_1242_;
v___y_1222_ = v___x_1273_;
goto v___jp_1215_;
}
else
{
uint8_t v___x_1274_; uint8_t v___x_1275_; 
v___x_1274_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_1275_ = lean_uint8_dec_le(v___x_1269_, v___x_1274_);
v___y_1216_ = v_res_1239_;
v___y_1217_ = v___x_1271_;
v___y_1218_ = v___x_1249_;
v___y_1219_ = v___x_1252_;
v___y_1220_ = v_it_x27_1267_;
v___y_1221_ = v_res_1242_;
v___y_1222_ = v___x_1275_;
goto v___jp_1215_;
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
lean_object* v_pos_1281_; lean_object* v_err_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec(v_res_1239_);
v_pos_1281_ = lean_ctor_get(v___x_1240_, 0);
v_err_1282_ = lean_ctor_get(v___x_1240_, 1);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1240_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_err_1282_);
lean_inc(v_pos_1281_);
lean_dec(v___x_1240_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_pos_1281_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_err_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
v___jp_1290_:
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1293_, 0, v_res_1292_);
v_pos_1238_ = v_pos_1291_;
v_res_1239_ = v___x_1293_;
goto v___jp_1237_;
}
v___jp_1294_:
{
lean_object* v_idx_1296_; uint8_t v___x_1297_; 
v_idx_1296_ = lean_ctor_get(v_a_1148_, 1);
v___x_1297_ = lean_nat_dec_eq(v_idx_1296_, v_idx_1296_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; 
v___x_1298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1298_, 0, v_a_1148_);
lean_ctor_set(v___x_1298_, 1, v_err_1295_);
return v___x_1298_;
}
else
{
lean_object* v___x_1299_; 
lean_dec(v_err_1295_);
v___x_1299_ = lean_box(0);
v_pos_1238_ = v_a_1148_;
v_res_1239_ = v___x_1299_;
goto v___jp_1237_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___boxed(lean_object* v_config_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_1324_, v_a_1325_);
lean_dec_ref(v_config_1324_);
return v_res_1326_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(uint8_t v_c_1327_){
_start:
{
uint8_t v___y_1329_; uint8_t v___y_1333_; uint8_t v___y_1339_; uint8_t v___y_1359_; uint8_t v___y_1365_; uint8_t v___y_1371_; uint8_t v___y_1377_; uint8_t v___y_1383_; uint8_t v___x_1388_; uint8_t v___x_1389_; 
v___x_1388_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_1389_ = lean_uint8_dec_le(v___x_1388_, v_c_1327_);
if (v___x_1389_ == 0)
{
v___y_1383_ = v___x_1389_;
goto v___jp_1382_;
}
else
{
uint8_t v___x_1390_; uint8_t v___x_1391_; 
v___x_1390_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_1391_ = lean_uint8_dec_le(v_c_1327_, v___x_1390_);
v___y_1383_ = v___x_1391_;
goto v___jp_1382_;
}
v___jp_1328_:
{
if (v___y_1329_ == 0)
{
uint8_t v___x_1330_; uint8_t v___x_1331_; 
v___x_1330_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_1331_ = lean_uint8_dec_eq(v_c_1327_, v___x_1330_);
if (v___x_1331_ == 0)
{
return v___y_1329_;
}
else
{
return v___x_1331_;
}
}
else
{
return v___y_1329_;
}
}
v___jp_1332_:
{
if (v___y_1333_ == 0)
{
uint8_t v___x_1334_; uint8_t v___x_1335_; 
v___x_1334_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1335_ = lean_uint8_dec_eq(v_c_1327_, v___x_1334_);
if (v___x_1335_ == 0)
{
uint8_t v___x_1336_; uint8_t v___x_1337_; 
v___x_1336_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1337_ = lean_uint8_dec_eq(v_c_1327_, v___x_1336_);
v___y_1329_ = v___x_1337_;
goto v___jp_1328_;
}
else
{
v___y_1329_ = v___x_1335_;
goto v___jp_1328_;
}
}
else
{
return v___y_1333_;
}
}
v___jp_1338_:
{
if (v___y_1339_ == 0)
{
uint8_t v___x_1340_; uint8_t v___x_1341_; 
v___x_1340_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_1341_ = lean_uint8_dec_eq(v_c_1327_, v___x_1340_);
if (v___x_1341_ == 0)
{
uint8_t v___x_1342_; uint8_t v___x_1343_; 
v___x_1342_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_1343_ = lean_uint8_dec_eq(v_c_1327_, v___x_1342_);
if (v___x_1343_ == 0)
{
uint8_t v___x_1344_; uint8_t v___x_1345_; 
v___x_1344_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_1345_ = lean_uint8_dec_eq(v_c_1327_, v___x_1344_);
if (v___x_1345_ == 0)
{
uint8_t v___x_1346_; uint8_t v___x_1347_; 
v___x_1346_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_1347_ = lean_uint8_dec_eq(v_c_1327_, v___x_1346_);
if (v___x_1347_ == 0)
{
uint8_t v___x_1348_; uint8_t v___x_1349_; 
v___x_1348_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_1349_ = lean_uint8_dec_eq(v_c_1327_, v___x_1348_);
if (v___x_1349_ == 0)
{
uint8_t v___x_1350_; uint8_t v___x_1351_; 
v___x_1350_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0);
v___x_1351_ = lean_uint8_dec_eq(v_c_1327_, v___x_1350_);
if (v___x_1351_ == 0)
{
uint8_t v___x_1352_; uint8_t v___x_1353_; 
v___x_1352_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_1353_ = lean_uint8_dec_eq(v_c_1327_, v___x_1352_);
if (v___x_1353_ == 0)
{
uint8_t v___x_1354_; uint8_t v___x_1355_; 
v___x_1354_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_1355_ = lean_uint8_dec_eq(v_c_1327_, v___x_1354_);
if (v___x_1355_ == 0)
{
uint8_t v___x_1356_; uint8_t v___x_1357_; 
v___x_1356_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_1357_ = lean_uint8_dec_eq(v_c_1327_, v___x_1356_);
v___y_1333_ = v___x_1357_;
goto v___jp_1332_;
}
else
{
v___y_1333_ = v___x_1355_;
goto v___jp_1332_;
}
}
else
{
v___y_1333_ = v___x_1353_;
goto v___jp_1332_;
}
}
else
{
v___y_1333_ = v___x_1351_;
goto v___jp_1332_;
}
}
else
{
v___y_1333_ = v___x_1349_;
goto v___jp_1332_;
}
}
else
{
v___y_1333_ = v___x_1347_;
goto v___jp_1332_;
}
}
else
{
v___y_1333_ = v___x_1345_;
goto v___jp_1332_;
}
}
else
{
v___y_1333_ = v___x_1343_;
goto v___jp_1332_;
}
}
else
{
v___y_1333_ = v___x_1341_;
goto v___jp_1332_;
}
}
else
{
return v___y_1339_;
}
}
v___jp_1358_:
{
if (v___y_1359_ == 0)
{
uint8_t v___x_1360_; uint8_t v___x_1361_; 
v___x_1360_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_1361_ = lean_uint8_dec_eq(v_c_1327_, v___x_1360_);
if (v___x_1361_ == 0)
{
uint8_t v___x_1362_; uint8_t v___x_1363_; 
v___x_1362_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_1363_ = lean_uint8_dec_eq(v_c_1327_, v___x_1362_);
v___y_1339_ = v___x_1363_;
goto v___jp_1338_;
}
else
{
v___y_1339_ = v___x_1361_;
goto v___jp_1338_;
}
}
else
{
return v___y_1359_;
}
}
v___jp_1364_:
{
if (v___y_1365_ == 0)
{
uint8_t v___x_1366_; uint8_t v___x_1367_; 
v___x_1366_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_1367_ = lean_uint8_dec_eq(v_c_1327_, v___x_1366_);
if (v___x_1367_ == 0)
{
uint8_t v___x_1368_; uint8_t v___x_1369_; 
v___x_1368_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_1369_ = lean_uint8_dec_eq(v_c_1327_, v___x_1368_);
v___y_1359_ = v___x_1369_;
goto v___jp_1358_;
}
else
{
v___y_1359_ = v___x_1367_;
goto v___jp_1358_;
}
}
else
{
return v___y_1365_;
}
}
v___jp_1370_:
{
if (v___y_1371_ == 0)
{
uint8_t v___x_1372_; uint8_t v___x_1373_; 
v___x_1372_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1);
v___x_1373_ = lean_uint8_dec_eq(v_c_1327_, v___x_1372_);
if (v___x_1373_ == 0)
{
uint8_t v___x_1374_; uint8_t v___x_1375_; 
v___x_1374_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2);
v___x_1375_ = lean_uint8_dec_eq(v_c_1327_, v___x_1374_);
v___y_1365_ = v___x_1375_;
goto v___jp_1364_;
}
else
{
v___y_1365_ = v___x_1373_;
goto v___jp_1364_;
}
}
else
{
return v___y_1371_;
}
}
v___jp_1376_:
{
if (v___y_1377_ == 0)
{
uint8_t v___x_1378_; uint8_t v___x_1379_; 
v___x_1378_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_1379_ = lean_uint8_dec_le(v___x_1378_, v_c_1327_);
if (v___x_1379_ == 0)
{
v___y_1371_ = v___x_1379_;
goto v___jp_1370_;
}
else
{
uint8_t v___x_1380_; uint8_t v___x_1381_; 
v___x_1380_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_1381_ = lean_uint8_dec_le(v_c_1327_, v___x_1380_);
v___y_1371_ = v___x_1381_;
goto v___jp_1370_;
}
}
else
{
return v___y_1377_;
}
}
v___jp_1382_:
{
if (v___y_1383_ == 0)
{
uint8_t v___x_1384_; uint8_t v___x_1385_; 
v___x_1384_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_1385_ = lean_uint8_dec_le(v___x_1384_, v_c_1327_);
if (v___x_1385_ == 0)
{
v___y_1377_ = v___x_1385_;
goto v___jp_1376_;
}
else
{
uint8_t v___x_1386_; uint8_t v___x_1387_; 
v___x_1386_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_1387_ = lean_uint8_dec_le(v_c_1327_, v___x_1386_);
v___y_1377_ = v___x_1387_;
goto v___jp_1376_;
}
}
else
{
return v___y_1383_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0___boxed(lean_object* v_c_1392_){
_start:
{
uint8_t v_c_boxed_1393_; uint8_t v_res_1394_; lean_object* v_r_1395_; 
v_c_boxed_1393_ = lean_unbox(v_c_1392_);
v_res_1394_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(v_c_boxed_1393_);
v_r_1395_ = lean_box(v_res_1394_);
return v_r_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(lean_object* v_config_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v_maxSegmentLength_1399_; lean_object* v___f_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v_fst_1403_; lean_object* v_snd_1404_; lean_object* v_array_1405_; lean_object* v_idx_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1423_; 
v_maxSegmentLength_1399_ = lean_ctor_get(v_config_1397_, 3);
v___f_1400_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0));
v___x_1401_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1398_);
v___x_1402_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd(v___f_1400_, v_maxSegmentLength_1399_, v___x_1401_, v_a_1398_);
v_fst_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_fst_1403_);
v_snd_1404_ = lean_ctor_get(v___x_1402_, 1);
lean_inc(v_snd_1404_);
lean_dec_ref(v___x_1402_);
v_array_1405_ = lean_ctor_get(v_a_1398_, 0);
v_idx_1406_ = lean_ctor_get(v_a_1398_, 1);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_a_1398_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1408_ = v_a_1398_;
v_isShared_1409_ = v_isSharedCheck_1423_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_idx_1406_);
lean_inc(v_array_1405_);
lean_dec(v_a_1398_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1423_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v_lower_1411_; lean_object* v_upper_1412_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___y_1420_; uint8_t v___x_1422_; 
v___x_1417_ = lean_nat_add(v_idx_1406_, v_fst_1403_);
lean_dec(v_fst_1403_);
v___x_1418_ = lean_byte_array_size(v_array_1405_);
v___x_1422_ = lean_nat_dec_le(v_idx_1406_, v___x_1401_);
if (v___x_1422_ == 0)
{
v___y_1420_ = v_idx_1406_;
goto v___jp_1419_;
}
else
{
lean_dec(v_idx_1406_);
v___y_1420_ = v___x_1401_;
goto v___jp_1419_;
}
v___jp_1410_:
{
lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1413_ = l_ByteArray_toByteSlice(v_array_1405_, v_lower_1411_, v_upper_1412_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 1, v___x_1413_);
lean_ctor_set(v___x_1408_, 0, v_snd_1404_);
v___x_1415_ = v___x_1408_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_snd_1404_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
v___jp_1419_:
{
uint8_t v___x_1421_; 
v___x_1421_ = lean_nat_dec_le(v___x_1417_, v___x_1418_);
if (v___x_1421_ == 0)
{
lean_dec(v___x_1417_);
v_lower_1411_ = v___y_1420_;
v_upper_1412_ = v___x_1418_;
goto v___jp_1410_;
}
else
{
v_lower_1411_ = v___y_1420_;
v_upper_1412_ = v___x_1417_;
goto v___jp_1410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___boxed(lean_object* v_config_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1424_, v_a_1425_);
lean_dec_ref(v_config_1424_);
return v_res_1426_;
}
}
LEAN_EXPORT uint8_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0(uint8_t v_c_1427_){
_start:
{
uint8_t v___x_1428_; uint8_t v___x_1429_; 
v___x_1428_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_1429_ = lean_uint8_dec_eq(v_c_1427_, v___x_1428_);
if (v___x_1429_ == 0)
{
uint8_t v___x_1430_; uint8_t v___x_1431_; 
v___x_1430_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v___x_1431_ = lean_uint8_dec_eq(v_c_1427_, v___x_1430_);
return v___x_1431_;
}
else
{
return v___x_1429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0___boxed(lean_object* v_c_1432_){
_start:
{
uint8_t v_c_boxed_1433_; uint8_t v_res_1434_; lean_object* v_r_1435_; 
v_c_boxed_1433_ = lean_unbox(v_c_1432_);
v_res_1434_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0(v_c_boxed_1433_);
v_r_1435_ = lean_box(v_res_1434_);
return v_r_1435_;
}
}
LEAN_EXPORT uint8_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__1(uint8_t v___y_1436_){
_start:
{
uint8_t v___y_1438_; uint8_t v___y_1444_; uint8_t v___y_1464_; uint8_t v___y_1470_; uint8_t v___y_1476_; uint8_t v___y_1482_; uint8_t v___y_1488_; uint8_t v___x_1493_; uint8_t v___x_1494_; 
v___x_1493_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_1494_ = lean_uint8_dec_le(v___x_1493_, v___y_1436_);
if (v___x_1494_ == 0)
{
v___y_1488_ = v___x_1494_;
goto v___jp_1487_;
}
else
{
uint8_t v___x_1495_; uint8_t v___x_1496_; 
v___x_1495_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_1496_ = lean_uint8_dec_le(v___y_1436_, v___x_1495_);
v___y_1488_ = v___x_1496_;
goto v___jp_1487_;
}
v___jp_1437_:
{
if (v___y_1438_ == 0)
{
uint8_t v___x_1439_; uint8_t v___x_1440_; 
v___x_1439_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1440_ = lean_uint8_dec_eq(v___y_1436_, v___x_1439_);
if (v___x_1440_ == 0)
{
uint8_t v___x_1441_; uint8_t v___x_1442_; 
v___x_1441_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1442_ = lean_uint8_dec_eq(v___y_1436_, v___x_1441_);
return v___x_1442_;
}
else
{
return v___x_1440_;
}
}
else
{
return v___y_1438_;
}
}
v___jp_1443_:
{
if (v___y_1444_ == 0)
{
uint8_t v___x_1445_; uint8_t v___x_1446_; 
v___x_1445_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_1446_ = lean_uint8_dec_eq(v___y_1436_, v___x_1445_);
if (v___x_1446_ == 0)
{
uint8_t v___x_1447_; uint8_t v___x_1448_; 
v___x_1447_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_1448_ = lean_uint8_dec_eq(v___y_1436_, v___x_1447_);
if (v___x_1448_ == 0)
{
uint8_t v___x_1449_; uint8_t v___x_1450_; 
v___x_1449_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_1450_ = lean_uint8_dec_eq(v___y_1436_, v___x_1449_);
if (v___x_1450_ == 0)
{
uint8_t v___x_1451_; uint8_t v___x_1452_; 
v___x_1451_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_1452_ = lean_uint8_dec_eq(v___y_1436_, v___x_1451_);
if (v___x_1452_ == 0)
{
uint8_t v___x_1453_; uint8_t v___x_1454_; 
v___x_1453_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_1454_ = lean_uint8_dec_eq(v___y_1436_, v___x_1453_);
if (v___x_1454_ == 0)
{
uint8_t v___x_1455_; uint8_t v___x_1456_; 
v___x_1455_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0);
v___x_1456_ = lean_uint8_dec_eq(v___y_1436_, v___x_1455_);
if (v___x_1456_ == 0)
{
uint8_t v___x_1457_; uint8_t v___x_1458_; 
v___x_1457_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_1458_ = lean_uint8_dec_eq(v___y_1436_, v___x_1457_);
if (v___x_1458_ == 0)
{
uint8_t v___x_1459_; uint8_t v___x_1460_; 
v___x_1459_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_1460_ = lean_uint8_dec_eq(v___y_1436_, v___x_1459_);
if (v___x_1460_ == 0)
{
uint8_t v___x_1461_; uint8_t v___x_1462_; 
v___x_1461_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_1462_ = lean_uint8_dec_eq(v___y_1436_, v___x_1461_);
v___y_1438_ = v___x_1462_;
goto v___jp_1437_;
}
else
{
v___y_1438_ = v___x_1460_;
goto v___jp_1437_;
}
}
else
{
v___y_1438_ = v___x_1458_;
goto v___jp_1437_;
}
}
else
{
v___y_1438_ = v___x_1456_;
goto v___jp_1437_;
}
}
else
{
v___y_1438_ = v___x_1454_;
goto v___jp_1437_;
}
}
else
{
v___y_1438_ = v___x_1452_;
goto v___jp_1437_;
}
}
else
{
v___y_1438_ = v___x_1450_;
goto v___jp_1437_;
}
}
else
{
v___y_1438_ = v___x_1448_;
goto v___jp_1437_;
}
}
else
{
v___y_1438_ = v___x_1446_;
goto v___jp_1437_;
}
}
else
{
return v___y_1444_;
}
}
v___jp_1463_:
{
if (v___y_1464_ == 0)
{
uint8_t v___x_1465_; uint8_t v___x_1466_; 
v___x_1465_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_1466_ = lean_uint8_dec_eq(v___y_1436_, v___x_1465_);
if (v___x_1466_ == 0)
{
uint8_t v___x_1467_; uint8_t v___x_1468_; 
v___x_1467_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_1468_ = lean_uint8_dec_eq(v___y_1436_, v___x_1467_);
v___y_1444_ = v___x_1468_;
goto v___jp_1443_;
}
else
{
v___y_1444_ = v___x_1466_;
goto v___jp_1443_;
}
}
else
{
return v___y_1464_;
}
}
v___jp_1469_:
{
if (v___y_1470_ == 0)
{
uint8_t v___x_1471_; uint8_t v___x_1472_; 
v___x_1471_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_1472_ = lean_uint8_dec_eq(v___y_1436_, v___x_1471_);
if (v___x_1472_ == 0)
{
uint8_t v___x_1473_; uint8_t v___x_1474_; 
v___x_1473_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_1474_ = lean_uint8_dec_eq(v___y_1436_, v___x_1473_);
v___y_1464_ = v___x_1474_;
goto v___jp_1463_;
}
else
{
v___y_1464_ = v___x_1472_;
goto v___jp_1463_;
}
}
else
{
return v___y_1470_;
}
}
v___jp_1475_:
{
if (v___y_1476_ == 0)
{
uint8_t v___x_1477_; uint8_t v___x_1478_; 
v___x_1477_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1);
v___x_1478_ = lean_uint8_dec_eq(v___y_1436_, v___x_1477_);
if (v___x_1478_ == 0)
{
uint8_t v___x_1479_; uint8_t v___x_1480_; 
v___x_1479_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2);
v___x_1480_ = lean_uint8_dec_eq(v___y_1436_, v___x_1479_);
v___y_1470_ = v___x_1480_;
goto v___jp_1469_;
}
else
{
v___y_1470_ = v___x_1478_;
goto v___jp_1469_;
}
}
else
{
return v___y_1476_;
}
}
v___jp_1481_:
{
if (v___y_1482_ == 0)
{
uint8_t v___x_1483_; uint8_t v___x_1484_; 
v___x_1483_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_1484_ = lean_uint8_dec_le(v___x_1483_, v___y_1436_);
if (v___x_1484_ == 0)
{
v___y_1476_ = v___x_1484_;
goto v___jp_1475_;
}
else
{
uint8_t v___x_1485_; uint8_t v___x_1486_; 
v___x_1485_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_1486_ = lean_uint8_dec_le(v___y_1436_, v___x_1485_);
v___y_1476_ = v___x_1486_;
goto v___jp_1475_;
}
}
else
{
return v___y_1482_;
}
}
v___jp_1487_:
{
if (v___y_1488_ == 0)
{
uint8_t v___x_1489_; uint8_t v___x_1490_; 
v___x_1489_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_1490_ = lean_uint8_dec_le(v___x_1489_, v___y_1436_);
if (v___x_1490_ == 0)
{
v___y_1482_ = v___x_1490_;
goto v___jp_1481_;
}
else
{
uint8_t v___x_1491_; uint8_t v___x_1492_; 
v___x_1491_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_1492_ = lean_uint8_dec_le(v___y_1436_, v___x_1491_);
v___y_1482_ = v___x_1492_;
goto v___jp_1481_;
}
}
else
{
return v___y_1488_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__1___boxed(lean_object* v___y_1497_){
_start:
{
uint8_t v___y_19202__boxed_1498_; uint8_t v_res_1499_; lean_object* v_r_1500_; 
v___y_19202__boxed_1498_ = lean_unbox(v___y_1497_);
v_res_1499_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__1(v___y_19202__boxed_1498_);
v_r_1500_ = lean_box(v_res_1499_);
return v_r_1500_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___f_1502_; lean_object* v___x_1503_; 
v___f_1502_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__0));
v___x_1503_ = l_Std_Http_URI_EncodedString_empty(v___f_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(lean_object* v_config_1511_, lean_object* v_b_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v_array_1526_; lean_object* v_idx_1527_; lean_object* v_fst_1528_; lean_object* v_snd_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1731_; 
v_array_1526_ = lean_ctor_get(v___y_1513_, 0);
v_idx_1527_ = lean_ctor_get(v___y_1513_, 1);
v_fst_1528_ = lean_ctor_get(v_b_1512_, 0);
v_snd_1529_ = lean_ctor_get(v_b_1512_, 1);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_b_1512_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1531_ = v_b_1512_;
v_isShared_1532_ = v_isSharedCheck_1731_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_snd_1529_);
lean_inc(v_fst_1528_);
lean_dec(v_b_1512_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1731_;
goto v_resetjp_1530_;
}
v___jp_1514_:
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___y_1516_);
lean_ctor_set(v___x_1518_, 1, v___y_1517_);
v_b_1512_ = v___x_1518_;
v___y_1513_ = v___y_1515_;
goto _start;
}
v___jp_1520_:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___y_1521_);
lean_ctor_set(v___x_1524_, 1, v___y_1523_);
v___x_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___y_1522_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
return v___x_1525_;
}
v_resetjp_1530_:
{
lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1533_ = lean_byte_array_size(v_array_1526_);
v___x_1534_ = lean_nat_dec_lt(v_idx_1527_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1536_; 
lean_dec_ref(v_config_1511_);
if (v_isShared_1532_ == 0)
{
v___x_1536_ = v___x_1531_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_fst_1528_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_snd_1529_);
v___x_1536_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___y_1513_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
return v___x_1537_;
}
}
else
{
if (v___x_1534_ == 0)
{
lean_object* v___x_1540_; 
lean_dec_ref(v_config_1511_);
if (v_isShared_1532_ == 0)
{
v___x_1540_ = v___x_1531_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_fst_1528_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_snd_1529_);
v___x_1540_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
lean_object* v___x_1541_; 
v___x_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___y_1513_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
return v___x_1541_;
}
}
else
{
uint8_t v___x_1543_; uint8_t v___x_1544_; 
v___x_1543_ = lean_byte_array_fget(v_array_1526_, v_idx_1527_);
v___x_1544_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0(v___x_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; uint8_t v___y_1658_; uint8_t v___y_1662_; uint8_t v___y_1666_; uint8_t v___y_1672_; uint8_t v___y_1692_; uint8_t v___y_1698_; uint8_t v___y_1704_; uint8_t v___y_1710_; uint8_t v___y_1716_; uint8_t v___x_1721_; uint8_t v___x_1722_; 
v___x_1721_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_1722_ = lean_uint8_dec_eq(v___x_1543_, v___x_1721_);
if (v___x_1722_ == 0)
{
uint8_t v___x_1723_; uint8_t v___x_1724_; 
v___x_1723_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_1724_ = lean_uint8_dec_le(v___x_1723_, v___x_1543_);
if (v___x_1724_ == 0)
{
v___y_1716_ = v___x_1724_;
goto v___jp_1715_;
}
else
{
uint8_t v___x_1725_; uint8_t v___x_1726_; 
v___x_1725_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_1726_ = lean_uint8_dec_le(v___x_1543_, v___x_1725_);
v___y_1716_ = v___x_1726_;
goto v___jp_1715_;
}
}
else
{
v___y_1658_ = v___x_1722_;
goto v___jp_1657_;
}
v___jp_1545_:
{
lean_object* v___x_1550_; uint8_t v___x_1551_; 
v___x_1550_ = lean_array_get_size(v___y_1548_);
v___x_1551_ = lean_nat_dec_le(v___y_1546_, v___x_1550_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1555_; 
lean_dec(v___y_1546_);
v___x_1552_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1);
v___x_1553_ = lean_array_push(v___y_1548_, v___x_1552_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 1, v___y_1549_);
lean_ctor_set(v___x_1531_, 0, v___x_1553_);
v___x_1555_ = v___x_1531_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v___y_1549_);
v___x_1555_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
v_b_1512_ = v___x_1555_;
v___y_1513_ = v___y_1547_;
goto _start;
}
}
else
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_del_object(v___x_1531_);
lean_dec_ref(v_config_1511_);
v___x_1558_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__2));
v___x_1559_ = l_Nat_reprFast(v___y_1546_);
v___x_1560_ = lean_string_append(v___x_1558_, v___x_1559_);
lean_dec_ref(v___x_1559_);
v___x_1561_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__3));
v___x_1562_ = lean_string_append(v___x_1560_, v___x_1561_);
v___x_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
v___x_1564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___y_1547_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
return v___x_1564_;
}
}
v___jp_1565_:
{
lean_object* v_maxPathSegments_1566_; lean_object* v_maxTotalPathLength_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
v_maxPathSegments_1566_ = lean_ctor_get(v_config_1511_, 6);
v_maxTotalPathLength_1567_ = lean_ctor_get(v_config_1511_, 7);
v___x_1568_ = lean_array_get_size(v_fst_1528_);
v___x_1569_ = lean_nat_dec_le(v_maxPathSegments_1566_, v___x_1568_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; 
v___x_1570_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1511_, v___y_1513_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_pos_1571_; lean_object* v_res_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1640_; 
v_pos_1571_ = lean_ctor_get(v___x_1570_, 0);
v_res_1572_ = lean_ctor_get(v___x_1570_, 1);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1574_ = v___x_1570_;
v_isShared_1575_ = v_isSharedCheck_1640_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_res_1572_);
lean_inc(v_pos_1571_);
lean_dec(v___x_1570_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1640_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
lean_inc(v_res_1572_);
v___x_1576_ = l_ByteSlice_toByteArray(v_res_1572_);
v___x_1577_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1576_);
if (lean_obj_tag(v___x_1577_) == 1)
{
lean_object* v_val_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1635_; 
v_val_1578_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1580_ = v___x_1577_;
v_isShared_1581_ = v_isSharedCheck_1635_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_val_1578_);
lean_dec(v___x_1577_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1635_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; 
v___x_1582_ = l_ByteSlice_size(v_res_1572_);
lean_dec(v_res_1572_);
v___x_1583_ = lean_nat_add(v_snd_1529_, v___x_1582_);
lean_dec(v___x_1582_);
lean_dec(v_snd_1529_);
v___x_1584_ = lean_nat_dec_lt(v_maxTotalPathLength_1567_, v___x_1583_);
if (v___x_1584_ == 0)
{
lean_object* v_array_1585_; lean_object* v_idx_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; 
v_array_1585_ = lean_ctor_get(v_pos_1571_, 0);
v_idx_1586_ = lean_ctor_get(v_pos_1571_, 1);
v___x_1587_ = lean_array_push(v_fst_1528_, v_val_1578_);
v___x_1588_ = lean_byte_array_size(v_array_1585_);
v___x_1589_ = lean_nat_dec_lt(v_idx_1586_, v___x_1588_);
if (v___x_1589_ == 0)
{
lean_del_object(v___x_1580_);
lean_del_object(v___x_1574_);
lean_del_object(v___x_1531_);
lean_dec_ref(v_config_1511_);
v___y_1521_ = v___x_1587_;
v___y_1522_ = v_pos_1571_;
v___y_1523_ = v___x_1583_;
goto v___jp_1520_;
}
else
{
uint8_t v___x_1590_; uint8_t v___x_1591_; uint8_t v___x_1592_; 
v___x_1590_ = lean_byte_array_fget(v_array_1585_, v_idx_1586_);
v___x_1591_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_1592_ = lean_uint8_dec_eq(v___x_1590_, v___x_1591_);
if (v___x_1592_ == 0)
{
lean_del_object(v___x_1580_);
lean_del_object(v___x_1574_);
lean_del_object(v___x_1531_);
lean_dec_ref(v_config_1511_);
v___y_1521_ = v___x_1587_;
v___y_1522_ = v_pos_1571_;
v___y_1523_ = v___x_1583_;
goto v___jp_1520_;
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
v___x_1593_ = lean_unsigned_to_nat(1u);
v___x_1594_ = lean_nat_add(v___x_1583_, v___x_1593_);
lean_dec(v___x_1583_);
v___x_1595_ = lean_nat_dec_lt(v_maxTotalPathLength_1567_, v___x_1594_);
if (v___x_1595_ == 0)
{
lean_del_object(v___x_1580_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1596_; lean_object* v___x_1598_; 
lean_dec(v___x_1594_);
lean_dec_ref(v___x_1587_);
lean_del_object(v___x_1531_);
lean_dec_ref(v_config_1511_);
v___x_1596_ = lean_box(0);
if (v_isShared_1575_ == 0)
{
lean_ctor_set_tag(v___x_1574_, 1);
lean_ctor_set(v___x_1574_, 1, v___x_1596_);
v___x_1598_ = v___x_1574_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_pos_1571_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
else
{
lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1610_; 
lean_inc(v_idx_1586_);
lean_inc_ref(v_array_1585_);
lean_del_object(v___x_1574_);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_pos_1571_);
if (v_isSharedCheck_1610_ == 0)
{
lean_object* v_unused_1611_; lean_object* v_unused_1612_; 
v_unused_1611_ = lean_ctor_get(v_pos_1571_, 1);
lean_dec(v_unused_1611_);
v_unused_1612_ = lean_ctor_get(v_pos_1571_, 0);
lean_dec(v_unused_1612_);
v___x_1601_ = v_pos_1571_;
v_isShared_1602_ = v_isSharedCheck_1610_;
goto v_resetjp_1600_;
}
else
{
lean_dec(v_pos_1571_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1610_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; lean_object* v___x_1605_; 
v___x_1603_ = lean_nat_add(v_idx_1586_, v___x_1593_);
lean_dec(v_idx_1586_);
lean_inc(v___x_1603_);
lean_inc_ref(v_array_1585_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 1, v___x_1603_);
v___x_1605_ = v___x_1601_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_array_1585_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
uint8_t v___x_1606_; 
v___x_1606_ = lean_nat_dec_lt(v___x_1603_, v___x_1588_);
if (v___x_1606_ == 0)
{
lean_dec(v___x_1603_);
lean_dec_ref(v_array_1585_);
if (v___x_1589_ == 0)
{
lean_del_object(v___x_1531_);
v___y_1515_ = v___x_1605_;
v___y_1516_ = v___x_1587_;
v___y_1517_ = v___x_1594_;
goto v___jp_1514_;
}
else
{
lean_inc(v_maxPathSegments_1566_);
v___y_1546_ = v_maxPathSegments_1566_;
v___y_1547_ = v___x_1605_;
v___y_1548_ = v___x_1587_;
v___y_1549_ = v___x_1594_;
goto v___jp_1545_;
}
}
else
{
uint8_t v___x_1607_; uint8_t v___x_1608_; 
v___x_1607_ = lean_byte_array_fget(v_array_1585_, v___x_1603_);
lean_dec(v___x_1603_);
lean_dec_ref(v_array_1585_);
v___x_1608_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0(v___x_1607_);
if (v___x_1608_ == 0)
{
lean_del_object(v___x_1531_);
v___y_1515_ = v___x_1605_;
v___y_1516_ = v___x_1587_;
v___y_1517_ = v___x_1594_;
goto v___jp_1514_;
}
else
{
lean_inc(v_maxPathSegments_1566_);
v___y_1546_ = v_maxPathSegments_1566_;
v___y_1547_ = v___x_1605_;
v___y_1548_ = v___x_1587_;
v___y_1549_ = v___x_1594_;
goto v___jp_1545_;
}
}
}
}
}
}
else
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1619_; 
lean_inc(v_maxTotalPathLength_1567_);
lean_dec(v___x_1594_);
lean_dec_ref(v___x_1587_);
lean_del_object(v___x_1531_);
lean_dec_ref(v_config_1511_);
v___x_1613_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__4));
v___x_1614_ = l_Nat_reprFast(v_maxTotalPathLength_1567_);
v___x_1615_ = lean_string_append(v___x_1613_, v___x_1614_);
lean_dec_ref(v___x_1614_);
v___x_1616_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__5));
v___x_1617_ = lean_string_append(v___x_1615_, v___x_1616_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v___x_1617_);
v___x_1619_ = v___x_1580_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
lean_object* v___x_1621_; 
if (v_isShared_1575_ == 0)
{
lean_ctor_set_tag(v___x_1574_, 1);
lean_ctor_set(v___x_1574_, 1, v___x_1619_);
v___x_1621_ = v___x_1574_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_pos_1571_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
}
}
else
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1630_; 
lean_inc(v_maxTotalPathLength_1567_);
lean_dec(v___x_1583_);
lean_dec(v_val_1578_);
lean_del_object(v___x_1531_);
lean_dec(v_fst_1528_);
lean_dec_ref(v_config_1511_);
v___x_1624_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__4));
v___x_1625_ = l_Nat_reprFast(v_maxTotalPathLength_1567_);
v___x_1626_ = lean_string_append(v___x_1624_, v___x_1625_);
lean_dec_ref(v___x_1625_);
v___x_1627_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__5));
v___x_1628_ = lean_string_append(v___x_1626_, v___x_1627_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v___x_1628_);
v___x_1630_ = v___x_1580_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1632_; 
if (v_isShared_1575_ == 0)
{
lean_ctor_set_tag(v___x_1574_, 1);
lean_ctor_set(v___x_1574_, 1, v___x_1630_);
v___x_1632_ = v___x_1574_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_pos_1571_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v___x_1630_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
else
{
lean_object* v___x_1636_; lean_object* v___x_1638_; 
lean_dec(v___x_1577_);
lean_dec(v_res_1572_);
lean_del_object(v___x_1531_);
lean_dec(v_snd_1529_);
lean_dec(v_fst_1528_);
lean_dec_ref(v_config_1511_);
v___x_1636_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__7));
if (v_isShared_1575_ == 0)
{
lean_ctor_set_tag(v___x_1574_, 1);
lean_ctor_set(v___x_1574_, 1, v___x_1636_);
v___x_1638_ = v___x_1574_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_pos_1571_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v___x_1636_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
else
{
lean_object* v_pos_1641_; lean_object* v_err_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
lean_del_object(v___x_1531_);
lean_dec(v_snd_1529_);
lean_dec(v_fst_1528_);
lean_dec_ref(v_config_1511_);
v_pos_1641_ = lean_ctor_get(v___x_1570_, 0);
v_err_1642_ = lean_ctor_get(v___x_1570_, 1);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1570_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_err_1642_);
lean_inc(v_pos_1641_);
lean_dec(v___x_1570_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_pos_1641_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_err_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
else
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
lean_inc(v_maxPathSegments_1566_);
lean_del_object(v___x_1531_);
lean_dec(v_snd_1529_);
lean_dec(v_fst_1528_);
lean_dec_ref(v_config_1511_);
v___x_1650_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__2));
v___x_1651_ = l_Nat_reprFast(v_maxPathSegments_1566_);
v___x_1652_ = lean_string_append(v___x_1650_, v___x_1651_);
lean_dec_ref(v___x_1651_);
v___x_1653_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__3));
v___x_1654_ = lean_string_append(v___x_1652_, v___x_1653_);
v___x_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
v___x_1656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___y_1513_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
return v___x_1656_;
}
}
v___jp_1657_:
{
if (v___y_1658_ == 0)
{
if (v___x_1534_ == 0)
{
goto v___jp_1565_;
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
lean_del_object(v___x_1531_);
lean_dec_ref(v_config_1511_);
v___x_1659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1659_, 0, v_fst_1528_);
lean_ctor_set(v___x_1659_, 1, v_snd_1529_);
v___x_1660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___y_1513_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
return v___x_1660_;
}
}
else
{
goto v___jp_1565_;
}
}
v___jp_1661_:
{
if (v___y_1662_ == 0)
{
uint8_t v___x_1663_; uint8_t v___x_1664_; 
v___x_1663_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_1664_ = lean_uint8_dec_eq(v___x_1543_, v___x_1663_);
if (v___x_1664_ == 0)
{
v___y_1658_ = v___x_1664_;
goto v___jp_1657_;
}
else
{
v___y_1658_ = v___x_1534_;
goto v___jp_1657_;
}
}
else
{
v___y_1658_ = v___x_1534_;
goto v___jp_1657_;
}
}
v___jp_1665_:
{
if (v___y_1666_ == 0)
{
uint8_t v___x_1667_; uint8_t v___x_1668_; 
v___x_1667_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1668_ = lean_uint8_dec_eq(v___x_1543_, v___x_1667_);
if (v___x_1668_ == 0)
{
uint8_t v___x_1669_; uint8_t v___x_1670_; 
v___x_1669_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1670_ = lean_uint8_dec_eq(v___x_1543_, v___x_1669_);
v___y_1662_ = v___x_1670_;
goto v___jp_1661_;
}
else
{
v___y_1662_ = v___x_1668_;
goto v___jp_1661_;
}
}
else
{
v___y_1658_ = v___x_1534_;
goto v___jp_1657_;
}
}
v___jp_1671_:
{
if (v___y_1672_ == 0)
{
uint8_t v___x_1673_; uint8_t v___x_1674_; 
v___x_1673_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_1674_ = lean_uint8_dec_eq(v___x_1543_, v___x_1673_);
if (v___x_1674_ == 0)
{
uint8_t v___x_1675_; uint8_t v___x_1676_; 
v___x_1675_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_1676_ = lean_uint8_dec_eq(v___x_1543_, v___x_1675_);
if (v___x_1676_ == 0)
{
uint8_t v___x_1677_; uint8_t v___x_1678_; 
v___x_1677_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_1678_ = lean_uint8_dec_eq(v___x_1543_, v___x_1677_);
if (v___x_1678_ == 0)
{
uint8_t v___x_1679_; uint8_t v___x_1680_; 
v___x_1679_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_1680_ = lean_uint8_dec_eq(v___x_1543_, v___x_1679_);
if (v___x_1680_ == 0)
{
uint8_t v___x_1681_; uint8_t v___x_1682_; 
v___x_1681_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_1682_ = lean_uint8_dec_eq(v___x_1543_, v___x_1681_);
if (v___x_1682_ == 0)
{
uint8_t v___x_1683_; uint8_t v___x_1684_; 
v___x_1683_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0);
v___x_1684_ = lean_uint8_dec_eq(v___x_1543_, v___x_1683_);
if (v___x_1684_ == 0)
{
uint8_t v___x_1685_; uint8_t v___x_1686_; 
v___x_1685_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_1686_ = lean_uint8_dec_eq(v___x_1543_, v___x_1685_);
if (v___x_1686_ == 0)
{
uint8_t v___x_1687_; uint8_t v___x_1688_; 
v___x_1687_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_1688_ = lean_uint8_dec_eq(v___x_1543_, v___x_1687_);
if (v___x_1688_ == 0)
{
uint8_t v___x_1689_; uint8_t v___x_1690_; 
v___x_1689_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_1690_ = lean_uint8_dec_eq(v___x_1543_, v___x_1689_);
v___y_1666_ = v___x_1690_;
goto v___jp_1665_;
}
else
{
v___y_1666_ = v___x_1688_;
goto v___jp_1665_;
}
}
else
{
v___y_1666_ = v___x_1686_;
goto v___jp_1665_;
}
}
else
{
v___y_1666_ = v___x_1684_;
goto v___jp_1665_;
}
}
else
{
v___y_1666_ = v___x_1682_;
goto v___jp_1665_;
}
}
else
{
v___y_1666_ = v___x_1680_;
goto v___jp_1665_;
}
}
else
{
v___y_1666_ = v___x_1678_;
goto v___jp_1665_;
}
}
else
{
v___y_1666_ = v___x_1676_;
goto v___jp_1665_;
}
}
else
{
v___y_1666_ = v___x_1674_;
goto v___jp_1665_;
}
}
else
{
v___y_1658_ = v___x_1534_;
goto v___jp_1657_;
}
}
v___jp_1691_:
{
if (v___y_1692_ == 0)
{
uint8_t v___x_1693_; uint8_t v___x_1694_; 
v___x_1693_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_1694_ = lean_uint8_dec_eq(v___x_1543_, v___x_1693_);
if (v___x_1694_ == 0)
{
uint8_t v___x_1695_; uint8_t v___x_1696_; 
v___x_1695_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_1696_ = lean_uint8_dec_eq(v___x_1543_, v___x_1695_);
v___y_1672_ = v___x_1696_;
goto v___jp_1671_;
}
else
{
v___y_1672_ = v___x_1694_;
goto v___jp_1671_;
}
}
else
{
v___y_1658_ = v___x_1534_;
goto v___jp_1657_;
}
}
v___jp_1697_:
{
if (v___y_1698_ == 0)
{
uint8_t v___x_1699_; uint8_t v___x_1700_; 
v___x_1699_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_1700_ = lean_uint8_dec_eq(v___x_1543_, v___x_1699_);
if (v___x_1700_ == 0)
{
uint8_t v___x_1701_; uint8_t v___x_1702_; 
v___x_1701_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_1702_ = lean_uint8_dec_eq(v___x_1543_, v___x_1701_);
v___y_1692_ = v___x_1702_;
goto v___jp_1691_;
}
else
{
v___y_1692_ = v___x_1700_;
goto v___jp_1691_;
}
}
else
{
v___y_1658_ = v___x_1534_;
goto v___jp_1657_;
}
}
v___jp_1703_:
{
if (v___y_1704_ == 0)
{
uint8_t v___x_1705_; uint8_t v___x_1706_; 
v___x_1705_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1);
v___x_1706_ = lean_uint8_dec_eq(v___x_1543_, v___x_1705_);
if (v___x_1706_ == 0)
{
uint8_t v___x_1707_; uint8_t v___x_1708_; 
v___x_1707_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2);
v___x_1708_ = lean_uint8_dec_eq(v___x_1543_, v___x_1707_);
v___y_1698_ = v___x_1708_;
goto v___jp_1697_;
}
else
{
v___y_1698_ = v___x_1706_;
goto v___jp_1697_;
}
}
else
{
v___y_1658_ = v___x_1534_;
goto v___jp_1657_;
}
}
v___jp_1709_:
{
if (v___y_1710_ == 0)
{
uint8_t v___x_1711_; uint8_t v___x_1712_; 
v___x_1711_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_1712_ = lean_uint8_dec_le(v___x_1711_, v___x_1543_);
if (v___x_1712_ == 0)
{
v___y_1704_ = v___x_1712_;
goto v___jp_1703_;
}
else
{
uint8_t v___x_1713_; uint8_t v___x_1714_; 
v___x_1713_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_1714_ = lean_uint8_dec_le(v___x_1543_, v___x_1713_);
v___y_1704_ = v___x_1714_;
goto v___jp_1703_;
}
}
else
{
v___y_1658_ = v___x_1534_;
goto v___jp_1657_;
}
}
v___jp_1715_:
{
if (v___y_1716_ == 0)
{
uint8_t v___x_1717_; uint8_t v___x_1718_; 
v___x_1717_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_1718_ = lean_uint8_dec_le(v___x_1717_, v___x_1543_);
if (v___x_1718_ == 0)
{
v___y_1710_ = v___x_1718_;
goto v___jp_1709_;
}
else
{
uint8_t v___x_1719_; uint8_t v___x_1720_; 
v___x_1719_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_1720_ = lean_uint8_dec_le(v___x_1543_, v___x_1719_);
v___y_1710_ = v___x_1720_;
goto v___jp_1709_;
}
}
else
{
v___y_1658_ = v___x_1534_;
goto v___jp_1657_;
}
}
}
else
{
lean_object* v___x_1728_; 
lean_dec_ref(v_config_1511_);
if (v_isShared_1532_ == 0)
{
v___x_1728_ = v___x_1531_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_fst_1528_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_snd_1529_);
v___x_1728_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
lean_object* v___x_1729_; 
v___x_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___y_1513_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
return v___x_1729_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0(lean_object* v_config_1732_, lean_object* v_b_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v_array_1747_; lean_object* v_idx_1748_; lean_object* v_fst_1749_; lean_object* v_snd_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1952_; 
v_array_1747_ = lean_ctor_get(v___y_1734_, 0);
v_idx_1748_ = lean_ctor_get(v___y_1734_, 1);
v_fst_1749_ = lean_ctor_get(v_b_1733_, 0);
v_snd_1750_ = lean_ctor_get(v_b_1733_, 1);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_b_1733_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1752_ = v_b_1733_;
v_isShared_1753_ = v_isSharedCheck_1952_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_snd_1750_);
lean_inc(v_fst_1749_);
lean_dec(v_b_1733_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1952_;
goto v_resetjp_1751_;
}
v___jp_1735_:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___y_1737_);
lean_ctor_set(v___x_1739_, 1, v___y_1736_);
v___x_1740_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(v_config_1732_, v___x_1739_, v___y_1738_);
return v___x_1740_;
}
v___jp_1741_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___y_1743_);
lean_ctor_set(v___x_1745_, 1, v___y_1742_);
v___x_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___y_1744_);
lean_ctor_set(v___x_1746_, 1, v___x_1745_);
return v___x_1746_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1754_ = lean_byte_array_size(v_array_1747_);
v___x_1755_ = lean_nat_dec_lt(v_idx_1748_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1757_; 
lean_dec_ref(v_config_1732_);
if (v_isShared_1753_ == 0)
{
v___x_1757_ = v___x_1752_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_fst_1749_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_snd_1750_);
v___x_1757_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___y_1734_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
return v___x_1758_;
}
}
else
{
if (v___x_1755_ == 0)
{
lean_object* v___x_1761_; 
lean_dec_ref(v_config_1732_);
if (v_isShared_1753_ == 0)
{
v___x_1761_ = v___x_1752_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_fst_1749_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v_snd_1750_);
v___x_1761_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1762_; 
v___x_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___y_1734_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
return v___x_1762_;
}
}
else
{
uint8_t v___x_1764_; uint8_t v___x_1765_; 
v___x_1764_ = lean_byte_array_fget(v_array_1747_, v_idx_1748_);
v___x_1765_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0(v___x_1764_);
if (v___x_1765_ == 0)
{
lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; uint8_t v___y_1879_; uint8_t v___y_1883_; uint8_t v___y_1887_; uint8_t v___y_1893_; uint8_t v___y_1913_; uint8_t v___y_1919_; uint8_t v___y_1925_; uint8_t v___y_1931_; uint8_t v___y_1937_; uint8_t v___x_1942_; uint8_t v___x_1943_; 
v___x_1942_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_1943_ = lean_uint8_dec_eq(v___x_1764_, v___x_1942_);
if (v___x_1943_ == 0)
{
uint8_t v___x_1944_; uint8_t v___x_1945_; 
v___x_1944_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_1945_ = lean_uint8_dec_le(v___x_1944_, v___x_1764_);
if (v___x_1945_ == 0)
{
v___y_1937_ = v___x_1945_;
goto v___jp_1936_;
}
else
{
uint8_t v___x_1946_; uint8_t v___x_1947_; 
v___x_1946_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_1947_ = lean_uint8_dec_le(v___x_1764_, v___x_1946_);
v___y_1937_ = v___x_1947_;
goto v___jp_1936_;
}
}
else
{
v___y_1879_ = v___x_1943_;
goto v___jp_1878_;
}
v___jp_1766_:
{
lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1771_ = lean_array_get_size(v___y_1769_);
v___x_1772_ = lean_nat_dec_le(v___y_1768_, v___x_1771_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1776_; 
lean_dec(v___y_1768_);
v___x_1773_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1);
v___x_1774_ = lean_array_push(v___y_1769_, v___x_1773_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 1, v___y_1767_);
lean_ctor_set(v___x_1752_, 0, v___x_1774_);
v___x_1776_ = v___x_1752_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v___y_1767_);
v___x_1776_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v___x_1777_; 
v___x_1777_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(v_config_1732_, v___x_1776_, v___y_1770_);
return v___x_1777_;
}
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1767_);
lean_del_object(v___x_1752_);
lean_dec_ref(v_config_1732_);
v___x_1779_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__2));
v___x_1780_ = l_Nat_reprFast(v___y_1768_);
v___x_1781_ = lean_string_append(v___x_1779_, v___x_1780_);
lean_dec_ref(v___x_1780_);
v___x_1782_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__3));
v___x_1783_ = lean_string_append(v___x_1781_, v___x_1782_);
v___x_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
v___x_1785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___y_1770_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
return v___x_1785_;
}
}
v___jp_1786_:
{
lean_object* v_maxPathSegments_1787_; lean_object* v_maxTotalPathLength_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v_maxPathSegments_1787_ = lean_ctor_get(v_config_1732_, 6);
v_maxTotalPathLength_1788_ = lean_ctor_get(v_config_1732_, 7);
v___x_1789_ = lean_array_get_size(v_fst_1749_);
v___x_1790_ = lean_nat_dec_le(v_maxPathSegments_1787_, v___x_1789_);
if (v___x_1790_ == 0)
{
lean_object* v___x_1791_; 
v___x_1791_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1732_, v___y_1734_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_pos_1792_; lean_object* v_res_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1861_; 
v_pos_1792_ = lean_ctor_get(v___x_1791_, 0);
v_res_1793_ = lean_ctor_get(v___x_1791_, 1);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1795_ = v___x_1791_;
v_isShared_1796_ = v_isSharedCheck_1861_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_res_1793_);
lean_inc(v_pos_1792_);
lean_dec(v___x_1791_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1861_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
lean_inc(v_res_1793_);
v___x_1797_ = l_ByteSlice_toByteArray(v_res_1793_);
v___x_1798_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1797_);
if (lean_obj_tag(v___x_1798_) == 1)
{
lean_object* v_val_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1856_; 
v_val_1799_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1801_ = v___x_1798_;
v_isShared_1802_ = v_isSharedCheck_1856_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_val_1799_);
lean_dec(v___x_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1856_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v___x_1803_ = l_ByteSlice_size(v_res_1793_);
lean_dec(v_res_1793_);
v___x_1804_ = lean_nat_add(v_snd_1750_, v___x_1803_);
lean_dec(v___x_1803_);
lean_dec(v_snd_1750_);
v___x_1805_ = lean_nat_dec_lt(v_maxTotalPathLength_1788_, v___x_1804_);
if (v___x_1805_ == 0)
{
lean_object* v_array_1806_; lean_object* v_idx_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
v_array_1806_ = lean_ctor_get(v_pos_1792_, 0);
v_idx_1807_ = lean_ctor_get(v_pos_1792_, 1);
v___x_1808_ = lean_array_push(v_fst_1749_, v_val_1799_);
v___x_1809_ = lean_byte_array_size(v_array_1806_);
v___x_1810_ = lean_nat_dec_lt(v_idx_1807_, v___x_1809_);
if (v___x_1810_ == 0)
{
lean_del_object(v___x_1801_);
lean_del_object(v___x_1795_);
lean_del_object(v___x_1752_);
lean_dec_ref(v_config_1732_);
v___y_1742_ = v___x_1804_;
v___y_1743_ = v___x_1808_;
v___y_1744_ = v_pos_1792_;
goto v___jp_1741_;
}
else
{
uint8_t v___x_1811_; uint8_t v___x_1812_; uint8_t v___x_1813_; 
v___x_1811_ = lean_byte_array_fget(v_array_1806_, v_idx_1807_);
v___x_1812_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_1813_ = lean_uint8_dec_eq(v___x_1811_, v___x_1812_);
if (v___x_1813_ == 0)
{
lean_del_object(v___x_1801_);
lean_del_object(v___x_1795_);
lean_del_object(v___x_1752_);
lean_dec_ref(v_config_1732_);
v___y_1742_ = v___x_1804_;
v___y_1743_ = v___x_1808_;
v___y_1744_ = v_pos_1792_;
goto v___jp_1741_;
}
else
{
lean_object* v___x_1814_; lean_object* v___x_1815_; uint8_t v___x_1816_; 
v___x_1814_ = lean_unsigned_to_nat(1u);
v___x_1815_ = lean_nat_add(v___x_1804_, v___x_1814_);
lean_dec(v___x_1804_);
v___x_1816_ = lean_nat_dec_lt(v_maxTotalPathLength_1788_, v___x_1815_);
if (v___x_1816_ == 0)
{
lean_del_object(v___x_1801_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1819_; 
lean_dec(v___x_1815_);
lean_dec_ref(v___x_1808_);
lean_del_object(v___x_1752_);
lean_dec_ref(v_config_1732_);
v___x_1817_ = lean_box(0);
if (v_isShared_1796_ == 0)
{
lean_ctor_set_tag(v___x_1795_, 1);
lean_ctor_set(v___x_1795_, 1, v___x_1817_);
v___x_1819_ = v___x_1795_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_pos_1792_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
else
{
lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1831_; 
lean_inc(v_idx_1807_);
lean_inc_ref(v_array_1806_);
lean_del_object(v___x_1795_);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_pos_1792_);
if (v_isSharedCheck_1831_ == 0)
{
lean_object* v_unused_1832_; lean_object* v_unused_1833_; 
v_unused_1832_ = lean_ctor_get(v_pos_1792_, 1);
lean_dec(v_unused_1832_);
v_unused_1833_ = lean_ctor_get(v_pos_1792_, 0);
lean_dec(v_unused_1833_);
v___x_1822_ = v_pos_1792_;
v_isShared_1823_ = v_isSharedCheck_1831_;
goto v_resetjp_1821_;
}
else
{
lean_dec(v_pos_1792_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1831_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1824_ = lean_nat_add(v_idx_1807_, v___x_1814_);
lean_dec(v_idx_1807_);
lean_inc(v___x_1824_);
lean_inc_ref(v_array_1806_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 1, v___x_1824_);
v___x_1826_ = v___x_1822_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_array_1806_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
uint8_t v___x_1827_; 
v___x_1827_ = lean_nat_dec_lt(v___x_1824_, v___x_1809_);
if (v___x_1827_ == 0)
{
lean_dec(v___x_1824_);
lean_dec_ref(v_array_1806_);
if (v___x_1810_ == 0)
{
lean_del_object(v___x_1752_);
v___y_1736_ = v___x_1815_;
v___y_1737_ = v___x_1808_;
v___y_1738_ = v___x_1826_;
goto v___jp_1735_;
}
else
{
lean_inc(v_maxPathSegments_1787_);
v___y_1767_ = v___x_1815_;
v___y_1768_ = v_maxPathSegments_1787_;
v___y_1769_ = v___x_1808_;
v___y_1770_ = v___x_1826_;
goto v___jp_1766_;
}
}
else
{
uint8_t v___x_1828_; uint8_t v___x_1829_; 
v___x_1828_ = lean_byte_array_fget(v_array_1806_, v___x_1824_);
lean_dec(v___x_1824_);
lean_dec_ref(v_array_1806_);
v___x_1829_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0(v___x_1828_);
if (v___x_1829_ == 0)
{
lean_del_object(v___x_1752_);
v___y_1736_ = v___x_1815_;
v___y_1737_ = v___x_1808_;
v___y_1738_ = v___x_1826_;
goto v___jp_1735_;
}
else
{
lean_inc(v_maxPathSegments_1787_);
v___y_1767_ = v___x_1815_;
v___y_1768_ = v_maxPathSegments_1787_;
v___y_1769_ = v___x_1808_;
v___y_1770_ = v___x_1826_;
goto v___jp_1766_;
}
}
}
}
}
}
else
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
lean_inc(v_maxTotalPathLength_1788_);
lean_dec(v___x_1815_);
lean_dec_ref(v___x_1808_);
lean_del_object(v___x_1752_);
lean_dec_ref(v_config_1732_);
v___x_1834_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__4));
v___x_1835_ = l_Nat_reprFast(v_maxTotalPathLength_1788_);
v___x_1836_ = lean_string_append(v___x_1834_, v___x_1835_);
lean_dec_ref(v___x_1835_);
v___x_1837_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__5));
v___x_1838_ = lean_string_append(v___x_1836_, v___x_1837_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1838_);
v___x_1840_ = v___x_1801_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1842_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set_tag(v___x_1795_, 1);
lean_ctor_set(v___x_1795_, 1, v___x_1840_);
v___x_1842_ = v___x_1795_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_pos_1792_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
}
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1851_; 
lean_inc(v_maxTotalPathLength_1788_);
lean_dec(v___x_1804_);
lean_dec(v_val_1799_);
lean_del_object(v___x_1752_);
lean_dec(v_fst_1749_);
lean_dec_ref(v_config_1732_);
v___x_1845_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__4));
v___x_1846_ = l_Nat_reprFast(v_maxTotalPathLength_1788_);
v___x_1847_ = lean_string_append(v___x_1845_, v___x_1846_);
lean_dec_ref(v___x_1846_);
v___x_1848_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__5));
v___x_1849_ = lean_string_append(v___x_1847_, v___x_1848_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1849_);
v___x_1851_ = v___x_1801_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1853_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set_tag(v___x_1795_, 1);
lean_ctor_set(v___x_1795_, 1, v___x_1851_);
v___x_1853_ = v___x_1795_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_pos_1792_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1859_; 
lean_dec(v___x_1798_);
lean_dec(v_res_1793_);
lean_del_object(v___x_1752_);
lean_dec(v_snd_1750_);
lean_dec(v_fst_1749_);
lean_dec_ref(v_config_1732_);
v___x_1857_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__7));
if (v_isShared_1796_ == 0)
{
lean_ctor_set_tag(v___x_1795_, 1);
lean_ctor_set(v___x_1795_, 1, v___x_1857_);
v___x_1859_ = v___x_1795_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_pos_1792_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
else
{
lean_object* v_pos_1862_; lean_object* v_err_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_del_object(v___x_1752_);
lean_dec(v_snd_1750_);
lean_dec(v_fst_1749_);
lean_dec_ref(v_config_1732_);
v_pos_1862_ = lean_ctor_get(v___x_1791_, 0);
v_err_1863_ = lean_ctor_get(v___x_1791_, 1);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1791_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_err_1863_);
lean_inc(v_pos_1862_);
lean_dec(v___x_1791_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_pos_1862_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v_err_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
else
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
lean_inc(v_maxPathSegments_1787_);
lean_del_object(v___x_1752_);
lean_dec(v_snd_1750_);
lean_dec(v_fst_1749_);
lean_dec_ref(v_config_1732_);
v___x_1871_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__2));
v___x_1872_ = l_Nat_reprFast(v_maxPathSegments_1787_);
v___x_1873_ = lean_string_append(v___x_1871_, v___x_1872_);
lean_dec_ref(v___x_1872_);
v___x_1874_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__3));
v___x_1875_ = lean_string_append(v___x_1873_, v___x_1874_);
v___x_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
v___x_1877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___y_1734_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
return v___x_1877_;
}
}
v___jp_1878_:
{
if (v___y_1879_ == 0)
{
if (v___x_1755_ == 0)
{
goto v___jp_1786_;
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
lean_del_object(v___x_1752_);
lean_dec_ref(v_config_1732_);
v___x_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1880_, 0, v_fst_1749_);
lean_ctor_set(v___x_1880_, 1, v_snd_1750_);
v___x_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___y_1734_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
return v___x_1881_;
}
}
else
{
goto v___jp_1786_;
}
}
v___jp_1882_:
{
if (v___y_1883_ == 0)
{
uint8_t v___x_1884_; uint8_t v___x_1885_; 
v___x_1884_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_1885_ = lean_uint8_dec_eq(v___x_1764_, v___x_1884_);
if (v___x_1885_ == 0)
{
v___y_1879_ = v___x_1885_;
goto v___jp_1878_;
}
else
{
v___y_1879_ = v___x_1755_;
goto v___jp_1878_;
}
}
else
{
v___y_1879_ = v___x_1755_;
goto v___jp_1878_;
}
}
v___jp_1886_:
{
if (v___y_1887_ == 0)
{
uint8_t v___x_1888_; uint8_t v___x_1889_; 
v___x_1888_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1889_ = lean_uint8_dec_eq(v___x_1764_, v___x_1888_);
if (v___x_1889_ == 0)
{
uint8_t v___x_1890_; uint8_t v___x_1891_; 
v___x_1890_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1891_ = lean_uint8_dec_eq(v___x_1764_, v___x_1890_);
v___y_1883_ = v___x_1891_;
goto v___jp_1882_;
}
else
{
v___y_1883_ = v___x_1889_;
goto v___jp_1882_;
}
}
else
{
v___y_1879_ = v___x_1755_;
goto v___jp_1878_;
}
}
v___jp_1892_:
{
if (v___y_1893_ == 0)
{
uint8_t v___x_1894_; uint8_t v___x_1895_; 
v___x_1894_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_1895_ = lean_uint8_dec_eq(v___x_1764_, v___x_1894_);
if (v___x_1895_ == 0)
{
uint8_t v___x_1896_; uint8_t v___x_1897_; 
v___x_1896_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_1897_ = lean_uint8_dec_eq(v___x_1764_, v___x_1896_);
if (v___x_1897_ == 0)
{
uint8_t v___x_1898_; uint8_t v___x_1899_; 
v___x_1898_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_1899_ = lean_uint8_dec_eq(v___x_1764_, v___x_1898_);
if (v___x_1899_ == 0)
{
uint8_t v___x_1900_; uint8_t v___x_1901_; 
v___x_1900_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_1901_ = lean_uint8_dec_eq(v___x_1764_, v___x_1900_);
if (v___x_1901_ == 0)
{
uint8_t v___x_1902_; uint8_t v___x_1903_; 
v___x_1902_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_1903_ = lean_uint8_dec_eq(v___x_1764_, v___x_1902_);
if (v___x_1903_ == 0)
{
uint8_t v___x_1904_; uint8_t v___x_1905_; 
v___x_1904_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0);
v___x_1905_ = lean_uint8_dec_eq(v___x_1764_, v___x_1904_);
if (v___x_1905_ == 0)
{
uint8_t v___x_1906_; uint8_t v___x_1907_; 
v___x_1906_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_1907_ = lean_uint8_dec_eq(v___x_1764_, v___x_1906_);
if (v___x_1907_ == 0)
{
uint8_t v___x_1908_; uint8_t v___x_1909_; 
v___x_1908_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_1909_ = lean_uint8_dec_eq(v___x_1764_, v___x_1908_);
if (v___x_1909_ == 0)
{
uint8_t v___x_1910_; uint8_t v___x_1911_; 
v___x_1910_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_1911_ = lean_uint8_dec_eq(v___x_1764_, v___x_1910_);
v___y_1887_ = v___x_1911_;
goto v___jp_1886_;
}
else
{
v___y_1887_ = v___x_1909_;
goto v___jp_1886_;
}
}
else
{
v___y_1887_ = v___x_1907_;
goto v___jp_1886_;
}
}
else
{
v___y_1887_ = v___x_1905_;
goto v___jp_1886_;
}
}
else
{
v___y_1887_ = v___x_1903_;
goto v___jp_1886_;
}
}
else
{
v___y_1887_ = v___x_1901_;
goto v___jp_1886_;
}
}
else
{
v___y_1887_ = v___x_1899_;
goto v___jp_1886_;
}
}
else
{
v___y_1887_ = v___x_1897_;
goto v___jp_1886_;
}
}
else
{
v___y_1887_ = v___x_1895_;
goto v___jp_1886_;
}
}
else
{
v___y_1879_ = v___x_1755_;
goto v___jp_1878_;
}
}
v___jp_1912_:
{
if (v___y_1913_ == 0)
{
uint8_t v___x_1914_; uint8_t v___x_1915_; 
v___x_1914_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_1915_ = lean_uint8_dec_eq(v___x_1764_, v___x_1914_);
if (v___x_1915_ == 0)
{
uint8_t v___x_1916_; uint8_t v___x_1917_; 
v___x_1916_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_1917_ = lean_uint8_dec_eq(v___x_1764_, v___x_1916_);
v___y_1893_ = v___x_1917_;
goto v___jp_1892_;
}
else
{
v___y_1893_ = v___x_1915_;
goto v___jp_1892_;
}
}
else
{
v___y_1879_ = v___x_1755_;
goto v___jp_1878_;
}
}
v___jp_1918_:
{
if (v___y_1919_ == 0)
{
uint8_t v___x_1920_; uint8_t v___x_1921_; 
v___x_1920_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_1921_ = lean_uint8_dec_eq(v___x_1764_, v___x_1920_);
if (v___x_1921_ == 0)
{
uint8_t v___x_1922_; uint8_t v___x_1923_; 
v___x_1922_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_1923_ = lean_uint8_dec_eq(v___x_1764_, v___x_1922_);
v___y_1913_ = v___x_1923_;
goto v___jp_1912_;
}
else
{
v___y_1913_ = v___x_1921_;
goto v___jp_1912_;
}
}
else
{
v___y_1879_ = v___x_1755_;
goto v___jp_1878_;
}
}
v___jp_1924_:
{
if (v___y_1925_ == 0)
{
uint8_t v___x_1926_; uint8_t v___x_1927_; 
v___x_1926_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1);
v___x_1927_ = lean_uint8_dec_eq(v___x_1764_, v___x_1926_);
if (v___x_1927_ == 0)
{
uint8_t v___x_1928_; uint8_t v___x_1929_; 
v___x_1928_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2);
v___x_1929_ = lean_uint8_dec_eq(v___x_1764_, v___x_1928_);
v___y_1919_ = v___x_1929_;
goto v___jp_1918_;
}
else
{
v___y_1919_ = v___x_1927_;
goto v___jp_1918_;
}
}
else
{
v___y_1879_ = v___x_1755_;
goto v___jp_1878_;
}
}
v___jp_1930_:
{
if (v___y_1931_ == 0)
{
uint8_t v___x_1932_; uint8_t v___x_1933_; 
v___x_1932_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_1933_ = lean_uint8_dec_le(v___x_1932_, v___x_1764_);
if (v___x_1933_ == 0)
{
v___y_1925_ = v___x_1933_;
goto v___jp_1924_;
}
else
{
uint8_t v___x_1934_; uint8_t v___x_1935_; 
v___x_1934_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_1935_ = lean_uint8_dec_le(v___x_1764_, v___x_1934_);
v___y_1925_ = v___x_1935_;
goto v___jp_1924_;
}
}
else
{
v___y_1879_ = v___x_1755_;
goto v___jp_1878_;
}
}
v___jp_1936_:
{
if (v___y_1937_ == 0)
{
uint8_t v___x_1938_; uint8_t v___x_1939_; 
v___x_1938_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_1939_ = lean_uint8_dec_le(v___x_1938_, v___x_1764_);
if (v___x_1939_ == 0)
{
v___y_1931_ = v___x_1939_;
goto v___jp_1930_;
}
else
{
uint8_t v___x_1940_; uint8_t v___x_1941_; 
v___x_1940_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_1941_ = lean_uint8_dec_le(v___x_1764_, v___x_1940_);
v___y_1931_ = v___x_1941_;
goto v___jp_1930_;
}
}
else
{
v___y_1879_ = v___x_1755_;
goto v___jp_1878_;
}
}
}
else
{
lean_object* v___x_1949_; 
lean_dec_ref(v_config_1732_);
if (v_isShared_1753_ == 0)
{
v___x_1949_ = v___x_1752_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_fst_1749_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_snd_1750_);
v___x_1949_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
lean_object* v___x_1950_; 
v___x_1950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___y_1734_);
lean_ctor_set(v___x_1950_, 1, v___x_1949_);
return v___x_1950_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath(lean_object* v_config_1964_, uint8_t v_forceAbsolute_1965_, uint8_t v_allowEmpty_1966_, lean_object* v_a_1967_){
_start:
{
lean_object* v___y_1969_; lean_object* v___y_1973_; lean_object* v_array_1976_; lean_object* v_idx_1977_; uint8_t v_isAbsolute_1978_; lean_object* v___x_1979_; lean_object* v_segments_1980_; uint8_t v_isAbsolute_1982_; lean_object* v_totalLength_1983_; lean_object* v___y_1984_; lean_object* v___y_2008_; uint8_t v___y_2012_; lean_object* v_pos_2013_; uint8_t v_res_2014_; uint8_t v___y_2016_; lean_object* v_pos_2017_; lean_object* v___y_2023_; uint8_t v___y_2024_; uint8_t v___y_2046_; lean_object* v_pos_2047_; uint8_t v_res_2048_; lean_object* v_pos_2050_; lean_object* v_array_2051_; lean_object* v_idx_2052_; uint8_t v_res_2053_; uint8_t v___y_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v_array_1976_ = lean_ctor_get(v_a_1967_, 0);
lean_inc_ref(v_array_1976_);
v_idx_1977_ = lean_ctor_get(v_a_1967_, 1);
lean_inc(v_idx_1977_);
v_isAbsolute_1978_ = 0;
v___x_1979_ = lean_unsigned_to_nat(0u);
v_segments_1980_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__4));
v___x_2059_ = lean_byte_array_size(v_array_1976_);
v___x_2060_ = lean_nat_dec_lt(v_idx_1977_, v___x_2059_);
if (v___x_2060_ == 0)
{
v_pos_2050_ = v_a_1967_;
v_array_2051_ = v_array_1976_;
v_idx_2052_ = v_idx_1977_;
v_res_2053_ = v_isAbsolute_1978_;
goto v___jp_2049_;
}
else
{
uint8_t v___x_2061_; uint8_t v___y_2063_; uint8_t v___y_2069_; uint8_t v___y_2075_; uint8_t v___y_2095_; uint8_t v___y_2101_; uint8_t v___y_2107_; uint8_t v___y_2113_; uint8_t v___y_2119_; uint8_t v___x_2124_; uint8_t v___x_2125_; 
v___x_2061_ = lean_byte_array_fget(v_array_1976_, v_idx_1977_);
v___x_2124_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_2125_ = lean_uint8_dec_le(v___x_2124_, v___x_2061_);
if (v___x_2125_ == 0)
{
v___y_2119_ = v___x_2125_;
goto v___jp_2118_;
}
else
{
uint8_t v___x_2126_; uint8_t v___x_2127_; 
v___x_2126_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_2127_ = lean_uint8_dec_le(v___x_2061_, v___x_2126_);
v___y_2119_ = v___x_2127_;
goto v___jp_2118_;
}
v___jp_2062_:
{
if (v___y_2063_ == 0)
{
uint8_t v___x_2064_; uint8_t v___x_2065_; 
v___x_2064_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_2065_ = lean_uint8_dec_eq(v___x_2061_, v___x_2064_);
if (v___x_2065_ == 0)
{
uint8_t v___x_2066_; uint8_t v___x_2067_; 
v___x_2066_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2067_ = lean_uint8_dec_eq(v___x_2061_, v___x_2066_);
v___y_2058_ = v___x_2067_;
goto v___jp_2057_;
}
else
{
v___y_2058_ = v___x_2065_;
goto v___jp_2057_;
}
}
else
{
v___y_2058_ = v___x_2060_;
goto v___jp_2057_;
}
}
v___jp_2068_:
{
if (v___y_2069_ == 0)
{
uint8_t v___x_2070_; uint8_t v___x_2071_; 
v___x_2070_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_2071_ = lean_uint8_dec_eq(v___x_2061_, v___x_2070_);
if (v___x_2071_ == 0)
{
uint8_t v___x_2072_; uint8_t v___x_2073_; 
v___x_2072_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_2073_ = lean_uint8_dec_eq(v___x_2061_, v___x_2072_);
v___y_2063_ = v___x_2073_;
goto v___jp_2062_;
}
else
{
v___y_2063_ = v___x_2071_;
goto v___jp_2062_;
}
}
else
{
v___y_2058_ = v___x_2060_;
goto v___jp_2057_;
}
}
v___jp_2074_:
{
if (v___y_2075_ == 0)
{
uint8_t v___x_2076_; uint8_t v___x_2077_; 
v___x_2076_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_2077_ = lean_uint8_dec_eq(v___x_2061_, v___x_2076_);
if (v___x_2077_ == 0)
{
uint8_t v___x_2078_; uint8_t v___x_2079_; 
v___x_2078_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_2079_ = lean_uint8_dec_eq(v___x_2061_, v___x_2078_);
if (v___x_2079_ == 0)
{
uint8_t v___x_2080_; uint8_t v___x_2081_; 
v___x_2080_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_2081_ = lean_uint8_dec_eq(v___x_2061_, v___x_2080_);
if (v___x_2081_ == 0)
{
uint8_t v___x_2082_; uint8_t v___x_2083_; 
v___x_2082_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_2083_ = lean_uint8_dec_eq(v___x_2061_, v___x_2082_);
if (v___x_2083_ == 0)
{
uint8_t v___x_2084_; uint8_t v___x_2085_; 
v___x_2084_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_2085_ = lean_uint8_dec_eq(v___x_2061_, v___x_2084_);
if (v___x_2085_ == 0)
{
uint8_t v___x_2086_; uint8_t v___x_2087_; 
v___x_2086_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0);
v___x_2087_ = lean_uint8_dec_eq(v___x_2061_, v___x_2086_);
if (v___x_2087_ == 0)
{
uint8_t v___x_2088_; uint8_t v___x_2089_; 
v___x_2088_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_2089_ = lean_uint8_dec_eq(v___x_2061_, v___x_2088_);
if (v___x_2089_ == 0)
{
uint8_t v___x_2090_; uint8_t v___x_2091_; 
v___x_2090_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_2091_ = lean_uint8_dec_eq(v___x_2061_, v___x_2090_);
if (v___x_2091_ == 0)
{
uint8_t v___x_2092_; uint8_t v___x_2093_; 
v___x_2092_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_2093_ = lean_uint8_dec_eq(v___x_2061_, v___x_2092_);
v___y_2069_ = v___x_2093_;
goto v___jp_2068_;
}
else
{
v___y_2069_ = v___x_2091_;
goto v___jp_2068_;
}
}
else
{
v___y_2069_ = v___x_2089_;
goto v___jp_2068_;
}
}
else
{
v___y_2069_ = v___x_2087_;
goto v___jp_2068_;
}
}
else
{
v___y_2069_ = v___x_2085_;
goto v___jp_2068_;
}
}
else
{
v___y_2069_ = v___x_2083_;
goto v___jp_2068_;
}
}
else
{
v___y_2069_ = v___x_2081_;
goto v___jp_2068_;
}
}
else
{
v___y_2069_ = v___x_2079_;
goto v___jp_2068_;
}
}
else
{
v___y_2069_ = v___x_2077_;
goto v___jp_2068_;
}
}
else
{
v___y_2058_ = v___x_2060_;
goto v___jp_2057_;
}
}
v___jp_2094_:
{
if (v___y_2095_ == 0)
{
uint8_t v___x_2096_; uint8_t v___x_2097_; 
v___x_2096_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_2097_ = lean_uint8_dec_eq(v___x_2061_, v___x_2096_);
if (v___x_2097_ == 0)
{
uint8_t v___x_2098_; uint8_t v___x_2099_; 
v___x_2098_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_2099_ = lean_uint8_dec_eq(v___x_2061_, v___x_2098_);
v___y_2075_ = v___x_2099_;
goto v___jp_2074_;
}
else
{
v___y_2075_ = v___x_2097_;
goto v___jp_2074_;
}
}
else
{
v___y_2058_ = v___x_2060_;
goto v___jp_2057_;
}
}
v___jp_2100_:
{
if (v___y_2101_ == 0)
{
uint8_t v___x_2102_; uint8_t v___x_2103_; 
v___x_2102_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_2103_ = lean_uint8_dec_eq(v___x_2061_, v___x_2102_);
if (v___x_2103_ == 0)
{
uint8_t v___x_2104_; uint8_t v___x_2105_; 
v___x_2104_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_2105_ = lean_uint8_dec_eq(v___x_2061_, v___x_2104_);
v___y_2095_ = v___x_2105_;
goto v___jp_2094_;
}
else
{
v___y_2095_ = v___x_2103_;
goto v___jp_2094_;
}
}
else
{
v___y_2058_ = v___x_2060_;
goto v___jp_2057_;
}
}
v___jp_2106_:
{
if (v___y_2107_ == 0)
{
uint8_t v___x_2108_; uint8_t v___x_2109_; 
v___x_2108_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1);
v___x_2109_ = lean_uint8_dec_eq(v___x_2061_, v___x_2108_);
if (v___x_2109_ == 0)
{
uint8_t v___x_2110_; uint8_t v___x_2111_; 
v___x_2110_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2);
v___x_2111_ = lean_uint8_dec_eq(v___x_2061_, v___x_2110_);
v___y_2101_ = v___x_2111_;
goto v___jp_2100_;
}
else
{
v___y_2101_ = v___x_2109_;
goto v___jp_2100_;
}
}
else
{
v___y_2058_ = v___x_2060_;
goto v___jp_2057_;
}
}
v___jp_2112_:
{
if (v___y_2113_ == 0)
{
uint8_t v___x_2114_; uint8_t v___x_2115_; 
v___x_2114_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_2115_ = lean_uint8_dec_le(v___x_2114_, v___x_2061_);
if (v___x_2115_ == 0)
{
v___y_2107_ = v___x_2115_;
goto v___jp_2106_;
}
else
{
uint8_t v___x_2116_; uint8_t v___x_2117_; 
v___x_2116_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_2117_ = lean_uint8_dec_le(v___x_2061_, v___x_2116_);
v___y_2107_ = v___x_2117_;
goto v___jp_2106_;
}
}
else
{
v___y_2058_ = v___x_2060_;
goto v___jp_2057_;
}
}
v___jp_2118_:
{
if (v___y_2119_ == 0)
{
uint8_t v___x_2120_; uint8_t v___x_2121_; 
v___x_2120_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_2121_ = lean_uint8_dec_le(v___x_2120_, v___x_2061_);
if (v___x_2121_ == 0)
{
v___y_2113_ = v___x_2121_;
goto v___jp_2112_;
}
else
{
uint8_t v___x_2122_; uint8_t v___x_2123_; 
v___x_2122_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_2123_ = lean_uint8_dec_le(v___x_2061_, v___x_2122_);
v___y_2113_ = v___x_2123_;
goto v___jp_2112_;
}
}
else
{
v___y_2058_ = v___x_2060_;
goto v___jp_2057_;
}
}
}
v___jp_1968_:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__1));
v___x_1971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___y_1969_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
return v___x_1971_;
}
v___jp_1972_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__3));
v___x_1975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___y_1973_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
return v___x_1975_;
}
v___jp_1981_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1985_, 0, v_segments_1980_);
lean_ctor_set(v___x_1985_, 1, v_totalLength_1983_);
v___x_1986_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0(v_config_1964_, v___x_1985_, v___y_1984_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_res_1987_; lean_object* v_pos_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1997_; 
v_res_1987_ = lean_ctor_get(v___x_1986_, 1);
v_pos_1988_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1990_ = v___x_1986_;
v_isShared_1991_ = v_isSharedCheck_1997_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_res_1987_);
lean_inc(v_pos_1988_);
lean_dec(v___x_1986_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1997_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v_fst_1992_; lean_object* v___x_1993_; lean_object* v___x_1995_; 
v_fst_1992_ = lean_ctor_get(v_res_1987_, 0);
lean_inc(v_fst_1992_);
lean_dec(v_res_1987_);
v___x_1993_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1993_, 0, v_fst_1992_);
lean_ctor_set_uint8(v___x_1993_, sizeof(void*)*1, v_isAbsolute_1982_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 1, v___x_1993_);
v___x_1995_ = v___x_1990_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_pos_1988_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
else
{
lean_object* v_pos_1998_; lean_object* v_err_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
v_pos_1998_ = lean_ctor_get(v___x_1986_, 0);
v_err_1999_ = lean_ctor_get(v___x_1986_, 1);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1986_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_err_1999_);
lean_inc(v_pos_1998_);
lean_dec(v___x_1986_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_pos_1998_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_err_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
v___jp_2007_:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__5));
v___x_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___y_2008_);
lean_ctor_set(v___x_2010_, 1, v___x_2009_);
return v___x_2010_;
}
v___jp_2011_:
{
if (v_allowEmpty_1966_ == 0)
{
v___y_1969_ = v_pos_2013_;
goto v___jp_1968_;
}
else
{
if (v_res_2014_ == 0)
{
if (v___y_2012_ == 0)
{
v___y_2008_ = v_pos_2013_;
goto v___jp_2007_;
}
else
{
v___y_1969_ = v_pos_2013_;
goto v___jp_1968_;
}
}
else
{
v___y_2008_ = v_pos_2013_;
goto v___jp_2007_;
}
}
}
v___jp_2015_:
{
if (v_forceAbsolute_1965_ == 0)
{
v_isAbsolute_1982_ = v_isAbsolute_1978_;
v_totalLength_1983_ = v___x_1979_;
v___y_1984_ = v_pos_2017_;
goto v___jp_1981_;
}
else
{
lean_object* v_array_2018_; lean_object* v_idx_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; 
lean_dec_ref(v_config_1964_);
v_array_2018_ = lean_ctor_get(v_pos_2017_, 0);
v_idx_2019_ = lean_ctor_get(v_pos_2017_, 1);
v___x_2020_ = lean_byte_array_size(v_array_2018_);
v___x_2021_ = lean_nat_dec_lt(v_idx_2019_, v___x_2020_);
if (v___x_2021_ == 0)
{
v___y_2012_ = v___y_2016_;
v_pos_2013_ = v_pos_2017_;
v_res_2014_ = v_forceAbsolute_1965_;
goto v___jp_2011_;
}
else
{
v___y_2012_ = v___y_2016_;
v_pos_2013_ = v_pos_2017_;
v_res_2014_ = v_isAbsolute_1978_;
goto v___jp_2011_;
}
}
}
v___jp_2022_:
{
lean_object* v_array_2025_; lean_object* v_idx_2026_; lean_object* v___x_2027_; uint8_t v___x_2028_; 
v_array_2025_ = lean_ctor_get(v___y_2023_, 0);
v_idx_2026_ = lean_ctor_get(v___y_2023_, 1);
v___x_2027_ = lean_byte_array_size(v_array_2025_);
v___x_2028_ = lean_nat_dec_lt(v_idx_2026_, v___x_2027_);
if (v___x_2028_ == 0)
{
v___y_2016_ = v___y_2024_;
v_pos_2017_ = v___y_2023_;
goto v___jp_2015_;
}
else
{
uint8_t v___x_2029_; uint8_t v___x_2030_; uint8_t v___x_2031_; 
v___x_2029_ = lean_byte_array_fget(v_array_2025_, v_idx_2026_);
v___x_2030_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2031_ = lean_uint8_dec_eq(v___x_2029_, v___x_2030_);
if (v___x_2031_ == 0)
{
v___y_2016_ = v___y_2024_;
v_pos_2017_ = v___y_2023_;
goto v___jp_2015_;
}
else
{
if (v___x_2028_ == 0)
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
lean_dec_ref(v_config_1964_);
v___x_2032_ = lean_box(0);
v___x_2033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___y_2023_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
return v___x_2033_;
}
else
{
lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2042_; 
lean_inc(v_idx_2026_);
lean_inc_ref(v_array_2025_);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___y_2023_);
if (v_isSharedCheck_2042_ == 0)
{
lean_object* v_unused_2043_; lean_object* v_unused_2044_; 
v_unused_2043_ = lean_ctor_get(v___y_2023_, 1);
lean_dec(v_unused_2043_);
v_unused_2044_ = lean_ctor_get(v___y_2023_, 0);
lean_dec(v_unused_2044_);
v___x_2035_ = v___y_2023_;
v_isShared_2036_ = v_isSharedCheck_2042_;
goto v_resetjp_2034_;
}
else
{
lean_dec(v___y_2023_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2042_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2037_ = lean_unsigned_to_nat(1u);
v___x_2038_ = lean_nat_add(v_idx_2026_, v___x_2037_);
lean_dec(v_idx_2026_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 1, v___x_2038_);
v___x_2040_ = v___x_2035_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_array_2025_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
v_isAbsolute_1982_ = v___x_2028_;
v_totalLength_1983_ = v___x_2037_;
v___y_1984_ = v___x_2040_;
goto v___jp_1981_;
}
}
}
}
}
}
v___jp_2045_:
{
if (v_allowEmpty_1966_ == 0)
{
if (v_res_2048_ == 0)
{
if (v___y_2046_ == 0)
{
lean_dec_ref(v_config_1964_);
v___y_1973_ = v_pos_2047_;
goto v___jp_1972_;
}
else
{
v___y_2023_ = v_pos_2047_;
v___y_2024_ = v___y_2046_;
goto v___jp_2022_;
}
}
else
{
lean_dec_ref(v_config_1964_);
v___y_1973_ = v_pos_2047_;
goto v___jp_1972_;
}
}
else
{
v___y_2023_ = v_pos_2047_;
v___y_2024_ = v___y_2046_;
goto v___jp_2022_;
}
}
v___jp_2049_:
{
lean_object* v___x_2054_; uint8_t v___x_2055_; 
v___x_2054_ = lean_byte_array_size(v_array_2051_);
lean_dec_ref(v_array_2051_);
v___x_2055_ = lean_nat_dec_lt(v_idx_2052_, v___x_2054_);
lean_dec(v_idx_2052_);
if (v___x_2055_ == 0)
{
uint8_t v___x_2056_; 
v___x_2056_ = 1;
v___y_2046_ = v_res_2053_;
v_pos_2047_ = v_pos_2050_;
v_res_2048_ = v___x_2056_;
goto v___jp_2045_;
}
else
{
v___y_2046_ = v_res_2053_;
v_pos_2047_ = v_pos_2050_;
v_res_2048_ = v_isAbsolute_1978_;
goto v___jp_2045_;
}
}
v___jp_2057_:
{
if (v___y_2058_ == 0)
{
v_pos_2050_ = v_a_1967_;
v_array_2051_ = v_array_1976_;
v_idx_2052_ = v_idx_1977_;
v_res_2053_ = v_isAbsolute_1978_;
goto v___jp_2049_;
}
else
{
v_pos_2050_ = v_a_1967_;
v_array_2051_ = v_array_1976_;
v_idx_2052_ = v_idx_1977_;
v_res_2053_ = v___y_2058_;
goto v___jp_2049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath___boxed(lean_object* v_config_2128_, lean_object* v_forceAbsolute_2129_, lean_object* v_allowEmpty_2130_, lean_object* v_a_2131_){
_start:
{
uint8_t v_forceAbsolute_boxed_2132_; uint8_t v_allowEmpty_boxed_2133_; lean_object* v_res_2134_; 
v_forceAbsolute_boxed_2132_ = lean_unbox(v_forceAbsolute_2129_);
v_allowEmpty_boxed_2133_ = lean_unbox(v_allowEmpty_2130_);
v_res_2134_ = l_Std_Http_URI_Parser_parsePath(v_config_2128_, v_forceAbsolute_boxed_2132_, v_allowEmpty_boxed_2133_, v_a_2131_);
return v_res_2134_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(uint8_t v_c_2135_){
_start:
{
uint8_t v___y_2137_; uint8_t v___y_2141_; uint8_t v___y_2147_; uint8_t v___y_2153_; uint8_t v___y_2173_; uint8_t v___y_2179_; uint8_t v___y_2185_; uint8_t v___y_2191_; uint8_t v___y_2197_; uint8_t v___x_2202_; uint8_t v___x_2203_; 
v___x_2202_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_2203_ = lean_uint8_dec_le(v___x_2202_, v_c_2135_);
if (v___x_2203_ == 0)
{
v___y_2197_ = v___x_2203_;
goto v___jp_2196_;
}
else
{
uint8_t v___x_2204_; uint8_t v___x_2205_; 
v___x_2204_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_2205_ = lean_uint8_dec_le(v_c_2135_, v___x_2204_);
v___y_2197_ = v___x_2205_;
goto v___jp_2196_;
}
v___jp_2136_:
{
if (v___y_2137_ == 0)
{
uint8_t v___x_2138_; uint8_t v___x_2139_; 
v___x_2138_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_2139_ = lean_uint8_dec_eq(v_c_2135_, v___x_2138_);
if (v___x_2139_ == 0)
{
return v___y_2137_;
}
else
{
return v___x_2139_;
}
}
else
{
return v___y_2137_;
}
}
v___jp_2140_:
{
if (v___y_2141_ == 0)
{
uint8_t v___x_2142_; uint8_t v___x_2143_; 
v___x_2142_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2143_ = lean_uint8_dec_eq(v_c_2135_, v___x_2142_);
if (v___x_2143_ == 0)
{
uint8_t v___x_2144_; uint8_t v___x_2145_; 
v___x_2144_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_2145_ = lean_uint8_dec_eq(v_c_2135_, v___x_2144_);
v___y_2137_ = v___x_2145_;
goto v___jp_2136_;
}
else
{
v___y_2137_ = v___x_2143_;
goto v___jp_2136_;
}
}
else
{
return v___y_2141_;
}
}
v___jp_2146_:
{
if (v___y_2147_ == 0)
{
uint8_t v___x_2148_; uint8_t v___x_2149_; 
v___x_2148_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_2149_ = lean_uint8_dec_eq(v_c_2135_, v___x_2148_);
if (v___x_2149_ == 0)
{
uint8_t v___x_2150_; uint8_t v___x_2151_; 
v___x_2150_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_2151_ = lean_uint8_dec_eq(v_c_2135_, v___x_2150_);
v___y_2141_ = v___x_2151_;
goto v___jp_2140_;
}
else
{
v___y_2141_ = v___x_2149_;
goto v___jp_2140_;
}
}
else
{
return v___y_2147_;
}
}
v___jp_2152_:
{
if (v___y_2153_ == 0)
{
uint8_t v___x_2154_; uint8_t v___x_2155_; 
v___x_2154_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_2155_ = lean_uint8_dec_eq(v_c_2135_, v___x_2154_);
if (v___x_2155_ == 0)
{
uint8_t v___x_2156_; uint8_t v___x_2157_; 
v___x_2156_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_2157_ = lean_uint8_dec_eq(v_c_2135_, v___x_2156_);
if (v___x_2157_ == 0)
{
uint8_t v___x_2158_; uint8_t v___x_2159_; 
v___x_2158_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_2159_ = lean_uint8_dec_eq(v_c_2135_, v___x_2158_);
if (v___x_2159_ == 0)
{
uint8_t v___x_2160_; uint8_t v___x_2161_; 
v___x_2160_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_2161_ = lean_uint8_dec_eq(v_c_2135_, v___x_2160_);
if (v___x_2161_ == 0)
{
uint8_t v___x_2162_; uint8_t v___x_2163_; 
v___x_2162_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_2163_ = lean_uint8_dec_eq(v_c_2135_, v___x_2162_);
if (v___x_2163_ == 0)
{
uint8_t v___x_2164_; uint8_t v___x_2165_; 
v___x_2164_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__0);
v___x_2165_ = lean_uint8_dec_eq(v_c_2135_, v___x_2164_);
if (v___x_2165_ == 0)
{
uint8_t v___x_2166_; uint8_t v___x_2167_; 
v___x_2166_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_2167_ = lean_uint8_dec_eq(v_c_2135_, v___x_2166_);
if (v___x_2167_ == 0)
{
uint8_t v___x_2168_; uint8_t v___x_2169_; 
v___x_2168_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_2169_ = lean_uint8_dec_eq(v_c_2135_, v___x_2168_);
if (v___x_2169_ == 0)
{
uint8_t v___x_2170_; uint8_t v___x_2171_; 
v___x_2170_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_2171_ = lean_uint8_dec_eq(v_c_2135_, v___x_2170_);
v___y_2147_ = v___x_2171_;
goto v___jp_2146_;
}
else
{
v___y_2147_ = v___x_2169_;
goto v___jp_2146_;
}
}
else
{
v___y_2147_ = v___x_2167_;
goto v___jp_2146_;
}
}
else
{
v___y_2147_ = v___x_2165_;
goto v___jp_2146_;
}
}
else
{
v___y_2147_ = v___x_2163_;
goto v___jp_2146_;
}
}
else
{
v___y_2147_ = v___x_2161_;
goto v___jp_2146_;
}
}
else
{
v___y_2147_ = v___x_2159_;
goto v___jp_2146_;
}
}
else
{
v___y_2147_ = v___x_2157_;
goto v___jp_2146_;
}
}
else
{
v___y_2147_ = v___x_2155_;
goto v___jp_2146_;
}
}
else
{
return v___y_2153_;
}
}
v___jp_2172_:
{
if (v___y_2173_ == 0)
{
uint8_t v___x_2174_; uint8_t v___x_2175_; 
v___x_2174_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_2175_ = lean_uint8_dec_eq(v_c_2135_, v___x_2174_);
if (v___x_2175_ == 0)
{
uint8_t v___x_2176_; uint8_t v___x_2177_; 
v___x_2176_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_2177_ = lean_uint8_dec_eq(v_c_2135_, v___x_2176_);
v___y_2153_ = v___x_2177_;
goto v___jp_2152_;
}
else
{
v___y_2153_ = v___x_2175_;
goto v___jp_2152_;
}
}
else
{
return v___y_2173_;
}
}
v___jp_2178_:
{
if (v___y_2179_ == 0)
{
uint8_t v___x_2180_; uint8_t v___x_2181_; 
v___x_2180_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_2181_ = lean_uint8_dec_eq(v_c_2135_, v___x_2180_);
if (v___x_2181_ == 0)
{
uint8_t v___x_2182_; uint8_t v___x_2183_; 
v___x_2182_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_2183_ = lean_uint8_dec_eq(v_c_2135_, v___x_2182_);
v___y_2173_ = v___x_2183_;
goto v___jp_2172_;
}
else
{
v___y_2173_ = v___x_2181_;
goto v___jp_2172_;
}
}
else
{
return v___y_2179_;
}
}
v___jp_2184_:
{
if (v___y_2185_ == 0)
{
uint8_t v___x_2186_; uint8_t v___x_2187_; 
v___x_2186_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__1);
v___x_2187_ = lean_uint8_dec_eq(v_c_2135_, v___x_2186_);
if (v___x_2187_ == 0)
{
uint8_t v___x_2188_; uint8_t v___x_2189_; 
v___x_2188_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__2);
v___x_2189_ = lean_uint8_dec_eq(v_c_2135_, v___x_2188_);
v___y_2179_ = v___x_2189_;
goto v___jp_2178_;
}
else
{
v___y_2179_ = v___x_2187_;
goto v___jp_2178_;
}
}
else
{
return v___y_2185_;
}
}
v___jp_2190_:
{
if (v___y_2191_ == 0)
{
uint8_t v___x_2192_; uint8_t v___x_2193_; 
v___x_2192_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_2193_ = lean_uint8_dec_le(v___x_2192_, v_c_2135_);
if (v___x_2193_ == 0)
{
v___y_2185_ = v___x_2193_;
goto v___jp_2184_;
}
else
{
uint8_t v___x_2194_; uint8_t v___x_2195_; 
v___x_2194_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_2195_ = lean_uint8_dec_le(v_c_2135_, v___x_2194_);
v___y_2185_ = v___x_2195_;
goto v___jp_2184_;
}
}
else
{
return v___y_2191_;
}
}
v___jp_2196_:
{
if (v___y_2197_ == 0)
{
uint8_t v___x_2198_; uint8_t v___x_2199_; 
v___x_2198_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_2199_ = lean_uint8_dec_le(v___x_2198_, v_c_2135_);
if (v___x_2199_ == 0)
{
v___y_2191_ = v___x_2199_;
goto v___jp_2190_;
}
else
{
uint8_t v___x_2200_; uint8_t v___x_2201_; 
v___x_2200_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_2201_ = lean_uint8_dec_le(v_c_2135_, v___x_2200_);
v___y_2191_ = v___x_2201_;
goto v___jp_2190_;
}
}
else
{
return v___y_2197_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed(lean_object* v_c_2206_){
_start:
{
uint8_t v_c_boxed_2207_; uint8_t v_res_2208_; lean_object* v_r_2209_; 
v_c_boxed_2207_ = lean_unbox(v_c_2206_);
v_res_2208_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(v_c_boxed_2207_);
v_r_2209_ = lean_box(v_res_2208_);
return v_r_2209_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(lean_object* v_x_2211_, lean_object* v_x_2212_){
_start:
{
if (lean_obj_tag(v_x_2212_) == 0)
{
lean_object* v___x_2213_; 
v___x_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2213_, 0, v_x_2211_);
return v___x_2213_;
}
else
{
lean_object* v_head_2214_; lean_object* v_tail_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v_head_2214_ = lean_ctor_get(v_x_2212_, 0);
v_tail_2215_ = lean_ctor_get(v_x_2212_, 1);
v___x_2216_ = ((lean_object*)(l_List_foldlM___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___closed__0));
v___x_2217_ = lean_unsigned_to_nat(0u);
v___x_2218_ = lean_box(0);
v___x_2219_ = l_String_splitOnAux(v_head_2214_, v___x_2216_, v___x_2217_, v___x_2217_, v___x_2217_, v___x_2218_);
if (lean_obj_tag(v___x_2219_) == 0)
{
v_x_2212_ = v_tail_2215_;
goto _start;
}
else
{
lean_object* v_tail_2221_; 
v_tail_2221_ = lean_ctor_get(v___x_2219_, 1);
lean_inc(v_tail_2221_);
if (lean_obj_tag(v_tail_2221_) == 0)
{
lean_object* v_head_2222_; lean_object* v___x_2223_; 
v_head_2222_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_head_2222_);
lean_dec_ref(v___x_2219_);
v___x_2223_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2222_);
lean_dec(v_head_2222_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v___x_2224_; 
lean_dec_ref(v_x_2211_);
v___x_2224_ = lean_box(0);
return v___x_2224_;
}
else
{
lean_object* v_val_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v_val_2225_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_val_2225_);
lean_dec_ref(v___x_2223_);
v___x_2226_ = lean_box(0);
v___x_2227_ = l_Std_Http_URI_Query_insertEncoded(v_x_2211_, v_val_2225_, v___x_2226_);
v_x_2211_ = v___x_2227_;
v_x_2212_ = v_tail_2215_;
goto _start;
}
}
else
{
lean_object* v_head_2229_; lean_object* v___x_2230_; 
v_head_2229_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_head_2229_);
lean_dec_ref(v___x_2219_);
v___x_2230_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2229_);
lean_dec(v_head_2229_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v___x_2231_; 
lean_dec(v_tail_2221_);
lean_dec_ref(v_x_2211_);
v___x_2231_ = lean_box(0);
return v___x_2231_;
}
else
{
lean_object* v_val_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v_val_2232_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_val_2232_);
lean_dec_ref(v___x_2230_);
v___x_2233_ = l_String_intercalate(v___x_2216_, v_tail_2221_);
v___x_2234_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2233_);
lean_dec_ref(v___x_2233_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v___x_2235_; 
lean_dec(v_val_2232_);
lean_dec_ref(v_x_2211_);
v___x_2235_ = lean_box(0);
return v___x_2235_;
}
else
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Std_Http_URI_Query_insertEncoded(v_x_2211_, v_val_2232_, v___x_2234_);
v_x_2211_ = v___x_2236_;
v_x_2212_ = v_tail_2215_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___boxed(lean_object* v_x_2238_, lean_object* v_x_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_List_foldlM___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(v_x_2238_, v_x_2239_);
lean_dec(v_x_2239_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(lean_object* v_config_2247_, lean_object* v_a_2248_){
_start:
{
lean_object* v_maxQueryLength_2249_; lean_object* v_maxQueryParams_2250_; lean_object* v___f_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v_fst_2254_; lean_object* v_snd_2255_; lean_object* v_array_2256_; lean_object* v_idx_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2308_; 
v_maxQueryLength_2249_ = lean_ctor_get(v_config_2247_, 4);
lean_inc(v_maxQueryLength_2249_);
v_maxQueryParams_2250_ = lean_ctor_get(v_config_2247_, 8);
lean_inc(v_maxQueryParams_2250_);
lean_dec_ref(v_config_2247_);
v___f_2251_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2252_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2248_);
v___x_2253_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd(v___f_2251_, v_maxQueryLength_2249_, v___x_2252_, v_a_2248_);
lean_dec(v_maxQueryLength_2249_);
v_fst_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_fst_2254_);
v_snd_2255_ = lean_ctor_get(v___x_2253_, 1);
lean_inc(v_snd_2255_);
lean_dec_ref(v___x_2253_);
v_array_2256_ = lean_ctor_get(v_a_2248_, 0);
v_idx_2257_ = lean_ctor_get(v_a_2248_, 1);
v_isSharedCheck_2308_ = !lean_is_exclusive(v_a_2248_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2259_ = v_a_2248_;
v_isShared_2260_ = v_isSharedCheck_2308_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_idx_2257_);
lean_inc(v_array_2256_);
lean_dec(v_a_2248_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2308_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v_lower_2262_; lean_object* v_upper_2263_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___y_2305_; uint8_t v___x_2307_; 
v___x_2302_ = lean_nat_add(v_idx_2257_, v_fst_2254_);
lean_dec(v_fst_2254_);
v___x_2303_ = lean_byte_array_size(v_array_2256_);
v___x_2307_ = lean_nat_dec_le(v_idx_2257_, v___x_2252_);
if (v___x_2307_ == 0)
{
v___y_2305_ = v_idx_2257_;
goto v___jp_2304_;
}
else
{
lean_dec(v_idx_2257_);
v___y_2305_ = v___x_2252_;
goto v___jp_2304_;
}
v___jp_2261_:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; uint8_t v___x_2266_; 
v___x_2264_ = l_ByteArray_toByteSlice(v_array_2256_, v_lower_2262_, v_upper_2263_);
v___x_2265_ = l_ByteSlice_toByteArray(v___x_2264_);
v___x_2266_ = lean_string_validate_utf8(v___x_2265_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2267_; lean_object* v___x_2269_; 
lean_dec_ref(v___x_2265_);
lean_dec(v_maxQueryParams_2250_);
v___x_2267_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2260_ == 0)
{
lean_ctor_set_tag(v___x_2259_, 1);
lean_ctor_set(v___x_2259_, 1, v___x_2267_);
lean_ctor_set(v___x_2259_, 0, v_snd_2255_);
v___x_2269_ = v___x_2259_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_snd_2255_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
else
{
lean_object* v___x_2271_; lean_object* v___x_2272_; uint8_t v___x_2273_; 
v___x_2271_ = lean_string_from_utf8_unchecked(v___x_2265_);
v___x_2272_ = lean_string_utf8_byte_size(v___x_2271_);
v___x_2273_ = lean_nat_dec_eq(v___x_2272_, v___x_2252_);
if (v___x_2273_ == 0)
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; 
v___x_2274_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3));
v___x_2275_ = lean_box(0);
v___x_2276_ = l_String_splitOnAux(v___x_2271_, v___x_2274_, v___x_2252_, v___x_2252_, v___x_2252_, v___x_2275_);
lean_dec_ref(v___x_2271_);
v___x_2277_ = l_List_lengthTR___redArg(v___x_2276_);
v___x_2278_ = lean_nat_dec_lt(v_maxQueryParams_2250_, v___x_2277_);
lean_dec(v___x_2277_);
if (v___x_2278_ == 0)
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
lean_dec(v_maxQueryParams_2250_);
v___x_2279_ = l_Std_Http_URI_Query_empty;
v___x_2280_ = l_List_foldlM___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(v___x_2279_, v___x_2276_);
lean_dec(v___x_2276_);
if (lean_obj_tag(v___x_2280_) == 1)
{
lean_object* v_val_2281_; lean_object* v___x_2283_; 
v_val_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_val_2281_);
lean_dec_ref(v___x_2280_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 1, v_val_2281_);
lean_ctor_set(v___x_2259_, 0, v_snd_2255_);
v___x_2283_ = v___x_2259_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_snd_2255_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_val_2281_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
else
{
lean_object* v___x_2285_; lean_object* v___x_2287_; 
lean_dec(v___x_2280_);
v___x_2285_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2260_ == 0)
{
lean_ctor_set_tag(v___x_2259_, 1);
lean_ctor_set(v___x_2259_, 1, v___x_2285_);
lean_ctor_set(v___x_2259_, 0, v_snd_2255_);
v___x_2287_ = v___x_2259_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_snd_2255_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
else
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2296_; 
lean_dec(v___x_2276_);
v___x_2289_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__4));
v___x_2290_ = l_Nat_reprFast(v_maxQueryParams_2250_);
v___x_2291_ = lean_string_append(v___x_2289_, v___x_2290_);
lean_dec_ref(v___x_2290_);
v___x_2292_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__3));
v___x_2293_ = lean_string_append(v___x_2291_, v___x_2292_);
v___x_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set_tag(v___x_2259_, 1);
lean_ctor_set(v___x_2259_, 1, v___x_2294_);
lean_ctor_set(v___x_2259_, 0, v_snd_2255_);
v___x_2296_ = v___x_2259_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_snd_2255_);
lean_ctor_set(v_reuseFailAlloc_2297_, 1, v___x_2294_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
else
{
lean_object* v___x_2298_; lean_object* v___x_2300_; 
lean_dec_ref(v___x_2271_);
lean_dec(v_maxQueryParams_2250_);
v___x_2298_ = l_Std_Http_URI_Query_empty;
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 1, v___x_2298_);
lean_ctor_set(v___x_2259_, 0, v_snd_2255_);
v___x_2300_ = v___x_2259_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_snd_2255_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v___x_2298_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
v___jp_2304_:
{
uint8_t v___x_2306_; 
v___x_2306_ = lean_nat_dec_le(v___x_2302_, v___x_2303_);
if (v___x_2306_ == 0)
{
lean_dec(v___x_2302_);
v_lower_2262_ = v___y_2305_;
v_upper_2263_ = v___x_2303_;
goto v___jp_2261_;
}
else
{
v_lower_2262_ = v___y_2305_;
v_upper_2263_ = v___x_2302_;
goto v___jp_2261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(lean_object* v_config_2312_, lean_object* v_a_2313_){
_start:
{
lean_object* v_maxFragmentLength_2314_; lean_object* v___f_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v_fst_2318_; lean_object* v_snd_2319_; lean_object* v_array_2320_; lean_object* v_idx_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2345_; 
v_maxFragmentLength_2314_ = lean_ctor_get(v_config_2312_, 5);
v___f_2315_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2316_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2313_);
v___x_2317_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd(v___f_2315_, v_maxFragmentLength_2314_, v___x_2316_, v_a_2313_);
v_fst_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_fst_2318_);
v_snd_2319_ = lean_ctor_get(v___x_2317_, 1);
lean_inc(v_snd_2319_);
lean_dec_ref(v___x_2317_);
v_array_2320_ = lean_ctor_get(v_a_2313_, 0);
v_idx_2321_ = lean_ctor_get(v_a_2313_, 1);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_a_2313_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2323_ = v_a_2313_;
v_isShared_2324_ = v_isSharedCheck_2345_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_idx_2321_);
lean_inc(v_array_2320_);
lean_dec(v_a_2313_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2345_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v_lower_2326_; lean_object* v_upper_2327_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___y_2342_; uint8_t v___x_2344_; 
v___x_2339_ = lean_nat_add(v_idx_2321_, v_fst_2318_);
lean_dec(v_fst_2318_);
v___x_2340_ = lean_byte_array_size(v_array_2320_);
v___x_2344_ = lean_nat_dec_le(v_idx_2321_, v___x_2316_);
if (v___x_2344_ == 0)
{
v___y_2342_ = v_idx_2321_;
goto v___jp_2341_;
}
else
{
lean_dec(v_idx_2321_);
v___y_2342_ = v___x_2316_;
goto v___jp_2341_;
}
v___jp_2325_:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2328_ = l_ByteArray_toByteSlice(v_array_2320_, v_lower_2326_, v_upper_2327_);
v___x_2329_ = l_ByteSlice_toByteArray(v___x_2328_);
v___x_2330_ = l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(v___x_2329_);
if (lean_obj_tag(v___x_2330_) == 1)
{
lean_object* v_val_2331_; lean_object* v___x_2333_; 
v_val_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_val_2331_);
lean_dec_ref(v___x_2330_);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 1, v_val_2331_);
lean_ctor_set(v___x_2323_, 0, v_snd_2319_);
v___x_2333_ = v___x_2323_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_snd_2319_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_val_2331_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
else
{
lean_object* v___x_2335_; lean_object* v___x_2337_; 
lean_dec(v___x_2330_);
v___x_2335_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1));
if (v_isShared_2324_ == 0)
{
lean_ctor_set_tag(v___x_2323_, 1);
lean_ctor_set(v___x_2323_, 1, v___x_2335_);
lean_ctor_set(v___x_2323_, 0, v_snd_2319_);
v___x_2337_ = v___x_2323_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_snd_2319_);
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
v___jp_2341_:
{
uint8_t v___x_2343_; 
v___x_2343_ = lean_nat_dec_le(v___x_2339_, v___x_2340_);
if (v___x_2343_ == 0)
{
lean_dec(v___x_2339_);
v_lower_2326_ = v___y_2342_;
v_upper_2327_ = v___x_2340_;
goto v___jp_2325_;
}
else
{
v_lower_2326_ = v___y_2342_;
v_upper_2327_ = v___x_2339_;
goto v___jp_2325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___boxed(lean_object* v_config_2346_, lean_object* v_a_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2346_, v_a_2347_);
lean_dec_ref(v_config_2346_);
return v_res_2348_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1(void){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0));
v___x_2351_ = lean_string_to_utf8(v___x_2350_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(lean_object* v_config_2352_, lean_object* v_a_2353_){
_start:
{
lean_object* v_pos_2355_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_2353_);
v___x_2391_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2390_, v_a_2353_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_pos_2392_; 
lean_dec_ref(v_a_2353_);
v_pos_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_pos_2392_);
lean_dec_ref(v___x_2391_);
v_pos_2355_ = v_pos_2392_;
goto v___jp_2354_;
}
else
{
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_pos_2393_; 
lean_dec_ref(v_a_2353_);
v_pos_2393_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_pos_2393_);
lean_dec_ref(v___x_2391_);
v_pos_2355_ = v_pos_2393_;
goto v___jp_2354_;
}
else
{
lean_object* v_err_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2425_; 
v_err_2394_ = lean_ctor_get(v___x_2391_, 1);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2425_ == 0)
{
lean_object* v_unused_2426_; 
v_unused_2426_ = lean_ctor_get(v___x_2391_, 0);
lean_dec(v_unused_2426_);
v___x_2396_ = v___x_2391_;
v_isShared_2397_ = v_isSharedCheck_2425_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_err_2394_);
lean_dec(v___x_2391_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2425_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v_idx_2398_; uint8_t v___x_2399_; 
v_idx_2398_ = lean_ctor_get(v_a_2353_, 1);
v___x_2399_ = lean_nat_dec_eq(v_idx_2398_, v_idx_2398_);
if (v___x_2399_ == 0)
{
lean_object* v___x_2401_; 
lean_dec_ref(v_config_2352_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v_a_2353_);
v___x_2401_ = v___x_2396_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2353_);
lean_ctor_set(v_reuseFailAlloc_2402_, 1, v_err_2394_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
else
{
uint8_t v___x_2403_; lean_object* v___x_2404_; 
lean_del_object(v___x_2396_);
lean_dec(v_err_2394_);
v___x_2403_ = 0;
v___x_2404_ = l_Std_Http_URI_Parser_parsePath(v_config_2352_, v___x_2403_, v___x_2399_, v_a_2353_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_pos_2405_; lean_object* v_res_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2415_; 
v_pos_2405_ = lean_ctor_get(v___x_2404_, 0);
v_res_2406_ = lean_ctor_get(v___x_2404_, 1);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2408_ = v___x_2404_;
v_isShared_2409_ = v_isSharedCheck_2415_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_res_2406_);
lean_inc(v_pos_2405_);
lean_dec(v___x_2404_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2415_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2413_; 
v___x_2410_ = lean_box(0);
v___x_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
lean_ctor_set(v___x_2411_, 1, v_res_2406_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 1, v___x_2411_);
v___x_2413_ = v___x_2408_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_pos_2405_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v___x_2411_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
else
{
lean_object* v_pos_2416_; lean_object* v_err_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
v_pos_2416_ = lean_ctor_get(v___x_2404_, 0);
v_err_2417_ = lean_ctor_get(v___x_2404_, 1);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2404_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_err_2417_);
lean_inc(v_pos_2416_);
lean_dec(v___x_2404_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_pos_2416_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_err_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
}
}
}
v___jp_2354_:
{
lean_object* v___x_2356_; 
v___x_2356_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_2352_, v_pos_2355_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_pos_2357_; lean_object* v_res_2358_; uint8_t v___x_2359_; lean_object* v___x_2360_; 
v_pos_2357_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_pos_2357_);
v_res_2358_ = lean_ctor_get(v___x_2356_, 1);
lean_inc(v_res_2358_);
lean_dec_ref(v___x_2356_);
v___x_2359_ = 1;
v___x_2360_ = l_Std_Http_URI_Parser_parsePath(v_config_2352_, v___x_2359_, v___x_2359_, v_pos_2357_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_pos_2361_; lean_object* v_res_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2371_; 
v_pos_2361_ = lean_ctor_get(v___x_2360_, 0);
v_res_2362_ = lean_ctor_get(v___x_2360_, 1);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2364_ = v___x_2360_;
v_isShared_2365_ = v_isSharedCheck_2371_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_res_2362_);
lean_inc(v_pos_2361_);
lean_dec(v___x_2360_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2371_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2366_, 0, v_res_2358_);
v___x_2367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
lean_ctor_set(v___x_2367_, 1, v_res_2362_);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 1, v___x_2367_);
v___x_2369_ = v___x_2364_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_pos_2361_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
else
{
lean_object* v_pos_2372_; lean_object* v_err_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_dec(v_res_2358_);
v_pos_2372_ = lean_ctor_get(v___x_2360_, 0);
v_err_2373_ = lean_ctor_get(v___x_2360_, 1);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2360_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_err_2373_);
lean_inc(v_pos_2372_);
lean_dec(v___x_2360_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_pos_2372_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v_err_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
else
{
lean_object* v_pos_2381_; lean_object* v_err_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_dec_ref(v_config_2352_);
v_pos_2381_ = lean_ctor_get(v___x_2356_, 0);
v_err_2382_ = lean_ctor_get(v___x_2356_, 1);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2356_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_err_2382_);
lean_inc(v_pos_2381_);
lean_dec(v___x_2356_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_pos_2381_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_err_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__0(void){
_start:
{
uint8_t v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v___x_2428_ = lean_uint8_to_nat(v___x_2427_);
return v___x_2428_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__1(void){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2429_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__0, &l_Std_Http_URI_Parser_parseURI___closed__0_once, _init_l_Std_Http_URI_Parser_parseURI___closed__0);
v___x_2430_ = l_Nat_reprFast(v___x_2429_);
return v___x_2430_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__2(void){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2431_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__1, &l_Std_Http_URI_Parser_parseURI___closed__1_once, _init_l_Std_Http_URI_Parser_parseURI___closed__1);
v___x_2432_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_2433_ = lean_string_append(v___x_2432_, v___x_2431_);
return v___x_2433_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__3(void){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2434_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_2435_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__2, &l_Std_Http_URI_Parser_parseURI___closed__2_once, _init_l_Std_Http_URI_Parser_parseURI___closed__2);
v___x_2436_ = lean_string_append(v___x_2435_, v___x_2434_);
return v___x_2436_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__4(void){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__3, &l_Std_Http_URI_Parser_parseURI___closed__3_once, _init_l_Std_Http_URI_Parser_parseURI___closed__3);
v___x_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
return v___x_2438_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__7(void){
_start:
{
uint8_t v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_2443_ = lean_uint8_to_nat(v___x_2442_);
return v___x_2443_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__8(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__7, &l_Std_Http_URI_Parser_parseURI___closed__7_once, _init_l_Std_Http_URI_Parser_parseURI___closed__7);
v___x_2445_ = l_Nat_reprFast(v___x_2444_);
return v___x_2445_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__9(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2446_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__8, &l_Std_Http_URI_Parser_parseURI___closed__8_once, _init_l_Std_Http_URI_Parser_parseURI___closed__8);
v___x_2447_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_2448_ = lean_string_append(v___x_2447_, v___x_2446_);
return v___x_2448_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__10(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2449_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_2450_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__9, &l_Std_Http_URI_Parser_parseURI___closed__9_once, _init_l_Std_Http_URI_Parser_parseURI___closed__9);
v___x_2451_ = lean_string_append(v___x_2450_, v___x_2449_);
return v___x_2451_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__11(void){
_start:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__10, &l_Std_Http_URI_Parser_parseURI___closed__10_once, _init_l_Std_Http_URI_Parser_parseURI___closed__10);
v___x_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURI(lean_object* v_config_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v___x_2456_; 
v___x_2456_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_2454_, v_a_2455_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_pos_2457_; lean_object* v_res_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2598_; 
v_pos_2457_ = lean_ctor_get(v___x_2456_, 0);
v_res_2458_ = lean_ctor_get(v___x_2456_, 1);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2460_ = v___x_2456_;
v_isShared_2461_ = v_isSharedCheck_2598_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_res_2458_);
lean_inc(v_pos_2457_);
lean_dec(v___x_2456_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2598_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v_array_2462_; lean_object* v_idx_2463_; lean_object* v___x_2464_; uint8_t v___x_2465_; 
v_array_2462_ = lean_ctor_get(v_pos_2457_, 0);
v_idx_2463_ = lean_ctor_get(v_pos_2457_, 1);
v___x_2464_ = lean_byte_array_size(v_array_2462_);
v___x_2465_ = lean_nat_dec_lt(v_idx_2463_, v___x_2464_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; lean_object* v___x_2468_; 
lean_dec(v_res_2458_);
lean_dec_ref(v_config_2454_);
v___x_2466_ = lean_box(0);
if (v_isShared_2461_ == 0)
{
lean_ctor_set_tag(v___x_2460_, 1);
lean_ctor_set(v___x_2460_, 1, v___x_2466_);
v___x_2468_ = v___x_2460_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_pos_2457_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v___x_2466_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
else
{
uint8_t v___x_2470_; uint8_t v_c_2471_; uint8_t v___x_2472_; 
v___x_2470_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v_c_2471_ = lean_byte_array_fget(v_array_2462_, v_idx_2463_);
v___x_2472_ = lean_uint8_dec_eq(v_c_2471_, v___x_2470_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; lean_object* v___x_2475_; 
lean_dec(v_res_2458_);
lean_dec_ref(v_config_2454_);
v___x_2473_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
if (v_isShared_2461_ == 0)
{
lean_ctor_set_tag(v___x_2460_, 1);
lean_ctor_set(v___x_2460_, 1, v___x_2473_);
v___x_2475_ = v___x_2460_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_pos_2457_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v___x_2473_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
else
{
lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2595_; 
lean_inc(v_idx_2463_);
lean_inc_ref(v_array_2462_);
v_isSharedCheck_2595_ = !lean_is_exclusive(v_pos_2457_);
if (v_isSharedCheck_2595_ == 0)
{
lean_object* v_unused_2596_; lean_object* v_unused_2597_; 
v_unused_2596_ = lean_ctor_get(v_pos_2457_, 1);
lean_dec(v_unused_2596_);
v_unused_2597_ = lean_ctor_get(v_pos_2457_, 0);
lean_dec(v_unused_2597_);
v___x_2478_ = v_pos_2457_;
v_isShared_2479_ = v_isSharedCheck_2595_;
goto v_resetjp_2477_;
}
else
{
lean_dec(v_pos_2457_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2595_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v_it_x27_2483_; 
v___x_2480_ = lean_unsigned_to_nat(1u);
v___x_2481_ = lean_nat_add(v_idx_2463_, v___x_2480_);
lean_dec(v_idx_2463_);
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 1, v___x_2481_);
v_it_x27_2483_ = v___x_2478_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_array_2462_);
lean_ctor_set(v_reuseFailAlloc_2594_, 1, v___x_2481_);
v_it_x27_2483_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
lean_object* v___x_2484_; 
lean_inc_ref(v_config_2454_);
v___x_2484_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2454_, v_it_x27_2483_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v_res_2485_; lean_object* v_pos_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2584_; 
v_res_2485_ = lean_ctor_get(v___x_2484_, 1);
v_pos_2486_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2488_ = v___x_2484_;
v_isShared_2489_ = v_isSharedCheck_2584_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_res_2485_);
lean_inc(v_pos_2486_);
lean_dec(v___x_2484_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2584_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v_fst_2490_; lean_object* v_snd_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2583_; 
v_fst_2490_ = lean_ctor_get(v_res_2485_, 0);
v_snd_2491_ = lean_ctor_get(v_res_2485_, 1);
v_isSharedCheck_2583_ = !lean_is_exclusive(v_res_2485_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2493_ = v_res_2485_;
v_isShared_2494_ = v_isSharedCheck_2583_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_snd_2491_);
lean_inc(v_fst_2490_);
lean_dec(v_res_2485_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2583_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___y_2496_; lean_object* v_pos_2497_; lean_object* v_res_2498_; lean_object* v___y_2504_; lean_object* v_idx_2505_; lean_object* v_pos_2506_; lean_object* v_idx_2507_; lean_object* v_err_2508_; lean_object* v___y_2515_; lean_object* v_idx_2516_; lean_object* v_pos_2517_; lean_object* v_err_2518_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v_array_2549_; lean_object* v_idx_2550_; lean_object* v_pos_2552_; lean_object* v_idx_2553_; lean_object* v_err_2554_; lean_object* v___x_2560_; uint8_t v___x_2561_; 
v_array_2549_ = lean_ctor_get(v_pos_2486_, 0);
v_idx_2550_ = lean_ctor_get(v_pos_2486_, 1);
lean_inc(v_idx_2550_);
v___x_2560_ = lean_byte_array_size(v_array_2549_);
v___x_2561_ = lean_nat_dec_lt(v_idx_2550_, v___x_2560_);
if (v___x_2561_ == 0)
{
lean_object* v___x_2562_; 
v___x_2562_ = lean_box(0);
lean_inc(v_idx_2550_);
v_pos_2552_ = v_pos_2486_;
v_idx_2553_ = v_idx_2550_;
v_err_2554_ = v___x_2562_;
goto v___jp_2551_;
}
else
{
uint8_t v___x_2563_; uint8_t v_c_2564_; uint8_t v___x_2565_; 
v___x_2563_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_c_2564_ = lean_byte_array_fget(v_array_2549_, v_idx_2550_);
v___x_2565_ = lean_uint8_dec_eq(v_c_2564_, v___x_2563_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; 
v___x_2566_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_2550_);
v_pos_2552_ = v_pos_2486_;
v_idx_2553_ = v_idx_2550_;
v_err_2554_ = v___x_2566_;
goto v___jp_2551_;
}
else
{
lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2580_; 
lean_inc_ref(v_array_2549_);
v_isSharedCheck_2580_ = !lean_is_exclusive(v_pos_2486_);
if (v_isSharedCheck_2580_ == 0)
{
lean_object* v_unused_2581_; lean_object* v_unused_2582_; 
v_unused_2581_ = lean_ctor_get(v_pos_2486_, 1);
lean_dec(v_unused_2581_);
v_unused_2582_ = lean_ctor_get(v_pos_2486_, 0);
lean_dec(v_unused_2582_);
v___x_2568_ = v_pos_2486_;
v_isShared_2569_ = v_isSharedCheck_2580_;
goto v_resetjp_2567_;
}
else
{
lean_dec(v_pos_2486_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2580_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2570_; lean_object* v_it_x27_2572_; 
v___x_2570_ = lean_nat_add(v_idx_2550_, v___x_2480_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 1, v___x_2570_);
v_it_x27_2572_ = v___x_2568_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_array_2549_);
lean_ctor_set(v_reuseFailAlloc_2579_, 1, v___x_2570_);
v_it_x27_2572_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
lean_object* v___x_2573_; 
lean_inc_ref(v_config_2454_);
v___x_2573_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2454_, v_it_x27_2572_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_pos_2574_; lean_object* v_res_2575_; 
lean_dec(v_idx_2550_);
lean_del_object(v___x_2493_);
v_pos_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_pos_2574_);
v_res_2575_ = lean_ctor_get(v___x_2573_, 1);
lean_inc(v_res_2575_);
lean_dec_ref(v___x_2573_);
v___y_2521_ = v_pos_2574_;
v___y_2522_ = v_res_2575_;
goto v___jp_2520_;
}
else
{
lean_object* v_pos_2576_; lean_object* v_err_2577_; lean_object* v_idx_2578_; 
v_pos_2576_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_pos_2576_);
v_err_2577_ = lean_ctor_get(v___x_2573_, 1);
lean_inc(v_err_2577_);
lean_dec_ref(v___x_2573_);
v_idx_2578_ = lean_ctor_get(v_pos_2576_, 1);
lean_inc(v_idx_2578_);
v_pos_2552_ = v_pos_2576_;
v_idx_2553_ = v_idx_2578_;
v_err_2554_ = v_err_2577_;
goto v___jp_2551_;
}
}
}
}
}
v___jp_2495_:
{
lean_object* v___x_2499_; lean_object* v___x_2501_; 
v___x_2499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2499_, 0, v_res_2458_);
lean_ctor_set(v___x_2499_, 1, v_fst_2490_);
lean_ctor_set(v___x_2499_, 2, v_snd_2491_);
lean_ctor_set(v___x_2499_, 3, v___y_2496_);
lean_ctor_set(v___x_2499_, 4, v_res_2498_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 1, v___x_2499_);
lean_ctor_set(v___x_2488_, 0, v_pos_2497_);
v___x_2501_ = v___x_2488_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_pos_2497_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v___x_2499_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
v___jp_2503_:
{
uint8_t v___x_2509_; 
v___x_2509_ = lean_nat_dec_eq(v_idx_2505_, v_idx_2507_);
lean_dec(v_idx_2507_);
lean_dec(v_idx_2505_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2511_; 
lean_dec_ref(v___y_2504_);
lean_dec(v_snd_2491_);
lean_dec(v_fst_2490_);
lean_del_object(v___x_2488_);
lean_dec(v_res_2458_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set_tag(v___x_2460_, 1);
lean_ctor_set(v___x_2460_, 1, v_err_2508_);
lean_ctor_set(v___x_2460_, 0, v_pos_2506_);
v___x_2511_ = v___x_2460_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_pos_2506_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v_err_2508_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
else
{
lean_object* v___x_2513_; 
lean_dec(v_err_2508_);
lean_del_object(v___x_2460_);
v___x_2513_ = lean_box(0);
v___y_2496_ = v___y_2504_;
v_pos_2497_ = v_pos_2506_;
v_res_2498_ = v___x_2513_;
goto v___jp_2495_;
}
}
v___jp_2514_:
{
lean_object* v_idx_2519_; 
v_idx_2519_ = lean_ctor_get(v_pos_2517_, 1);
lean_inc(v_idx_2519_);
v___y_2504_ = v___y_2515_;
v_idx_2505_ = v_idx_2516_;
v_pos_2506_ = v_pos_2517_;
v_idx_2507_ = v_idx_2519_;
v_err_2508_ = v_err_2518_;
goto v___jp_2503_;
}
v___jp_2520_:
{
lean_object* v_array_2523_; lean_object* v_idx_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; 
v_array_2523_ = lean_ctor_get(v___y_2521_, 0);
v_idx_2524_ = lean_ctor_get(v___y_2521_, 1);
lean_inc(v_idx_2524_);
v___x_2525_ = lean_byte_array_size(v_array_2523_);
v___x_2526_ = lean_nat_dec_lt(v_idx_2524_, v___x_2525_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; 
lean_dec_ref(v_config_2454_);
v___x_2527_ = lean_box(0);
lean_inc(v_idx_2524_);
v___y_2504_ = v___y_2522_;
v_idx_2505_ = v_idx_2524_;
v_pos_2506_ = v___y_2521_;
v_idx_2507_ = v_idx_2524_;
v_err_2508_ = v___x_2527_;
goto v___jp_2503_;
}
else
{
uint8_t v___x_2528_; uint8_t v_c_2529_; uint8_t v___x_2530_; 
v___x_2528_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v_c_2529_ = lean_byte_array_fget(v_array_2523_, v_idx_2524_);
v___x_2530_ = lean_uint8_dec_eq(v_c_2529_, v___x_2528_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; 
lean_dec_ref(v_config_2454_);
v___x_2531_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__4, &l_Std_Http_URI_Parser_parseURI___closed__4_once, _init_l_Std_Http_URI_Parser_parseURI___closed__4);
lean_inc(v_idx_2524_);
v___y_2504_ = v___y_2522_;
v_idx_2505_ = v_idx_2524_;
v_pos_2506_ = v___y_2521_;
v_idx_2507_ = v_idx_2524_;
v_err_2508_ = v___x_2531_;
goto v___jp_2503_;
}
else
{
lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2546_; 
lean_inc_ref(v_array_2523_);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___y_2521_);
if (v_isSharedCheck_2546_ == 0)
{
lean_object* v_unused_2547_; lean_object* v_unused_2548_; 
v_unused_2547_ = lean_ctor_get(v___y_2521_, 1);
lean_dec(v_unused_2547_);
v_unused_2548_ = lean_ctor_get(v___y_2521_, 0);
lean_dec(v_unused_2548_);
v___x_2533_ = v___y_2521_;
v_isShared_2534_ = v_isSharedCheck_2546_;
goto v_resetjp_2532_;
}
else
{
lean_dec(v___y_2521_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2546_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2535_; lean_object* v_it_x27_2537_; 
v___x_2535_ = lean_nat_add(v_idx_2524_, v___x_2480_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 1, v___x_2535_);
v_it_x27_2537_ = v___x_2533_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_array_2523_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v___x_2535_);
v_it_x27_2537_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2538_; 
v___x_2538_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2454_, v_it_x27_2537_);
lean_dec_ref(v_config_2454_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_pos_2539_; lean_object* v_res_2540_; lean_object* v___x_2541_; 
v_pos_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_pos_2539_);
v_res_2540_ = lean_ctor_get(v___x_2538_, 1);
lean_inc(v_res_2540_);
lean_dec_ref(v___x_2538_);
v___x_2541_ = l_Std_Http_URI_EncodedFragment_decode(v_res_2540_);
lean_dec(v_res_2540_);
if (lean_obj_tag(v___x_2541_) == 1)
{
lean_dec(v_idx_2524_);
lean_del_object(v___x_2460_);
v___y_2496_ = v___y_2522_;
v_pos_2497_ = v_pos_2539_;
v_res_2498_ = v___x_2541_;
goto v___jp_2495_;
}
else
{
lean_object* v___x_2542_; 
lean_dec(v___x_2541_);
v___x_2542_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__6));
v___y_2515_ = v___y_2522_;
v_idx_2516_ = v_idx_2524_;
v_pos_2517_ = v_pos_2539_;
v_err_2518_ = v___x_2542_;
goto v___jp_2514_;
}
}
else
{
lean_object* v_pos_2543_; lean_object* v_err_2544_; 
v_pos_2543_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_pos_2543_);
v_err_2544_ = lean_ctor_get(v___x_2538_, 1);
lean_inc(v_err_2544_);
lean_dec_ref(v___x_2538_);
v___y_2515_ = v___y_2522_;
v_idx_2516_ = v_idx_2524_;
v_pos_2517_ = v_pos_2543_;
v_err_2518_ = v_err_2544_;
goto v___jp_2514_;
}
}
}
}
}
}
v___jp_2551_:
{
uint8_t v___x_2555_; 
v___x_2555_ = lean_nat_dec_eq(v_idx_2550_, v_idx_2553_);
lean_dec(v_idx_2553_);
lean_dec(v_idx_2550_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2557_; 
lean_dec(v_snd_2491_);
lean_dec(v_fst_2490_);
lean_del_object(v___x_2488_);
lean_del_object(v___x_2460_);
lean_dec(v_res_2458_);
lean_dec_ref(v_config_2454_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set_tag(v___x_2493_, 1);
lean_ctor_set(v___x_2493_, 1, v_err_2554_);
lean_ctor_set(v___x_2493_, 0, v_pos_2552_);
v___x_2557_ = v___x_2493_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_pos_2552_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v_err_2554_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
else
{
lean_object* v___x_2559_; 
lean_dec(v_err_2554_);
lean_del_object(v___x_2493_);
v___x_2559_ = l_Std_Http_URI_Query_empty;
v___y_2521_ = v_pos_2552_;
v___y_2522_ = v___x_2559_;
goto v___jp_2520_;
}
}
}
}
}
else
{
lean_object* v_pos_2585_; lean_object* v_err_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_del_object(v___x_2460_);
lean_dec(v_res_2458_);
lean_dec_ref(v_config_2454_);
v_pos_2585_ = lean_ctor_get(v___x_2484_, 0);
v_err_2586_ = lean_ctor_get(v___x_2484_, 1);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2484_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_err_2586_);
lean_inc(v_pos_2585_);
lean_dec(v___x_2484_);
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
}
else
{
lean_object* v_pos_2599_; lean_object* v_err_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_dec_ref(v_config_2454_);
v_pos_2599_ = lean_ctor_get(v___x_2456_, 0);
v_err_2600_ = lean_ctor_get(v___x_2456_, 1);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2456_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_err_2600_);
lean_inc(v_pos_2599_);
lean_dec(v___x_2456_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_pos_2599_);
lean_ctor_set(v_reuseFailAlloc_2606_, 1, v_err_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0(void){
_start:
{
uint8_t v___x_2608_; lean_object* v___x_2609_; 
v___x_2608_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_2609_ = lean_uint8_to_nat(v___x_2608_);
return v___x_2609_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1(void){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0);
v___x_2611_ = l_Nat_reprFast(v___x_2610_);
return v___x_2611_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2612_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1);
v___x_2613_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_2614_ = lean_string_append(v___x_2613_, v___x_2612_);
return v___x_2614_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3(void){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2615_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_2616_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2);
v___x_2617_ = lean_string_append(v___x_2616_, v___x_2615_);
return v___x_2617_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4(void){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2618_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3);
v___x_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2618_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(lean_object* v_a_2620_){
_start:
{
lean_object* v_array_2621_; lean_object* v_idx_2622_; lean_object* v___x_2623_; uint8_t v___x_2624_; 
v_array_2621_ = lean_ctor_get(v_a_2620_, 0);
v_idx_2622_ = lean_ctor_get(v_a_2620_, 1);
v___x_2623_ = lean_byte_array_size(v_array_2621_);
v___x_2624_ = lean_nat_dec_lt(v_idx_2622_, v___x_2623_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = lean_box(0);
v___x_2626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2626_, 0, v_a_2620_);
lean_ctor_set(v___x_2626_, 1, v___x_2625_);
return v___x_2626_;
}
else
{
uint8_t v___x_2627_; uint8_t v_c_2628_; uint8_t v___x_2629_; 
v___x_2627_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v_c_2628_ = lean_byte_array_fget(v_array_2621_, v_idx_2622_);
v___x_2629_ = lean_uint8_dec_eq(v_c_2628_, v___x_2627_);
if (v___x_2629_ == 0)
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2630_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4);
v___x_2631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2631_, 0, v_a_2620_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
return v___x_2631_;
}
else
{
lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2642_; 
lean_inc(v_idx_2622_);
lean_inc_ref(v_array_2621_);
v_isSharedCheck_2642_ = !lean_is_exclusive(v_a_2620_);
if (v_isSharedCheck_2642_ == 0)
{
lean_object* v_unused_2643_; lean_object* v_unused_2644_; 
v_unused_2643_ = lean_ctor_get(v_a_2620_, 1);
lean_dec(v_unused_2643_);
v_unused_2644_ = lean_ctor_get(v_a_2620_, 0);
lean_dec(v_unused_2644_);
v___x_2633_ = v_a_2620_;
v_isShared_2634_ = v_isSharedCheck_2642_;
goto v_resetjp_2632_;
}
else
{
lean_dec(v_a_2620_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2642_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v_it_x27_2638_; 
v___x_2635_ = lean_unsigned_to_nat(1u);
v___x_2636_ = lean_nat_add(v_idx_2622_, v___x_2635_);
lean_dec(v_idx_2622_);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 1, v___x_2636_);
v_it_x27_2638_ = v___x_2633_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_array_2621_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v___x_2636_);
v_it_x27_2638_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2639_ = lean_box(3);
v___x_2640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2640_, 0, v_it_x27_2638_);
lean_ctor_set(v___x_2640_, 1, v___x_2639_);
return v___x_2640_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(lean_object* v_config_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v_array_2653_; lean_object* v_idx_2654_; lean_object* v___x_2655_; uint8_t v___x_2656_; 
v_array_2653_ = lean_ctor_get(v_a_2649_, 0);
v_idx_2654_ = lean_ctor_get(v_a_2649_, 1);
v___x_2655_ = lean_byte_array_size(v_array_2653_);
v___x_2656_ = lean_nat_dec_lt(v_idx_2654_, v___x_2655_);
if (v___x_2656_ == 0)
{
lean_dec_ref(v_config_2648_);
goto v___jp_2650_;
}
else
{
uint8_t v___x_2657_; uint8_t v___x_2658_; uint8_t v___x_2659_; 
v___x_2657_ = lean_byte_array_fget(v_array_2653_, v_idx_2654_);
v___x_2658_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2659_ = lean_uint8_dec_eq(v___x_2657_, v___x_2658_);
if (v___x_2659_ == 0)
{
lean_dec_ref(v_config_2648_);
goto v___jp_2650_;
}
else
{
if (v___x_2659_ == 0)
{
lean_dec_ref(v_config_2648_);
goto v___jp_2650_;
}
else
{
lean_object* v___x_2660_; 
lean_inc_ref(v_a_2649_);
lean_inc_ref(v_config_2648_);
v___x_2660_ = l_Std_Http_URI_Parser_parsePath(v_config_2648_, v___x_2659_, v___x_2659_, v_a_2649_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v_pos_2661_; lean_object* v_res_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2707_; 
v_pos_2661_ = lean_ctor_get(v___x_2660_, 0);
v_res_2662_ = lean_ctor_get(v___x_2660_, 1);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2664_ = v___x_2660_;
v_isShared_2665_ = v_isSharedCheck_2707_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_res_2662_);
lean_inc(v_pos_2661_);
lean_dec(v___x_2660_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2707_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v_pos_2667_; lean_object* v_res_2668_; lean_object* v_array_2673_; lean_object* v_idx_2674_; lean_object* v_pos_2676_; lean_object* v_idx_2677_; lean_object* v_err_2678_; lean_object* v___x_2682_; uint8_t v___x_2683_; 
v_array_2673_ = lean_ctor_get(v_pos_2661_, 0);
v_idx_2674_ = lean_ctor_get(v_pos_2661_, 1);
lean_inc(v_idx_2674_);
v___x_2682_ = lean_byte_array_size(v_array_2673_);
v___x_2683_ = lean_nat_dec_lt(v_idx_2674_, v___x_2682_);
if (v___x_2683_ == 0)
{
lean_object* v___x_2684_; 
lean_dec_ref(v_config_2648_);
v___x_2684_ = lean_box(0);
lean_inc(v_idx_2674_);
v_pos_2676_ = v_pos_2661_;
v_idx_2677_ = v_idx_2674_;
v_err_2678_ = v___x_2684_;
goto v___jp_2675_;
}
else
{
uint8_t v___x_2685_; uint8_t v_c_2686_; uint8_t v___x_2687_; 
v___x_2685_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_c_2686_ = lean_byte_array_fget(v_array_2673_, v_idx_2674_);
v___x_2687_ = lean_uint8_dec_eq(v_c_2686_, v___x_2685_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; 
lean_dec_ref(v_config_2648_);
v___x_2688_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_2674_);
v_pos_2676_ = v_pos_2661_;
v_idx_2677_ = v_idx_2674_;
v_err_2678_ = v___x_2688_;
goto v___jp_2675_;
}
else
{
lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2704_; 
lean_inc_ref(v_array_2673_);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_pos_2661_);
if (v_isSharedCheck_2704_ == 0)
{
lean_object* v_unused_2705_; lean_object* v_unused_2706_; 
v_unused_2705_ = lean_ctor_get(v_pos_2661_, 1);
lean_dec(v_unused_2705_);
v_unused_2706_ = lean_ctor_get(v_pos_2661_, 0);
lean_dec(v_unused_2706_);
v___x_2690_ = v_pos_2661_;
v_isShared_2691_ = v_isSharedCheck_2704_;
goto v_resetjp_2689_;
}
else
{
lean_dec(v_pos_2661_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2704_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v_it_x27_2695_; 
v___x_2692_ = lean_unsigned_to_nat(1u);
v___x_2693_ = lean_nat_add(v_idx_2674_, v___x_2692_);
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 1, v___x_2693_);
v_it_x27_2695_ = v___x_2690_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_array_2673_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v___x_2693_);
v_it_x27_2695_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
lean_object* v___x_2696_; 
v___x_2696_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2648_, v_it_x27_2695_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_pos_2697_; lean_object* v_res_2698_; lean_object* v___x_2699_; 
lean_dec(v_idx_2674_);
lean_dec_ref(v_a_2649_);
v_pos_2697_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_pos_2697_);
v_res_2698_ = lean_ctor_get(v___x_2696_, 1);
lean_inc(v_res_2698_);
lean_dec_ref(v___x_2696_);
v___x_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2699_, 0, v_res_2698_);
v_pos_2667_ = v_pos_2697_;
v_res_2668_ = v___x_2699_;
goto v___jp_2666_;
}
else
{
lean_object* v_pos_2700_; lean_object* v_err_2701_; lean_object* v_idx_2702_; 
v_pos_2700_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_pos_2700_);
v_err_2701_ = lean_ctor_get(v___x_2696_, 1);
lean_inc(v_err_2701_);
lean_dec_ref(v___x_2696_);
v_idx_2702_ = lean_ctor_get(v_pos_2700_, 1);
lean_inc(v_idx_2702_);
v_pos_2676_ = v_pos_2700_;
v_idx_2677_ = v_idx_2702_;
v_err_2678_ = v_err_2701_;
goto v___jp_2675_;
}
}
}
}
}
v___jp_2666_:
{
lean_object* v___x_2669_; lean_object* v___x_2671_; 
v___x_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2669_, 0, v_res_2662_);
lean_ctor_set(v___x_2669_, 1, v_res_2668_);
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 1, v___x_2669_);
lean_ctor_set(v___x_2664_, 0, v_pos_2667_);
v___x_2671_ = v___x_2664_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_pos_2667_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v___x_2669_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
v___jp_2675_:
{
uint8_t v___x_2679_; 
v___x_2679_ = lean_nat_dec_eq(v_idx_2674_, v_idx_2677_);
lean_dec(v_idx_2677_);
lean_dec(v_idx_2674_);
if (v___x_2679_ == 0)
{
lean_object* v___x_2680_; 
lean_dec_ref(v_pos_2676_);
lean_del_object(v___x_2664_);
lean_dec(v_res_2662_);
v___x_2680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2680_, 0, v_a_2649_);
lean_ctor_set(v___x_2680_, 1, v_err_2678_);
return v___x_2680_;
}
else
{
lean_object* v___x_2681_; 
lean_dec(v_err_2678_);
lean_dec_ref(v_a_2649_);
v___x_2681_ = lean_box(0);
v_pos_2667_ = v_pos_2676_;
v_res_2668_ = v___x_2681_;
goto v___jp_2666_;
}
}
}
}
else
{
lean_object* v_err_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
lean_dec_ref(v_config_2648_);
v_err_2708_ = lean_ctor_get(v___x_2660_, 1);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2715_ == 0)
{
lean_object* v_unused_2716_; 
v_unused_2716_ = lean_ctor_get(v___x_2660_, 0);
lean_dec(v_unused_2716_);
v___x_2710_ = v___x_2660_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_err_2708_);
lean_dec(v___x_2660_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 0, v_a_2649_);
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2649_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v_err_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
}
}
v___jp_2650_:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1));
v___x_2652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2652_, 0, v_a_2649_);
lean_ctor_set(v___x_2652_, 1, v___x_2651_);
return v___x_2652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(lean_object* v_config_2717_, lean_object* v_scheme_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v_array_2720_; lean_object* v_idx_2721_; lean_object* v___x_2722_; uint8_t v___x_2723_; 
v_array_2720_ = lean_ctor_get(v_a_2719_, 0);
v_idx_2721_ = lean_ctor_get(v_a_2719_, 1);
v___x_2722_ = lean_byte_array_size(v_array_2720_);
v___x_2723_ = lean_nat_dec_lt(v_idx_2721_, v___x_2722_);
if (v___x_2723_ == 0)
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
lean_dec_ref(v_scheme_2718_);
lean_dec_ref(v_config_2717_);
v___x_2724_ = lean_box(0);
v___x_2725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2725_, 0, v_a_2719_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
return v___x_2725_;
}
else
{
uint8_t v___x_2726_; uint8_t v_c_2727_; uint8_t v___x_2728_; 
v___x_2726_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v_c_2727_ = lean_byte_array_fget(v_array_2720_, v_idx_2721_);
v___x_2728_ = lean_uint8_dec_eq(v_c_2727_, v___x_2726_);
if (v___x_2728_ == 0)
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
lean_dec_ref(v_scheme_2718_);
lean_dec_ref(v_config_2717_);
v___x_2729_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
v___x_2730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2730_, 0, v_a_2719_);
lean_ctor_set(v___x_2730_, 1, v___x_2729_);
return v___x_2730_;
}
else
{
lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2804_; 
lean_inc(v_idx_2721_);
lean_inc_ref(v_array_2720_);
v_isSharedCheck_2804_ = !lean_is_exclusive(v_a_2719_);
if (v_isSharedCheck_2804_ == 0)
{
lean_object* v_unused_2805_; lean_object* v_unused_2806_; 
v_unused_2805_ = lean_ctor_get(v_a_2719_, 1);
lean_dec(v_unused_2805_);
v_unused_2806_ = lean_ctor_get(v_a_2719_, 0);
lean_dec(v_unused_2806_);
v___x_2732_ = v_a_2719_;
v_isShared_2733_ = v_isSharedCheck_2804_;
goto v_resetjp_2731_;
}
else
{
lean_dec(v_a_2719_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2804_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v_it_x27_2737_; 
v___x_2734_ = lean_unsigned_to_nat(1u);
v___x_2735_ = lean_nat_add(v_idx_2721_, v___x_2734_);
lean_dec(v_idx_2721_);
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 1, v___x_2735_);
v_it_x27_2737_ = v___x_2732_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_array_2720_);
lean_ctor_set(v_reuseFailAlloc_2803_, 1, v___x_2735_);
v_it_x27_2737_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
lean_object* v___x_2738_; 
lean_inc_ref(v_config_2717_);
v___x_2738_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2717_, v_it_x27_2737_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_res_2739_; lean_object* v_pos_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2793_; 
v_res_2739_ = lean_ctor_get(v___x_2738_, 1);
v_pos_2740_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2742_ = v___x_2738_;
v_isShared_2743_ = v_isSharedCheck_2793_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_res_2739_);
lean_inc(v_pos_2740_);
lean_dec(v___x_2738_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2793_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v_fst_2744_; lean_object* v_snd_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2792_; 
v_fst_2744_ = lean_ctor_get(v_res_2739_, 0);
v_snd_2745_ = lean_ctor_get(v_res_2739_, 1);
v_isSharedCheck_2792_ = !lean_is_exclusive(v_res_2739_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2747_ = v_res_2739_;
v_isShared_2748_ = v_isSharedCheck_2792_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_snd_2745_);
lean_inc(v_fst_2744_);
lean_dec(v_res_2739_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2792_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v_array_2758_; lean_object* v_idx_2759_; lean_object* v_pos_2761_; lean_object* v_idx_2762_; lean_object* v_err_2763_; lean_object* v___x_2769_; uint8_t v___x_2770_; 
v_array_2758_ = lean_ctor_get(v_pos_2740_, 0);
v_idx_2759_ = lean_ctor_get(v_pos_2740_, 1);
lean_inc(v_idx_2759_);
v___x_2769_ = lean_byte_array_size(v_array_2758_);
v___x_2770_ = lean_nat_dec_lt(v_idx_2759_, v___x_2769_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2771_; 
lean_dec_ref(v_config_2717_);
v___x_2771_ = lean_box(0);
lean_inc(v_idx_2759_);
v_pos_2761_ = v_pos_2740_;
v_idx_2762_ = v_idx_2759_;
v_err_2763_ = v___x_2771_;
goto v___jp_2760_;
}
else
{
uint8_t v___x_2772_; uint8_t v_c_2773_; uint8_t v___x_2774_; 
v___x_2772_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_c_2773_ = lean_byte_array_fget(v_array_2758_, v_idx_2759_);
v___x_2774_ = lean_uint8_dec_eq(v_c_2773_, v___x_2772_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2775_; 
lean_dec_ref(v_config_2717_);
v___x_2775_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_2759_);
v_pos_2761_ = v_pos_2740_;
v_idx_2762_ = v_idx_2759_;
v_err_2763_ = v___x_2775_;
goto v___jp_2760_;
}
else
{
lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2789_; 
lean_inc_ref(v_array_2758_);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_pos_2740_);
if (v_isSharedCheck_2789_ == 0)
{
lean_object* v_unused_2790_; lean_object* v_unused_2791_; 
v_unused_2790_ = lean_ctor_get(v_pos_2740_, 1);
lean_dec(v_unused_2790_);
v_unused_2791_ = lean_ctor_get(v_pos_2740_, 0);
lean_dec(v_unused_2791_);
v___x_2777_ = v_pos_2740_;
v_isShared_2778_ = v_isSharedCheck_2789_;
goto v_resetjp_2776_;
}
else
{
lean_dec(v_pos_2740_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2789_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; lean_object* v_it_x27_2781_; 
v___x_2779_ = lean_nat_add(v_idx_2759_, v___x_2734_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 1, v___x_2779_);
v_it_x27_2781_ = v___x_2777_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_array_2758_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v___x_2779_);
v_it_x27_2781_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2782_; 
v___x_2782_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2717_, v_it_x27_2781_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_pos_2783_; lean_object* v_res_2784_; 
lean_dec(v_idx_2759_);
lean_del_object(v___x_2747_);
v_pos_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_pos_2783_);
v_res_2784_ = lean_ctor_get(v___x_2782_, 1);
lean_inc(v_res_2784_);
lean_dec_ref(v___x_2782_);
v___y_2750_ = v_pos_2783_;
v___y_2751_ = v_res_2784_;
goto v___jp_2749_;
}
else
{
lean_object* v_pos_2785_; lean_object* v_err_2786_; lean_object* v_idx_2787_; 
v_pos_2785_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_pos_2785_);
v_err_2786_ = lean_ctor_get(v___x_2782_, 1);
lean_inc(v_err_2786_);
lean_dec_ref(v___x_2782_);
v_idx_2787_ = lean_ctor_get(v_pos_2785_, 1);
lean_inc(v_idx_2787_);
v_pos_2761_ = v_pos_2785_;
v_idx_2762_ = v_idx_2787_;
v_err_2763_ = v_err_2786_;
goto v___jp_2760_;
}
}
}
}
}
v___jp_2749_:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2756_; 
v___x_2752_ = lean_box(0);
v___x_2753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2753_, 0, v_scheme_2718_);
lean_ctor_set(v___x_2753_, 1, v_fst_2744_);
lean_ctor_set(v___x_2753_, 2, v_snd_2745_);
lean_ctor_set(v___x_2753_, 3, v___y_2751_);
lean_ctor_set(v___x_2753_, 4, v___x_2752_);
v___x_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2753_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 1, v___x_2754_);
lean_ctor_set(v___x_2742_, 0, v___y_2750_);
v___x_2756_ = v___x_2742_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___y_2750_);
lean_ctor_set(v_reuseFailAlloc_2757_, 1, v___x_2754_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
v___jp_2760_:
{
uint8_t v___x_2764_; 
v___x_2764_ = lean_nat_dec_eq(v_idx_2759_, v_idx_2762_);
lean_dec(v_idx_2762_);
lean_dec(v_idx_2759_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2766_; 
lean_dec(v_snd_2745_);
lean_dec(v_fst_2744_);
lean_del_object(v___x_2742_);
lean_dec_ref(v_scheme_2718_);
if (v_isShared_2748_ == 0)
{
lean_ctor_set_tag(v___x_2747_, 1);
lean_ctor_set(v___x_2747_, 1, v_err_2763_);
lean_ctor_set(v___x_2747_, 0, v_pos_2761_);
v___x_2766_ = v___x_2747_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_pos_2761_);
lean_ctor_set(v_reuseFailAlloc_2767_, 1, v_err_2763_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
else
{
lean_object* v___x_2768_; 
lean_dec(v_err_2763_);
lean_del_object(v___x_2747_);
v___x_2768_ = l_Std_Http_URI_Query_empty;
v___y_2750_ = v_pos_2761_;
v___y_2751_ = v___x_2768_;
goto v___jp_2749_;
}
}
}
}
}
else
{
lean_object* v_pos_2794_; lean_object* v_err_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
lean_dec_ref(v_scheme_2718_);
lean_dec_ref(v_config_2717_);
v_pos_2794_ = lean_ctor_get(v___x_2738_, 0);
v_err_2795_ = lean_ctor_get(v___x_2738_, 1);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2738_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_err_2795_);
lean_inc(v_pos_2794_);
lean_dec(v___x_2738_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_pos_2794_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v_err_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(lean_object* v_config_2815_, lean_object* v_a_2816_){
_start:
{
lean_object* v___x_2820_; 
lean_inc_ref(v_a_2816_);
v___x_2820_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_2815_, v_a_2816_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_pos_2821_; lean_object* v_res_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2918_; 
v_pos_2821_ = lean_ctor_get(v___x_2820_, 0);
v_res_2822_ = lean_ctor_get(v___x_2820_, 1);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2824_ = v___x_2820_;
v_isShared_2825_ = v_isSharedCheck_2918_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_res_2822_);
lean_inc(v_pos_2821_);
lean_dec(v___x_2820_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2918_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2838_; lean_object* v_idx_2839_; lean_object* v___y_2840_; lean_object* v_pos_2841_; lean_object* v_idx_2842_; lean_object* v_err_2843_; uint8_t v___y_2848_; lean_object* v___x_2914_; uint8_t v___x_2915_; 
v___x_2914_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__4));
v___x_2915_ = lean_string_dec_eq(v_res_2822_, v___x_2914_);
if (v___x_2915_ == 0)
{
lean_object* v___x_2916_; uint8_t v___x_2917_; 
v___x_2916_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5));
v___x_2917_ = lean_string_dec_eq(v_res_2822_, v___x_2916_);
v___y_2848_ = v___x_2917_;
goto v___jp_2847_;
}
else
{
v___y_2848_ = v___x_2915_;
goto v___jp_2847_;
}
v___jp_2826_:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2835_; 
v___x_2831_ = lean_box(0);
v___x_2832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2832_, 0, v_res_2822_);
lean_ctor_set(v___x_2832_, 1, v___y_2827_);
lean_ctor_set(v___x_2832_, 2, v___y_2829_);
lean_ctor_set(v___x_2832_, 3, v___y_2830_);
lean_ctor_set(v___x_2832_, 4, v___x_2831_);
v___x_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 1, v___x_2833_);
lean_ctor_set(v___x_2824_, 0, v___y_2828_);
v___x_2835_ = v___x_2824_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___y_2828_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v___x_2833_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
v___jp_2837_:
{
uint8_t v___x_2844_; 
v___x_2844_ = lean_nat_dec_eq(v_idx_2839_, v_idx_2842_);
lean_dec(v_idx_2842_);
lean_dec(v_idx_2839_);
if (v___x_2844_ == 0)
{
lean_object* v___x_2845_; 
lean_dec_ref(v_pos_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2838_);
lean_del_object(v___x_2824_);
lean_dec(v_res_2822_);
v___x_2845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2845_, 0, v_a_2816_);
lean_ctor_set(v___x_2845_, 1, v_err_2843_);
return v___x_2845_;
}
else
{
lean_object* v___x_2846_; 
lean_dec(v_err_2843_);
lean_dec_ref(v_a_2816_);
v___x_2846_ = l_Std_Http_URI_Query_empty;
v___y_2827_ = v___y_2838_;
v___y_2828_ = v_pos_2841_;
v___y_2829_ = v___y_2840_;
v___y_2830_ = v___x_2846_;
goto v___jp_2826_;
}
}
v___jp_2847_:
{
if (v___y_2848_ == 0)
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
lean_del_object(v___x_2824_);
lean_dec(v_res_2822_);
lean_dec(v_pos_2821_);
lean_dec_ref(v_config_2815_);
v___x_2849_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3));
v___x_2850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2850_, 0, v_a_2816_);
lean_ctor_set(v___x_2850_, 1, v___x_2849_);
return v___x_2850_;
}
else
{
lean_object* v_array_2851_; lean_object* v_idx_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2913_; 
v_array_2851_ = lean_ctor_get(v_pos_2821_, 0);
v_idx_2852_ = lean_ctor_get(v_pos_2821_, 1);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_pos_2821_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2854_ = v_pos_2821_;
v_isShared_2855_ = v_isSharedCheck_2913_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_idx_2852_);
lean_inc(v_array_2851_);
lean_dec(v_pos_2821_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2913_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2856_; uint8_t v___x_2857_; 
v___x_2856_ = lean_byte_array_size(v_array_2851_);
v___x_2857_ = lean_nat_dec_lt(v_idx_2852_, v___x_2856_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
lean_del_object(v___x_2854_);
lean_dec(v_idx_2852_);
lean_dec_ref(v_array_2851_);
lean_del_object(v___x_2824_);
lean_dec(v_res_2822_);
lean_dec_ref(v_config_2815_);
v___x_2858_ = lean_box(0);
v___x_2859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2859_, 0, v_a_2816_);
lean_ctor_set(v___x_2859_, 1, v___x_2858_);
return v___x_2859_;
}
else
{
uint8_t v___x_2860_; uint8_t v_c_2861_; uint8_t v___x_2862_; 
v___x_2860_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v_c_2861_ = lean_byte_array_fget(v_array_2851_, v_idx_2852_);
v___x_2862_ = lean_uint8_dec_eq(v_c_2861_, v___x_2860_);
if (v___x_2862_ == 0)
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
lean_del_object(v___x_2854_);
lean_dec(v_idx_2852_);
lean_dec_ref(v_array_2851_);
lean_del_object(v___x_2824_);
lean_dec(v_res_2822_);
lean_dec_ref(v_config_2815_);
v___x_2863_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
v___x_2864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2864_, 0, v_a_2816_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
return v___x_2864_;
}
else
{
lean_object* v___x_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; 
v___x_2865_ = lean_unsigned_to_nat(1u);
v___x_2866_ = lean_nat_add(v_idx_2852_, v___x_2865_);
lean_dec(v_idx_2852_);
v___x_2867_ = lean_nat_dec_lt(v___x_2866_, v___x_2856_);
if (v___x_2867_ == 0)
{
lean_dec(v___x_2866_);
lean_del_object(v___x_2854_);
lean_dec_ref(v_array_2851_);
lean_del_object(v___x_2824_);
lean_dec(v_res_2822_);
lean_dec_ref(v_config_2815_);
goto v___jp_2817_;
}
else
{
uint8_t v___x_2868_; uint8_t v___x_2869_; uint8_t v___x_2870_; 
v___x_2868_ = lean_byte_array_fget(v_array_2851_, v___x_2866_);
v___x_2869_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2870_ = lean_uint8_dec_eq(v___x_2868_, v___x_2869_);
if (v___x_2870_ == 0)
{
lean_dec(v___x_2866_);
lean_del_object(v___x_2854_);
lean_dec_ref(v_array_2851_);
lean_del_object(v___x_2824_);
lean_dec(v_res_2822_);
lean_dec_ref(v_config_2815_);
goto v___jp_2817_;
}
else
{
if (v___x_2870_ == 0)
{
lean_dec(v___x_2866_);
lean_del_object(v___x_2854_);
lean_dec_ref(v_array_2851_);
lean_del_object(v___x_2824_);
lean_dec(v_res_2822_);
lean_dec_ref(v_config_2815_);
goto v___jp_2817_;
}
else
{
lean_object* v_it_x27_2872_; 
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 1, v___x_2866_);
v_it_x27_2872_ = v___x_2854_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_array_2851_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v___x_2866_);
v_it_x27_2872_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
lean_object* v___x_2873_; 
lean_inc_ref(v_config_2815_);
v___x_2873_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2815_, v_it_x27_2872_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_res_2874_; lean_object* v_pos_2875_; lean_object* v_fst_2876_; lean_object* v_snd_2877_; lean_object* v_array_2878_; lean_object* v_idx_2879_; lean_object* v___x_2880_; uint8_t v___x_2881_; 
v_res_2874_ = lean_ctor_get(v___x_2873_, 1);
lean_inc(v_res_2874_);
v_pos_2875_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_pos_2875_);
lean_dec_ref(v___x_2873_);
v_fst_2876_ = lean_ctor_get(v_res_2874_, 0);
lean_inc(v_fst_2876_);
v_snd_2877_ = lean_ctor_get(v_res_2874_, 1);
lean_inc(v_snd_2877_);
lean_dec(v_res_2874_);
v_array_2878_ = lean_ctor_get(v_pos_2875_, 0);
v_idx_2879_ = lean_ctor_get(v_pos_2875_, 1);
lean_inc(v_idx_2879_);
v___x_2880_ = lean_byte_array_size(v_array_2878_);
v___x_2881_ = lean_nat_dec_lt(v_idx_2879_, v___x_2880_);
if (v___x_2881_ == 0)
{
lean_object* v___x_2882_; 
lean_dec_ref(v_config_2815_);
v___x_2882_ = lean_box(0);
lean_inc(v_idx_2879_);
v___y_2838_ = v_fst_2876_;
v_idx_2839_ = v_idx_2879_;
v___y_2840_ = v_snd_2877_;
v_pos_2841_ = v_pos_2875_;
v_idx_2842_ = v_idx_2879_;
v_err_2843_ = v___x_2882_;
goto v___jp_2837_;
}
else
{
uint8_t v___x_2883_; uint8_t v_c_2884_; uint8_t v___x_2885_; 
v___x_2883_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_c_2884_ = lean_byte_array_fget(v_array_2878_, v_idx_2879_);
v___x_2885_ = lean_uint8_dec_eq(v_c_2884_, v___x_2883_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2886_; 
lean_dec_ref(v_config_2815_);
v___x_2886_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_2879_);
v___y_2838_ = v_fst_2876_;
v_idx_2839_ = v_idx_2879_;
v___y_2840_ = v_snd_2877_;
v_pos_2841_ = v_pos_2875_;
v_idx_2842_ = v_idx_2879_;
v_err_2843_ = v___x_2886_;
goto v___jp_2837_;
}
else
{
lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2900_; 
lean_inc_ref(v_array_2878_);
v_isSharedCheck_2900_ = !lean_is_exclusive(v_pos_2875_);
if (v_isSharedCheck_2900_ == 0)
{
lean_object* v_unused_2901_; lean_object* v_unused_2902_; 
v_unused_2901_ = lean_ctor_get(v_pos_2875_, 1);
lean_dec(v_unused_2901_);
v_unused_2902_ = lean_ctor_get(v_pos_2875_, 0);
lean_dec(v_unused_2902_);
v___x_2888_ = v_pos_2875_;
v_isShared_2889_ = v_isSharedCheck_2900_;
goto v_resetjp_2887_;
}
else
{
lean_dec(v_pos_2875_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2900_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2890_; lean_object* v_it_x27_2892_; 
v___x_2890_ = lean_nat_add(v_idx_2879_, v___x_2865_);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 1, v___x_2890_);
v_it_x27_2892_ = v___x_2888_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_array_2878_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v___x_2890_);
v_it_x27_2892_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
lean_object* v___x_2893_; 
v___x_2893_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2815_, v_it_x27_2892_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_pos_2894_; lean_object* v_res_2895_; 
lean_dec(v_idx_2879_);
lean_dec_ref(v_a_2816_);
v_pos_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_pos_2894_);
v_res_2895_ = lean_ctor_get(v___x_2893_, 1);
lean_inc(v_res_2895_);
lean_dec_ref(v___x_2893_);
v___y_2827_ = v_fst_2876_;
v___y_2828_ = v_pos_2894_;
v___y_2829_ = v_snd_2877_;
v___y_2830_ = v_res_2895_;
goto v___jp_2826_;
}
else
{
lean_object* v_pos_2896_; lean_object* v_err_2897_; lean_object* v_idx_2898_; 
v_pos_2896_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_pos_2896_);
v_err_2897_ = lean_ctor_get(v___x_2893_, 1);
lean_inc(v_err_2897_);
lean_dec_ref(v___x_2893_);
v_idx_2898_ = lean_ctor_get(v_pos_2896_, 1);
lean_inc(v_idx_2898_);
v___y_2838_ = v_fst_2876_;
v_idx_2839_ = v_idx_2879_;
v___y_2840_ = v_snd_2877_;
v_pos_2841_ = v_pos_2896_;
v_idx_2842_ = v_idx_2898_;
v_err_2843_ = v_err_2897_;
goto v___jp_2837_;
}
}
}
}
}
}
else
{
lean_object* v_err_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
lean_del_object(v___x_2824_);
lean_dec(v_res_2822_);
lean_dec_ref(v_config_2815_);
v_err_2903_ = lean_ctor_get(v___x_2873_, 1);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2910_ == 0)
{
lean_object* v_unused_2911_; 
v_unused_2911_ = lean_ctor_get(v___x_2873_, 0);
lean_dec(v_unused_2911_);
v___x_2905_ = v___x_2873_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_err_2903_);
lean_dec(v___x_2873_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 0, v_a_2816_);
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_a_2816_);
lean_ctor_set(v_reuseFailAlloc_2909_, 1, v_err_2903_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
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
lean_object* v_err_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
lean_dec_ref(v_config_2815_);
v_err_2919_ = lean_ctor_get(v___x_2820_, 1);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2926_ == 0)
{
lean_object* v_unused_2927_; 
v_unused_2927_ = lean_ctor_get(v___x_2820_, 0);
lean_dec(v_unused_2927_);
v___x_2921_ = v___x_2820_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_err_2919_);
lean_dec(v___x_2820_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 0, v_a_2816_);
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2816_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v_err_2919_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
v___jp_2817_:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2818_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1));
v___x_2819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2819_, 0, v_a_2816_);
lean_ctor_set(v___x_2819_, 1, v___x_2818_);
return v___x_2819_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(lean_object* v_config_2928_, lean_object* v_a_2929_){
_start:
{
lean_object* v___x_2930_; 
lean_inc_ref(v_a_2929_);
v___x_2930_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_2928_, v_a_2929_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_pos_2931_; lean_object* v_res_2932_; lean_object* v___x_2933_; 
v_pos_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_pos_2931_);
v_res_2932_ = lean_ctor_get(v___x_2930_, 1);
lean_inc(v_res_2932_);
lean_dec_ref(v___x_2930_);
v___x_2933_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(v_config_2928_, v_res_2932_, v_pos_2931_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_dec_ref(v_a_2929_);
return v___x_2933_;
}
else
{
lean_object* v_err_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
v_err_2934_ = lean_ctor_get(v___x_2933_, 1);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2941_ == 0)
{
lean_object* v_unused_2942_; 
v_unused_2942_ = lean_ctor_get(v___x_2933_, 0);
lean_dec(v_unused_2942_);
v___x_2936_ = v___x_2933_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_err_2934_);
lean_dec(v___x_2933_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 0, v_a_2929_);
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2929_);
lean_ctor_set(v_reuseFailAlloc_2940_, 1, v_err_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
else
{
lean_object* v_err_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_dec_ref(v_config_2928_);
v_err_2943_ = lean_ctor_get(v___x_2930_, 1);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2950_ == 0)
{
lean_object* v_unused_2951_; 
v_unused_2951_ = lean_ctor_get(v___x_2930_, 0);
lean_dec(v_unused_2951_);
v___x_2945_ = v___x_2930_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_err_2943_);
lean_dec(v___x_2930_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 0, v_a_2929_);
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2929_);
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(lean_object* v_config_2952_, lean_object* v_a_2953_){
_start:
{
lean_object* v___x_2954_; 
lean_inc_ref(v_a_2953_);
v___x_2954_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_2952_, v_a_2953_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_pos_2955_; lean_object* v_res_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_3008_; 
v_pos_2955_ = lean_ctor_get(v___x_2954_, 0);
v_res_2956_ = lean_ctor_get(v___x_2954_, 1);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_2958_ = v___x_2954_;
v_isShared_2959_ = v_isSharedCheck_3008_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_res_2956_);
lean_inc(v_pos_2955_);
lean_dec(v___x_2954_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_3008_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v_array_2960_; lean_object* v_idx_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_3007_; 
v_array_2960_ = lean_ctor_get(v_pos_2955_, 0);
v_idx_2961_ = lean_ctor_get(v_pos_2955_, 1);
v_isSharedCheck_3007_ = !lean_is_exclusive(v_pos_2955_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_2963_ = v_pos_2955_;
v_isShared_2964_ = v_isSharedCheck_3007_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_idx_2961_);
lean_inc(v_array_2960_);
lean_dec(v_pos_2955_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_3007_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; uint8_t v___x_2966_; 
v___x_2965_ = lean_byte_array_size(v_array_2960_);
v___x_2966_ = lean_nat_dec_lt(v_idx_2961_, v___x_2965_);
if (v___x_2966_ == 0)
{
lean_object* v___x_2967_; lean_object* v___x_2969_; 
lean_del_object(v___x_2963_);
lean_dec(v_idx_2961_);
lean_dec_ref(v_array_2960_);
lean_dec(v_res_2956_);
v___x_2967_ = lean_box(0);
if (v_isShared_2959_ == 0)
{
lean_ctor_set_tag(v___x_2958_, 1);
lean_ctor_set(v___x_2958_, 1, v___x_2967_);
lean_ctor_set(v___x_2958_, 0, v_a_2953_);
v___x_2969_ = v___x_2958_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2953_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v___x_2967_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
else
{
uint8_t v___x_2971_; uint8_t v_c_2972_; uint8_t v___x_2973_; 
v___x_2971_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v_c_2972_ = lean_byte_array_fget(v_array_2960_, v_idx_2961_);
v___x_2973_ = lean_uint8_dec_eq(v_c_2972_, v___x_2971_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; lean_object* v___x_2976_; 
lean_del_object(v___x_2963_);
lean_dec(v_idx_2961_);
lean_dec_ref(v_array_2960_);
lean_dec(v_res_2956_);
v___x_2974_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
if (v_isShared_2959_ == 0)
{
lean_ctor_set_tag(v___x_2958_, 1);
lean_ctor_set(v___x_2958_, 1, v___x_2974_);
lean_ctor_set(v___x_2958_, 0, v_a_2953_);
v___x_2976_ = v___x_2958_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2953_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v___x_2974_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
else
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v_it_x27_2981_; 
lean_del_object(v___x_2958_);
v___x_2978_ = lean_unsigned_to_nat(1u);
v___x_2979_ = lean_nat_add(v_idx_2961_, v___x_2978_);
lean_dec(v_idx_2961_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 1, v___x_2979_);
v_it_x27_2981_ = v___x_2963_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_array_2960_);
lean_ctor_set(v_reuseFailAlloc_3006_, 1, v___x_2979_);
v_it_x27_2981_ = v_reuseFailAlloc_3006_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
lean_object* v___x_2982_; 
v___x_2982_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v_it_x27_2981_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_pos_2983_; lean_object* v_res_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2996_; 
lean_dec_ref(v_a_2953_);
v_pos_2983_ = lean_ctor_get(v___x_2982_, 0);
v_res_2984_ = lean_ctor_get(v___x_2982_, 1);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2986_ = v___x_2982_;
v_isShared_2987_ = v_isSharedCheck_2996_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_res_2984_);
lean_inc(v_pos_2983_);
lean_dec(v___x_2982_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2996_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; uint16_t v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2994_; 
v___x_2988_ = lean_box(0);
v___x_2989_ = lean_alloc_ctor(2, 0, 2);
v___x_2990_ = lean_unbox(v_res_2984_);
lean_dec(v_res_2984_);
lean_ctor_set_uint16(v___x_2989_, 0, v___x_2990_);
v___x_2991_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2988_);
lean_ctor_set(v___x_2991_, 1, v_res_2956_);
lean_ctor_set(v___x_2991_, 2, v___x_2989_);
v___x_2992_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
if (v_isShared_2987_ == 0)
{
lean_ctor_set(v___x_2986_, 1, v___x_2992_);
v___x_2994_ = v___x_2986_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_pos_2983_);
lean_ctor_set(v_reuseFailAlloc_2995_, 1, v___x_2992_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
else
{
lean_object* v_err_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3004_; 
lean_dec(v_res_2956_);
v_err_2997_ = lean_ctor_get(v___x_2982_, 1);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3004_ == 0)
{
lean_object* v_unused_3005_; 
v_unused_3005_ = lean_ctor_get(v___x_2982_, 0);
lean_dec(v_unused_3005_);
v___x_2999_ = v___x_2982_;
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_err_2997_);
lean_dec(v___x_2982_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3002_; 
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 0, v_a_2953_);
v___x_3002_ = v___x_2999_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_a_2953_);
lean_ctor_set(v_reuseFailAlloc_3003_, 1, v_err_2997_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
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
lean_object* v_err_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
v_err_3009_ = lean_ctor_get(v___x_2954_, 1);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_3016_ == 0)
{
lean_object* v_unused_3017_; 
v_unused_3017_ = lean_ctor_get(v___x_2954_, 0);
lean_dec(v_unused_3017_);
v___x_3011_ = v___x_2954_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_err_3009_);
lean_dec(v___x_2954_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 0, v_a_2953_);
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_2953_);
lean_ctor_set(v_reuseFailAlloc_3015_, 1, v_err_3009_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority___boxed(lean_object* v_config_3018_, lean_object* v_a_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3018_, v_a_3019_);
lean_dec_ref(v_config_3018_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object* v_config_3021_, lean_object* v_a_3022_){
_start:
{
lean_object* v___x_3023_; 
lean_inc_ref(v_a_3022_);
v___x_3023_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(v_a_3022_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_dec_ref(v_a_3022_);
lean_dec_ref(v_config_3021_);
return v___x_3023_;
}
else
{
lean_object* v_pos_3024_; lean_object* v_idx_3025_; lean_object* v_idx_3026_; uint8_t v___x_3027_; 
v_pos_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc(v_pos_3024_);
v_idx_3025_ = lean_ctor_get(v_a_3022_, 1);
lean_inc(v_idx_3025_);
lean_dec_ref(v_a_3022_);
v_idx_3026_ = lean_ctor_get(v_pos_3024_, 1);
lean_inc(v_idx_3026_);
v___x_3027_ = lean_nat_dec_eq(v_idx_3025_, v_idx_3026_);
lean_dec(v_idx_3025_);
if (v___x_3027_ == 0)
{
lean_dec(v_idx_3026_);
lean_dec(v_pos_3024_);
lean_dec_ref(v_config_3021_);
return v___x_3023_;
}
else
{
lean_object* v___x_3028_; 
lean_dec_ref(v___x_3023_);
lean_inc_ref(v_config_3021_);
v___x_3028_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(v_config_3021_, v_pos_3024_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_dec(v_idx_3026_);
lean_dec_ref(v_config_3021_);
return v___x_3028_;
}
else
{
lean_object* v_pos_3029_; lean_object* v_idx_3030_; uint8_t v___x_3031_; 
v_pos_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_pos_3029_);
v_idx_3030_ = lean_ctor_get(v_pos_3029_, 1);
lean_inc(v_idx_3030_);
v___x_3031_ = lean_nat_dec_eq(v_idx_3026_, v_idx_3030_);
lean_dec(v_idx_3026_);
if (v___x_3031_ == 0)
{
lean_dec(v_idx_3030_);
lean_dec(v_pos_3029_);
lean_dec_ref(v_config_3021_);
return v___x_3028_;
}
else
{
lean_object* v___x_3032_; 
lean_dec_ref(v___x_3028_);
lean_inc_ref(v_config_3021_);
v___x_3032_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(v_config_3021_, v_pos_3029_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_dec(v_idx_3030_);
lean_dec_ref(v_config_3021_);
return v___x_3032_;
}
else
{
lean_object* v_pos_3033_; lean_object* v_idx_3034_; uint8_t v___x_3035_; 
v_pos_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_pos_3033_);
v_idx_3034_ = lean_ctor_get(v_pos_3033_, 1);
lean_inc(v_idx_3034_);
v___x_3035_ = lean_nat_dec_eq(v_idx_3030_, v_idx_3034_);
lean_dec(v_idx_3030_);
if (v___x_3035_ == 0)
{
lean_dec(v_idx_3034_);
lean_dec(v_pos_3033_);
lean_dec_ref(v_config_3021_);
return v___x_3032_;
}
else
{
lean_object* v___x_3036_; 
lean_dec_ref(v___x_3032_);
v___x_3036_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3021_, v_pos_3033_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_dec(v_idx_3034_);
lean_dec_ref(v_config_3021_);
return v___x_3036_;
}
else
{
lean_object* v_pos_3037_; lean_object* v_idx_3038_; uint8_t v___x_3039_; 
v_pos_3037_ = lean_ctor_get(v___x_3036_, 0);
lean_inc(v_pos_3037_);
v_idx_3038_ = lean_ctor_get(v_pos_3037_, 1);
v___x_3039_ = lean_nat_dec_eq(v_idx_3034_, v_idx_3038_);
lean_dec(v_idx_3034_);
if (v___x_3039_ == 0)
{
lean_dec(v_pos_3037_);
lean_dec_ref(v_config_3021_);
return v___x_3036_;
}
else
{
lean_object* v___x_3040_; 
lean_dec_ref(v___x_3036_);
v___x_3040_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(v_config_3021_, v_pos_3037_);
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
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader(lean_object* v_config_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v___y_3050_; lean_object* v___x_3053_; 
v___x_3053_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3047_, v_a_3048_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_pos_3054_; lean_object* v_res_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3128_; 
v_pos_3054_ = lean_ctor_get(v___x_3053_, 0);
v_res_3055_ = lean_ctor_get(v___x_3053_, 1);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3057_ = v___x_3053_;
v_isShared_3058_ = v_isSharedCheck_3128_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_res_3055_);
lean_inc(v_pos_3054_);
lean_dec(v___x_3053_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3128_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v_port_3060_; lean_object* v___y_3061_; lean_object* v_pos_3075_; lean_object* v_array_3077_; lean_object* v_idx_3078_; lean_object* v___x_3079_; uint8_t v___x_3080_; lean_object* v___y_3082_; lean_object* v_array_3083_; lean_object* v_idx_3084_; 
v_array_3077_ = lean_ctor_get(v_pos_3054_, 0);
v_idx_3078_ = lean_ctor_get(v_pos_3054_, 1);
v___x_3079_ = lean_byte_array_size(v_array_3077_);
v___x_3080_ = lean_nat_dec_lt(v_idx_3078_, v___x_3079_);
if (v___x_3080_ == 0)
{
v_pos_3075_ = v_pos_3054_;
goto v___jp_3074_;
}
else
{
uint8_t v___x_3088_; uint8_t v___x_3089_; uint8_t v___x_3090_; 
v___x_3088_ = lean_byte_array_fget(v_array_3077_, v_idx_3078_);
v___x_3089_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_3090_ = lean_uint8_dec_eq(v___x_3088_, v___x_3089_);
if (v___x_3090_ == 0)
{
v_pos_3075_ = v_pos_3054_;
goto v___jp_3074_;
}
else
{
if (v___x_3090_ == 0)
{
v_pos_3075_ = v_pos_3054_;
goto v___jp_3074_;
}
else
{
if (v___x_3080_ == 0)
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
lean_del_object(v___x_3057_);
lean_dec(v_res_3055_);
v___x_3091_ = lean_box(0);
v___x_3092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3092_, 0, v_pos_3054_);
lean_ctor_set(v___x_3092_, 1, v___x_3091_);
return v___x_3092_;
}
else
{
if (v___x_3090_ == 0)
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
lean_del_object(v___x_3057_);
lean_dec(v_res_3055_);
v___x_3093_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
v___x_3094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3094_, 0, v_pos_3054_);
lean_ctor_set(v___x_3094_, 1, v___x_3093_);
return v___x_3094_;
}
else
{
lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3125_; 
lean_inc(v_idx_3078_);
lean_inc_ref(v_array_3077_);
v_isSharedCheck_3125_ = !lean_is_exclusive(v_pos_3054_);
if (v_isSharedCheck_3125_ == 0)
{
lean_object* v_unused_3126_; lean_object* v_unused_3127_; 
v_unused_3126_ = lean_ctor_get(v_pos_3054_, 1);
lean_dec(v_unused_3126_);
v_unused_3127_ = lean_ctor_get(v_pos_3054_, 0);
lean_dec(v_unused_3127_);
v___x_3096_ = v_pos_3054_;
v_isShared_3097_ = v_isSharedCheck_3125_;
goto v_resetjp_3095_;
}
else
{
lean_dec(v_pos_3054_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3125_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v_it_x27_3101_; 
v___x_3098_ = lean_unsigned_to_nat(1u);
v___x_3099_ = lean_nat_add(v_idx_3078_, v___x_3098_);
lean_dec(v_idx_3078_);
lean_inc(v___x_3099_);
lean_inc_ref(v_array_3077_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 1, v___x_3099_);
v_it_x27_3101_ = v___x_3096_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_array_3077_);
lean_ctor_set(v_reuseFailAlloc_3124_, 1, v___x_3099_);
v_it_x27_3101_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
uint8_t v___y_3103_; uint8_t v___x_3118_; 
v___x_3118_ = lean_nat_dec_lt(v___x_3099_, v___x_3079_);
if (v___x_3118_ == 0)
{
v___y_3082_ = v_it_x27_3101_;
v_array_3083_ = v_array_3077_;
v_idx_3084_ = v___x_3099_;
goto v___jp_3081_;
}
else
{
uint8_t v___x_3119_; uint8_t v___x_3120_; uint8_t v___x_3121_; 
v___x_3119_ = lean_byte_array_fget(v_array_3077_, v___x_3099_);
v___x_3120_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__3);
v___x_3121_ = lean_uint8_dec_le(v___x_3120_, v___x_3119_);
if (v___x_3121_ == 0)
{
v___y_3103_ = v___x_3121_;
goto v___jp_3102_;
}
else
{
uint8_t v___x_3122_; uint8_t v___x_3123_; 
v___x_3122_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__2___closed__4);
v___x_3123_ = lean_uint8_dec_le(v___x_3119_, v___x_3122_);
v___y_3103_ = v___x_3123_;
goto v___jp_3102_;
}
}
v___jp_3102_:
{
if (v___y_3103_ == 0)
{
v___y_3082_ = v_it_x27_3101_;
v_array_3083_ = v_array_3077_;
v_idx_3084_ = v___x_3099_;
goto v___jp_3081_;
}
else
{
if (v___x_3080_ == 0)
{
v___y_3082_ = v_it_x27_3101_;
v_array_3083_ = v_array_3077_;
v_idx_3084_ = v___x_3099_;
goto v___jp_3081_;
}
else
{
lean_object* v___x_3104_; 
lean_dec(v___x_3099_);
lean_dec_ref(v_array_3077_);
v___x_3104_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v_it_x27_3101_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_pos_3105_; lean_object* v_res_3106_; lean_object* v___x_3107_; uint16_t v___x_3108_; 
v_pos_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_pos_3105_);
v_res_3106_ = lean_ctor_get(v___x_3104_, 1);
lean_inc(v_res_3106_);
lean_dec_ref(v___x_3104_);
v___x_3107_ = lean_alloc_ctor(2, 0, 2);
v___x_3108_ = lean_unbox(v_res_3106_);
lean_dec(v_res_3106_);
lean_ctor_set_uint16(v___x_3107_, 0, v___x_3108_);
v_port_3060_ = v___x_3107_;
v___y_3061_ = v_pos_3105_;
goto v___jp_3059_;
}
else
{
lean_object* v_pos_3109_; lean_object* v_err_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_del_object(v___x_3057_);
lean_dec(v_res_3055_);
v_pos_3109_ = lean_ctor_get(v___x_3104_, 0);
v_err_3110_ = lean_ctor_get(v___x_3104_, 1);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3104_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_err_3110_);
lean_inc(v_pos_3109_);
lean_dec(v___x_3104_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_pos_3109_);
lean_ctor_set(v_reuseFailAlloc_3116_, 1, v_err_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
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
v___jp_3059_:
{
lean_object* v_array_3062_; lean_object* v_idx_3063_; lean_object* v___x_3064_; uint8_t v___x_3065_; 
v_array_3062_ = lean_ctor_get(v___y_3061_, 0);
v_idx_3063_ = lean_ctor_get(v___y_3061_, 1);
v___x_3064_ = lean_byte_array_size(v_array_3062_);
v___x_3065_ = lean_nat_dec_lt(v_idx_3063_, v___x_3064_);
if (v___x_3065_ == 0)
{
lean_object* v___x_3066_; lean_object* v___x_3068_; 
v___x_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3066_, 0, v_res_3055_);
lean_ctor_set(v___x_3066_, 1, v_port_3060_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 1, v___x_3066_);
lean_ctor_set(v___x_3057_, 0, v___y_3061_);
v___x_3068_ = v___x_3057_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v___y_3061_);
lean_ctor_set(v_reuseFailAlloc_3069_, 1, v___x_3066_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
else
{
lean_object* v___x_3070_; lean_object* v___x_3072_; 
lean_dec(v_port_3060_);
lean_dec(v_res_3055_);
v___x_3070_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__3));
if (v_isShared_3058_ == 0)
{
lean_ctor_set_tag(v___x_3057_, 1);
lean_ctor_set(v___x_3057_, 1, v___x_3070_);
lean_ctor_set(v___x_3057_, 0, v___y_3061_);
v___x_3072_ = v___x_3057_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v___y_3061_);
lean_ctor_set(v_reuseFailAlloc_3073_, 1, v___x_3070_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
v___jp_3074_:
{
lean_object* v___x_3076_; 
v___x_3076_ = lean_box(0);
v_port_3060_ = v___x_3076_;
v___y_3061_ = v_pos_3075_;
goto v___jp_3059_;
}
v___jp_3081_:
{
lean_object* v___x_3085_; uint8_t v___x_3086_; 
v___x_3085_ = lean_byte_array_size(v_array_3083_);
lean_dec_ref(v_array_3083_);
v___x_3086_ = lean_nat_dec_lt(v_idx_3084_, v___x_3085_);
lean_dec(v_idx_3084_);
if (v___x_3086_ == 0)
{
if (v___x_3080_ == 0)
{
lean_del_object(v___x_3057_);
lean_dec(v_res_3055_);
v___y_3050_ = v___y_3082_;
goto v___jp_3049_;
}
else
{
lean_object* v___x_3087_; 
v___x_3087_ = lean_box(1);
v_port_3060_ = v___x_3087_;
v___y_3061_ = v___y_3082_;
goto v___jp_3059_;
}
}
else
{
lean_del_object(v___x_3057_);
lean_dec(v_res_3055_);
v___y_3050_ = v___y_3082_;
goto v___jp_3049_;
}
}
}
}
else
{
lean_object* v_pos_3129_; lean_object* v_err_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3137_; 
v_pos_3129_ = lean_ctor_get(v___x_3053_, 0);
v_err_3130_ = lean_ctor_get(v___x_3053_, 1);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3132_ = v___x_3053_;
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_err_3130_);
lean_inc(v_pos_3129_);
lean_dec(v___x_3053_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3135_; 
if (v_isShared_3133_ == 0)
{
v___x_3135_ = v___x_3132_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_pos_3129_);
lean_ctor_set(v_reuseFailAlloc_3136_, 1, v_err_3130_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
v___jp_3049_:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3051_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__1));
v___x_3052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___y_3050_);
lean_ctor_set(v___x_3052_, 1, v___x_3051_);
return v___x_3052_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader___boxed(lean_object* v_config_3138_, lean_object* v_a_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_Std_Http_URI_Parser_parseHostHeader(v_config_3138_, v_a_3139_);
lean_dec_ref(v_config_3138_);
return v_res_3140_;
}
}
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec_ByteArray(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_URI_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_URI_Config(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Data_URI_Parser(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String(builtin);
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
lean_object* initialize_Init_Data_String(uint8_t builtin);
lean_object* initialize_Std_Internal_Parsec(uint8_t builtin);
lean_object* initialize_Std_Internal_Parsec_ByteArray(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_URI_Basic(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_URI_Config(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Data_URI_Parser(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String(builtin);
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
