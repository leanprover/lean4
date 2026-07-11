// Lean compiler output
// Module: Std.Http.Protocol.H1.Parser
// Imports: public import Std.Internal.Parsec public import Std.Http.Data public import Std.Internal.Parsec.ByteArray public import Std.Http.Protocol.H1.Config
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
uint32_t lean_uint8_to_uint32(uint8_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes___boxed(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
extern lean_object* l_Std_Http_Headers_empty;
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_string_data(lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
lean_object* l_Std_Http_Status_ofCode(lean_object*, uint16_t);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_toByteSlice(lean_object*, lean_object*, lean_object*);
lean_object* l_ByteSlice_toByteArray(lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
uint8_t lean_uint8_add(uint8_t, uint8_t);
lean_object* l_Char_quote(uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_ByteSlice_size(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_ByteArray_Iterator_remainingBytes(lean_object*);
lean_object* l_Std_Http_Chunk_ExtensionValue_ofString_x3f(lean_object*);
lean_object* l_Std_Http_Chunk_ExtensionName_ofString_x3f(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_take(lean_object*, lean_object*);
lean_object* l_Std_Http_Version_ofNumber_x3f(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte___boxed(lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "end of items"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "too many items: "};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__2_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " > "};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "expected value but got none"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected at least one char"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__1_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__1_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__0_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf(lean_object*);
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "too many leading empty lines"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__1_value)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "expected: '"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__2;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__3;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__4;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__5 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__5_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__6;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp(lean_object*);
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__0_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid space sequence"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__1;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__2;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "invalid hex digit "};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__5 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__5_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__6;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit(lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "expected hex digit"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "chunk size too large"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__2_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__2_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "HTTP/"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__0_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "digit expected"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__2_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__2_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__6;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__7;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__8;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__9;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersion(lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39___boxed(lean_object*);
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__0_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__1_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__5 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__5_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__8 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__8_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__9 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__9_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__12 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__12_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__13 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__13_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__16 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__16_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__17 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__17_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "unrecognized method"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__20 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__20_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__20_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__21 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__21_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "VERSION-CONTROL"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__25 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__25_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UPDATE"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "UPDATEREDIRECTREF"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__29 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__29_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__32 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__32_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLOCK"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__33 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__33_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLINK"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__36 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__36_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "UNCHECKOUT"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__40 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__40_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNBIND"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REPORT"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REBIND"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__53 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__53_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PROPPATCH"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "PROPFIND"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__57 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__57_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__60 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__60_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PRI"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__61 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__61_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PATCH"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__64 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__64_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PUT"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__68 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__68_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "POST"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ORDERPATCH"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OPTIONS"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__81 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__81_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "MOVE"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MKWORKSPACE"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__85 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__85_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__88 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__88_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "MKREDIRECTREF"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__89 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__89_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MKCOL"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__92 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__92_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKCALENDAR"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__96 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__96_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKACTIVITY"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MERGE"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LOCK"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__109 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__109_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LINK"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "LABEL"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__113 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__113_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__116 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__116_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COPY"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__117 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__117_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CHECKOUT"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__120 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__120_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CHECKIN"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__124 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__124_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CONNECT"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "BIND"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "BASELINE-CONTROL"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__137 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__137_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "SEARCH"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "QUERY"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__141 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__141_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__144_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__144 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__144_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ACL"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__145 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__145_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__148_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "TRACE"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__148 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__148_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "DELETE"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__152 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__152_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GET"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__0_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "uri too long"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__1_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__1_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "expected end of input"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*9 + 0, .m_other = 9, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(253) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(256) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(128) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(100) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___closed__0_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___closed__0_value)} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_parseRequestLine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "unsupported HTTP version"};
static const lean_object* l_Std_Http_Protocol_H1_parseRequestLine___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_parseRequestLine___closed__0_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_parseRequestLine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_parseRequestLine___closed__0_value)}};
static const lean_object* l_Std_Http_Protocol_H1_parseRequestLine___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_parseRequestLine___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0(uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__5;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Protocol_H1_parseSingleHeader___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_parseSingleHeader___closed__0;
static lean_once_cell_t l_Std_Http_Protocol_H1_parseSingleHeader___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Protocol_H1_parseSingleHeader___closed__1;
static lean_once_cell_t l_Std_Http_Protocol_H1_parseSingleHeader___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_parseSingleHeader___closed__2;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__3;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__4;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__5;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "invalid quoted-pair byte: "};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__6 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__6_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair(lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "quoted-string too long"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid qdtext byte: "};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__0;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__2;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__3;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__4;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__1(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__3(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__3___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "invalid extension value"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__8;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid extension name"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__9 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__9_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__9_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__10 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__10_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__11;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__12;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__13;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__14;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__15;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__16;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkPartial(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "host"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "connection"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "expect"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "te"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "authorization"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "max-forwards"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__5 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__5_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "cache-control"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__6 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__6_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "content-encoding"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__7 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__7_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "upgrade"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__8 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__8_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trailer"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__9 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__9_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "content-length"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__10 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__10_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "transfer-encoding"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__11 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__11_value;
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___boxed(lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "forbidden trailer field: "};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailers(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "invalid status code"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseLastChunkBody(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar(uint8_t v_c_1_){
_start:
{
uint32_t v___x_2_; uint32_t v___x_8_; uint8_t v___x_9_; 
v___x_2_ = lean_uint8_to_uint32(v_c_1_);
v___x_8_ = 33;
v___x_9_ = lean_uint32_dec_le(v___x_8_, v___x_2_);
if (v___x_9_ == 0)
{
goto v___jp_3_;
}
else
{
uint32_t v___x_10_; uint8_t v___x_11_; 
v___x_10_ = 126;
v___x_11_ = lean_uint32_dec_le(v___x_2_, v___x_10_);
if (v___x_11_ == 0)
{
goto v___jp_3_;
}
else
{
return v___x_11_;
}
}
v___jp_3_:
{
uint32_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = 32;
v___x_5_ = lean_uint32_dec_eq(v___x_2_, v___x_4_);
if (v___x_5_ == 0)
{
uint32_t v___x_6_; uint8_t v___x_7_; 
v___x_6_ = 9;
v___x_7_ = lean_uint32_dec_eq(v___x_2_, v___x_6_);
return v___x_7_;
}
else
{
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar___boxed(lean_object* v_c_12_){
_start:
{
uint8_t v_c_boxed_13_; uint8_t v_res_14_; lean_object* v_r_15_; 
v_c_boxed_13_ = lean_unbox(v_c_12_);
v_res_14_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar(v_c_boxed_13_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText(uint8_t v_c_16_){
_start:
{
uint32_t v___x_17_; uint32_t v___x_23_; uint8_t v___x_24_; 
v___x_17_ = lean_uint8_to_uint32(v_c_16_);
v___x_23_ = 9;
v___x_24_ = lean_uint32_dec_eq(v___x_17_, v___x_23_);
if (v___x_24_ == 0)
{
uint32_t v___x_25_; uint8_t v___x_26_; 
v___x_25_ = 32;
v___x_26_ = lean_uint32_dec_eq(v___x_17_, v___x_25_);
if (v___x_26_ == 0)
{
uint32_t v___x_27_; uint8_t v___x_28_; 
v___x_27_ = 33;
v___x_28_ = lean_uint32_dec_eq(v___x_17_, v___x_27_);
if (v___x_28_ == 0)
{
uint32_t v___x_29_; uint8_t v___x_30_; 
v___x_29_ = 35;
v___x_30_ = lean_uint32_dec_le(v___x_29_, v___x_17_);
if (v___x_30_ == 0)
{
goto v___jp_18_;
}
else
{
uint32_t v___x_31_; uint8_t v___x_32_; 
v___x_31_ = 91;
v___x_32_ = lean_uint32_dec_le(v___x_17_, v___x_31_);
if (v___x_32_ == 0)
{
goto v___jp_18_;
}
else
{
return v___x_32_;
}
}
}
else
{
return v___x_28_;
}
}
else
{
return v___x_26_;
}
}
else
{
return v___x_24_;
}
v___jp_18_:
{
uint32_t v___x_19_; uint8_t v___x_20_; 
v___x_19_ = 93;
v___x_20_ = lean_uint32_dec_le(v___x_19_, v___x_17_);
if (v___x_20_ == 0)
{
return v___x_20_;
}
else
{
uint32_t v___x_21_; uint8_t v___x_22_; 
v___x_21_ = 126;
v___x_22_ = lean_uint32_dec_le(v___x_17_, v___x_21_);
return v___x_22_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText___boxed(lean_object* v_c_33_){
_start:
{
uint8_t v_c_boxed_34_; uint8_t v_res_35_; lean_object* v_r_36_; 
v_c_boxed_34_ = lean_unbox(v_c_33_);
v_res_35_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText(v_c_boxed_34_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte(uint8_t v_c_37_){
_start:
{
uint32_t v___x_38_; uint32_t v___x_39_; uint8_t v___x_40_; 
v___x_38_ = lean_uint8_to_uint32(v_c_37_);
v___x_39_ = 32;
v___x_40_ = lean_uint32_dec_eq(v___x_38_, v___x_39_);
if (v___x_40_ == 0)
{
uint32_t v___x_41_; uint8_t v___x_42_; 
v___x_41_ = 9;
v___x_42_ = lean_uint32_dec_eq(v___x_38_, v___x_41_);
return v___x_42_;
}
else
{
return v___x_40_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte___boxed(lean_object* v_c_43_){
_start:
{
uint8_t v_c_boxed_44_; uint8_t v_res_45_; lean_object* v_r_46_; 
v_c_boxed_44_ = lean_unbox(v_c_43_);
v_res_45_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte(v_c_boxed_44_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(lean_object* v_parser_52_, lean_object* v_maxCount_53_, lean_object* v_acc_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_pos_57_; lean_object* v_err_58_; lean_object* v___x_73_; 
lean_inc_ref(v_parser_52_);
lean_inc_ref(v_a_55_);
v___x_73_ = lean_apply_1(v_parser_52_, v_a_55_);
if (lean_obj_tag(v___x_73_) == 0)
{
lean_object* v_res_74_; 
v_res_74_ = lean_ctor_get(v___x_73_, 1);
lean_inc(v_res_74_);
if (lean_obj_tag(v_res_74_) == 0)
{
lean_object* v___x_75_; 
lean_dec_ref_known(v___x_73_, 2);
lean_dec(v_maxCount_53_);
lean_dec_ref(v_parser_52_);
v___x_75_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__1));
lean_inc_ref(v_a_55_);
v_pos_57_ = v_a_55_;
v_err_58_ = v___x_75_;
goto v___jp_56_;
}
else
{
lean_object* v_pos_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_102_; 
lean_dec_ref(v_a_55_);
v_pos_76_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; 
v_unused_103_ = lean_ctor_get(v___x_73_, 1);
lean_dec(v_unused_103_);
v___x_78_ = v___x_73_;
v_isShared_79_ = v_isSharedCheck_102_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_pos_76_);
lean_dec(v___x_73_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_102_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v_val_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_101_; 
v_val_80_ = lean_ctor_get(v_res_74_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v_res_74_);
if (v_isSharedCheck_101_ == 0)
{
v___x_82_ = v_res_74_;
v_isShared_83_ = v_isSharedCheck_101_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_val_80_);
lean_dec(v_res_74_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_101_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_84_ = lean_array_push(v_acc_54_, v_val_80_);
v___x_85_ = lean_array_get_size(v___x_84_);
v___x_86_ = lean_nat_dec_lt(v_maxCount_53_, v___x_85_);
if (v___x_86_ == 0)
{
lean_del_object(v___x_82_);
lean_del_object(v___x_78_);
v_acc_54_ = v___x_84_;
v_a_55_ = v_pos_76_;
goto _start;
}
else
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_96_; 
lean_dec_ref(v___x_84_);
lean_dec_ref(v_parser_52_);
v___x_88_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__2));
v___x_89_ = l_Nat_reprFast(v___x_85_);
v___x_90_ = lean_string_append(v___x_88_, v___x_89_);
lean_dec_ref(v___x_89_);
v___x_91_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__3));
v___x_92_ = lean_string_append(v___x_90_, v___x_91_);
v___x_93_ = l_Nat_reprFast(v_maxCount_53_);
v___x_94_ = lean_string_append(v___x_92_, v___x_93_);
lean_dec_ref(v___x_93_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 0, v___x_94_);
v___x_96_ = v___x_82_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_94_);
v___x_96_ = v_reuseFailAlloc_100_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
lean_object* v___x_98_; 
if (v_isShared_79_ == 0)
{
lean_ctor_set_tag(v___x_78_, 1);
lean_ctor_set(v___x_78_, 1, v___x_96_);
v___x_98_ = v___x_78_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_pos_76_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
}
}
else
{
lean_object* v_err_104_; 
lean_dec(v_maxCount_53_);
lean_dec_ref(v_parser_52_);
v_err_104_ = lean_ctor_get(v___x_73_, 1);
lean_inc(v_err_104_);
lean_dec_ref_known(v___x_73_, 2);
lean_inc_ref(v_a_55_);
v_pos_57_ = v_a_55_;
v_err_58_ = v_err_104_;
goto v___jp_56_;
}
v___jp_56_:
{
lean_object* v_idx_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_71_; 
v_idx_59_ = lean_ctor_get(v_a_55_, 1);
v_isSharedCheck_71_ = !lean_is_exclusive(v_a_55_);
if (v_isSharedCheck_71_ == 0)
{
lean_object* v_unused_72_; 
v_unused_72_ = lean_ctor_get(v_a_55_, 0);
lean_dec(v_unused_72_);
v___x_61_ = v_a_55_;
v_isShared_62_ = v_isSharedCheck_71_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_idx_59_);
lean_dec(v_a_55_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_71_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v_idx_63_; uint8_t v___x_64_; 
v_idx_63_ = lean_ctor_get(v_pos_57_, 1);
v___x_64_ = lean_nat_dec_eq(v_idx_59_, v_idx_63_);
lean_dec(v_idx_59_);
if (v___x_64_ == 0)
{
lean_object* v___x_66_; 
lean_dec_ref(v_acc_54_);
if (v_isShared_62_ == 0)
{
lean_ctor_set_tag(v___x_61_, 1);
lean_ctor_set(v___x_61_, 1, v_err_58_);
lean_ctor_set(v___x_61_, 0, v_pos_57_);
v___x_66_ = v___x_61_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_pos_57_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v_err_58_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
else
{
lean_object* v___x_69_; 
lean_dec(v_err_58_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 1, v_acc_54_);
lean_ctor_set(v___x_61_, 0, v_pos_57_);
v___x_69_ = v___x_61_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_pos_57_);
lean_ctor_set(v_reuseFailAlloc_70_, 1, v_acc_54_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go(lean_object* v_00_u03b1_105_, lean_object* v_parser_106_, lean_object* v_maxCount_107_, lean_object* v_acc_108_, lean_object* v_a_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(v_parser_106_, v_maxCount_107_, v_acc_108_, v_a_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(lean_object* v_parser_113_, lean_object* v_maxCount_114_, lean_object* v_a_115_){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg___closed__0));
v___x_117_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(v_parser_113_, v_maxCount_114_, v___x_116_, v_a_115_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems(lean_object* v_00_u03b1_118_, lean_object* v_parser_119_, lean_object* v_maxCount_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v_parser_119_, v_maxCount_120_, v_a_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(lean_object* v_x_126_, lean_object* v_a_127_){
_start:
{
if (lean_obj_tag(v_x_126_) == 1)
{
lean_object* v_val_128_; lean_object* v___x_129_; 
v_val_128_ = lean_ctor_get(v_x_126_, 0);
lean_inc(v_val_128_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v_a_127_);
lean_ctor_set(v___x_129_, 1, v_val_128_);
return v___x_129_;
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___closed__1));
v___x_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_131_, 0, v_a_127_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___boxed(lean_object* v_x_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_x_132_, v_a_133_);
lean_dec(v_x_132_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption(lean_object* v_00_u03b1_135_, lean_object* v_x_136_, lean_object* v_a_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_x_136_, v_a_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___boxed(lean_object* v_00_u03b1_139_, lean_object* v_x_140_, lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption(v_00_u03b1_139_, v_x_140_, v_a_141_);
lean_dec(v_x_140_);
return v_res_142_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0(uint8_t v_c_143_){
_start:
{
uint32_t v___x_144_; uint8_t v___y_151_; uint32_t v___x_156_; uint8_t v___x_157_; 
v___x_144_ = lean_uint8_to_uint32(v_c_143_);
v___x_156_ = 33;
v___x_157_ = lean_uint32_dec_eq(v___x_144_, v___x_156_);
if (v___x_157_ == 0)
{
uint32_t v___x_158_; uint8_t v___x_159_; 
v___x_158_ = 35;
v___x_159_ = lean_uint32_dec_eq(v___x_144_, v___x_158_);
if (v___x_159_ == 0)
{
uint32_t v___x_160_; uint8_t v___x_161_; 
v___x_160_ = 36;
v___x_161_ = lean_uint32_dec_eq(v___x_144_, v___x_160_);
if (v___x_161_ == 0)
{
uint32_t v___x_162_; uint8_t v___x_163_; 
v___x_162_ = 37;
v___x_163_ = lean_uint32_dec_eq(v___x_144_, v___x_162_);
if (v___x_163_ == 0)
{
uint32_t v___x_164_; uint8_t v___x_165_; 
v___x_164_ = 38;
v___x_165_ = lean_uint32_dec_eq(v___x_144_, v___x_164_);
if (v___x_165_ == 0)
{
uint32_t v___x_166_; uint8_t v___x_167_; 
v___x_166_ = 39;
v___x_167_ = lean_uint32_dec_eq(v___x_144_, v___x_166_);
if (v___x_167_ == 0)
{
uint32_t v___x_168_; uint8_t v___x_169_; 
v___x_168_ = 42;
v___x_169_ = lean_uint32_dec_eq(v___x_144_, v___x_168_);
if (v___x_169_ == 0)
{
uint32_t v___x_170_; uint8_t v___x_171_; 
v___x_170_ = 43;
v___x_171_ = lean_uint32_dec_eq(v___x_144_, v___x_170_);
if (v___x_171_ == 0)
{
uint32_t v___x_172_; uint8_t v___x_173_; 
v___x_172_ = 45;
v___x_173_ = lean_uint32_dec_eq(v___x_144_, v___x_172_);
if (v___x_173_ == 0)
{
uint32_t v___x_174_; uint8_t v___x_175_; 
v___x_174_ = 46;
v___x_175_ = lean_uint32_dec_eq(v___x_144_, v___x_174_);
if (v___x_175_ == 0)
{
uint32_t v___x_176_; uint8_t v___x_177_; 
v___x_176_ = 94;
v___x_177_ = lean_uint32_dec_eq(v___x_144_, v___x_176_);
if (v___x_177_ == 0)
{
uint32_t v___x_178_; uint8_t v___x_179_; 
v___x_178_ = 95;
v___x_179_ = lean_uint32_dec_eq(v___x_144_, v___x_178_);
if (v___x_179_ == 0)
{
uint32_t v___x_180_; uint8_t v___x_181_; 
v___x_180_ = 96;
v___x_181_ = lean_uint32_dec_eq(v___x_144_, v___x_180_);
if (v___x_181_ == 0)
{
uint32_t v___x_182_; uint8_t v___x_183_; 
v___x_182_ = 124;
v___x_183_ = lean_uint32_dec_eq(v___x_144_, v___x_182_);
if (v___x_183_ == 0)
{
uint32_t v___x_184_; uint8_t v___x_185_; 
v___x_184_ = 126;
v___x_185_ = lean_uint32_dec_eq(v___x_144_, v___x_184_);
if (v___x_185_ == 0)
{
uint32_t v___x_186_; uint8_t v___x_187_; 
v___x_186_ = 48;
v___x_187_ = lean_uint32_dec_le(v___x_186_, v___x_144_);
if (v___x_187_ == 0)
{
v___y_151_ = v___x_187_;
goto v___jp_150_;
}
else
{
uint32_t v___x_188_; uint8_t v___x_189_; 
v___x_188_ = 57;
v___x_189_ = lean_uint32_dec_le(v___x_144_, v___x_188_);
v___y_151_ = v___x_189_;
goto v___jp_150_;
}
}
else
{
return v___x_185_;
}
}
else
{
return v___x_183_;
}
}
else
{
return v___x_181_;
}
}
else
{
return v___x_179_;
}
}
else
{
return v___x_177_;
}
}
else
{
return v___x_175_;
}
}
else
{
return v___x_173_;
}
}
else
{
return v___x_171_;
}
}
else
{
return v___x_169_;
}
}
else
{
return v___x_167_;
}
}
else
{
return v___x_165_;
}
}
else
{
return v___x_163_;
}
}
else
{
return v___x_161_;
}
}
else
{
return v___x_159_;
}
}
else
{
return v___x_157_;
}
v___jp_145_:
{
uint32_t v___x_146_; uint8_t v___x_147_; 
v___x_146_ = 97;
v___x_147_ = lean_uint32_dec_le(v___x_146_, v___x_144_);
if (v___x_147_ == 0)
{
return v___x_147_;
}
else
{
uint32_t v___x_148_; uint8_t v___x_149_; 
v___x_148_ = 122;
v___x_149_ = lean_uint32_dec_le(v___x_144_, v___x_148_);
return v___x_149_;
}
}
v___jp_150_:
{
if (v___y_151_ == 0)
{
uint32_t v___x_152_; uint8_t v___x_153_; 
v___x_152_ = 65;
v___x_153_ = lean_uint32_dec_le(v___x_152_, v___x_144_);
if (v___x_153_ == 0)
{
goto v___jp_145_;
}
else
{
uint32_t v___x_154_; uint8_t v___x_155_; 
v___x_154_ = 90;
v___x_155_ = lean_uint32_dec_le(v___x_144_, v___x_154_);
if (v___x_155_ == 0)
{
goto v___jp_145_;
}
else
{
return v___x_155_;
}
}
}
else
{
return v___y_151_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0___boxed(lean_object* v_c_190_){
_start:
{
uint8_t v_c_boxed_191_; uint8_t v_res_192_; lean_object* v_r_193_; 
v_c_boxed_191_ = lean_unbox(v_c_190_);
v_res_192_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0(v_c_boxed_191_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken(lean_object* v_limit_198_, lean_object* v_a_199_){
_start:
{
lean_object* v___f_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v_snd_203_; lean_object* v_snd_204_; uint8_t v___x_205_; 
v___f_200_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_201_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_199_);
v___x_202_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_200_, v_limit_198_, v___x_201_, v_a_199_);
v_snd_203_ = lean_ctor_get(v___x_202_, 1);
lean_inc(v_snd_203_);
v_snd_204_ = lean_ctor_get(v_snd_203_, 1);
v___x_205_ = lean_unbox(v_snd_204_);
if (v___x_205_ == 0)
{
lean_object* v_fst_206_; lean_object* v_fst_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_235_; 
v_fst_206_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_fst_206_);
lean_dec_ref(v___x_202_);
v_fst_207_ = lean_ctor_get(v_snd_203_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v_snd_203_);
if (v_isSharedCheck_235_ == 0)
{
lean_object* v_unused_236_; 
v_unused_236_ = lean_ctor_get(v_snd_203_, 1);
lean_dec(v_unused_236_);
v___x_209_ = v_snd_203_;
v_isShared_210_ = v_isSharedCheck_235_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_fst_207_);
lean_dec(v_snd_203_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_235_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
uint8_t v___x_211_; 
v___x_211_ = lean_nat_dec_eq(v_fst_206_, v___x_201_);
if (v___x_211_ == 0)
{
lean_object* v_array_212_; lean_object* v_idx_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_230_; 
lean_del_object(v___x_209_);
v_array_212_ = lean_ctor_get(v_a_199_, 0);
v_idx_213_ = lean_ctor_get(v_a_199_, 1);
v_isSharedCheck_230_ = !lean_is_exclusive(v_a_199_);
if (v_isSharedCheck_230_ == 0)
{
v___x_215_ = v_a_199_;
v_isShared_216_ = v_isSharedCheck_230_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_idx_213_);
lean_inc(v_array_212_);
lean_dec(v_a_199_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_230_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v_lower_218_; lean_object* v_upper_219_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___y_227_; uint8_t v___x_229_; 
v___x_224_ = lean_nat_add(v_idx_213_, v_fst_206_);
lean_dec(v_fst_206_);
v___x_225_ = lean_byte_array_size(v_array_212_);
v___x_229_ = lean_nat_dec_le(v_idx_213_, v___x_201_);
if (v___x_229_ == 0)
{
v___y_227_ = v_idx_213_;
goto v___jp_226_;
}
else
{
lean_dec(v_idx_213_);
v___y_227_ = v___x_201_;
goto v___jp_226_;
}
v___jp_217_:
{
lean_object* v___x_220_; lean_object* v___x_222_; 
v___x_220_ = l_ByteArray_toByteSlice(v_array_212_, v_lower_218_, v_upper_219_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 1, v___x_220_);
lean_ctor_set(v___x_215_, 0, v_fst_207_);
v___x_222_ = v___x_215_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_fst_207_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v___x_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
v___jp_226_:
{
uint8_t v___x_228_; 
v___x_228_ = lean_nat_dec_le(v___x_224_, v___x_225_);
if (v___x_228_ == 0)
{
lean_dec(v___x_224_);
v_lower_218_ = v___y_227_;
v_upper_219_ = v___x_225_;
goto v___jp_217_;
}
else
{
v_lower_218_ = v___y_227_;
v_upper_219_ = v___x_224_;
goto v___jp_217_;
}
}
}
}
else
{
lean_object* v___x_231_; lean_object* v___x_233_; 
lean_dec(v_fst_207_);
lean_dec(v_fst_206_);
v___x_231_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_210_ == 0)
{
lean_ctor_set_tag(v___x_209_, 1);
lean_ctor_set(v___x_209_, 1, v___x_231_);
lean_ctor_set(v___x_209_, 0, v_a_199_);
v___x_233_ = v___x_209_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_199_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
else
{
lean_object* v_fst_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_245_; 
lean_dec_ref(v___x_202_);
lean_dec_ref(v_a_199_);
v_fst_237_ = lean_ctor_get(v_snd_203_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v_snd_203_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; 
v_unused_246_ = lean_ctor_get(v_snd_203_, 1);
lean_dec(v_unused_246_);
v___x_239_ = v_snd_203_;
v_isShared_240_ = v_isSharedCheck_245_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_fst_237_);
lean_dec(v_snd_203_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_245_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; lean_object* v___x_243_; 
v___x_241_ = lean_box(0);
if (v_isShared_240_ == 0)
{
lean_ctor_set_tag(v___x_239_, 1);
lean_ctor_set(v___x_239_, 1, v___x_241_);
v___x_243_ = v___x_239_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_fst_237_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v___x_241_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___boxed(lean_object* v_limit_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken(v_limit_247_, v_a_248_);
lean_dec(v_limit_247_);
return v_res_249_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__0));
v___x_252_ = lean_string_to_utf8(v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf(lean_object* v_a_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_255_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_254_, v_a_253_);
return v___x_255_;
}
}
static uint8_t _init_l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0(void){
_start:
{
uint32_t v___x_256_; uint8_t v___x_257_; 
v___x_256_ = 13;
v___x_257_ = lean_uint32_to_uint8(v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(lean_object* v_limits_261_, lean_object* v_a_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_array_264_; lean_object* v_idx_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v_array_264_ = lean_ctor_get(v___y_263_, 0);
v_idx_265_ = lean_ctor_get(v___y_263_, 1);
v___x_266_ = lean_byte_array_size(v_array_264_);
v___x_267_ = lean_nat_dec_lt(v_idx_265_, v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v___y_263_);
lean_ctor_set(v___x_268_, 1, v_a_262_);
return v___x_268_;
}
else
{
uint8_t v___x_269_; uint8_t v___x_270_; uint8_t v___x_271_; 
v___x_269_ = lean_byte_array_fget(v_array_264_, v_idx_265_);
v___x_270_ = lean_uint8_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0);
v___x_271_ = lean_uint8_dec_eq(v___x_269_, v___x_270_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; 
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___y_263_);
lean_ctor_set(v___x_272_, 1, v_a_262_);
return v___x_272_;
}
else
{
lean_object* v_maxLeadingEmptyLines_273_; uint8_t v___x_274_; 
v_maxLeadingEmptyLines_273_ = lean_ctor_get(v_limits_261_, 9);
v___x_274_ = lean_nat_dec_le(v_maxLeadingEmptyLines_273_, v_a_262_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_276_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_275_, v___y_263_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_pos_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_pos_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_pos_277_);
lean_dec_ref_known(v___x_276_, 2);
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = lean_nat_add(v_a_262_, v___x_278_);
lean_dec(v_a_262_);
v_a_262_ = v___x_279_;
v___y_263_ = v_pos_277_;
goto _start;
}
else
{
lean_object* v_pos_281_; lean_object* v_err_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
lean_dec(v_a_262_);
v_pos_281_ = lean_ctor_get(v___x_276_, 0);
v_err_282_ = lean_ctor_get(v___x_276_, 1);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_276_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_err_282_);
lean_inc(v_pos_281_);
lean_dec(v___x_276_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_pos_281_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_err_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; 
lean_dec(v_a_262_);
v___x_290_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__2));
v___x_291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_291_, 0, v___y_263_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
return v___x_291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___boxed(lean_object* v_limits_292_, lean_object* v_a_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_292_, v_a_293_, v___y_294_);
lean_dec_ref(v_limits_292_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(lean_object* v_limits_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_count_298_; lean_object* v___x_299_; 
v_count_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_296_, v_count_298_, v_a_297_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_pos_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_308_; 
v_pos_300_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_308_ == 0)
{
lean_object* v_unused_309_; 
v_unused_309_ = lean_ctor_get(v___x_299_, 1);
lean_dec(v_unused_309_);
v___x_302_ = v___x_299_;
v_isShared_303_ = v_isSharedCheck_308_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_pos_300_);
lean_dec(v___x_299_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_308_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_306_; 
v___x_304_ = lean_box(0);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v___x_304_);
v___x_306_ = v___x_302_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_pos_300_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v___x_304_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
else
{
lean_object* v_pos_310_; lean_object* v_err_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
v_pos_310_ = lean_ctor_get(v___x_299_, 0);
v_err_311_ = lean_ctor_get(v___x_299_, 1);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_299_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_err_311_);
lean_inc(v_pos_310_);
lean_dec(v___x_299_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_pos_310_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_err_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines___boxed(lean_object* v_limits_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_319_, v_a_320_);
lean_dec_ref(v_limits_319_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0(lean_object* v_limits_322_, lean_object* v_inst_323_, lean_object* v_a_324_, lean_object* v___y_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_322_, v_a_324_, v___y_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___boxed(lean_object* v_limits_327_, lean_object* v_inst_328_, lean_object* v_a_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0(v_limits_327_, v_inst_328_, v_a_329_, v___y_330_);
lean_dec_ref(v_limits_327_);
return v_res_331_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0(void){
_start:
{
uint32_t v___x_332_; uint8_t v___x_333_; 
v___x_332_ = 32;
v___x_333_ = lean_uint32_to_uint8(v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__2(void){
_start:
{
uint8_t v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v___x_336_ = lean_uint8_to_nat(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__3(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__2);
v___x_338_ = l_Nat_reprFast(v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__4(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_339_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__3);
v___x_340_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_341_ = lean_string_append(v___x_340_, v___x_339_);
return v___x_341_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__6(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__5));
v___x_344_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__4);
v___x_345_ = lean_string_append(v___x_344_, v___x_343_);
return v___x_345_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__6, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__6_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__6);
v___x_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp(lean_object* v_a_348_){
_start:
{
lean_object* v_array_349_; lean_object* v_idx_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v_array_349_ = lean_ctor_get(v_a_348_, 0);
v_idx_350_ = lean_ctor_get(v_a_348_, 1);
v___x_351_ = lean_byte_array_size(v_array_349_);
v___x_352_ = lean_nat_dec_lt(v_idx_350_, v___x_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_box(0);
v___x_354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_354_, 0, v_a_348_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
return v___x_354_;
}
else
{
uint8_t v___x_355_; uint8_t v_got_356_; uint8_t v___x_357_; 
v___x_355_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v_got_356_ = lean_byte_array_fget(v_array_349_, v_idx_350_);
v___x_357_ = lean_uint8_dec_eq(v_got_356_, v___x_355_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7);
v___x_359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_359_, 0, v_a_348_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
return v___x_359_;
}
else
{
lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_370_; 
lean_inc(v_idx_350_);
lean_inc_ref(v_array_349_);
v_isSharedCheck_370_ = !lean_is_exclusive(v_a_348_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; lean_object* v_unused_372_; 
v_unused_371_ = lean_ctor_get(v_a_348_, 1);
lean_dec(v_unused_371_);
v_unused_372_ = lean_ctor_get(v_a_348_, 0);
lean_dec(v_unused_372_);
v___x_361_ = v_a_348_;
v_isShared_362_ = v_isSharedCheck_370_;
goto v_resetjp_360_;
}
else
{
lean_dec(v_a_348_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_370_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_363_ = lean_unsigned_to_nat(1u);
v___x_364_ = lean_nat_add(v_idx_350_, v___x_363_);
lean_dec(v_idx_350_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 1, v___x_364_);
v___x_366_ = v___x_361_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_array_349_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v___x_364_);
v___x_366_ = v_reuseFailAlloc_369_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_box(0);
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_366_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
return v___x_368_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows(lean_object* v_limits_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_pos_380_; lean_object* v_maxSpaceSequence_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v_snd_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_418_; 
v_maxSpaceSequence_383_ = lean_ctor_get(v_limits_377_, 8);
v___x_384_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__0));
v___x_385_ = lean_unsigned_to_nat(0u);
v___x_386_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___x_384_, v_maxSpaceSequence_383_, v___x_385_, v_a_378_);
v_snd_387_ = lean_ctor_get(v___x_386_, 1);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; 
v_unused_419_ = lean_ctor_get(v___x_386_, 0);
lean_dec(v_unused_419_);
v___x_389_ = v___x_386_;
v_isShared_390_ = v_isSharedCheck_418_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_snd_387_);
lean_dec(v___x_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_418_;
goto v_resetjp_388_;
}
v___jp_379_:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_box(0);
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v_pos_380_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
return v___x_382_;
}
v_resetjp_388_:
{
lean_object* v_fst_391_; lean_object* v_snd_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_417_; 
v_fst_391_ = lean_ctor_get(v_snd_387_, 0);
v_snd_392_ = lean_ctor_get(v_snd_387_, 1);
v_isSharedCheck_417_ = !lean_is_exclusive(v_snd_387_);
if (v_isSharedCheck_417_ == 0)
{
v___x_394_ = v_snd_387_;
v_isShared_395_ = v_isSharedCheck_417_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_snd_392_);
lean_inc(v_fst_391_);
lean_dec(v_snd_387_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_417_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
uint8_t v___y_397_; uint8_t v___x_402_; 
v___x_402_ = lean_unbox(v_snd_392_);
lean_dec(v_snd_392_);
if (v___x_402_ == 0)
{
lean_object* v_array_403_; lean_object* v_idx_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
lean_del_object(v___x_389_);
v_array_403_ = lean_ctor_get(v_fst_391_, 0);
v_idx_404_ = lean_ctor_get(v_fst_391_, 1);
v___x_405_ = lean_byte_array_size(v_array_403_);
v___x_406_ = lean_nat_dec_lt(v_idx_404_, v___x_405_);
if (v___x_406_ == 0)
{
lean_del_object(v___x_394_);
v_pos_380_ = v_fst_391_;
goto v___jp_379_;
}
else
{
uint8_t v___x_407_; uint32_t v___x_408_; uint32_t v___x_409_; uint8_t v___x_410_; 
v___x_407_ = lean_byte_array_fget(v_array_403_, v_idx_404_);
v___x_408_ = lean_uint8_to_uint32(v___x_407_);
v___x_409_ = 32;
v___x_410_ = lean_uint32_dec_eq(v___x_408_, v___x_409_);
if (v___x_410_ == 0)
{
uint32_t v___x_411_; uint8_t v___x_412_; 
v___x_411_ = 9;
v___x_412_ = lean_uint32_dec_eq(v___x_408_, v___x_411_);
if (v___x_412_ == 0)
{
lean_del_object(v___x_394_);
v_pos_380_ = v_fst_391_;
goto v___jp_379_;
}
else
{
v___y_397_ = v___x_406_;
goto v___jp_396_;
}
}
else
{
v___y_397_ = v___x_406_;
goto v___jp_396_;
}
}
}
else
{
lean_object* v___x_413_; lean_object* v___x_415_; 
lean_del_object(v___x_394_);
v___x_413_ = lean_box(0);
if (v_isShared_390_ == 0)
{
lean_ctor_set_tag(v___x_389_, 1);
lean_ctor_set(v___x_389_, 1, v___x_413_);
lean_ctor_set(v___x_389_, 0, v_fst_391_);
v___x_415_ = v___x_389_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_fst_391_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
v___jp_396_:
{
if (v___y_397_ == 0)
{
lean_del_object(v___x_394_);
v_pos_380_ = v_fst_391_;
goto v___jp_379_;
}
else
{
lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_398_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2));
if (v_isShared_395_ == 0)
{
lean_ctor_set_tag(v___x_394_, 1);
lean_ctor_set(v___x_394_, 1, v___x_398_);
v___x_400_ = v___x_394_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_fst_391_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___boxed(lean_object* v_limits_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows(v_limits_420_, v_a_421_);
lean_dec_ref(v_limits_420_);
return v_res_422_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0(void){
_start:
{
uint32_t v___x_423_; uint8_t v___x_424_; 
v___x_423_ = 97;
v___x_424_ = lean_uint32_to_uint8(v___x_423_);
return v___x_424_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__1(void){
_start:
{
uint32_t v___x_425_; uint8_t v___x_426_; 
v___x_425_ = 65;
v___x_426_ = lean_uint32_to_uint8(v___x_425_);
return v___x_426_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__2(void){
_start:
{
uint32_t v___x_427_; uint8_t v___x_428_; 
v___x_427_ = 70;
v___x_428_ = lean_uint32_to_uint8(v___x_427_);
return v___x_428_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3(void){
_start:
{
uint32_t v___x_429_; uint8_t v___x_430_; 
v___x_429_ = 48;
v___x_430_ = lean_uint32_to_uint8(v___x_429_);
return v___x_430_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4(void){
_start:
{
uint32_t v___x_431_; uint8_t v___x_432_; 
v___x_431_ = 57;
v___x_432_ = lean_uint32_to_uint8(v___x_431_);
return v___x_432_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__6(void){
_start:
{
uint32_t v___x_434_; uint8_t v___x_435_; 
v___x_434_ = 102;
v___x_435_ = lean_uint32_to_uint8(v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit(lean_object* v_a_436_){
_start:
{
lean_object* v_array_437_; lean_object* v_idx_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v_array_437_ = lean_ctor_get(v_a_436_, 0);
v_idx_438_ = lean_ctor_get(v_a_436_, 1);
v___x_439_ = lean_byte_array_size(v_array_437_);
v___x_440_ = lean_nat_dec_lt(v_idx_438_, v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_box(0);
v___x_442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_442_, 0, v_a_436_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
return v___x_442_;
}
else
{
lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_505_; 
lean_inc(v_idx_438_);
lean_inc_ref(v_array_437_);
v_isSharedCheck_505_ = !lean_is_exclusive(v_a_436_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; lean_object* v_unused_507_; 
v_unused_506_ = lean_ctor_get(v_a_436_, 1);
lean_dec(v_unused_506_);
v_unused_507_ = lean_ctor_get(v_a_436_, 0);
lean_dec(v_unused_507_);
v___x_444_ = v_a_436_;
v_isShared_445_ = v_isSharedCheck_505_;
goto v_resetjp_443_;
}
else
{
lean_dec(v_a_436_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_505_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
uint8_t v_c_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v_it_x27_450_; 
v_c_446_ = lean_byte_array_fget(v_array_437_, v_idx_438_);
v___x_447_ = lean_unsigned_to_nat(1u);
v___x_448_ = lean_nat_add(v_idx_438_, v___x_447_);
lean_dec(v_idx_438_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v___x_448_);
v_it_x27_450_ = v___x_444_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_array_437_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_448_);
v_it_x27_450_ = v_reuseFailAlloc_504_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
uint8_t v___y_452_; uint8_t v___y_453_; uint8_t v___y_466_; uint8_t v___y_467_; uint8_t v___y_481_; uint8_t v___y_489_; uint8_t v___y_495_; uint8_t v___x_500_; uint8_t v___x_501_; 
v___x_500_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3);
v___x_501_ = lean_uint8_dec_le(v___x_500_, v_c_446_);
if (v___x_501_ == 0)
{
v___y_495_ = v___x_501_;
goto v___jp_494_;
}
else
{
uint8_t v___x_502_; uint8_t v___x_503_; 
v___x_502_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4);
v___x_503_ = lean_uint8_dec_le(v_c_446_, v___x_502_);
v___y_495_ = v___x_503_;
goto v___jp_494_;
}
v___jp_451_:
{
if (v___y_453_ == 0)
{
uint8_t v___x_454_; uint8_t v___x_455_; uint8_t v___x_456_; uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_454_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0);
v___x_455_ = lean_uint8_sub(v_c_446_, v___x_454_);
v___x_456_ = 10;
v___x_457_ = lean_uint8_add(v___x_455_, v___x_456_);
v___x_458_ = lean_box(v___x_457_);
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v_it_x27_450_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
return v___x_459_;
}
else
{
uint8_t v___x_460_; uint8_t v___x_461_; uint8_t v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_460_ = lean_uint8_sub(v_c_446_, v___y_452_);
v___x_461_ = 10;
v___x_462_ = lean_uint8_add(v___x_460_, v___x_461_);
v___x_463_ = lean_box(v___x_462_);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v_it_x27_450_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
return v___x_464_;
}
}
v___jp_465_:
{
if (v___y_467_ == 0)
{
uint8_t v___x_468_; uint8_t v___x_469_; 
v___x_468_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__1);
v___x_469_ = lean_uint8_dec_le(v___x_468_, v_c_446_);
if (v___x_469_ == 0)
{
v___y_452_ = v___x_468_;
v___y_453_ = v___x_469_;
goto v___jp_451_;
}
else
{
uint8_t v___x_470_; uint8_t v___x_471_; 
v___x_470_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__2);
v___x_471_ = lean_uint8_dec_le(v_c_446_, v___x_470_);
v___y_452_ = v___x_468_;
v___y_453_ = v___x_471_;
goto v___jp_451_;
}
}
else
{
uint8_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = lean_uint8_sub(v_c_446_, v___y_466_);
v___x_473_ = lean_box(v___x_472_);
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v_it_x27_450_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
return v___x_474_;
}
}
v___jp_475_:
{
uint8_t v___x_476_; uint8_t v___x_477_; 
v___x_476_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3);
v___x_477_ = lean_uint8_dec_le(v___x_476_, v_c_446_);
if (v___x_477_ == 0)
{
v___y_466_ = v___x_476_;
v___y_467_ = v___x_477_;
goto v___jp_465_;
}
else
{
uint8_t v___x_478_; uint8_t v___x_479_; 
v___x_478_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4);
v___x_479_ = lean_uint8_dec_le(v_c_446_, v___x_478_);
v___y_466_ = v___x_476_;
v___y_467_ = v___x_479_;
goto v___jp_465_;
}
}
v___jp_480_:
{
if (v___y_481_ == 0)
{
lean_object* v___x_482_; uint32_t v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_482_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__5));
v___x_483_ = lean_uint8_to_uint32(v_c_446_);
v___x_484_ = l_Char_quote(v___x_483_);
v___x_485_ = lean_string_append(v___x_482_, v___x_484_);
lean_dec_ref(v___x_484_);
v___x_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
v___x_487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_487_, 0, v_it_x27_450_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
return v___x_487_;
}
else
{
goto v___jp_475_;
}
}
v___jp_488_:
{
if (v___y_489_ == 0)
{
uint8_t v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__1);
v___x_491_ = lean_uint8_dec_le(v___x_490_, v_c_446_);
if (v___x_491_ == 0)
{
v___y_481_ = v___x_491_;
goto v___jp_480_;
}
else
{
uint8_t v___x_492_; uint8_t v___x_493_; 
v___x_492_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__2);
v___x_493_ = lean_uint8_dec_le(v_c_446_, v___x_492_);
v___y_481_ = v___x_493_;
goto v___jp_480_;
}
}
else
{
goto v___jp_475_;
}
}
v___jp_494_:
{
if (v___y_495_ == 0)
{
uint8_t v___x_496_; uint8_t v___x_497_; 
v___x_496_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0);
v___x_497_ = lean_uint8_dec_le(v___x_496_, v_c_446_);
if (v___x_497_ == 0)
{
v___y_489_ = v___x_497_;
goto v___jp_488_;
}
else
{
uint8_t v___x_498_; uint8_t v___x_499_; 
v___x_498_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__6, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__6_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__6);
v___x_499_ = lean_uint8_dec_le(v_c_446_, v___x_498_);
v___y_489_ = v___x_499_;
goto v___jp_488_;
}
}
else
{
goto v___jp_475_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(lean_object* v_acc_514_, lean_object* v_count_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_pos_518_; lean_object* v_err_519_; lean_object* v___x_547_; 
lean_inc_ref(v_a_516_);
v___x_547_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit(v_a_516_);
if (lean_obj_tag(v___x_547_) == 0)
{
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_pos_548_; lean_object* v_res_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_566_; 
lean_dec_ref(v_a_516_);
v_pos_548_ = lean_ctor_get(v___x_547_, 0);
v_res_549_ = lean_ctor_get(v___x_547_, 1);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_566_ == 0)
{
v___x_551_ = v___x_547_;
v_isShared_552_ = v_isSharedCheck_566_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_res_549_);
lean_inc(v_pos_548_);
lean_dec(v___x_547_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_566_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_553_ = lean_unsigned_to_nat(16u);
v___x_554_ = lean_unsigned_to_nat(1u);
v___x_555_ = lean_nat_add(v_count_515_, v___x_554_);
lean_dec(v_count_515_);
v___x_556_ = lean_nat_dec_lt(v___x_553_, v___x_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; uint8_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
lean_del_object(v___x_551_);
v___x_557_ = lean_nat_mul(v_acc_514_, v___x_553_);
lean_dec(v_acc_514_);
v___x_558_ = lean_unbox(v_res_549_);
lean_dec(v_res_549_);
v___x_559_ = lean_uint8_to_nat(v___x_558_);
v___x_560_ = lean_nat_add(v___x_557_, v___x_559_);
lean_dec(v___x_557_);
v_acc_514_ = v___x_560_;
v_count_515_ = v___x_555_;
v_a_516_ = v_pos_548_;
goto _start;
}
else
{
lean_object* v___x_562_; lean_object* v___x_564_; 
lean_dec(v___x_555_);
lean_dec(v_res_549_);
lean_dec(v_acc_514_);
v___x_562_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__3));
if (v_isShared_552_ == 0)
{
lean_ctor_set_tag(v___x_551_, 1);
lean_ctor_set(v___x_551_, 1, v___x_562_);
v___x_564_ = v___x_551_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_pos_548_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
else
{
lean_object* v_pos_567_; lean_object* v_err_568_; 
v_pos_567_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_pos_567_);
v_err_568_ = lean_ctor_get(v___x_547_, 1);
lean_inc(v_err_568_);
lean_dec_ref_known(v___x_547_, 2);
v_pos_518_ = v_pos_567_;
v_err_519_ = v_err_568_;
goto v___jp_517_;
}
}
else
{
lean_object* v_err_569_; 
v_err_569_ = lean_ctor_get(v___x_547_, 1);
lean_inc(v_err_569_);
lean_dec_ref_known(v___x_547_, 2);
lean_inc_ref(v_a_516_);
v_pos_518_ = v_a_516_;
v_err_519_ = v_err_569_;
goto v___jp_517_;
}
v___jp_517_:
{
lean_object* v_idx_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_545_; 
v_idx_520_ = lean_ctor_get(v_a_516_, 1);
v_isSharedCheck_545_ = !lean_is_exclusive(v_a_516_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; 
v_unused_546_ = lean_ctor_get(v_a_516_, 0);
lean_dec(v_unused_546_);
v___x_522_ = v_a_516_;
v_isShared_523_ = v_isSharedCheck_545_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_idx_520_);
lean_dec(v_a_516_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_545_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v_array_524_; lean_object* v_idx_525_; uint8_t v___x_526_; 
v_array_524_ = lean_ctor_get(v_pos_518_, 0);
v_idx_525_ = lean_ctor_get(v_pos_518_, 1);
v___x_526_ = lean_nat_dec_eq(v_idx_520_, v_idx_525_);
lean_dec(v_idx_520_);
if (v___x_526_ == 0)
{
lean_object* v___x_528_; 
lean_dec(v_count_515_);
lean_dec(v_acc_514_);
if (v_isShared_523_ == 0)
{
lean_ctor_set_tag(v___x_522_, 1);
lean_ctor_set(v___x_522_, 1, v_err_519_);
lean_ctor_set(v___x_522_, 0, v_pos_518_);
v___x_528_ = v___x_522_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_pos_518_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_err_519_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
else
{
lean_object* v___x_530_; uint8_t v___x_531_; 
lean_dec(v_err_519_);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = lean_nat_dec_eq(v_count_515_, v___x_530_);
lean_dec(v_count_515_);
if (v___x_531_ == 0)
{
lean_object* v___x_533_; 
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 1, v_acc_514_);
lean_ctor_set(v___x_522_, 0, v_pos_518_);
v___x_533_ = v___x_522_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_pos_518_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_acc_514_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
else
{
lean_object* v___x_535_; uint8_t v___x_536_; 
lean_dec(v_acc_514_);
v___x_535_ = lean_byte_array_size(v_array_524_);
v___x_536_ = lean_nat_dec_lt(v_idx_525_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_537_ = lean_box(0);
if (v_isShared_523_ == 0)
{
lean_ctor_set_tag(v___x_522_, 1);
lean_ctor_set(v___x_522_, 1, v___x_537_);
lean_ctor_set(v___x_522_, 0, v_pos_518_);
v___x_539_ = v___x_522_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_pos_518_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
else
{
lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_541_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__1));
if (v_isShared_523_ == 0)
{
lean_ctor_set_tag(v___x_522_, 1);
lean_ctor_set(v___x_522_, 1, v___x_541_);
lean_ctor_set(v___x_522_, 0, v_pos_518_);
v___x_543_ = v___x_522_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_pos_518_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(lean_object* v_a_570_){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_572_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(v___x_571_, v___x_571_, v_a_570_);
return v___x_572_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__0));
v___x_575_ = lean_string_to_utf8(v___x_574_);
return v___x_575_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4(void){
_start:
{
uint32_t v___x_579_; uint8_t v___x_580_; 
v___x_579_ = 46;
v___x_580_ = lean_uint32_to_uint8(v___x_579_);
return v___x_580_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5(void){
_start:
{
uint8_t v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4);
v___x_582_ = lean_uint8_to_nat(v___x_581_);
return v___x_582_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__6(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5);
v___x_584_ = l_Nat_reprFast(v___x_583_);
return v___x_584_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__7(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__6, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__6_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__6);
v___x_586_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_587_ = lean_string_append(v___x_586_, v___x_585_);
return v___x_587_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__8(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__5));
v___x_589_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__7);
v___x_590_ = lean_string_append(v___x_589_, v___x_588_);
return v___x_590_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__9(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__8, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__8_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__8);
v___x_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(lean_object* v_a_593_){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1);
v___x_595_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_594_, v_a_593_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_pos_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_657_; 
v_pos_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; 
v_unused_658_ = lean_ctor_get(v___x_595_, 1);
lean_dec(v_unused_658_);
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_657_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_pos_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_657_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v_array_605_; lean_object* v_idx_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v_array_605_ = lean_ctor_get(v_pos_596_, 0);
v_idx_606_ = lean_ctor_get(v_pos_596_, 1);
v___x_607_ = lean_byte_array_size(v_array_605_);
v___x_608_ = lean_nat_dec_lt(v_idx_606_, v___x_607_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; lean_object* v___x_610_; 
lean_del_object(v___x_598_);
v___x_609_ = lean_box(0);
v___x_610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_610_, 0, v_pos_596_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
return v___x_610_;
}
else
{
uint8_t v_c_611_; uint8_t v___x_612_; uint8_t v___x_613_; 
v_c_611_ = lean_byte_array_fget(v_array_605_, v_idx_606_);
v___x_612_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3);
v___x_613_ = lean_uint8_dec_le(v___x_612_, v_c_611_);
if (v___x_613_ == 0)
{
goto v___jp_600_;
}
else
{
uint8_t v___x_614_; uint8_t v___x_615_; 
v___x_614_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4);
v___x_615_ = lean_uint8_dec_le(v_c_611_, v___x_614_);
if (v___x_615_ == 0)
{
goto v___jp_600_;
}
else
{
lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_654_; 
lean_inc(v_idx_606_);
lean_inc_ref(v_array_605_);
lean_del_object(v___x_598_);
v_isSharedCheck_654_ = !lean_is_exclusive(v_pos_596_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; lean_object* v_unused_656_; 
v_unused_655_ = lean_ctor_get(v_pos_596_, 1);
lean_dec(v_unused_655_);
v_unused_656_ = lean_ctor_get(v_pos_596_, 0);
lean_dec(v_unused_656_);
v___x_617_ = v_pos_596_;
v_isShared_618_ = v_isSharedCheck_654_;
goto v_resetjp_616_;
}
else
{
lean_dec(v_pos_596_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_654_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v_it_x27_622_; 
v___x_619_ = lean_unsigned_to_nat(1u);
v___x_620_ = lean_nat_add(v_idx_606_, v___x_619_);
lean_dec(v_idx_606_);
lean_inc(v___x_620_);
lean_inc_ref(v_array_605_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v___x_620_);
v_it_x27_622_ = v___x_617_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_array_605_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_620_);
v_it_x27_622_ = v_reuseFailAlloc_653_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
uint8_t v___x_623_; 
v___x_623_ = lean_nat_dec_lt(v___x_620_, v___x_607_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec(v___x_620_);
lean_dec_ref(v_array_605_);
v___x_624_ = lean_box(0);
v___x_625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_625_, 0, v_it_x27_622_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
return v___x_625_;
}
else
{
uint8_t v___x_626_; uint8_t v_got_627_; uint8_t v___x_628_; 
v___x_626_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4);
v_got_627_ = lean_byte_array_fget(v_array_605_, v___x_620_);
v___x_628_ = lean_uint8_dec_eq(v_got_627_, v___x_626_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; 
lean_dec(v___x_620_);
lean_dec_ref(v_array_605_);
v___x_629_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__9, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__9_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__9);
v___x_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_630_, 0, v_it_x27_622_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
return v___x_630_;
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_636_; 
lean_dec_ref(v_it_x27_622_);
v___x_631_ = lean_nat_add(v___x_620_, v___x_619_);
lean_dec(v___x_620_);
lean_inc(v___x_631_);
lean_inc_ref(v_array_605_);
v___x_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_632_, 0, v_array_605_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_636_ = lean_nat_dec_lt(v___x_631_, v___x_607_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; lean_object* v___x_638_; 
lean_dec(v___x_631_);
lean_dec_ref(v_array_605_);
v___x_637_ = lean_box(0);
v___x_638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_632_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
return v___x_638_;
}
else
{
uint8_t v_c_639_; uint8_t v___x_640_; 
v_c_639_ = lean_byte_array_fget(v_array_605_, v___x_631_);
v___x_640_ = lean_uint8_dec_le(v___x_612_, v_c_639_);
if (v___x_640_ == 0)
{
lean_dec(v___x_631_);
lean_dec_ref(v_array_605_);
goto v___jp_633_;
}
else
{
uint8_t v___x_641_; 
v___x_641_ = lean_uint8_dec_le(v_c_639_, v___x_614_);
if (v___x_641_ == 0)
{
lean_dec(v___x_631_);
lean_dec_ref(v_array_605_);
goto v___jp_633_;
}
else
{
uint32_t v___x_642_; lean_object* v___x_643_; lean_object* v_it_x27_644_; uint32_t v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
lean_dec_ref_known(v___x_632_, 2);
v___x_642_ = lean_uint8_to_uint32(v_c_611_);
v___x_643_ = lean_nat_add(v___x_631_, v___x_619_);
lean_dec(v___x_631_);
v_it_x27_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_644_, 0, v_array_605_);
lean_ctor_set(v_it_x27_644_, 1, v___x_643_);
v___x_645_ = lean_uint8_to_uint32(v_c_639_);
v___x_646_ = lean_uint32_to_nat(v___x_642_);
v___x_647_ = lean_unsigned_to_nat(48u);
v___x_648_ = lean_nat_sub(v___x_646_, v___x_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_uint32_to_nat(v___x_645_);
v___x_650_ = lean_nat_sub(v___x_649_, v___x_647_);
lean_dec(v___x_649_);
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_648_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v_it_x27_644_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
return v___x_652_;
}
}
}
v___jp_633_:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_632_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
return v___x_635_;
}
}
}
}
}
}
}
}
v___jp_600_:
{
lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_601_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
if (v_isShared_599_ == 0)
{
lean_ctor_set_tag(v___x_598_, 1);
lean_ctor_set(v___x_598_, 1, v___x_601_);
v___x_603_ = v___x_598_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_pos_596_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_object* v_pos_659_; lean_object* v_err_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
v_pos_659_ = lean_ctor_get(v___x_595_, 0);
v_err_660_ = lean_ctor_get(v___x_595_, 1);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_595_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_err_660_);
lean_inc(v_pos_659_);
lean_dec(v___x_595_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_pos_659_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_err_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersion(lean_object* v_a_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_668_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_res_670_; lean_object* v_pos_671_; lean_object* v_fst_672_; lean_object* v_snd_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_res_670_ = lean_ctor_get(v___x_669_, 1);
lean_inc(v_res_670_);
v_pos_671_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_pos_671_);
lean_dec_ref_known(v___x_669_, 2);
v_fst_672_ = lean_ctor_get(v_res_670_, 0);
lean_inc(v_fst_672_);
v_snd_673_ = lean_ctor_get(v_res_670_, 1);
lean_inc(v_snd_673_);
lean_dec(v_res_670_);
v___x_674_ = l_Std_Http_Version_ofNumber_x3f(v_fst_672_, v_snd_673_);
lean_dec(v_snd_673_);
lean_dec(v_fst_672_);
v___x_675_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_674_, v_pos_671_);
lean_dec(v___x_674_);
return v___x_675_;
}
else
{
lean_object* v_pos_676_; lean_object* v_err_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
v_pos_676_ = lean_ctor_get(v___x_669_, 0);
v_err_677_ = lean_ctor_get(v___x_669_, 1);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_669_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_err_677_);
lean_inc(v_pos_676_);
lean_dec(v___x_669_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_pos_676_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_err_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(lean_object* v_a_685_, lean_object* v_f_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = lean_apply_1(v_a_685_, v___y_687_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_pos_689_; lean_object* v_res_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_698_; 
v_pos_689_ = lean_ctor_get(v___x_688_, 0);
v_res_690_ = lean_ctor_get(v___x_688_, 1);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_698_ == 0)
{
v___x_692_ = v___x_688_;
v_isShared_693_ = v_isSharedCheck_698_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_res_690_);
lean_inc(v_pos_689_);
lean_dec(v___x_688_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_698_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_694_ = lean_apply_1(v_f_686_, v_res_690_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_694_);
v___x_696_ = v___x_692_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_pos_689_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
else
{
lean_object* v_pos_699_; lean_object* v_err_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec(v_f_686_);
v_pos_699_ = lean_ctor_get(v___x_688_, 0);
v_err_700_ = lean_ctor_get(v___x_688_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_688_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_err_700_);
lean_inc(v_pos_699_);
lean_dec(v___x_688_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_pos_699_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_err_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0(lean_object* v_00_u03b1_708_, lean_object* v_00_u03b2_709_, lean_object* v_a_710_, lean_object* v_f_711_, lean_object* v___y_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v_a_710_, v_f_711_, v___y_712_);
return v___x_713_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0(lean_object* v_x_714_){
_start:
{
uint8_t v___x_715_; 
v___x_715_ = 9;
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0___boxed(lean_object* v_x_716_){
_start:
{
uint8_t v_res_717_; lean_object* v_r_718_; 
v_res_717_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0(v_x_716_);
v_r_718_ = lean_box(v_res_717_);
return v_r_718_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1(lean_object* v_x_719_){
_start:
{
uint8_t v___x_720_; 
v___x_720_ = 32;
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1___boxed(lean_object* v_x_721_){
_start:
{
uint8_t v_res_722_; lean_object* v_r_723_; 
v_res_722_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1(v_x_721_);
v_r_723_ = lean_box(v_res_722_);
return v_r_723_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2(lean_object* v_x_724_){
_start:
{
uint8_t v___x_725_; 
v___x_725_ = 28;
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2___boxed(lean_object* v_x_726_){
_start:
{
uint8_t v_res_727_; lean_object* v_r_728_; 
v_res_727_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2(v_x_726_);
v_r_728_ = lean_box(v_res_727_);
return v_r_728_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3(lean_object* v_x_729_){
_start:
{
uint8_t v___x_730_; 
v___x_730_ = 1;
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3___boxed(lean_object* v_x_731_){
_start:
{
uint8_t v_res_732_; lean_object* v_r_733_; 
v_res_732_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3(v_x_731_);
v_r_733_ = lean_box(v_res_732_);
return v_r_733_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4(lean_object* v_x_734_){
_start:
{
uint8_t v___x_735_; 
v___x_735_ = 5;
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4___boxed(lean_object* v_x_736_){
_start:
{
uint8_t v_res_737_; lean_object* v_r_738_; 
v_res_737_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4(v_x_736_);
v_r_738_ = lean_box(v_res_737_);
return v_r_738_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5(lean_object* v_x_739_){
_start:
{
uint8_t v___x_740_; 
v___x_740_ = 4;
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5___boxed(lean_object* v_x_741_){
_start:
{
uint8_t v_res_742_; lean_object* v_r_743_; 
v_res_742_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5(v_x_741_);
v_r_743_ = lean_box(v_res_742_);
return v_r_743_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6(lean_object* v_x_744_){
_start:
{
uint8_t v___x_745_; 
v___x_745_ = 10;
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6___boxed(lean_object* v_x_746_){
_start:
{
uint8_t v_res_747_; lean_object* v_r_748_; 
v_res_747_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6(v_x_746_);
v_r_748_ = lean_box(v_res_747_);
return v_r_748_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7(lean_object* v_x_749_){
_start:
{
uint8_t v___x_750_; 
v___x_750_ = 12;
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7___boxed(lean_object* v_x_751_){
_start:
{
uint8_t v_res_752_; lean_object* v_r_753_; 
v_res_752_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7(v_x_751_);
v_r_753_ = lean_box(v_res_752_);
return v_r_753_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8(lean_object* v_x_754_){
_start:
{
uint8_t v___x_755_; 
v___x_755_ = 14;
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8___boxed(lean_object* v_x_756_){
_start:
{
uint8_t v_res_757_; lean_object* v_r_758_; 
v_res_757_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8(v_x_756_);
v_r_758_ = lean_box(v_res_757_);
return v_r_758_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9(lean_object* v_x_759_){
_start:
{
uint8_t v___x_760_; 
v___x_760_ = 16;
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9___boxed(lean_object* v_x_761_){
_start:
{
uint8_t v_res_762_; lean_object* v_r_763_; 
v_res_762_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9(v_x_761_);
v_r_763_ = lean_box(v_res_762_);
return v_r_763_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10(lean_object* v_x_764_){
_start:
{
uint8_t v___x_765_; 
v___x_765_ = 18;
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10___boxed(lean_object* v_x_766_){
_start:
{
uint8_t v_res_767_; lean_object* v_r_768_; 
v_res_767_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10(v_x_766_);
v_r_768_ = lean_box(v_res_767_);
return v_r_768_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11(lean_object* v_x_769_){
_start:
{
uint8_t v___x_770_; 
v___x_770_ = 20;
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11___boxed(lean_object* v_x_771_){
_start:
{
uint8_t v_res_772_; lean_object* v_r_773_; 
v_res_772_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11(v_x_771_);
v_r_773_ = lean_box(v_res_772_);
return v_r_773_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12(lean_object* v_x_774_){
_start:
{
uint8_t v___x_775_; 
v___x_775_ = 23;
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12___boxed(lean_object* v_x_776_){
_start:
{
uint8_t v_res_777_; lean_object* v_r_778_; 
v_res_777_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12(v_x_776_);
v_r_778_ = lean_box(v_res_777_);
return v_r_778_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13(lean_object* v_x_779_){
_start:
{
uint8_t v___x_780_; 
v___x_780_ = 22;
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13___boxed(lean_object* v_x_781_){
_start:
{
uint8_t v_res_782_; lean_object* v_r_783_; 
v_res_782_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13(v_x_781_);
v_r_783_ = lean_box(v_res_782_);
return v_r_783_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14(lean_object* v_x_784_){
_start:
{
uint8_t v___x_785_; 
v___x_785_ = 25;
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14___boxed(lean_object* v_x_786_){
_start:
{
uint8_t v_res_787_; lean_object* v_r_788_; 
v_res_787_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14(v_x_786_);
v_r_788_ = lean_box(v_res_787_);
return v_r_788_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15(lean_object* v_x_789_){
_start:
{
uint8_t v___x_790_; 
v___x_790_ = 29;
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15___boxed(lean_object* v_x_791_){
_start:
{
uint8_t v_res_792_; lean_object* v_r_793_; 
v_res_792_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15(v_x_791_);
v_r_793_ = lean_box(v_res_792_);
return v_r_793_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16(lean_object* v_x_794_){
_start:
{
uint8_t v___x_795_; 
v___x_795_ = 33;
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16___boxed(lean_object* v_x_796_){
_start:
{
uint8_t v_res_797_; lean_object* v_r_798_; 
v_res_797_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16(v_x_796_);
v_r_798_ = lean_box(v_res_797_);
return v_r_798_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17(lean_object* v_x_799_){
_start:
{
uint8_t v___x_800_; 
v___x_800_ = 35;
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17___boxed(lean_object* v_x_801_){
_start:
{
uint8_t v_res_802_; lean_object* v_r_803_; 
v_res_802_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17(v_x_801_);
v_r_803_ = lean_box(v_res_802_);
return v_r_803_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18(lean_object* v_x_804_){
_start:
{
uint8_t v___x_805_; 
v___x_805_ = 38;
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18___boxed(lean_object* v_x_806_){
_start:
{
uint8_t v_res_807_; lean_object* v_r_808_; 
v_res_807_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18(v_x_806_);
v_r_808_ = lean_box(v_res_807_);
return v_r_808_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19(lean_object* v_x_809_){
_start:
{
uint8_t v___x_810_; 
v___x_810_ = 39;
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19___boxed(lean_object* v_x_811_){
_start:
{
uint8_t v_res_812_; lean_object* v_r_813_; 
v_res_812_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19(v_x_811_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21(lean_object* v_x_814_){
_start:
{
uint8_t v___x_815_; 
v___x_815_ = 37;
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21___boxed(lean_object* v_x_816_){
_start:
{
uint8_t v_res_817_; lean_object* v_r_818_; 
v_res_817_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21(v_x_816_);
v_r_818_ = lean_box(v_res_817_);
return v_r_818_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20(lean_object* v_x_819_){
_start:
{
uint8_t v___x_820_; 
v___x_820_ = 36;
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20___boxed(lean_object* v_x_821_){
_start:
{
uint8_t v_res_822_; lean_object* v_r_823_; 
v_res_822_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20(v_x_821_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22(lean_object* v_x_824_){
_start:
{
uint8_t v___x_825_; 
v___x_825_ = 34;
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22___boxed(lean_object* v_x_826_){
_start:
{
uint8_t v_res_827_; lean_object* v_r_828_; 
v_res_827_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22(v_x_826_);
v_r_828_ = lean_box(v_res_827_);
return v_r_828_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23(lean_object* v_x_829_){
_start:
{
uint8_t v___x_830_; 
v___x_830_ = 30;
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23___boxed(lean_object* v_x_831_){
_start:
{
uint8_t v_res_832_; lean_object* v_r_833_; 
v_res_832_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23(v_x_831_);
v_r_833_ = lean_box(v_res_832_);
return v_r_833_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24(lean_object* v_x_834_){
_start:
{
uint8_t v___x_835_; 
v___x_835_ = 26;
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24___boxed(lean_object* v_x_836_){
_start:
{
uint8_t v_res_837_; lean_object* v_r_838_; 
v_res_837_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24(v_x_836_);
v_r_838_ = lean_box(v_res_837_);
return v_r_838_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25(lean_object* v_x_839_){
_start:
{
uint8_t v___x_840_; 
v___x_840_ = 24;
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25___boxed(lean_object* v_x_841_){
_start:
{
uint8_t v_res_842_; lean_object* v_r_843_; 
v_res_842_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25(v_x_841_);
v_r_843_ = lean_box(v_res_842_);
return v_r_843_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26(lean_object* v_x_844_){
_start:
{
uint8_t v___x_845_; 
v___x_845_ = 27;
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26___boxed(lean_object* v_x_846_){
_start:
{
uint8_t v_res_847_; lean_object* v_r_848_; 
v_res_847_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26(v_x_846_);
v_r_848_ = lean_box(v_res_847_);
return v_r_848_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27(lean_object* v_x_849_){
_start:
{
uint8_t v___x_850_; 
v___x_850_ = 21;
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27___boxed(lean_object* v_x_851_){
_start:
{
uint8_t v_res_852_; lean_object* v_r_853_; 
v_res_852_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27(v_x_851_);
v_r_853_ = lean_box(v_res_852_);
return v_r_853_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28(lean_object* v_x_854_){
_start:
{
uint8_t v___x_855_; 
v___x_855_ = 19;
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28___boxed(lean_object* v_x_856_){
_start:
{
uint8_t v_res_857_; lean_object* v_r_858_; 
v_res_857_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28(v_x_856_);
v_r_858_ = lean_box(v_res_857_);
return v_r_858_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29(lean_object* v_x_859_){
_start:
{
uint8_t v___x_860_; 
v___x_860_ = 17;
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29___boxed(lean_object* v_x_861_){
_start:
{
uint8_t v_res_862_; lean_object* v_r_863_; 
v_res_862_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29(v_x_861_);
v_r_863_ = lean_box(v_res_862_);
return v_r_863_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30(lean_object* v_x_864_){
_start:
{
uint8_t v___x_865_; 
v___x_865_ = 15;
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30___boxed(lean_object* v_x_866_){
_start:
{
uint8_t v_res_867_; lean_object* v_r_868_; 
v_res_867_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30(v_x_866_);
v_r_868_ = lean_box(v_res_867_);
return v_r_868_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31(lean_object* v_x_869_){
_start:
{
uint8_t v___x_870_; 
v___x_870_ = 13;
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31___boxed(lean_object* v_x_871_){
_start:
{
uint8_t v_res_872_; lean_object* v_r_873_; 
v_res_872_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31(v_x_871_);
v_r_873_ = lean_box(v_res_872_);
return v_r_873_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32(lean_object* v_x_874_){
_start:
{
uint8_t v___x_875_; 
v___x_875_ = 11;
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32___boxed(lean_object* v_x_876_){
_start:
{
uint8_t v_res_877_; lean_object* v_r_878_; 
v_res_877_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32(v_x_876_);
v_r_878_ = lean_box(v_res_877_);
return v_r_878_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33(lean_object* v_x_879_){
_start:
{
uint8_t v___x_880_; 
v___x_880_ = 6;
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33___boxed(lean_object* v_x_881_){
_start:
{
uint8_t v_res_882_; lean_object* v_r_883_; 
v_res_882_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33(v_x_881_);
v_r_883_ = lean_box(v_res_882_);
return v_r_883_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34(lean_object* v_x_884_){
_start:
{
uint8_t v___x_885_; 
v___x_885_ = 3;
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34___boxed(lean_object* v_x_886_){
_start:
{
uint8_t v_res_887_; lean_object* v_r_888_; 
v_res_887_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34(v_x_886_);
v_r_888_ = lean_box(v_res_887_);
return v_r_888_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35(lean_object* v_x_889_){
_start:
{
uint8_t v___x_890_; 
v___x_890_ = 2;
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35___boxed(lean_object* v_x_891_){
_start:
{
uint8_t v_res_892_; lean_object* v_r_893_; 
v_res_892_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35(v_x_891_);
v_r_893_ = lean_box(v_res_892_);
return v_r_893_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36(lean_object* v_x_894_){
_start:
{
uint8_t v___x_895_; 
v___x_895_ = 31;
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36___boxed(lean_object* v_x_896_){
_start:
{
uint8_t v_res_897_; lean_object* v_r_898_; 
v_res_897_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36(v_x_896_);
v_r_898_ = lean_box(v_res_897_);
return v_r_898_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37(lean_object* v_x_899_){
_start:
{
uint8_t v___x_900_; 
v___x_900_ = 0;
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37___boxed(lean_object* v_x_901_){
_start:
{
uint8_t v_res_902_; lean_object* v_r_903_; 
v_res_902_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37(v_x_901_);
v_r_903_ = lean_box(v_res_902_);
return v_r_903_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38(lean_object* v_x_904_){
_start:
{
uint8_t v___x_905_; 
v___x_905_ = 7;
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38___boxed(lean_object* v_x_906_){
_start:
{
uint8_t v_res_907_; lean_object* v_r_908_; 
v_res_907_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38(v_x_906_);
v_r_908_ = lean_box(v_res_907_);
return v_r_908_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39(lean_object* v_x_909_){
_start:
{
uint8_t v___x_910_; 
v___x_910_ = 8;
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39___boxed(lean_object* v_x_911_){
_start:
{
uint8_t v_res_912_; lean_object* v_r_913_; 
v_res_912_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39(v_x_911_);
v_r_913_ = lean_box(v_res_912_);
return v_r_913_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22));
v___x_939_ = lean_string_to_utf8(v___x_938_);
return v___x_939_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23);
v___x_941_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_941_, 0, v___x_940_);
return v___x_941_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26));
v___x_945_ = lean_string_to_utf8(v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27);
v___x_947_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_947_, 0, v___x_946_);
return v___x_947_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__29));
v___x_950_ = lean_string_to_utf8(v___x_949_);
return v___x_950_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30);
v___x_952_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__33));
v___x_956_ = lean_string_to_utf8(v___x_955_);
return v___x_956_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34);
v___x_958_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__36));
v___x_961_ = lean_string_to_utf8(v___x_960_);
return v___x_961_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37);
v___x_963_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_963_, 0, v___x_962_);
return v___x_963_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__40));
v___x_967_ = lean_string_to_utf8(v___x_966_);
return v___x_967_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41);
v___x_969_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_969_, 0, v___x_968_);
return v___x_969_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43));
v___x_972_ = lean_string_to_utf8(v___x_971_);
return v___x_972_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44);
v___x_974_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_974_, 0, v___x_973_);
return v___x_974_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47));
v___x_978_ = lean_string_to_utf8(v___x_977_);
return v___x_978_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48);
v___x_980_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_980_, 0, v___x_979_);
return v___x_980_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50));
v___x_983_ = lean_string_to_utf8(v___x_982_);
return v___x_983_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51);
v___x_985_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_985_, 0, v___x_984_);
return v___x_985_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54));
v___x_989_ = lean_string_to_utf8(v___x_988_);
return v___x_989_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55);
v___x_991_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__57));
v___x_994_ = lean_string_to_utf8(v___x_993_);
return v___x_994_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58);
v___x_996_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_996_, 0, v___x_995_);
return v___x_996_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__61));
v___x_1000_ = lean_string_to_utf8(v___x_999_);
return v___x_1000_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62);
v___x_1002_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1002_, 0, v___x_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__64));
v___x_1005_ = lean_string_to_utf8(v___x_1004_);
return v___x_1005_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65);
v___x_1007_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1007_, 0, v___x_1006_);
return v___x_1007_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__68));
v___x_1011_ = lean_string_to_utf8(v___x_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69);
v___x_1013_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1013_, 0, v___x_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71));
v___x_1016_ = lean_string_to_utf8(v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72);
v___x_1018_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1018_, 0, v___x_1017_);
return v___x_1018_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75));
v___x_1022_ = lean_string_to_utf8(v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76);
v___x_1024_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1024_, 0, v___x_1023_);
return v___x_1024_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78));
v___x_1027_ = lean_string_to_utf8(v___x_1026_);
return v___x_1027_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79);
v___x_1029_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1029_, 0, v___x_1028_);
return v___x_1029_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82));
v___x_1033_ = lean_string_to_utf8(v___x_1032_);
return v___x_1033_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83);
v___x_1035_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1035_, 0, v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__85));
v___x_1038_ = lean_string_to_utf8(v___x_1037_);
return v___x_1038_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86);
v___x_1040_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1040_, 0, v___x_1039_);
return v___x_1040_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__89));
v___x_1044_ = lean_string_to_utf8(v___x_1043_);
return v___x_1044_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90);
v___x_1046_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1046_, 0, v___x_1045_);
return v___x_1046_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__92));
v___x_1049_ = lean_string_to_utf8(v___x_1048_);
return v___x_1049_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93);
v___x_1051_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1051_, 0, v___x_1050_);
return v___x_1051_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__96));
v___x_1055_ = lean_string_to_utf8(v___x_1054_);
return v___x_1055_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97);
v___x_1057_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99));
v___x_1060_ = lean_string_to_utf8(v___x_1059_);
return v___x_1060_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100);
v___x_1062_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1062_, 0, v___x_1061_);
return v___x_1062_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103));
v___x_1066_ = lean_string_to_utf8(v___x_1065_);
return v___x_1066_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104);
v___x_1068_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1068_, 0, v___x_1067_);
return v___x_1068_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106));
v___x_1071_ = lean_string_to_utf8(v___x_1070_);
return v___x_1071_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107);
v___x_1073_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1073_, 0, v___x_1072_);
return v___x_1073_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110));
v___x_1077_ = lean_string_to_utf8(v___x_1076_);
return v___x_1077_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111);
v___x_1079_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1079_, 0, v___x_1078_);
return v___x_1079_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__113));
v___x_1082_ = lean_string_to_utf8(v___x_1081_);
return v___x_1082_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114);
v___x_1084_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__117));
v___x_1088_ = lean_string_to_utf8(v___x_1087_);
return v___x_1088_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118);
v___x_1090_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1090_, 0, v___x_1089_);
return v___x_1090_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__120));
v___x_1093_ = lean_string_to_utf8(v___x_1092_);
return v___x_1093_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121);
v___x_1095_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1095_, 0, v___x_1094_);
return v___x_1095_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__124));
v___x_1099_ = lean_string_to_utf8(v___x_1098_);
return v___x_1099_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125);
v___x_1101_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1101_, 0, v___x_1100_);
return v___x_1101_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127));
v___x_1104_ = lean_string_to_utf8(v___x_1103_);
return v___x_1104_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128);
v___x_1106_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1106_, 0, v___x_1105_);
return v___x_1106_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131));
v___x_1110_ = lean_string_to_utf8(v___x_1109_);
return v___x_1110_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132);
v___x_1112_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1112_, 0, v___x_1111_);
return v___x_1112_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134));
v___x_1115_ = lean_string_to_utf8(v___x_1114_);
return v___x_1115_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135);
v___x_1117_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1117_, 0, v___x_1116_);
return v___x_1117_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139(void){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138));
v___x_1121_ = lean_string_to_utf8(v___x_1120_);
return v___x_1121_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139);
v___x_1123_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1123_, 0, v___x_1122_);
return v___x_1123_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__141));
v___x_1126_ = lean_string_to_utf8(v___x_1125_);
return v___x_1126_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142);
v___x_1128_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1128_, 0, v___x_1127_);
return v___x_1128_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__145));
v___x_1132_ = lean_string_to_utf8(v___x_1131_);
return v___x_1132_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146);
v___x_1134_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1134_, 0, v___x_1133_);
return v___x_1134_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__148));
v___x_1137_ = lean_string_to_utf8(v___x_1136_);
return v___x_1137_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149);
v___x_1139_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1139_, 0, v___x_1138_);
return v___x_1139_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__152));
v___x_1143_ = lean_string_to_utf8(v___x_1142_);
return v___x_1143_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153);
v___x_1145_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1145_, 0, v___x_1144_);
return v___x_1145_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155));
v___x_1148_ = lean_string_to_utf8(v___x_1147_);
return v___x_1148_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156);
v___x_1150_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1150_, 0, v___x_1149_);
return v___x_1150_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159));
v___x_1154_ = lean_string_to_utf8(v___x_1153_);
return v___x_1154_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160);
v___x_1156_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1156_, 0, v___x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(lean_object* v_a_1157_){
_start:
{
lean_object* v___f_1158_; lean_object* v___f_1159_; lean_object* v___f_1160_; lean_object* v___f_1161_; lean_object* v___f_1162_; lean_object* v___f_1163_; lean_object* v___f_1164_; lean_object* v___f_1165_; lean_object* v___f_1166_; lean_object* v___f_1167_; lean_object* v___f_1168_; lean_object* v___f_1169_; lean_object* v___f_1170_; lean_object* v___f_1171_; lean_object* v___f_1172_; lean_object* v___f_1173_; lean_object* v___f_1174_; lean_object* v___f_1175_; lean_object* v___f_1176_; lean_object* v___f_1177_; lean_object* v___f_1178_; lean_object* v_idx_1180_; lean_object* v___y_1181_; lean_object* v_pos_1182_; lean_object* v_idx_1183_; lean_object* v_idx_1218_; lean_object* v___y_1219_; lean_object* v_pos_1220_; lean_object* v_idx_1221_; lean_object* v___f_1236_; lean_object* v_idx_1238_; lean_object* v___y_1239_; lean_object* v_pos_1240_; lean_object* v_idx_1241_; lean_object* v_idx_1257_; lean_object* v___y_1258_; lean_object* v_pos_1259_; lean_object* v_idx_1260_; lean_object* v___f_1275_; lean_object* v_idx_1277_; lean_object* v___y_1278_; lean_object* v_pos_1279_; lean_object* v_idx_1280_; lean_object* v_idx_1296_; lean_object* v___y_1297_; lean_object* v_pos_1298_; lean_object* v_idx_1299_; lean_object* v___f_1314_; lean_object* v_idx_1316_; lean_object* v___y_1317_; lean_object* v_pos_1318_; lean_object* v_idx_1319_; lean_object* v_idx_1335_; lean_object* v___y_1336_; lean_object* v_pos_1337_; lean_object* v_idx_1338_; lean_object* v___f_1353_; lean_object* v_idx_1355_; lean_object* v___y_1356_; lean_object* v_pos_1357_; lean_object* v_idx_1358_; lean_object* v_idx_1374_; lean_object* v___y_1375_; lean_object* v_pos_1376_; lean_object* v_idx_1377_; lean_object* v___f_1392_; lean_object* v_idx_1394_; lean_object* v___y_1395_; lean_object* v_pos_1396_; lean_object* v_idx_1397_; lean_object* v_idx_1413_; lean_object* v___y_1414_; lean_object* v_pos_1415_; lean_object* v_idx_1416_; lean_object* v___f_1431_; lean_object* v_idx_1433_; lean_object* v___y_1434_; lean_object* v_pos_1435_; lean_object* v_idx_1436_; lean_object* v_idx_1452_; lean_object* v___y_1453_; lean_object* v_pos_1454_; lean_object* v_idx_1455_; lean_object* v___f_1470_; lean_object* v_idx_1472_; lean_object* v___y_1473_; lean_object* v_pos_1474_; lean_object* v_idx_1475_; lean_object* v_idx_1491_; lean_object* v___y_1492_; lean_object* v_pos_1493_; lean_object* v_idx_1494_; lean_object* v___f_1509_; lean_object* v_idx_1511_; lean_object* v___y_1512_; lean_object* v_pos_1513_; lean_object* v_idx_1514_; lean_object* v_idx_1530_; lean_object* v___y_1531_; lean_object* v_pos_1532_; lean_object* v_idx_1533_; lean_object* v___f_1548_; lean_object* v_idx_1550_; lean_object* v___y_1551_; lean_object* v_pos_1552_; lean_object* v_idx_1553_; lean_object* v_idx_1569_; lean_object* v___y_1570_; lean_object* v_pos_1571_; lean_object* v_idx_1572_; lean_object* v___f_1587_; lean_object* v_idx_1589_; lean_object* v___y_1590_; lean_object* v_pos_1591_; lean_object* v_idx_1592_; lean_object* v_idx_1608_; lean_object* v___y_1609_; lean_object* v_pos_1610_; lean_object* v_idx_1611_; lean_object* v___f_1626_; lean_object* v_idx_1628_; lean_object* v___y_1629_; lean_object* v_pos_1630_; lean_object* v_idx_1631_; lean_object* v_idx_1647_; lean_object* v___y_1648_; lean_object* v_pos_1649_; lean_object* v_idx_1650_; lean_object* v___f_1665_; lean_object* v_idx_1667_; lean_object* v___y_1668_; lean_object* v_pos_1669_; lean_object* v_idx_1670_; lean_object* v_idx_1686_; lean_object* v___y_1687_; lean_object* v_pos_1688_; lean_object* v_idx_1689_; lean_object* v___f_1704_; lean_object* v_idx_1706_; lean_object* v___y_1707_; lean_object* v_pos_1708_; lean_object* v_idx_1709_; lean_object* v_idx_1725_; lean_object* v___y_1726_; lean_object* v_pos_1727_; lean_object* v_idx_1728_; lean_object* v___f_1743_; lean_object* v_idx_1745_; lean_object* v___y_1746_; lean_object* v_pos_1747_; lean_object* v_idx_1748_; lean_object* v_idx_1764_; lean_object* v___y_1765_; lean_object* v_pos_1766_; lean_object* v_idx_1767_; lean_object* v___f_1782_; lean_object* v_idx_1784_; lean_object* v___y_1785_; lean_object* v_pos_1786_; lean_object* v_idx_1787_; lean_object* v_idx_1803_; lean_object* v___y_1804_; lean_object* v_pos_1805_; lean_object* v_idx_1806_; lean_object* v___f_1821_; lean_object* v_idx_1823_; lean_object* v___y_1824_; lean_object* v_pos_1825_; lean_object* v_idx_1826_; lean_object* v_idx_1842_; lean_object* v___y_1843_; lean_object* v_pos_1844_; lean_object* v_idx_1845_; lean_object* v___f_1860_; lean_object* v_idx_1862_; lean_object* v___y_1863_; lean_object* v_pos_1864_; lean_object* v_idx_1865_; lean_object* v_idx_1881_; lean_object* v___y_1882_; lean_object* v_pos_1883_; lean_object* v_idx_1884_; lean_object* v___f_1899_; lean_object* v_idx_1901_; lean_object* v___y_1902_; lean_object* v_pos_1903_; lean_object* v_idx_1904_; lean_object* v_idx_1920_; lean_object* v___y_1921_; lean_object* v_pos_1922_; lean_object* v_idx_1923_; lean_object* v___f_1938_; lean_object* v_idx_1940_; lean_object* v___y_1941_; lean_object* v_pos_1942_; lean_object* v_idx_1943_; lean_object* v___y_1959_; lean_object* v_pos_1960_; lean_object* v___f_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___f_1158_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__0));
v___f_1159_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__1));
v___f_1160_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2));
v___f_1161_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3));
v___f_1162_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4));
v___f_1163_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__5));
v___f_1164_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6));
v___f_1165_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7));
v___f_1166_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__8));
v___f_1167_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__9));
v___f_1168_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10));
v___f_1169_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11));
v___f_1170_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__12));
v___f_1171_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__13));
v___f_1172_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14));
v___f_1173_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15));
v___f_1174_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__16));
v___f_1175_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__17));
v___f_1176_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18));
v___f_1177_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19));
v___f_1178_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___f_1236_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__25));
v___f_1275_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__32));
v___f_1314_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39));
v___f_1353_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46));
v___f_1392_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__53));
v___f_1431_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__60));
v___f_1470_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67));
v___f_1509_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74));
v___f_1548_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__81));
v___f_1587_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__88));
v___f_1626_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95));
v___f_1665_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102));
v___f_1704_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__109));
v___f_1743_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__116));
v___f_1782_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123));
v___f_1821_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130));
v___f_1860_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__137));
v___f_1899_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__144));
v___f_1938_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151));
v___f_1977_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158));
v___x_1978_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161);
lean_inc_ref(v_a_1157_);
v___x_1979_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1978_, v___f_1977_, v_a_1157_);
if (lean_obj_tag(v___x_1979_) == 0)
{
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_dec_ref(v_a_1157_);
return v___x_1979_;
}
else
{
lean_object* v_pos_1980_; 
v_pos_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_pos_1980_);
v___y_1959_ = v___x_1979_;
v_pos_1960_ = v_pos_1980_;
goto v___jp_1958_;
}
}
else
{
lean_object* v_err_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
v_err_1981_ = lean_ctor_get(v___x_1979_, 1);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1988_ == 0)
{
lean_object* v_unused_1989_; 
v_unused_1989_ = lean_ctor_get(v___x_1979_, 0);
lean_dec(v_unused_1989_);
v___x_1983_ = v___x_1979_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_err_1981_);
lean_dec(v___x_1979_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
lean_inc_ref(v_a_1157_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v_a_1157_);
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1157_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_err_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
lean_inc_ref(v_a_1157_);
v___y_1959_ = v___x_1986_;
v_pos_1960_ = v_a_1157_;
goto v___jp_1958_;
}
}
}
v___jp_1179_:
{
uint8_t v___x_1184_; 
v___x_1184_ = lean_nat_dec_eq(v_idx_1180_, v_idx_1183_);
lean_dec(v_idx_1183_);
lean_dec(v_idx_1180_);
if (v___x_1184_ == 0)
{
lean_dec_ref(v_pos_1182_);
return v___y_1181_;
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v_snd_1188_; lean_object* v_snd_1189_; uint8_t v___x_1190_; 
lean_dec_ref(v___y_1181_);
v___x_1185_ = lean_unsigned_to_nat(64u);
v___x_1186_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pos_1182_);
v___x_1187_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1178_, v___x_1185_, v___x_1186_, v_pos_1182_);
v_snd_1188_ = lean_ctor_get(v___x_1187_, 1);
lean_inc(v_snd_1188_);
v_snd_1189_ = lean_ctor_get(v_snd_1188_, 1);
v___x_1190_ = lean_unbox(v_snd_1189_);
if (v___x_1190_ == 0)
{
lean_object* v_fst_1191_; lean_object* v_fst_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1205_; 
v_fst_1191_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_fst_1191_);
lean_dec_ref(v___x_1187_);
v_fst_1192_ = lean_ctor_get(v_snd_1188_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_snd_1188_);
if (v_isSharedCheck_1205_ == 0)
{
lean_object* v_unused_1206_; 
v_unused_1206_ = lean_ctor_get(v_snd_1188_, 1);
lean_dec(v_unused_1206_);
v___x_1194_ = v_snd_1188_;
v_isShared_1195_ = v_isSharedCheck_1205_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_fst_1192_);
lean_dec(v_snd_1188_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1205_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
uint8_t v___x_1196_; 
v___x_1196_ = lean_nat_dec_eq(v_fst_1191_, v___x_1186_);
lean_dec(v_fst_1191_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; lean_object* v___x_1199_; 
lean_dec_ref(v_pos_1182_);
v___x_1197_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__21));
if (v_isShared_1195_ == 0)
{
lean_ctor_set_tag(v___x_1194_, 1);
lean_ctor_set(v___x_1194_, 1, v___x_1197_);
v___x_1199_ = v___x_1194_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_fst_1192_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1203_; 
lean_dec(v_fst_1192_);
v___x_1201_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_1195_ == 0)
{
lean_ctor_set_tag(v___x_1194_, 1);
lean_ctor_set(v___x_1194_, 1, v___x_1201_);
lean_ctor_set(v___x_1194_, 0, v_pos_1182_);
v___x_1203_ = v___x_1194_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_pos_1182_);
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
}
else
{
lean_object* v_fst_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1215_; 
lean_dec_ref(v___x_1187_);
lean_dec_ref(v_pos_1182_);
v_fst_1207_ = lean_ctor_get(v_snd_1188_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_snd_1188_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; 
v_unused_1216_ = lean_ctor_get(v_snd_1188_, 1);
lean_dec(v_unused_1216_);
v___x_1209_ = v_snd_1188_;
v_isShared_1210_ = v_isSharedCheck_1215_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_fst_1207_);
lean_dec(v_snd_1188_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1215_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; lean_object* v___x_1213_; 
v___x_1211_ = lean_box(0);
if (v_isShared_1210_ == 0)
{
lean_ctor_set_tag(v___x_1209_, 1);
lean_ctor_set(v___x_1209_, 1, v___x_1211_);
v___x_1213_ = v___x_1209_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_fst_1207_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
}
v___jp_1217_:
{
uint8_t v___x_1222_; 
v___x_1222_ = lean_nat_dec_eq(v_idx_1218_, v_idx_1221_);
lean_dec(v_idx_1218_);
if (v___x_1222_ == 0)
{
lean_dec(v_idx_1221_);
lean_dec_ref(v_pos_1220_);
return v___y_1219_;
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec_ref(v___y_1219_);
v___x_1223_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24);
lean_inc_ref(v_pos_1220_);
v___x_1224_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1223_, v___f_1177_, v_pos_1220_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_dec_ref(v_pos_1220_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_dec(v_idx_1221_);
return v___x_1224_;
}
else
{
lean_object* v_pos_1225_; lean_object* v_idx_1226_; 
v_pos_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_pos_1225_);
v_idx_1226_ = lean_ctor_get(v_pos_1225_, 1);
lean_inc(v_idx_1226_);
v_idx_1180_ = v_idx_1221_;
v___y_1181_ = v___x_1224_;
v_pos_1182_ = v_pos_1225_;
v_idx_1183_ = v_idx_1226_;
goto v___jp_1179_;
}
}
else
{
lean_object* v_err_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
v_err_1227_ = lean_ctor_get(v___x_1224_, 1);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1234_ == 0)
{
lean_object* v_unused_1235_; 
v_unused_1235_ = lean_ctor_get(v___x_1224_, 0);
lean_dec(v_unused_1235_);
v___x_1229_ = v___x_1224_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_err_1227_);
lean_dec(v___x_1224_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
lean_inc_ref(v_pos_1220_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v_pos_1220_);
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_pos_1220_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_err_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_inc(v_idx_1221_);
v_idx_1180_ = v_idx_1221_;
v___y_1181_ = v___x_1232_;
v_pos_1182_ = v_pos_1220_;
v_idx_1183_ = v_idx_1221_;
goto v___jp_1179_;
}
}
}
}
}
v___jp_1237_:
{
uint8_t v___x_1242_; 
v___x_1242_ = lean_nat_dec_eq(v_idx_1238_, v_idx_1241_);
lean_dec(v_idx_1238_);
if (v___x_1242_ == 0)
{
lean_dec(v_idx_1241_);
lean_dec_ref(v_pos_1240_);
return v___y_1239_;
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_dec_ref(v___y_1239_);
v___x_1243_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28);
lean_inc_ref(v_pos_1240_);
v___x_1244_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1243_, v___f_1236_, v_pos_1240_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_dec_ref(v_pos_1240_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_dec(v_idx_1241_);
return v___x_1244_;
}
else
{
lean_object* v_pos_1245_; lean_object* v_idx_1246_; 
v_pos_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_pos_1245_);
v_idx_1246_ = lean_ctor_get(v_pos_1245_, 1);
lean_inc(v_idx_1246_);
v_idx_1218_ = v_idx_1241_;
v___y_1219_ = v___x_1244_;
v_pos_1220_ = v_pos_1245_;
v_idx_1221_ = v_idx_1246_;
goto v___jp_1217_;
}
}
else
{
lean_object* v_err_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
v_err_1247_ = lean_ctor_get(v___x_1244_, 1);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1254_ == 0)
{
lean_object* v_unused_1255_; 
v_unused_1255_ = lean_ctor_get(v___x_1244_, 0);
lean_dec(v_unused_1255_);
v___x_1249_ = v___x_1244_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_err_1247_);
lean_dec(v___x_1244_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
lean_inc_ref(v_pos_1240_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v_pos_1240_);
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_pos_1240_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_err_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_inc(v_idx_1241_);
v_idx_1218_ = v_idx_1241_;
v___y_1219_ = v___x_1252_;
v_pos_1220_ = v_pos_1240_;
v_idx_1221_ = v_idx_1241_;
goto v___jp_1217_;
}
}
}
}
}
v___jp_1256_:
{
uint8_t v___x_1261_; 
v___x_1261_ = lean_nat_dec_eq(v_idx_1257_, v_idx_1260_);
lean_dec(v_idx_1257_);
if (v___x_1261_ == 0)
{
lean_dec(v_idx_1260_);
lean_dec_ref(v_pos_1259_);
return v___y_1258_;
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
lean_dec_ref(v___y_1258_);
v___x_1262_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31);
lean_inc_ref(v_pos_1259_);
v___x_1263_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1262_, v___f_1176_, v_pos_1259_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_dec_ref(v_pos_1259_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_dec(v_idx_1260_);
return v___x_1263_;
}
else
{
lean_object* v_pos_1264_; lean_object* v_idx_1265_; 
v_pos_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_pos_1264_);
v_idx_1265_ = lean_ctor_get(v_pos_1264_, 1);
lean_inc(v_idx_1265_);
v_idx_1238_ = v_idx_1260_;
v___y_1239_ = v___x_1263_;
v_pos_1240_ = v_pos_1264_;
v_idx_1241_ = v_idx_1265_;
goto v___jp_1237_;
}
}
else
{
lean_object* v_err_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
v_err_1266_ = lean_ctor_get(v___x_1263_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1273_ == 0)
{
lean_object* v_unused_1274_; 
v_unused_1274_ = lean_ctor_get(v___x_1263_, 0);
lean_dec(v_unused_1274_);
v___x_1268_ = v___x_1263_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_err_1266_);
lean_dec(v___x_1263_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
lean_inc_ref(v_pos_1259_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v_pos_1259_);
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_pos_1259_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_err_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_inc(v_idx_1260_);
v_idx_1238_ = v_idx_1260_;
v___y_1239_ = v___x_1271_;
v_pos_1240_ = v_pos_1259_;
v_idx_1241_ = v_idx_1260_;
goto v___jp_1237_;
}
}
}
}
}
v___jp_1276_:
{
uint8_t v___x_1281_; 
v___x_1281_ = lean_nat_dec_eq(v_idx_1277_, v_idx_1280_);
lean_dec(v_idx_1277_);
if (v___x_1281_ == 0)
{
lean_dec(v_idx_1280_);
lean_dec_ref(v_pos_1279_);
return v___y_1278_;
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
lean_dec_ref(v___y_1278_);
v___x_1282_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35);
lean_inc_ref(v_pos_1279_);
v___x_1283_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1282_, v___f_1275_, v_pos_1279_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_dec_ref(v_pos_1279_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_dec(v_idx_1280_);
return v___x_1283_;
}
else
{
lean_object* v_pos_1284_; lean_object* v_idx_1285_; 
v_pos_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_pos_1284_);
v_idx_1285_ = lean_ctor_get(v_pos_1284_, 1);
lean_inc(v_idx_1285_);
v_idx_1257_ = v_idx_1280_;
v___y_1258_ = v___x_1283_;
v_pos_1259_ = v_pos_1284_;
v_idx_1260_ = v_idx_1285_;
goto v___jp_1256_;
}
}
else
{
lean_object* v_err_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
v_err_1286_ = lean_ctor_get(v___x_1283_, 1);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1293_ == 0)
{
lean_object* v_unused_1294_; 
v_unused_1294_ = lean_ctor_get(v___x_1283_, 0);
lean_dec(v_unused_1294_);
v___x_1288_ = v___x_1283_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_err_1286_);
lean_dec(v___x_1283_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
lean_inc_ref(v_pos_1279_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v_pos_1279_);
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_pos_1279_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_err_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
lean_inc(v_idx_1280_);
v_idx_1257_ = v_idx_1280_;
v___y_1258_ = v___x_1291_;
v_pos_1259_ = v_pos_1279_;
v_idx_1260_ = v_idx_1280_;
goto v___jp_1256_;
}
}
}
}
}
v___jp_1295_:
{
uint8_t v___x_1300_; 
v___x_1300_ = lean_nat_dec_eq(v_idx_1296_, v_idx_1299_);
lean_dec(v_idx_1296_);
if (v___x_1300_ == 0)
{
lean_dec(v_idx_1299_);
lean_dec_ref(v_pos_1298_);
return v___y_1297_;
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
lean_dec_ref(v___y_1297_);
v___x_1301_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38);
lean_inc_ref(v_pos_1298_);
v___x_1302_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1301_, v___f_1175_, v_pos_1298_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_dec_ref(v_pos_1298_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_dec(v_idx_1299_);
return v___x_1302_;
}
else
{
lean_object* v_pos_1303_; lean_object* v_idx_1304_; 
v_pos_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_pos_1303_);
v_idx_1304_ = lean_ctor_get(v_pos_1303_, 1);
lean_inc(v_idx_1304_);
v_idx_1277_ = v_idx_1299_;
v___y_1278_ = v___x_1302_;
v_pos_1279_ = v_pos_1303_;
v_idx_1280_ = v_idx_1304_;
goto v___jp_1276_;
}
}
else
{
lean_object* v_err_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
v_err_1305_ = lean_ctor_get(v___x_1302_, 1);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1312_ == 0)
{
lean_object* v_unused_1313_; 
v_unused_1313_ = lean_ctor_get(v___x_1302_, 0);
lean_dec(v_unused_1313_);
v___x_1307_ = v___x_1302_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_err_1305_);
lean_dec(v___x_1302_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
lean_inc_ref(v_pos_1298_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v_pos_1298_);
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_pos_1298_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_err_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
lean_inc(v_idx_1299_);
v_idx_1277_ = v_idx_1299_;
v___y_1278_ = v___x_1310_;
v_pos_1279_ = v_pos_1298_;
v_idx_1280_ = v_idx_1299_;
goto v___jp_1276_;
}
}
}
}
}
v___jp_1315_:
{
uint8_t v___x_1320_; 
v___x_1320_ = lean_nat_dec_eq(v_idx_1316_, v_idx_1319_);
lean_dec(v_idx_1316_);
if (v___x_1320_ == 0)
{
lean_dec(v_idx_1319_);
lean_dec_ref(v_pos_1318_);
return v___y_1317_;
}
else
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_dec_ref(v___y_1317_);
v___x_1321_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42);
lean_inc_ref(v_pos_1318_);
v___x_1322_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1321_, v___f_1314_, v_pos_1318_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_dec_ref(v_pos_1318_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_dec(v_idx_1319_);
return v___x_1322_;
}
else
{
lean_object* v_pos_1323_; lean_object* v_idx_1324_; 
v_pos_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_pos_1323_);
v_idx_1324_ = lean_ctor_get(v_pos_1323_, 1);
lean_inc(v_idx_1324_);
v_idx_1296_ = v_idx_1319_;
v___y_1297_ = v___x_1322_;
v_pos_1298_ = v_pos_1323_;
v_idx_1299_ = v_idx_1324_;
goto v___jp_1295_;
}
}
else
{
lean_object* v_err_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
v_err_1325_ = lean_ctor_get(v___x_1322_, 1);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1332_ == 0)
{
lean_object* v_unused_1333_; 
v_unused_1333_ = lean_ctor_get(v___x_1322_, 0);
lean_dec(v_unused_1333_);
v___x_1327_ = v___x_1322_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_err_1325_);
lean_dec(v___x_1322_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
lean_inc_ref(v_pos_1318_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v_pos_1318_);
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_pos_1318_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_err_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_inc(v_idx_1319_);
v_idx_1296_ = v_idx_1319_;
v___y_1297_ = v___x_1330_;
v_pos_1298_ = v_pos_1318_;
v_idx_1299_ = v_idx_1319_;
goto v___jp_1295_;
}
}
}
}
}
v___jp_1334_:
{
uint8_t v___x_1339_; 
v___x_1339_ = lean_nat_dec_eq(v_idx_1335_, v_idx_1338_);
lean_dec(v_idx_1335_);
if (v___x_1339_ == 0)
{
lean_dec(v_idx_1338_);
lean_dec_ref(v_pos_1337_);
return v___y_1336_;
}
else
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_dec_ref(v___y_1336_);
v___x_1340_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45);
lean_inc_ref(v_pos_1337_);
v___x_1341_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1340_, v___f_1174_, v_pos_1337_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_dec_ref(v_pos_1337_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_dec(v_idx_1338_);
return v___x_1341_;
}
else
{
lean_object* v_pos_1342_; lean_object* v_idx_1343_; 
v_pos_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_pos_1342_);
v_idx_1343_ = lean_ctor_get(v_pos_1342_, 1);
lean_inc(v_idx_1343_);
v_idx_1316_ = v_idx_1338_;
v___y_1317_ = v___x_1341_;
v_pos_1318_ = v_pos_1342_;
v_idx_1319_ = v_idx_1343_;
goto v___jp_1315_;
}
}
else
{
lean_object* v_err_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
v_err_1344_ = lean_ctor_get(v___x_1341_, 1);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1351_ == 0)
{
lean_object* v_unused_1352_; 
v_unused_1352_ = lean_ctor_get(v___x_1341_, 0);
lean_dec(v_unused_1352_);
v___x_1346_ = v___x_1341_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_err_1344_);
lean_dec(v___x_1341_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
lean_inc_ref(v_pos_1337_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v_pos_1337_);
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_pos_1337_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_err_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_inc(v_idx_1338_);
v_idx_1316_ = v_idx_1338_;
v___y_1317_ = v___x_1349_;
v_pos_1318_ = v_pos_1337_;
v_idx_1319_ = v_idx_1338_;
goto v___jp_1315_;
}
}
}
}
}
v___jp_1354_:
{
uint8_t v___x_1359_; 
v___x_1359_ = lean_nat_dec_eq(v_idx_1355_, v_idx_1358_);
lean_dec(v_idx_1355_);
if (v___x_1359_ == 0)
{
lean_dec(v_idx_1358_);
lean_dec_ref(v_pos_1357_);
return v___y_1356_;
}
else
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
lean_dec_ref(v___y_1356_);
v___x_1360_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49);
lean_inc_ref(v_pos_1357_);
v___x_1361_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1360_, v___f_1353_, v_pos_1357_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_dec_ref(v_pos_1357_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_dec(v_idx_1358_);
return v___x_1361_;
}
else
{
lean_object* v_pos_1362_; lean_object* v_idx_1363_; 
v_pos_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_pos_1362_);
v_idx_1363_ = lean_ctor_get(v_pos_1362_, 1);
lean_inc(v_idx_1363_);
v_idx_1335_ = v_idx_1358_;
v___y_1336_ = v___x_1361_;
v_pos_1337_ = v_pos_1362_;
v_idx_1338_ = v_idx_1363_;
goto v___jp_1334_;
}
}
else
{
lean_object* v_err_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
v_err_1364_ = lean_ctor_get(v___x_1361_, 1);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1371_ == 0)
{
lean_object* v_unused_1372_; 
v_unused_1372_ = lean_ctor_get(v___x_1361_, 0);
lean_dec(v_unused_1372_);
v___x_1366_ = v___x_1361_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_err_1364_);
lean_dec(v___x_1361_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
lean_inc_ref(v_pos_1357_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v_pos_1357_);
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_pos_1357_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_err_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_inc(v_idx_1358_);
v_idx_1335_ = v_idx_1358_;
v___y_1336_ = v___x_1369_;
v_pos_1337_ = v_pos_1357_;
v_idx_1338_ = v_idx_1358_;
goto v___jp_1334_;
}
}
}
}
}
v___jp_1373_:
{
uint8_t v___x_1378_; 
v___x_1378_ = lean_nat_dec_eq(v_idx_1374_, v_idx_1377_);
lean_dec(v_idx_1374_);
if (v___x_1378_ == 0)
{
lean_dec(v_idx_1377_);
lean_dec_ref(v_pos_1376_);
return v___y_1375_;
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
lean_dec_ref(v___y_1375_);
v___x_1379_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52);
lean_inc_ref(v_pos_1376_);
v___x_1380_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1379_, v___f_1173_, v_pos_1376_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_dec_ref(v_pos_1376_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_dec(v_idx_1377_);
return v___x_1380_;
}
else
{
lean_object* v_pos_1381_; lean_object* v_idx_1382_; 
v_pos_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_pos_1381_);
v_idx_1382_ = lean_ctor_get(v_pos_1381_, 1);
lean_inc(v_idx_1382_);
v_idx_1355_ = v_idx_1377_;
v___y_1356_ = v___x_1380_;
v_pos_1357_ = v_pos_1381_;
v_idx_1358_ = v_idx_1382_;
goto v___jp_1354_;
}
}
else
{
lean_object* v_err_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
v_err_1383_ = lean_ctor_get(v___x_1380_, 1);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1390_ == 0)
{
lean_object* v_unused_1391_; 
v_unused_1391_ = lean_ctor_get(v___x_1380_, 0);
lean_dec(v_unused_1391_);
v___x_1385_ = v___x_1380_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_err_1383_);
lean_dec(v___x_1380_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
lean_inc_ref(v_pos_1376_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v_pos_1376_);
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_pos_1376_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_err_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_inc(v_idx_1377_);
v_idx_1355_ = v_idx_1377_;
v___y_1356_ = v___x_1388_;
v_pos_1357_ = v_pos_1376_;
v_idx_1358_ = v_idx_1377_;
goto v___jp_1354_;
}
}
}
}
}
v___jp_1393_:
{
uint8_t v___x_1398_; 
v___x_1398_ = lean_nat_dec_eq(v_idx_1394_, v_idx_1397_);
lean_dec(v_idx_1394_);
if (v___x_1398_ == 0)
{
lean_dec(v_idx_1397_);
lean_dec_ref(v_pos_1396_);
return v___y_1395_;
}
else
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_dec_ref(v___y_1395_);
v___x_1399_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56);
lean_inc_ref(v_pos_1396_);
v___x_1400_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1399_, v___f_1392_, v_pos_1396_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_dec_ref(v_pos_1396_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_dec(v_idx_1397_);
return v___x_1400_;
}
else
{
lean_object* v_pos_1401_; lean_object* v_idx_1402_; 
v_pos_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_pos_1401_);
v_idx_1402_ = lean_ctor_get(v_pos_1401_, 1);
lean_inc(v_idx_1402_);
v_idx_1374_ = v_idx_1397_;
v___y_1375_ = v___x_1400_;
v_pos_1376_ = v_pos_1401_;
v_idx_1377_ = v_idx_1402_;
goto v___jp_1373_;
}
}
else
{
lean_object* v_err_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
v_err_1403_ = lean_ctor_get(v___x_1400_, 1);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1410_ == 0)
{
lean_object* v_unused_1411_; 
v_unused_1411_ = lean_ctor_get(v___x_1400_, 0);
lean_dec(v_unused_1411_);
v___x_1405_ = v___x_1400_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_err_1403_);
lean_dec(v___x_1400_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
lean_inc_ref(v_pos_1396_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v_pos_1396_);
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_pos_1396_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_err_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_inc(v_idx_1397_);
v_idx_1374_ = v_idx_1397_;
v___y_1375_ = v___x_1408_;
v_pos_1376_ = v_pos_1396_;
v_idx_1377_ = v_idx_1397_;
goto v___jp_1373_;
}
}
}
}
}
v___jp_1412_:
{
uint8_t v___x_1417_; 
v___x_1417_ = lean_nat_dec_eq(v_idx_1413_, v_idx_1416_);
lean_dec(v_idx_1413_);
if (v___x_1417_ == 0)
{
lean_dec(v_idx_1416_);
lean_dec_ref(v_pos_1415_);
return v___y_1414_;
}
else
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
lean_dec_ref(v___y_1414_);
v___x_1418_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59);
lean_inc_ref(v_pos_1415_);
v___x_1419_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1418_, v___f_1172_, v_pos_1415_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_dec_ref(v_pos_1415_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_dec(v_idx_1416_);
return v___x_1419_;
}
else
{
lean_object* v_pos_1420_; lean_object* v_idx_1421_; 
v_pos_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_pos_1420_);
v_idx_1421_ = lean_ctor_get(v_pos_1420_, 1);
lean_inc(v_idx_1421_);
v_idx_1394_ = v_idx_1416_;
v___y_1395_ = v___x_1419_;
v_pos_1396_ = v_pos_1420_;
v_idx_1397_ = v_idx_1421_;
goto v___jp_1393_;
}
}
else
{
lean_object* v_err_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
v_err_1422_ = lean_ctor_get(v___x_1419_, 1);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; 
v_unused_1430_ = lean_ctor_get(v___x_1419_, 0);
lean_dec(v_unused_1430_);
v___x_1424_ = v___x_1419_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_err_1422_);
lean_dec(v___x_1419_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
lean_inc_ref(v_pos_1415_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v_pos_1415_);
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_pos_1415_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_err_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_inc(v_idx_1416_);
v_idx_1394_ = v_idx_1416_;
v___y_1395_ = v___x_1427_;
v_pos_1396_ = v_pos_1415_;
v_idx_1397_ = v_idx_1416_;
goto v___jp_1393_;
}
}
}
}
}
v___jp_1432_:
{
uint8_t v___x_1437_; 
v___x_1437_ = lean_nat_dec_eq(v_idx_1433_, v_idx_1436_);
lean_dec(v_idx_1433_);
if (v___x_1437_ == 0)
{
lean_dec(v_idx_1436_);
lean_dec_ref(v_pos_1435_);
return v___y_1434_;
}
else
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
lean_dec_ref(v___y_1434_);
v___x_1438_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63);
lean_inc_ref(v_pos_1435_);
v___x_1439_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1438_, v___f_1431_, v_pos_1435_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_dec_ref(v_pos_1435_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_dec(v_idx_1436_);
return v___x_1439_;
}
else
{
lean_object* v_pos_1440_; lean_object* v_idx_1441_; 
v_pos_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_pos_1440_);
v_idx_1441_ = lean_ctor_get(v_pos_1440_, 1);
lean_inc(v_idx_1441_);
v_idx_1413_ = v_idx_1436_;
v___y_1414_ = v___x_1439_;
v_pos_1415_ = v_pos_1440_;
v_idx_1416_ = v_idx_1441_;
goto v___jp_1412_;
}
}
else
{
lean_object* v_err_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
v_err_1442_ = lean_ctor_get(v___x_1439_, 1);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1449_ == 0)
{
lean_object* v_unused_1450_; 
v_unused_1450_ = lean_ctor_get(v___x_1439_, 0);
lean_dec(v_unused_1450_);
v___x_1444_ = v___x_1439_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_err_1442_);
lean_dec(v___x_1439_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
lean_inc_ref(v_pos_1435_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v_pos_1435_);
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_pos_1435_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_err_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_inc(v_idx_1436_);
v_idx_1413_ = v_idx_1436_;
v___y_1414_ = v___x_1447_;
v_pos_1415_ = v_pos_1435_;
v_idx_1416_ = v_idx_1436_;
goto v___jp_1412_;
}
}
}
}
}
v___jp_1451_:
{
uint8_t v___x_1456_; 
v___x_1456_ = lean_nat_dec_eq(v_idx_1452_, v_idx_1455_);
lean_dec(v_idx_1452_);
if (v___x_1456_ == 0)
{
lean_dec(v_idx_1455_);
lean_dec_ref(v_pos_1454_);
return v___y_1453_;
}
else
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_dec_ref(v___y_1453_);
v___x_1457_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66);
lean_inc_ref(v_pos_1454_);
v___x_1458_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1457_, v___f_1171_, v_pos_1454_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_dec_ref(v_pos_1454_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_dec(v_idx_1455_);
return v___x_1458_;
}
else
{
lean_object* v_pos_1459_; lean_object* v_idx_1460_; 
v_pos_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_pos_1459_);
v_idx_1460_ = lean_ctor_get(v_pos_1459_, 1);
lean_inc(v_idx_1460_);
v_idx_1433_ = v_idx_1455_;
v___y_1434_ = v___x_1458_;
v_pos_1435_ = v_pos_1459_;
v_idx_1436_ = v_idx_1460_;
goto v___jp_1432_;
}
}
else
{
lean_object* v_err_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
v_err_1461_ = lean_ctor_get(v___x_1458_, 1);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1468_ == 0)
{
lean_object* v_unused_1469_; 
v_unused_1469_ = lean_ctor_get(v___x_1458_, 0);
lean_dec(v_unused_1469_);
v___x_1463_ = v___x_1458_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_err_1461_);
lean_dec(v___x_1458_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
lean_inc_ref(v_pos_1454_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 0, v_pos_1454_);
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_pos_1454_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_err_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_inc(v_idx_1455_);
v_idx_1433_ = v_idx_1455_;
v___y_1434_ = v___x_1466_;
v_pos_1435_ = v_pos_1454_;
v_idx_1436_ = v_idx_1455_;
goto v___jp_1432_;
}
}
}
}
}
v___jp_1471_:
{
uint8_t v___x_1476_; 
v___x_1476_ = lean_nat_dec_eq(v_idx_1472_, v_idx_1475_);
lean_dec(v_idx_1472_);
if (v___x_1476_ == 0)
{
lean_dec(v_idx_1475_);
lean_dec_ref(v_pos_1474_);
return v___y_1473_;
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_dec_ref(v___y_1473_);
v___x_1477_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70);
lean_inc_ref(v_pos_1474_);
v___x_1478_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1477_, v___f_1470_, v_pos_1474_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_dec_ref(v_pos_1474_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_dec(v_idx_1475_);
return v___x_1478_;
}
else
{
lean_object* v_pos_1479_; lean_object* v_idx_1480_; 
v_pos_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_pos_1479_);
v_idx_1480_ = lean_ctor_get(v_pos_1479_, 1);
lean_inc(v_idx_1480_);
v_idx_1452_ = v_idx_1475_;
v___y_1453_ = v___x_1478_;
v_pos_1454_ = v_pos_1479_;
v_idx_1455_ = v_idx_1480_;
goto v___jp_1451_;
}
}
else
{
lean_object* v_err_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
v_err_1481_ = lean_ctor_get(v___x_1478_, 1);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1488_ == 0)
{
lean_object* v_unused_1489_; 
v_unused_1489_ = lean_ctor_get(v___x_1478_, 0);
lean_dec(v_unused_1489_);
v___x_1483_ = v___x_1478_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_err_1481_);
lean_dec(v___x_1478_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
lean_inc_ref(v_pos_1474_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v_pos_1474_);
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_pos_1474_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_err_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_inc(v_idx_1475_);
v_idx_1452_ = v_idx_1475_;
v___y_1453_ = v___x_1486_;
v_pos_1454_ = v_pos_1474_;
v_idx_1455_ = v_idx_1475_;
goto v___jp_1451_;
}
}
}
}
}
v___jp_1490_:
{
uint8_t v___x_1495_; 
v___x_1495_ = lean_nat_dec_eq(v_idx_1491_, v_idx_1494_);
lean_dec(v_idx_1491_);
if (v___x_1495_ == 0)
{
lean_dec(v_idx_1494_);
lean_dec_ref(v_pos_1493_);
return v___y_1492_;
}
else
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
lean_dec_ref(v___y_1492_);
v___x_1496_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73);
lean_inc_ref(v_pos_1493_);
v___x_1497_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1496_, v___f_1170_, v_pos_1493_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_dec_ref(v_pos_1493_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_dec(v_idx_1494_);
return v___x_1497_;
}
else
{
lean_object* v_pos_1498_; lean_object* v_idx_1499_; 
v_pos_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_pos_1498_);
v_idx_1499_ = lean_ctor_get(v_pos_1498_, 1);
lean_inc(v_idx_1499_);
v_idx_1472_ = v_idx_1494_;
v___y_1473_ = v___x_1497_;
v_pos_1474_ = v_pos_1498_;
v_idx_1475_ = v_idx_1499_;
goto v___jp_1471_;
}
}
else
{
lean_object* v_err_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
v_err_1500_ = lean_ctor_get(v___x_1497_, 1);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1507_ == 0)
{
lean_object* v_unused_1508_; 
v_unused_1508_ = lean_ctor_get(v___x_1497_, 0);
lean_dec(v_unused_1508_);
v___x_1502_ = v___x_1497_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_err_1500_);
lean_dec(v___x_1497_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
lean_inc_ref(v_pos_1493_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v_pos_1493_);
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_pos_1493_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_err_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
lean_inc(v_idx_1494_);
v_idx_1472_ = v_idx_1494_;
v___y_1473_ = v___x_1505_;
v_pos_1474_ = v_pos_1493_;
v_idx_1475_ = v_idx_1494_;
goto v___jp_1471_;
}
}
}
}
}
v___jp_1510_:
{
uint8_t v___x_1515_; 
v___x_1515_ = lean_nat_dec_eq(v_idx_1511_, v_idx_1514_);
lean_dec(v_idx_1511_);
if (v___x_1515_ == 0)
{
lean_dec(v_idx_1514_);
lean_dec_ref(v_pos_1513_);
return v___y_1512_;
}
else
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_dec_ref(v___y_1512_);
v___x_1516_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77);
lean_inc_ref(v_pos_1513_);
v___x_1517_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1516_, v___f_1509_, v_pos_1513_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_dec_ref(v_pos_1513_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_dec(v_idx_1514_);
return v___x_1517_;
}
else
{
lean_object* v_pos_1518_; lean_object* v_idx_1519_; 
v_pos_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_pos_1518_);
v_idx_1519_ = lean_ctor_get(v_pos_1518_, 1);
lean_inc(v_idx_1519_);
v_idx_1491_ = v_idx_1514_;
v___y_1492_ = v___x_1517_;
v_pos_1493_ = v_pos_1518_;
v_idx_1494_ = v_idx_1519_;
goto v___jp_1490_;
}
}
else
{
lean_object* v_err_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
v_err_1520_ = lean_ctor_get(v___x_1517_, 1);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1527_ == 0)
{
lean_object* v_unused_1528_; 
v_unused_1528_ = lean_ctor_get(v___x_1517_, 0);
lean_dec(v_unused_1528_);
v___x_1522_ = v___x_1517_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_err_1520_);
lean_dec(v___x_1517_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
lean_inc_ref(v_pos_1513_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v_pos_1513_);
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_pos_1513_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_err_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_inc(v_idx_1514_);
v_idx_1491_ = v_idx_1514_;
v___y_1492_ = v___x_1525_;
v_pos_1493_ = v_pos_1513_;
v_idx_1494_ = v_idx_1514_;
goto v___jp_1490_;
}
}
}
}
}
v___jp_1529_:
{
uint8_t v___x_1534_; 
v___x_1534_ = lean_nat_dec_eq(v_idx_1530_, v_idx_1533_);
lean_dec(v_idx_1530_);
if (v___x_1534_ == 0)
{
lean_dec(v_idx_1533_);
lean_dec_ref(v_pos_1532_);
return v___y_1531_;
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_dec_ref(v___y_1531_);
v___x_1535_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80);
lean_inc_ref(v_pos_1532_);
v___x_1536_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1535_, v___f_1169_, v_pos_1532_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_dec_ref(v_pos_1532_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_dec(v_idx_1533_);
return v___x_1536_;
}
else
{
lean_object* v_pos_1537_; lean_object* v_idx_1538_; 
v_pos_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_pos_1537_);
v_idx_1538_ = lean_ctor_get(v_pos_1537_, 1);
lean_inc(v_idx_1538_);
v_idx_1511_ = v_idx_1533_;
v___y_1512_ = v___x_1536_;
v_pos_1513_ = v_pos_1537_;
v_idx_1514_ = v_idx_1538_;
goto v___jp_1510_;
}
}
else
{
lean_object* v_err_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
v_err_1539_ = lean_ctor_get(v___x_1536_, 1);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; 
v_unused_1547_ = lean_ctor_get(v___x_1536_, 0);
lean_dec(v_unused_1547_);
v___x_1541_ = v___x_1536_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_err_1539_);
lean_dec(v___x_1536_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
lean_inc_ref(v_pos_1532_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v_pos_1532_);
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_pos_1532_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_err_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_inc(v_idx_1533_);
v_idx_1511_ = v_idx_1533_;
v___y_1512_ = v___x_1544_;
v_pos_1513_ = v_pos_1532_;
v_idx_1514_ = v_idx_1533_;
goto v___jp_1510_;
}
}
}
}
}
v___jp_1549_:
{
uint8_t v___x_1554_; 
v___x_1554_ = lean_nat_dec_eq(v_idx_1550_, v_idx_1553_);
lean_dec(v_idx_1550_);
if (v___x_1554_ == 0)
{
lean_dec(v_idx_1553_);
lean_dec_ref(v_pos_1552_);
return v___y_1551_;
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
lean_dec_ref(v___y_1551_);
v___x_1555_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84);
lean_inc_ref(v_pos_1552_);
v___x_1556_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1555_, v___f_1548_, v_pos_1552_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_dec_ref(v_pos_1552_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_dec(v_idx_1553_);
return v___x_1556_;
}
else
{
lean_object* v_pos_1557_; lean_object* v_idx_1558_; 
v_pos_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_pos_1557_);
v_idx_1558_ = lean_ctor_get(v_pos_1557_, 1);
lean_inc(v_idx_1558_);
v_idx_1530_ = v_idx_1553_;
v___y_1531_ = v___x_1556_;
v_pos_1532_ = v_pos_1557_;
v_idx_1533_ = v_idx_1558_;
goto v___jp_1529_;
}
}
else
{
lean_object* v_err_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
v_err_1559_ = lean_ctor_get(v___x_1556_, 1);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1566_ == 0)
{
lean_object* v_unused_1567_; 
v_unused_1567_ = lean_ctor_get(v___x_1556_, 0);
lean_dec(v_unused_1567_);
v___x_1561_ = v___x_1556_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_err_1559_);
lean_dec(v___x_1556_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
lean_inc_ref(v_pos_1552_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v_pos_1552_);
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_pos_1552_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v_err_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_inc(v_idx_1553_);
v_idx_1530_ = v_idx_1553_;
v___y_1531_ = v___x_1564_;
v_pos_1532_ = v_pos_1552_;
v_idx_1533_ = v_idx_1553_;
goto v___jp_1529_;
}
}
}
}
}
v___jp_1568_:
{
uint8_t v___x_1573_; 
v___x_1573_ = lean_nat_dec_eq(v_idx_1569_, v_idx_1572_);
lean_dec(v_idx_1569_);
if (v___x_1573_ == 0)
{
lean_dec(v_idx_1572_);
lean_dec_ref(v_pos_1571_);
return v___y_1570_;
}
else
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
lean_dec_ref(v___y_1570_);
v___x_1574_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87);
lean_inc_ref(v_pos_1571_);
v___x_1575_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1574_, v___f_1168_, v_pos_1571_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_dec_ref(v_pos_1571_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_dec(v_idx_1572_);
return v___x_1575_;
}
else
{
lean_object* v_pos_1576_; lean_object* v_idx_1577_; 
v_pos_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_pos_1576_);
v_idx_1577_ = lean_ctor_get(v_pos_1576_, 1);
lean_inc(v_idx_1577_);
v_idx_1550_ = v_idx_1572_;
v___y_1551_ = v___x_1575_;
v_pos_1552_ = v_pos_1576_;
v_idx_1553_ = v_idx_1577_;
goto v___jp_1549_;
}
}
else
{
lean_object* v_err_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
v_err_1578_ = lean_ctor_get(v___x_1575_, 1);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1585_ == 0)
{
lean_object* v_unused_1586_; 
v_unused_1586_ = lean_ctor_get(v___x_1575_, 0);
lean_dec(v_unused_1586_);
v___x_1580_ = v___x_1575_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_err_1578_);
lean_dec(v___x_1575_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
lean_inc_ref(v_pos_1571_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v_pos_1571_);
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_pos_1571_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_err_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_inc(v_idx_1572_);
v_idx_1550_ = v_idx_1572_;
v___y_1551_ = v___x_1583_;
v_pos_1552_ = v_pos_1571_;
v_idx_1553_ = v_idx_1572_;
goto v___jp_1549_;
}
}
}
}
}
v___jp_1588_:
{
uint8_t v___x_1593_; 
v___x_1593_ = lean_nat_dec_eq(v_idx_1589_, v_idx_1592_);
lean_dec(v_idx_1589_);
if (v___x_1593_ == 0)
{
lean_dec(v_idx_1592_);
lean_dec_ref(v_pos_1591_);
return v___y_1590_;
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
lean_dec_ref(v___y_1590_);
v___x_1594_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91);
lean_inc_ref(v_pos_1591_);
v___x_1595_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1594_, v___f_1587_, v_pos_1591_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_dec_ref(v_pos_1591_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_dec(v_idx_1592_);
return v___x_1595_;
}
else
{
lean_object* v_pos_1596_; lean_object* v_idx_1597_; 
v_pos_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_pos_1596_);
v_idx_1597_ = lean_ctor_get(v_pos_1596_, 1);
lean_inc(v_idx_1597_);
v_idx_1569_ = v_idx_1592_;
v___y_1570_ = v___x_1595_;
v_pos_1571_ = v_pos_1596_;
v_idx_1572_ = v_idx_1597_;
goto v___jp_1568_;
}
}
else
{
lean_object* v_err_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
v_err_1598_ = lean_ctor_get(v___x_1595_, 1);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; 
v_unused_1606_ = lean_ctor_get(v___x_1595_, 0);
lean_dec(v_unused_1606_);
v___x_1600_ = v___x_1595_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_err_1598_);
lean_dec(v___x_1595_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
lean_inc_ref(v_pos_1591_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v_pos_1591_);
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_pos_1591_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_err_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_inc(v_idx_1592_);
v_idx_1569_ = v_idx_1592_;
v___y_1570_ = v___x_1603_;
v_pos_1571_ = v_pos_1591_;
v_idx_1572_ = v_idx_1592_;
goto v___jp_1568_;
}
}
}
}
}
v___jp_1607_:
{
uint8_t v___x_1612_; 
v___x_1612_ = lean_nat_dec_eq(v_idx_1608_, v_idx_1611_);
lean_dec(v_idx_1608_);
if (v___x_1612_ == 0)
{
lean_dec(v_idx_1611_);
lean_dec_ref(v_pos_1610_);
return v___y_1609_;
}
else
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
lean_dec_ref(v___y_1609_);
v___x_1613_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94);
lean_inc_ref(v_pos_1610_);
v___x_1614_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1613_, v___f_1167_, v_pos_1610_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_dec_ref(v_pos_1610_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_dec(v_idx_1611_);
return v___x_1614_;
}
else
{
lean_object* v_pos_1615_; lean_object* v_idx_1616_; 
v_pos_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_pos_1615_);
v_idx_1616_ = lean_ctor_get(v_pos_1615_, 1);
lean_inc(v_idx_1616_);
v_idx_1589_ = v_idx_1611_;
v___y_1590_ = v___x_1614_;
v_pos_1591_ = v_pos_1615_;
v_idx_1592_ = v_idx_1616_;
goto v___jp_1588_;
}
}
else
{
lean_object* v_err_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
v_err_1617_ = lean_ctor_get(v___x_1614_, 1);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1624_ == 0)
{
lean_object* v_unused_1625_; 
v_unused_1625_ = lean_ctor_get(v___x_1614_, 0);
lean_dec(v_unused_1625_);
v___x_1619_ = v___x_1614_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_err_1617_);
lean_dec(v___x_1614_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
lean_inc_ref(v_pos_1610_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 0, v_pos_1610_);
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_pos_1610_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_err_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_inc(v_idx_1611_);
v_idx_1589_ = v_idx_1611_;
v___y_1590_ = v___x_1622_;
v_pos_1591_ = v_pos_1610_;
v_idx_1592_ = v_idx_1611_;
goto v___jp_1588_;
}
}
}
}
}
v___jp_1627_:
{
uint8_t v___x_1632_; 
v___x_1632_ = lean_nat_dec_eq(v_idx_1628_, v_idx_1631_);
lean_dec(v_idx_1628_);
if (v___x_1632_ == 0)
{
lean_dec(v_idx_1631_);
lean_dec_ref(v_pos_1630_);
return v___y_1629_;
}
else
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
lean_dec_ref(v___y_1629_);
v___x_1633_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98);
lean_inc_ref(v_pos_1630_);
v___x_1634_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1633_, v___f_1626_, v_pos_1630_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_dec_ref(v_pos_1630_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_dec(v_idx_1631_);
return v___x_1634_;
}
else
{
lean_object* v_pos_1635_; lean_object* v_idx_1636_; 
v_pos_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_pos_1635_);
v_idx_1636_ = lean_ctor_get(v_pos_1635_, 1);
lean_inc(v_idx_1636_);
v_idx_1608_ = v_idx_1631_;
v___y_1609_ = v___x_1634_;
v_pos_1610_ = v_pos_1635_;
v_idx_1611_ = v_idx_1636_;
goto v___jp_1607_;
}
}
else
{
lean_object* v_err_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
v_err_1637_ = lean_ctor_get(v___x_1634_, 1);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1644_ == 0)
{
lean_object* v_unused_1645_; 
v_unused_1645_ = lean_ctor_get(v___x_1634_, 0);
lean_dec(v_unused_1645_);
v___x_1639_ = v___x_1634_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_err_1637_);
lean_dec(v___x_1634_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
lean_inc_ref(v_pos_1630_);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v_pos_1630_);
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_pos_1630_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_err_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
lean_inc(v_idx_1631_);
v_idx_1608_ = v_idx_1631_;
v___y_1609_ = v___x_1642_;
v_pos_1610_ = v_pos_1630_;
v_idx_1611_ = v_idx_1631_;
goto v___jp_1607_;
}
}
}
}
}
v___jp_1646_:
{
uint8_t v___x_1651_; 
v___x_1651_ = lean_nat_dec_eq(v_idx_1647_, v_idx_1650_);
lean_dec(v_idx_1647_);
if (v___x_1651_ == 0)
{
lean_dec(v_idx_1650_);
lean_dec_ref(v_pos_1649_);
return v___y_1648_;
}
else
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
lean_dec_ref(v___y_1648_);
v___x_1652_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101);
lean_inc_ref(v_pos_1649_);
v___x_1653_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1652_, v___f_1166_, v_pos_1649_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_dec_ref(v_pos_1649_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_dec(v_idx_1650_);
return v___x_1653_;
}
else
{
lean_object* v_pos_1654_; lean_object* v_idx_1655_; 
v_pos_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_pos_1654_);
v_idx_1655_ = lean_ctor_get(v_pos_1654_, 1);
lean_inc(v_idx_1655_);
v_idx_1628_ = v_idx_1650_;
v___y_1629_ = v___x_1653_;
v_pos_1630_ = v_pos_1654_;
v_idx_1631_ = v_idx_1655_;
goto v___jp_1627_;
}
}
else
{
lean_object* v_err_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
v_err_1656_ = lean_ctor_get(v___x_1653_, 1);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1663_ == 0)
{
lean_object* v_unused_1664_; 
v_unused_1664_ = lean_ctor_get(v___x_1653_, 0);
lean_dec(v_unused_1664_);
v___x_1658_ = v___x_1653_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_err_1656_);
lean_dec(v___x_1653_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
lean_inc_ref(v_pos_1649_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v_pos_1649_);
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_pos_1649_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_err_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_inc(v_idx_1650_);
v_idx_1628_ = v_idx_1650_;
v___y_1629_ = v___x_1661_;
v_pos_1630_ = v_pos_1649_;
v_idx_1631_ = v_idx_1650_;
goto v___jp_1627_;
}
}
}
}
}
v___jp_1666_:
{
uint8_t v___x_1671_; 
v___x_1671_ = lean_nat_dec_eq(v_idx_1667_, v_idx_1670_);
lean_dec(v_idx_1667_);
if (v___x_1671_ == 0)
{
lean_dec(v_idx_1670_);
lean_dec_ref(v_pos_1669_);
return v___y_1668_;
}
else
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
lean_dec_ref(v___y_1668_);
v___x_1672_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105);
lean_inc_ref(v_pos_1669_);
v___x_1673_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1672_, v___f_1665_, v_pos_1669_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_dec_ref(v_pos_1669_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_dec(v_idx_1670_);
return v___x_1673_;
}
else
{
lean_object* v_pos_1674_; lean_object* v_idx_1675_; 
v_pos_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_pos_1674_);
v_idx_1675_ = lean_ctor_get(v_pos_1674_, 1);
lean_inc(v_idx_1675_);
v_idx_1647_ = v_idx_1670_;
v___y_1648_ = v___x_1673_;
v_pos_1649_ = v_pos_1674_;
v_idx_1650_ = v_idx_1675_;
goto v___jp_1646_;
}
}
else
{
lean_object* v_err_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
v_err_1676_ = lean_ctor_get(v___x_1673_, 1);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1683_ == 0)
{
lean_object* v_unused_1684_; 
v_unused_1684_ = lean_ctor_get(v___x_1673_, 0);
lean_dec(v_unused_1684_);
v___x_1678_ = v___x_1673_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_err_1676_);
lean_dec(v___x_1673_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
lean_inc_ref(v_pos_1669_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v_pos_1669_);
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_pos_1669_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_err_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_inc(v_idx_1670_);
v_idx_1647_ = v_idx_1670_;
v___y_1648_ = v___x_1681_;
v_pos_1649_ = v_pos_1669_;
v_idx_1650_ = v_idx_1670_;
goto v___jp_1646_;
}
}
}
}
}
v___jp_1685_:
{
uint8_t v___x_1690_; 
v___x_1690_ = lean_nat_dec_eq(v_idx_1686_, v_idx_1689_);
lean_dec(v_idx_1686_);
if (v___x_1690_ == 0)
{
lean_dec(v_idx_1689_);
lean_dec_ref(v_pos_1688_);
return v___y_1687_;
}
else
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
lean_dec_ref(v___y_1687_);
v___x_1691_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108);
lean_inc_ref(v_pos_1688_);
v___x_1692_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1691_, v___f_1165_, v_pos_1688_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_dec_ref(v_pos_1688_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_dec(v_idx_1689_);
return v___x_1692_;
}
else
{
lean_object* v_pos_1693_; lean_object* v_idx_1694_; 
v_pos_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_pos_1693_);
v_idx_1694_ = lean_ctor_get(v_pos_1693_, 1);
lean_inc(v_idx_1694_);
v_idx_1667_ = v_idx_1689_;
v___y_1668_ = v___x_1692_;
v_pos_1669_ = v_pos_1693_;
v_idx_1670_ = v_idx_1694_;
goto v___jp_1666_;
}
}
else
{
lean_object* v_err_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
v_err_1695_ = lean_ctor_get(v___x_1692_, 1);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1702_ == 0)
{
lean_object* v_unused_1703_; 
v_unused_1703_ = lean_ctor_get(v___x_1692_, 0);
lean_dec(v_unused_1703_);
v___x_1697_ = v___x_1692_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_err_1695_);
lean_dec(v___x_1692_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
lean_inc_ref(v_pos_1688_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 0, v_pos_1688_);
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_pos_1688_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v_err_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
lean_inc(v_idx_1689_);
v_idx_1667_ = v_idx_1689_;
v___y_1668_ = v___x_1700_;
v_pos_1669_ = v_pos_1688_;
v_idx_1670_ = v_idx_1689_;
goto v___jp_1666_;
}
}
}
}
}
v___jp_1705_:
{
uint8_t v___x_1710_; 
v___x_1710_ = lean_nat_dec_eq(v_idx_1706_, v_idx_1709_);
lean_dec(v_idx_1706_);
if (v___x_1710_ == 0)
{
lean_dec(v_idx_1709_);
lean_dec_ref(v_pos_1708_);
return v___y_1707_;
}
else
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
lean_dec_ref(v___y_1707_);
v___x_1711_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112);
lean_inc_ref(v_pos_1708_);
v___x_1712_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1711_, v___f_1704_, v_pos_1708_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_dec_ref(v_pos_1708_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_dec(v_idx_1709_);
return v___x_1712_;
}
else
{
lean_object* v_pos_1713_; lean_object* v_idx_1714_; 
v_pos_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_pos_1713_);
v_idx_1714_ = lean_ctor_get(v_pos_1713_, 1);
lean_inc(v_idx_1714_);
v_idx_1686_ = v_idx_1709_;
v___y_1687_ = v___x_1712_;
v_pos_1688_ = v_pos_1713_;
v_idx_1689_ = v_idx_1714_;
goto v___jp_1685_;
}
}
else
{
lean_object* v_err_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
v_err_1715_ = lean_ctor_get(v___x_1712_, 1);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1722_ == 0)
{
lean_object* v_unused_1723_; 
v_unused_1723_ = lean_ctor_get(v___x_1712_, 0);
lean_dec(v_unused_1723_);
v___x_1717_ = v___x_1712_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_err_1715_);
lean_dec(v___x_1712_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
lean_inc_ref(v_pos_1708_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v_pos_1708_);
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_pos_1708_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_err_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_inc(v_idx_1709_);
v_idx_1686_ = v_idx_1709_;
v___y_1687_ = v___x_1720_;
v_pos_1688_ = v_pos_1708_;
v_idx_1689_ = v_idx_1709_;
goto v___jp_1685_;
}
}
}
}
}
v___jp_1724_:
{
uint8_t v___x_1729_; 
v___x_1729_ = lean_nat_dec_eq(v_idx_1725_, v_idx_1728_);
lean_dec(v_idx_1725_);
if (v___x_1729_ == 0)
{
lean_dec(v_idx_1728_);
lean_dec_ref(v_pos_1727_);
return v___y_1726_;
}
else
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_dec_ref(v___y_1726_);
v___x_1730_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115);
lean_inc_ref(v_pos_1727_);
v___x_1731_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1730_, v___f_1164_, v_pos_1727_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_dec_ref(v_pos_1727_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_dec(v_idx_1728_);
return v___x_1731_;
}
else
{
lean_object* v_pos_1732_; lean_object* v_idx_1733_; 
v_pos_1732_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_pos_1732_);
v_idx_1733_ = lean_ctor_get(v_pos_1732_, 1);
lean_inc(v_idx_1733_);
v_idx_1706_ = v_idx_1728_;
v___y_1707_ = v___x_1731_;
v_pos_1708_ = v_pos_1732_;
v_idx_1709_ = v_idx_1733_;
goto v___jp_1705_;
}
}
else
{
lean_object* v_err_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
v_err_1734_ = lean_ctor_get(v___x_1731_, 1);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1741_ == 0)
{
lean_object* v_unused_1742_; 
v_unused_1742_ = lean_ctor_get(v___x_1731_, 0);
lean_dec(v_unused_1742_);
v___x_1736_ = v___x_1731_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_err_1734_);
lean_dec(v___x_1731_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
lean_inc_ref(v_pos_1727_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v_pos_1727_);
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_pos_1727_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_err_1734_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
lean_inc(v_idx_1728_);
v_idx_1706_ = v_idx_1728_;
v___y_1707_ = v___x_1739_;
v_pos_1708_ = v_pos_1727_;
v_idx_1709_ = v_idx_1728_;
goto v___jp_1705_;
}
}
}
}
}
v___jp_1744_:
{
uint8_t v___x_1749_; 
v___x_1749_ = lean_nat_dec_eq(v_idx_1745_, v_idx_1748_);
lean_dec(v_idx_1745_);
if (v___x_1749_ == 0)
{
lean_dec(v_idx_1748_);
lean_dec_ref(v_pos_1747_);
return v___y_1746_;
}
else
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
lean_dec_ref(v___y_1746_);
v___x_1750_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119);
lean_inc_ref(v_pos_1747_);
v___x_1751_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1750_, v___f_1743_, v_pos_1747_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_dec_ref(v_pos_1747_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_dec(v_idx_1748_);
return v___x_1751_;
}
else
{
lean_object* v_pos_1752_; lean_object* v_idx_1753_; 
v_pos_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_pos_1752_);
v_idx_1753_ = lean_ctor_get(v_pos_1752_, 1);
lean_inc(v_idx_1753_);
v_idx_1725_ = v_idx_1748_;
v___y_1726_ = v___x_1751_;
v_pos_1727_ = v_pos_1752_;
v_idx_1728_ = v_idx_1753_;
goto v___jp_1724_;
}
}
else
{
lean_object* v_err_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
v_err_1754_ = lean_ctor_get(v___x_1751_, 1);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1761_ == 0)
{
lean_object* v_unused_1762_; 
v_unused_1762_ = lean_ctor_get(v___x_1751_, 0);
lean_dec(v_unused_1762_);
v___x_1756_ = v___x_1751_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_err_1754_);
lean_dec(v___x_1751_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
lean_inc_ref(v_pos_1747_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v_pos_1747_);
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_pos_1747_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_err_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_inc(v_idx_1748_);
v_idx_1725_ = v_idx_1748_;
v___y_1726_ = v___x_1759_;
v_pos_1727_ = v_pos_1747_;
v_idx_1728_ = v_idx_1748_;
goto v___jp_1724_;
}
}
}
}
}
v___jp_1763_:
{
uint8_t v___x_1768_; 
v___x_1768_ = lean_nat_dec_eq(v_idx_1764_, v_idx_1767_);
lean_dec(v_idx_1764_);
if (v___x_1768_ == 0)
{
lean_dec(v_idx_1767_);
lean_dec_ref(v_pos_1766_);
return v___y_1765_;
}
else
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_dec_ref(v___y_1765_);
v___x_1769_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122);
lean_inc_ref(v_pos_1766_);
v___x_1770_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1769_, v___f_1163_, v_pos_1766_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_dec_ref(v_pos_1766_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_dec(v_idx_1767_);
return v___x_1770_;
}
else
{
lean_object* v_pos_1771_; lean_object* v_idx_1772_; 
v_pos_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_pos_1771_);
v_idx_1772_ = lean_ctor_get(v_pos_1771_, 1);
lean_inc(v_idx_1772_);
v_idx_1745_ = v_idx_1767_;
v___y_1746_ = v___x_1770_;
v_pos_1747_ = v_pos_1771_;
v_idx_1748_ = v_idx_1772_;
goto v___jp_1744_;
}
}
else
{
lean_object* v_err_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
v_err_1773_ = lean_ctor_get(v___x_1770_, 1);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1780_ == 0)
{
lean_object* v_unused_1781_; 
v_unused_1781_ = lean_ctor_get(v___x_1770_, 0);
lean_dec(v_unused_1781_);
v___x_1775_ = v___x_1770_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_err_1773_);
lean_dec(v___x_1770_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
lean_inc_ref(v_pos_1766_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v_pos_1766_);
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_pos_1766_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_err_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_inc(v_idx_1767_);
v_idx_1745_ = v_idx_1767_;
v___y_1746_ = v___x_1778_;
v_pos_1747_ = v_pos_1766_;
v_idx_1748_ = v_idx_1767_;
goto v___jp_1744_;
}
}
}
}
}
v___jp_1783_:
{
uint8_t v___x_1788_; 
v___x_1788_ = lean_nat_dec_eq(v_idx_1784_, v_idx_1787_);
lean_dec(v_idx_1784_);
if (v___x_1788_ == 0)
{
lean_dec(v_idx_1787_);
lean_dec_ref(v_pos_1786_);
return v___y_1785_;
}
else
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_dec_ref(v___y_1785_);
v___x_1789_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126);
lean_inc_ref(v_pos_1786_);
v___x_1790_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1789_, v___f_1782_, v_pos_1786_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_dec_ref(v_pos_1786_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_dec(v_idx_1787_);
return v___x_1790_;
}
else
{
lean_object* v_pos_1791_; lean_object* v_idx_1792_; 
v_pos_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_pos_1791_);
v_idx_1792_ = lean_ctor_get(v_pos_1791_, 1);
lean_inc(v_idx_1792_);
v_idx_1764_ = v_idx_1787_;
v___y_1765_ = v___x_1790_;
v_pos_1766_ = v_pos_1791_;
v_idx_1767_ = v_idx_1792_;
goto v___jp_1763_;
}
}
else
{
lean_object* v_err_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
v_err_1793_ = lean_ctor_get(v___x_1790_, 1);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; 
v_unused_1801_ = lean_ctor_get(v___x_1790_, 0);
lean_dec(v_unused_1801_);
v___x_1795_ = v___x_1790_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_err_1793_);
lean_dec(v___x_1790_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
lean_inc_ref(v_pos_1786_);
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 0, v_pos_1786_);
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_pos_1786_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_err_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_inc(v_idx_1787_);
v_idx_1764_ = v_idx_1787_;
v___y_1765_ = v___x_1798_;
v_pos_1766_ = v_pos_1786_;
v_idx_1767_ = v_idx_1787_;
goto v___jp_1763_;
}
}
}
}
}
v___jp_1802_:
{
uint8_t v___x_1807_; 
v___x_1807_ = lean_nat_dec_eq(v_idx_1803_, v_idx_1806_);
lean_dec(v_idx_1803_);
if (v___x_1807_ == 0)
{
lean_dec(v_idx_1806_);
lean_dec_ref(v_pos_1805_);
return v___y_1804_;
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
lean_dec_ref(v___y_1804_);
v___x_1808_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129);
lean_inc_ref(v_pos_1805_);
v___x_1809_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1808_, v___f_1162_, v_pos_1805_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_dec_ref(v_pos_1805_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_dec(v_idx_1806_);
return v___x_1809_;
}
else
{
lean_object* v_pos_1810_; lean_object* v_idx_1811_; 
v_pos_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_pos_1810_);
v_idx_1811_ = lean_ctor_get(v_pos_1810_, 1);
lean_inc(v_idx_1811_);
v_idx_1784_ = v_idx_1806_;
v___y_1785_ = v___x_1809_;
v_pos_1786_ = v_pos_1810_;
v_idx_1787_ = v_idx_1811_;
goto v___jp_1783_;
}
}
else
{
lean_object* v_err_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
v_err_1812_ = lean_ctor_get(v___x_1809_, 1);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1819_ == 0)
{
lean_object* v_unused_1820_; 
v_unused_1820_ = lean_ctor_get(v___x_1809_, 0);
lean_dec(v_unused_1820_);
v___x_1814_ = v___x_1809_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_err_1812_);
lean_dec(v___x_1809_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
lean_inc_ref(v_pos_1805_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v_pos_1805_);
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_pos_1805_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_err_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_inc(v_idx_1806_);
v_idx_1784_ = v_idx_1806_;
v___y_1785_ = v___x_1817_;
v_pos_1786_ = v_pos_1805_;
v_idx_1787_ = v_idx_1806_;
goto v___jp_1783_;
}
}
}
}
}
v___jp_1822_:
{
uint8_t v___x_1827_; 
v___x_1827_ = lean_nat_dec_eq(v_idx_1823_, v_idx_1826_);
lean_dec(v_idx_1823_);
if (v___x_1827_ == 0)
{
lean_dec(v_idx_1826_);
lean_dec_ref(v_pos_1825_);
return v___y_1824_;
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_dec_ref(v___y_1824_);
v___x_1828_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133);
lean_inc_ref(v_pos_1825_);
v___x_1829_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1828_, v___f_1821_, v_pos_1825_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_dec_ref(v_pos_1825_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_dec(v_idx_1826_);
return v___x_1829_;
}
else
{
lean_object* v_pos_1830_; lean_object* v_idx_1831_; 
v_pos_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_pos_1830_);
v_idx_1831_ = lean_ctor_get(v_pos_1830_, 1);
lean_inc(v_idx_1831_);
v_idx_1803_ = v_idx_1826_;
v___y_1804_ = v___x_1829_;
v_pos_1805_ = v_pos_1830_;
v_idx_1806_ = v_idx_1831_;
goto v___jp_1802_;
}
}
else
{
lean_object* v_err_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
v_err_1832_ = lean_ctor_get(v___x_1829_, 1);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1839_ == 0)
{
lean_object* v_unused_1840_; 
v_unused_1840_ = lean_ctor_get(v___x_1829_, 0);
lean_dec(v_unused_1840_);
v___x_1834_ = v___x_1829_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_err_1832_);
lean_dec(v___x_1829_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
lean_inc_ref(v_pos_1825_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v_pos_1825_);
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_pos_1825_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_err_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
lean_inc(v_idx_1826_);
v_idx_1803_ = v_idx_1826_;
v___y_1804_ = v___x_1837_;
v_pos_1805_ = v_pos_1825_;
v_idx_1806_ = v_idx_1826_;
goto v___jp_1802_;
}
}
}
}
}
v___jp_1841_:
{
uint8_t v___x_1846_; 
v___x_1846_ = lean_nat_dec_eq(v_idx_1842_, v_idx_1845_);
lean_dec(v_idx_1842_);
if (v___x_1846_ == 0)
{
lean_dec(v_idx_1845_);
lean_dec_ref(v_pos_1844_);
return v___y_1843_;
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
lean_dec_ref(v___y_1843_);
v___x_1847_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136);
lean_inc_ref(v_pos_1844_);
v___x_1848_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1847_, v___f_1161_, v_pos_1844_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_dec_ref(v_pos_1844_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_dec(v_idx_1845_);
return v___x_1848_;
}
else
{
lean_object* v_pos_1849_; lean_object* v_idx_1850_; 
v_pos_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_pos_1849_);
v_idx_1850_ = lean_ctor_get(v_pos_1849_, 1);
lean_inc(v_idx_1850_);
v_idx_1823_ = v_idx_1845_;
v___y_1824_ = v___x_1848_;
v_pos_1825_ = v_pos_1849_;
v_idx_1826_ = v_idx_1850_;
goto v___jp_1822_;
}
}
else
{
lean_object* v_err_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
v_err_1851_ = lean_ctor_get(v___x_1848_, 1);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1858_ == 0)
{
lean_object* v_unused_1859_; 
v_unused_1859_ = lean_ctor_get(v___x_1848_, 0);
lean_dec(v_unused_1859_);
v___x_1853_ = v___x_1848_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_err_1851_);
lean_dec(v___x_1848_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
lean_inc_ref(v_pos_1844_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v_pos_1844_);
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_pos_1844_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_err_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_inc(v_idx_1845_);
v_idx_1823_ = v_idx_1845_;
v___y_1824_ = v___x_1856_;
v_pos_1825_ = v_pos_1844_;
v_idx_1826_ = v_idx_1845_;
goto v___jp_1822_;
}
}
}
}
}
v___jp_1861_:
{
uint8_t v___x_1866_; 
v___x_1866_ = lean_nat_dec_eq(v_idx_1862_, v_idx_1865_);
lean_dec(v_idx_1862_);
if (v___x_1866_ == 0)
{
lean_dec(v_idx_1865_);
lean_dec_ref(v_pos_1864_);
return v___y_1863_;
}
else
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
lean_dec_ref(v___y_1863_);
v___x_1867_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140);
lean_inc_ref(v_pos_1864_);
v___x_1868_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1867_, v___f_1860_, v_pos_1864_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_dec_ref(v_pos_1864_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_dec(v_idx_1865_);
return v___x_1868_;
}
else
{
lean_object* v_pos_1869_; lean_object* v_idx_1870_; 
v_pos_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_pos_1869_);
v_idx_1870_ = lean_ctor_get(v_pos_1869_, 1);
lean_inc(v_idx_1870_);
v_idx_1842_ = v_idx_1865_;
v___y_1843_ = v___x_1868_;
v_pos_1844_ = v_pos_1869_;
v_idx_1845_ = v_idx_1870_;
goto v___jp_1841_;
}
}
else
{
lean_object* v_err_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
v_err_1871_ = lean_ctor_get(v___x_1868_, 1);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1878_ == 0)
{
lean_object* v_unused_1879_; 
v_unused_1879_ = lean_ctor_get(v___x_1868_, 0);
lean_dec(v_unused_1879_);
v___x_1873_ = v___x_1868_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_err_1871_);
lean_dec(v___x_1868_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
lean_inc_ref(v_pos_1864_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v_pos_1864_);
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_pos_1864_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v_err_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_inc(v_idx_1865_);
v_idx_1842_ = v_idx_1865_;
v___y_1843_ = v___x_1876_;
v_pos_1844_ = v_pos_1864_;
v_idx_1845_ = v_idx_1865_;
goto v___jp_1841_;
}
}
}
}
}
v___jp_1880_:
{
uint8_t v___x_1885_; 
v___x_1885_ = lean_nat_dec_eq(v_idx_1881_, v_idx_1884_);
lean_dec(v_idx_1881_);
if (v___x_1885_ == 0)
{
lean_dec(v_idx_1884_);
lean_dec_ref(v_pos_1883_);
return v___y_1882_;
}
else
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
lean_dec_ref(v___y_1882_);
v___x_1886_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143);
lean_inc_ref(v_pos_1883_);
v___x_1887_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1886_, v___f_1160_, v_pos_1883_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_dec_ref(v_pos_1883_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_dec(v_idx_1884_);
return v___x_1887_;
}
else
{
lean_object* v_pos_1888_; lean_object* v_idx_1889_; 
v_pos_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_pos_1888_);
v_idx_1889_ = lean_ctor_get(v_pos_1888_, 1);
lean_inc(v_idx_1889_);
v_idx_1862_ = v_idx_1884_;
v___y_1863_ = v___x_1887_;
v_pos_1864_ = v_pos_1888_;
v_idx_1865_ = v_idx_1889_;
goto v___jp_1861_;
}
}
else
{
lean_object* v_err_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
v_err_1890_ = lean_ctor_get(v___x_1887_, 1);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1897_ == 0)
{
lean_object* v_unused_1898_; 
v_unused_1898_ = lean_ctor_get(v___x_1887_, 0);
lean_dec(v_unused_1898_);
v___x_1892_ = v___x_1887_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_err_1890_);
lean_dec(v___x_1887_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
lean_inc_ref(v_pos_1883_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v_pos_1883_);
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_pos_1883_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_err_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_inc(v_idx_1884_);
v_idx_1862_ = v_idx_1884_;
v___y_1863_ = v___x_1895_;
v_pos_1864_ = v_pos_1883_;
v_idx_1865_ = v_idx_1884_;
goto v___jp_1861_;
}
}
}
}
}
v___jp_1900_:
{
uint8_t v___x_1905_; 
v___x_1905_ = lean_nat_dec_eq(v_idx_1901_, v_idx_1904_);
lean_dec(v_idx_1901_);
if (v___x_1905_ == 0)
{
lean_dec(v_idx_1904_);
lean_dec_ref(v_pos_1903_);
return v___y_1902_;
}
else
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
lean_dec_ref(v___y_1902_);
v___x_1906_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147);
lean_inc_ref(v_pos_1903_);
v___x_1907_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1906_, v___f_1899_, v_pos_1903_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_dec_ref(v_pos_1903_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_dec(v_idx_1904_);
return v___x_1907_;
}
else
{
lean_object* v_pos_1908_; lean_object* v_idx_1909_; 
v_pos_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_pos_1908_);
v_idx_1909_ = lean_ctor_get(v_pos_1908_, 1);
lean_inc(v_idx_1909_);
v_idx_1881_ = v_idx_1904_;
v___y_1882_ = v___x_1907_;
v_pos_1883_ = v_pos_1908_;
v_idx_1884_ = v_idx_1909_;
goto v___jp_1880_;
}
}
else
{
lean_object* v_err_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
v_err_1910_ = lean_ctor_get(v___x_1907_, 1);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1917_ == 0)
{
lean_object* v_unused_1918_; 
v_unused_1918_ = lean_ctor_get(v___x_1907_, 0);
lean_dec(v_unused_1918_);
v___x_1912_ = v___x_1907_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_err_1910_);
lean_dec(v___x_1907_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
lean_inc_ref(v_pos_1903_);
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 0, v_pos_1903_);
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_pos_1903_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v_err_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_inc(v_idx_1904_);
v_idx_1881_ = v_idx_1904_;
v___y_1882_ = v___x_1915_;
v_pos_1883_ = v_pos_1903_;
v_idx_1884_ = v_idx_1904_;
goto v___jp_1880_;
}
}
}
}
}
v___jp_1919_:
{
uint8_t v___x_1924_; 
v___x_1924_ = lean_nat_dec_eq(v_idx_1920_, v_idx_1923_);
lean_dec(v_idx_1920_);
if (v___x_1924_ == 0)
{
lean_dec(v_idx_1923_);
lean_dec_ref(v_pos_1922_);
return v___y_1921_;
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
lean_dec_ref(v___y_1921_);
v___x_1925_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150);
lean_inc_ref(v_pos_1922_);
v___x_1926_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1925_, v___f_1159_, v_pos_1922_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_dec_ref(v_pos_1922_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_dec(v_idx_1923_);
return v___x_1926_;
}
else
{
lean_object* v_pos_1927_; lean_object* v_idx_1928_; 
v_pos_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_pos_1927_);
v_idx_1928_ = lean_ctor_get(v_pos_1927_, 1);
lean_inc(v_idx_1928_);
v_idx_1901_ = v_idx_1923_;
v___y_1902_ = v___x_1926_;
v_pos_1903_ = v_pos_1927_;
v_idx_1904_ = v_idx_1928_;
goto v___jp_1900_;
}
}
else
{
lean_object* v_err_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
v_err_1929_ = lean_ctor_get(v___x_1926_, 1);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1936_ == 0)
{
lean_object* v_unused_1937_; 
v_unused_1937_ = lean_ctor_get(v___x_1926_, 0);
lean_dec(v_unused_1937_);
v___x_1931_ = v___x_1926_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_err_1929_);
lean_dec(v___x_1926_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
lean_inc_ref(v_pos_1922_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v_pos_1922_);
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_pos_1922_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_err_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_inc(v_idx_1923_);
v_idx_1901_ = v_idx_1923_;
v___y_1902_ = v___x_1934_;
v_pos_1903_ = v_pos_1922_;
v_idx_1904_ = v_idx_1923_;
goto v___jp_1900_;
}
}
}
}
}
v___jp_1939_:
{
uint8_t v___x_1944_; 
v___x_1944_ = lean_nat_dec_eq(v_idx_1940_, v_idx_1943_);
lean_dec(v_idx_1940_);
if (v___x_1944_ == 0)
{
lean_dec(v_idx_1943_);
lean_dec_ref(v_pos_1942_);
return v___y_1941_;
}
else
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
lean_dec_ref(v___y_1941_);
v___x_1945_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154);
lean_inc_ref(v_pos_1942_);
v___x_1946_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1945_, v___f_1938_, v_pos_1942_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_dec_ref(v_pos_1942_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_dec(v_idx_1943_);
return v___x_1946_;
}
else
{
lean_object* v_pos_1947_; lean_object* v_idx_1948_; 
v_pos_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_pos_1947_);
v_idx_1948_ = lean_ctor_get(v_pos_1947_, 1);
lean_inc(v_idx_1948_);
v_idx_1920_ = v_idx_1943_;
v___y_1921_ = v___x_1946_;
v_pos_1922_ = v_pos_1947_;
v_idx_1923_ = v_idx_1948_;
goto v___jp_1919_;
}
}
else
{
lean_object* v_err_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
v_err_1949_ = lean_ctor_get(v___x_1946_, 1);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1956_ == 0)
{
lean_object* v_unused_1957_; 
v_unused_1957_ = lean_ctor_get(v___x_1946_, 0);
lean_dec(v_unused_1957_);
v___x_1951_ = v___x_1946_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_err_1949_);
lean_dec(v___x_1946_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
lean_inc_ref(v_pos_1942_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v_pos_1942_);
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_pos_1942_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_err_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
lean_inc(v_idx_1943_);
v_idx_1920_ = v_idx_1943_;
v___y_1921_ = v___x_1954_;
v_pos_1922_ = v_pos_1942_;
v_idx_1923_ = v_idx_1943_;
goto v___jp_1919_;
}
}
}
}
}
v___jp_1958_:
{
lean_object* v_idx_1961_; lean_object* v_idx_1962_; uint8_t v___x_1963_; 
v_idx_1961_ = lean_ctor_get(v_a_1157_, 1);
lean_inc(v_idx_1961_);
lean_dec_ref(v_a_1157_);
v_idx_1962_ = lean_ctor_get(v_pos_1960_, 1);
lean_inc(v_idx_1962_);
v___x_1963_ = lean_nat_dec_eq(v_idx_1961_, v_idx_1962_);
lean_dec(v_idx_1961_);
if (v___x_1963_ == 0)
{
lean_dec(v_idx_1962_);
lean_dec_ref(v_pos_1960_);
return v___y_1959_;
}
else
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
lean_dec_ref(v___y_1959_);
v___x_1964_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157);
lean_inc_ref(v_pos_1960_);
v___x_1965_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1964_, v___f_1158_, v_pos_1960_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_dec_ref(v_pos_1960_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_dec(v_idx_1962_);
return v___x_1965_;
}
else
{
lean_object* v_pos_1966_; lean_object* v_idx_1967_; 
v_pos_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_pos_1966_);
v_idx_1967_ = lean_ctor_get(v_pos_1966_, 1);
lean_inc(v_idx_1967_);
v_idx_1940_ = v_idx_1962_;
v___y_1941_ = v___x_1965_;
v_pos_1942_ = v_pos_1966_;
v_idx_1943_ = v_idx_1967_;
goto v___jp_1939_;
}
}
else
{
lean_object* v_err_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
v_err_1968_ = lean_ctor_get(v___x_1965_, 1);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1975_ == 0)
{
lean_object* v_unused_1976_; 
v_unused_1976_ = lean_ctor_get(v___x_1965_, 0);
lean_dec(v_unused_1976_);
v___x_1970_ = v___x_1965_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_err_1968_);
lean_dec(v___x_1965_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
lean_inc_ref(v_pos_1960_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v_pos_1960_);
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_pos_1960_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_err_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
lean_inc(v_idx_1962_);
v_idx_1940_ = v_idx_1962_;
v___y_1941_ = v___x_1973_;
v_pos_1942_ = v_pos_1960_;
v_idx_1943_ = v_idx_1962_;
goto v___jp_1939_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(uint8_t v_b_1990_){
_start:
{
uint8_t v___x_1991_; uint8_t v___x_1992_; 
v___x_1991_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v___x_1992_ = lean_uint8_dec_eq(v_b_1990_, v___x_1991_);
if (v___x_1992_ == 0)
{
uint8_t v___x_1993_; 
v___x_1993_ = 1;
return v___x_1993_;
}
else
{
uint8_t v___x_1994_; 
v___x_1994_ = 0;
return v___x_1994_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0___boxed(lean_object* v_b_1995_){
_start:
{
uint8_t v_b_boxed_1996_; uint8_t v_res_1997_; lean_object* v_r_1998_; 
v_b_boxed_1996_ = lean_unbox(v_b_1995_);
v_res_1997_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(v_b_boxed_1996_);
v_r_1998_ = lean_box(v_res_1997_);
return v_r_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(lean_object* v_limits_2003_, lean_object* v_a_2004_){
_start:
{
lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v_maxUriLength_2010_; lean_object* v___f_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v_snd_2014_; lean_object* v_snd_2015_; uint8_t v___x_2016_; 
v_maxUriLength_2010_ = lean_ctor_get(v_limits_2003_, 4);
v___f_2011_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__0));
v___x_2012_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2004_);
v___x_2013_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2011_, v_maxUriLength_2010_, v___x_2012_, v_a_2004_);
v_snd_2014_ = lean_ctor_get(v___x_2013_, 1);
lean_inc(v_snd_2014_);
v_snd_2015_ = lean_ctor_get(v_snd_2014_, 1);
v___x_2016_ = lean_unbox(v_snd_2015_);
if (v___x_2016_ == 0)
{
lean_object* v_fst_2017_; lean_object* v_fst_2018_; lean_object* v_array_2019_; lean_object* v_idx_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2048_; 
v_fst_2017_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_fst_2017_);
lean_dec_ref(v___x_2013_);
v_fst_2018_ = lean_ctor_get(v_snd_2014_, 0);
lean_inc(v_fst_2018_);
lean_dec(v_snd_2014_);
v_array_2019_ = lean_ctor_get(v_a_2004_, 0);
v_idx_2020_ = lean_ctor_get(v_a_2004_, 1);
v_isSharedCheck_2048_ = !lean_is_exclusive(v_a_2004_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2022_ = v_a_2004_;
v_isShared_2023_ = v_isSharedCheck_2048_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_idx_2020_);
lean_inc(v_array_2019_);
lean_dec(v_a_2004_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2048_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v_lower_2025_; lean_object* v_upper_2026_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___y_2045_; uint8_t v___x_2047_; 
v___x_2042_ = lean_nat_add(v_idx_2020_, v_fst_2017_);
lean_dec(v_fst_2017_);
v___x_2043_ = lean_byte_array_size(v_array_2019_);
v___x_2047_ = lean_nat_dec_le(v_idx_2020_, v___x_2012_);
if (v___x_2047_ == 0)
{
v___y_2045_ = v_idx_2020_;
goto v___jp_2044_;
}
else
{
lean_dec(v_idx_2020_);
v___y_2045_ = v___x_2012_;
goto v___jp_2044_;
}
v___jp_2024_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2027_ = l_ByteArray_toByteSlice(v_array_2019_, v_lower_2025_, v_upper_2026_);
v___x_2028_ = l_ByteSlice_size(v___x_2027_);
v___x_2029_ = lean_nat_dec_eq(v___x_2028_, v_maxUriLength_2010_);
lean_dec(v___x_2028_);
if (v___x_2029_ == 0)
{
lean_del_object(v___x_2022_);
v___y_2006_ = v___x_2027_;
v___y_2007_ = v_fst_2018_;
goto v___jp_2005_;
}
else
{
lean_object* v_array_2030_; lean_object* v_idx_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v_array_2030_ = lean_ctor_get(v_fst_2018_, 0);
v_idx_2031_ = lean_ctor_get(v_fst_2018_, 1);
v___x_2032_ = lean_byte_array_size(v_array_2030_);
v___x_2033_ = lean_nat_dec_lt(v_idx_2031_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_del_object(v___x_2022_);
v___y_2006_ = v___x_2027_;
v___y_2007_ = v_fst_2018_;
goto v___jp_2005_;
}
else
{
uint8_t v___x_2034_; uint8_t v___x_2035_; uint8_t v___x_2036_; uint8_t v___x_2037_; 
v___x_2034_ = lean_byte_array_fget(v_array_2030_, v_idx_2031_);
v___x_2035_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v___x_2036_ = lean_uint8_dec_eq(v___x_2034_, v___x_2035_);
v___x_2037_ = lean_bool_not(v___x_2036_);
if (v___x_2037_ == 0)
{
lean_del_object(v___x_2022_);
v___y_2006_ = v___x_2027_;
v___y_2007_ = v_fst_2018_;
goto v___jp_2005_;
}
else
{
if (v___x_2029_ == 0)
{
lean_del_object(v___x_2022_);
v___y_2006_ = v___x_2027_;
v___y_2007_ = v_fst_2018_;
goto v___jp_2005_;
}
else
{
lean_object* v___x_2038_; lean_object* v___x_2040_; 
lean_dec_ref(v___x_2027_);
v___x_2038_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__2));
if (v_isShared_2023_ == 0)
{
lean_ctor_set_tag(v___x_2022_, 1);
lean_ctor_set(v___x_2022_, 1, v___x_2038_);
lean_ctor_set(v___x_2022_, 0, v_fst_2018_);
v___x_2040_ = v___x_2022_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_fst_2018_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
}
v___jp_2044_:
{
uint8_t v___x_2046_; 
v___x_2046_ = lean_nat_dec_le(v___x_2042_, v___x_2043_);
if (v___x_2046_ == 0)
{
lean_dec(v___x_2042_);
v_lower_2025_ = v___y_2045_;
v_upper_2026_ = v___x_2043_;
goto v___jp_2024_;
}
else
{
v_lower_2025_ = v___y_2045_;
v_upper_2026_ = v___x_2042_;
goto v___jp_2024_;
}
}
}
}
else
{
lean_object* v_fst_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2057_; 
lean_dec_ref(v___x_2013_);
lean_dec_ref(v_a_2004_);
v_fst_2049_ = lean_ctor_get(v_snd_2014_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_snd_2014_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; 
v_unused_2058_ = lean_ctor_get(v_snd_2014_, 1);
lean_dec(v_unused_2058_);
v___x_2051_ = v_snd_2014_;
v_isShared_2052_ = v_isSharedCheck_2057_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_fst_2049_);
lean_dec(v_snd_2014_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2057_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2053_ = lean_box(0);
if (v_isShared_2052_ == 0)
{
lean_ctor_set_tag(v___x_2051_, 1);
lean_ctor_set(v___x_2051_, 1, v___x_2053_);
v___x_2055_ = v___x_2051_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_fst_2049_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
v___jp_2005_:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = l_ByteSlice_toByteArray(v___y_2006_);
v___x_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___y_2007_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
return v___x_2009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___boxed(lean_object* v_limits_2059_, lean_object* v_a_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_2059_, v_a_2060_);
lean_dec_ref(v_limits_2059_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0(lean_object* v___x_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_2065_, v___y_2066_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_pos_2068_; lean_object* v_array_2069_; lean_object* v_idx_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
v_pos_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_pos_2068_);
v_array_2069_ = lean_ctor_get(v_pos_2068_, 0);
v_idx_2070_ = lean_ctor_get(v_pos_2068_, 1);
v___x_2071_ = lean_byte_array_size(v_array_2069_);
v___x_2072_ = lean_nat_dec_lt(v_idx_2070_, v___x_2071_);
if (v___x_2072_ == 0)
{
lean_dec(v_pos_2068_);
return v___x_2067_;
}
else
{
lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2080_; 
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2080_ == 0)
{
lean_object* v_unused_2081_; lean_object* v_unused_2082_; 
v_unused_2081_ = lean_ctor_get(v___x_2067_, 1);
lean_dec(v_unused_2081_);
v_unused_2082_ = lean_ctor_get(v___x_2067_, 0);
lean_dec(v_unused_2082_);
v___x_2074_ = v___x_2067_;
v_isShared_2075_ = v_isSharedCheck_2080_;
goto v_resetjp_2073_;
}
else
{
lean_dec(v___x_2067_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2080_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2076_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__1));
if (v_isShared_2075_ == 0)
{
lean_ctor_set_tag(v___x_2074_, 1);
lean_ctor_set(v___x_2074_, 1, v___x_2076_);
v___x_2078_ = v___x_2074_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_pos_2068_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
else
{
return v___x_2067_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(lean_object* v_limits_2093_, lean_object* v_a_2094_){
_start:
{
lean_object* v___y_2096_; lean_object* v_pos_2097_; lean_object* v_res_2098_; lean_object* v_pos_2102_; lean_object* v_res_2103_; lean_object* v___x_2142_; 
v___x_2142_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_2093_, v_a_2094_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_pos_2143_; lean_object* v_res_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2174_; 
v_pos_2143_ = lean_ctor_get(v___x_2142_, 0);
v_res_2144_ = lean_ctor_get(v___x_2142_, 1);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2146_ = v___x_2142_;
v_isShared_2147_ = v_isSharedCheck_2174_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_res_2144_);
lean_inc(v_pos_2143_);
lean_dec(v___x_2142_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2174_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v_array_2148_; lean_object* v_idx_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; 
v_array_2148_ = lean_ctor_get(v_pos_2143_, 0);
v_idx_2149_ = lean_ctor_get(v_pos_2143_, 1);
v___x_2150_ = lean_byte_array_size(v_array_2148_);
v___x_2151_ = lean_nat_dec_lt(v_idx_2149_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; lean_object* v___x_2154_; 
lean_dec(v_res_2144_);
v___x_2152_ = lean_box(0);
if (v_isShared_2147_ == 0)
{
lean_ctor_set_tag(v___x_2146_, 1);
lean_ctor_set(v___x_2146_, 1, v___x_2152_);
v___x_2154_ = v___x_2146_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_pos_2143_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v___x_2152_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
else
{
uint8_t v___x_2156_; uint8_t v_got_2157_; uint8_t v___x_2158_; 
v___x_2156_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v_got_2157_ = lean_byte_array_fget(v_array_2148_, v_idx_2149_);
v___x_2158_ = lean_uint8_dec_eq(v_got_2157_, v___x_2156_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
lean_dec(v_res_2144_);
v___x_2159_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7);
if (v_isShared_2147_ == 0)
{
lean_ctor_set_tag(v___x_2146_, 1);
lean_ctor_set(v___x_2146_, 1, v___x_2159_);
v___x_2161_ = v___x_2146_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_pos_2143_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
else
{
lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2171_; 
lean_inc(v_idx_2149_);
lean_inc_ref(v_array_2148_);
lean_del_object(v___x_2146_);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_pos_2143_);
if (v_isSharedCheck_2171_ == 0)
{
lean_object* v_unused_2172_; lean_object* v_unused_2173_; 
v_unused_2172_ = lean_ctor_get(v_pos_2143_, 1);
lean_dec(v_unused_2172_);
v_unused_2173_ = lean_ctor_get(v_pos_2143_, 0);
lean_dec(v_unused_2173_);
v___x_2164_ = v_pos_2143_;
v_isShared_2165_ = v_isSharedCheck_2171_;
goto v_resetjp_2163_;
}
else
{
lean_dec(v_pos_2143_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2171_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2169_; 
v___x_2166_ = lean_unsigned_to_nat(1u);
v___x_2167_ = lean_nat_add(v_idx_2149_, v___x_2166_);
lean_dec(v_idx_2149_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 1, v___x_2167_);
v___x_2169_ = v___x_2164_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_array_2148_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
v_pos_2102_ = v___x_2169_;
v_res_2103_ = v_res_2144_;
goto v___jp_2101_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_pos_2175_; lean_object* v_res_2176_; 
v_pos_2175_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_pos_2175_);
v_res_2176_ = lean_ctor_get(v___x_2142_, 1);
lean_inc(v_res_2176_);
lean_dec_ref_known(v___x_2142_, 2);
v_pos_2102_ = v_pos_2175_;
v_res_2103_ = v_res_2176_;
goto v___jp_2101_;
}
else
{
lean_object* v_pos_2177_; lean_object* v_err_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
v_pos_2177_ = lean_ctor_get(v___x_2142_, 0);
v_err_2178_ = lean_ctor_get(v___x_2142_, 1);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2142_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_err_2178_);
lean_inc(v_pos_2177_);
lean_dec(v___x_2142_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_pos_2177_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_err_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
v___jp_2095_:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___y_2096_);
lean_ctor_set(v___x_2099_, 1, v_res_2098_);
v___x_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2100_, 0, v_pos_2097_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
return v___x_2100_;
}
v___jp_2101_:
{
lean_object* v___f_2104_; lean_object* v___x_2105_; 
v___f_2104_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___closed__1));
v___x_2105_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_2104_, v_res_2103_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2114_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2108_ = v___x_2105_;
v_isShared_2109_ = v_isSharedCheck_2114_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2105_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2114_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
lean_ctor_set_tag(v___x_2108_, 1);
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
lean_object* v___x_2112_; 
v___x_2112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2112_, 0, v_pos_2102_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
return v___x_2112_;
}
}
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2116_; 
v_a_2115_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2105_, 1);
v___x_2116_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_pos_2102_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_pos_2117_; lean_object* v_res_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v_pos_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_pos_2117_);
v_res_2118_ = lean_ctor_get(v___x_2116_, 1);
lean_inc(v_res_2118_);
lean_dec_ref_known(v___x_2116_, 2);
v___x_2119_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2120_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2119_, v_pos_2117_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_pos_2121_; 
v_pos_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_pos_2121_);
lean_dec_ref_known(v___x_2120_, 2);
v___y_2096_ = v_a_2115_;
v_pos_2097_ = v_pos_2121_;
v_res_2098_ = v_res_2118_;
goto v___jp_2095_;
}
else
{
lean_object* v_pos_2122_; lean_object* v_err_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec(v_res_2118_);
lean_dec(v_a_2115_);
v_pos_2122_ = lean_ctor_get(v___x_2120_, 0);
v_err_2123_ = lean_ctor_get(v___x_2120_, 1);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2120_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_err_2123_);
lean_inc(v_pos_2122_);
lean_dec(v___x_2120_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_pos_2122_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_err_2123_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_pos_2131_; lean_object* v_res_2132_; 
v_pos_2131_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_pos_2131_);
v_res_2132_ = lean_ctor_get(v___x_2116_, 1);
lean_inc(v_res_2132_);
lean_dec_ref_known(v___x_2116_, 2);
v___y_2096_ = v_a_2115_;
v_pos_2097_ = v_pos_2131_;
v_res_2098_ = v_res_2132_;
goto v___jp_2095_;
}
else
{
lean_object* v_pos_2133_; lean_object* v_err_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec(v_a_2115_);
v_pos_2133_ = lean_ctor_get(v___x_2116_, 0);
v_err_2134_ = lean_ctor_get(v___x_2116_, 1);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2116_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_err_2134_);
lean_inc(v_pos_2133_);
lean_dec(v___x_2116_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_pos_2133_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v_err_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___boxed(lean_object* v_limits_2186_, lean_object* v_a_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_2186_, v_a_2187_);
lean_dec_ref(v_limits_2186_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine(lean_object* v_limits_2192_, lean_object* v_a_2193_){
_start:
{
lean_object* v___y_2195_; lean_object* v___y_2199_; lean_object* v___y_2200_; uint8_t v___y_2201_; lean_object* v___y_2202_; uint8_t v___y_2203_; lean_object* v_pos_2211_; uint8_t v_res_2212_; lean_object* v___x_2243_; 
v___x_2243_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_2192_, v_a_2193_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_pos_2244_; lean_object* v___x_2245_; 
v_pos_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_pos_2244_);
lean_dec_ref_known(v___x_2243_, 2);
v___x_2245_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(v_pos_2244_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_pos_2246_; lean_object* v_res_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2278_; 
v_pos_2246_ = lean_ctor_get(v___x_2245_, 0);
v_res_2247_ = lean_ctor_get(v___x_2245_, 1);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2249_ = v___x_2245_;
v_isShared_2250_ = v_isSharedCheck_2278_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_res_2247_);
lean_inc(v_pos_2246_);
lean_dec(v___x_2245_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2278_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v_array_2251_; lean_object* v_idx_2252_; lean_object* v___x_2253_; uint8_t v___x_2254_; 
v_array_2251_ = lean_ctor_get(v_pos_2246_, 0);
v_idx_2252_ = lean_ctor_get(v_pos_2246_, 1);
v___x_2253_ = lean_byte_array_size(v_array_2251_);
v___x_2254_ = lean_nat_dec_lt(v_idx_2252_, v___x_2253_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; lean_object* v___x_2257_; 
lean_dec(v_res_2247_);
v___x_2255_ = lean_box(0);
if (v_isShared_2250_ == 0)
{
lean_ctor_set_tag(v___x_2249_, 1);
lean_ctor_set(v___x_2249_, 1, v___x_2255_);
v___x_2257_ = v___x_2249_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_pos_2246_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v___x_2255_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
else
{
uint8_t v___x_2259_; uint8_t v_got_2260_; uint8_t v___x_2261_; 
v___x_2259_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v_got_2260_ = lean_byte_array_fget(v_array_2251_, v_idx_2252_);
v___x_2261_ = lean_uint8_dec_eq(v_got_2260_, v___x_2259_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2262_; lean_object* v___x_2264_; 
lean_dec(v_res_2247_);
v___x_2262_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7);
if (v_isShared_2250_ == 0)
{
lean_ctor_set_tag(v___x_2249_, 1);
lean_ctor_set(v___x_2249_, 1, v___x_2262_);
v___x_2264_ = v___x_2249_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_pos_2246_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
else
{
lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2275_; 
lean_inc(v_idx_2252_);
lean_inc_ref(v_array_2251_);
lean_del_object(v___x_2249_);
v_isSharedCheck_2275_ = !lean_is_exclusive(v_pos_2246_);
if (v_isSharedCheck_2275_ == 0)
{
lean_object* v_unused_2276_; lean_object* v_unused_2277_; 
v_unused_2276_ = lean_ctor_get(v_pos_2246_, 1);
lean_dec(v_unused_2276_);
v_unused_2277_ = lean_ctor_get(v_pos_2246_, 0);
lean_dec(v_unused_2277_);
v___x_2267_ = v_pos_2246_;
v_isShared_2268_ = v_isSharedCheck_2275_;
goto v_resetjp_2266_;
}
else
{
lean_dec(v_pos_2246_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2275_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2272_; 
v___x_2269_ = lean_unsigned_to_nat(1u);
v___x_2270_ = lean_nat_add(v_idx_2252_, v___x_2269_);
lean_dec(v_idx_2252_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 1, v___x_2270_);
v___x_2272_ = v___x_2267_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_array_2251_);
lean_ctor_set(v_reuseFailAlloc_2274_, 1, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
uint8_t v___x_2273_; 
v___x_2273_ = lean_unbox(v_res_2247_);
lean_dec(v_res_2247_);
v_pos_2211_ = v___x_2272_;
v_res_2212_ = v___x_2273_;
goto v___jp_2210_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_pos_2279_; lean_object* v_res_2280_; uint8_t v___x_2281_; 
v_pos_2279_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_pos_2279_);
v_res_2280_ = lean_ctor_get(v___x_2245_, 1);
lean_inc(v_res_2280_);
lean_dec_ref_known(v___x_2245_, 2);
v___x_2281_ = lean_unbox(v_res_2280_);
lean_dec(v_res_2280_);
v_pos_2211_ = v_pos_2279_;
v_res_2212_ = v___x_2281_;
goto v___jp_2210_;
}
else
{
lean_object* v_pos_2282_; lean_object* v_err_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
v_pos_2282_ = lean_ctor_get(v___x_2245_, 0);
v_err_2283_ = lean_ctor_get(v___x_2245_, 1);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2245_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_err_2283_);
lean_inc(v_pos_2282_);
lean_dec(v___x_2245_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_pos_2282_);
lean_ctor_set(v_reuseFailAlloc_2289_, 1, v_err_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
}
else
{
lean_object* v_pos_2291_; lean_object* v_err_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
v_pos_2291_ = lean_ctor_get(v___x_2243_, 0);
v_err_2292_ = lean_ctor_get(v___x_2243_, 1);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2243_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_err_2292_);
lean_inc(v_pos_2291_);
lean_dec(v___x_2243_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_pos_2291_);
lean_ctor_set(v_reuseFailAlloc_2298_, 1, v_err_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
v___jp_2194_:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
v___x_2197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___y_2195_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
return v___x_2197_;
}
v___jp_2198_:
{
if (v___y_2203_ == 0)
{
lean_dec(v___y_2202_);
lean_dec(v___y_2200_);
v___y_2195_ = v___y_2199_;
goto v___jp_2194_;
}
else
{
lean_object* v___x_2204_; uint8_t v___x_2205_; 
v___x_2204_ = lean_unsigned_to_nat(0u);
v___x_2205_ = lean_nat_dec_eq(v___y_2202_, v___x_2204_);
lean_dec(v___y_2202_);
if (v___x_2205_ == 0)
{
lean_dec(v___y_2200_);
v___y_2195_ = v___y_2199_;
goto v___jp_2194_;
}
else
{
uint8_t v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2206_ = 0;
v___x_2207_ = l_Std_Http_Headers_empty;
v___x_2208_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_2208_, 0, v___y_2200_);
lean_ctor_set(v___x_2208_, 1, v___x_2207_);
lean_ctor_set_uint8(v___x_2208_, sizeof(void*)*2, v___y_2201_);
lean_ctor_set_uint8(v___x_2208_, sizeof(void*)*2 + 1, v___x_2206_);
v___x_2209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___y_2199_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
return v___x_2209_;
}
}
}
v___jp_2210_:
{
lean_object* v___x_2213_; 
v___x_2213_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_2192_, v_pos_2211_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_res_2214_; lean_object* v_snd_2215_; lean_object* v_pos_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2232_; 
v_res_2214_ = lean_ctor_get(v___x_2213_, 1);
lean_inc(v_res_2214_);
v_snd_2215_ = lean_ctor_get(v_res_2214_, 1);
lean_inc(v_snd_2215_);
v_pos_2216_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2232_ == 0)
{
lean_object* v_unused_2233_; 
v_unused_2233_ = lean_ctor_get(v___x_2213_, 1);
lean_dec(v_unused_2233_);
v___x_2218_ = v___x_2213_;
v_isShared_2219_ = v_isSharedCheck_2232_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_pos_2216_);
lean_dec(v___x_2213_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2232_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v_fst_2220_; lean_object* v_fst_2221_; lean_object* v_snd_2222_; lean_object* v___x_2223_; uint8_t v___x_2224_; 
v_fst_2220_ = lean_ctor_get(v_res_2214_, 0);
lean_inc(v_fst_2220_);
lean_dec(v_res_2214_);
v_fst_2221_ = lean_ctor_get(v_snd_2215_, 0);
lean_inc(v_fst_2221_);
v_snd_2222_ = lean_ctor_get(v_snd_2215_, 1);
lean_inc(v_snd_2222_);
lean_dec(v_snd_2215_);
v___x_2223_ = lean_unsigned_to_nat(1u);
v___x_2224_ = lean_nat_dec_eq(v_fst_2221_, v___x_2223_);
lean_dec(v_fst_2221_);
if (v___x_2224_ == 0)
{
lean_del_object(v___x_2218_);
v___y_2199_ = v_pos_2216_;
v___y_2200_ = v_fst_2220_;
v___y_2201_ = v_res_2212_;
v___y_2202_ = v_snd_2222_;
v___y_2203_ = v___x_2224_;
goto v___jp_2198_;
}
else
{
uint8_t v___x_2225_; 
v___x_2225_ = lean_nat_dec_eq(v_snd_2222_, v___x_2223_);
if (v___x_2225_ == 0)
{
lean_del_object(v___x_2218_);
v___y_2199_ = v_pos_2216_;
v___y_2200_ = v_fst_2220_;
v___y_2201_ = v_res_2212_;
v___y_2202_ = v_snd_2222_;
v___y_2203_ = v___x_2224_;
goto v___jp_2198_;
}
else
{
uint8_t v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2230_; 
lean_dec(v_snd_2222_);
v___x_2226_ = 1;
v___x_2227_ = l_Std_Http_Headers_empty;
v___x_2228_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_2228_, 0, v_fst_2220_);
lean_ctor_set(v___x_2228_, 1, v___x_2227_);
lean_ctor_set_uint8(v___x_2228_, sizeof(void*)*2, v_res_2212_);
lean_ctor_set_uint8(v___x_2228_, sizeof(void*)*2 + 1, v___x_2226_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v___x_2228_);
v___x_2230_ = v___x_2218_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_pos_2216_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v___x_2228_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
}
else
{
lean_object* v_pos_2234_; lean_object* v_err_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
v_pos_2234_ = lean_ctor_get(v___x_2213_, 0);
v_err_2235_ = lean_ctor_get(v___x_2213_, 1);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2213_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_err_2235_);
lean_inc(v_pos_2234_);
lean_dec(v___x_2213_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_pos_2234_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_err_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine___boxed(lean_object* v_limits_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Std_Http_Protocol_H1_parseRequestLine(v_limits_2300_, v_a_2301_);
lean_dec_ref(v_limits_2300_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion(lean_object* v_limits_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v_pos_2306_; uint8_t v_res_2307_; lean_object* v___x_2349_; 
v___x_2349_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_2303_, v_a_2304_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_pos_2350_; lean_object* v___x_2351_; 
v_pos_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_pos_2350_);
lean_dec_ref_known(v___x_2349_, 2);
v___x_2351_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(v_pos_2350_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_pos_2352_; lean_object* v_res_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2384_; 
v_pos_2352_ = lean_ctor_get(v___x_2351_, 0);
v_res_2353_ = lean_ctor_get(v___x_2351_, 1);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2355_ = v___x_2351_;
v_isShared_2356_ = v_isSharedCheck_2384_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_res_2353_);
lean_inc(v_pos_2352_);
lean_dec(v___x_2351_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2384_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v_array_2357_; lean_object* v_idx_2358_; lean_object* v___x_2359_; uint8_t v___x_2360_; 
v_array_2357_ = lean_ctor_get(v_pos_2352_, 0);
v_idx_2358_ = lean_ctor_get(v_pos_2352_, 1);
v___x_2359_ = lean_byte_array_size(v_array_2357_);
v___x_2360_ = lean_nat_dec_lt(v_idx_2358_, v___x_2359_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; lean_object* v___x_2363_; 
lean_dec(v_res_2353_);
v___x_2361_ = lean_box(0);
if (v_isShared_2356_ == 0)
{
lean_ctor_set_tag(v___x_2355_, 1);
lean_ctor_set(v___x_2355_, 1, v___x_2361_);
v___x_2363_ = v___x_2355_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_pos_2352_);
lean_ctor_set(v_reuseFailAlloc_2364_, 1, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
else
{
uint8_t v___x_2365_; uint8_t v_got_2366_; uint8_t v___x_2367_; 
v___x_2365_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v_got_2366_ = lean_byte_array_fget(v_array_2357_, v_idx_2358_);
v___x_2367_ = lean_uint8_dec_eq(v_got_2366_, v___x_2365_);
if (v___x_2367_ == 0)
{
lean_object* v___x_2368_; lean_object* v___x_2370_; 
lean_dec(v_res_2353_);
v___x_2368_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7);
if (v_isShared_2356_ == 0)
{
lean_ctor_set_tag(v___x_2355_, 1);
lean_ctor_set(v___x_2355_, 1, v___x_2368_);
v___x_2370_ = v___x_2355_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_pos_2352_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v___x_2368_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
else
{
lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2381_; 
lean_inc(v_idx_2358_);
lean_inc_ref(v_array_2357_);
lean_del_object(v___x_2355_);
v_isSharedCheck_2381_ = !lean_is_exclusive(v_pos_2352_);
if (v_isSharedCheck_2381_ == 0)
{
lean_object* v_unused_2382_; lean_object* v_unused_2383_; 
v_unused_2382_ = lean_ctor_get(v_pos_2352_, 1);
lean_dec(v_unused_2382_);
v_unused_2383_ = lean_ctor_get(v_pos_2352_, 0);
lean_dec(v_unused_2383_);
v___x_2373_ = v_pos_2352_;
v_isShared_2374_ = v_isSharedCheck_2381_;
goto v_resetjp_2372_;
}
else
{
lean_dec(v_pos_2352_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2381_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2378_; 
v___x_2375_ = lean_unsigned_to_nat(1u);
v___x_2376_ = lean_nat_add(v_idx_2358_, v___x_2375_);
lean_dec(v_idx_2358_);
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 1, v___x_2376_);
v___x_2378_ = v___x_2373_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_array_2357_);
lean_ctor_set(v_reuseFailAlloc_2380_, 1, v___x_2376_);
v___x_2378_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
uint8_t v___x_2379_; 
v___x_2379_ = lean_unbox(v_res_2353_);
lean_dec(v_res_2353_);
v_pos_2306_ = v___x_2378_;
v_res_2307_ = v___x_2379_;
goto v___jp_2305_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_pos_2385_; lean_object* v_res_2386_; uint8_t v___x_2387_; 
v_pos_2385_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_pos_2385_);
v_res_2386_ = lean_ctor_get(v___x_2351_, 1);
lean_inc(v_res_2386_);
lean_dec_ref_known(v___x_2351_, 2);
v___x_2387_ = lean_unbox(v_res_2386_);
lean_dec(v_res_2386_);
v_pos_2306_ = v_pos_2385_;
v_res_2307_ = v___x_2387_;
goto v___jp_2305_;
}
else
{
lean_object* v_pos_2388_; lean_object* v_err_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
v_pos_2388_ = lean_ctor_get(v___x_2351_, 0);
v_err_2389_ = lean_ctor_get(v___x_2351_, 1);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2351_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_err_2389_);
lean_inc(v_pos_2388_);
lean_dec(v___x_2351_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_pos_2388_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_err_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
}
else
{
lean_object* v_pos_2397_; lean_object* v_err_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
v_pos_2397_ = lean_ctor_get(v___x_2349_, 0);
v_err_2398_ = lean_ctor_get(v___x_2349_, 1);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2349_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_err_2398_);
lean_inc(v_pos_2397_);
lean_dec(v___x_2349_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_pos_2397_);
lean_ctor_set(v_reuseFailAlloc_2404_, 1, v_err_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
v___jp_2305_:
{
lean_object* v___x_2308_; 
v___x_2308_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_2303_, v_pos_2306_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_res_2309_; lean_object* v_snd_2310_; lean_object* v_pos_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2338_; 
v_res_2309_ = lean_ctor_get(v___x_2308_, 1);
lean_inc(v_res_2309_);
v_snd_2310_ = lean_ctor_get(v_res_2309_, 1);
lean_inc(v_snd_2310_);
v_pos_2311_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2338_ == 0)
{
lean_object* v_unused_2339_; 
v_unused_2339_ = lean_ctor_get(v___x_2308_, 1);
lean_dec(v_unused_2339_);
v___x_2313_ = v___x_2308_;
v_isShared_2314_ = v_isSharedCheck_2338_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_pos_2311_);
lean_dec(v___x_2308_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2338_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v_fst_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2336_; 
v_fst_2315_ = lean_ctor_get(v_res_2309_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v_res_2309_);
if (v_isSharedCheck_2336_ == 0)
{
lean_object* v_unused_2337_; 
v_unused_2337_ = lean_ctor_get(v_res_2309_, 1);
lean_dec(v_unused_2337_);
v___x_2317_ = v_res_2309_;
v_isShared_2318_ = v_isSharedCheck_2336_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_fst_2315_);
lean_dec(v_res_2309_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2336_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v_fst_2319_; lean_object* v_snd_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2335_; 
v_fst_2319_ = lean_ctor_get(v_snd_2310_, 0);
v_snd_2320_ = lean_ctor_get(v_snd_2310_, 1);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_snd_2310_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2322_ = v_snd_2310_;
v_isShared_2323_ = v_isSharedCheck_2335_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_snd_2320_);
lean_inc(v_fst_2319_);
lean_dec(v_snd_2310_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2335_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2324_; lean_object* v___x_2326_; 
v___x_2324_ = l_Std_Http_Version_ofNumber_x3f(v_fst_2319_, v_snd_2320_);
lean_dec(v_snd_2320_);
lean_dec(v_fst_2319_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 1, v___x_2324_);
lean_ctor_set(v___x_2322_, 0, v_fst_2315_);
v___x_2326_ = v___x_2322_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_fst_2315_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
lean_object* v___x_2327_; lean_object* v___x_2329_; 
v___x_2327_ = lean_box(v_res_2307_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 1, v___x_2326_);
lean_ctor_set(v___x_2317_, 0, v___x_2327_);
v___x_2329_ = v___x_2317_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2327_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v___x_2326_);
v___x_2329_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
lean_object* v___x_2331_; 
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 1, v___x_2329_);
v___x_2331_ = v___x_2313_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_pos_2311_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
}
}
}
else
{
lean_object* v_pos_2340_; lean_object* v_err_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
v_pos_2340_ = lean_ctor_get(v___x_2308_, 0);
v_err_2341_ = lean_ctor_get(v___x_2308_, 1);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2308_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_err_2341_);
lean_inc(v_pos_2340_);
lean_dec(v___x_2308_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_pos_2340_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_err_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion___boxed(lean_object* v_limits_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Std_Http_Protocol_H1_parseRequestLineRawVersion(v_limits_2406_, v_a_2407_);
lean_dec_ref(v_limits_2406_);
return v_res_2408_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(uint8_t v_snd_2409_, uint8_t v___x_2410_, uint8_t v___y_2411_){
_start:
{
uint32_t v___x_2412_; uint32_t v___x_2413_; uint8_t v___x_2414_; 
v___x_2412_ = lean_uint8_to_uint32(v___y_2411_);
v___x_2413_ = 32;
v___x_2414_ = lean_uint32_dec_eq(v___x_2412_, v___x_2413_);
if (v___x_2414_ == 0)
{
uint32_t v___x_2415_; uint8_t v___x_2416_; 
v___x_2415_ = 9;
v___x_2416_ = lean_uint32_dec_eq(v___x_2412_, v___x_2415_);
if (v___x_2416_ == 0)
{
return v_snd_2409_;
}
else
{
return v___x_2410_;
}
}
else
{
return v___x_2410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed(lean_object* v_snd_2417_, lean_object* v___x_2418_, lean_object* v___y_2419_){
_start:
{
uint8_t v_snd_3191__boxed_2420_; uint8_t v___x_3192__boxed_2421_; uint8_t v___y_3193__boxed_2422_; uint8_t v_res_2423_; lean_object* v_r_2424_; 
v_snd_3191__boxed_2420_ = lean_unbox(v_snd_2417_);
v___x_3192__boxed_2421_ = lean_unbox(v___x_2418_);
v___y_3193__boxed_2422_ = lean_unbox(v___y_2419_);
v_res_2423_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(v_snd_3191__boxed_2420_, v___x_3192__boxed_2421_, v___y_3193__boxed_2422_);
v_r_2424_ = lean_box(v_res_2423_);
return v_r_2424_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0(uint8_t v_snd_2425_, uint8_t v___x_2426_, uint8_t v___y_2427_){
_start:
{
uint32_t v___x_2428_; uint32_t v___x_2434_; uint8_t v___x_2435_; 
v___x_2428_ = lean_uint8_to_uint32(v___y_2427_);
v___x_2434_ = 33;
v___x_2435_ = lean_uint32_dec_le(v___x_2434_, v___x_2428_);
if (v___x_2435_ == 0)
{
goto v___jp_2429_;
}
else
{
uint32_t v___x_2436_; uint8_t v___x_2437_; 
v___x_2436_ = 126;
v___x_2437_ = lean_uint32_dec_le(v___x_2428_, v___x_2436_);
if (v___x_2437_ == 0)
{
goto v___jp_2429_;
}
else
{
return v___x_2426_;
}
}
v___jp_2429_:
{
uint32_t v___x_2430_; uint8_t v___x_2431_; 
v___x_2430_ = 32;
v___x_2431_ = lean_uint32_dec_eq(v___x_2428_, v___x_2430_);
if (v___x_2431_ == 0)
{
uint32_t v___x_2432_; uint8_t v___x_2433_; 
v___x_2432_ = 9;
v___x_2433_ = lean_uint32_dec_eq(v___x_2428_, v___x_2432_);
if (v___x_2433_ == 0)
{
return v_snd_2425_;
}
else
{
return v___x_2426_;
}
}
else
{
return v___x_2426_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0___boxed(lean_object* v_snd_2438_, lean_object* v___x_2439_, lean_object* v___y_2440_){
_start:
{
uint8_t v_snd_3210__boxed_2441_; uint8_t v___x_3211__boxed_2442_; uint8_t v___y_3212__boxed_2443_; uint8_t v_res_2444_; lean_object* v_r_2445_; 
v_snd_3210__boxed_2441_ = lean_unbox(v_snd_2438_);
v___x_3211__boxed_2442_ = lean_unbox(v___x_2439_);
v___y_3212__boxed_2443_ = lean_unbox(v___y_2440_);
v_res_2444_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0(v_snd_3210__boxed_2441_, v___x_3211__boxed_2442_, v___y_3212__boxed_2443_);
v_r_2445_ = lean_box(v_res_2444_);
return v_r_2445_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(lean_object* v_s_2446_, lean_object* v_pos_2447_){
_start:
{
lean_object* v_str_2448_; lean_object* v_startInclusive_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; uint8_t v___x_2453_; 
v_str_2448_ = lean_ctor_get(v_s_2446_, 0);
v_startInclusive_2449_ = lean_ctor_get(v_s_2446_, 1);
v___x_2450_ = lean_nat_add(v_startInclusive_2449_, v_pos_2447_);
v___x_2451_ = lean_nat_sub(v___x_2450_, v_startInclusive_2449_);
v___x_2452_ = lean_unsigned_to_nat(0u);
v___x_2453_ = lean_nat_dec_eq(v___x_2451_, v___x_2452_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; uint8_t v___y_2462_; lean_object* v___x_2463_; uint32_t v___x_2464_; uint8_t v___y_2466_; uint32_t v___x_2471_; uint8_t v___x_2472_; 
lean_inc(v_startInclusive_2449_);
lean_inc_ref(v_str_2448_);
v___x_2454_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2454_, 0, v_str_2448_);
lean_ctor_set(v___x_2454_, 1, v_startInclusive_2449_);
lean_ctor_set(v___x_2454_, 2, v___x_2450_);
v___x_2455_ = lean_unsigned_to_nat(1u);
v___x_2456_ = lean_nat_sub(v___x_2451_, v___x_2455_);
lean_dec(v___x_2451_);
v___x_2457_ = l_String_Slice_posLE(v___x_2454_, v___x_2456_);
lean_dec_ref_known(v___x_2454_, 3);
v___x_2463_ = lean_nat_add(v_startInclusive_2449_, v___x_2457_);
v___x_2464_ = lean_string_utf8_get_fast(v_str_2448_, v___x_2463_);
lean_dec(v___x_2463_);
v___x_2471_ = 32;
v___x_2472_ = lean_uint32_dec_eq(v___x_2464_, v___x_2471_);
if (v___x_2472_ == 0)
{
uint32_t v___x_2473_; uint8_t v___x_2474_; 
v___x_2473_ = 9;
v___x_2474_ = lean_uint32_dec_eq(v___x_2464_, v___x_2473_);
v___y_2466_ = v___x_2474_;
goto v___jp_2465_;
}
else
{
v___y_2466_ = v___x_2472_;
goto v___jp_2465_;
}
v___jp_2458_:
{
uint8_t v___x_2459_; 
v___x_2459_ = lean_nat_dec_lt(v___x_2457_, v_pos_2447_);
if (v___x_2459_ == 0)
{
lean_dec(v___x_2457_);
return v_pos_2447_;
}
else
{
lean_dec(v_pos_2447_);
v_pos_2447_ = v___x_2457_;
goto _start;
}
}
v___jp_2461_:
{
if (v___y_2462_ == 0)
{
lean_dec(v___x_2457_);
return v_pos_2447_;
}
else
{
goto v___jp_2458_;
}
}
v___jp_2465_:
{
if (v___y_2466_ == 0)
{
uint32_t v___x_2467_; uint8_t v___x_2468_; 
v___x_2467_ = 13;
v___x_2468_ = lean_uint32_dec_eq(v___x_2464_, v___x_2467_);
if (v___x_2468_ == 0)
{
uint32_t v___x_2469_; uint8_t v___x_2470_; 
v___x_2469_ = 10;
v___x_2470_ = lean_uint32_dec_eq(v___x_2464_, v___x_2469_);
v___y_2462_ = v___x_2470_;
goto v___jp_2461_;
}
else
{
v___y_2462_ = v___x_2468_;
goto v___jp_2461_;
}
}
else
{
goto v___jp_2458_;
}
}
}
else
{
lean_dec(v___x_2451_);
lean_dec(v___x_2450_);
return v_pos_2447_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0___boxed(lean_object* v_s_2475_, lean_object* v_pos_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(v_s_2475_, v_pos_2476_);
lean_dec_ref(v_s_2475_);
return v_res_2477_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0(void){
_start:
{
uint32_t v___x_2478_; uint8_t v___x_2479_; 
v___x_2478_ = 58;
v___x_2479_ = lean_uint32_to_uint8(v___x_2478_);
return v___x_2479_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1(void){
_start:
{
uint8_t v___x_2480_; lean_object* v___x_2481_; 
v___x_2480_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0);
v___x_2481_ = lean_uint8_to_nat(v___x_2480_);
return v___x_2481_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2(void){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1);
v___x_2483_ = l_Nat_reprFast(v___x_2482_);
return v___x_2483_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3(void){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2484_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2);
v___x_2485_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_2486_ = lean_string_append(v___x_2485_, v___x_2484_);
return v___x_2486_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4(void){
_start:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2487_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__5));
v___x_2488_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3);
v___x_2489_ = lean_string_append(v___x_2488_, v___x_2487_);
return v___x_2489_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__5(void){
_start:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2490_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4);
v___x_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2490_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(lean_object* v_limits_2492_, lean_object* v_a_2493_){
_start:
{
lean_object* v_maxHeaderNameLength_2494_; lean_object* v_maxHeaderValueLength_2495_; lean_object* v_maxSpaceSequence_2496_; lean_object* v___f_2497_; lean_object* v___x_2498_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2558_; lean_object* v_pos_2559_; lean_object* v_res_2560_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; uint8_t v___y_2570_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v_pos_2576_; lean_object* v_res_2577_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v_lower_2608_; lean_object* v_upper_2609_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v_pos_2625_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; uint8_t v___y_2656_; lean_object* v___x_2659_; lean_object* v_snd_2660_; lean_object* v_snd_2661_; uint8_t v___x_2662_; 
v_maxHeaderNameLength_2494_ = lean_ctor_get(v_limits_2492_, 6);
v_maxHeaderValueLength_2495_ = lean_ctor_get(v_limits_2492_, 7);
v_maxSpaceSequence_2496_ = lean_ctor_get(v_limits_2492_, 8);
v___f_2497_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_2498_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2493_);
v___x_2659_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2497_, v_maxHeaderNameLength_2494_, v___x_2498_, v_a_2493_);
v_snd_2660_ = lean_ctor_get(v___x_2659_, 1);
lean_inc(v_snd_2660_);
v_snd_2661_ = lean_ctor_get(v_snd_2660_, 1);
v___x_2662_ = lean_unbox(v_snd_2661_);
if (v___x_2662_ == 0)
{
lean_object* v_fst_2663_; lean_object* v_fst_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2753_; 
lean_inc(v_snd_2661_);
v_fst_2663_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_fst_2663_);
lean_dec_ref(v___x_2659_);
v_fst_2664_ = lean_ctor_get(v_snd_2660_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v_snd_2660_);
if (v_isSharedCheck_2753_ == 0)
{
lean_object* v_unused_2754_; 
v_unused_2754_ = lean_ctor_get(v_snd_2660_, 1);
lean_dec(v_unused_2754_);
v___x_2666_ = v_snd_2660_;
v_isShared_2667_ = v_isSharedCheck_2753_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_fst_2664_);
lean_dec(v_snd_2660_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2753_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
uint8_t v___x_2668_; 
v___x_2668_ = lean_nat_dec_eq(v_fst_2663_, v___x_2498_);
if (v___x_2668_ == 0)
{
lean_object* v_array_2669_; lean_object* v_idx_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2748_; 
v_array_2669_ = lean_ctor_get(v_a_2493_, 0);
v_idx_2670_ = lean_ctor_get(v_a_2493_, 1);
v_isSharedCheck_2748_ = !lean_is_exclusive(v_a_2493_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2672_ = v_a_2493_;
v_isShared_2673_ = v_isSharedCheck_2748_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_idx_2670_);
lean_inc(v_array_2669_);
lean_dec(v_a_2493_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2748_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___y_2675_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___y_2739_; uint8_t v___x_2747_; 
v___x_2736_ = lean_nat_add(v_idx_2670_, v_fst_2663_);
lean_dec(v_fst_2663_);
v___x_2737_ = lean_byte_array_size(v_array_2669_);
v___x_2747_ = lean_nat_dec_le(v_idx_2670_, v___x_2498_);
if (v___x_2747_ == 0)
{
v___y_2739_ = v_idx_2670_;
goto v___jp_2738_;
}
else
{
lean_dec(v_idx_2670_);
v___y_2739_ = v___x_2498_;
goto v___jp_2738_;
}
v___jp_2674_:
{
lean_object* v_array_2676_; lean_object* v_idx_2677_; lean_object* v___x_2678_; uint8_t v___x_2679_; 
v_array_2676_ = lean_ctor_get(v_fst_2664_, 0);
v_idx_2677_ = lean_ctor_get(v_fst_2664_, 1);
v___x_2678_ = lean_byte_array_size(v_array_2676_);
v___x_2679_ = lean_nat_dec_lt(v_idx_2677_, v___x_2678_);
if (v___x_2679_ == 0)
{
lean_object* v___x_2680_; lean_object* v___x_2682_; 
lean_dec_ref(v___y_2675_);
lean_dec_ref(v_array_2669_);
lean_dec(v_snd_2661_);
v___x_2680_ = lean_box(0);
if (v_isShared_2673_ == 0)
{
lean_ctor_set_tag(v___x_2672_, 1);
lean_ctor_set(v___x_2672_, 1, v___x_2680_);
lean_ctor_set(v___x_2672_, 0, v_fst_2664_);
v___x_2682_ = v___x_2672_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_fst_2664_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
else
{
uint8_t v___x_2684_; uint8_t v_got_2685_; uint8_t v___x_2686_; 
v___x_2684_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0);
v_got_2685_ = lean_byte_array_fget(v_array_2676_, v_idx_2677_);
v___x_2686_ = lean_uint8_dec_eq(v_got_2685_, v___x_2684_);
if (v___x_2686_ == 0)
{
lean_object* v___x_2687_; lean_object* v___x_2689_; 
lean_dec_ref(v___y_2675_);
lean_dec_ref(v_array_2669_);
lean_dec(v_snd_2661_);
v___x_2687_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__5, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__5_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__5);
if (v_isShared_2673_ == 0)
{
lean_ctor_set_tag(v___x_2672_, 1);
lean_ctor_set(v___x_2672_, 1, v___x_2687_);
lean_ctor_set(v___x_2672_, 0, v_fst_2664_);
v___x_2689_ = v___x_2672_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_fst_2664_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v___x_2687_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
else
{
lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2733_; 
lean_inc(v_idx_2677_);
lean_inc_ref(v_array_2676_);
lean_del_object(v___x_2672_);
v_isSharedCheck_2733_ = !lean_is_exclusive(v_fst_2664_);
if (v_isSharedCheck_2733_ == 0)
{
lean_object* v_unused_2734_; lean_object* v_unused_2735_; 
v_unused_2734_ = lean_ctor_get(v_fst_2664_, 1);
lean_dec(v_unused_2734_);
v_unused_2735_ = lean_ctor_get(v_fst_2664_, 0);
lean_dec(v_unused_2735_);
v___x_2692_ = v_fst_2664_;
v_isShared_2693_ = v_isSharedCheck_2733_;
goto v_resetjp_2691_;
}
else
{
lean_dec(v_fst_2664_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2733_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2694_; lean_object* v___f_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2699_; 
v___x_2694_ = lean_box(v___x_2679_);
v___f_2695_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2695_, 0, v_snd_2661_);
lean_closure_set(v___f_2695_, 1, v___x_2694_);
v___x_2696_ = lean_unsigned_to_nat(1u);
v___x_2697_ = lean_nat_add(v_idx_2677_, v___x_2696_);
lean_dec(v_idx_2677_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 1, v___x_2697_);
v___x_2699_ = v___x_2692_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_array_2676_);
lean_ctor_set(v_reuseFailAlloc_2732_, 1, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
lean_object* v___x_2700_; lean_object* v_snd_2701_; lean_object* v_snd_2702_; uint8_t v___x_2703_; 
v___x_2700_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2695_, v_maxSpaceSequence_2496_, v___x_2498_, v___x_2699_);
v_snd_2701_ = lean_ctor_get(v___x_2700_, 1);
lean_inc(v_snd_2701_);
lean_dec_ref(v___x_2700_);
v_snd_2702_ = lean_ctor_get(v_snd_2701_, 1);
v___x_2703_ = lean_unbox(v_snd_2702_);
if (v___x_2703_ == 0)
{
lean_object* v_fst_2704_; lean_object* v_array_2705_; lean_object* v_idx_2706_; lean_object* v_lower_2707_; lean_object* v_upper_2708_; lean_object* v___x_2709_; lean_object* v___f_2710_; lean_object* v___x_2711_; lean_object* v___f_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; uint8_t v___x_2715_; 
lean_inc_n(v_snd_2702_, 2);
v_fst_2704_ = lean_ctor_get(v_snd_2701_, 0);
lean_inc(v_fst_2704_);
lean_dec(v_snd_2701_);
v_array_2705_ = lean_ctor_get(v_fst_2704_, 0);
v_idx_2706_ = lean_ctor_get(v_fst_2704_, 1);
v_lower_2707_ = lean_ctor_get(v___y_2675_, 0);
lean_inc(v_lower_2707_);
v_upper_2708_ = lean_ctor_get(v___y_2675_, 1);
lean_inc(v_upper_2708_);
lean_dec_ref(v___y_2675_);
v___x_2709_ = lean_box(v___x_2679_);
v___f_2710_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2710_, 0, v_snd_2702_);
lean_closure_set(v___f_2710_, 1, v___x_2709_);
v___x_2711_ = lean_box(v___x_2679_);
v___f_2712_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2712_, 0, v_snd_2702_);
lean_closure_set(v___f_2712_, 1, v___x_2711_);
v___x_2713_ = l_ByteArray_toByteSlice(v_array_2669_, v_lower_2707_, v_upper_2708_);
v___x_2714_ = lean_byte_array_size(v_array_2705_);
v___x_2715_ = lean_nat_dec_lt(v_idx_2706_, v___x_2714_);
if (v___x_2715_ == 0)
{
v___y_2622_ = v___f_2712_;
v___y_2623_ = v___f_2710_;
v___y_2624_ = v___x_2713_;
v_pos_2625_ = v_fst_2704_;
goto v___jp_2621_;
}
else
{
uint8_t v___x_2716_; uint32_t v___x_2717_; uint32_t v___x_2718_; uint8_t v___x_2719_; 
v___x_2716_ = lean_byte_array_fget(v_array_2705_, v_idx_2706_);
v___x_2717_ = lean_uint8_to_uint32(v___x_2716_);
v___x_2718_ = 32;
v___x_2719_ = lean_uint32_dec_eq(v___x_2717_, v___x_2718_);
if (v___x_2719_ == 0)
{
uint32_t v___x_2720_; uint8_t v___x_2721_; 
v___x_2720_ = 9;
v___x_2721_ = lean_uint32_dec_eq(v___x_2717_, v___x_2720_);
if (v___x_2721_ == 0)
{
v___y_2622_ = v___f_2712_;
v___y_2623_ = v___f_2710_;
v___y_2624_ = v___x_2713_;
v_pos_2625_ = v_fst_2704_;
goto v___jp_2621_;
}
else
{
v___y_2652_ = v___f_2712_;
v___y_2653_ = v___f_2710_;
v___y_2654_ = v___x_2713_;
v___y_2655_ = v_fst_2704_;
v___y_2656_ = v___x_2715_;
goto v___jp_2651_;
}
}
else
{
v___y_2652_ = v___f_2712_;
v___y_2653_ = v___f_2710_;
v___y_2654_ = v___x_2713_;
v___y_2655_ = v_fst_2704_;
v___y_2656_ = v___x_2715_;
goto v___jp_2651_;
}
}
}
else
{
lean_object* v_fst_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2730_; 
lean_dec_ref(v___y_2675_);
lean_dec_ref(v_array_2669_);
v_fst_2722_ = lean_ctor_get(v_snd_2701_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v_snd_2701_);
if (v_isSharedCheck_2730_ == 0)
{
lean_object* v_unused_2731_; 
v_unused_2731_ = lean_ctor_get(v_snd_2701_, 1);
lean_dec(v_unused_2731_);
v___x_2724_ = v_snd_2701_;
v_isShared_2725_ = v_isSharedCheck_2730_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_fst_2722_);
lean_dec(v_snd_2701_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2730_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2726_; lean_object* v___x_2728_; 
v___x_2726_ = lean_box(0);
if (v_isShared_2725_ == 0)
{
lean_ctor_set_tag(v___x_2724_, 1);
lean_ctor_set(v___x_2724_, 1, v___x_2726_);
v___x_2728_ = v___x_2724_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_fst_2722_);
lean_ctor_set(v_reuseFailAlloc_2729_, 1, v___x_2726_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
}
}
}
}
v___jp_2738_:
{
uint8_t v___x_2740_; 
v___x_2740_ = lean_nat_dec_le(v___x_2736_, v___x_2737_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2742_; 
lean_dec(v___x_2736_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 1, v___x_2737_);
lean_ctor_set(v___x_2666_, 0, v___y_2739_);
v___x_2742_ = v___x_2666_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___y_2739_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v___x_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
v___y_2675_ = v___x_2742_;
goto v___jp_2674_;
}
}
else
{
lean_object* v___x_2745_; 
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 1, v___x_2736_);
lean_ctor_set(v___x_2666_, 0, v___y_2739_);
v___x_2745_ = v___x_2666_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___y_2739_);
lean_ctor_set(v_reuseFailAlloc_2746_, 1, v___x_2736_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
v___y_2675_ = v___x_2745_;
goto v___jp_2674_;
}
}
}
}
}
else
{
lean_object* v___x_2749_; lean_object* v___x_2751_; 
lean_dec(v_fst_2664_);
lean_dec(v_fst_2663_);
lean_dec(v_snd_2661_);
v___x_2749_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_2667_ == 0)
{
lean_ctor_set_tag(v___x_2666_, 1);
lean_ctor_set(v___x_2666_, 1, v___x_2749_);
lean_ctor_set(v___x_2666_, 0, v_a_2493_);
v___x_2751_ = v___x_2666_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2493_);
lean_ctor_set(v_reuseFailAlloc_2752_, 1, v___x_2749_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
else
{
lean_object* v_fst_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2763_; 
lean_dec_ref(v___x_2659_);
lean_dec_ref(v_a_2493_);
v_fst_2755_ = lean_ctor_get(v_snd_2660_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v_snd_2660_);
if (v_isSharedCheck_2763_ == 0)
{
lean_object* v_unused_2764_; 
v_unused_2764_ = lean_ctor_get(v_snd_2660_, 1);
lean_dec(v_unused_2764_);
v___x_2757_ = v_snd_2660_;
v_isShared_2758_ = v_isSharedCheck_2763_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_fst_2755_);
lean_dec(v_snd_2660_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2763_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2759_; lean_object* v___x_2761_; 
v___x_2759_ = lean_box(0);
if (v_isShared_2758_ == 0)
{
lean_ctor_set_tag(v___x_2757_, 1);
lean_ctor_set(v___x_2757_, 1, v___x_2759_);
v___x_2761_ = v___x_2757_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_fst_2755_);
lean_ctor_set(v_reuseFailAlloc_2762_, 1, v___x_2759_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
v___jp_2499_:
{
lean_object* v___x_2503_; 
v___x_2503_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___y_2502_, v___y_2501_);
lean_dec(v___y_2502_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_pos_2504_; lean_object* v_res_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2518_; 
v_pos_2504_ = lean_ctor_get(v___x_2503_, 0);
v_res_2505_ = lean_ctor_get(v___x_2503_, 1);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2507_ = v___x_2503_;
v_isShared_2508_ = v_isSharedCheck_2518_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_res_2505_);
lean_inc(v_pos_2504_);
lean_dec(v___x_2503_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2518_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2516_; 
v___x_2509_ = lean_string_utf8_byte_size(v_res_2505_);
lean_inc(v_res_2505_);
v___x_2510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2510_, 0, v_res_2505_);
lean_ctor_set(v___x_2510_, 1, v___x_2498_);
lean_ctor_set(v___x_2510_, 2, v___x_2509_);
v___x_2511_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(v___x_2510_, v___x_2509_);
lean_dec_ref_known(v___x_2510_, 3);
v___x_2512_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2512_, 0, v_res_2505_);
lean_ctor_set(v___x_2512_, 1, v___x_2498_);
lean_ctor_set(v___x_2512_, 2, v___x_2511_);
v___x_2513_ = l_String_Slice_toString(v___x_2512_);
lean_dec_ref_known(v___x_2512_, 3);
v___x_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___y_2500_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 1, v___x_2514_);
v___x_2516_ = v___x_2507_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_pos_2504_);
lean_ctor_set(v_reuseFailAlloc_2517_, 1, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
else
{
lean_object* v_pos_2519_; lean_object* v_err_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
lean_dec_ref(v___y_2500_);
v_pos_2519_ = lean_ctor_get(v___x_2503_, 0);
v_err_2520_ = lean_ctor_get(v___x_2503_, 1);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2503_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_err_2520_);
lean_inc(v_pos_2519_);
lean_dec(v___x_2503_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_pos_2519_);
lean_ctor_set(v_reuseFailAlloc_2526_, 1, v_err_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
v___jp_2528_:
{
uint8_t v___x_2532_; 
v___x_2532_ = lean_string_validate_utf8(v___y_2531_);
if (v___x_2532_ == 0)
{
lean_object* v___x_2533_; 
lean_dec_ref(v___y_2531_);
v___x_2533_ = lean_box(0);
v___y_2500_ = v___y_2529_;
v___y_2501_ = v___y_2530_;
v___y_2502_ = v___x_2533_;
goto v___jp_2499_;
}
else
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2534_ = lean_string_from_utf8_unchecked(v___y_2531_);
v___x_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2534_);
v___y_2500_ = v___y_2529_;
v___y_2501_ = v___y_2530_;
v___y_2502_ = v___x_2535_;
goto v___jp_2499_;
}
}
v___jp_2536_:
{
lean_object* v___x_2540_; 
v___x_2540_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___y_2539_, v___y_2538_);
lean_dec(v___y_2539_);
if (lean_obj_tag(v___x_2540_) == 0)
{
if (lean_obj_tag(v___y_2537_) == 0)
{
lean_object* v_pos_2541_; lean_object* v_res_2542_; lean_object* v___x_2543_; 
v_pos_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_pos_2541_);
v_res_2542_ = lean_ctor_get(v___x_2540_, 1);
lean_inc(v_res_2542_);
lean_dec_ref_known(v___x_2540_, 2);
v___x_2543_ = l_ByteArray_empty;
v___y_2529_ = v_res_2542_;
v___y_2530_ = v_pos_2541_;
v___y_2531_ = v___x_2543_;
goto v___jp_2528_;
}
else
{
lean_object* v_pos_2544_; lean_object* v_res_2545_; lean_object* v_val_2546_; lean_object* v___x_2547_; 
v_pos_2544_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_pos_2544_);
v_res_2545_ = lean_ctor_get(v___x_2540_, 1);
lean_inc(v_res_2545_);
lean_dec_ref_known(v___x_2540_, 2);
v_val_2546_ = lean_ctor_get(v___y_2537_, 0);
lean_inc(v_val_2546_);
lean_dec_ref_known(v___y_2537_, 1);
v___x_2547_ = l_ByteSlice_toByteArray(v_val_2546_);
v___y_2529_ = v_res_2545_;
v___y_2530_ = v_pos_2544_;
v___y_2531_ = v___x_2547_;
goto v___jp_2528_;
}
}
else
{
lean_object* v_pos_2548_; lean_object* v_err_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec(v___y_2537_);
v_pos_2548_ = lean_ctor_get(v___x_2540_, 0);
v_err_2549_ = lean_ctor_get(v___x_2540_, 1);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2540_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_err_2549_);
lean_inc(v_pos_2548_);
lean_dec(v___x_2540_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_pos_2548_);
lean_ctor_set(v_reuseFailAlloc_2555_, 1, v_err_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
v___jp_2557_:
{
lean_object* v___x_2561_; uint8_t v___x_2562_; 
v___x_2561_ = l_ByteSlice_toByteArray(v___y_2558_);
v___x_2562_ = lean_string_validate_utf8(v___x_2561_);
if (v___x_2562_ == 0)
{
lean_object* v___x_2563_; 
lean_dec_ref(v___x_2561_);
v___x_2563_ = lean_box(0);
v___y_2537_ = v_res_2560_;
v___y_2538_ = v_pos_2559_;
v___y_2539_ = v___x_2563_;
goto v___jp_2536_;
}
else
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2564_ = lean_string_from_utf8_unchecked(v___x_2561_);
v___x_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
v___y_2537_ = v_res_2560_;
v___y_2538_ = v_pos_2559_;
v___y_2539_ = v___x_2565_;
goto v___jp_2536_;
}
}
v___jp_2566_:
{
if (v___y_2570_ == 0)
{
v___y_2558_ = v___y_2569_;
v_pos_2559_ = v___y_2567_;
v_res_2560_ = v___y_2568_;
goto v___jp_2557_;
}
else
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
lean_dec_ref(v___y_2569_);
lean_dec(v___y_2568_);
v___x_2571_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2));
v___x_2572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___y_2567_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
return v___x_2572_;
}
}
v___jp_2573_:
{
lean_object* v___x_2578_; lean_object* v_snd_2579_; lean_object* v_snd_2580_; uint8_t v___x_2581_; 
v___x_2578_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___y_2574_, v_maxSpaceSequence_2496_, v___x_2498_, v_pos_2576_);
v_snd_2579_ = lean_ctor_get(v___x_2578_, 1);
lean_inc(v_snd_2579_);
lean_dec_ref(v___x_2578_);
v_snd_2580_ = lean_ctor_get(v_snd_2579_, 1);
v___x_2581_ = lean_unbox(v_snd_2580_);
if (v___x_2581_ == 0)
{
lean_object* v_fst_2582_; lean_object* v_array_2583_; lean_object* v_idx_2584_; lean_object* v___x_2585_; uint8_t v___x_2586_; 
v_fst_2582_ = lean_ctor_get(v_snd_2579_, 0);
lean_inc(v_fst_2582_);
lean_dec(v_snd_2579_);
v_array_2583_ = lean_ctor_get(v_fst_2582_, 0);
v_idx_2584_ = lean_ctor_get(v_fst_2582_, 1);
v___x_2585_ = lean_byte_array_size(v_array_2583_);
v___x_2586_ = lean_nat_dec_lt(v_idx_2584_, v___x_2585_);
if (v___x_2586_ == 0)
{
v___y_2558_ = v___y_2575_;
v_pos_2559_ = v_fst_2582_;
v_res_2560_ = v_res_2577_;
goto v___jp_2557_;
}
else
{
uint8_t v___x_2587_; uint32_t v___x_2588_; uint32_t v___x_2589_; uint8_t v___x_2590_; 
v___x_2587_ = lean_byte_array_fget(v_array_2583_, v_idx_2584_);
v___x_2588_ = lean_uint8_to_uint32(v___x_2587_);
v___x_2589_ = 32;
v___x_2590_ = lean_uint32_dec_eq(v___x_2588_, v___x_2589_);
if (v___x_2590_ == 0)
{
uint32_t v___x_2591_; uint8_t v___x_2592_; 
v___x_2591_ = 9;
v___x_2592_ = lean_uint32_dec_eq(v___x_2588_, v___x_2591_);
if (v___x_2592_ == 0)
{
v___y_2558_ = v___y_2575_;
v_pos_2559_ = v_fst_2582_;
v_res_2560_ = v_res_2577_;
goto v___jp_2557_;
}
else
{
v___y_2567_ = v_fst_2582_;
v___y_2568_ = v_res_2577_;
v___y_2569_ = v___y_2575_;
v___y_2570_ = v___x_2586_;
goto v___jp_2566_;
}
}
else
{
v___y_2567_ = v_fst_2582_;
v___y_2568_ = v_res_2577_;
v___y_2569_ = v___y_2575_;
v___y_2570_ = v___x_2586_;
goto v___jp_2566_;
}
}
}
else
{
lean_object* v_fst_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2601_; 
lean_dec(v_res_2577_);
lean_dec_ref(v___y_2575_);
v_fst_2593_ = lean_ctor_get(v_snd_2579_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v_snd_2579_);
if (v_isSharedCheck_2601_ == 0)
{
lean_object* v_unused_2602_; 
v_unused_2602_ = lean_ctor_get(v_snd_2579_, 1);
lean_dec(v_unused_2602_);
v___x_2595_ = v_snd_2579_;
v_isShared_2596_ = v_isSharedCheck_2601_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_fst_2593_);
lean_dec(v_snd_2579_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2601_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2597_; lean_object* v___x_2599_; 
v___x_2597_ = lean_box(0);
if (v_isShared_2596_ == 0)
{
lean_ctor_set_tag(v___x_2595_, 1);
lean_ctor_set(v___x_2595_, 1, v___x_2597_);
v___x_2599_ = v___x_2595_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_fst_2593_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v___x_2597_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
v___jp_2603_:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = l_ByteArray_toByteSlice(v___y_2606_, v_lower_2608_, v_upper_2609_);
v___x_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
v___y_2574_ = v___y_2604_;
v___y_2575_ = v___y_2607_;
v_pos_2576_ = v___y_2605_;
v_res_2577_ = v___x_2611_;
goto v___jp_2573_;
}
v___jp_2612_:
{
uint8_t v___x_2620_; 
v___x_2620_ = lean_nat_dec_le(v___y_2616_, v___y_2617_);
if (v___x_2620_ == 0)
{
lean_dec(v___y_2616_);
v___y_2604_ = v___y_2613_;
v___y_2605_ = v___y_2614_;
v___y_2606_ = v___y_2615_;
v___y_2607_ = v___y_2618_;
v_lower_2608_ = v___y_2619_;
v_upper_2609_ = v___y_2617_;
goto v___jp_2603_;
}
else
{
lean_dec(v___y_2617_);
v___y_2604_ = v___y_2613_;
v___y_2605_ = v___y_2614_;
v___y_2606_ = v___y_2615_;
v___y_2607_ = v___y_2618_;
v_lower_2608_ = v___y_2619_;
v_upper_2609_ = v___y_2616_;
goto v___jp_2603_;
}
}
v___jp_2621_:
{
lean_object* v___x_2626_; lean_object* v_snd_2627_; lean_object* v_snd_2628_; uint8_t v___x_2629_; 
lean_inc_ref(v_pos_2625_);
v___x_2626_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___y_2623_, v_maxHeaderValueLength_2495_, v___x_2498_, v_pos_2625_);
v_snd_2627_ = lean_ctor_get(v___x_2626_, 1);
lean_inc(v_snd_2627_);
v_snd_2628_ = lean_ctor_get(v_snd_2627_, 1);
v___x_2629_ = lean_unbox(v_snd_2628_);
if (v___x_2629_ == 0)
{
lean_object* v_fst_2630_; lean_object* v_fst_2631_; lean_object* v_array_2632_; lean_object* v_idx_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; uint8_t v___x_2636_; 
v_fst_2630_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_fst_2630_);
lean_dec_ref(v___x_2626_);
v_fst_2631_ = lean_ctor_get(v_snd_2627_, 0);
lean_inc(v_fst_2631_);
lean_dec(v_snd_2627_);
v_array_2632_ = lean_ctor_get(v_pos_2625_, 0);
lean_inc_ref(v_array_2632_);
v_idx_2633_ = lean_ctor_get(v_pos_2625_, 1);
lean_inc(v_idx_2633_);
lean_dec_ref(v_pos_2625_);
v___x_2634_ = lean_nat_add(v_idx_2633_, v_fst_2630_);
lean_dec(v_fst_2630_);
v___x_2635_ = lean_byte_array_size(v_array_2632_);
v___x_2636_ = lean_nat_dec_le(v_idx_2633_, v___x_2498_);
if (v___x_2636_ == 0)
{
v___y_2613_ = v___y_2622_;
v___y_2614_ = v_fst_2631_;
v___y_2615_ = v_array_2632_;
v___y_2616_ = v___x_2634_;
v___y_2617_ = v___x_2635_;
v___y_2618_ = v___y_2624_;
v___y_2619_ = v_idx_2633_;
goto v___jp_2612_;
}
else
{
lean_dec(v_idx_2633_);
v___y_2613_ = v___y_2622_;
v___y_2614_ = v_fst_2631_;
v___y_2615_ = v_array_2632_;
v___y_2616_ = v___x_2634_;
v___y_2617_ = v___x_2635_;
v___y_2618_ = v___y_2624_;
v___y_2619_ = v___x_2498_;
goto v___jp_2612_;
}
}
else
{
lean_object* v_fst_2637_; lean_object* v_idx_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2649_; 
lean_dec_ref(v___x_2626_);
v_fst_2637_ = lean_ctor_get(v_snd_2627_, 0);
lean_inc(v_fst_2637_);
lean_dec(v_snd_2627_);
v_idx_2638_ = lean_ctor_get(v_pos_2625_, 1);
v_isSharedCheck_2649_ = !lean_is_exclusive(v_pos_2625_);
if (v_isSharedCheck_2649_ == 0)
{
lean_object* v_unused_2650_; 
v_unused_2650_ = lean_ctor_get(v_pos_2625_, 0);
lean_dec(v_unused_2650_);
v___x_2640_ = v_pos_2625_;
v_isShared_2641_ = v_isSharedCheck_2649_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_idx_2638_);
lean_dec(v_pos_2625_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2649_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v_idx_2642_; uint8_t v___x_2643_; 
v_idx_2642_ = lean_ctor_get(v_fst_2637_, 1);
v___x_2643_ = lean_nat_dec_eq(v_idx_2638_, v_idx_2642_);
lean_dec(v_idx_2638_);
if (v___x_2643_ == 0)
{
lean_object* v___x_2644_; lean_object* v___x_2646_; 
lean_dec_ref(v___y_2624_);
lean_dec_ref(v___y_2622_);
v___x_2644_ = lean_box(0);
if (v_isShared_2641_ == 0)
{
lean_ctor_set_tag(v___x_2640_, 1);
lean_ctor_set(v___x_2640_, 1, v___x_2644_);
lean_ctor_set(v___x_2640_, 0, v_fst_2637_);
v___x_2646_ = v___x_2640_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_fst_2637_);
lean_ctor_set(v_reuseFailAlloc_2647_, 1, v___x_2644_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
else
{
lean_object* v___x_2648_; 
lean_del_object(v___x_2640_);
v___x_2648_ = lean_box(0);
v___y_2574_ = v___y_2622_;
v___y_2575_ = v___y_2624_;
v_pos_2576_ = v_fst_2637_;
v_res_2577_ = v___x_2648_;
goto v___jp_2573_;
}
}
}
}
v___jp_2651_:
{
if (v___y_2656_ == 0)
{
v___y_2622_ = v___y_2652_;
v___y_2623_ = v___y_2653_;
v___y_2624_ = v___y_2654_;
v_pos_2625_ = v___y_2655_;
goto v___jp_2621_;
}
else
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
lean_dec_ref(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec_ref(v___y_2652_);
v___x_2657_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2));
v___x_2658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2658_, 0, v___y_2655_);
lean_ctor_set(v___x_2658_, 1, v___x_2657_);
return v___x_2658_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___boxed(lean_object* v_limits_2765_, lean_object* v_a_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_2765_, v_a_2766_);
lean_dec_ref(v_limits_2765_);
return v_res_2767_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(lean_object* v_x_2768_, lean_object* v_x_2769_){
_start:
{
if (lean_obj_tag(v_x_2768_) == 0)
{
if (lean_obj_tag(v_x_2769_) == 0)
{
uint8_t v___x_2770_; 
v___x_2770_ = 1;
return v___x_2770_;
}
else
{
uint8_t v___x_2771_; 
v___x_2771_ = 0;
return v___x_2771_;
}
}
else
{
if (lean_obj_tag(v_x_2769_) == 0)
{
uint8_t v___x_2772_; 
v___x_2772_ = 0;
return v___x_2772_;
}
else
{
lean_object* v_val_2773_; lean_object* v_val_2774_; uint8_t v___x_2775_; uint8_t v___x_2776_; uint8_t v___x_2777_; 
v_val_2773_ = lean_ctor_get(v_x_2768_, 0);
v_val_2774_ = lean_ctor_get(v_x_2769_, 0);
v___x_2775_ = lean_unbox(v_val_2773_);
v___x_2776_ = lean_unbox(v_val_2774_);
v___x_2777_ = lean_uint8_dec_eq(v___x_2775_, v___x_2776_);
return v___x_2777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0___boxed(lean_object* v_x_2778_, lean_object* v_x_2779_){
_start:
{
uint8_t v_res_2780_; lean_object* v_r_2781_; 
v_res_2780_ = l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_x_2778_, v_x_2779_);
lean_dec(v_x_2779_);
lean_dec(v_x_2778_);
v_r_2781_ = lean_box(v_res_2780_);
return v_r_2781_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_parseSingleHeader___closed__0(void){
_start:
{
uint8_t v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2782_ = lean_uint8_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0);
v___x_2783_ = lean_box(v___x_2782_);
v___x_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
return v___x_2784_;
}
}
static uint8_t _init_l_Std_Http_Protocol_H1_parseSingleHeader___closed__1(void){
_start:
{
uint32_t v___x_2785_; uint8_t v___x_2786_; 
v___x_2785_ = 10;
v___x_2786_ = lean_uint32_to_uint8(v___x_2785_);
return v___x_2786_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_parseSingleHeader___closed__2(void){
_start:
{
uint8_t v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2787_ = lean_uint8_once(&l_Std_Http_Protocol_H1_parseSingleHeader___closed__1, &l_Std_Http_Protocol_H1_parseSingleHeader___closed__1_once, _init_l_Std_Http_Protocol_H1_parseSingleHeader___closed__1);
v___x_2788_ = lean_box(v___x_2787_);
v___x_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader(lean_object* v_limits_2790_, lean_object* v_a_2791_){
_start:
{
lean_object* v_pos_2793_; lean_object* v_res_2794_; lean_object* v___y_2798_; lean_object* v_pos_2821_; lean_object* v_res_2822_; lean_object* v_array_2853_; lean_object* v_idx_2854_; lean_object* v___x_2855_; uint8_t v___x_2856_; 
v_array_2853_ = lean_ctor_get(v_a_2791_, 0);
v_idx_2854_ = lean_ctor_get(v_a_2791_, 1);
v___x_2855_ = lean_byte_array_size(v_array_2853_);
v___x_2856_ = lean_nat_dec_lt(v_idx_2854_, v___x_2855_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; 
v___x_2857_ = lean_box(0);
v_pos_2821_ = v_a_2791_;
v_res_2822_ = v___x_2857_;
goto v___jp_2820_;
}
else
{
uint8_t v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2858_ = lean_byte_array_fget(v_array_2853_, v_idx_2854_);
v___x_2859_ = lean_box(v___x_2858_);
v___x_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
v_pos_2821_ = v_a_2791_;
v_res_2822_ = v___x_2860_;
goto v___jp_2820_;
}
v___jp_2792_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2795_, 0, v_res_2794_);
v___x_2796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2796_, 0, v_pos_2793_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
return v___x_2796_;
}
v___jp_2797_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2800_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2799_, v___y_2798_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_pos_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2809_; 
v_pos_2801_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2809_ == 0)
{
lean_object* v_unused_2810_; 
v_unused_2810_ = lean_ctor_get(v___x_2800_, 1);
lean_dec(v_unused_2810_);
v___x_2803_ = v___x_2800_;
v_isShared_2804_ = v_isSharedCheck_2809_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_pos_2801_);
lean_dec(v___x_2800_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2809_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2805_; lean_object* v___x_2807_; 
v___x_2805_ = lean_box(0);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 1, v___x_2805_);
v___x_2807_ = v___x_2803_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_pos_2801_);
lean_ctor_set(v_reuseFailAlloc_2808_, 1, v___x_2805_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
else
{
lean_object* v_pos_2811_; lean_object* v_err_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
v_pos_2811_ = lean_ctor_get(v___x_2800_, 0);
v_err_2812_ = lean_ctor_get(v___x_2800_, 1);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2800_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_err_2812_);
lean_inc(v_pos_2811_);
lean_dec(v___x_2800_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_pos_2811_);
lean_ctor_set(v_reuseFailAlloc_2818_, 1, v_err_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
v___jp_2820_:
{
lean_object* v___x_2823_; uint8_t v___x_2824_; 
v___x_2823_ = lean_obj_once(&l_Std_Http_Protocol_H1_parseSingleHeader___closed__0, &l_Std_Http_Protocol_H1_parseSingleHeader___closed__0_once, _init_l_Std_Http_Protocol_H1_parseSingleHeader___closed__0);
v___x_2824_ = l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_2822_, v___x_2823_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; uint8_t v___x_2826_; 
v___x_2825_ = lean_obj_once(&l_Std_Http_Protocol_H1_parseSingleHeader___closed__2, &l_Std_Http_Protocol_H1_parseSingleHeader___closed__2_once, _init_l_Std_Http_Protocol_H1_parseSingleHeader___closed__2);
v___x_2826_ = l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_2822_, v___x_2825_);
lean_dec(v_res_2822_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; 
v___x_2827_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_2790_, v_pos_2821_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_pos_2828_; lean_object* v_res_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v_pos_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_pos_2828_);
v_res_2829_ = lean_ctor_get(v___x_2827_, 1);
lean_inc(v_res_2829_);
lean_dec_ref_known(v___x_2827_, 2);
v___x_2830_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2831_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2830_, v_pos_2828_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_pos_2832_; 
v_pos_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc(v_pos_2832_);
lean_dec_ref_known(v___x_2831_, 2);
v_pos_2793_ = v_pos_2832_;
v_res_2794_ = v_res_2829_;
goto v___jp_2792_;
}
else
{
lean_object* v_pos_2833_; lean_object* v_err_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec(v_res_2829_);
v_pos_2833_ = lean_ctor_get(v___x_2831_, 0);
v_err_2834_ = lean_ctor_get(v___x_2831_, 1);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2831_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_err_2834_);
lean_inc(v_pos_2833_);
lean_dec(v___x_2831_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_pos_2833_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_err_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_pos_2842_; lean_object* v_res_2843_; 
v_pos_2842_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_pos_2842_);
v_res_2843_ = lean_ctor_get(v___x_2827_, 1);
lean_inc(v_res_2843_);
lean_dec_ref_known(v___x_2827_, 2);
v_pos_2793_ = v_pos_2842_;
v_res_2794_ = v_res_2843_;
goto v___jp_2792_;
}
else
{
lean_object* v_pos_2844_; lean_object* v_err_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
v_pos_2844_ = lean_ctor_get(v___x_2827_, 0);
v_err_2845_ = lean_ctor_get(v___x_2827_, 1);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2827_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_err_2845_);
lean_inc(v_pos_2844_);
lean_dec(v___x_2827_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_pos_2844_);
lean_ctor_set(v_reuseFailAlloc_2851_, 1, v_err_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
}
else
{
v___y_2798_ = v_pos_2821_;
goto v___jp_2797_;
}
}
else
{
lean_dec(v_res_2822_);
v___y_2798_ = v_pos_2821_;
goto v___jp_2797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader___boxed(lean_object* v_limits_2861_, lean_object* v_a_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_2861_, v_a_2862_);
lean_dec_ref(v_limits_2861_);
return v_res_2863_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0(void){
_start:
{
uint32_t v___x_2864_; uint8_t v___x_2865_; 
v___x_2864_ = 92;
v___x_2865_ = lean_uint32_to_uint8(v___x_2864_);
return v___x_2865_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1(void){
_start:
{
uint8_t v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0);
v___x_2867_ = lean_uint8_to_nat(v___x_2866_);
return v___x_2867_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2(void){
_start:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2868_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1);
v___x_2869_ = l_Nat_reprFast(v___x_2868_);
return v___x_2869_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__3(void){
_start:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2870_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2);
v___x_2871_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_2872_ = lean_string_append(v___x_2871_, v___x_2870_);
return v___x_2872_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__4(void){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2873_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__5));
v___x_2874_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__3);
v___x_2875_ = lean_string_append(v___x_2874_, v___x_2873_);
return v___x_2875_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__5(void){
_start:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2876_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__4);
v___x_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair(lean_object* v_a_2879_){
_start:
{
lean_object* v_array_2880_; lean_object* v_idx_2881_; lean_object* v___x_2882_; uint8_t v___x_2883_; 
v_array_2880_ = lean_ctor_get(v_a_2879_, 0);
v_idx_2881_ = lean_ctor_get(v_a_2879_, 1);
v___x_2882_ = lean_byte_array_size(v_array_2880_);
v___x_2883_ = lean_nat_dec_lt(v_idx_2881_, v___x_2882_);
if (v___x_2883_ == 0)
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2884_ = lean_box(0);
v___x_2885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2885_, 0, v_a_2879_);
lean_ctor_set(v___x_2885_, 1, v___x_2884_);
return v___x_2885_;
}
else
{
uint8_t v___x_2886_; uint8_t v_got_2887_; uint8_t v___x_2888_; 
v___x_2886_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0);
v_got_2887_ = lean_byte_array_fget(v_array_2880_, v_idx_2881_);
v___x_2888_ = lean_uint8_dec_eq(v_got_2887_, v___x_2886_);
if (v___x_2888_ == 0)
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__5, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__5_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__5);
v___x_2890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2890_, 0, v_a_2879_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
return v___x_2890_;
}
else
{
lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2926_; 
lean_inc(v_idx_2881_);
lean_inc_ref(v_array_2880_);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_a_2879_);
if (v_isSharedCheck_2926_ == 0)
{
lean_object* v_unused_2927_; lean_object* v_unused_2928_; 
v_unused_2927_ = lean_ctor_get(v_a_2879_, 1);
lean_dec(v_unused_2927_);
v_unused_2928_ = lean_ctor_get(v_a_2879_, 0);
lean_dec(v_unused_2928_);
v___x_2892_ = v_a_2879_;
v_isShared_2893_ = v_isSharedCheck_2926_;
goto v_resetjp_2891_;
}
else
{
lean_dec(v_a_2879_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2926_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; uint8_t v___x_2896_; 
v___x_2894_ = lean_unsigned_to_nat(1u);
v___x_2895_ = lean_nat_add(v_idx_2881_, v___x_2894_);
lean_dec(v_idx_2881_);
v___x_2896_ = lean_nat_dec_lt(v___x_2895_, v___x_2882_);
if (v___x_2896_ == 0)
{
lean_object* v___x_2898_; 
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 1, v___x_2895_);
v___x_2898_ = v___x_2892_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_array_2880_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v___x_2895_);
v___x_2898_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2899_ = lean_box(0);
v___x_2900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2898_);
lean_ctor_set(v___x_2900_, 1, v___x_2899_);
return v___x_2900_;
}
}
else
{
uint8_t v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2905_; 
v___x_2902_ = lean_byte_array_fget(v_array_2880_, v___x_2895_);
v___x_2903_ = lean_nat_add(v___x_2895_, v___x_2894_);
lean_dec(v___x_2895_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 1, v___x_2903_);
v___x_2905_ = v___x_2892_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_array_2880_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v___x_2903_);
v___x_2905_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; uint32_t v___x_2908_; uint8_t v___y_2916_; uint32_t v___x_2917_; uint8_t v___x_2918_; 
v___x_2906_ = lean_box(v___x_2902_);
lean_inc_ref(v___x_2905_);
v___x_2907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2905_);
lean_ctor_set(v___x_2907_, 1, v___x_2906_);
v___x_2908_ = lean_uint8_to_uint32(v___x_2902_);
v___x_2917_ = 9;
v___x_2918_ = lean_uint32_dec_eq(v___x_2908_, v___x_2917_);
if (v___x_2918_ == 0)
{
uint32_t v___x_2919_; uint8_t v___x_2920_; 
v___x_2919_ = 32;
v___x_2920_ = lean_uint32_dec_eq(v___x_2908_, v___x_2919_);
if (v___x_2920_ == 0)
{
uint32_t v___x_2921_; uint8_t v___x_2922_; 
v___x_2921_ = 33;
v___x_2922_ = lean_uint32_dec_le(v___x_2921_, v___x_2908_);
if (v___x_2922_ == 0)
{
lean_dec_ref_known(v___x_2907_, 2);
goto v___jp_2909_;
}
else
{
uint32_t v___x_2923_; uint8_t v___x_2924_; 
v___x_2923_ = 126;
v___x_2924_ = lean_uint32_dec_le(v___x_2908_, v___x_2923_);
if (v___x_2924_ == 0)
{
lean_dec_ref_known(v___x_2907_, 2);
goto v___jp_2909_;
}
else
{
v___y_2916_ = v___x_2896_;
goto v___jp_2915_;
}
}
}
else
{
v___y_2916_ = v___x_2896_;
goto v___jp_2915_;
}
}
else
{
v___y_2916_ = v___x_2896_;
goto v___jp_2915_;
}
v___jp_2909_:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2910_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__6));
v___x_2911_ = l_Char_quote(v___x_2908_);
v___x_2912_ = lean_string_append(v___x_2910_, v___x_2911_);
lean_dec_ref(v___x_2911_);
v___x_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
v___x_2914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2905_);
lean_ctor_set(v___x_2914_, 1, v___x_2913_);
return v___x_2914_;
}
v___jp_2915_:
{
if (v___y_2916_ == 0)
{
lean_dec_ref_known(v___x_2907_, 2);
goto v___jp_2909_;
}
else
{
lean_dec_ref(v___x_2905_);
return v___x_2907_;
}
}
}
}
}
}
}
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3(void){
_start:
{
uint32_t v___x_2933_; uint8_t v___x_2934_; 
v___x_2933_ = 34;
v___x_2934_ = lean_uint32_to_uint8(v___x_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(lean_object* v_maxLength_2935_, lean_object* v_buf_2936_, lean_object* v_length_2937_, lean_object* v_a_2938_){
_start:
{
lean_object* v_array_2939_; lean_object* v_idx_2940_; lean_object* v___x_2941_; uint8_t v___x_2942_; 
v_array_2939_ = lean_ctor_get(v_a_2938_, 0);
v_idx_2940_ = lean_ctor_get(v_a_2938_, 1);
v___x_2941_ = lean_byte_array_size(v_array_2939_);
v___x_2942_ = lean_nat_dec_lt(v_idx_2940_, v___x_2941_);
if (v___x_2942_ == 0)
{
lean_object* v___x_2943_; lean_object* v___x_2944_; 
lean_dec(v_length_2937_);
lean_dec_ref(v_buf_2936_);
v___x_2943_ = lean_box(0);
v___x_2944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2944_, 0, v_a_2938_);
lean_ctor_set(v___x_2944_, 1, v___x_2943_);
return v___x_2944_;
}
else
{
lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_3018_; 
lean_inc(v_idx_2940_);
lean_inc_ref(v_array_2939_);
v_isSharedCheck_3018_ = !lean_is_exclusive(v_a_2938_);
if (v_isSharedCheck_3018_ == 0)
{
lean_object* v_unused_3019_; lean_object* v_unused_3020_; 
v_unused_3019_ = lean_ctor_get(v_a_2938_, 1);
lean_dec(v_unused_3019_);
v_unused_3020_ = lean_ctor_get(v_a_2938_, 0);
lean_dec(v_unused_3020_);
v___x_2946_ = v_a_2938_;
v_isShared_2947_ = v_isSharedCheck_3018_;
goto v_resetjp_2945_;
}
else
{
lean_dec(v_a_2938_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_3018_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
uint8_t v_c_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v_it_x27_2952_; 
v_c_2948_ = lean_byte_array_fget(v_array_2939_, v_idx_2940_);
v___x_2949_ = lean_unsigned_to_nat(1u);
v___x_2950_ = lean_nat_add(v_idx_2940_, v___x_2949_);
lean_dec(v_idx_2940_);
lean_inc(v___x_2950_);
lean_inc_ref(v_array_2939_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 1, v___x_2950_);
v_it_x27_2952_ = v___x_2946_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_array_2939_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v___x_2950_);
v_it_x27_2952_ = v_reuseFailAlloc_3017_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
uint8_t v___y_2961_; uint8_t v___x_2968_; uint8_t v___x_2969_; 
v___x_2968_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3);
v___x_2969_ = lean_uint8_dec_eq(v_c_2948_, v___x_2968_);
if (v___x_2969_ == 0)
{
uint8_t v___x_2970_; uint8_t v___x_2971_; 
v___x_2970_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0);
v___x_2971_ = lean_uint8_dec_eq(v_c_2948_, v___x_2970_);
if (v___x_2971_ == 0)
{
uint32_t v___x_2972_; uint32_t v___x_2978_; uint8_t v___x_2979_; 
lean_dec(v___x_2950_);
lean_dec_ref(v_array_2939_);
v___x_2972_ = lean_uint8_to_uint32(v_c_2948_);
v___x_2978_ = 9;
v___x_2979_ = lean_uint32_dec_eq(v___x_2972_, v___x_2978_);
if (v___x_2979_ == 0)
{
uint32_t v___x_2980_; uint8_t v___x_2981_; 
v___x_2980_ = 32;
v___x_2981_ = lean_uint32_dec_eq(v___x_2972_, v___x_2980_);
if (v___x_2981_ == 0)
{
uint32_t v___x_2982_; uint8_t v___x_2983_; 
v___x_2982_ = 33;
v___x_2983_ = lean_uint32_dec_eq(v___x_2972_, v___x_2982_);
if (v___x_2983_ == 0)
{
uint32_t v___x_2984_; uint8_t v___x_2985_; 
v___x_2984_ = 35;
v___x_2985_ = lean_uint32_dec_le(v___x_2984_, v___x_2972_);
if (v___x_2985_ == 0)
{
goto v___jp_2973_;
}
else
{
uint32_t v___x_2986_; uint8_t v___x_2987_; 
v___x_2986_ = 91;
v___x_2987_ = lean_uint32_dec_le(v___x_2972_, v___x_2986_);
if (v___x_2987_ == 0)
{
goto v___jp_2973_;
}
else
{
goto v___jp_2953_;
}
}
}
else
{
v___y_2961_ = v___x_2942_;
goto v___jp_2960_;
}
}
else
{
v___y_2961_ = v___x_2942_;
goto v___jp_2960_;
}
}
else
{
v___y_2961_ = v___x_2942_;
goto v___jp_2960_;
}
v___jp_2973_:
{
uint32_t v___x_2974_; uint8_t v___x_2975_; 
v___x_2974_ = 93;
v___x_2975_ = lean_uint32_dec_le(v___x_2974_, v___x_2972_);
if (v___x_2975_ == 0)
{
v___y_2961_ = v___x_2971_;
goto v___jp_2960_;
}
else
{
uint32_t v___x_2976_; uint8_t v___x_2977_; 
v___x_2976_ = 126;
v___x_2977_ = lean_uint32_dec_le(v___x_2972_, v___x_2976_);
if (v___x_2977_ == 0)
{
v___y_2961_ = v___x_2971_;
goto v___jp_2960_;
}
else
{
v___y_2961_ = v___x_2942_;
goto v___jp_2960_;
}
}
}
}
else
{
uint8_t v___x_2988_; 
v___x_2988_ = lean_nat_dec_lt(v___x_2950_, v___x_2941_);
if (v___x_2988_ == 0)
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
lean_dec(v___x_2950_);
lean_dec_ref(v_array_2939_);
lean_dec(v_length_2937_);
lean_dec_ref(v_buf_2936_);
v___x_2989_ = lean_box(0);
v___x_2990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2990_, 0, v_it_x27_2952_);
lean_ctor_set(v___x_2990_, 1, v___x_2989_);
return v___x_2990_;
}
else
{
uint8_t v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; uint32_t v___x_2994_; uint8_t v___y_2996_; uint32_t v___x_3008_; uint8_t v___x_3009_; 
lean_dec_ref(v_it_x27_2952_);
v___x_2991_ = lean_byte_array_fget(v_array_2939_, v___x_2950_);
v___x_2992_ = lean_nat_add(v___x_2950_, v___x_2949_);
lean_dec(v___x_2950_);
v___x_2993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2993_, 0, v_array_2939_);
lean_ctor_set(v___x_2993_, 1, v___x_2992_);
v___x_2994_ = lean_uint8_to_uint32(v___x_2991_);
v___x_3008_ = 9;
v___x_3009_ = lean_uint32_dec_eq(v___x_2994_, v___x_3008_);
if (v___x_3009_ == 0)
{
uint32_t v___x_3010_; uint8_t v___x_3011_; 
v___x_3010_ = 32;
v___x_3011_ = lean_uint32_dec_eq(v___x_2994_, v___x_3010_);
if (v___x_3011_ == 0)
{
uint32_t v___x_3012_; uint8_t v___x_3013_; 
v___x_3012_ = 33;
v___x_3013_ = lean_uint32_dec_le(v___x_3012_, v___x_2994_);
if (v___x_3013_ == 0)
{
v___y_2996_ = v___x_2969_;
goto v___jp_2995_;
}
else
{
uint32_t v___x_3014_; uint8_t v___x_3015_; 
v___x_3014_ = 126;
v___x_3015_ = lean_uint32_dec_le(v___x_2994_, v___x_3014_);
if (v___x_3015_ == 0)
{
v___y_2996_ = v___x_2969_;
goto v___jp_2995_;
}
else
{
v___y_2996_ = v___x_2988_;
goto v___jp_2995_;
}
}
}
else
{
v___y_2996_ = v___x_2988_;
goto v___jp_2995_;
}
}
else
{
v___y_2996_ = v___x_2988_;
goto v___jp_2995_;
}
v___jp_2995_:
{
if (v___y_2996_ == 0)
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
lean_dec(v_length_2937_);
lean_dec_ref(v_buf_2936_);
v___x_2997_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__6));
v___x_2998_ = l_Char_quote(v___x_2994_);
v___x_2999_ = lean_string_append(v___x_2997_, v___x_2998_);
lean_dec_ref(v___x_2998_);
v___x_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2999_);
v___x_3001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3001_, 0, v___x_2993_);
lean_ctor_set(v___x_3001_, 1, v___x_3000_);
return v___x_3001_;
}
else
{
lean_object* v___x_3002_; uint8_t v___x_3003_; 
v___x_3002_ = lean_nat_add(v_length_2937_, v___x_2949_);
lean_dec(v_length_2937_);
v___x_3003_ = lean_nat_dec_lt(v_maxLength_2935_, v___x_3002_);
if (v___x_3003_ == 0)
{
lean_object* v___x_3004_; 
v___x_3004_ = lean_byte_array_push(v_buf_2936_, v___x_2991_);
v_buf_2936_ = v___x_3004_;
v_length_2937_ = v___x_3002_;
v_a_2938_ = v___x_2993_;
goto _start;
}
else
{
lean_object* v___x_3006_; lean_object* v___x_3007_; 
lean_dec(v___x_3002_);
lean_dec_ref(v_buf_2936_);
v___x_3006_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_3007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3007_, 0, v___x_2993_);
lean_ctor_set(v___x_3007_, 1, v___x_3006_);
return v___x_3007_;
}
}
}
}
}
}
else
{
lean_object* v___x_3016_; 
lean_dec(v___x_2950_);
lean_dec_ref(v_array_2939_);
lean_dec(v_length_2937_);
v___x_3016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3016_, 0, v_it_x27_2952_);
lean_ctor_set(v___x_3016_, 1, v_buf_2936_);
return v___x_3016_;
}
v___jp_2953_:
{
lean_object* v___x_2954_; uint8_t v___x_2955_; 
v___x_2954_ = lean_nat_add(v_length_2937_, v___x_2949_);
lean_dec(v_length_2937_);
v___x_2955_ = lean_nat_dec_lt(v_maxLength_2935_, v___x_2954_);
if (v___x_2955_ == 0)
{
lean_object* v___x_2956_; 
v___x_2956_ = lean_byte_array_push(v_buf_2936_, v_c_2948_);
v_buf_2936_ = v___x_2956_;
v_length_2937_ = v___x_2954_;
v_a_2938_ = v_it_x27_2952_;
goto _start;
}
else
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
lean_dec(v___x_2954_);
lean_dec_ref(v_buf_2936_);
v___x_2958_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_2959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2959_, 0, v_it_x27_2952_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
return v___x_2959_;
}
}
v___jp_2960_:
{
if (v___y_2961_ == 0)
{
lean_object* v___x_2962_; uint32_t v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
lean_dec(v_length_2937_);
lean_dec_ref(v_buf_2936_);
v___x_2962_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2));
v___x_2963_ = lean_uint8_to_uint32(v_c_2948_);
v___x_2964_ = l_Char_quote(v___x_2963_);
v___x_2965_ = lean_string_append(v___x_2962_, v___x_2964_);
lean_dec_ref(v___x_2964_);
v___x_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2965_);
v___x_2967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2967_, 0, v_it_x27_2952_);
lean_ctor_set(v___x_2967_, 1, v___x_2966_);
return v___x_2967_;
}
else
{
goto v___jp_2953_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___boxed(lean_object* v_maxLength_3021_, lean_object* v_buf_3022_, lean_object* v_length_3023_, lean_object* v_a_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_3021_, v_buf_3022_, v_length_3023_, v_a_3024_);
lean_dec(v_maxLength_3021_);
return v_res_3025_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__0(void){
_start:
{
uint8_t v___x_3026_; lean_object* v___x_3027_; 
v___x_3026_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3);
v___x_3027_ = lean_uint8_to_nat(v___x_3026_);
return v___x_3027_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1(void){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__0);
v___x_3029_ = l_Nat_reprFast(v___x_3028_);
return v___x_3029_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__2(void){
_start:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3030_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1);
v___x_3031_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_3032_ = lean_string_append(v___x_3031_, v___x_3030_);
return v___x_3032_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__3(void){
_start:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3033_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__5));
v___x_3034_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__2);
v___x_3035_ = lean_string_append(v___x_3034_, v___x_3033_);
return v___x_3035_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__4(void){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3036_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__3);
v___x_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(lean_object* v_maxLength_3038_, lean_object* v_a_3039_){
_start:
{
lean_object* v_array_3040_; lean_object* v_idx_3041_; lean_object* v___x_3042_; uint8_t v___x_3043_; 
v_array_3040_ = lean_ctor_get(v_a_3039_, 0);
v_idx_3041_ = lean_ctor_get(v_a_3039_, 1);
v___x_3042_ = lean_byte_array_size(v_array_3040_);
v___x_3043_ = lean_nat_dec_lt(v_idx_3041_, v___x_3042_);
if (v___x_3043_ == 0)
{
lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3044_ = lean_box(0);
v___x_3045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3045_, 0, v_a_3039_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
return v___x_3045_;
}
else
{
uint8_t v___x_3046_; uint8_t v_got_3047_; uint8_t v___x_3048_; 
v___x_3046_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3);
v_got_3047_ = lean_byte_array_fget(v_array_3040_, v_idx_3041_);
v___x_3048_ = lean_uint8_dec_eq(v_got_3047_, v___x_3046_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3049_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__4);
v___x_3050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3050_, 0, v_a_3039_);
lean_ctor_set(v___x_3050_, 1, v___x_3049_);
return v___x_3050_;
}
else
{
lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3079_; 
lean_inc(v_idx_3041_);
lean_inc_ref(v_array_3040_);
v_isSharedCheck_3079_ = !lean_is_exclusive(v_a_3039_);
if (v_isSharedCheck_3079_ == 0)
{
lean_object* v_unused_3080_; lean_object* v_unused_3081_; 
v_unused_3080_ = lean_ctor_get(v_a_3039_, 1);
lean_dec(v_unused_3080_);
v_unused_3081_ = lean_ctor_get(v_a_3039_, 0);
lean_dec(v_unused_3081_);
v___x_3052_ = v_a_3039_;
v_isShared_3053_ = v_isSharedCheck_3079_;
goto v_resetjp_3051_;
}
else
{
lean_dec(v_a_3039_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3079_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3057_; 
v___x_3054_ = lean_unsigned_to_nat(1u);
v___x_3055_ = lean_nat_add(v_idx_3041_, v___x_3054_);
lean_dec(v_idx_3041_);
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 1, v___x_3055_);
v___x_3057_ = v___x_3052_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_array_3040_);
lean_ctor_set(v_reuseFailAlloc_3078_, 1, v___x_3055_);
v___x_3057_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3058_ = l_ByteArray_empty;
v___x_3059_ = lean_unsigned_to_nat(0u);
v___x_3060_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_3038_, v___x_3058_, v___x_3059_, v___x_3057_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_pos_3061_; lean_object* v_res_3062_; uint8_t v___x_3063_; 
v_pos_3061_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_pos_3061_);
v_res_3062_ = lean_ctor_get(v___x_3060_, 1);
lean_inc(v_res_3062_);
lean_dec_ref_known(v___x_3060_, 2);
v___x_3063_ = lean_string_validate_utf8(v_res_3062_);
if (v___x_3063_ == 0)
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
lean_dec(v_res_3062_);
v___x_3064_ = lean_box(0);
v___x_3065_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_3064_, v_pos_3061_);
return v___x_3065_;
}
else
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3066_ = lean_string_from_utf8_unchecked(v_res_3062_);
v___x_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3066_);
v___x_3068_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_3067_, v_pos_3061_);
lean_dec_ref_known(v___x_3067_, 1);
return v___x_3068_;
}
}
else
{
lean_object* v_pos_3069_; lean_object* v_err_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
v_pos_3069_ = lean_ctor_get(v___x_3060_, 0);
v_err_3070_ = lean_ctor_get(v___x_3060_, 1);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___x_3060_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_err_3070_);
lean_inc(v_pos_3069_);
lean_dec(v___x_3060_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_pos_3069_);
lean_ctor_set(v_reuseFailAlloc_3076_, 1, v_err_3070_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___boxed(lean_object* v_maxLength_3082_, lean_object* v_a_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxLength_3082_, v_a_3083_);
lean_dec(v_maxLength_3082_);
return v_res_3084_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__0(uint8_t v___y_3085_){
_start:
{
uint32_t v___x_3086_; uint32_t v___x_3087_; uint8_t v___x_3088_; 
v___x_3086_ = lean_uint8_to_uint32(v___y_3085_);
v___x_3087_ = 32;
v___x_3088_ = lean_uint32_dec_eq(v___x_3086_, v___x_3087_);
if (v___x_3088_ == 0)
{
uint32_t v___x_3089_; uint8_t v___x_3090_; 
v___x_3089_ = 9;
v___x_3090_ = lean_uint32_dec_eq(v___x_3086_, v___x_3089_);
return v___x_3090_;
}
else
{
return v___x_3088_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__0___boxed(lean_object* v___y_3091_){
_start:
{
uint8_t v___y_10054__boxed_3092_; uint8_t v_res_3093_; lean_object* v_r_3094_; 
v___y_10054__boxed_3092_ = lean_unbox(v___y_3091_);
v_res_3093_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__0(v___y_10054__boxed_3092_);
v_r_3094_ = lean_box(v_res_3093_);
return v_r_3094_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(lean_object* v___f_3095_, lean_object* v_maxSpaceSequence_3096_, lean_object* v_x_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v_pos_3100_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v_snd_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3136_; 
v___x_3103_ = lean_unsigned_to_nat(0u);
v___x_3104_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3095_, v_maxSpaceSequence_3096_, v___x_3103_, v___y_3098_);
v_snd_3105_ = lean_ctor_get(v___x_3104_, 1);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3136_ == 0)
{
lean_object* v_unused_3137_; 
v_unused_3137_ = lean_ctor_get(v___x_3104_, 0);
lean_dec(v_unused_3137_);
v___x_3107_ = v___x_3104_;
v_isShared_3108_ = v_isSharedCheck_3136_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_snd_3105_);
lean_dec(v___x_3104_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3136_;
goto v_resetjp_3106_;
}
v___jp_3099_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3101_ = lean_box(0);
v___x_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3102_, 0, v_pos_3100_);
lean_ctor_set(v___x_3102_, 1, v___x_3101_);
return v___x_3102_;
}
v_resetjp_3106_:
{
lean_object* v_fst_3109_; lean_object* v_snd_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3135_; 
v_fst_3109_ = lean_ctor_get(v_snd_3105_, 0);
v_snd_3110_ = lean_ctor_get(v_snd_3105_, 1);
v_isSharedCheck_3135_ = !lean_is_exclusive(v_snd_3105_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3112_ = v_snd_3105_;
v_isShared_3113_ = v_isSharedCheck_3135_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_snd_3110_);
lean_inc(v_fst_3109_);
lean_dec(v_snd_3105_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3135_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
uint8_t v___y_3115_; uint8_t v___x_3120_; 
v___x_3120_ = lean_unbox(v_snd_3110_);
lean_dec(v_snd_3110_);
if (v___x_3120_ == 0)
{
lean_object* v_array_3121_; lean_object* v_idx_3122_; lean_object* v___x_3123_; uint8_t v___x_3124_; 
lean_del_object(v___x_3107_);
v_array_3121_ = lean_ctor_get(v_fst_3109_, 0);
v_idx_3122_ = lean_ctor_get(v_fst_3109_, 1);
v___x_3123_ = lean_byte_array_size(v_array_3121_);
v___x_3124_ = lean_nat_dec_lt(v_idx_3122_, v___x_3123_);
if (v___x_3124_ == 0)
{
lean_del_object(v___x_3112_);
v_pos_3100_ = v_fst_3109_;
goto v___jp_3099_;
}
else
{
uint8_t v___x_3125_; uint32_t v___x_3126_; uint32_t v___x_3127_; uint8_t v___x_3128_; 
v___x_3125_ = lean_byte_array_fget(v_array_3121_, v_idx_3122_);
v___x_3126_ = lean_uint8_to_uint32(v___x_3125_);
v___x_3127_ = 32;
v___x_3128_ = lean_uint32_dec_eq(v___x_3126_, v___x_3127_);
if (v___x_3128_ == 0)
{
uint32_t v___x_3129_; uint8_t v___x_3130_; 
v___x_3129_ = 9;
v___x_3130_ = lean_uint32_dec_eq(v___x_3126_, v___x_3129_);
if (v___x_3130_ == 0)
{
lean_del_object(v___x_3112_);
v_pos_3100_ = v_fst_3109_;
goto v___jp_3099_;
}
else
{
v___y_3115_ = v___x_3124_;
goto v___jp_3114_;
}
}
else
{
v___y_3115_ = v___x_3124_;
goto v___jp_3114_;
}
}
}
else
{
lean_object* v___x_3131_; lean_object* v___x_3133_; 
lean_del_object(v___x_3112_);
v___x_3131_ = lean_box(0);
if (v_isShared_3108_ == 0)
{
lean_ctor_set_tag(v___x_3107_, 1);
lean_ctor_set(v___x_3107_, 1, v___x_3131_);
lean_ctor_set(v___x_3107_, 0, v_fst_3109_);
v___x_3133_ = v___x_3107_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_fst_3109_);
lean_ctor_set(v_reuseFailAlloc_3134_, 1, v___x_3131_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
v___jp_3114_:
{
if (v___y_3115_ == 0)
{
lean_del_object(v___x_3112_);
v_pos_3100_ = v_fst_3109_;
goto v___jp_3099_;
}
else
{
lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3116_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2));
if (v_isShared_3113_ == 0)
{
lean_ctor_set_tag(v___x_3112_, 1);
lean_ctor_set(v___x_3112_, 1, v___x_3116_);
v___x_3118_ = v___x_3112_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_fst_3109_);
lean_ctor_set(v_reuseFailAlloc_3119_, 1, v___x_3116_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2___boxed(lean_object* v___f_3138_, lean_object* v_maxSpaceSequence_3139_, lean_object* v_x_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_3138_, v_maxSpaceSequence_3139_, v_x_3140_, v___y_3141_);
lean_dec(v_maxSpaceSequence_3139_);
return v_res_3142_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__1(uint8_t v___x_3143_, uint8_t v___y_3144_){
_start:
{
uint32_t v___x_3145_; uint32_t v___x_3146_; uint8_t v___x_3147_; 
v___x_3145_ = lean_uint8_to_uint32(v___y_3144_);
v___x_3146_ = 32;
v___x_3147_ = lean_uint32_dec_eq(v___x_3145_, v___x_3146_);
if (v___x_3147_ == 0)
{
uint32_t v___x_3148_; uint8_t v___x_3149_; 
v___x_3148_ = 9;
v___x_3149_ = lean_uint32_dec_eq(v___x_3145_, v___x_3148_);
if (v___x_3149_ == 0)
{
return v___x_3149_;
}
else
{
return v___x_3143_;
}
}
else
{
return v___x_3143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__1___boxed(lean_object* v___x_3150_, lean_object* v___y_3151_){
_start:
{
uint8_t v___x_10158__boxed_3152_; uint8_t v___y_10159__boxed_3153_; uint8_t v_res_3154_; lean_object* v_r_3155_; 
v___x_10158__boxed_3152_ = lean_unbox(v___x_3150_);
v___y_10159__boxed_3153_ = lean_unbox(v___y_3151_);
v_res_3154_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__1(v___x_10158__boxed_3152_, v___y_10159__boxed_3153_);
v_r_3155_ = lean_box(v_res_3154_);
return v_r_3155_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__3(uint8_t v___x_3156_, uint8_t v_c_3157_){
_start:
{
uint32_t v___x_3158_; uint8_t v___y_3165_; uint32_t v___x_3170_; uint8_t v___x_3171_; 
v___x_3158_ = lean_uint8_to_uint32(v_c_3157_);
v___x_3170_ = 33;
v___x_3171_ = lean_uint32_dec_eq(v___x_3158_, v___x_3170_);
if (v___x_3171_ == 0)
{
uint32_t v___x_3172_; uint8_t v___x_3173_; 
v___x_3172_ = 35;
v___x_3173_ = lean_uint32_dec_eq(v___x_3158_, v___x_3172_);
if (v___x_3173_ == 0)
{
uint32_t v___x_3174_; uint8_t v___x_3175_; 
v___x_3174_ = 36;
v___x_3175_ = lean_uint32_dec_eq(v___x_3158_, v___x_3174_);
if (v___x_3175_ == 0)
{
uint32_t v___x_3176_; uint8_t v___x_3177_; 
v___x_3176_ = 37;
v___x_3177_ = lean_uint32_dec_eq(v___x_3158_, v___x_3176_);
if (v___x_3177_ == 0)
{
uint32_t v___x_3178_; uint8_t v___x_3179_; 
v___x_3178_ = 38;
v___x_3179_ = lean_uint32_dec_eq(v___x_3158_, v___x_3178_);
if (v___x_3179_ == 0)
{
uint32_t v___x_3180_; uint8_t v___x_3181_; 
v___x_3180_ = 39;
v___x_3181_ = lean_uint32_dec_eq(v___x_3158_, v___x_3180_);
if (v___x_3181_ == 0)
{
uint32_t v___x_3182_; uint8_t v___x_3183_; 
v___x_3182_ = 42;
v___x_3183_ = lean_uint32_dec_eq(v___x_3158_, v___x_3182_);
if (v___x_3183_ == 0)
{
uint32_t v___x_3184_; uint8_t v___x_3185_; 
v___x_3184_ = 43;
v___x_3185_ = lean_uint32_dec_eq(v___x_3158_, v___x_3184_);
if (v___x_3185_ == 0)
{
uint32_t v___x_3186_; uint8_t v___x_3187_; 
v___x_3186_ = 45;
v___x_3187_ = lean_uint32_dec_eq(v___x_3158_, v___x_3186_);
if (v___x_3187_ == 0)
{
uint32_t v___x_3188_; uint8_t v___x_3189_; 
v___x_3188_ = 46;
v___x_3189_ = lean_uint32_dec_eq(v___x_3158_, v___x_3188_);
if (v___x_3189_ == 0)
{
uint32_t v___x_3190_; uint8_t v___x_3191_; 
v___x_3190_ = 94;
v___x_3191_ = lean_uint32_dec_eq(v___x_3158_, v___x_3190_);
if (v___x_3191_ == 0)
{
uint32_t v___x_3192_; uint8_t v___x_3193_; 
v___x_3192_ = 95;
v___x_3193_ = lean_uint32_dec_eq(v___x_3158_, v___x_3192_);
if (v___x_3193_ == 0)
{
uint32_t v___x_3194_; uint8_t v___x_3195_; 
v___x_3194_ = 96;
v___x_3195_ = lean_uint32_dec_eq(v___x_3158_, v___x_3194_);
if (v___x_3195_ == 0)
{
uint32_t v___x_3196_; uint8_t v___x_3197_; 
v___x_3196_ = 124;
v___x_3197_ = lean_uint32_dec_eq(v___x_3158_, v___x_3196_);
if (v___x_3197_ == 0)
{
uint32_t v___x_3198_; uint8_t v___x_3199_; 
v___x_3198_ = 126;
v___x_3199_ = lean_uint32_dec_eq(v___x_3158_, v___x_3198_);
if (v___x_3199_ == 0)
{
uint32_t v___x_3200_; uint8_t v___x_3201_; 
v___x_3200_ = 48;
v___x_3201_ = lean_uint32_dec_le(v___x_3200_, v___x_3158_);
if (v___x_3201_ == 0)
{
v___y_3165_ = v___x_3201_;
goto v___jp_3164_;
}
else
{
uint32_t v___x_3202_; uint8_t v___x_3203_; 
v___x_3202_ = 57;
v___x_3203_ = lean_uint32_dec_le(v___x_3158_, v___x_3202_);
v___y_3165_ = v___x_3203_;
goto v___jp_3164_;
}
}
else
{
return v___x_3156_;
}
}
else
{
return v___x_3156_;
}
}
else
{
return v___x_3156_;
}
}
else
{
return v___x_3156_;
}
}
else
{
return v___x_3156_;
}
}
else
{
return v___x_3156_;
}
}
else
{
return v___x_3156_;
}
}
else
{
return v___x_3156_;
}
}
else
{
return v___x_3156_;
}
}
else
{
return v___x_3156_;
}
}
else
{
return v___x_3156_;
}
}
else
{
return v___x_3156_;
}
}
else
{
return v___x_3156_;
}
}
else
{
return v___x_3156_;
}
}
else
{
return v___x_3156_;
}
v___jp_3159_:
{
uint32_t v___x_3160_; uint8_t v___x_3161_; 
v___x_3160_ = 97;
v___x_3161_ = lean_uint32_dec_le(v___x_3160_, v___x_3158_);
if (v___x_3161_ == 0)
{
return v___x_3161_;
}
else
{
uint32_t v___x_3162_; uint8_t v___x_3163_; 
v___x_3162_ = 122;
v___x_3163_ = lean_uint32_dec_le(v___x_3158_, v___x_3162_);
return v___x_3163_;
}
}
v___jp_3164_:
{
if (v___y_3165_ == 0)
{
uint32_t v___x_3166_; uint8_t v___x_3167_; 
v___x_3166_ = 65;
v___x_3167_ = lean_uint32_dec_le(v___x_3166_, v___x_3158_);
if (v___x_3167_ == 0)
{
goto v___jp_3159_;
}
else
{
uint32_t v___x_3168_; uint8_t v___x_3169_; 
v___x_3168_ = 90;
v___x_3169_ = lean_uint32_dec_le(v___x_3158_, v___x_3168_);
if (v___x_3169_ == 0)
{
goto v___jp_3159_;
}
else
{
return v___x_3156_;
}
}
}
else
{
return v___y_3165_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__3___boxed(lean_object* v___x_3204_, lean_object* v_c_3205_){
_start:
{
uint8_t v___x_10174__boxed_3206_; uint8_t v_c_boxed_3207_; uint8_t v_res_3208_; lean_object* v_r_3209_; 
v___x_10174__boxed_3206_ = lean_unbox(v___x_3204_);
v_c_boxed_3207_ = lean_unbox(v_c_3205_);
v_res_3208_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__3(v___x_10174__boxed_3206_, v_c_boxed_3207_);
v_r_3209_ = lean_box(v_res_3208_);
return v_r_3209_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3(void){
_start:
{
uint32_t v___x_3214_; uint8_t v___x_3215_; 
v___x_3214_ = 61;
v___x_3215_ = lean_uint32_to_uint8(v___x_3214_);
return v___x_3215_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4(void){
_start:
{
uint8_t v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3);
v___x_3217_ = lean_uint8_to_nat(v___x_3216_);
return v___x_3217_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5(void){
_start:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3218_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4);
v___x_3219_ = l_Nat_reprFast(v___x_3218_);
return v___x_3219_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6(void){
_start:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3220_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5);
v___x_3221_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_3222_ = lean_string_append(v___x_3221_, v___x_3220_);
return v___x_3222_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7(void){
_start:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3223_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__5));
v___x_3224_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6);
v___x_3225_ = lean_string_append(v___x_3224_, v___x_3223_);
return v___x_3225_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__8(void){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7);
v___x_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3226_);
return v___x_3227_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__11(void){
_start:
{
uint32_t v___x_3231_; uint8_t v___x_3232_; 
v___x_3231_ = 59;
v___x_3232_ = lean_uint32_to_uint8(v___x_3231_);
return v___x_3232_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__12(void){
_start:
{
uint8_t v___x_3233_; lean_object* v___x_3234_; 
v___x_3233_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__11, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__11_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__11);
v___x_3234_ = lean_uint8_to_nat(v___x_3233_);
return v___x_3234_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__13(void){
_start:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3235_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__12, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__12_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__12);
v___x_3236_ = l_Nat_reprFast(v___x_3235_);
return v___x_3236_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__14(void){
_start:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3237_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__13, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__13_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__13);
v___x_3238_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_3239_ = lean_string_append(v___x_3238_, v___x_3237_);
return v___x_3239_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__15(void){
_start:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3240_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__5));
v___x_3241_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__14, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__14_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__14);
v___x_3242_ = lean_string_append(v___x_3241_, v___x_3240_);
return v___x_3242_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__16(void){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__15, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__15_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__15);
v___x_3244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3243_);
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(lean_object* v_limits_3245_, lean_object* v_a_3246_){
_start:
{
lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3275_; lean_object* v_pos_3276_; lean_object* v_res_3277_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v_lower_3283_; lean_object* v_upper_3284_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3300_; lean_object* v_pos_3301_; lean_object* v_maxSpaceSequence_3305_; lean_object* v_maxChunkExtNameLength_3306_; lean_object* v_maxChunkExtValueLength_3307_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v_pos_3311_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; uint8_t v___y_3348_; lean_object* v___f_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v_snd_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3632_; 
v_maxSpaceSequence_3305_ = lean_ctor_get(v_limits_3245_, 8);
v_maxChunkExtNameLength_3306_ = lean_ctor_get(v_limits_3245_, 11);
v_maxChunkExtValueLength_3307_ = lean_ctor_get(v_limits_3245_, 12);
v___f_3351_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2));
v___x_3352_ = lean_unsigned_to_nat(0u);
v___x_3353_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3351_, v_maxSpaceSequence_3305_, v___x_3352_, v_a_3246_);
v_snd_3354_ = lean_ctor_get(v___x_3353_, 1);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3632_ == 0)
{
lean_object* v_unused_3633_; 
v_unused_3633_ = lean_ctor_get(v___x_3353_, 0);
lean_dec(v_unused_3633_);
v___x_3356_ = v___x_3353_;
v_isShared_3357_ = v_isSharedCheck_3632_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_snd_3354_);
lean_dec(v___x_3353_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3632_;
goto v_resetjp_3355_;
}
v___jp_3247_:
{
if (lean_obj_tag(v___y_3249_) == 0)
{
lean_object* v_pos_3250_; lean_object* v_res_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3264_; 
v_pos_3250_ = lean_ctor_get(v___y_3249_, 0);
v_res_3251_ = lean_ctor_get(v___y_3249_, 1);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___y_3249_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3253_ = v___y_3249_;
v_isShared_3254_ = v_isSharedCheck_3264_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_res_3251_);
lean_inc(v_pos_3250_);
lean_dec(v___y_3249_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3264_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3255_; 
v___x_3255_ = l_Std_Http_Chunk_ExtensionValue_ofString_x3f(v_res_3251_);
if (lean_obj_tag(v___x_3255_) == 1)
{
lean_object* v___x_3256_; lean_object* v___x_3258_; 
v___x_3256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___y_3248_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 1, v___x_3256_);
v___x_3258_ = v___x_3253_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_pos_3250_);
lean_ctor_set(v_reuseFailAlloc_3259_, 1, v___x_3256_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
else
{
lean_object* v___x_3260_; lean_object* v___x_3262_; 
lean_dec(v___x_3255_);
lean_dec_ref(v___y_3248_);
v___x_3260_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1));
if (v_isShared_3254_ == 0)
{
lean_ctor_set_tag(v___x_3253_, 1);
lean_ctor_set(v___x_3253_, 1, v___x_3260_);
v___x_3262_ = v___x_3253_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_pos_3250_);
lean_ctor_set(v_reuseFailAlloc_3263_, 1, v___x_3260_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
else
{
lean_object* v_pos_3265_; lean_object* v_err_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
lean_dec_ref(v___y_3248_);
v_pos_3265_ = lean_ctor_get(v___y_3249_, 0);
v_err_3266_ = lean_ctor_get(v___y_3249_, 1);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___y_3249_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3268_ = v___y_3249_;
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_err_3266_);
lean_inc(v_pos_3265_);
lean_dec(v___y_3249_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3271_; 
if (v_isShared_3269_ == 0)
{
v___x_3271_ = v___x_3268_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_pos_3265_);
lean_ctor_set(v_reuseFailAlloc_3272_, 1, v_err_3266_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
}
v___jp_3274_:
{
lean_object* v___x_3278_; 
v___x_3278_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_3277_, v_pos_3276_);
lean_dec(v_res_3277_);
v___y_3248_ = v___y_3275_;
v___y_3249_ = v___x_3278_;
goto v___jp_3247_;
}
v___jp_3279_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; uint8_t v___x_3287_; 
v___x_3285_ = l_ByteArray_toByteSlice(v___y_3280_, v_lower_3283_, v_upper_3284_);
v___x_3286_ = l_ByteSlice_toByteArray(v___x_3285_);
v___x_3287_ = lean_string_validate_utf8(v___x_3286_);
if (v___x_3287_ == 0)
{
lean_object* v___x_3288_; 
lean_dec_ref(v___x_3286_);
v___x_3288_ = lean_box(0);
v___y_3275_ = v___y_3282_;
v_pos_3276_ = v___y_3281_;
v_res_3277_ = v___x_3288_;
goto v___jp_3274_;
}
else
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = lean_string_from_utf8_unchecked(v___x_3286_);
v___x_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3289_);
v___y_3275_ = v___y_3282_;
v_pos_3276_ = v___y_3281_;
v_res_3277_ = v___x_3290_;
goto v___jp_3274_;
}
}
v___jp_3291_:
{
uint8_t v___x_3298_; 
v___x_3298_ = lean_nat_dec_le(v___y_3293_, v___y_3292_);
if (v___x_3298_ == 0)
{
lean_dec(v___y_3293_);
v___y_3280_ = v___y_3294_;
v___y_3281_ = v___y_3295_;
v___y_3282_ = v___y_3296_;
v_lower_3283_ = v___y_3297_;
v_upper_3284_ = v___y_3292_;
goto v___jp_3279_;
}
else
{
lean_dec(v___y_3292_);
v___y_3280_ = v___y_3294_;
v___y_3281_ = v___y_3295_;
v___y_3282_ = v___y_3296_;
v_lower_3283_ = v___y_3297_;
v_upper_3284_ = v___y_3293_;
goto v___jp_3279_;
}
}
v___jp_3299_:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3302_ = lean_box(0);
v___x_3303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___y_3300_);
lean_ctor_set(v___x_3303_, 1, v___x_3302_);
v___x_3304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3304_, 0, v_pos_3301_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
return v___x_3304_;
}
v___jp_3308_:
{
lean_object* v___x_3312_; 
lean_inc_ref(v_pos_3311_);
v___x_3312_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxChunkExtValueLength_3307_, v_pos_3311_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_dec_ref(v_pos_3311_);
lean_dec_ref(v___y_3309_);
v___y_3248_ = v___y_3310_;
v___y_3249_ = v___x_3312_;
goto v___jp_3247_;
}
else
{
lean_object* v_pos_3313_; lean_object* v_idx_3314_; lean_object* v_array_3315_; lean_object* v_idx_3316_; uint8_t v___x_3317_; 
v_pos_3313_ = lean_ctor_get(v___x_3312_, 0);
lean_inc(v_pos_3313_);
v_idx_3314_ = lean_ctor_get(v_pos_3311_, 1);
lean_inc(v_idx_3314_);
lean_dec_ref(v_pos_3311_);
v_array_3315_ = lean_ctor_get(v_pos_3313_, 0);
v_idx_3316_ = lean_ctor_get(v_pos_3313_, 1);
v___x_3317_ = lean_nat_dec_eq(v_idx_3314_, v_idx_3316_);
lean_dec(v_idx_3314_);
if (v___x_3317_ == 0)
{
lean_dec(v_pos_3313_);
lean_dec_ref(v___y_3309_);
v___y_3248_ = v___y_3310_;
v___y_3249_ = v___x_3312_;
goto v___jp_3247_;
}
else
{
lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3341_; 
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3312_);
if (v_isSharedCheck_3341_ == 0)
{
lean_object* v_unused_3342_; lean_object* v_unused_3343_; 
v_unused_3342_ = lean_ctor_get(v___x_3312_, 1);
lean_dec(v_unused_3342_);
v_unused_3343_ = lean_ctor_get(v___x_3312_, 0);
lean_dec(v_unused_3343_);
v___x_3319_ = v___x_3312_;
v_isShared_3320_ = v_isSharedCheck_3341_;
goto v_resetjp_3318_;
}
else
{
lean_dec(v___x_3312_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3341_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v_snd_3323_; lean_object* v_snd_3324_; uint8_t v___x_3325_; 
v___x_3321_ = lean_unsigned_to_nat(0u);
lean_inc(v_pos_3313_);
v___x_3322_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___y_3309_, v_maxChunkExtValueLength_3307_, v___x_3321_, v_pos_3313_);
v_snd_3323_ = lean_ctor_get(v___x_3322_, 1);
lean_inc(v_snd_3323_);
v_snd_3324_ = lean_ctor_get(v_snd_3323_, 1);
v___x_3325_ = lean_unbox(v_snd_3324_);
if (v___x_3325_ == 0)
{
lean_object* v_fst_3326_; lean_object* v_fst_3327_; uint8_t v___x_3328_; 
v_fst_3326_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_fst_3326_);
lean_dec_ref(v___x_3322_);
v_fst_3327_ = lean_ctor_get(v_snd_3323_, 0);
lean_inc(v_fst_3327_);
lean_dec(v_snd_3323_);
v___x_3328_ = lean_nat_dec_eq(v_fst_3326_, v___x_3321_);
if (v___x_3328_ == 0)
{
lean_object* v___x_3329_; lean_object* v___x_3330_; uint8_t v___x_3331_; 
lean_inc(v_idx_3316_);
lean_inc_ref(v_array_3315_);
lean_del_object(v___x_3319_);
lean_dec(v_pos_3313_);
v___x_3329_ = lean_nat_add(v_idx_3316_, v_fst_3326_);
lean_dec(v_fst_3326_);
v___x_3330_ = lean_byte_array_size(v_array_3315_);
v___x_3331_ = lean_nat_dec_le(v_idx_3316_, v___x_3321_);
if (v___x_3331_ == 0)
{
v___y_3292_ = v___x_3330_;
v___y_3293_ = v___x_3329_;
v___y_3294_ = v_array_3315_;
v___y_3295_ = v_fst_3327_;
v___y_3296_ = v___y_3310_;
v___y_3297_ = v_idx_3316_;
goto v___jp_3291_;
}
else
{
lean_dec(v_idx_3316_);
v___y_3292_ = v___x_3330_;
v___y_3293_ = v___x_3329_;
v___y_3294_ = v_array_3315_;
v___y_3295_ = v_fst_3327_;
v___y_3296_ = v___y_3310_;
v___y_3297_ = v___x_3321_;
goto v___jp_3291_;
}
}
else
{
lean_object* v___x_3332_; lean_object* v___x_3334_; 
lean_dec(v_fst_3327_);
lean_dec(v_fst_3326_);
lean_dec_ref(v___y_3310_);
v___x_3332_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_3320_ == 0)
{
lean_ctor_set(v___x_3319_, 1, v___x_3332_);
v___x_3334_ = v___x_3319_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_pos_3313_);
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
lean_object* v_fst_3336_; lean_object* v___x_3337_; lean_object* v___x_3339_; 
lean_dec_ref(v___x_3322_);
lean_dec(v_pos_3313_);
lean_dec_ref(v___y_3310_);
v_fst_3336_ = lean_ctor_get(v_snd_3323_, 0);
lean_inc(v_fst_3336_);
lean_dec(v_snd_3323_);
v___x_3337_ = lean_box(0);
if (v_isShared_3320_ == 0)
{
lean_ctor_set(v___x_3319_, 1, v___x_3337_);
lean_ctor_set(v___x_3319_, 0, v_fst_3336_);
v___x_3339_ = v___x_3319_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_fst_3336_);
lean_ctor_set(v_reuseFailAlloc_3340_, 1, v___x_3337_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
}
}
v___jp_3344_:
{
if (v___y_3348_ == 0)
{
v___y_3309_ = v___y_3345_;
v___y_3310_ = v___y_3347_;
v_pos_3311_ = v___y_3346_;
goto v___jp_3308_;
}
else
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
lean_dec_ref(v___y_3347_);
lean_dec_ref(v___y_3345_);
v___x_3349_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2));
v___x_3350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___y_3346_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
return v___x_3350_;
}
}
v_resetjp_3355_:
{
lean_object* v_snd_3358_; uint8_t v___x_3359_; 
v_snd_3358_ = lean_ctor_get(v_snd_3354_, 1);
v___x_3359_ = lean_unbox(v_snd_3358_);
if (v___x_3359_ == 0)
{
lean_object* v_fst_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3620_; 
v_fst_3360_ = lean_ctor_get(v_snd_3354_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v_snd_3354_);
if (v_isSharedCheck_3620_ == 0)
{
lean_object* v_unused_3621_; 
v_unused_3621_ = lean_ctor_get(v_snd_3354_, 1);
lean_dec(v_unused_3621_);
v___x_3362_ = v_snd_3354_;
v_isShared_3363_ = v_isSharedCheck_3620_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_fst_3360_);
lean_dec(v_snd_3354_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3620_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v_array_3364_; lean_object* v_idx_3365_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v_pos_3369_; lean_object* v_array_3370_; lean_object* v_idx_3371_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; uint8_t v___y_3434_; lean_object* v_pos_3442_; lean_object* v_res_3443_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v_lower_3511_; lean_object* v_upper_3512_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___f_3526_; lean_object* v_pos_3528_; lean_object* v___y_3561_; uint8_t v___y_3562_; lean_object* v_pos_3566_; lean_object* v_array_3567_; lean_object* v_idx_3568_; uint8_t v___y_3609_; lean_object* v___x_3612_; uint8_t v___x_3613_; 
v_array_3364_ = lean_ctor_get(v_fst_3360_, 0);
v_idx_3365_ = lean_ctor_get(v_fst_3360_, 1);
v___f_3526_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_3612_ = lean_byte_array_size(v_array_3364_);
v___x_3613_ = lean_nat_dec_lt(v_idx_3365_, v___x_3612_);
if (v___x_3613_ == 0)
{
lean_inc(v_idx_3365_);
lean_inc_ref(v_array_3364_);
v_pos_3566_ = v_fst_3360_;
v_array_3567_ = v_array_3364_;
v_idx_3568_ = v_idx_3365_;
goto v___jp_3565_;
}
else
{
uint8_t v___x_3614_; uint32_t v___x_3615_; uint32_t v___x_3616_; uint8_t v___x_3617_; 
v___x_3614_ = lean_byte_array_fget(v_array_3364_, v_idx_3365_);
v___x_3615_ = lean_uint8_to_uint32(v___x_3614_);
v___x_3616_ = 32;
v___x_3617_ = lean_uint32_dec_eq(v___x_3615_, v___x_3616_);
if (v___x_3617_ == 0)
{
uint32_t v___x_3618_; uint8_t v___x_3619_; 
v___x_3618_ = 9;
v___x_3619_ = lean_uint32_dec_eq(v___x_3615_, v___x_3618_);
if (v___x_3619_ == 0)
{
lean_inc(v_idx_3365_);
lean_inc_ref(v_array_3364_);
v_pos_3566_ = v_fst_3360_;
v_array_3567_ = v_array_3364_;
v_idx_3568_ = v_idx_3365_;
goto v___jp_3565_;
}
else
{
v___y_3609_ = v___x_3613_;
goto v___jp_3608_;
}
}
else
{
v___y_3609_ = v___x_3613_;
goto v___jp_3608_;
}
}
v___jp_3366_:
{
lean_object* v___x_3372_; uint8_t v___x_3373_; 
v___x_3372_ = lean_byte_array_size(v_array_3370_);
v___x_3373_ = lean_nat_dec_lt(v_idx_3371_, v___x_3372_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3374_; lean_object* v___x_3376_; 
lean_dec(v_idx_3371_);
lean_dec_ref(v_array_3370_);
lean_dec_ref(v___y_3368_);
v___x_3374_ = lean_box(0);
if (v_isShared_3363_ == 0)
{
lean_ctor_set_tag(v___x_3362_, 1);
lean_ctor_set(v___x_3362_, 1, v___x_3374_);
lean_ctor_set(v___x_3362_, 0, v_pos_3369_);
v___x_3376_ = v___x_3362_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_pos_3369_);
lean_ctor_set(v_reuseFailAlloc_3377_, 1, v___x_3374_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
else
{
uint8_t v___x_3378_; uint8_t v_got_3379_; uint8_t v___x_3380_; 
v___x_3378_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3);
v_got_3379_ = lean_byte_array_fget(v_array_3370_, v_idx_3371_);
v___x_3380_ = lean_uint8_dec_eq(v_got_3379_, v___x_3378_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; lean_object* v___x_3383_; 
lean_dec(v_idx_3371_);
lean_dec_ref(v_array_3370_);
lean_dec_ref(v___y_3368_);
v___x_3381_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__8, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__8_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__8);
if (v_isShared_3363_ == 0)
{
lean_ctor_set_tag(v___x_3362_, 1);
lean_ctor_set(v___x_3362_, 1, v___x_3381_);
lean_ctor_set(v___x_3362_, 0, v_pos_3369_);
v___x_3383_ = v___x_3362_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_pos_3369_);
lean_ctor_set(v_reuseFailAlloc_3384_, 1, v___x_3381_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
else
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3388_; 
lean_dec_ref(v_pos_3369_);
v___x_3385_ = lean_unsigned_to_nat(1u);
v___x_3386_ = lean_nat_add(v_idx_3371_, v___x_3385_);
lean_dec(v_idx_3371_);
if (v_isShared_3363_ == 0)
{
lean_ctor_set(v___x_3362_, 1, v___x_3386_);
lean_ctor_set(v___x_3362_, 0, v_array_3370_);
v___x_3388_ = v___x_3362_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_array_3370_);
lean_ctor_set(v_reuseFailAlloc_3429_, 1, v___x_3386_);
v___x_3388_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
lean_object* v___x_3389_; 
v___x_3389_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_3351_, v_maxSpaceSequence_3305_, v___y_3367_, v___x_3388_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v_pos_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3418_; 
v_pos_3390_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3418_ == 0)
{
lean_object* v_unused_3419_; 
v_unused_3419_ = lean_ctor_get(v___x_3389_, 1);
lean_dec(v_unused_3419_);
v___x_3392_ = v___x_3389_;
v_isShared_3393_ = v_isSharedCheck_3418_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_pos_3390_);
lean_dec(v___x_3389_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3418_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3394_; lean_object* v___f_3395_; lean_object* v___x_3396_; lean_object* v_snd_3397_; lean_object* v_snd_3398_; uint8_t v___x_3399_; 
v___x_3394_ = lean_box(v___x_3373_);
v___f_3395_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3395_, 0, v___x_3394_);
v___x_3396_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3395_, v_maxSpaceSequence_3305_, v___x_3352_, v_pos_3390_);
v_snd_3397_ = lean_ctor_get(v___x_3396_, 1);
lean_inc(v_snd_3397_);
lean_dec_ref(v___x_3396_);
v_snd_3398_ = lean_ctor_get(v_snd_3397_, 1);
v___x_3399_ = lean_unbox(v_snd_3398_);
if (v___x_3399_ == 0)
{
lean_object* v_fst_3400_; lean_object* v_array_3401_; lean_object* v_idx_3402_; lean_object* v___x_3403_; lean_object* v___f_3404_; lean_object* v___x_3405_; uint8_t v___x_3406_; 
lean_del_object(v___x_3392_);
v_fst_3400_ = lean_ctor_get(v_snd_3397_, 0);
lean_inc(v_fst_3400_);
lean_dec(v_snd_3397_);
v_array_3401_ = lean_ctor_get(v_fst_3400_, 0);
v_idx_3402_ = lean_ctor_get(v_fst_3400_, 1);
v___x_3403_ = lean_box(v___x_3373_);
v___f_3404_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__3___boxed), 2, 1);
lean_closure_set(v___f_3404_, 0, v___x_3403_);
v___x_3405_ = lean_byte_array_size(v_array_3401_);
v___x_3406_ = lean_nat_dec_lt(v_idx_3402_, v___x_3405_);
if (v___x_3406_ == 0)
{
v___y_3309_ = v___f_3404_;
v___y_3310_ = v___y_3368_;
v_pos_3311_ = v_fst_3400_;
goto v___jp_3308_;
}
else
{
uint8_t v___x_3407_; uint32_t v___x_3408_; uint32_t v___x_3409_; uint8_t v___x_3410_; 
v___x_3407_ = lean_byte_array_fget(v_array_3401_, v_idx_3402_);
v___x_3408_ = lean_uint8_to_uint32(v___x_3407_);
v___x_3409_ = 32;
v___x_3410_ = lean_uint32_dec_eq(v___x_3408_, v___x_3409_);
if (v___x_3410_ == 0)
{
uint32_t v___x_3411_; uint8_t v___x_3412_; 
v___x_3411_ = 9;
v___x_3412_ = lean_uint32_dec_eq(v___x_3408_, v___x_3411_);
if (v___x_3412_ == 0)
{
v___y_3309_ = v___f_3404_;
v___y_3310_ = v___y_3368_;
v_pos_3311_ = v_fst_3400_;
goto v___jp_3308_;
}
else
{
v___y_3345_ = v___f_3404_;
v___y_3346_ = v_fst_3400_;
v___y_3347_ = v___y_3368_;
v___y_3348_ = v___x_3406_;
goto v___jp_3344_;
}
}
else
{
v___y_3345_ = v___f_3404_;
v___y_3346_ = v_fst_3400_;
v___y_3347_ = v___y_3368_;
v___y_3348_ = v___x_3406_;
goto v___jp_3344_;
}
}
}
else
{
lean_object* v_fst_3413_; lean_object* v___x_3414_; lean_object* v___x_3416_; 
lean_dec_ref(v___y_3368_);
v_fst_3413_ = lean_ctor_get(v_snd_3397_, 0);
lean_inc(v_fst_3413_);
lean_dec(v_snd_3397_);
v___x_3414_ = lean_box(0);
if (v_isShared_3393_ == 0)
{
lean_ctor_set_tag(v___x_3392_, 1);
lean_ctor_set(v___x_3392_, 1, v___x_3414_);
lean_ctor_set(v___x_3392_, 0, v_fst_3413_);
v___x_3416_ = v___x_3392_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_fst_3413_);
lean_ctor_set(v_reuseFailAlloc_3417_, 1, v___x_3414_);
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
lean_object* v_pos_3420_; lean_object* v_err_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3428_; 
lean_dec_ref(v___y_3368_);
v_pos_3420_ = lean_ctor_get(v___x_3389_, 0);
v_err_3421_ = lean_ctor_get(v___x_3389_, 1);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3423_ = v___x_3389_;
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_err_3421_);
lean_inc(v_pos_3420_);
lean_dec(v___x_3389_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3424_ == 0)
{
v___x_3426_ = v___x_3423_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_pos_3420_);
lean_ctor_set(v_reuseFailAlloc_3427_, 1, v_err_3421_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
}
}
}
v___jp_3430_:
{
if (v___y_3434_ == 0)
{
lean_object* v_array_3435_; lean_object* v_idx_3436_; 
lean_del_object(v___x_3356_);
v_array_3435_ = lean_ctor_get(v___y_3432_, 0);
lean_inc_ref(v_array_3435_);
v_idx_3436_ = lean_ctor_get(v___y_3432_, 1);
lean_inc(v_idx_3436_);
v___y_3367_ = v___y_3431_;
v___y_3368_ = v___y_3433_;
v_pos_3369_ = v___y_3432_;
v_array_3370_ = v_array_3435_;
v_idx_3371_ = v_idx_3436_;
goto v___jp_3366_;
}
else
{
lean_object* v___x_3437_; lean_object* v___x_3439_; 
lean_dec_ref(v___y_3433_);
lean_del_object(v___x_3362_);
v___x_3437_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2));
if (v_isShared_3357_ == 0)
{
lean_ctor_set_tag(v___x_3356_, 1);
lean_ctor_set(v___x_3356_, 1, v___x_3437_);
lean_ctor_set(v___x_3356_, 0, v___y_3432_);
v___x_3439_ = v___x_3356_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___y_3432_);
lean_ctor_set(v_reuseFailAlloc_3440_, 1, v___x_3437_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
v___jp_3441_:
{
lean_object* v___x_3444_; 
v___x_3444_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_3443_, v_pos_3442_);
lean_dec(v_res_3443_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_pos_3445_; lean_object* v_res_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v_pos_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_pos_3445_);
v_res_3446_ = lean_ctor_get(v___x_3444_, 1);
lean_inc(v_res_3446_);
lean_dec_ref_known(v___x_3444_, 2);
v___x_3447_ = lean_box(0);
v___x_3448_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_3351_, v_maxSpaceSequence_3305_, v___x_3447_, v_pos_3445_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_pos_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3488_; 
v_pos_3449_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3488_ == 0)
{
lean_object* v_unused_3489_; 
v_unused_3489_ = lean_ctor_get(v___x_3448_, 1);
lean_dec(v_unused_3489_);
v___x_3451_ = v___x_3448_;
v_isShared_3452_ = v_isSharedCheck_3488_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_pos_3449_);
lean_dec(v___x_3448_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3488_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3453_; 
v___x_3453_ = l_Std_Http_Chunk_ExtensionName_ofString_x3f(v_res_3446_);
if (lean_obj_tag(v___x_3453_) == 1)
{
lean_object* v_val_3454_; lean_object* v_array_3455_; lean_object* v_idx_3456_; lean_object* v___x_3457_; uint8_t v___x_3458_; 
v_val_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_val_3454_);
lean_dec_ref_known(v___x_3453_, 1);
v_array_3455_ = lean_ctor_get(v_pos_3449_, 0);
v_idx_3456_ = lean_ctor_get(v_pos_3449_, 1);
v___x_3457_ = lean_byte_array_size(v_array_3455_);
v___x_3458_ = lean_nat_dec_lt(v_idx_3456_, v___x_3457_);
if (v___x_3458_ == 0)
{
lean_del_object(v___x_3451_);
lean_del_object(v___x_3362_);
lean_del_object(v___x_3356_);
v___y_3300_ = v_val_3454_;
v_pos_3301_ = v_pos_3449_;
goto v___jp_3299_;
}
else
{
uint8_t v___x_3459_; uint8_t v___x_3460_; uint8_t v___x_3461_; 
v___x_3459_ = lean_byte_array_fget(v_array_3455_, v_idx_3456_);
v___x_3460_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3);
v___x_3461_ = lean_uint8_dec_eq(v___x_3459_, v___x_3460_);
if (v___x_3461_ == 0)
{
lean_del_object(v___x_3451_);
lean_del_object(v___x_3362_);
lean_del_object(v___x_3356_);
v___y_3300_ = v_val_3454_;
v_pos_3301_ = v_pos_3449_;
goto v___jp_3299_;
}
else
{
lean_object* v___x_3462_; lean_object* v___f_3463_; lean_object* v___x_3464_; lean_object* v_snd_3465_; lean_object* v_snd_3466_; uint8_t v___x_3467_; 
v___x_3462_ = lean_box(v___x_3461_);
v___f_3463_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3463_, 0, v___x_3462_);
v___x_3464_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3463_, v_maxSpaceSequence_3305_, v___x_3352_, v_pos_3449_);
v_snd_3465_ = lean_ctor_get(v___x_3464_, 1);
lean_inc(v_snd_3465_);
lean_dec_ref(v___x_3464_);
v_snd_3466_ = lean_ctor_get(v_snd_3465_, 1);
v___x_3467_ = lean_unbox(v_snd_3466_);
if (v___x_3467_ == 0)
{
lean_object* v_fst_3468_; lean_object* v_array_3469_; lean_object* v_idx_3470_; lean_object* v___x_3471_; uint8_t v___x_3472_; 
lean_del_object(v___x_3451_);
v_fst_3468_ = lean_ctor_get(v_snd_3465_, 0);
lean_inc(v_fst_3468_);
lean_dec(v_snd_3465_);
v_array_3469_ = lean_ctor_get(v_fst_3468_, 0);
v_idx_3470_ = lean_ctor_get(v_fst_3468_, 1);
v___x_3471_ = lean_byte_array_size(v_array_3469_);
v___x_3472_ = lean_nat_dec_lt(v_idx_3470_, v___x_3471_);
if (v___x_3472_ == 0)
{
lean_inc(v_idx_3470_);
lean_inc_ref(v_array_3469_);
lean_del_object(v___x_3356_);
v___y_3367_ = v___x_3447_;
v___y_3368_ = v_val_3454_;
v_pos_3369_ = v_fst_3468_;
v_array_3370_ = v_array_3469_;
v_idx_3371_ = v_idx_3470_;
goto v___jp_3366_;
}
else
{
uint8_t v___x_3473_; uint32_t v___x_3474_; uint32_t v___x_3475_; uint8_t v___x_3476_; 
v___x_3473_ = lean_byte_array_fget(v_array_3469_, v_idx_3470_);
v___x_3474_ = lean_uint8_to_uint32(v___x_3473_);
v___x_3475_ = 32;
v___x_3476_ = lean_uint32_dec_eq(v___x_3474_, v___x_3475_);
if (v___x_3476_ == 0)
{
uint32_t v___x_3477_; uint8_t v___x_3478_; 
v___x_3477_ = 9;
v___x_3478_ = lean_uint32_dec_eq(v___x_3474_, v___x_3477_);
if (v___x_3478_ == 0)
{
lean_inc(v_idx_3470_);
lean_inc_ref(v_array_3469_);
lean_del_object(v___x_3356_);
v___y_3367_ = v___x_3447_;
v___y_3368_ = v_val_3454_;
v_pos_3369_ = v_fst_3468_;
v_array_3370_ = v_array_3469_;
v_idx_3371_ = v_idx_3470_;
goto v___jp_3366_;
}
else
{
v___y_3431_ = v___x_3447_;
v___y_3432_ = v_fst_3468_;
v___y_3433_ = v_val_3454_;
v___y_3434_ = v___x_3472_;
goto v___jp_3430_;
}
}
else
{
v___y_3431_ = v___x_3447_;
v___y_3432_ = v_fst_3468_;
v___y_3433_ = v_val_3454_;
v___y_3434_ = v___x_3472_;
goto v___jp_3430_;
}
}
}
else
{
lean_object* v_fst_3479_; lean_object* v___x_3480_; lean_object* v___x_3482_; 
lean_dec(v_val_3454_);
lean_del_object(v___x_3362_);
lean_del_object(v___x_3356_);
v_fst_3479_ = lean_ctor_get(v_snd_3465_, 0);
lean_inc(v_fst_3479_);
lean_dec(v_snd_3465_);
v___x_3480_ = lean_box(0);
if (v_isShared_3452_ == 0)
{
lean_ctor_set_tag(v___x_3451_, 1);
lean_ctor_set(v___x_3451_, 1, v___x_3480_);
lean_ctor_set(v___x_3451_, 0, v_fst_3479_);
v___x_3482_ = v___x_3451_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_fst_3479_);
lean_ctor_set(v_reuseFailAlloc_3483_, 1, v___x_3480_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
}
else
{
lean_object* v___x_3484_; lean_object* v___x_3486_; 
lean_dec(v___x_3453_);
lean_del_object(v___x_3362_);
lean_del_object(v___x_3356_);
v___x_3484_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__10));
if (v_isShared_3452_ == 0)
{
lean_ctor_set_tag(v___x_3451_, 1);
lean_ctor_set(v___x_3451_, 1, v___x_3484_);
v___x_3486_ = v___x_3451_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_pos_3449_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v___x_3484_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
else
{
lean_object* v_pos_3490_; lean_object* v_err_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
lean_dec(v_res_3446_);
lean_del_object(v___x_3362_);
lean_del_object(v___x_3356_);
v_pos_3490_ = lean_ctor_get(v___x_3448_, 0);
v_err_3491_ = lean_ctor_get(v___x_3448_, 1);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3493_ = v___x_3448_;
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_err_3491_);
lean_inc(v_pos_3490_);
lean_dec(v___x_3448_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_pos_3490_);
lean_ctor_set(v_reuseFailAlloc_3497_, 1, v_err_3491_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
else
{
lean_object* v_pos_3499_; lean_object* v_err_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3507_; 
lean_del_object(v___x_3362_);
lean_del_object(v___x_3356_);
v_pos_3499_ = lean_ctor_get(v___x_3444_, 0);
v_err_3500_ = lean_ctor_get(v___x_3444_, 1);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3502_ = v___x_3444_;
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_err_3500_);
lean_inc(v_pos_3499_);
lean_dec(v___x_3444_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
if (v_isShared_3503_ == 0)
{
v___x_3505_ = v___x_3502_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_pos_3499_);
lean_ctor_set(v_reuseFailAlloc_3506_, 1, v_err_3500_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
}
v___jp_3508_:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; uint8_t v___x_3515_; 
v___x_3513_ = l_ByteArray_toByteSlice(v___y_3509_, v_lower_3511_, v_upper_3512_);
v___x_3514_ = l_ByteSlice_toByteArray(v___x_3513_);
v___x_3515_ = lean_string_validate_utf8(v___x_3514_);
if (v___x_3515_ == 0)
{
lean_object* v___x_3516_; 
lean_dec_ref(v___x_3514_);
v___x_3516_ = lean_box(0);
v_pos_3442_ = v___y_3510_;
v_res_3443_ = v___x_3516_;
goto v___jp_3441_;
}
else
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = lean_string_from_utf8_unchecked(v___x_3514_);
v___x_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
v_pos_3442_ = v___y_3510_;
v_res_3443_ = v___x_3518_;
goto v___jp_3441_;
}
}
v___jp_3519_:
{
uint8_t v___x_3525_; 
v___x_3525_ = lean_nat_dec_le(v___y_3520_, v___y_3523_);
if (v___x_3525_ == 0)
{
lean_dec(v___y_3520_);
v___y_3509_ = v___y_3521_;
v___y_3510_ = v___y_3522_;
v_lower_3511_ = v___y_3524_;
v_upper_3512_ = v___y_3523_;
goto v___jp_3508_;
}
else
{
lean_dec(v___y_3523_);
v___y_3509_ = v___y_3521_;
v___y_3510_ = v___y_3522_;
v_lower_3511_ = v___y_3524_;
v_upper_3512_ = v___y_3520_;
goto v___jp_3508_;
}
}
v___jp_3527_:
{
lean_object* v___x_3529_; lean_object* v_snd_3530_; lean_object* v_snd_3531_; uint8_t v___x_3532_; 
lean_inc_ref(v_pos_3528_);
v___x_3529_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3526_, v_maxChunkExtNameLength_3306_, v___x_3352_, v_pos_3528_);
v_snd_3530_ = lean_ctor_get(v___x_3529_, 1);
lean_inc(v_snd_3530_);
v_snd_3531_ = lean_ctor_get(v_snd_3530_, 1);
v___x_3532_ = lean_unbox(v_snd_3531_);
if (v___x_3532_ == 0)
{
lean_object* v_fst_3533_; lean_object* v_fst_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3548_; 
v_fst_3533_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_fst_3533_);
lean_dec_ref(v___x_3529_);
v_fst_3534_ = lean_ctor_get(v_snd_3530_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v_snd_3530_);
if (v_isSharedCheck_3548_ == 0)
{
lean_object* v_unused_3549_; 
v_unused_3549_ = lean_ctor_get(v_snd_3530_, 1);
lean_dec(v_unused_3549_);
v___x_3536_ = v_snd_3530_;
v_isShared_3537_ = v_isSharedCheck_3548_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_fst_3534_);
lean_dec(v_snd_3530_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3548_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
uint8_t v___x_3538_; 
v___x_3538_ = lean_nat_dec_eq(v_fst_3533_, v___x_3352_);
if (v___x_3538_ == 0)
{
lean_object* v_array_3539_; lean_object* v_idx_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; uint8_t v___x_3543_; 
lean_del_object(v___x_3536_);
v_array_3539_ = lean_ctor_get(v_pos_3528_, 0);
lean_inc_ref(v_array_3539_);
v_idx_3540_ = lean_ctor_get(v_pos_3528_, 1);
lean_inc(v_idx_3540_);
lean_dec_ref(v_pos_3528_);
v___x_3541_ = lean_nat_add(v_idx_3540_, v_fst_3533_);
lean_dec(v_fst_3533_);
v___x_3542_ = lean_byte_array_size(v_array_3539_);
v___x_3543_ = lean_nat_dec_le(v_idx_3540_, v___x_3352_);
if (v___x_3543_ == 0)
{
v___y_3520_ = v___x_3541_;
v___y_3521_ = v_array_3539_;
v___y_3522_ = v_fst_3534_;
v___y_3523_ = v___x_3542_;
v___y_3524_ = v_idx_3540_;
goto v___jp_3519_;
}
else
{
lean_dec(v_idx_3540_);
v___y_3520_ = v___x_3541_;
v___y_3521_ = v_array_3539_;
v___y_3522_ = v_fst_3534_;
v___y_3523_ = v___x_3542_;
v___y_3524_ = v___x_3352_;
goto v___jp_3519_;
}
}
else
{
lean_object* v___x_3544_; lean_object* v___x_3546_; 
lean_dec(v_fst_3534_);
lean_dec(v_fst_3533_);
lean_del_object(v___x_3362_);
lean_del_object(v___x_3356_);
v___x_3544_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_3537_ == 0)
{
lean_ctor_set_tag(v___x_3536_, 1);
lean_ctor_set(v___x_3536_, 1, v___x_3544_);
lean_ctor_set(v___x_3536_, 0, v_pos_3528_);
v___x_3546_ = v___x_3536_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_pos_3528_);
lean_ctor_set(v_reuseFailAlloc_3547_, 1, v___x_3544_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
else
{
lean_object* v_fst_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3558_; 
lean_dec_ref(v___x_3529_);
lean_dec_ref(v_pos_3528_);
lean_del_object(v___x_3362_);
lean_del_object(v___x_3356_);
v_fst_3550_ = lean_ctor_get(v_snd_3530_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v_snd_3530_);
if (v_isSharedCheck_3558_ == 0)
{
lean_object* v_unused_3559_; 
v_unused_3559_ = lean_ctor_get(v_snd_3530_, 1);
lean_dec(v_unused_3559_);
v___x_3552_ = v_snd_3530_;
v_isShared_3553_ = v_isSharedCheck_3558_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_fst_3550_);
lean_dec(v_snd_3530_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3558_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3554_; lean_object* v___x_3556_; 
v___x_3554_ = lean_box(0);
if (v_isShared_3553_ == 0)
{
lean_ctor_set_tag(v___x_3552_, 1);
lean_ctor_set(v___x_3552_, 1, v___x_3554_);
v___x_3556_ = v___x_3552_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_fst_3550_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
v___jp_3560_:
{
if (v___y_3562_ == 0)
{
v_pos_3528_ = v___y_3561_;
goto v___jp_3527_;
}
else
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
lean_del_object(v___x_3362_);
lean_del_object(v___x_3356_);
v___x_3563_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2));
v___x_3564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3564_, 0, v___y_3561_);
lean_ctor_set(v___x_3564_, 1, v___x_3563_);
return v___x_3564_;
}
}
v___jp_3565_:
{
lean_object* v___x_3569_; uint8_t v___x_3570_; 
v___x_3569_ = lean_byte_array_size(v_array_3567_);
v___x_3570_ = lean_nat_dec_lt(v_idx_3568_, v___x_3569_);
if (v___x_3570_ == 0)
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
lean_dec(v_idx_3568_);
lean_dec_ref(v_array_3567_);
lean_del_object(v___x_3362_);
lean_del_object(v___x_3356_);
v___x_3571_ = lean_box(0);
v___x_3572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3572_, 0, v_pos_3566_);
lean_ctor_set(v___x_3572_, 1, v___x_3571_);
return v___x_3572_;
}
else
{
uint8_t v___x_3573_; uint8_t v_got_3574_; uint8_t v___x_3575_; 
v___x_3573_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__11, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__11_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__11);
v_got_3574_ = lean_byte_array_fget(v_array_3567_, v_idx_3568_);
v___x_3575_ = lean_uint8_dec_eq(v_got_3574_, v___x_3573_);
if (v___x_3575_ == 0)
{
lean_object* v___x_3576_; lean_object* v___x_3577_; 
lean_dec(v_idx_3568_);
lean_dec_ref(v_array_3567_);
lean_del_object(v___x_3362_);
lean_del_object(v___x_3356_);
v___x_3576_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__16, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__16_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__16);
v___x_3577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3577_, 0, v_pos_3566_);
lean_ctor_set(v___x_3577_, 1, v___x_3576_);
return v___x_3577_;
}
else
{
lean_object* v___x_3578_; lean_object* v___f_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v_snd_3584_; lean_object* v_snd_3585_; uint8_t v___x_3586_; 
lean_dec_ref(v_pos_3566_);
v___x_3578_ = lean_box(v___x_3570_);
v___f_3579_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3579_, 0, v___x_3578_);
v___x_3580_ = lean_unsigned_to_nat(1u);
v___x_3581_ = lean_nat_add(v_idx_3568_, v___x_3580_);
lean_dec(v_idx_3568_);
v___x_3582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3582_, 0, v_array_3567_);
lean_ctor_set(v___x_3582_, 1, v___x_3581_);
v___x_3583_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3579_, v_maxSpaceSequence_3305_, v___x_3352_, v___x_3582_);
v_snd_3584_ = lean_ctor_get(v___x_3583_, 1);
lean_inc(v_snd_3584_);
lean_dec_ref(v___x_3583_);
v_snd_3585_ = lean_ctor_get(v_snd_3584_, 1);
v___x_3586_ = lean_unbox(v_snd_3585_);
if (v___x_3586_ == 0)
{
lean_object* v_fst_3587_; lean_object* v_array_3588_; lean_object* v_idx_3589_; lean_object* v___x_3590_; uint8_t v___x_3591_; 
v_fst_3587_ = lean_ctor_get(v_snd_3584_, 0);
lean_inc(v_fst_3587_);
lean_dec(v_snd_3584_);
v_array_3588_ = lean_ctor_get(v_fst_3587_, 0);
v_idx_3589_ = lean_ctor_get(v_fst_3587_, 1);
v___x_3590_ = lean_byte_array_size(v_array_3588_);
v___x_3591_ = lean_nat_dec_lt(v_idx_3589_, v___x_3590_);
if (v___x_3591_ == 0)
{
v_pos_3528_ = v_fst_3587_;
goto v___jp_3527_;
}
else
{
uint8_t v___x_3592_; uint32_t v___x_3593_; uint32_t v___x_3594_; uint8_t v___x_3595_; 
v___x_3592_ = lean_byte_array_fget(v_array_3588_, v_idx_3589_);
v___x_3593_ = lean_uint8_to_uint32(v___x_3592_);
v___x_3594_ = 32;
v___x_3595_ = lean_uint32_dec_eq(v___x_3593_, v___x_3594_);
if (v___x_3595_ == 0)
{
uint32_t v___x_3596_; uint8_t v___x_3597_; 
v___x_3596_ = 9;
v___x_3597_ = lean_uint32_dec_eq(v___x_3593_, v___x_3596_);
if (v___x_3597_ == 0)
{
v_pos_3528_ = v_fst_3587_;
goto v___jp_3527_;
}
else
{
v___y_3561_ = v_fst_3587_;
v___y_3562_ = v___x_3591_;
goto v___jp_3560_;
}
}
else
{
v___y_3561_ = v_fst_3587_;
v___y_3562_ = v___x_3591_;
goto v___jp_3560_;
}
}
}
else
{
lean_object* v_fst_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3606_; 
lean_del_object(v___x_3362_);
lean_del_object(v___x_3356_);
v_fst_3598_ = lean_ctor_get(v_snd_3584_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v_snd_3584_);
if (v_isSharedCheck_3606_ == 0)
{
lean_object* v_unused_3607_; 
v_unused_3607_ = lean_ctor_get(v_snd_3584_, 1);
lean_dec(v_unused_3607_);
v___x_3600_ = v_snd_3584_;
v_isShared_3601_ = v_isSharedCheck_3606_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_fst_3598_);
lean_dec(v_snd_3584_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3606_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3602_; lean_object* v___x_3604_; 
v___x_3602_ = lean_box(0);
if (v_isShared_3601_ == 0)
{
lean_ctor_set_tag(v___x_3600_, 1);
lean_ctor_set(v___x_3600_, 1, v___x_3602_);
v___x_3604_ = v___x_3600_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_fst_3598_);
lean_ctor_set(v_reuseFailAlloc_3605_, 1, v___x_3602_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
}
}
}
v___jp_3608_:
{
if (v___y_3609_ == 0)
{
lean_inc(v_idx_3365_);
lean_inc_ref(v_array_3364_);
v_pos_3566_ = v_fst_3360_;
v_array_3567_ = v_array_3364_;
v_idx_3568_ = v_idx_3365_;
goto v___jp_3565_;
}
else
{
lean_object* v___x_3610_; lean_object* v___x_3611_; 
lean_del_object(v___x_3362_);
lean_del_object(v___x_3356_);
v___x_3610_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2));
v___x_3611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3611_, 0, v_fst_3360_);
lean_ctor_set(v___x_3611_, 1, v___x_3610_);
return v___x_3611_;
}
}
}
}
else
{
lean_object* v_fst_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3630_; 
lean_del_object(v___x_3356_);
v_fst_3622_ = lean_ctor_get(v_snd_3354_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v_snd_3354_);
if (v_isSharedCheck_3630_ == 0)
{
lean_object* v_unused_3631_; 
v_unused_3631_ = lean_ctor_get(v_snd_3354_, 1);
lean_dec(v_unused_3631_);
v___x_3624_ = v_snd_3354_;
v_isShared_3625_ = v_isSharedCheck_3630_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_fst_3622_);
lean_dec(v_snd_3354_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3630_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3626_; lean_object* v___x_3628_; 
v___x_3626_ = lean_box(0);
if (v_isShared_3625_ == 0)
{
lean_ctor_set_tag(v___x_3624_, 1);
lean_ctor_set(v___x_3624_, 1, v___x_3626_);
v___x_3628_ = v___x_3624_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_fst_3622_);
lean_ctor_set(v_reuseFailAlloc_3629_, 1, v___x_3626_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___boxed(lean_object* v_limits_3634_, lean_object* v_a_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_3634_, v_a_3635_);
lean_dec_ref(v_limits_3634_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0(lean_object* v_limits_3637_, lean_object* v___y_3638_){
_start:
{
lean_object* v_pos_3640_; lean_object* v_err_3641_; lean_object* v___x_3657_; 
lean_inc_ref(v___y_3638_);
v___x_3657_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_3637_, v___y_3638_);
if (lean_obj_tag(v___x_3657_) == 0)
{
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v_pos_3658_; lean_object* v_res_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3667_; 
lean_dec_ref(v___y_3638_);
v_pos_3658_ = lean_ctor_get(v___x_3657_, 0);
v_res_3659_ = lean_ctor_get(v___x_3657_, 1);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3661_ = v___x_3657_;
v_isShared_3662_ = v_isSharedCheck_3667_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_res_3659_);
lean_inc(v_pos_3658_);
lean_dec(v___x_3657_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3667_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3663_; lean_object* v___x_3665_; 
v___x_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3663_, 0, v_res_3659_);
if (v_isShared_3662_ == 0)
{
lean_ctor_set(v___x_3661_, 1, v___x_3663_);
v___x_3665_ = v___x_3661_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_pos_3658_);
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
else
{
lean_object* v_pos_3668_; lean_object* v_err_3669_; 
v_pos_3668_ = lean_ctor_get(v___x_3657_, 0);
lean_inc(v_pos_3668_);
v_err_3669_ = lean_ctor_get(v___x_3657_, 1);
lean_inc(v_err_3669_);
lean_dec_ref_known(v___x_3657_, 2);
v_pos_3640_ = v_pos_3668_;
v_err_3641_ = v_err_3669_;
goto v___jp_3639_;
}
}
else
{
lean_object* v_err_3670_; 
v_err_3670_ = lean_ctor_get(v___x_3657_, 1);
lean_inc(v_err_3670_);
lean_dec_ref_known(v___x_3657_, 2);
lean_inc_ref(v___y_3638_);
v_pos_3640_ = v___y_3638_;
v_err_3641_ = v_err_3670_;
goto v___jp_3639_;
}
v___jp_3639_:
{
lean_object* v_idx_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3655_; 
v_idx_3642_ = lean_ctor_get(v___y_3638_, 1);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___y_3638_);
if (v_isSharedCheck_3655_ == 0)
{
lean_object* v_unused_3656_; 
v_unused_3656_ = lean_ctor_get(v___y_3638_, 0);
lean_dec(v_unused_3656_);
v___x_3644_ = v___y_3638_;
v_isShared_3645_ = v_isSharedCheck_3655_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_idx_3642_);
lean_dec(v___y_3638_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3655_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v_idx_3646_; uint8_t v___x_3647_; 
v_idx_3646_ = lean_ctor_get(v_pos_3640_, 1);
v___x_3647_ = lean_nat_dec_eq(v_idx_3642_, v_idx_3646_);
lean_dec(v_idx_3642_);
if (v___x_3647_ == 0)
{
lean_object* v___x_3649_; 
if (v_isShared_3645_ == 0)
{
lean_ctor_set_tag(v___x_3644_, 1);
lean_ctor_set(v___x_3644_, 1, v_err_3641_);
lean_ctor_set(v___x_3644_, 0, v_pos_3640_);
v___x_3649_ = v___x_3644_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_pos_3640_);
lean_ctor_set(v_reuseFailAlloc_3650_, 1, v_err_3641_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
else
{
lean_object* v___x_3651_; lean_object* v___x_3653_; 
lean_dec(v_err_3641_);
v___x_3651_ = lean_box(0);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 1, v___x_3651_);
lean_ctor_set(v___x_3644_, 0, v_pos_3640_);
v___x_3653_ = v___x_3644_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_pos_3640_);
lean_ctor_set(v_reuseFailAlloc_3654_, 1, v___x_3651_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed(lean_object* v_limits_3671_, lean_object* v___y_3672_){
_start:
{
lean_object* v_res_3673_; 
v_res_3673_ = l_Std_Http_Protocol_H1_parseChunkSize___lam__0(v_limits_3671_, v___y_3672_);
lean_dec_ref(v_limits_3671_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize(lean_object* v_limits_3674_, lean_object* v_a_3675_){
_start:
{
lean_object* v___x_3676_; 
v___x_3676_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(v_a_3675_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_pos_3677_; lean_object* v_res_3678_; lean_object* v_maxChunkExtensions_3679_; lean_object* v___f_3680_; lean_object* v___x_3681_; 
v_pos_3677_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_pos_3677_);
v_res_3678_ = lean_ctor_get(v___x_3676_, 1);
lean_inc(v_res_3678_);
lean_dec_ref_known(v___x_3676_, 2);
v_maxChunkExtensions_3679_ = lean_ctor_get(v_limits_3674_, 10);
lean_inc(v_maxChunkExtensions_3679_);
v___f_3680_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3680_, 0, v_limits_3674_);
v___x_3681_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___f_3680_, v_maxChunkExtensions_3679_, v_pos_3677_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_object* v_pos_3682_; lean_object* v_res_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v_pos_3682_ = lean_ctor_get(v___x_3681_, 0);
lean_inc(v_pos_3682_);
v_res_3683_ = lean_ctor_get(v___x_3681_, 1);
lean_inc(v_res_3683_);
lean_dec_ref_known(v___x_3681_, 2);
v___x_3684_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3685_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3684_, v_pos_3682_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v_pos_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3694_; 
v_pos_3686_ = lean_ctor_get(v___x_3685_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3694_ == 0)
{
lean_object* v_unused_3695_; 
v_unused_3695_ = lean_ctor_get(v___x_3685_, 1);
lean_dec(v_unused_3695_);
v___x_3688_ = v___x_3685_;
v_isShared_3689_ = v_isSharedCheck_3694_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_pos_3686_);
lean_dec(v___x_3685_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3694_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3690_; lean_object* v___x_3692_; 
v___x_3690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3690_, 0, v_res_3678_);
lean_ctor_set(v___x_3690_, 1, v_res_3683_);
if (v_isShared_3689_ == 0)
{
lean_ctor_set(v___x_3688_, 1, v___x_3690_);
v___x_3692_ = v___x_3688_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_pos_3686_);
lean_ctor_set(v_reuseFailAlloc_3693_, 1, v___x_3690_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
else
{
lean_object* v_pos_3696_; lean_object* v_err_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3704_; 
lean_dec(v_res_3683_);
lean_dec(v_res_3678_);
v_pos_3696_ = lean_ctor_get(v___x_3685_, 0);
v_err_3697_ = lean_ctor_get(v___x_3685_, 1);
v_isSharedCheck_3704_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3699_ = v___x_3685_;
v_isShared_3700_ = v_isSharedCheck_3704_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_err_3697_);
lean_inc(v_pos_3696_);
lean_dec(v___x_3685_);
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
else
{
lean_object* v_pos_3705_; lean_object* v_err_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3713_; 
lean_dec(v_res_3678_);
v_pos_3705_ = lean_ctor_get(v___x_3681_, 0);
v_err_3706_ = lean_ctor_get(v___x_3681_, 1);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3708_ = v___x_3681_;
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_err_3706_);
lean_inc(v_pos_3705_);
lean_dec(v___x_3681_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3711_; 
if (v_isShared_3709_ == 0)
{
v___x_3711_ = v___x_3708_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_pos_3705_);
lean_ctor_set(v_reuseFailAlloc_3712_, 1, v_err_3706_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
}
else
{
lean_object* v_pos_3714_; lean_object* v_err_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
lean_dec_ref(v_limits_3674_);
v_pos_3714_ = lean_ctor_get(v___x_3676_, 0);
v_err_3715_ = lean_ctor_get(v___x_3676_, 1);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3717_ = v___x_3676_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_err_3715_);
lean_inc(v_pos_3714_);
lean_dec(v___x_3676_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_pos_3714_);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx(lean_object* v_x_3723_){
_start:
{
if (lean_obj_tag(v_x_3723_) == 0)
{
lean_object* v___x_3724_; 
v___x_3724_ = lean_unsigned_to_nat(0u);
return v___x_3724_;
}
else
{
lean_object* v___x_3725_; 
v___x_3725_ = lean_unsigned_to_nat(1u);
return v___x_3725_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___boxed(lean_object* v_x_3726_){
_start:
{
lean_object* v_res_3727_; 
v_res_3727_ = l_Std_Http_Protocol_H1_TakeResult_ctorIdx(v_x_3726_);
lean_dec_ref(v_x_3726_);
return v_res_3727_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(lean_object* v_t_3728_, lean_object* v_k_3729_){
_start:
{
if (lean_obj_tag(v_t_3728_) == 0)
{
lean_object* v_data_3730_; lean_object* v___x_3731_; 
v_data_3730_ = lean_ctor_get(v_t_3728_, 0);
lean_inc_ref(v_data_3730_);
lean_dec_ref_known(v_t_3728_, 1);
v___x_3731_ = lean_apply_1(v_k_3729_, v_data_3730_);
return v___x_3731_;
}
else
{
lean_object* v_data_3732_; lean_object* v_remaining_3733_; lean_object* v___x_3734_; 
v_data_3732_ = lean_ctor_get(v_t_3728_, 0);
lean_inc_ref(v_data_3732_);
v_remaining_3733_ = lean_ctor_get(v_t_3728_, 1);
lean_inc(v_remaining_3733_);
lean_dec_ref_known(v_t_3728_, 2);
v___x_3734_ = lean_apply_2(v_k_3729_, v_data_3732_, v_remaining_3733_);
return v___x_3734_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim(lean_object* v_motive_3735_, lean_object* v_ctorIdx_3736_, lean_object* v_t_3737_, lean_object* v_h_3738_, lean_object* v_k_3739_){
_start:
{
lean_object* v___x_3740_; 
v___x_3740_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3737_, v_k_3739_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___boxed(lean_object* v_motive_3741_, lean_object* v_ctorIdx_3742_, lean_object* v_t_3743_, lean_object* v_h_3744_, lean_object* v_k_3745_){
_start:
{
lean_object* v_res_3746_; 
v_res_3746_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim(v_motive_3741_, v_ctorIdx_3742_, v_t_3743_, v_h_3744_, v_k_3745_);
lean_dec(v_ctorIdx_3742_);
return v_res_3746_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim___redArg(lean_object* v_t_3747_, lean_object* v_complete_3748_){
_start:
{
lean_object* v___x_3749_; 
v___x_3749_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3747_, v_complete_3748_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim(lean_object* v_motive_3750_, lean_object* v_t_3751_, lean_object* v_h_3752_, lean_object* v_complete_3753_){
_start:
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3751_, v_complete_3753_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim___redArg(lean_object* v_t_3755_, lean_object* v_incomplete_3756_){
_start:
{
lean_object* v___x_3757_; 
v___x_3757_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3755_, v_incomplete_3756_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim(lean_object* v_motive_3758_, lean_object* v_t_3759_, lean_object* v_h_3760_, lean_object* v_incomplete_3761_){
_start:
{
lean_object* v___x_3762_; 
v___x_3762_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3759_, v_incomplete_3761_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkPartial(lean_object* v_limits_3763_, lean_object* v_a_3764_){
_start:
{
lean_object* v___x_3765_; 
v___x_3765_ = l_Std_Http_Protocol_H1_parseChunkSize(v_limits_3763_, v_a_3764_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_res_3766_; lean_object* v_pos_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3807_; 
v_res_3766_ = lean_ctor_get(v___x_3765_, 1);
v_pos_3767_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3769_ = v___x_3765_;
v_isShared_3770_ = v_isSharedCheck_3807_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_res_3766_);
lean_inc(v_pos_3767_);
lean_dec(v___x_3765_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3807_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v_fst_3771_; lean_object* v_snd_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3806_; 
v_fst_3771_ = lean_ctor_get(v_res_3766_, 0);
v_snd_3772_ = lean_ctor_get(v_res_3766_, 1);
v_isSharedCheck_3806_ = !lean_is_exclusive(v_res_3766_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3774_ = v_res_3766_;
v_isShared_3775_ = v_isSharedCheck_3806_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_snd_3772_);
lean_inc(v_fst_3771_);
lean_dec(v_res_3766_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3806_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3776_; uint8_t v___x_3777_; 
v___x_3776_ = lean_unsigned_to_nat(0u);
v___x_3777_ = lean_nat_dec_eq(v_fst_3771_, v___x_3776_);
if (v___x_3777_ == 0)
{
lean_object* v___x_3778_; 
lean_del_object(v___x_3769_);
v___x_3778_ = l_Std_Internal_Parsec_ByteArray_take(v_fst_3771_, v_pos_3767_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_pos_3779_; lean_object* v_res_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3792_; 
v_pos_3779_ = lean_ctor_get(v___x_3778_, 0);
v_res_3780_ = lean_ctor_get(v___x_3778_, 1);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3782_ = v___x_3778_;
v_isShared_3783_ = v_isSharedCheck_3792_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_res_3780_);
lean_inc(v_pos_3779_);
lean_dec(v___x_3778_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3792_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 1, v_res_3780_);
lean_ctor_set(v___x_3774_, 0, v_snd_3772_);
v___x_3785_ = v___x_3774_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_snd_3772_);
lean_ctor_set(v_reuseFailAlloc_3791_, 1, v_res_3780_);
v___x_3785_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3789_; 
v___x_3786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3786_, 0, v_fst_3771_);
lean_ctor_set(v___x_3786_, 1, v___x_3785_);
v___x_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3786_);
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 1, v___x_3787_);
v___x_3789_ = v___x_3782_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_pos_3779_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v___x_3787_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
else
{
lean_object* v_pos_3793_; lean_object* v_err_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_del_object(v___x_3774_);
lean_dec(v_snd_3772_);
lean_dec(v_fst_3771_);
v_pos_3793_ = lean_ctor_get(v___x_3778_, 0);
v_err_3794_ = lean_ctor_get(v___x_3778_, 1);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3778_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_err_3794_);
lean_inc(v_pos_3793_);
lean_dec(v___x_3778_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3799_; 
if (v_isShared_3797_ == 0)
{
v___x_3799_ = v___x_3796_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_pos_3793_);
lean_ctor_set(v_reuseFailAlloc_3800_, 1, v_err_3794_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
else
{
lean_object* v___x_3802_; lean_object* v___x_3804_; 
lean_del_object(v___x_3774_);
lean_dec(v_snd_3772_);
lean_dec(v_fst_3771_);
v___x_3802_ = lean_box(0);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 1, v___x_3802_);
v___x_3804_ = v___x_3769_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_pos_3767_);
lean_ctor_set(v_reuseFailAlloc_3805_, 1, v___x_3802_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
}
}
else
{
lean_object* v_pos_3808_; lean_object* v_err_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
v_pos_3808_ = lean_ctor_get(v___x_3765_, 0);
v_err_3809_ = lean_ctor_get(v___x_3765_, 1);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3811_ = v___x_3765_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_err_3809_);
lean_inc(v_pos_3808_);
lean_dec(v___x_3765_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_pos_3808_);
lean_ctor_set(v_reuseFailAlloc_3815_, 1, v_err_3809_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData(lean_object* v_size_3817_, lean_object* v_it_3818_){
_start:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; uint8_t v___x_3821_; 
v___x_3819_ = l_ByteArray_Iterator_remainingBytes(v_it_3818_);
v___x_3820_ = lean_unsigned_to_nat(0u);
v___x_3821_ = lean_nat_dec_eq(v___x_3819_, v___x_3820_);
if (v___x_3821_ == 0)
{
uint8_t v___x_3822_; 
v___x_3822_ = lean_nat_dec_lt(v___x_3819_, v_size_3817_);
if (v___x_3822_ == 0)
{
lean_object* v_array_3823_; lean_object* v_idx_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3843_; 
lean_dec(v___x_3819_);
v_array_3823_ = lean_ctor_get(v_it_3818_, 0);
v_idx_3824_ = lean_ctor_get(v_it_3818_, 1);
v_isSharedCheck_3843_ = !lean_is_exclusive(v_it_3818_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3826_ = v_it_3818_;
v_isShared_3827_ = v_isSharedCheck_3843_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_idx_3824_);
lean_inc(v_array_3823_);
lean_dec(v_it_3818_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3843_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3828_; lean_object* v___x_3830_; 
v___x_3828_ = lean_nat_add(v_idx_3824_, v_size_3817_);
lean_inc(v___x_3828_);
lean_inc_ref(v_array_3823_);
if (v_isShared_3827_ == 0)
{
lean_ctor_set(v___x_3826_, 1, v___x_3828_);
v___x_3830_ = v___x_3826_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_array_3823_);
lean_ctor_set(v_reuseFailAlloc_3842_, 1, v___x_3828_);
v___x_3830_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
lean_object* v_lower_3832_; lean_object* v_upper_3833_; lean_object* v___x_3837_; lean_object* v___y_3839_; uint8_t v___x_3841_; 
v___x_3837_ = lean_byte_array_size(v_array_3823_);
v___x_3841_ = lean_nat_dec_le(v_idx_3824_, v___x_3820_);
if (v___x_3841_ == 0)
{
v___y_3839_ = v_idx_3824_;
goto v___jp_3838_;
}
else
{
lean_dec(v_idx_3824_);
v___y_3839_ = v___x_3820_;
goto v___jp_3838_;
}
v___jp_3831_:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3834_ = l_ByteArray_toByteSlice(v_array_3823_, v_lower_3832_, v_upper_3833_);
v___x_3835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3835_, 0, v___x_3834_);
v___x_3836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3830_);
lean_ctor_set(v___x_3836_, 1, v___x_3835_);
return v___x_3836_;
}
v___jp_3838_:
{
uint8_t v___x_3840_; 
v___x_3840_ = lean_nat_dec_le(v___x_3828_, v___x_3837_);
if (v___x_3840_ == 0)
{
lean_dec(v___x_3828_);
v_lower_3832_ = v___y_3839_;
v_upper_3833_ = v___x_3837_;
goto v___jp_3831_;
}
else
{
v_lower_3832_ = v___y_3839_;
v_upper_3833_ = v___x_3828_;
goto v___jp_3831_;
}
}
}
}
}
else
{
lean_object* v_array_3844_; lean_object* v_idx_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3865_; 
v_array_3844_ = lean_ctor_get(v_it_3818_, 0);
v_idx_3845_ = lean_ctor_get(v_it_3818_, 1);
v_isSharedCheck_3865_ = !lean_is_exclusive(v_it_3818_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3847_ = v_it_3818_;
v_isShared_3848_ = v_isSharedCheck_3865_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_idx_3845_);
lean_inc(v_array_3844_);
lean_dec(v_it_3818_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3865_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3849_; lean_object* v___x_3851_; 
v___x_3849_ = lean_nat_add(v_idx_3845_, v___x_3819_);
lean_inc(v___x_3849_);
lean_inc_ref(v_array_3844_);
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 1, v___x_3849_);
v___x_3851_ = v___x_3847_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_array_3844_);
lean_ctor_set(v_reuseFailAlloc_3864_, 1, v___x_3849_);
v___x_3851_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
lean_object* v_lower_3853_; lean_object* v_upper_3854_; lean_object* v___x_3859_; lean_object* v___y_3861_; uint8_t v___x_3863_; 
v___x_3859_ = lean_byte_array_size(v_array_3844_);
v___x_3863_ = lean_nat_dec_le(v_idx_3845_, v___x_3820_);
if (v___x_3863_ == 0)
{
v___y_3861_ = v_idx_3845_;
goto v___jp_3860_;
}
else
{
lean_dec(v_idx_3845_);
v___y_3861_ = v___x_3820_;
goto v___jp_3860_;
}
v___jp_3852_:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3855_ = l_ByteArray_toByteSlice(v_array_3844_, v_lower_3853_, v_upper_3854_);
v___x_3856_ = lean_nat_sub(v_size_3817_, v___x_3819_);
lean_dec(v___x_3819_);
v___x_3857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3855_);
lean_ctor_set(v___x_3857_, 1, v___x_3856_);
v___x_3858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3851_);
lean_ctor_set(v___x_3858_, 1, v___x_3857_);
return v___x_3858_;
}
v___jp_3860_:
{
uint8_t v___x_3862_; 
v___x_3862_ = lean_nat_dec_le(v___x_3849_, v___x_3859_);
if (v___x_3862_ == 0)
{
lean_dec(v___x_3849_);
v_lower_3853_ = v___y_3861_;
v_upper_3854_ = v___x_3859_;
goto v___jp_3852_;
}
else
{
v_lower_3853_ = v___y_3861_;
v_upper_3854_ = v___x_3849_;
goto v___jp_3852_;
}
}
}
}
}
}
else
{
lean_object* v___x_3866_; lean_object* v___x_3867_; 
lean_dec(v___x_3819_);
v___x_3866_ = lean_box(0);
v___x_3867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3867_, 0, v_it_3818_);
lean_ctor_set(v___x_3867_, 1, v___x_3866_);
return v___x_3867_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData___boxed(lean_object* v_size_3868_, lean_object* v_it_3869_){
_start:
{
lean_object* v_res_3870_; 
v_res_3870_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_3868_, v_it_3869_);
lean_dec(v_size_3868_);
return v_res_3870_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData(lean_object* v_size_3871_, lean_object* v_a_3872_){
_start:
{
lean_object* v___x_3873_; 
v___x_3873_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_3871_, v_a_3872_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_res_3874_; 
v_res_3874_ = lean_ctor_get(v___x_3873_, 1);
lean_inc(v_res_3874_);
if (lean_obj_tag(v_res_3874_) == 0)
{
lean_object* v_pos_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v_pos_3875_ = lean_ctor_get(v___x_3873_, 0);
lean_inc(v_pos_3875_);
lean_dec_ref_known(v___x_3873_, 2);
v___x_3876_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3877_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3876_, v_pos_3875_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_object* v_pos_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
v_pos_3878_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3885_ == 0)
{
lean_object* v_unused_3886_; 
v_unused_3886_ = lean_ctor_get(v___x_3877_, 1);
lean_dec(v_unused_3886_);
v___x_3880_ = v___x_3877_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_pos_3878_);
lean_dec(v___x_3877_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 1, v_res_3874_);
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_pos_3878_);
lean_ctor_set(v_reuseFailAlloc_3884_, 1, v_res_3874_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
else
{
lean_object* v_pos_3887_; lean_object* v_err_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
lean_dec_ref_known(v_res_3874_, 1);
v_pos_3887_ = lean_ctor_get(v___x_3877_, 0);
v_err_3888_ = lean_ctor_get(v___x_3877_, 1);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3877_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_err_3888_);
lean_inc(v_pos_3887_);
lean_dec(v___x_3877_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_pos_3887_);
lean_ctor_set(v_reuseFailAlloc_3894_, 1, v_err_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
else
{
lean_dec_ref_known(v_res_3874_, 2);
return v___x_3873_;
}
}
else
{
return v___x_3873_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData___boxed(lean_object* v_size_3896_, lean_object* v_a_3897_){
_start:
{
lean_object* v_res_3898_; 
v_res_3898_ = l_Std_Http_Protocol_H1_parseChunkSizedData(v_size_3896_, v_a_3897_);
lean_dec(v_size_3896_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField_spec__0(lean_object* v_s_3899_, lean_object* v_p_3900_){
_start:
{
uint32_t v___y_3902_; lean_object* v___x_3907_; uint8_t v___x_3908_; 
v___x_3907_ = lean_string_utf8_byte_size(v_s_3899_);
v___x_3908_ = lean_nat_dec_eq(v_p_3900_, v___x_3907_);
if (v___x_3908_ == 0)
{
uint32_t v___x_3909_; uint32_t v___x_3910_; uint8_t v___x_3911_; 
v___x_3909_ = lean_string_utf8_get_fast(v_s_3899_, v_p_3900_);
v___x_3910_ = 65;
v___x_3911_ = lean_uint32_dec_le(v___x_3910_, v___x_3909_);
if (v___x_3911_ == 0)
{
v___y_3902_ = v___x_3909_;
goto v___jp_3901_;
}
else
{
uint32_t v___x_3912_; uint8_t v___x_3913_; 
v___x_3912_ = 90;
v___x_3913_ = lean_uint32_dec_le(v___x_3909_, v___x_3912_);
if (v___x_3913_ == 0)
{
v___y_3902_ = v___x_3909_;
goto v___jp_3901_;
}
else
{
uint32_t v___x_3914_; uint32_t v___x_3915_; 
v___x_3914_ = 32;
v___x_3915_ = lean_uint32_add(v___x_3909_, v___x_3914_);
v___y_3902_ = v___x_3915_;
goto v___jp_3901_;
}
}
}
else
{
lean_dec(v_p_3900_);
return v_s_3899_;
}
v___jp_3901_:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
lean_inc(v_p_3900_);
v___x_3903_ = lean_string_utf8_set(v_s_3899_, v_p_3900_, v___y_3902_);
v___x_3904_ = l_Char_utf8Size(v___y_3902_);
v___x_3905_ = lean_nat_add(v_p_3900_, v___x_3904_);
lean_dec(v___x_3904_);
lean_dec(v_p_3900_);
v_s_3899_ = v___x_3903_;
v_p_3900_ = v___x_3905_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(lean_object* v_name_3928_){
_start:
{
lean_object* v___x_3929_; lean_object* v_n_3930_; uint8_t v___y_3932_; lean_object* v___x_3953_; uint8_t v___x_3954_; 
v___x_3929_ = lean_unsigned_to_nat(0u);
v_n_3930_ = l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField_spec__0(v_name_3928_, v___x_3929_);
v___x_3953_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__10));
v___x_3954_ = lean_string_dec_eq(v_n_3930_, v___x_3953_);
if (v___x_3954_ == 0)
{
lean_object* v___x_3955_; uint8_t v___x_3956_; 
v___x_3955_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__11));
v___x_3956_ = lean_string_dec_eq(v_n_3930_, v___x_3955_);
v___y_3932_ = v___x_3956_;
goto v___jp_3931_;
}
else
{
v___y_3932_ = v___x_3954_;
goto v___jp_3931_;
}
v___jp_3931_:
{
if (v___y_3932_ == 0)
{
lean_object* v___x_3933_; uint8_t v___x_3934_; 
v___x_3933_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0));
v___x_3934_ = lean_string_dec_eq(v_n_3930_, v___x_3933_);
if (v___x_3934_ == 0)
{
lean_object* v___x_3935_; uint8_t v___x_3936_; 
v___x_3935_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1));
v___x_3936_ = lean_string_dec_eq(v_n_3930_, v___x_3935_);
if (v___x_3936_ == 0)
{
lean_object* v___x_3937_; uint8_t v___x_3938_; 
v___x_3937_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2));
v___x_3938_ = lean_string_dec_eq(v_n_3930_, v___x_3937_);
if (v___x_3938_ == 0)
{
lean_object* v___x_3939_; uint8_t v___x_3940_; 
v___x_3939_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3));
v___x_3940_ = lean_string_dec_eq(v_n_3930_, v___x_3939_);
if (v___x_3940_ == 0)
{
lean_object* v___x_3941_; uint8_t v___x_3942_; 
v___x_3941_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4));
v___x_3942_ = lean_string_dec_eq(v_n_3930_, v___x_3941_);
if (v___x_3942_ == 0)
{
lean_object* v___x_3943_; uint8_t v___x_3944_; 
v___x_3943_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__5));
v___x_3944_ = lean_string_dec_eq(v_n_3930_, v___x_3943_);
if (v___x_3944_ == 0)
{
lean_object* v___x_3945_; uint8_t v___x_3946_; 
v___x_3945_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__6));
v___x_3946_ = lean_string_dec_eq(v_n_3930_, v___x_3945_);
if (v___x_3946_ == 0)
{
lean_object* v___x_3947_; uint8_t v___x_3948_; 
v___x_3947_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__7));
v___x_3948_ = lean_string_dec_eq(v_n_3930_, v___x_3947_);
if (v___x_3948_ == 0)
{
lean_object* v___x_3949_; uint8_t v___x_3950_; 
v___x_3949_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__8));
v___x_3950_ = lean_string_dec_eq(v_n_3930_, v___x_3949_);
if (v___x_3950_ == 0)
{
lean_object* v___x_3951_; uint8_t v___x_3952_; 
v___x_3951_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__9));
v___x_3952_ = lean_string_dec_eq(v_n_3930_, v___x_3951_);
lean_dec_ref(v_n_3930_);
return v___x_3952_;
}
else
{
lean_dec_ref(v_n_3930_);
return v___x_3950_;
}
}
else
{
lean_dec_ref(v_n_3930_);
return v___x_3948_;
}
}
else
{
lean_dec_ref(v_n_3930_);
return v___x_3946_;
}
}
else
{
lean_dec_ref(v_n_3930_);
return v___x_3944_;
}
}
else
{
lean_dec_ref(v_n_3930_);
return v___x_3942_;
}
}
else
{
lean_dec_ref(v_n_3930_);
return v___x_3940_;
}
}
else
{
lean_dec_ref(v_n_3930_);
return v___x_3938_;
}
}
else
{
lean_dec_ref(v_n_3930_);
return v___x_3936_;
}
}
else
{
lean_dec_ref(v_n_3930_);
return v___x_3934_;
}
}
else
{
lean_dec_ref(v_n_3930_);
return v___y_3932_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___boxed(lean_object* v_name_3957_){
_start:
{
uint8_t v_res_3958_; lean_object* v_r_3959_; 
v_res_3958_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_name_3957_);
v_r_3959_ = lean_box(v_res_3958_);
return v_r_3959_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader(lean_object* v_limits_3961_, lean_object* v_a_3962_){
_start:
{
lean_object* v___x_3963_; 
v___x_3963_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_3961_, v_a_3962_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v_res_3964_; 
v_res_3964_ = lean_ctor_get(v___x_3963_, 1);
lean_inc(v_res_3964_);
if (lean_obj_tag(v_res_3964_) == 1)
{
lean_object* v_val_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3986_; 
v_val_3965_ = lean_ctor_get(v_res_3964_, 0);
v_isSharedCheck_3986_ = !lean_is_exclusive(v_res_3964_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3967_ = v_res_3964_;
v_isShared_3968_ = v_isSharedCheck_3986_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_val_3965_);
lean_dec(v_res_3964_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3986_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v_pos_3969_; lean_object* v_fst_3970_; uint8_t v___x_3971_; 
v_pos_3969_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_pos_3969_);
v_fst_3970_ = lean_ctor_get(v_val_3965_, 0);
lean_inc_n(v_fst_3970_, 2);
lean_dec(v_val_3965_);
v___x_3971_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_fst_3970_);
if (v___x_3971_ == 0)
{
lean_dec(v_fst_3970_);
lean_dec(v_pos_3969_);
lean_del_object(v___x_3967_);
return v___x_3963_;
}
else
{
lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3983_; 
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3983_ == 0)
{
lean_object* v_unused_3984_; lean_object* v_unused_3985_; 
v_unused_3984_ = lean_ctor_get(v___x_3963_, 1);
lean_dec(v_unused_3984_);
v_unused_3985_ = lean_ctor_get(v___x_3963_, 0);
lean_dec(v_unused_3985_);
v___x_3973_ = v___x_3963_;
v_isShared_3974_ = v_isSharedCheck_3983_;
goto v_resetjp_3972_;
}
else
{
lean_dec(v___x_3963_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3983_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3978_; 
v___x_3975_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___closed__0));
v___x_3976_ = lean_string_append(v___x_3975_, v_fst_3970_);
lean_dec(v_fst_3970_);
if (v_isShared_3968_ == 0)
{
lean_ctor_set(v___x_3967_, 0, v___x_3976_);
v___x_3978_ = v___x_3967_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v___x_3976_);
v___x_3978_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
lean_object* v___x_3980_; 
if (v_isShared_3974_ == 0)
{
lean_ctor_set_tag(v___x_3973_, 1);
lean_ctor_set(v___x_3973_, 1, v___x_3978_);
v___x_3980_ = v___x_3973_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_pos_3969_);
lean_ctor_set(v_reuseFailAlloc_3981_, 1, v___x_3978_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
}
}
}
else
{
lean_dec(v_res_3964_);
return v___x_3963_;
}
}
else
{
return v___x_3963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___boxed(lean_object* v_limits_3987_, lean_object* v_a_3988_){
_start:
{
lean_object* v_res_3989_; 
v_res_3989_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader(v_limits_3987_, v_a_3988_);
lean_dec_ref(v_limits_3987_);
return v_res_3989_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailers(lean_object* v_limits_3990_, lean_object* v_a_3991_){
_start:
{
lean_object* v_maxTrailerHeaders_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
v_maxTrailerHeaders_3992_ = lean_ctor_get(v_limits_3990_, 17);
lean_inc(v_maxTrailerHeaders_3992_);
v___x_3993_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___boxed), 2, 1);
lean_closure_set(v___x_3993_, 0, v_limits_3990_);
v___x_3994_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___x_3993_, v_maxTrailerHeaders_3992_, v_a_3991_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_object* v_pos_3995_; lean_object* v_res_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v_pos_3995_ = lean_ctor_get(v___x_3994_, 0);
lean_inc(v_pos_3995_);
v_res_3996_ = lean_ctor_get(v___x_3994_, 1);
lean_inc(v_res_3996_);
lean_dec_ref_known(v___x_3994_, 2);
v___x_3997_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3998_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3997_, v_pos_3995_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_pos_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4006_; 
v_pos_3999_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4006_ == 0)
{
lean_object* v_unused_4007_; 
v_unused_4007_ = lean_ctor_get(v___x_3998_, 1);
lean_dec(v_unused_4007_);
v___x_4001_ = v___x_3998_;
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_pos_3999_);
lean_dec(v___x_3998_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4004_; 
if (v_isShared_4002_ == 0)
{
lean_ctor_set(v___x_4001_, 1, v_res_3996_);
v___x_4004_ = v___x_4001_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_pos_3999_);
lean_ctor_set(v_reuseFailAlloc_4005_, 1, v_res_3996_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
return v___x_4004_;
}
}
}
else
{
lean_object* v_pos_4008_; lean_object* v_err_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4016_; 
lean_dec(v_res_3996_);
v_pos_4008_ = lean_ctor_get(v___x_3998_, 0);
v_err_4009_ = lean_ctor_get(v___x_3998_, 1);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_4011_ = v___x_3998_;
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_err_4009_);
lean_inc(v_pos_4008_);
lean_dec(v___x_3998_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4014_; 
if (v_isShared_4012_ == 0)
{
v___x_4014_ = v___x_4011_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_pos_4008_);
lean_ctor_set(v_reuseFailAlloc_4015_, 1, v_err_4009_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
}
else
{
return v___x_3994_;
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(uint8_t v_c_4017_){
_start:
{
uint32_t v___x_4018_; uint32_t v___x_4024_; uint8_t v___x_4025_; 
v___x_4018_ = lean_uint8_to_uint32(v_c_4017_);
v___x_4024_ = 33;
v___x_4025_ = lean_uint32_dec_le(v___x_4024_, v___x_4018_);
if (v___x_4025_ == 0)
{
goto v___jp_4019_;
}
else
{
uint32_t v___x_4026_; uint8_t v___x_4027_; 
v___x_4026_ = 126;
v___x_4027_ = lean_uint32_dec_le(v___x_4018_, v___x_4026_);
if (v___x_4027_ == 0)
{
goto v___jp_4019_;
}
else
{
return v___x_4027_;
}
}
v___jp_4019_:
{
uint32_t v___x_4020_; uint8_t v___x_4021_; 
v___x_4020_ = 32;
v___x_4021_ = lean_uint32_dec_eq(v___x_4018_, v___x_4020_);
if (v___x_4021_ == 0)
{
uint32_t v___x_4022_; uint8_t v___x_4023_; 
v___x_4022_ = 9;
v___x_4023_ = lean_uint32_dec_eq(v___x_4018_, v___x_4022_);
return v___x_4023_;
}
else
{
return v___x_4021_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte___boxed(lean_object* v_c_4028_){
_start:
{
uint8_t v_c_boxed_4029_; uint8_t v_res_4030_; lean_object* v_r_4031_; 
v_c_boxed_4029_ = lean_unbox(v_c_4028_);
v_res_4030_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(v_c_boxed_4029_);
v_r_4031_ = lean_box(v_res_4030_);
return v_r_4031_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___lam__0(uint8_t v___y_4032_){
_start:
{
uint32_t v___x_4033_; uint32_t v___x_4039_; uint8_t v___x_4040_; 
v___x_4033_ = lean_uint8_to_uint32(v___y_4032_);
v___x_4039_ = 33;
v___x_4040_ = lean_uint32_dec_le(v___x_4039_, v___x_4033_);
if (v___x_4040_ == 0)
{
goto v___jp_4034_;
}
else
{
uint32_t v___x_4041_; uint8_t v___x_4042_; 
v___x_4041_ = 126;
v___x_4042_ = lean_uint32_dec_le(v___x_4033_, v___x_4041_);
if (v___x_4042_ == 0)
{
goto v___jp_4034_;
}
else
{
return v___x_4042_;
}
}
v___jp_4034_:
{
uint32_t v___x_4035_; uint8_t v___x_4036_; 
v___x_4035_ = 32;
v___x_4036_ = lean_uint32_dec_eq(v___x_4033_, v___x_4035_);
if (v___x_4036_ == 0)
{
uint32_t v___x_4037_; uint8_t v___x_4038_; 
v___x_4037_ = 9;
v___x_4038_ = lean_uint32_dec_eq(v___x_4033_, v___x_4037_);
return v___x_4038_;
}
else
{
return v___x_4036_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___lam__0___boxed(lean_object* v___y_4043_){
_start:
{
uint8_t v___y_225__boxed_4044_; uint8_t v_res_4045_; lean_object* v_r_4046_; 
v___y_225__boxed_4044_ = lean_unbox(v___y_4043_);
v_res_4045_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___lam__0(v___y_225__boxed_4044_);
v_r_4046_ = lean_box(v_res_4045_);
return v_r_4046_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(lean_object* v_limits_4048_, lean_object* v_a_4049_){
_start:
{
lean_object* v_maxReasonPhraseLength_4050_; lean_object* v___f_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v_snd_4054_; lean_object* v_snd_4055_; uint8_t v___x_4056_; 
v_maxReasonPhraseLength_4050_ = lean_ctor_get(v_limits_4048_, 16);
v___f_4051_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___closed__0));
v___x_4052_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_4049_);
v___x_4053_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_4051_, v_maxReasonPhraseLength_4050_, v___x_4052_, v_a_4049_);
v_snd_4054_ = lean_ctor_get(v___x_4053_, 1);
lean_inc(v_snd_4054_);
v_snd_4055_ = lean_ctor_get(v_snd_4054_, 1);
v___x_4056_ = lean_unbox(v_snd_4055_);
if (v___x_4056_ == 0)
{
lean_object* v_fst_4057_; lean_object* v_fst_4058_; lean_object* v_array_4059_; lean_object* v_idx_4060_; lean_object* v_lower_4062_; lean_object* v_upper_4063_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___y_4075_; uint8_t v___x_4077_; 
v_fst_4057_ = lean_ctor_get(v___x_4053_, 0);
lean_inc(v_fst_4057_);
lean_dec_ref(v___x_4053_);
v_fst_4058_ = lean_ctor_get(v_snd_4054_, 0);
lean_inc(v_fst_4058_);
lean_dec(v_snd_4054_);
v_array_4059_ = lean_ctor_get(v_a_4049_, 0);
lean_inc_ref(v_array_4059_);
v_idx_4060_ = lean_ctor_get(v_a_4049_, 1);
lean_inc(v_idx_4060_);
lean_dec_ref(v_a_4049_);
v___x_4072_ = lean_nat_add(v_idx_4060_, v_fst_4057_);
lean_dec(v_fst_4057_);
v___x_4073_ = lean_byte_array_size(v_array_4059_);
v___x_4077_ = lean_nat_dec_le(v_idx_4060_, v___x_4052_);
if (v___x_4077_ == 0)
{
v___y_4075_ = v_idx_4060_;
goto v___jp_4074_;
}
else
{
lean_dec(v_idx_4060_);
v___y_4075_ = v___x_4052_;
goto v___jp_4074_;
}
v___jp_4061_:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; uint8_t v___x_4066_; 
v___x_4064_ = l_ByteArray_toByteSlice(v_array_4059_, v_lower_4062_, v_upper_4063_);
v___x_4065_ = l_ByteSlice_toByteArray(v___x_4064_);
v___x_4066_ = lean_string_validate_utf8(v___x_4065_);
if (v___x_4066_ == 0)
{
lean_object* v___x_4067_; lean_object* v___x_4068_; 
lean_dec_ref(v___x_4065_);
v___x_4067_ = lean_box(0);
v___x_4068_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_4067_, v_fst_4058_);
return v___x_4068_;
}
else
{
lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v___x_4069_ = lean_string_from_utf8_unchecked(v___x_4065_);
v___x_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4069_);
v___x_4071_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_4070_, v_fst_4058_);
lean_dec_ref_known(v___x_4070_, 1);
return v___x_4071_;
}
}
v___jp_4074_:
{
uint8_t v___x_4076_; 
v___x_4076_ = lean_nat_dec_le(v___x_4072_, v___x_4073_);
if (v___x_4076_ == 0)
{
lean_dec(v___x_4072_);
v_lower_4062_ = v___y_4075_;
v_upper_4063_ = v___x_4073_;
goto v___jp_4061_;
}
else
{
v_lower_4062_ = v___y_4075_;
v_upper_4063_ = v___x_4072_;
goto v___jp_4061_;
}
}
}
else
{
lean_object* v_fst_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4086_; 
lean_dec_ref(v___x_4053_);
lean_dec_ref(v_a_4049_);
v_fst_4078_ = lean_ctor_get(v_snd_4054_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v_snd_4054_);
if (v_isSharedCheck_4086_ == 0)
{
lean_object* v_unused_4087_; 
v_unused_4087_ = lean_ctor_get(v_snd_4054_, 1);
lean_dec(v_unused_4087_);
v___x_4080_ = v_snd_4054_;
v_isShared_4081_ = v_isSharedCheck_4086_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_fst_4078_);
lean_dec(v_snd_4054_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4086_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4082_; lean_object* v___x_4084_; 
v___x_4082_ = lean_box(0);
if (v_isShared_4081_ == 0)
{
lean_ctor_set_tag(v___x_4080_, 1);
lean_ctor_set(v___x_4080_, 1, v___x_4082_);
v___x_4084_ = v___x_4080_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_fst_4078_);
lean_ctor_set(v_reuseFailAlloc_4085_, 1, v___x_4082_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___boxed(lean_object* v_limits_4088_, lean_object* v_a_4089_){
_start:
{
lean_object* v_res_4090_; 
v_res_4090_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_4088_, v_a_4089_);
lean_dec_ref(v_limits_4088_);
return v_res_4090_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(lean_object* v___x_4091_, lean_object* v___x_4092_, lean_object* v_x_4093_){
_start:
{
if (lean_obj_tag(v_x_4093_) == 0)
{
uint8_t v___x_4094_; 
v___x_4094_ = 1;
return v___x_4094_;
}
else
{
lean_object* v_head_4095_; lean_object* v_tail_4096_; uint8_t v___x_4097_; uint32_t v___x_4100_; uint32_t v___x_4101_; uint8_t v___x_4102_; 
v_head_4095_ = lean_ctor_get(v_x_4093_, 0);
v_tail_4096_ = lean_ctor_get(v_x_4093_, 1);
v___x_4097_ = lean_nat_dec_lt(v___x_4091_, v___x_4092_);
v___x_4100_ = 9;
v___x_4101_ = lean_unbox_uint32(v_head_4095_);
v___x_4102_ = lean_uint32_dec_eq(v___x_4101_, v___x_4100_);
if (v___x_4102_ == 0)
{
uint32_t v___x_4103_; uint32_t v___x_4104_; uint8_t v___x_4105_; 
v___x_4103_ = 32;
v___x_4104_ = lean_unbox_uint32(v_head_4095_);
v___x_4105_ = lean_uint32_dec_eq(v___x_4104_, v___x_4103_);
if (v___x_4105_ == 0)
{
uint32_t v___x_4106_; uint32_t v___x_4107_; uint8_t v___x_4108_; 
v___x_4106_ = 33;
v___x_4107_ = lean_unbox_uint32(v_head_4095_);
v___x_4108_ = lean_uint32_dec_le(v___x_4106_, v___x_4107_);
if (v___x_4108_ == 0)
{
return v___x_4108_;
}
else
{
uint32_t v___x_4109_; uint32_t v___x_4110_; uint8_t v___x_4111_; 
v___x_4109_ = 126;
v___x_4110_ = lean_unbox_uint32(v_head_4095_);
v___x_4111_ = lean_uint32_dec_le(v___x_4110_, v___x_4109_);
if (v___x_4111_ == 0)
{
return v___x_4111_;
}
else
{
goto v___jp_4098_;
}
}
}
else
{
goto v___jp_4098_;
}
}
else
{
goto v___jp_4098_;
}
v___jp_4098_:
{
if (v___x_4097_ == 0)
{
return v___x_4097_;
}
else
{
v_x_4093_ = v_tail_4096_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0___boxed(lean_object* v___x_4112_, lean_object* v___x_4113_, lean_object* v_x_4114_){
_start:
{
uint8_t v_res_4115_; lean_object* v_r_4116_; 
v_res_4115_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v___x_4112_, v___x_4113_, v_x_4114_);
lean_dec(v_x_4114_);
lean_dec(v___x_4113_);
lean_dec(v___x_4112_);
v_r_4116_ = lean_box(v_res_4115_);
return v_r_4116_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(lean_object* v_limits_4120_, lean_object* v_a_4121_){
_start:
{
lean_object* v___y_4123_; lean_object* v_array_4129_; lean_object* v_idx_4130_; lean_object* v___x_4131_; uint8_t v___x_4132_; 
v_array_4129_ = lean_ctor_get(v_a_4121_, 0);
v_idx_4130_ = lean_ctor_get(v_a_4121_, 1);
v___x_4131_ = lean_byte_array_size(v_array_4129_);
v___x_4132_ = lean_nat_dec_lt(v_idx_4130_, v___x_4131_);
if (v___x_4132_ == 0)
{
lean_object* v___x_4133_; lean_object* v___x_4134_; 
v___x_4133_ = lean_box(0);
v___x_4134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4134_, 0, v_a_4121_);
lean_ctor_set(v___x_4134_, 1, v___x_4133_);
return v___x_4134_;
}
else
{
uint8_t v_c_4135_; uint8_t v___x_4136_; uint8_t v___x_4137_; 
v_c_4135_ = lean_byte_array_fget(v_array_4129_, v_idx_4130_);
v___x_4136_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3);
v___x_4137_ = lean_uint8_dec_le(v___x_4136_, v_c_4135_);
if (v___x_4137_ == 0)
{
goto v___jp_4126_;
}
else
{
uint8_t v___x_4138_; uint8_t v___x_4139_; 
v___x_4138_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4);
v___x_4139_ = lean_uint8_dec_le(v_c_4135_, v___x_4138_);
if (v___x_4139_ == 0)
{
goto v___jp_4126_;
}
else
{
lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4232_; 
lean_inc(v_idx_4130_);
lean_inc_ref(v_array_4129_);
v_isSharedCheck_4232_ = !lean_is_exclusive(v_a_4121_);
if (v_isSharedCheck_4232_ == 0)
{
lean_object* v_unused_4233_; lean_object* v_unused_4234_; 
v_unused_4233_ = lean_ctor_get(v_a_4121_, 1);
lean_dec(v_unused_4233_);
v_unused_4234_ = lean_ctor_get(v_a_4121_, 0);
lean_dec(v_unused_4234_);
v___x_4141_ = v_a_4121_;
v_isShared_4142_ = v_isSharedCheck_4232_;
goto v_resetjp_4140_;
}
else
{
lean_dec(v_a_4121_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4232_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v_it_x27_4146_; 
v___x_4143_ = lean_unsigned_to_nat(1u);
v___x_4144_ = lean_nat_add(v_idx_4130_, v___x_4143_);
lean_dec(v_idx_4130_);
lean_inc(v___x_4144_);
lean_inc_ref(v_array_4129_);
if (v_isShared_4142_ == 0)
{
lean_ctor_set(v___x_4141_, 1, v___x_4144_);
v_it_x27_4146_ = v___x_4141_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_array_4129_);
lean_ctor_set(v_reuseFailAlloc_4231_, 1, v___x_4144_);
v_it_x27_4146_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
uint8_t v___x_4150_; 
v___x_4150_ = lean_nat_dec_lt(v___x_4144_, v___x_4131_);
if (v___x_4150_ == 0)
{
lean_object* v___x_4151_; lean_object* v___x_4152_; 
lean_dec(v___x_4144_);
lean_dec_ref(v_array_4129_);
v___x_4151_ = lean_box(0);
v___x_4152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4152_, 0, v_it_x27_4146_);
lean_ctor_set(v___x_4152_, 1, v___x_4151_);
return v___x_4152_;
}
else
{
uint8_t v_c_4153_; uint8_t v___x_4154_; 
v_c_4153_ = lean_byte_array_fget(v_array_4129_, v___x_4144_);
v___x_4154_ = lean_uint8_dec_le(v___x_4136_, v_c_4153_);
if (v___x_4154_ == 0)
{
lean_dec(v___x_4144_);
lean_dec_ref(v_array_4129_);
goto v___jp_4147_;
}
else
{
uint8_t v___x_4155_; 
v___x_4155_ = lean_uint8_dec_le(v_c_4153_, v___x_4138_);
if (v___x_4155_ == 0)
{
lean_dec(v___x_4144_);
lean_dec_ref(v_array_4129_);
goto v___jp_4147_;
}
else
{
lean_object* v___x_4156_; lean_object* v_it_x27_4157_; uint8_t v___x_4161_; 
lean_dec_ref(v_it_x27_4146_);
v___x_4156_ = lean_nat_add(v___x_4144_, v___x_4143_);
lean_dec(v___x_4144_);
lean_inc(v___x_4156_);
lean_inc_ref(v_array_4129_);
v_it_x27_4157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_4157_, 0, v_array_4129_);
lean_ctor_set(v_it_x27_4157_, 1, v___x_4156_);
v___x_4161_ = lean_nat_dec_lt(v___x_4156_, v___x_4131_);
if (v___x_4161_ == 0)
{
lean_object* v___x_4162_; lean_object* v___x_4163_; 
lean_dec(v___x_4156_);
lean_dec_ref(v_array_4129_);
v___x_4162_ = lean_box(0);
v___x_4163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4163_, 0, v_it_x27_4157_);
lean_ctor_set(v___x_4163_, 1, v___x_4162_);
return v___x_4163_;
}
else
{
uint8_t v_c_4164_; uint8_t v___x_4165_; 
v_c_4164_ = lean_byte_array_fget(v_array_4129_, v___x_4156_);
v___x_4165_ = lean_uint8_dec_le(v___x_4136_, v_c_4164_);
if (v___x_4165_ == 0)
{
lean_dec(v___x_4156_);
lean_dec_ref(v_array_4129_);
goto v___jp_4158_;
}
else
{
uint8_t v___x_4166_; 
v___x_4166_ = lean_uint8_dec_le(v_c_4164_, v___x_4138_);
if (v___x_4166_ == 0)
{
lean_dec(v___x_4156_);
lean_dec_ref(v_array_4129_);
goto v___jp_4158_;
}
else
{
lean_object* v___x_4167_; lean_object* v_it_x27_4168_; uint8_t v___x_4169_; 
lean_dec_ref_known(v_it_x27_4157_, 2);
v___x_4167_ = lean_nat_add(v___x_4156_, v___x_4143_);
lean_dec(v___x_4156_);
lean_inc(v___x_4167_);
lean_inc_ref(v_array_4129_);
v_it_x27_4168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_4168_, 0, v_array_4129_);
lean_ctor_set(v_it_x27_4168_, 1, v___x_4167_);
v___x_4169_ = lean_nat_dec_lt(v___x_4167_, v___x_4131_);
if (v___x_4169_ == 0)
{
lean_object* v___x_4170_; lean_object* v___x_4171_; 
lean_dec(v___x_4167_);
lean_dec_ref(v_array_4129_);
v___x_4170_ = lean_box(0);
v___x_4171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4171_, 0, v_it_x27_4168_);
lean_ctor_set(v___x_4171_, 1, v___x_4170_);
return v___x_4171_;
}
else
{
uint8_t v___x_4172_; uint8_t v_got_4173_; uint8_t v___x_4174_; 
v___x_4172_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v_got_4173_ = lean_byte_array_fget(v_array_4129_, v___x_4167_);
v___x_4174_ = lean_uint8_dec_eq(v_got_4173_, v___x_4172_);
if (v___x_4174_ == 0)
{
lean_object* v___x_4175_; lean_object* v___x_4176_; 
lean_dec(v___x_4167_);
lean_dec_ref(v_array_4129_);
v___x_4175_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7);
v___x_4176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4176_, 0, v_it_x27_4168_);
lean_ctor_set(v___x_4176_, 1, v___x_4175_);
return v___x_4176_;
}
else
{
uint32_t v___x_4177_; uint32_t v___x_4178_; uint32_t v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v_pos_4194_; lean_object* v_res_4195_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
lean_dec_ref_known(v_it_x27_4168_, 2);
v___x_4177_ = lean_uint8_to_uint32(v_c_4135_);
v___x_4178_ = lean_uint8_to_uint32(v_c_4153_);
v___x_4179_ = lean_uint8_to_uint32(v_c_4164_);
v___x_4180_ = lean_uint32_to_nat(v___x_4177_);
v___x_4181_ = lean_unsigned_to_nat(48u);
v___x_4182_ = lean_nat_sub(v___x_4180_, v___x_4181_);
lean_dec(v___x_4180_);
v___x_4183_ = lean_unsigned_to_nat(100u);
v___x_4184_ = lean_nat_mul(v___x_4182_, v___x_4183_);
lean_dec(v___x_4182_);
v___x_4185_ = lean_uint32_to_nat(v___x_4178_);
v___x_4186_ = lean_nat_sub(v___x_4185_, v___x_4181_);
lean_dec(v___x_4185_);
v___x_4187_ = lean_unsigned_to_nat(10u);
v___x_4188_ = lean_nat_mul(v___x_4186_, v___x_4187_);
lean_dec(v___x_4186_);
v___x_4189_ = lean_nat_add(v___x_4184_, v___x_4188_);
lean_dec(v___x_4188_);
lean_dec(v___x_4184_);
v___x_4190_ = lean_uint32_to_nat(v___x_4179_);
v___x_4191_ = lean_nat_sub(v___x_4190_, v___x_4181_);
lean_dec(v___x_4190_);
v___x_4192_ = lean_nat_add(v___x_4189_, v___x_4191_);
lean_dec(v___x_4191_);
lean_dec(v___x_4189_);
v___x_4203_ = lean_nat_add(v___x_4167_, v___x_4143_);
v___x_4204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4204_, 0, v_array_4129_);
lean_ctor_set(v___x_4204_, 1, v___x_4203_);
v___x_4205_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_4120_, v___x_4204_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_pos_4206_; lean_object* v_res_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
v_pos_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_pos_4206_);
v_res_4207_ = lean_ctor_get(v___x_4205_, 1);
lean_inc(v_res_4207_);
lean_dec_ref_known(v___x_4205_, 2);
v___x_4208_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_4209_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_4208_, v_pos_4206_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_object* v_pos_4210_; 
v_pos_4210_ = lean_ctor_get(v___x_4209_, 0);
lean_inc(v_pos_4210_);
lean_dec_ref_known(v___x_4209_, 2);
v_pos_4194_ = v_pos_4210_;
v_res_4195_ = v_res_4207_;
goto v___jp_4193_;
}
else
{
lean_object* v_pos_4211_; lean_object* v_err_4212_; lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4219_; 
lean_dec(v_res_4207_);
lean_dec(v___x_4192_);
lean_dec(v___x_4167_);
v_pos_4211_ = lean_ctor_get(v___x_4209_, 0);
v_err_4212_ = lean_ctor_get(v___x_4209_, 1);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4214_ = v___x_4209_;
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
else
{
lean_inc(v_err_4212_);
lean_inc(v_pos_4211_);
lean_dec(v___x_4209_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
lean_object* v___x_4217_; 
if (v_isShared_4215_ == 0)
{
v___x_4217_ = v___x_4214_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_pos_4211_);
lean_ctor_set(v_reuseFailAlloc_4218_, 1, v_err_4212_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_pos_4220_; lean_object* v_res_4221_; 
v_pos_4220_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_pos_4220_);
v_res_4221_ = lean_ctor_get(v___x_4205_, 1);
lean_inc(v_res_4221_);
lean_dec_ref_known(v___x_4205_, 2);
v_pos_4194_ = v_pos_4220_;
v_res_4195_ = v_res_4221_;
goto v___jp_4193_;
}
else
{
lean_object* v_pos_4222_; lean_object* v_err_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4230_; 
lean_dec(v___x_4192_);
lean_dec(v___x_4167_);
v_pos_4222_ = lean_ctor_get(v___x_4205_, 0);
v_err_4223_ = lean_ctor_get(v___x_4205_, 1);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4225_ = v___x_4205_;
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_err_4223_);
lean_inc(v_pos_4222_);
lean_dec(v___x_4205_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
if (v_isShared_4226_ == 0)
{
v___x_4228_ = v___x_4225_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_pos_4222_);
lean_ctor_set(v_reuseFailAlloc_4229_, 1, v_err_4223_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
}
}
v___jp_4193_:
{
lean_object* v___x_4196_; uint8_t v___x_4197_; 
lean_inc_ref(v_res_4195_);
v___x_4196_ = lean_string_data(v_res_4195_);
v___x_4197_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v___x_4167_, v___x_4131_, v___x_4196_);
lean_dec(v___x_4196_);
lean_dec(v___x_4167_);
if (v___x_4197_ == 0)
{
lean_dec_ref(v_res_4195_);
lean_dec(v___x_4192_);
v___y_4123_ = v_pos_4194_;
goto v___jp_4122_;
}
else
{
lean_object* v___x_4198_; uint16_t v___x_4199_; lean_object* v___x_4200_; 
v___x_4198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4198_, 0, v_res_4195_);
v___x_4199_ = lean_uint16_of_nat(v___x_4192_);
lean_dec(v___x_4192_);
v___x_4200_ = l_Std_Http_Status_ofCode(v___x_4198_, v___x_4199_);
if (lean_obj_tag(v___x_4200_) == 1)
{
lean_object* v_val_4201_; lean_object* v___x_4202_; 
v_val_4201_ = lean_ctor_get(v___x_4200_, 0);
lean_inc(v_val_4201_);
lean_dec_ref_known(v___x_4200_, 1);
v___x_4202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4202_, 0, v_pos_4194_);
lean_ctor_set(v___x_4202_, 1, v_val_4201_);
return v___x_4202_;
}
else
{
lean_dec(v___x_4200_);
v___y_4123_ = v_pos_4194_;
goto v___jp_4122_;
}
}
}
}
}
}
}
}
v___jp_4158_:
{
lean_object* v___x_4159_; lean_object* v___x_4160_; 
v___x_4159_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_4160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4160_, 0, v_it_x27_4157_);
lean_ctor_set(v___x_4160_, 1, v___x_4159_);
return v___x_4160_;
}
}
}
}
v___jp_4147_:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4148_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_4149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4149_, 0, v_it_x27_4146_);
lean_ctor_set(v___x_4149_, 1, v___x_4148_);
return v___x_4149_;
}
}
}
}
}
}
v___jp_4122_:
{
lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4124_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__1));
v___x_4125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4125_, 0, v___y_4123_);
lean_ctor_set(v___x_4125_, 1, v___x_4124_);
return v___x_4125_;
}
v___jp_4126_:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; 
v___x_4127_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_4128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4128_, 0, v_a_4121_);
lean_ctor_set(v___x_4128_, 1, v___x_4127_);
return v___x_4128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___boxed(lean_object* v_limits_4235_, lean_object* v_a_4236_){
_start:
{
lean_object* v_res_4237_; 
v_res_4237_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_4235_, v_a_4236_);
lean_dec_ref(v_limits_4235_);
return v_res_4237_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine(lean_object* v_limits_4238_, lean_object* v_a_4239_){
_start:
{
lean_object* v___y_4241_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; uint8_t v___y_4248_; lean_object* v_pos_4256_; lean_object* v_res_4257_; lean_object* v___x_4285_; 
v___x_4285_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_4239_);
if (lean_obj_tag(v___x_4285_) == 0)
{
lean_object* v_pos_4286_; lean_object* v_res_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4317_; 
v_pos_4286_ = lean_ctor_get(v___x_4285_, 0);
v_res_4287_ = lean_ctor_get(v___x_4285_, 1);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4285_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4289_ = v___x_4285_;
v_isShared_4290_ = v_isSharedCheck_4317_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_res_4287_);
lean_inc(v_pos_4286_);
lean_dec(v___x_4285_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4317_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v_array_4291_; lean_object* v_idx_4292_; lean_object* v___x_4293_; uint8_t v___x_4294_; 
v_array_4291_ = lean_ctor_get(v_pos_4286_, 0);
v_idx_4292_ = lean_ctor_get(v_pos_4286_, 1);
v___x_4293_ = lean_byte_array_size(v_array_4291_);
v___x_4294_ = lean_nat_dec_lt(v_idx_4292_, v___x_4293_);
if (v___x_4294_ == 0)
{
lean_object* v___x_4295_; lean_object* v___x_4297_; 
lean_dec(v_res_4287_);
v___x_4295_ = lean_box(0);
if (v_isShared_4290_ == 0)
{
lean_ctor_set_tag(v___x_4289_, 1);
lean_ctor_set(v___x_4289_, 1, v___x_4295_);
v___x_4297_ = v___x_4289_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_pos_4286_);
lean_ctor_set(v_reuseFailAlloc_4298_, 1, v___x_4295_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
else
{
uint8_t v___x_4299_; uint8_t v_got_4300_; uint8_t v___x_4301_; 
v___x_4299_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v_got_4300_ = lean_byte_array_fget(v_array_4291_, v_idx_4292_);
v___x_4301_ = lean_uint8_dec_eq(v_got_4300_, v___x_4299_);
if (v___x_4301_ == 0)
{
lean_object* v___x_4302_; lean_object* v___x_4304_; 
lean_dec(v_res_4287_);
v___x_4302_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7);
if (v_isShared_4290_ == 0)
{
lean_ctor_set_tag(v___x_4289_, 1);
lean_ctor_set(v___x_4289_, 1, v___x_4302_);
v___x_4304_ = v___x_4289_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v_pos_4286_);
lean_ctor_set(v_reuseFailAlloc_4305_, 1, v___x_4302_);
v___x_4304_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
return v___x_4304_;
}
}
else
{
lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4314_; 
lean_inc(v_idx_4292_);
lean_inc_ref(v_array_4291_);
lean_del_object(v___x_4289_);
v_isSharedCheck_4314_ = !lean_is_exclusive(v_pos_4286_);
if (v_isSharedCheck_4314_ == 0)
{
lean_object* v_unused_4315_; lean_object* v_unused_4316_; 
v_unused_4315_ = lean_ctor_get(v_pos_4286_, 1);
lean_dec(v_unused_4315_);
v_unused_4316_ = lean_ctor_get(v_pos_4286_, 0);
lean_dec(v_unused_4316_);
v___x_4307_ = v_pos_4286_;
v_isShared_4308_ = v_isSharedCheck_4314_;
goto v_resetjp_4306_;
}
else
{
lean_dec(v_pos_4286_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4314_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4312_; 
v___x_4309_ = lean_unsigned_to_nat(1u);
v___x_4310_ = lean_nat_add(v_idx_4292_, v___x_4309_);
lean_dec(v_idx_4292_);
if (v_isShared_4308_ == 0)
{
lean_ctor_set(v___x_4307_, 1, v___x_4310_);
v___x_4312_ = v___x_4307_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_array_4291_);
lean_ctor_set(v_reuseFailAlloc_4313_, 1, v___x_4310_);
v___x_4312_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
v_pos_4256_ = v___x_4312_;
v_res_4257_ = v_res_4287_;
goto v___jp_4255_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_4285_) == 0)
{
lean_object* v_pos_4318_; lean_object* v_res_4319_; 
v_pos_4318_ = lean_ctor_get(v___x_4285_, 0);
lean_inc(v_pos_4318_);
v_res_4319_ = lean_ctor_get(v___x_4285_, 1);
lean_inc(v_res_4319_);
lean_dec_ref_known(v___x_4285_, 2);
v_pos_4256_ = v_pos_4318_;
v_res_4257_ = v_res_4319_;
goto v___jp_4255_;
}
else
{
lean_object* v_pos_4320_; lean_object* v_err_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4328_; 
v_pos_4320_ = lean_ctor_get(v___x_4285_, 0);
v_err_4321_ = lean_ctor_get(v___x_4285_, 1);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4285_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4323_ = v___x_4285_;
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_err_4321_);
lean_inc(v_pos_4320_);
lean_dec(v___x_4285_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4326_; 
if (v_isShared_4324_ == 0)
{
v___x_4326_ = v___x_4323_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_pos_4320_);
lean_ctor_set(v_reuseFailAlloc_4327_, 1, v_err_4321_);
v___x_4326_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
return v___x_4326_;
}
}
}
}
v___jp_4240_:
{
lean_object* v___x_4242_; lean_object* v___x_4243_; 
v___x_4242_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
v___x_4243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4243_, 0, v___y_4241_);
lean_ctor_set(v___x_4243_, 1, v___x_4242_);
return v___x_4243_;
}
v___jp_4244_:
{
if (v___y_4248_ == 0)
{
lean_dec(v___y_4247_);
lean_dec(v___y_4245_);
v___y_4241_ = v___y_4246_;
goto v___jp_4240_;
}
else
{
lean_object* v___x_4249_; uint8_t v___x_4250_; 
v___x_4249_ = lean_unsigned_to_nat(0u);
v___x_4250_ = lean_nat_dec_eq(v___y_4245_, v___x_4249_);
lean_dec(v___y_4245_);
if (v___x_4250_ == 0)
{
lean_dec(v___y_4247_);
v___y_4241_ = v___y_4246_;
goto v___jp_4240_;
}
else
{
uint8_t v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; 
v___x_4251_ = 0;
v___x_4252_ = l_Std_Http_Headers_empty;
v___x_4253_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4253_, 0, v___y_4247_);
lean_ctor_set(v___x_4253_, 1, v___x_4252_);
lean_ctor_set_uint8(v___x_4253_, sizeof(void*)*2, v___x_4251_);
v___x_4254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4254_, 0, v___y_4246_);
lean_ctor_set(v___x_4254_, 1, v___x_4253_);
return v___x_4254_;
}
}
}
v___jp_4255_:
{
lean_object* v_fst_4258_; lean_object* v_snd_4259_; lean_object* v___x_4260_; 
v_fst_4258_ = lean_ctor_get(v_res_4257_, 0);
lean_inc(v_fst_4258_);
v_snd_4259_ = lean_ctor_get(v_res_4257_, 1);
lean_inc(v_snd_4259_);
lean_dec_ref(v_res_4257_);
v___x_4260_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_4238_, v_pos_4256_);
if (lean_obj_tag(v___x_4260_) == 0)
{
lean_object* v_pos_4261_; lean_object* v_res_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4275_; 
v_pos_4261_ = lean_ctor_get(v___x_4260_, 0);
v_res_4262_ = lean_ctor_get(v___x_4260_, 1);
v_isSharedCheck_4275_ = !lean_is_exclusive(v___x_4260_);
if (v_isSharedCheck_4275_ == 0)
{
v___x_4264_ = v___x_4260_;
v_isShared_4265_ = v_isSharedCheck_4275_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_res_4262_);
lean_inc(v_pos_4261_);
lean_dec(v___x_4260_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4275_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v___x_4266_; uint8_t v___x_4267_; 
v___x_4266_ = lean_unsigned_to_nat(1u);
v___x_4267_ = lean_nat_dec_eq(v_fst_4258_, v___x_4266_);
lean_dec(v_fst_4258_);
if (v___x_4267_ == 0)
{
lean_del_object(v___x_4264_);
v___y_4245_ = v_snd_4259_;
v___y_4246_ = v_pos_4261_;
v___y_4247_ = v_res_4262_;
v___y_4248_ = v___x_4267_;
goto v___jp_4244_;
}
else
{
uint8_t v___x_4268_; 
v___x_4268_ = lean_nat_dec_eq(v_snd_4259_, v___x_4266_);
if (v___x_4268_ == 0)
{
lean_del_object(v___x_4264_);
v___y_4245_ = v_snd_4259_;
v___y_4246_ = v_pos_4261_;
v___y_4247_ = v_res_4262_;
v___y_4248_ = v___x_4267_;
goto v___jp_4244_;
}
else
{
uint8_t v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4273_; 
lean_dec(v_snd_4259_);
v___x_4269_ = 1;
v___x_4270_ = l_Std_Http_Headers_empty;
v___x_4271_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4271_, 0, v_res_4262_);
lean_ctor_set(v___x_4271_, 1, v___x_4270_);
lean_ctor_set_uint8(v___x_4271_, sizeof(void*)*2, v___x_4269_);
if (v_isShared_4265_ == 0)
{
lean_ctor_set(v___x_4264_, 1, v___x_4271_);
v___x_4273_ = v___x_4264_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v_pos_4261_);
lean_ctor_set(v_reuseFailAlloc_4274_, 1, v___x_4271_);
v___x_4273_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
return v___x_4273_;
}
}
}
}
}
else
{
lean_object* v_pos_4276_; lean_object* v_err_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4284_; 
lean_dec(v_snd_4259_);
lean_dec(v_fst_4258_);
v_pos_4276_ = lean_ctor_get(v___x_4260_, 0);
v_err_4277_ = lean_ctor_get(v___x_4260_, 1);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4260_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4279_ = v___x_4260_;
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_err_4277_);
lean_inc(v_pos_4276_);
lean_dec(v___x_4260_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v___x_4282_; 
if (v_isShared_4280_ == 0)
{
v___x_4282_ = v___x_4279_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_pos_4276_);
lean_ctor_set(v_reuseFailAlloc_4283_, 1, v_err_4277_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine___boxed(lean_object* v_limits_4329_, lean_object* v_a_4330_){
_start:
{
lean_object* v_res_4331_; 
v_res_4331_ = l_Std_Http_Protocol_H1_parseStatusLine(v_limits_4329_, v_a_4330_);
lean_dec_ref(v_limits_4329_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion(lean_object* v_limits_4332_, lean_object* v_a_4333_){
_start:
{
lean_object* v_pos_4335_; lean_object* v_res_4336_; lean_object* v___x_4366_; 
v___x_4366_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_4333_);
if (lean_obj_tag(v___x_4366_) == 0)
{
lean_object* v_pos_4367_; lean_object* v_res_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4398_; 
v_pos_4367_ = lean_ctor_get(v___x_4366_, 0);
v_res_4368_ = lean_ctor_get(v___x_4366_, 1);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___x_4366_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4370_ = v___x_4366_;
v_isShared_4371_ = v_isSharedCheck_4398_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_res_4368_);
lean_inc(v_pos_4367_);
lean_dec(v___x_4366_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4398_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v_array_4372_; lean_object* v_idx_4373_; lean_object* v___x_4374_; uint8_t v___x_4375_; 
v_array_4372_ = lean_ctor_get(v_pos_4367_, 0);
v_idx_4373_ = lean_ctor_get(v_pos_4367_, 1);
v___x_4374_ = lean_byte_array_size(v_array_4372_);
v___x_4375_ = lean_nat_dec_lt(v_idx_4373_, v___x_4374_);
if (v___x_4375_ == 0)
{
lean_object* v___x_4376_; lean_object* v___x_4378_; 
lean_dec(v_res_4368_);
v___x_4376_ = lean_box(0);
if (v_isShared_4371_ == 0)
{
lean_ctor_set_tag(v___x_4370_, 1);
lean_ctor_set(v___x_4370_, 1, v___x_4376_);
v___x_4378_ = v___x_4370_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_pos_4367_);
lean_ctor_set(v_reuseFailAlloc_4379_, 1, v___x_4376_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
else
{
uint8_t v___x_4380_; uint8_t v_got_4381_; uint8_t v___x_4382_; 
v___x_4380_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v_got_4381_ = lean_byte_array_fget(v_array_4372_, v_idx_4373_);
v___x_4382_ = lean_uint8_dec_eq(v_got_4381_, v___x_4380_);
if (v___x_4382_ == 0)
{
lean_object* v___x_4383_; lean_object* v___x_4385_; 
lean_dec(v_res_4368_);
v___x_4383_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7);
if (v_isShared_4371_ == 0)
{
lean_ctor_set_tag(v___x_4370_, 1);
lean_ctor_set(v___x_4370_, 1, v___x_4383_);
v___x_4385_ = v___x_4370_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v_pos_4367_);
lean_ctor_set(v_reuseFailAlloc_4386_, 1, v___x_4383_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
else
{
lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4395_; 
lean_inc(v_idx_4373_);
lean_inc_ref(v_array_4372_);
lean_del_object(v___x_4370_);
v_isSharedCheck_4395_ = !lean_is_exclusive(v_pos_4367_);
if (v_isSharedCheck_4395_ == 0)
{
lean_object* v_unused_4396_; lean_object* v_unused_4397_; 
v_unused_4396_ = lean_ctor_get(v_pos_4367_, 1);
lean_dec(v_unused_4396_);
v_unused_4397_ = lean_ctor_get(v_pos_4367_, 0);
lean_dec(v_unused_4397_);
v___x_4388_ = v_pos_4367_;
v_isShared_4389_ = v_isSharedCheck_4395_;
goto v_resetjp_4387_;
}
else
{
lean_dec(v_pos_4367_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4395_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4393_; 
v___x_4390_ = lean_unsigned_to_nat(1u);
v___x_4391_ = lean_nat_add(v_idx_4373_, v___x_4390_);
lean_dec(v_idx_4373_);
if (v_isShared_4389_ == 0)
{
lean_ctor_set(v___x_4388_, 1, v___x_4391_);
v___x_4393_ = v___x_4388_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_array_4372_);
lean_ctor_set(v_reuseFailAlloc_4394_, 1, v___x_4391_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
v_pos_4335_ = v___x_4393_;
v_res_4336_ = v_res_4368_;
goto v___jp_4334_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_4366_) == 0)
{
lean_object* v_pos_4399_; lean_object* v_res_4400_; 
v_pos_4399_ = lean_ctor_get(v___x_4366_, 0);
lean_inc(v_pos_4399_);
v_res_4400_ = lean_ctor_get(v___x_4366_, 1);
lean_inc(v_res_4400_);
lean_dec_ref_known(v___x_4366_, 2);
v_pos_4335_ = v_pos_4399_;
v_res_4336_ = v_res_4400_;
goto v___jp_4334_;
}
else
{
lean_object* v_pos_4401_; lean_object* v_err_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4409_; 
v_pos_4401_ = lean_ctor_get(v___x_4366_, 0);
v_err_4402_ = lean_ctor_get(v___x_4366_, 1);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4366_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4404_ = v___x_4366_;
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_err_4402_);
lean_inc(v_pos_4401_);
lean_dec(v___x_4366_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4407_; 
if (v_isShared_4405_ == 0)
{
v___x_4407_ = v___x_4404_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_pos_4401_);
lean_ctor_set(v_reuseFailAlloc_4408_, 1, v_err_4402_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
}
}
}
}
v___jp_4334_:
{
lean_object* v_fst_4337_; lean_object* v_snd_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4365_; 
v_fst_4337_ = lean_ctor_get(v_res_4336_, 0);
v_snd_4338_ = lean_ctor_get(v_res_4336_, 1);
v_isSharedCheck_4365_ = !lean_is_exclusive(v_res_4336_);
if (v_isSharedCheck_4365_ == 0)
{
v___x_4340_ = v_res_4336_;
v_isShared_4341_ = v_isSharedCheck_4365_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_snd_4338_);
lean_inc(v_fst_4337_);
lean_dec(v_res_4336_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4365_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
lean_object* v___x_4342_; 
v___x_4342_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_4332_, v_pos_4335_);
if (lean_obj_tag(v___x_4342_) == 0)
{
lean_object* v_pos_4343_; lean_object* v_res_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4355_; 
v_pos_4343_ = lean_ctor_get(v___x_4342_, 0);
v_res_4344_ = lean_ctor_get(v___x_4342_, 1);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4342_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4346_ = v___x_4342_;
v_isShared_4347_ = v_isSharedCheck_4355_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_res_4344_);
lean_inc(v_pos_4343_);
lean_dec(v___x_4342_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4355_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4348_; lean_object* v___x_4350_; 
v___x_4348_ = l_Std_Http_Version_ofNumber_x3f(v_fst_4337_, v_snd_4338_);
lean_dec(v_snd_4338_);
lean_dec(v_fst_4337_);
if (v_isShared_4341_ == 0)
{
lean_ctor_set(v___x_4340_, 1, v___x_4348_);
lean_ctor_set(v___x_4340_, 0, v_res_4344_);
v___x_4350_ = v___x_4340_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_res_4344_);
lean_ctor_set(v_reuseFailAlloc_4354_, 1, v___x_4348_);
v___x_4350_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
lean_object* v___x_4352_; 
if (v_isShared_4347_ == 0)
{
lean_ctor_set(v___x_4346_, 1, v___x_4350_);
v___x_4352_ = v___x_4346_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_pos_4343_);
lean_ctor_set(v_reuseFailAlloc_4353_, 1, v___x_4350_);
v___x_4352_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
return v___x_4352_;
}
}
}
}
else
{
lean_object* v_pos_4356_; lean_object* v_err_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
lean_del_object(v___x_4340_);
lean_dec(v_snd_4338_);
lean_dec(v_fst_4337_);
v_pos_4356_ = lean_ctor_get(v___x_4342_, 0);
v_err_4357_ = lean_ctor_get(v___x_4342_, 1);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4342_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4359_ = v___x_4342_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_err_4357_);
lean_inc(v_pos_4356_);
lean_dec(v___x_4342_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v___x_4362_; 
if (v_isShared_4360_ == 0)
{
v___x_4362_ = v___x_4359_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_pos_4356_);
lean_ctor_set(v_reuseFailAlloc_4363_, 1, v_err_4357_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion___boxed(lean_object* v_limits_4410_, lean_object* v_a_4411_){
_start:
{
lean_object* v_res_4412_; 
v_res_4412_ = l_Std_Http_Protocol_H1_parseStatusLineRawVersion(v_limits_4410_, v_a_4411_);
lean_dec_ref(v_limits_4410_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseLastChunkBody(lean_object* v_limits_4413_, lean_object* v_a_4414_){
_start:
{
lean_object* v_maxTrailerHeaders_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; 
v_maxTrailerHeaders_4415_ = lean_ctor_get(v_limits_4413_, 17);
lean_inc(v_maxTrailerHeaders_4415_);
v___x_4416_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___boxed), 2, 1);
lean_closure_set(v___x_4416_, 0, v_limits_4413_);
v___x_4417_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___x_4416_, v_maxTrailerHeaders_4415_, v_a_4414_);
if (lean_obj_tag(v___x_4417_) == 0)
{
lean_object* v_pos_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; 
v_pos_4418_ = lean_ctor_get(v___x_4417_, 0);
lean_inc(v_pos_4418_);
lean_dec_ref_known(v___x_4417_, 2);
v___x_4419_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_4420_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_4419_, v_pos_4418_);
return v___x_4420_;
}
else
{
lean_object* v_pos_4421_; lean_object* v_err_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4429_; 
v_pos_4421_ = lean_ctor_get(v___x_4417_, 0);
v_err_4422_ = lean_ctor_get(v___x_4417_, 1);
v_isSharedCheck_4429_ = !lean_is_exclusive(v___x_4417_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4424_ = v___x_4417_;
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_err_4422_);
lean_inc(v_pos_4421_);
lean_dec(v___x_4417_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v___x_4427_; 
if (v_isShared_4425_ == 0)
{
v___x_4427_ = v___x_4424_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v_pos_4421_);
lean_ctor_set(v_reuseFailAlloc_4428_, 1, v_err_4422_);
v___x_4427_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
return v___x_4427_;
}
}
}
}
}
lean_object* runtime_initialize_Std_Internal_Parsec(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec_ByteArray(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Config(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Protocol_H1_Parser(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Internal_Parsec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Parsec_ByteArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Protocol_H1_Parser(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Parsec(uint8_t builtin);
lean_object* initialize_Std_Http_Data(uint8_t builtin);
lean_object* initialize_Std_Internal_Parsec_ByteArray(uint8_t builtin);
lean_object* initialize_Std_Http_Protocol_H1_Config(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Protocol_H1_Parser(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Parsec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Parsec_ByteArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Protocol_H1_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Protocol_H1_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Protocol_H1_Parser(builtin);
}
#ifdef __cplusplus
}
#endif
