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
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes___boxed(lean_object*, lean_object*);
uint32_t lean_uint8_to_uint32(uint8_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_uint8_to_nat(uint8_t);
extern lean_object* l_Std_Http_Headers_empty;
lean_object* lean_string_data(lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
lean_object* l_Std_Http_Status_ofCode(lean_object*, uint16_t);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_toByteSlice(lean_object*, lean_object*, lean_object*);
lean_object* l_ByteSlice_toByteArray(lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
uint8_t lean_uint8_add(uint8_t, uint8_t);
lean_object* l_Char_quote(uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_ByteSlice_size(lean_object*);
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
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid space sequence"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__5;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__6;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__7;
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
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid qdtext byte: "};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3_value;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "invalid extension value"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid extension name"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__8 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__8_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__8_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__9 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__9_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__10;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__11;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__12;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__13;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__14;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__15;
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
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "content-length"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "transfer-encoding"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "host"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "connection"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "expect"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "te"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__5 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__5_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "authorization"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__6 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__6_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "max-forwards"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__7 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__7_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "cache-control"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__8 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__8_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "content-encoding"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__9 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__9_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "upgrade"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__10 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__10_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trailer"};
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
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0___boxed(lean_object*);
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
uint32_t v___x_2_; uint8_t v___y_4_; uint32_t v___x_9_; uint8_t v___x_10_; 
v___x_2_ = lean_uint8_to_uint32(v_c_1_);
v___x_9_ = 33;
v___x_10_ = lean_uint32_dec_le(v___x_9_, v___x_2_);
if (v___x_10_ == 0)
{
v___y_4_ = v___x_10_;
goto v___jp_3_;
}
else
{
uint32_t v___x_11_; uint8_t v___x_12_; 
v___x_11_ = 126;
v___x_12_ = lean_uint32_dec_le(v___x_2_, v___x_11_);
v___y_4_ = v___x_12_;
goto v___jp_3_;
}
v___jp_3_:
{
if (v___y_4_ == 0)
{
uint32_t v___x_5_; uint8_t v___x_6_; 
v___x_5_ = 32;
v___x_6_ = lean_uint32_dec_eq(v___x_2_, v___x_5_);
if (v___x_6_ == 0)
{
uint32_t v___x_7_; uint8_t v___x_8_; 
v___x_7_ = 9;
v___x_8_ = lean_uint32_dec_eq(v___x_2_, v___x_7_);
return v___x_8_;
}
else
{
return v___x_6_;
}
}
else
{
return v___y_4_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar___boxed(lean_object* v_c_13_){
_start:
{
uint8_t v_c_boxed_14_; uint8_t v_res_15_; lean_object* v_r_16_; 
v_c_boxed_14_ = lean_unbox(v_c_13_);
v_res_15_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar(v_c_boxed_14_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText(uint8_t v_c_17_){
_start:
{
uint32_t v___x_18_; uint8_t v___y_20_; uint32_t v___x_25_; uint8_t v___x_26_; 
v___x_18_ = lean_uint8_to_uint32(v_c_17_);
v___x_25_ = 9;
v___x_26_ = lean_uint32_dec_eq(v___x_18_, v___x_25_);
if (v___x_26_ == 0)
{
uint32_t v___x_27_; uint8_t v___x_28_; 
v___x_27_ = 32;
v___x_28_ = lean_uint32_dec_eq(v___x_18_, v___x_27_);
if (v___x_28_ == 0)
{
uint32_t v___x_29_; uint8_t v___x_30_; 
v___x_29_ = 33;
v___x_30_ = lean_uint32_dec_eq(v___x_18_, v___x_29_);
if (v___x_30_ == 0)
{
uint32_t v___x_31_; uint8_t v___x_32_; 
v___x_31_ = 35;
v___x_32_ = lean_uint32_dec_le(v___x_31_, v___x_18_);
if (v___x_32_ == 0)
{
v___y_20_ = v___x_32_;
goto v___jp_19_;
}
else
{
uint32_t v___x_33_; uint8_t v___x_34_; 
v___x_33_ = 91;
v___x_34_ = lean_uint32_dec_le(v___x_18_, v___x_33_);
v___y_20_ = v___x_34_;
goto v___jp_19_;
}
}
else
{
return v___x_30_;
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
v___jp_19_:
{
if (v___y_20_ == 0)
{
uint32_t v___x_21_; uint8_t v___x_22_; 
v___x_21_ = 93;
v___x_22_ = lean_uint32_dec_le(v___x_21_, v___x_18_);
if (v___x_22_ == 0)
{
return v___x_22_;
}
else
{
uint32_t v___x_23_; uint8_t v___x_24_; 
v___x_23_ = 126;
v___x_24_ = lean_uint32_dec_le(v___x_18_, v___x_23_);
return v___x_24_;
}
}
else
{
return v___y_20_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText___boxed(lean_object* v_c_35_){
_start:
{
uint8_t v_c_boxed_36_; uint8_t v_res_37_; lean_object* v_r_38_; 
v_c_boxed_36_ = lean_unbox(v_c_35_);
v_res_37_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText(v_c_boxed_36_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte(uint8_t v_c_39_){
_start:
{
uint32_t v___x_40_; uint32_t v___x_41_; uint8_t v___x_42_; 
v___x_40_ = lean_uint8_to_uint32(v_c_39_);
v___x_41_ = 32;
v___x_42_ = lean_uint32_dec_eq(v___x_40_, v___x_41_);
if (v___x_42_ == 0)
{
uint32_t v___x_43_; uint8_t v___x_44_; 
v___x_43_ = 9;
v___x_44_ = lean_uint32_dec_eq(v___x_40_, v___x_43_);
return v___x_44_;
}
else
{
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte___boxed(lean_object* v_c_45_){
_start:
{
uint8_t v_c_boxed_46_; uint8_t v_res_47_; lean_object* v_r_48_; 
v_c_boxed_46_ = lean_unbox(v_c_45_);
v_res_47_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte(v_c_boxed_46_);
v_r_48_ = lean_box(v_res_47_);
return v_r_48_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(lean_object* v_parser_54_, lean_object* v_maxCount_55_, lean_object* v_acc_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_pos_59_; lean_object* v_err_60_; lean_object* v___x_75_; 
lean_inc_ref(v_parser_54_);
lean_inc_ref(v_a_57_);
v___x_75_ = lean_apply_1(v_parser_54_, v_a_57_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_res_76_; 
v_res_76_ = lean_ctor_get(v___x_75_, 1);
lean_inc(v_res_76_);
if (lean_obj_tag(v_res_76_) == 0)
{
lean_object* v___x_77_; 
lean_dec_ref_known(v___x_75_, 2);
lean_dec(v_maxCount_55_);
lean_dec_ref(v_parser_54_);
v___x_77_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__1));
lean_inc_ref(v_a_57_);
v_pos_59_ = v_a_57_;
v_err_60_ = v___x_77_;
goto v___jp_58_;
}
else
{
lean_object* v_pos_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_104_; 
lean_dec_ref(v_a_57_);
v_pos_78_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; 
v_unused_105_ = lean_ctor_get(v___x_75_, 1);
lean_dec(v_unused_105_);
v___x_80_ = v___x_75_;
v_isShared_81_ = v_isSharedCheck_104_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_pos_78_);
lean_dec(v___x_75_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_104_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v_val_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_103_; 
v_val_82_ = lean_ctor_get(v_res_76_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v_res_76_);
if (v_isSharedCheck_103_ == 0)
{
v___x_84_ = v_res_76_;
v_isShared_85_ = v_isSharedCheck_103_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_val_82_);
lean_dec(v_res_76_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_103_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_86_ = lean_array_push(v_acc_56_, v_val_82_);
v___x_87_ = lean_array_get_size(v___x_86_);
v___x_88_ = lean_nat_dec_lt(v_maxCount_55_, v___x_87_);
if (v___x_88_ == 0)
{
lean_del_object(v___x_84_);
lean_del_object(v___x_80_);
v_acc_56_ = v___x_86_;
v_a_57_ = v_pos_78_;
goto _start;
}
else
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_98_; 
lean_dec_ref(v___x_86_);
lean_dec_ref(v_parser_54_);
v___x_90_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__2));
v___x_91_ = l_Nat_reprFast(v___x_87_);
v___x_92_ = lean_string_append(v___x_90_, v___x_91_);
lean_dec_ref(v___x_91_);
v___x_93_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__3));
v___x_94_ = lean_string_append(v___x_92_, v___x_93_);
v___x_95_ = l_Nat_reprFast(v_maxCount_55_);
v___x_96_ = lean_string_append(v___x_94_, v___x_95_);
lean_dec_ref(v___x_95_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 0, v___x_96_);
v___x_98_ = v___x_84_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_96_);
v___x_98_ = v_reuseFailAlloc_102_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v___x_100_; 
if (v_isShared_81_ == 0)
{
lean_ctor_set_tag(v___x_80_, 1);
lean_ctor_set(v___x_80_, 1, v___x_98_);
v___x_100_ = v___x_80_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_pos_78_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v___x_98_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
}
}
}
else
{
lean_object* v_err_106_; 
lean_dec(v_maxCount_55_);
lean_dec_ref(v_parser_54_);
v_err_106_ = lean_ctor_get(v___x_75_, 1);
lean_inc(v_err_106_);
lean_dec_ref_known(v___x_75_, 2);
lean_inc_ref(v_a_57_);
v_pos_59_ = v_a_57_;
v_err_60_ = v_err_106_;
goto v___jp_58_;
}
v___jp_58_:
{
lean_object* v_idx_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_73_; 
v_idx_61_ = lean_ctor_get(v_a_57_, 1);
v_isSharedCheck_73_ = !lean_is_exclusive(v_a_57_);
if (v_isSharedCheck_73_ == 0)
{
lean_object* v_unused_74_; 
v_unused_74_ = lean_ctor_get(v_a_57_, 0);
lean_dec(v_unused_74_);
v___x_63_ = v_a_57_;
v_isShared_64_ = v_isSharedCheck_73_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_idx_61_);
lean_dec(v_a_57_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_73_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v_idx_65_; uint8_t v___x_66_; 
v_idx_65_ = lean_ctor_get(v_pos_59_, 1);
v___x_66_ = lean_nat_dec_eq(v_idx_61_, v_idx_65_);
lean_dec(v_idx_61_);
if (v___x_66_ == 0)
{
lean_object* v___x_68_; 
lean_dec_ref(v_acc_56_);
if (v_isShared_64_ == 0)
{
lean_ctor_set_tag(v___x_63_, 1);
lean_ctor_set(v___x_63_, 1, v_err_60_);
lean_ctor_set(v___x_63_, 0, v_pos_59_);
v___x_68_ = v___x_63_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_pos_59_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_err_60_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
else
{
lean_object* v___x_71_; 
lean_dec(v_err_60_);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 1, v_acc_56_);
lean_ctor_set(v___x_63_, 0, v_pos_59_);
v___x_71_ = v___x_63_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v_pos_59_);
lean_ctor_set(v_reuseFailAlloc_72_, 1, v_acc_56_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go(lean_object* v_00_u03b1_107_, lean_object* v_parser_108_, lean_object* v_maxCount_109_, lean_object* v_acc_110_, lean_object* v_a_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(v_parser_108_, v_maxCount_109_, v_acc_110_, v_a_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(lean_object* v_parser_115_, lean_object* v_maxCount_116_, lean_object* v_a_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg___closed__0));
v___x_119_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(v_parser_115_, v_maxCount_116_, v___x_118_, v_a_117_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems(lean_object* v_00_u03b1_120_, lean_object* v_parser_121_, lean_object* v_maxCount_122_, lean_object* v_a_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v_parser_121_, v_maxCount_122_, v_a_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(lean_object* v_x_128_, lean_object* v_a_129_){
_start:
{
if (lean_obj_tag(v_x_128_) == 1)
{
lean_object* v_val_130_; lean_object* v___x_131_; 
v_val_130_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_val_130_);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v_a_129_);
lean_ctor_set(v___x_131_, 1, v_val_130_);
return v___x_131_;
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___closed__1));
v___x_133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_133_, 0, v_a_129_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___boxed(lean_object* v_x_134_, lean_object* v_a_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_x_134_, v_a_135_);
lean_dec(v_x_134_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption(lean_object* v_00_u03b1_137_, lean_object* v_x_138_, lean_object* v_a_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_x_138_, v_a_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___boxed(lean_object* v_00_u03b1_141_, lean_object* v_x_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption(v_00_u03b1_141_, v_x_142_, v_a_143_);
lean_dec(v_x_142_);
return v_res_144_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0(uint8_t v_c_145_){
_start:
{
uint32_t v___x_146_; uint8_t v___y_148_; uint32_t v___x_158_; uint8_t v___x_159_; 
v___x_146_ = lean_uint8_to_uint32(v_c_145_);
v___x_158_ = 33;
v___x_159_ = lean_uint32_dec_eq(v___x_146_, v___x_158_);
if (v___x_159_ == 0)
{
uint32_t v___x_160_; uint8_t v___x_161_; 
v___x_160_ = 35;
v___x_161_ = lean_uint32_dec_eq(v___x_146_, v___x_160_);
if (v___x_161_ == 0)
{
uint32_t v___x_162_; uint8_t v___x_163_; 
v___x_162_ = 36;
v___x_163_ = lean_uint32_dec_eq(v___x_146_, v___x_162_);
if (v___x_163_ == 0)
{
uint32_t v___x_164_; uint8_t v___x_165_; 
v___x_164_ = 37;
v___x_165_ = lean_uint32_dec_eq(v___x_146_, v___x_164_);
if (v___x_165_ == 0)
{
uint32_t v___x_166_; uint8_t v___x_167_; 
v___x_166_ = 38;
v___x_167_ = lean_uint32_dec_eq(v___x_146_, v___x_166_);
if (v___x_167_ == 0)
{
uint32_t v___x_168_; uint8_t v___x_169_; 
v___x_168_ = 39;
v___x_169_ = lean_uint32_dec_eq(v___x_146_, v___x_168_);
if (v___x_169_ == 0)
{
uint32_t v___x_170_; uint8_t v___x_171_; 
v___x_170_ = 42;
v___x_171_ = lean_uint32_dec_eq(v___x_146_, v___x_170_);
if (v___x_171_ == 0)
{
uint32_t v___x_172_; uint8_t v___x_173_; 
v___x_172_ = 43;
v___x_173_ = lean_uint32_dec_eq(v___x_146_, v___x_172_);
if (v___x_173_ == 0)
{
uint32_t v___x_174_; uint8_t v___x_175_; 
v___x_174_ = 45;
v___x_175_ = lean_uint32_dec_eq(v___x_146_, v___x_174_);
if (v___x_175_ == 0)
{
uint32_t v___x_176_; uint8_t v___x_177_; 
v___x_176_ = 46;
v___x_177_ = lean_uint32_dec_eq(v___x_146_, v___x_176_);
if (v___x_177_ == 0)
{
uint32_t v___x_178_; uint8_t v___x_179_; 
v___x_178_ = 94;
v___x_179_ = lean_uint32_dec_eq(v___x_146_, v___x_178_);
if (v___x_179_ == 0)
{
uint32_t v___x_180_; uint8_t v___x_181_; 
v___x_180_ = 95;
v___x_181_ = lean_uint32_dec_eq(v___x_146_, v___x_180_);
if (v___x_181_ == 0)
{
uint32_t v___x_182_; uint8_t v___x_183_; 
v___x_182_ = 96;
v___x_183_ = lean_uint32_dec_eq(v___x_146_, v___x_182_);
if (v___x_183_ == 0)
{
uint32_t v___x_184_; uint8_t v___x_185_; 
v___x_184_ = 124;
v___x_185_ = lean_uint32_dec_eq(v___x_146_, v___x_184_);
if (v___x_185_ == 0)
{
uint32_t v___x_186_; uint8_t v___x_187_; 
v___x_186_ = 126;
v___x_187_ = lean_uint32_dec_eq(v___x_146_, v___x_186_);
if (v___x_187_ == 0)
{
uint32_t v___x_188_; uint8_t v___x_189_; 
v___x_188_ = 48;
v___x_189_ = lean_uint32_dec_le(v___x_188_, v___x_146_);
if (v___x_189_ == 0)
{
goto v___jp_153_;
}
else
{
uint32_t v___x_190_; uint8_t v___x_191_; 
v___x_190_ = 57;
v___x_191_ = lean_uint32_dec_le(v___x_146_, v___x_190_);
if (v___x_191_ == 0)
{
goto v___jp_153_;
}
else
{
return v___x_191_;
}
}
}
else
{
return v___x_187_;
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
v___jp_147_:
{
if (v___y_148_ == 0)
{
uint32_t v___x_149_; uint8_t v___x_150_; 
v___x_149_ = 97;
v___x_150_ = lean_uint32_dec_le(v___x_149_, v___x_146_);
if (v___x_150_ == 0)
{
return v___x_150_;
}
else
{
uint32_t v___x_151_; uint8_t v___x_152_; 
v___x_151_ = 122;
v___x_152_ = lean_uint32_dec_le(v___x_146_, v___x_151_);
return v___x_152_;
}
}
else
{
return v___y_148_;
}
}
v___jp_153_:
{
uint32_t v___x_154_; uint8_t v___x_155_; 
v___x_154_ = 65;
v___x_155_ = lean_uint32_dec_le(v___x_154_, v___x_146_);
if (v___x_155_ == 0)
{
v___y_148_ = v___x_155_;
goto v___jp_147_;
}
else
{
uint32_t v___x_156_; uint8_t v___x_157_; 
v___x_156_ = 90;
v___x_157_ = lean_uint32_dec_le(v___x_146_, v___x_156_);
v___y_148_ = v___x_157_;
goto v___jp_147_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0___boxed(lean_object* v_c_192_){
_start:
{
uint8_t v_c_boxed_193_; uint8_t v_res_194_; lean_object* v_r_195_; 
v_c_boxed_193_ = lean_unbox(v_c_192_);
v_res_194_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0(v_c_boxed_193_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken(lean_object* v_limit_200_, lean_object* v_a_201_){
_start:
{
lean_object* v___f_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v_snd_205_; lean_object* v_snd_206_; uint8_t v___x_207_; 
v___f_202_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_203_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_201_);
v___x_204_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_202_, v_limit_200_, v___x_203_, v_a_201_);
v_snd_205_ = lean_ctor_get(v___x_204_, 1);
lean_inc(v_snd_205_);
v_snd_206_ = lean_ctor_get(v_snd_205_, 1);
v___x_207_ = lean_unbox(v_snd_206_);
if (v___x_207_ == 0)
{
lean_object* v_fst_208_; lean_object* v_fst_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_237_; 
v_fst_208_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_fst_208_);
lean_dec_ref(v___x_204_);
v_fst_209_ = lean_ctor_get(v_snd_205_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v_snd_205_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; 
v_unused_238_ = lean_ctor_get(v_snd_205_, 1);
lean_dec(v_unused_238_);
v___x_211_ = v_snd_205_;
v_isShared_212_ = v_isSharedCheck_237_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_fst_209_);
lean_dec(v_snd_205_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_237_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
uint8_t v___x_213_; 
v___x_213_ = lean_nat_dec_eq(v_fst_208_, v___x_203_);
if (v___x_213_ == 0)
{
lean_object* v_array_214_; lean_object* v_idx_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_232_; 
lean_del_object(v___x_211_);
v_array_214_ = lean_ctor_get(v_a_201_, 0);
v_idx_215_ = lean_ctor_get(v_a_201_, 1);
v_isSharedCheck_232_ = !lean_is_exclusive(v_a_201_);
if (v_isSharedCheck_232_ == 0)
{
v___x_217_ = v_a_201_;
v_isShared_218_ = v_isSharedCheck_232_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_idx_215_);
lean_inc(v_array_214_);
lean_dec(v_a_201_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_232_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v_lower_220_; lean_object* v_upper_221_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___y_229_; uint8_t v___x_231_; 
v___x_226_ = lean_nat_add(v_idx_215_, v_fst_208_);
lean_dec(v_fst_208_);
v___x_227_ = lean_byte_array_size(v_array_214_);
v___x_231_ = lean_nat_dec_le(v_idx_215_, v___x_203_);
if (v___x_231_ == 0)
{
v___y_229_ = v_idx_215_;
goto v___jp_228_;
}
else
{
lean_dec(v_idx_215_);
v___y_229_ = v___x_203_;
goto v___jp_228_;
}
v___jp_219_:
{
lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_222_ = l_ByteArray_toByteSlice(v_array_214_, v_lower_220_, v_upper_221_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_222_);
lean_ctor_set(v___x_217_, 0, v_fst_209_);
v___x_224_ = v___x_217_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_fst_209_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
v___jp_228_:
{
uint8_t v___x_230_; 
v___x_230_ = lean_nat_dec_le(v___x_226_, v___x_227_);
if (v___x_230_ == 0)
{
lean_dec(v___x_226_);
v_lower_220_ = v___y_229_;
v_upper_221_ = v___x_227_;
goto v___jp_219_;
}
else
{
v_lower_220_ = v___y_229_;
v_upper_221_ = v___x_226_;
goto v___jp_219_;
}
}
}
}
else
{
lean_object* v___x_233_; lean_object* v___x_235_; 
lean_dec(v_fst_209_);
lean_dec(v_fst_208_);
v___x_233_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_212_ == 0)
{
lean_ctor_set_tag(v___x_211_, 1);
lean_ctor_set(v___x_211_, 1, v___x_233_);
lean_ctor_set(v___x_211_, 0, v_a_201_);
v___x_235_ = v___x_211_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_201_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v___x_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
else
{
lean_object* v_fst_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_247_; 
lean_dec_ref(v___x_204_);
lean_dec_ref(v_a_201_);
v_fst_239_ = lean_ctor_get(v_snd_205_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v_snd_205_);
if (v_isSharedCheck_247_ == 0)
{
lean_object* v_unused_248_; 
v_unused_248_ = lean_ctor_get(v_snd_205_, 1);
lean_dec(v_unused_248_);
v___x_241_ = v_snd_205_;
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_fst_239_);
lean_dec(v_snd_205_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_243_ = lean_box(0);
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 1);
lean_ctor_set(v___x_241_, 1, v___x_243_);
v___x_245_ = v___x_241_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_fst_239_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v___x_243_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___boxed(lean_object* v_limit_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken(v_limit_249_, v_a_250_);
lean_dec(v_limit_249_);
return v_res_251_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__0));
v___x_254_ = lean_string_to_utf8(v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf(lean_object* v_a_255_){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_257_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_256_, v_a_255_);
return v___x_257_;
}
}
static uint8_t _init_l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0(void){
_start:
{
uint32_t v___x_258_; uint8_t v___x_259_; 
v___x_258_ = 13;
v___x_259_ = lean_uint32_to_uint8(v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(lean_object* v_limits_263_, lean_object* v_a_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_array_266_; lean_object* v_idx_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v_array_266_ = lean_ctor_get(v___y_265_, 0);
v_idx_267_ = lean_ctor_get(v___y_265_, 1);
v___x_268_ = lean_byte_array_size(v_array_266_);
v___x_269_ = lean_nat_dec_lt(v_idx_267_, v___x_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; 
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v___y_265_);
lean_ctor_set(v___x_270_, 1, v_a_264_);
return v___x_270_;
}
else
{
uint8_t v___x_271_; uint8_t v___x_272_; uint8_t v___x_273_; 
v___x_271_ = lean_byte_array_fget(v_array_266_, v_idx_267_);
v___x_272_ = lean_uint8_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0);
v___x_273_ = lean_uint8_dec_eq(v___x_271_, v___x_272_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; 
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v___y_265_);
lean_ctor_set(v___x_274_, 1, v_a_264_);
return v___x_274_;
}
else
{
lean_object* v_maxLeadingEmptyLines_275_; uint8_t v___x_276_; 
v_maxLeadingEmptyLines_275_ = lean_ctor_get(v_limits_263_, 9);
v___x_276_ = lean_nat_dec_le(v_maxLeadingEmptyLines_275_, v_a_264_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_278_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_277_, v___y_265_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_pos_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v_pos_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_pos_279_);
lean_dec_ref_known(v___x_278_, 2);
v___x_280_ = lean_unsigned_to_nat(1u);
v___x_281_ = lean_nat_add(v_a_264_, v___x_280_);
lean_dec(v_a_264_);
v_a_264_ = v___x_281_;
v___y_265_ = v_pos_279_;
goto _start;
}
else
{
lean_object* v_pos_283_; lean_object* v_err_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
lean_dec(v_a_264_);
v_pos_283_ = lean_ctor_get(v___x_278_, 0);
v_err_284_ = lean_ctor_get(v___x_278_, 1);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_278_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_err_284_);
lean_inc(v_pos_283_);
lean_dec(v___x_278_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_pos_283_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_err_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
else
{
lean_object* v___x_292_; lean_object* v___x_293_; 
lean_dec(v_a_264_);
v___x_292_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__2));
v___x_293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_293_, 0, v___y_265_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
return v___x_293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___boxed(lean_object* v_limits_294_, lean_object* v_a_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_294_, v_a_295_, v___y_296_);
lean_dec_ref(v_limits_294_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(lean_object* v_limits_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_count_300_; lean_object* v___x_301_; 
v_count_300_ = lean_unsigned_to_nat(0u);
v___x_301_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_298_, v_count_300_, v_a_299_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_pos_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_310_; 
v_pos_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_310_ == 0)
{
lean_object* v_unused_311_; 
v_unused_311_ = lean_ctor_get(v___x_301_, 1);
lean_dec(v_unused_311_);
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_310_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_pos_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_310_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_306_ = lean_box(0);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 1, v___x_306_);
v___x_308_ = v___x_304_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_pos_302_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v___x_306_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
else
{
lean_object* v_pos_312_; lean_object* v_err_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
v_pos_312_ = lean_ctor_get(v___x_301_, 0);
v_err_313_ = lean_ctor_get(v___x_301_, 1);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_301_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_err_313_);
lean_inc(v_pos_312_);
lean_dec(v___x_301_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_pos_312_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_err_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines___boxed(lean_object* v_limits_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_321_, v_a_322_);
lean_dec_ref(v_limits_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0(lean_object* v_limits_324_, lean_object* v_inst_325_, lean_object* v_a_326_, lean_object* v___y_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_324_, v_a_326_, v___y_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___boxed(lean_object* v_limits_329_, lean_object* v_inst_330_, lean_object* v_a_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0(v_limits_329_, v_inst_330_, v_a_331_, v___y_332_);
lean_dec_ref(v_limits_329_);
return v_res_333_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0(void){
_start:
{
uint32_t v___x_334_; uint8_t v___x_335_; 
v___x_334_ = 32;
v___x_335_ = lean_uint32_to_uint8(v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__2(void){
_start:
{
uint8_t v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v___x_338_ = lean_uint8_to_nat(v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__3(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__2);
v___x_340_ = l_Nat_reprFast(v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__4(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__3);
v___x_342_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_343_ = lean_string_append(v___x_342_, v___x_341_);
return v___x_343_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__6(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__5));
v___x_346_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__4);
v___x_347_ = lean_string_append(v___x_346_, v___x_345_);
return v___x_347_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__6, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__6_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__6);
v___x_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp(lean_object* v_a_350_){
_start:
{
lean_object* v_array_351_; lean_object* v_idx_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v_array_351_ = lean_ctor_get(v_a_350_, 0);
v_idx_352_ = lean_ctor_get(v_a_350_, 1);
v___x_353_ = lean_byte_array_size(v_array_351_);
v___x_354_ = lean_nat_dec_lt(v_idx_352_, v___x_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_box(0);
v___x_356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_356_, 0, v_a_350_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
return v___x_356_;
}
else
{
uint8_t v___x_357_; uint8_t v_got_358_; uint8_t v___x_359_; 
v___x_357_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v_got_358_ = lean_byte_array_fget(v_array_351_, v_idx_352_);
v___x_359_ = lean_uint8_dec_eq(v_got_358_, v___x_357_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7);
v___x_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_361_, 0, v_a_350_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
return v___x_361_;
}
else
{
lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_372_; 
lean_inc(v_idx_352_);
lean_inc_ref(v_array_351_);
v_isSharedCheck_372_ = !lean_is_exclusive(v_a_350_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; lean_object* v_unused_374_; 
v_unused_373_ = lean_ctor_get(v_a_350_, 1);
lean_dec(v_unused_373_);
v_unused_374_ = lean_ctor_get(v_a_350_, 0);
lean_dec(v_unused_374_);
v___x_363_ = v_a_350_;
v_isShared_364_ = v_isSharedCheck_372_;
goto v_resetjp_362_;
}
else
{
lean_dec(v_a_350_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_372_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_365_ = lean_unsigned_to_nat(1u);
v___x_366_ = lean_nat_add(v_idx_352_, v___x_365_);
lean_dec(v_idx_352_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 1, v___x_366_);
v___x_368_ = v___x_363_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_array_351_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v___x_366_);
v___x_368_ = v_reuseFailAlloc_371_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_box(0);
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_368_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
return v___x_370_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows(lean_object* v_limits_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_pos_382_; lean_object* v_pos_386_; lean_object* v_maxSpaceSequence_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v_snd_393_; lean_object* v_snd_394_; uint8_t v___x_395_; 
v_maxSpaceSequence_389_ = lean_ctor_get(v_limits_379_, 8);
v___x_390_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2));
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___x_390_, v_maxSpaceSequence_389_, v___x_391_, v_a_380_);
v_snd_393_ = lean_ctor_get(v___x_392_, 1);
lean_inc(v_snd_393_);
lean_dec_ref(v___x_392_);
v_snd_394_ = lean_ctor_get(v_snd_393_, 1);
v___x_395_ = lean_unbox(v_snd_394_);
if (v___x_395_ == 0)
{
lean_object* v_fst_396_; lean_object* v_array_397_; lean_object* v_idx_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v_fst_396_ = lean_ctor_get(v_snd_393_, 0);
lean_inc(v_fst_396_);
lean_dec(v_snd_393_);
v_array_397_ = lean_ctor_get(v_fst_396_, 0);
v_idx_398_ = lean_ctor_get(v_fst_396_, 1);
v___x_399_ = lean_byte_array_size(v_array_397_);
v___x_400_ = lean_nat_dec_lt(v_idx_398_, v___x_399_);
if (v___x_400_ == 0)
{
v_pos_382_ = v_fst_396_;
goto v___jp_381_;
}
else
{
uint8_t v___x_401_; uint32_t v___x_402_; uint32_t v___x_403_; uint8_t v___x_404_; 
v___x_401_ = lean_byte_array_fget(v_array_397_, v_idx_398_);
v___x_402_ = lean_uint8_to_uint32(v___x_401_);
v___x_403_ = 32;
v___x_404_ = lean_uint32_dec_eq(v___x_402_, v___x_403_);
if (v___x_404_ == 0)
{
uint32_t v___x_405_; uint8_t v___x_406_; 
v___x_405_ = 9;
v___x_406_ = lean_uint32_dec_eq(v___x_402_, v___x_405_);
if (v___x_406_ == 0)
{
v_pos_382_ = v_fst_396_;
goto v___jp_381_;
}
else
{
v_pos_386_ = v_fst_396_;
goto v___jp_385_;
}
}
else
{
v_pos_386_ = v_fst_396_;
goto v___jp_385_;
}
}
}
else
{
lean_object* v_fst_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_415_; 
v_fst_407_ = lean_ctor_get(v_snd_393_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v_snd_393_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; 
v_unused_416_ = lean_ctor_get(v_snd_393_, 1);
lean_dec(v_unused_416_);
v___x_409_ = v_snd_393_;
v_isShared_410_ = v_isSharedCheck_415_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_fst_407_);
lean_dec(v_snd_393_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_415_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_411_ = lean_box(0);
if (v_isShared_410_ == 0)
{
lean_ctor_set_tag(v___x_409_, 1);
lean_ctor_set(v___x_409_, 1, v___x_411_);
v___x_413_ = v___x_409_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_fst_407_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v___x_411_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
v___jp_381_:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_box(0);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_pos_382_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
return v___x_384_;
}
v___jp_385_:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_388_, 0, v_pos_386_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
return v___x_388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___boxed(lean_object* v_limits_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows(v_limits_417_, v_a_418_);
lean_dec_ref(v_limits_417_);
return v_res_419_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0(void){
_start:
{
uint32_t v___x_420_; uint8_t v___x_421_; 
v___x_420_ = 97;
v___x_421_ = lean_uint32_to_uint8(v___x_420_);
return v___x_421_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__1(void){
_start:
{
uint32_t v___x_422_; uint8_t v___x_423_; 
v___x_422_ = 65;
v___x_423_ = lean_uint32_to_uint8(v___x_422_);
return v___x_423_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__2(void){
_start:
{
uint32_t v___x_424_; uint8_t v___x_425_; 
v___x_424_ = 70;
v___x_425_ = lean_uint32_to_uint8(v___x_424_);
return v___x_425_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3(void){
_start:
{
uint32_t v___x_426_; uint8_t v___x_427_; 
v___x_426_ = 48;
v___x_427_ = lean_uint32_to_uint8(v___x_426_);
return v___x_427_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4(void){
_start:
{
uint32_t v___x_428_; uint8_t v___x_429_; 
v___x_428_ = 57;
v___x_429_ = lean_uint32_to_uint8(v___x_428_);
return v___x_429_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__6(void){
_start:
{
uint32_t v___x_431_; uint8_t v___x_432_; 
v___x_431_ = 102;
v___x_432_ = lean_uint32_to_uint8(v___x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit(lean_object* v_a_433_){
_start:
{
lean_object* v_array_434_; lean_object* v_idx_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v_array_434_ = lean_ctor_get(v_a_433_, 0);
v_idx_435_ = lean_ctor_get(v_a_433_, 1);
v___x_436_ = lean_byte_array_size(v_array_434_);
v___x_437_ = lean_nat_dec_lt(v_idx_435_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_box(0);
v___x_439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_439_, 0, v_a_433_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
return v___x_439_;
}
else
{
lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_495_; 
lean_inc(v_idx_435_);
lean_inc_ref(v_array_434_);
v_isSharedCheck_495_ = !lean_is_exclusive(v_a_433_);
if (v_isSharedCheck_495_ == 0)
{
lean_object* v_unused_496_; lean_object* v_unused_497_; 
v_unused_496_ = lean_ctor_get(v_a_433_, 1);
lean_dec(v_unused_496_);
v_unused_497_ = lean_ctor_get(v_a_433_, 0);
lean_dec(v_unused_497_);
v___x_441_ = v_a_433_;
v_isShared_442_ = v_isSharedCheck_495_;
goto v_resetjp_440_;
}
else
{
lean_dec(v_a_433_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_495_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
uint8_t v_c_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v_it_x27_447_; 
v_c_443_ = lean_byte_array_fget(v_array_434_, v_idx_435_);
v___x_444_ = lean_unsigned_to_nat(1u);
v___x_445_ = lean_nat_add(v_idx_435_, v___x_444_);
lean_dec(v_idx_435_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 1, v___x_445_);
v_it_x27_447_ = v___x_441_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_array_434_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v___x_445_);
v_it_x27_447_ = v_reuseFailAlloc_494_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
uint8_t v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3);
v___x_491_ = lean_uint8_dec_le(v___x_490_, v_c_443_);
if (v___x_491_ == 0)
{
goto v___jp_485_;
}
else
{
uint8_t v___x_492_; uint8_t v___x_493_; 
v___x_492_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4);
v___x_493_ = lean_uint8_dec_le(v_c_443_, v___x_492_);
if (v___x_493_ == 0)
{
goto v___jp_485_;
}
else
{
goto v___jp_465_;
}
}
v___jp_448_:
{
uint8_t v___x_449_; uint8_t v___x_450_; uint8_t v___x_451_; uint8_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_449_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0);
v___x_450_ = lean_uint8_sub(v_c_443_, v___x_449_);
v___x_451_ = 10;
v___x_452_ = lean_uint8_add(v___x_450_, v___x_451_);
v___x_453_ = lean_box(v___x_452_);
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v_it_x27_447_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
return v___x_454_;
}
v___jp_455_:
{
uint8_t v___x_456_; uint8_t v___x_457_; 
v___x_456_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__1);
v___x_457_ = lean_uint8_dec_le(v___x_456_, v_c_443_);
if (v___x_457_ == 0)
{
goto v___jp_448_;
}
else
{
uint8_t v___x_458_; uint8_t v___x_459_; 
v___x_458_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__2);
v___x_459_ = lean_uint8_dec_le(v_c_443_, v___x_458_);
if (v___x_459_ == 0)
{
goto v___jp_448_;
}
else
{
uint8_t v___x_460_; uint8_t v___x_461_; uint8_t v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_460_ = lean_uint8_sub(v_c_443_, v___x_456_);
v___x_461_ = 10;
v___x_462_ = lean_uint8_add(v___x_460_, v___x_461_);
v___x_463_ = lean_box(v___x_462_);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v_it_x27_447_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
return v___x_464_;
}
}
}
v___jp_465_:
{
uint8_t v___x_466_; uint8_t v___x_467_; 
v___x_466_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3);
v___x_467_ = lean_uint8_dec_le(v___x_466_, v_c_443_);
if (v___x_467_ == 0)
{
goto v___jp_455_;
}
else
{
uint8_t v___x_468_; uint8_t v___x_469_; 
v___x_468_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4);
v___x_469_ = lean_uint8_dec_le(v_c_443_, v___x_468_);
if (v___x_469_ == 0)
{
goto v___jp_455_;
}
else
{
uint8_t v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_uint8_sub(v_c_443_, v___x_466_);
v___x_471_ = lean_box(v___x_470_);
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v_it_x27_447_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
return v___x_472_;
}
}
}
v___jp_473_:
{
lean_object* v___x_474_; uint32_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_474_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__5));
v___x_475_ = lean_uint8_to_uint32(v_c_443_);
v___x_476_ = l_Char_quote(v___x_475_);
v___x_477_ = lean_string_append(v___x_474_, v___x_476_);
lean_dec_ref(v___x_476_);
v___x_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
v___x_479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_479_, 0, v_it_x27_447_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
return v___x_479_;
}
v___jp_480_:
{
uint8_t v___x_481_; uint8_t v___x_482_; 
v___x_481_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__1);
v___x_482_ = lean_uint8_dec_le(v___x_481_, v_c_443_);
if (v___x_482_ == 0)
{
goto v___jp_473_;
}
else
{
uint8_t v___x_483_; uint8_t v___x_484_; 
v___x_483_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__2);
v___x_484_ = lean_uint8_dec_le(v_c_443_, v___x_483_);
if (v___x_484_ == 0)
{
goto v___jp_473_;
}
else
{
goto v___jp_465_;
}
}
}
v___jp_485_:
{
uint8_t v___x_486_; uint8_t v___x_487_; 
v___x_486_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0);
v___x_487_ = lean_uint8_dec_le(v___x_486_, v_c_443_);
if (v___x_487_ == 0)
{
goto v___jp_480_;
}
else
{
uint8_t v___x_488_; uint8_t v___x_489_; 
v___x_488_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__6, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__6_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__6);
v___x_489_ = lean_uint8_dec_le(v_c_443_, v___x_488_);
if (v___x_489_ == 0)
{
goto v___jp_480_;
}
else
{
goto v___jp_465_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(lean_object* v_acc_504_, lean_object* v_count_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_pos_508_; lean_object* v_err_509_; lean_object* v___x_537_; 
lean_inc_ref(v_a_506_);
v___x_537_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit(v_a_506_);
if (lean_obj_tag(v___x_537_) == 0)
{
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_pos_538_; lean_object* v_res_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_556_; 
lean_dec_ref(v_a_506_);
v_pos_538_ = lean_ctor_get(v___x_537_, 0);
v_res_539_ = lean_ctor_get(v___x_537_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_556_ == 0)
{
v___x_541_ = v___x_537_;
v_isShared_542_ = v_isSharedCheck_556_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_res_539_);
lean_inc(v_pos_538_);
lean_dec(v___x_537_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_556_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_543_ = lean_unsigned_to_nat(16u);
v___x_544_ = lean_unsigned_to_nat(1u);
v___x_545_ = lean_nat_add(v_count_505_, v___x_544_);
lean_dec(v_count_505_);
v___x_546_ = lean_nat_dec_lt(v___x_543_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; uint8_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
lean_del_object(v___x_541_);
v___x_547_ = lean_nat_mul(v_acc_504_, v___x_543_);
lean_dec(v_acc_504_);
v___x_548_ = lean_unbox(v_res_539_);
lean_dec(v_res_539_);
v___x_549_ = lean_uint8_to_nat(v___x_548_);
v___x_550_ = lean_nat_add(v___x_547_, v___x_549_);
lean_dec(v___x_547_);
v_acc_504_ = v___x_550_;
v_count_505_ = v___x_545_;
v_a_506_ = v_pos_538_;
goto _start;
}
else
{
lean_object* v___x_552_; lean_object* v___x_554_; 
lean_dec(v___x_545_);
lean_dec(v_res_539_);
lean_dec(v_acc_504_);
v___x_552_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__3));
if (v_isShared_542_ == 0)
{
lean_ctor_set_tag(v___x_541_, 1);
lean_ctor_set(v___x_541_, 1, v___x_552_);
v___x_554_ = v___x_541_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_pos_538_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
else
{
lean_object* v_pos_557_; lean_object* v_err_558_; 
v_pos_557_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_pos_557_);
v_err_558_ = lean_ctor_get(v___x_537_, 1);
lean_inc(v_err_558_);
lean_dec_ref_known(v___x_537_, 2);
v_pos_508_ = v_pos_557_;
v_err_509_ = v_err_558_;
goto v___jp_507_;
}
}
else
{
lean_object* v_err_559_; 
v_err_559_ = lean_ctor_get(v___x_537_, 1);
lean_inc(v_err_559_);
lean_dec_ref_known(v___x_537_, 2);
lean_inc_ref(v_a_506_);
v_pos_508_ = v_a_506_;
v_err_509_ = v_err_559_;
goto v___jp_507_;
}
v___jp_507_:
{
lean_object* v_idx_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_535_; 
v_idx_510_ = lean_ctor_get(v_a_506_, 1);
v_isSharedCheck_535_ = !lean_is_exclusive(v_a_506_);
if (v_isSharedCheck_535_ == 0)
{
lean_object* v_unused_536_; 
v_unused_536_ = lean_ctor_get(v_a_506_, 0);
lean_dec(v_unused_536_);
v___x_512_ = v_a_506_;
v_isShared_513_ = v_isSharedCheck_535_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_idx_510_);
lean_dec(v_a_506_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_535_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v_array_514_; lean_object* v_idx_515_; uint8_t v___x_516_; 
v_array_514_ = lean_ctor_get(v_pos_508_, 0);
v_idx_515_ = lean_ctor_get(v_pos_508_, 1);
v___x_516_ = lean_nat_dec_eq(v_idx_510_, v_idx_515_);
lean_dec(v_idx_510_);
if (v___x_516_ == 0)
{
lean_object* v___x_518_; 
lean_dec(v_count_505_);
lean_dec(v_acc_504_);
if (v_isShared_513_ == 0)
{
lean_ctor_set_tag(v___x_512_, 1);
lean_ctor_set(v___x_512_, 1, v_err_509_);
lean_ctor_set(v___x_512_, 0, v_pos_508_);
v___x_518_ = v___x_512_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_pos_508_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_err_509_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
else
{
lean_object* v___x_520_; uint8_t v___x_521_; 
lean_dec(v_err_509_);
v___x_520_ = lean_unsigned_to_nat(0u);
v___x_521_ = lean_nat_dec_eq(v_count_505_, v___x_520_);
lean_dec(v_count_505_);
if (v___x_521_ == 0)
{
lean_object* v___x_523_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 1, v_acc_504_);
lean_ctor_set(v___x_512_, 0, v_pos_508_);
v___x_523_ = v___x_512_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_pos_508_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_acc_504_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
else
{
lean_object* v___x_525_; uint8_t v___x_526_; 
lean_dec(v_acc_504_);
v___x_525_ = lean_byte_array_size(v_array_514_);
v___x_526_ = lean_nat_dec_lt(v_idx_515_, v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_527_ = lean_box(0);
if (v_isShared_513_ == 0)
{
lean_ctor_set_tag(v___x_512_, 1);
lean_ctor_set(v___x_512_, 1, v___x_527_);
lean_ctor_set(v___x_512_, 0, v_pos_508_);
v___x_529_ = v___x_512_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_pos_508_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
else
{
lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_531_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__1));
if (v_isShared_513_ == 0)
{
lean_ctor_set_tag(v___x_512_, 1);
lean_ctor_set(v___x_512_, 1, v___x_531_);
lean_ctor_set(v___x_512_, 0, v_pos_508_);
v___x_533_ = v___x_512_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_pos_508_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v___x_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(lean_object* v_a_560_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(v___x_561_, v___x_561_, v_a_560_);
return v___x_562_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__0));
v___x_565_ = lean_string_to_utf8(v___x_564_);
return v___x_565_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4(void){
_start:
{
uint32_t v___x_569_; uint8_t v___x_570_; 
v___x_569_ = 46;
v___x_570_ = lean_uint32_to_uint8(v___x_569_);
return v___x_570_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5(void){
_start:
{
uint8_t v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4);
v___x_572_ = lean_uint8_to_nat(v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__6(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5);
v___x_574_ = l_Nat_reprFast(v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__7(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__6, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__6_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__6);
v___x_576_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_577_ = lean_string_append(v___x_576_, v___x_575_);
return v___x_577_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__8(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__5));
v___x_579_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__7);
v___x_580_ = lean_string_append(v___x_579_, v___x_578_);
return v___x_580_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__9(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__8, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__8_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__8);
v___x_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(lean_object* v_a_583_){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1);
v___x_585_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_584_, v_a_583_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_pos_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_657_; 
v_pos_586_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; 
v_unused_658_ = lean_ctor_get(v___x_585_, 1);
lean_dec(v_unused_658_);
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_657_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_pos_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_657_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v_array_590_; lean_object* v_idx_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v_array_590_ = lean_ctor_get(v_pos_586_, 0);
v_idx_591_ = lean_ctor_get(v_pos_586_, 1);
v___x_592_ = lean_byte_array_size(v_array_590_);
v___x_593_ = lean_nat_dec_lt(v_idx_591_, v___x_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_594_ = lean_box(0);
if (v_isShared_589_ == 0)
{
lean_ctor_set_tag(v___x_588_, 1);
lean_ctor_set(v___x_588_, 1, v___x_594_);
v___x_596_ = v___x_588_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_pos_586_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v___x_594_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
else
{
uint8_t v_c_598_; uint8_t v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; uint8_t v___y_604_; uint8_t v___x_622_; uint8_t v___x_623_; uint8_t v___x_624_; uint8_t v___y_626_; 
v_c_598_ = lean_byte_array_fget(v_array_590_, v_idx_591_);
v___x_622_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3);
v___x_623_ = lean_uint8_dec_le(v___x_622_, v_c_598_);
v___x_624_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4);
if (v___x_623_ == 0)
{
v___y_626_ = v___x_623_;
goto v___jp_625_;
}
else
{
uint8_t v___x_656_; 
v___x_656_ = lean_uint8_dec_le(v_c_598_, v___x_624_);
v___y_626_ = v___x_656_;
goto v___jp_625_;
}
v___jp_599_:
{
if (v___y_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_607_; 
lean_dec(v___y_602_);
lean_dec_ref(v_array_590_);
v___x_605_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
if (v_isShared_589_ == 0)
{
lean_ctor_set_tag(v___x_588_, 1);
lean_ctor_set(v___x_588_, 1, v___x_605_);
lean_ctor_set(v___x_588_, 0, v___y_603_);
v___x_607_ = v___x_588_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___y_603_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v___x_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
else
{
uint32_t v___x_609_; lean_object* v___x_610_; lean_object* v_it_x27_611_; uint32_t v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
lean_dec_ref(v___y_603_);
v___x_609_ = lean_uint8_to_uint32(v_c_598_);
v___x_610_ = lean_nat_add(v___y_602_, v___y_601_);
lean_dec(v___y_602_);
v_it_x27_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_611_, 0, v_array_590_);
lean_ctor_set(v_it_x27_611_, 1, v___x_610_);
v___x_612_ = lean_uint8_to_uint32(v___y_600_);
v___x_613_ = lean_uint32_to_nat(v___x_609_);
v___x_614_ = lean_unsigned_to_nat(48u);
v___x_615_ = lean_nat_sub(v___x_613_, v___x_614_);
lean_dec(v___x_613_);
v___x_616_ = lean_uint32_to_nat(v___x_612_);
v___x_617_ = lean_nat_sub(v___x_616_, v___x_614_);
lean_dec(v___x_616_);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_615_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 1, v___x_618_);
lean_ctor_set(v___x_588_, 0, v_it_x27_611_);
v___x_620_ = v___x_588_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_it_x27_611_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v___x_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
v___jp_625_:
{
if (v___y_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; 
lean_del_object(v___x_588_);
v___x_627_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_628_, 0, v_pos_586_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
return v___x_628_;
}
else
{
lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_653_; 
lean_inc(v_idx_591_);
lean_inc_ref(v_array_590_);
v_isSharedCheck_653_ = !lean_is_exclusive(v_pos_586_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; lean_object* v_unused_655_; 
v_unused_654_ = lean_ctor_get(v_pos_586_, 1);
lean_dec(v_unused_654_);
v_unused_655_ = lean_ctor_get(v_pos_586_, 0);
lean_dec(v_unused_655_);
v___x_630_ = v_pos_586_;
v_isShared_631_ = v_isSharedCheck_653_;
goto v_resetjp_629_;
}
else
{
lean_dec(v_pos_586_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_653_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v_it_x27_635_; 
v___x_632_ = lean_unsigned_to_nat(1u);
v___x_633_ = lean_nat_add(v_idx_591_, v___x_632_);
lean_dec(v_idx_591_);
lean_inc(v___x_633_);
lean_inc_ref(v_array_590_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v___x_633_);
v_it_x27_635_ = v___x_630_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_array_590_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v___x_633_);
v_it_x27_635_ = v_reuseFailAlloc_652_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
uint8_t v___x_636_; 
v___x_636_ = lean_nat_dec_lt(v___x_633_, v___x_592_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; lean_object* v___x_638_; 
lean_dec(v___x_633_);
lean_dec_ref(v_array_590_);
lean_del_object(v___x_588_);
v___x_637_ = lean_box(0);
v___x_638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_638_, 0, v_it_x27_635_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
return v___x_638_;
}
else
{
uint8_t v___x_639_; uint8_t v_got_640_; uint8_t v___x_641_; 
v___x_639_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4);
v_got_640_ = lean_byte_array_fget(v_array_590_, v___x_633_);
v___x_641_ = lean_uint8_dec_eq(v_got_640_, v___x_639_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; 
lean_dec(v___x_633_);
lean_dec_ref(v_array_590_);
lean_del_object(v___x_588_);
v___x_642_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__9, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__9_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__9);
v___x_643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_643_, 0, v_it_x27_635_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
return v___x_643_;
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
lean_dec_ref(v_it_x27_635_);
v___x_644_ = lean_nat_add(v___x_633_, v___x_632_);
lean_dec(v___x_633_);
lean_inc(v___x_644_);
lean_inc_ref(v_array_590_);
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v_array_590_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
v___x_646_ = lean_nat_dec_lt(v___x_644_, v___x_592_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; 
lean_dec(v___x_644_);
lean_dec_ref(v_array_590_);
lean_del_object(v___x_588_);
v___x_647_ = lean_box(0);
v___x_648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_645_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
return v___x_648_;
}
else
{
uint8_t v_c_649_; uint8_t v___x_650_; 
v_c_649_ = lean_byte_array_fget(v_array_590_, v___x_644_);
v___x_650_ = lean_uint8_dec_le(v___x_622_, v_c_649_);
if (v___x_650_ == 0)
{
v___y_600_ = v_c_649_;
v___y_601_ = v___x_632_;
v___y_602_ = v___x_644_;
v___y_603_ = v___x_645_;
v___y_604_ = v___x_650_;
goto v___jp_599_;
}
else
{
uint8_t v___x_651_; 
v___x_651_ = lean_uint8_dec_le(v_c_649_, v___x_624_);
v___y_600_ = v_c_649_;
v___y_601_ = v___x_632_;
v___y_602_ = v___x_644_;
v___y_603_ = v___x_645_;
v___y_604_ = v___x_651_;
goto v___jp_599_;
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
lean_object* v_pos_659_; lean_object* v_err_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
v_pos_659_ = lean_ctor_get(v___x_585_, 0);
v_err_660_ = lean_ctor_get(v___x_585_, 1);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_585_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_err_660_);
lean_inc(v_pos_659_);
lean_dec(v___x_585_);
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
lean_object* v_fst_2017_; lean_object* v_fst_2018_; lean_object* v_array_2019_; lean_object* v_idx_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2047_; 
v_fst_2017_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_fst_2017_);
lean_dec_ref(v___x_2013_);
v_fst_2018_ = lean_ctor_get(v_snd_2014_, 0);
lean_inc(v_fst_2018_);
lean_dec(v_snd_2014_);
v_array_2019_ = lean_ctor_get(v_a_2004_, 0);
v_idx_2020_ = lean_ctor_get(v_a_2004_, 1);
v_isSharedCheck_2047_ = !lean_is_exclusive(v_a_2004_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2022_ = v_a_2004_;
v_isShared_2023_ = v_isSharedCheck_2047_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_idx_2020_);
lean_inc(v_array_2019_);
lean_dec(v_a_2004_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2047_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v_lower_2025_; lean_object* v_upper_2026_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___y_2044_; uint8_t v___x_2046_; 
v___x_2041_ = lean_nat_add(v_idx_2020_, v_fst_2017_);
lean_dec(v_fst_2017_);
v___x_2042_ = lean_byte_array_size(v_array_2019_);
v___x_2046_ = lean_nat_dec_le(v_idx_2020_, v___x_2012_);
if (v___x_2046_ == 0)
{
v___y_2044_ = v_idx_2020_;
goto v___jp_2043_;
}
else
{
lean_dec(v_idx_2020_);
v___y_2044_ = v___x_2012_;
goto v___jp_2043_;
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
uint8_t v___x_2034_; uint8_t v___x_2035_; uint8_t v___x_2036_; 
v___x_2034_ = lean_byte_array_fget(v_array_2030_, v_idx_2031_);
v___x_2035_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v___x_2036_ = lean_uint8_dec_eq(v___x_2034_, v___x_2035_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2037_; lean_object* v___x_2039_; 
lean_dec_ref(v___x_2027_);
v___x_2037_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__2));
if (v_isShared_2023_ == 0)
{
lean_ctor_set_tag(v___x_2022_, 1);
lean_ctor_set(v___x_2022_, 1, v___x_2037_);
lean_ctor_set(v___x_2022_, 0, v_fst_2018_);
v___x_2039_ = v___x_2022_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_fst_2018_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
else
{
lean_del_object(v___x_2022_);
v___y_2006_ = v___x_2027_;
v___y_2007_ = v_fst_2018_;
goto v___jp_2005_;
}
}
}
}
v___jp_2043_:
{
uint8_t v___x_2045_; 
v___x_2045_ = lean_nat_dec_le(v___x_2041_, v___x_2042_);
if (v___x_2045_ == 0)
{
lean_dec(v___x_2041_);
v_lower_2025_ = v___y_2044_;
v_upper_2026_ = v___x_2042_;
goto v___jp_2024_;
}
else
{
v_lower_2025_ = v___y_2044_;
v_upper_2026_ = v___x_2041_;
goto v___jp_2024_;
}
}
}
}
else
{
lean_object* v_fst_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2056_; 
lean_dec_ref(v___x_2013_);
lean_dec_ref(v_a_2004_);
v_fst_2048_ = lean_ctor_get(v_snd_2014_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_snd_2014_);
if (v_isSharedCheck_2056_ == 0)
{
lean_object* v_unused_2057_; 
v_unused_2057_ = lean_ctor_get(v_snd_2014_, 1);
lean_dec(v_unused_2057_);
v___x_2050_ = v_snd_2014_;
v_isShared_2051_ = v_isSharedCheck_2056_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_fst_2048_);
lean_dec(v_snd_2014_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2056_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2052_; lean_object* v___x_2054_; 
v___x_2052_ = lean_box(0);
if (v_isShared_2051_ == 0)
{
lean_ctor_set_tag(v___x_2050_, 1);
lean_ctor_set(v___x_2050_, 1, v___x_2052_);
v___x_2054_ = v___x_2050_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_fst_2048_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___boxed(lean_object* v_limits_2058_, lean_object* v_a_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_2058_, v_a_2059_);
lean_dec_ref(v_limits_2058_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0(lean_object* v___x_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_2064_, v___y_2065_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_pos_2067_; lean_object* v_array_2068_; lean_object* v_idx_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v_pos_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_pos_2067_);
v_array_2068_ = lean_ctor_get(v_pos_2067_, 0);
v_idx_2069_ = lean_ctor_get(v_pos_2067_, 1);
v___x_2070_ = lean_byte_array_size(v_array_2068_);
v___x_2071_ = lean_nat_dec_lt(v_idx_2069_, v___x_2070_);
if (v___x_2071_ == 0)
{
lean_dec(v_pos_2067_);
return v___x_2066_;
}
else
{
lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2079_; 
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2079_ == 0)
{
lean_object* v_unused_2080_; lean_object* v_unused_2081_; 
v_unused_2080_ = lean_ctor_get(v___x_2066_, 1);
lean_dec(v_unused_2080_);
v_unused_2081_ = lean_ctor_get(v___x_2066_, 0);
lean_dec(v_unused_2081_);
v___x_2073_ = v___x_2066_;
v_isShared_2074_ = v_isSharedCheck_2079_;
goto v_resetjp_2072_;
}
else
{
lean_dec(v___x_2066_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2079_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2075_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__1));
if (v_isShared_2074_ == 0)
{
lean_ctor_set_tag(v___x_2073_, 1);
lean_ctor_set(v___x_2073_, 1, v___x_2075_);
v___x_2077_ = v___x_2073_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_pos_2067_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
else
{
return v___x_2066_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(lean_object* v_limits_2092_, lean_object* v_a_2093_){
_start:
{
lean_object* v___y_2095_; lean_object* v_pos_2096_; lean_object* v_res_2097_; lean_object* v_pos_2101_; lean_object* v_res_2102_; lean_object* v___x_2141_; 
v___x_2141_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_2092_, v_a_2093_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_pos_2142_; lean_object* v_res_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2173_; 
v_pos_2142_ = lean_ctor_get(v___x_2141_, 0);
v_res_2143_ = lean_ctor_get(v___x_2141_, 1);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2145_ = v___x_2141_;
v_isShared_2146_ = v_isSharedCheck_2173_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_res_2143_);
lean_inc(v_pos_2142_);
lean_dec(v___x_2141_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2173_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v_array_2147_; lean_object* v_idx_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; 
v_array_2147_ = lean_ctor_get(v_pos_2142_, 0);
v_idx_2148_ = lean_ctor_get(v_pos_2142_, 1);
v___x_2149_ = lean_byte_array_size(v_array_2147_);
v___x_2150_ = lean_nat_dec_lt(v_idx_2148_, v___x_2149_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2151_; lean_object* v___x_2153_; 
lean_dec(v_res_2143_);
v___x_2151_ = lean_box(0);
if (v_isShared_2146_ == 0)
{
lean_ctor_set_tag(v___x_2145_, 1);
lean_ctor_set(v___x_2145_, 1, v___x_2151_);
v___x_2153_ = v___x_2145_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_pos_2142_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v___x_2151_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
else
{
uint8_t v___x_2155_; uint8_t v_got_2156_; uint8_t v___x_2157_; 
v___x_2155_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v_got_2156_ = lean_byte_array_fget(v_array_2147_, v_idx_2148_);
v___x_2157_ = lean_uint8_dec_eq(v_got_2156_, v___x_2155_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; lean_object* v___x_2160_; 
lean_dec(v_res_2143_);
v___x_2158_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7);
if (v_isShared_2146_ == 0)
{
lean_ctor_set_tag(v___x_2145_, 1);
lean_ctor_set(v___x_2145_, 1, v___x_2158_);
v___x_2160_ = v___x_2145_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_pos_2142_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
else
{
lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2170_; 
lean_inc(v_idx_2148_);
lean_inc_ref(v_array_2147_);
lean_del_object(v___x_2145_);
v_isSharedCheck_2170_ = !lean_is_exclusive(v_pos_2142_);
if (v_isSharedCheck_2170_ == 0)
{
lean_object* v_unused_2171_; lean_object* v_unused_2172_; 
v_unused_2171_ = lean_ctor_get(v_pos_2142_, 1);
lean_dec(v_unused_2171_);
v_unused_2172_ = lean_ctor_get(v_pos_2142_, 0);
lean_dec(v_unused_2172_);
v___x_2163_ = v_pos_2142_;
v_isShared_2164_ = v_isSharedCheck_2170_;
goto v_resetjp_2162_;
}
else
{
lean_dec(v_pos_2142_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2170_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2165_ = lean_unsigned_to_nat(1u);
v___x_2166_ = lean_nat_add(v_idx_2148_, v___x_2165_);
lean_dec(v_idx_2148_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 1, v___x_2166_);
v___x_2168_ = v___x_2163_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_array_2147_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
v_pos_2101_ = v___x_2168_;
v_res_2102_ = v_res_2143_;
goto v___jp_2100_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_pos_2174_; lean_object* v_res_2175_; 
v_pos_2174_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_pos_2174_);
v_res_2175_ = lean_ctor_get(v___x_2141_, 1);
lean_inc(v_res_2175_);
lean_dec_ref_known(v___x_2141_, 2);
v_pos_2101_ = v_pos_2174_;
v_res_2102_ = v_res_2175_;
goto v___jp_2100_;
}
else
{
lean_object* v_pos_2176_; lean_object* v_err_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
v_pos_2176_ = lean_ctor_get(v___x_2141_, 0);
v_err_2177_ = lean_ctor_get(v___x_2141_, 1);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2141_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_err_2177_);
lean_inc(v_pos_2176_);
lean_dec(v___x_2141_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_pos_2176_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_err_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
v___jp_2094_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___y_2095_);
lean_ctor_set(v___x_2098_, 1, v_res_2097_);
v___x_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2099_, 0, v_pos_2096_);
lean_ctor_set(v___x_2099_, 1, v___x_2098_);
return v___x_2099_;
}
v___jp_2100_:
{
lean_object* v___f_2103_; lean_object* v___x_2104_; 
v___f_2103_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___closed__1));
v___x_2104_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_2103_, v_res_2102_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2113_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2107_ = v___x_2104_;
v_isShared_2108_ = v_isSharedCheck_2113_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2104_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2113_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
lean_ctor_set_tag(v___x_2107_, 1);
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2111_; 
v___x_2111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2111_, 0, v_pos_2101_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
return v___x_2111_;
}
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2115_; 
v_a_2114_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___x_2104_, 1);
v___x_2115_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_pos_2101_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_pos_2116_; lean_object* v_res_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v_pos_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_pos_2116_);
v_res_2117_ = lean_ctor_get(v___x_2115_, 1);
lean_inc(v_res_2117_);
lean_dec_ref_known(v___x_2115_, 2);
v___x_2118_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2119_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2118_, v_pos_2116_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_pos_2120_; 
v_pos_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_pos_2120_);
lean_dec_ref_known(v___x_2119_, 2);
v___y_2095_ = v_a_2114_;
v_pos_2096_ = v_pos_2120_;
v_res_2097_ = v_res_2117_;
goto v___jp_2094_;
}
else
{
lean_object* v_pos_2121_; lean_object* v_err_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec(v_res_2117_);
lean_dec(v_a_2114_);
v_pos_2121_ = lean_ctor_get(v___x_2119_, 0);
v_err_2122_ = lean_ctor_get(v___x_2119_, 1);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2119_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_err_2122_);
lean_inc(v_pos_2121_);
lean_dec(v___x_2119_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_pos_2121_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_err_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_pos_2130_; lean_object* v_res_2131_; 
v_pos_2130_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_pos_2130_);
v_res_2131_ = lean_ctor_get(v___x_2115_, 1);
lean_inc(v_res_2131_);
lean_dec_ref_known(v___x_2115_, 2);
v___y_2095_ = v_a_2114_;
v_pos_2096_ = v_pos_2130_;
v_res_2097_ = v_res_2131_;
goto v___jp_2094_;
}
else
{
lean_object* v_pos_2132_; lean_object* v_err_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec(v_a_2114_);
v_pos_2132_ = lean_ctor_get(v___x_2115_, 0);
v_err_2133_ = lean_ctor_get(v___x_2115_, 1);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2115_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_err_2133_);
lean_inc(v_pos_2132_);
lean_dec(v___x_2115_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_pos_2132_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_err_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___boxed(lean_object* v_limits_2185_, lean_object* v_a_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_2185_, v_a_2186_);
lean_dec_ref(v_limits_2185_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine(lean_object* v_limits_2191_, lean_object* v_a_2192_){
_start:
{
lean_object* v___y_2194_; lean_object* v___y_2198_; lean_object* v___y_2199_; uint8_t v___y_2200_; lean_object* v___y_2201_; uint8_t v___y_2202_; uint8_t v___y_2203_; lean_object* v_pos_2215_; uint8_t v_res_2216_; lean_object* v___x_2236_; 
v___x_2236_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_2191_, v_a_2192_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_pos_2237_; lean_object* v___x_2238_; 
v_pos_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_pos_2237_);
lean_dec_ref_known(v___x_2236_, 2);
v___x_2238_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(v_pos_2237_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_pos_2239_; lean_object* v_res_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2271_; 
v_pos_2239_ = lean_ctor_get(v___x_2238_, 0);
v_res_2240_ = lean_ctor_get(v___x_2238_, 1);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2242_ = v___x_2238_;
v_isShared_2243_ = v_isSharedCheck_2271_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_res_2240_);
lean_inc(v_pos_2239_);
lean_dec(v___x_2238_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2271_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v_array_2244_; lean_object* v_idx_2245_; lean_object* v___x_2246_; uint8_t v___x_2247_; 
v_array_2244_ = lean_ctor_get(v_pos_2239_, 0);
v_idx_2245_ = lean_ctor_get(v_pos_2239_, 1);
v___x_2246_ = lean_byte_array_size(v_array_2244_);
v___x_2247_ = lean_nat_dec_lt(v_idx_2245_, v___x_2246_);
if (v___x_2247_ == 0)
{
lean_object* v___x_2248_; lean_object* v___x_2250_; 
lean_dec(v_res_2240_);
v___x_2248_ = lean_box(0);
if (v_isShared_2243_ == 0)
{
lean_ctor_set_tag(v___x_2242_, 1);
lean_ctor_set(v___x_2242_, 1, v___x_2248_);
v___x_2250_ = v___x_2242_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_pos_2239_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v___x_2248_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
else
{
uint8_t v___x_2252_; uint8_t v_got_2253_; uint8_t v___x_2254_; 
v___x_2252_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v_got_2253_ = lean_byte_array_fget(v_array_2244_, v_idx_2245_);
v___x_2254_ = lean_uint8_dec_eq(v_got_2253_, v___x_2252_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; lean_object* v___x_2257_; 
lean_dec(v_res_2240_);
v___x_2255_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7);
if (v_isShared_2243_ == 0)
{
lean_ctor_set_tag(v___x_2242_, 1);
lean_ctor_set(v___x_2242_, 1, v___x_2255_);
v___x_2257_ = v___x_2242_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_pos_2239_);
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
lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2268_; 
lean_inc(v_idx_2245_);
lean_inc_ref(v_array_2244_);
lean_del_object(v___x_2242_);
v_isSharedCheck_2268_ = !lean_is_exclusive(v_pos_2239_);
if (v_isSharedCheck_2268_ == 0)
{
lean_object* v_unused_2269_; lean_object* v_unused_2270_; 
v_unused_2269_ = lean_ctor_get(v_pos_2239_, 1);
lean_dec(v_unused_2269_);
v_unused_2270_ = lean_ctor_get(v_pos_2239_, 0);
lean_dec(v_unused_2270_);
v___x_2260_ = v_pos_2239_;
v_isShared_2261_ = v_isSharedCheck_2268_;
goto v_resetjp_2259_;
}
else
{
lean_dec(v_pos_2239_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2268_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2265_; 
v___x_2262_ = lean_unsigned_to_nat(1u);
v___x_2263_ = lean_nat_add(v_idx_2245_, v___x_2262_);
lean_dec(v_idx_2245_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 1, v___x_2263_);
v___x_2265_ = v___x_2260_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_array_2244_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2263_);
v___x_2265_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
uint8_t v___x_2266_; 
v___x_2266_ = lean_unbox(v_res_2240_);
lean_dec(v_res_2240_);
v_pos_2215_ = v___x_2265_;
v_res_2216_ = v___x_2266_;
goto v___jp_2214_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_pos_2272_; lean_object* v_res_2273_; uint8_t v___x_2274_; 
v_pos_2272_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_pos_2272_);
v_res_2273_ = lean_ctor_get(v___x_2238_, 1);
lean_inc(v_res_2273_);
lean_dec_ref_known(v___x_2238_, 2);
v___x_2274_ = lean_unbox(v_res_2273_);
lean_dec(v_res_2273_);
v_pos_2215_ = v_pos_2272_;
v_res_2216_ = v___x_2274_;
goto v___jp_2214_;
}
else
{
lean_object* v_pos_2275_; lean_object* v_err_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
v_pos_2275_ = lean_ctor_get(v___x_2238_, 0);
v_err_2276_ = lean_ctor_get(v___x_2238_, 1);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2238_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_err_2276_);
lean_inc(v_pos_2275_);
lean_dec(v___x_2238_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_pos_2275_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v_err_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
else
{
lean_object* v_pos_2284_; lean_object* v_err_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
v_pos_2284_ = lean_ctor_get(v___x_2236_, 0);
v_err_2285_ = lean_ctor_get(v___x_2236_, 1);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2236_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_err_2285_);
lean_inc(v_pos_2284_);
lean_dec(v___x_2236_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_pos_2284_);
lean_ctor_set(v_reuseFailAlloc_2291_, 1, v_err_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
v___jp_2193_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
v___x_2196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___y_2194_);
lean_ctor_set(v___x_2196_, 1, v___x_2195_);
return v___x_2196_;
}
v___jp_2197_:
{
if (v___y_2203_ == 0)
{
if (v___y_2200_ == 0)
{
lean_dec(v___y_2199_);
lean_dec(v___y_2198_);
v___y_2194_ = v___y_2201_;
goto v___jp_2193_;
}
else
{
lean_object* v___x_2204_; uint8_t v___x_2205_; 
v___x_2204_ = lean_unsigned_to_nat(0u);
v___x_2205_ = lean_nat_dec_eq(v___y_2199_, v___x_2204_);
lean_dec(v___y_2199_);
if (v___x_2205_ == 0)
{
lean_dec(v___y_2198_);
v___y_2194_ = v___y_2201_;
goto v___jp_2193_;
}
else
{
uint8_t v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2206_ = 0;
v___x_2207_ = l_Std_Http_Headers_empty;
v___x_2208_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_2208_, 0, v___y_2198_);
lean_ctor_set(v___x_2208_, 1, v___x_2207_);
lean_ctor_set_uint8(v___x_2208_, sizeof(void*)*2, v___y_2202_);
lean_ctor_set_uint8(v___x_2208_, sizeof(void*)*2 + 1, v___x_2206_);
v___x_2209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___y_2201_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
return v___x_2209_;
}
}
}
else
{
uint8_t v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
lean_dec(v___y_2199_);
v___x_2210_ = 1;
v___x_2211_ = l_Std_Http_Headers_empty;
v___x_2212_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_2212_, 0, v___y_2198_);
lean_ctor_set(v___x_2212_, 1, v___x_2211_);
lean_ctor_set_uint8(v___x_2212_, sizeof(void*)*2, v___y_2202_);
lean_ctor_set_uint8(v___x_2212_, sizeof(void*)*2 + 1, v___x_2210_);
v___x_2213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___y_2201_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
return v___x_2213_;
}
}
v___jp_2214_:
{
lean_object* v___x_2217_; 
v___x_2217_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_2191_, v_pos_2215_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_res_2218_; lean_object* v_snd_2219_; lean_object* v_pos_2220_; lean_object* v_fst_2221_; lean_object* v_fst_2222_; lean_object* v_snd_2223_; lean_object* v___x_2224_; uint8_t v___x_2225_; 
v_res_2218_ = lean_ctor_get(v___x_2217_, 1);
lean_inc(v_res_2218_);
v_snd_2219_ = lean_ctor_get(v_res_2218_, 1);
lean_inc(v_snd_2219_);
v_pos_2220_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_pos_2220_);
lean_dec_ref_known(v___x_2217_, 2);
v_fst_2221_ = lean_ctor_get(v_res_2218_, 0);
lean_inc(v_fst_2221_);
lean_dec(v_res_2218_);
v_fst_2222_ = lean_ctor_get(v_snd_2219_, 0);
lean_inc(v_fst_2222_);
v_snd_2223_ = lean_ctor_get(v_snd_2219_, 1);
lean_inc(v_snd_2223_);
lean_dec(v_snd_2219_);
v___x_2224_ = lean_unsigned_to_nat(1u);
v___x_2225_ = lean_nat_dec_eq(v_fst_2222_, v___x_2224_);
lean_dec(v_fst_2222_);
if (v___x_2225_ == 0)
{
v___y_2198_ = v_fst_2221_;
v___y_2199_ = v_snd_2223_;
v___y_2200_ = v___x_2225_;
v___y_2201_ = v_pos_2220_;
v___y_2202_ = v_res_2216_;
v___y_2203_ = v___x_2225_;
goto v___jp_2197_;
}
else
{
uint8_t v___x_2226_; 
v___x_2226_ = lean_nat_dec_eq(v_snd_2223_, v___x_2224_);
v___y_2198_ = v_fst_2221_;
v___y_2199_ = v_snd_2223_;
v___y_2200_ = v___x_2225_;
v___y_2201_ = v_pos_2220_;
v___y_2202_ = v_res_2216_;
v___y_2203_ = v___x_2226_;
goto v___jp_2197_;
}
}
else
{
lean_object* v_pos_2227_; lean_object* v_err_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
v_pos_2227_ = lean_ctor_get(v___x_2217_, 0);
v_err_2228_ = lean_ctor_get(v___x_2217_, 1);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2217_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_err_2228_);
lean_inc(v_pos_2227_);
lean_dec(v___x_2217_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_pos_2227_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_err_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine___boxed(lean_object* v_limits_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Std_Http_Protocol_H1_parseRequestLine(v_limits_2293_, v_a_2294_);
lean_dec_ref(v_limits_2293_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion(lean_object* v_limits_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v_pos_2299_; uint8_t v_res_2300_; lean_object* v___x_2342_; 
v___x_2342_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_2296_, v_a_2297_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_pos_2343_; lean_object* v___x_2344_; 
v_pos_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_pos_2343_);
lean_dec_ref_known(v___x_2342_, 2);
v___x_2344_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(v_pos_2343_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_pos_2345_; lean_object* v_res_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2377_; 
v_pos_2345_ = lean_ctor_get(v___x_2344_, 0);
v_res_2346_ = lean_ctor_get(v___x_2344_, 1);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2348_ = v___x_2344_;
v_isShared_2349_ = v_isSharedCheck_2377_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_res_2346_);
lean_inc(v_pos_2345_);
lean_dec(v___x_2344_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2377_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v_array_2350_; lean_object* v_idx_2351_; lean_object* v___x_2352_; uint8_t v___x_2353_; 
v_array_2350_ = lean_ctor_get(v_pos_2345_, 0);
v_idx_2351_ = lean_ctor_get(v_pos_2345_, 1);
v___x_2352_ = lean_byte_array_size(v_array_2350_);
v___x_2353_ = lean_nat_dec_lt(v_idx_2351_, v___x_2352_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; lean_object* v___x_2356_; 
lean_dec(v_res_2346_);
v___x_2354_ = lean_box(0);
if (v_isShared_2349_ == 0)
{
lean_ctor_set_tag(v___x_2348_, 1);
lean_ctor_set(v___x_2348_, 1, v___x_2354_);
v___x_2356_ = v___x_2348_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_pos_2345_);
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
uint8_t v___x_2358_; uint8_t v_got_2359_; uint8_t v___x_2360_; 
v___x_2358_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v_got_2359_ = lean_byte_array_fget(v_array_2350_, v_idx_2351_);
v___x_2360_ = lean_uint8_dec_eq(v_got_2359_, v___x_2358_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; lean_object* v___x_2363_; 
lean_dec(v_res_2346_);
v___x_2361_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7);
if (v_isShared_2349_ == 0)
{
lean_ctor_set_tag(v___x_2348_, 1);
lean_ctor_set(v___x_2348_, 1, v___x_2361_);
v___x_2363_ = v___x_2348_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_pos_2345_);
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
lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2374_; 
lean_inc(v_idx_2351_);
lean_inc_ref(v_array_2350_);
lean_del_object(v___x_2348_);
v_isSharedCheck_2374_ = !lean_is_exclusive(v_pos_2345_);
if (v_isSharedCheck_2374_ == 0)
{
lean_object* v_unused_2375_; lean_object* v_unused_2376_; 
v_unused_2375_ = lean_ctor_get(v_pos_2345_, 1);
lean_dec(v_unused_2375_);
v_unused_2376_ = lean_ctor_get(v_pos_2345_, 0);
lean_dec(v_unused_2376_);
v___x_2366_ = v_pos_2345_;
v_isShared_2367_ = v_isSharedCheck_2374_;
goto v_resetjp_2365_;
}
else
{
lean_dec(v_pos_2345_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2374_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2371_; 
v___x_2368_ = lean_unsigned_to_nat(1u);
v___x_2369_ = lean_nat_add(v_idx_2351_, v___x_2368_);
lean_dec(v_idx_2351_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 1, v___x_2369_);
v___x_2371_ = v___x_2366_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_array_2350_);
lean_ctor_set(v_reuseFailAlloc_2373_, 1, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
uint8_t v___x_2372_; 
v___x_2372_ = lean_unbox(v_res_2346_);
lean_dec(v_res_2346_);
v_pos_2299_ = v___x_2371_;
v_res_2300_ = v___x_2372_;
goto v___jp_2298_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_pos_2378_; lean_object* v_res_2379_; uint8_t v___x_2380_; 
v_pos_2378_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_pos_2378_);
v_res_2379_ = lean_ctor_get(v___x_2344_, 1);
lean_inc(v_res_2379_);
lean_dec_ref_known(v___x_2344_, 2);
v___x_2380_ = lean_unbox(v_res_2379_);
lean_dec(v_res_2379_);
v_pos_2299_ = v_pos_2378_;
v_res_2300_ = v___x_2380_;
goto v___jp_2298_;
}
else
{
lean_object* v_pos_2381_; lean_object* v_err_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
v_pos_2381_ = lean_ctor_get(v___x_2344_, 0);
v_err_2382_ = lean_ctor_get(v___x_2344_, 1);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2344_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_err_2382_);
lean_inc(v_pos_2381_);
lean_dec(v___x_2344_);
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
else
{
lean_object* v_pos_2390_; lean_object* v_err_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
v_pos_2390_ = lean_ctor_get(v___x_2342_, 0);
v_err_2391_ = lean_ctor_get(v___x_2342_, 1);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2342_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_err_2391_);
lean_inc(v_pos_2390_);
lean_dec(v___x_2342_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_pos_2390_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_err_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
v___jp_2298_:
{
lean_object* v___x_2301_; 
v___x_2301_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_2296_, v_pos_2299_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_res_2302_; lean_object* v_snd_2303_; lean_object* v_pos_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2331_; 
v_res_2302_ = lean_ctor_get(v___x_2301_, 1);
lean_inc(v_res_2302_);
v_snd_2303_ = lean_ctor_get(v_res_2302_, 1);
lean_inc(v_snd_2303_);
v_pos_2304_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2331_ == 0)
{
lean_object* v_unused_2332_; 
v_unused_2332_ = lean_ctor_get(v___x_2301_, 1);
lean_dec(v_unused_2332_);
v___x_2306_ = v___x_2301_;
v_isShared_2307_ = v_isSharedCheck_2331_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_pos_2304_);
lean_dec(v___x_2301_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2331_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v_fst_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2329_; 
v_fst_2308_ = lean_ctor_get(v_res_2302_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v_res_2302_);
if (v_isSharedCheck_2329_ == 0)
{
lean_object* v_unused_2330_; 
v_unused_2330_ = lean_ctor_get(v_res_2302_, 1);
lean_dec(v_unused_2330_);
v___x_2310_ = v_res_2302_;
v_isShared_2311_ = v_isSharedCheck_2329_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_fst_2308_);
lean_dec(v_res_2302_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2329_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v_fst_2312_; lean_object* v_snd_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2328_; 
v_fst_2312_ = lean_ctor_get(v_snd_2303_, 0);
v_snd_2313_ = lean_ctor_get(v_snd_2303_, 1);
v_isSharedCheck_2328_ = !lean_is_exclusive(v_snd_2303_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2315_ = v_snd_2303_;
v_isShared_2316_ = v_isSharedCheck_2328_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_snd_2313_);
lean_inc(v_fst_2312_);
lean_dec(v_snd_2303_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2328_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2317_ = l_Std_Http_Version_ofNumber_x3f(v_fst_2312_, v_snd_2313_);
lean_dec(v_snd_2313_);
lean_dec(v_fst_2312_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 1, v___x_2317_);
lean_ctor_set(v___x_2315_, 0, v_fst_2308_);
v___x_2319_ = v___x_2315_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_fst_2308_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
lean_object* v___x_2320_; lean_object* v___x_2322_; 
v___x_2320_ = lean_box(v_res_2300_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 1, v___x_2319_);
lean_ctor_set(v___x_2310_, 0, v___x_2320_);
v___x_2322_ = v___x_2310_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2320_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v___x_2319_);
v___x_2322_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
lean_object* v___x_2324_; 
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 1, v___x_2322_);
v___x_2324_ = v___x_2306_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_pos_2304_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v___x_2322_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
}
}
}
else
{
lean_object* v_pos_2333_; lean_object* v_err_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
v_pos_2333_ = lean_ctor_get(v___x_2301_, 0);
v_err_2334_ = lean_ctor_get(v___x_2301_, 1);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2301_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_err_2334_);
lean_inc(v_pos_2333_);
lean_dec(v___x_2301_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_pos_2333_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_err_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion___boxed(lean_object* v_limits_2399_, lean_object* v_a_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Std_Http_Protocol_H1_parseRequestLineRawVersion(v_limits_2399_, v_a_2400_);
lean_dec_ref(v_limits_2399_);
return v_res_2401_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(uint8_t v___y_2402_){
_start:
{
uint32_t v___x_2403_; uint32_t v___x_2404_; uint8_t v___x_2405_; 
v___x_2403_ = lean_uint8_to_uint32(v___y_2402_);
v___x_2404_ = 32;
v___x_2405_ = lean_uint32_dec_eq(v___x_2403_, v___x_2404_);
if (v___x_2405_ == 0)
{
uint32_t v___x_2406_; uint8_t v___x_2407_; 
v___x_2406_ = 9;
v___x_2407_ = lean_uint32_dec_eq(v___x_2403_, v___x_2406_);
return v___x_2407_;
}
else
{
return v___x_2405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed(lean_object* v___y_2408_){
_start:
{
uint8_t v___y_3678__boxed_2409_; uint8_t v_res_2410_; lean_object* v_r_2411_; 
v___y_3678__boxed_2409_ = lean_unbox(v___y_2408_);
v_res_2410_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(v___y_3678__boxed_2409_);
v_r_2411_ = lean_box(v_res_2410_);
return v_r_2411_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2(uint8_t v___y_2412_){
_start:
{
uint32_t v___x_2413_; uint8_t v___y_2415_; uint32_t v___x_2420_; uint8_t v___x_2421_; 
v___x_2413_ = lean_uint8_to_uint32(v___y_2412_);
v___x_2420_ = 33;
v___x_2421_ = lean_uint32_dec_le(v___x_2420_, v___x_2413_);
if (v___x_2421_ == 0)
{
v___y_2415_ = v___x_2421_;
goto v___jp_2414_;
}
else
{
uint32_t v___x_2422_; uint8_t v___x_2423_; 
v___x_2422_ = 126;
v___x_2423_ = lean_uint32_dec_le(v___x_2413_, v___x_2422_);
v___y_2415_ = v___x_2423_;
goto v___jp_2414_;
}
v___jp_2414_:
{
if (v___y_2415_ == 0)
{
uint32_t v___x_2416_; uint8_t v___x_2417_; 
v___x_2416_ = 32;
v___x_2417_ = lean_uint32_dec_eq(v___x_2413_, v___x_2416_);
if (v___x_2417_ == 0)
{
uint32_t v___x_2418_; uint8_t v___x_2419_; 
v___x_2418_ = 9;
v___x_2419_ = lean_uint32_dec_eq(v___x_2413_, v___x_2418_);
return v___x_2419_;
}
else
{
return v___x_2417_;
}
}
else
{
return v___y_2415_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2___boxed(lean_object* v___y_2424_){
_start:
{
uint8_t v___y_3691__boxed_2425_; uint8_t v_res_2426_; lean_object* v_r_2427_; 
v___y_3691__boxed_2425_ = lean_unbox(v___y_2424_);
v_res_2426_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2(v___y_3691__boxed_2425_);
v_r_2427_ = lean_box(v_res_2426_);
return v_r_2427_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(lean_object* v_s_2428_, lean_object* v_pos_2429_){
_start:
{
lean_object* v_str_2430_; lean_object* v_startInclusive_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; uint8_t v_decide_2435_; 
v_str_2430_ = lean_ctor_get(v_s_2428_, 0);
v_startInclusive_2431_ = lean_ctor_get(v_s_2428_, 1);
v___x_2432_ = lean_nat_add(v_startInclusive_2431_, v_pos_2429_);
v___x_2433_ = lean_nat_sub(v___x_2432_, v_startInclusive_2431_);
v___x_2434_ = lean_unsigned_to_nat(0u);
v_decide_2435_ = lean_nat_dec_eq(v___x_2433_, v___x_2434_);
if (v_decide_2435_ == 0)
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2444_; uint32_t v___x_2445_; uint32_t v___x_2446_; uint8_t v___x_2447_; 
lean_inc(v_startInclusive_2431_);
lean_inc_ref(v_str_2430_);
v___x_2436_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2436_, 0, v_str_2430_);
lean_ctor_set(v___x_2436_, 1, v_startInclusive_2431_);
lean_ctor_set(v___x_2436_, 2, v___x_2432_);
v___x_2437_ = lean_unsigned_to_nat(1u);
v___x_2438_ = lean_nat_sub(v___x_2433_, v___x_2437_);
lean_dec(v___x_2433_);
v___x_2439_ = l_String_Slice_posLE(v___x_2436_, v___x_2438_);
lean_dec_ref_known(v___x_2436_, 3);
v___x_2444_ = lean_nat_add(v_startInclusive_2431_, v___x_2439_);
v___x_2445_ = lean_string_utf8_get_fast(v_str_2430_, v___x_2444_);
lean_dec(v___x_2444_);
v___x_2446_ = 32;
v___x_2447_ = lean_uint32_dec_eq(v___x_2445_, v___x_2446_);
if (v___x_2447_ == 0)
{
uint32_t v___x_2448_; uint8_t v___x_2449_; 
v___x_2448_ = 9;
v___x_2449_ = lean_uint32_dec_eq(v___x_2445_, v___x_2448_);
if (v___x_2449_ == 0)
{
uint32_t v___x_2450_; uint8_t v___x_2451_; 
v___x_2450_ = 13;
v___x_2451_ = lean_uint32_dec_eq(v___x_2445_, v___x_2450_);
if (v___x_2451_ == 0)
{
uint32_t v___x_2452_; uint8_t v___x_2453_; 
v___x_2452_ = 10;
v___x_2453_ = lean_uint32_dec_eq(v___x_2445_, v___x_2452_);
if (v___x_2453_ == 0)
{
lean_dec(v___x_2439_);
return v_pos_2429_;
}
else
{
goto v___jp_2440_;
}
}
else
{
goto v___jp_2440_;
}
}
else
{
goto v___jp_2440_;
}
}
else
{
goto v___jp_2440_;
}
v___jp_2440_:
{
lean_object* v___x_2441_; uint8_t v___x_2442_; 
v___x_2441_ = lean_nat_add(v___x_2439_, v___x_2437_);
v___x_2442_ = lean_nat_dec_le(v___x_2441_, v_pos_2429_);
lean_dec(v___x_2441_);
if (v___x_2442_ == 0)
{
lean_dec(v___x_2439_);
return v_pos_2429_;
}
else
{
lean_dec(v_pos_2429_);
v_pos_2429_ = v___x_2439_;
goto _start;
}
}
}
else
{
lean_dec(v___x_2433_);
lean_dec(v___x_2432_);
return v_pos_2429_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0___boxed(lean_object* v_s_2454_, lean_object* v_pos_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(v_s_2454_, v_pos_2455_);
lean_dec_ref(v_s_2454_);
return v_res_2456_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2(void){
_start:
{
uint32_t v___x_2459_; uint8_t v___x_2460_; 
v___x_2459_ = 58;
v___x_2460_ = lean_uint32_to_uint8(v___x_2459_);
return v___x_2460_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3(void){
_start:
{
uint8_t v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2);
v___x_2462_ = lean_uint8_to_nat(v___x_2461_);
return v___x_2462_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4(void){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2463_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3);
v___x_2464_ = l_Nat_reprFast(v___x_2463_);
return v___x_2464_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__5(void){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2465_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4);
v___x_2466_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_2467_ = lean_string_append(v___x_2466_, v___x_2465_);
return v___x_2467_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__6(void){
_start:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2468_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__5));
v___x_2469_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__5, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__5_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__5);
v___x_2470_ = lean_string_append(v___x_2469_, v___x_2468_);
return v___x_2470_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__7(void){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__6, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__6_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__6);
v___x_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2471_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(lean_object* v_limits_2473_, lean_object* v_a_2474_){
_start:
{
lean_object* v_pos_2476_; lean_object* v_pos_2480_; lean_object* v_maxHeaderNameLength_2483_; lean_object* v_maxHeaderValueLength_2484_; lean_object* v_maxSpaceSequence_2485_; lean_object* v___f_2486_; lean_object* v___x_2487_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2547_; lean_object* v_pos_2548_; lean_object* v_res_2549_; lean_object* v___x_2555_; lean_object* v_snd_2556_; lean_object* v_snd_2557_; uint8_t v___x_2558_; 
v_maxHeaderNameLength_2483_ = lean_ctor_get(v_limits_2473_, 6);
v_maxHeaderValueLength_2484_ = lean_ctor_get(v_limits_2473_, 7);
v_maxSpaceSequence_2485_ = lean_ctor_get(v_limits_2473_, 8);
v___f_2486_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_2487_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2474_);
v___x_2555_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2486_, v_maxHeaderNameLength_2483_, v___x_2487_, v_a_2474_);
v_snd_2556_ = lean_ctor_get(v___x_2555_, 1);
lean_inc(v_snd_2556_);
v_snd_2557_ = lean_ctor_get(v_snd_2556_, 1);
v___x_2558_ = lean_unbox(v_snd_2557_);
if (v___x_2558_ == 0)
{
lean_object* v_fst_2559_; lean_object* v_fst_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2718_; 
v_fst_2559_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_fst_2559_);
lean_dec_ref(v___x_2555_);
v_fst_2560_ = lean_ctor_get(v_snd_2556_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v_snd_2556_);
if (v_isSharedCheck_2718_ == 0)
{
lean_object* v_unused_2719_; 
v_unused_2719_ = lean_ctor_get(v_snd_2556_, 1);
lean_dec(v_unused_2719_);
v___x_2562_ = v_snd_2556_;
v_isShared_2563_ = v_isSharedCheck_2718_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_fst_2560_);
lean_dec(v_snd_2556_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2718_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
uint8_t v___x_2564_; 
v___x_2564_ = lean_nat_dec_eq(v_fst_2559_, v___x_2487_);
if (v___x_2564_ == 0)
{
lean_object* v_array_2565_; lean_object* v_idx_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2713_; 
v_array_2565_ = lean_ctor_get(v_a_2474_, 0);
v_idx_2566_ = lean_ctor_get(v_a_2474_, 1);
v_isSharedCheck_2713_ = !lean_is_exclusive(v_a_2474_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2568_ = v_a_2474_;
v_isShared_2569_ = v_isSharedCheck_2713_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_idx_2566_);
lean_inc(v_array_2565_);
lean_dec(v_a_2474_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2713_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___f_2570_; lean_object* v___y_2572_; lean_object* v_pos_2573_; lean_object* v_res_2574_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v_lower_2604_; lean_object* v_upper_2605_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___f_2616_; lean_object* v___y_2618_; lean_object* v_pos_2619_; lean_object* v___y_2646_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___y_2704_; uint8_t v___x_2712_; 
v___f_2570_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0));
v___f_2616_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1));
v___x_2701_ = lean_nat_add(v_idx_2566_, v_fst_2559_);
lean_dec(v_fst_2559_);
v___x_2702_ = lean_byte_array_size(v_array_2565_);
v___x_2712_ = lean_nat_dec_le(v_idx_2566_, v___x_2487_);
if (v___x_2712_ == 0)
{
v___y_2704_ = v_idx_2566_;
goto v___jp_2703_;
}
else
{
lean_dec(v_idx_2566_);
v___y_2704_ = v___x_2487_;
goto v___jp_2703_;
}
v___jp_2571_:
{
lean_object* v___x_2575_; lean_object* v_snd_2576_; lean_object* v_snd_2577_; uint8_t v___x_2578_; 
v___x_2575_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2570_, v_maxSpaceSequence_2485_, v___x_2487_, v_pos_2573_);
v_snd_2576_ = lean_ctor_get(v___x_2575_, 1);
lean_inc(v_snd_2576_);
lean_dec_ref(v___x_2575_);
v_snd_2577_ = lean_ctor_get(v_snd_2576_, 1);
v___x_2578_ = lean_unbox(v_snd_2577_);
if (v___x_2578_ == 0)
{
lean_object* v_fst_2579_; lean_object* v_array_2580_; lean_object* v_idx_2581_; lean_object* v___x_2582_; uint8_t v___x_2583_; 
v_fst_2579_ = lean_ctor_get(v_snd_2576_, 0);
lean_inc(v_fst_2579_);
lean_dec(v_snd_2576_);
v_array_2580_ = lean_ctor_get(v_fst_2579_, 0);
v_idx_2581_ = lean_ctor_get(v_fst_2579_, 1);
v___x_2582_ = lean_byte_array_size(v_array_2580_);
v___x_2583_ = lean_nat_dec_lt(v_idx_2581_, v___x_2582_);
if (v___x_2583_ == 0)
{
v___y_2547_ = v___y_2572_;
v_pos_2548_ = v_fst_2579_;
v_res_2549_ = v_res_2574_;
goto v___jp_2546_;
}
else
{
uint8_t v___x_2584_; uint32_t v___x_2585_; uint32_t v___x_2586_; uint8_t v___x_2587_; 
v___x_2584_ = lean_byte_array_fget(v_array_2580_, v_idx_2581_);
v___x_2585_ = lean_uint8_to_uint32(v___x_2584_);
v___x_2586_ = 32;
v___x_2587_ = lean_uint32_dec_eq(v___x_2585_, v___x_2586_);
if (v___x_2587_ == 0)
{
uint32_t v___x_2588_; uint8_t v___x_2589_; 
v___x_2588_ = 9;
v___x_2589_ = lean_uint32_dec_eq(v___x_2585_, v___x_2588_);
if (v___x_2589_ == 0)
{
v___y_2547_ = v___y_2572_;
v_pos_2548_ = v_fst_2579_;
v_res_2549_ = v_res_2574_;
goto v___jp_2546_;
}
else
{
lean_dec(v_res_2574_);
lean_dec_ref(v___y_2572_);
v_pos_2480_ = v_fst_2579_;
goto v___jp_2479_;
}
}
else
{
lean_dec(v_res_2574_);
lean_dec_ref(v___y_2572_);
v_pos_2480_ = v_fst_2579_;
goto v___jp_2479_;
}
}
}
else
{
lean_object* v_fst_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2598_; 
lean_dec(v_res_2574_);
lean_dec_ref(v___y_2572_);
v_fst_2590_ = lean_ctor_get(v_snd_2576_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v_snd_2576_);
if (v_isSharedCheck_2598_ == 0)
{
lean_object* v_unused_2599_; 
v_unused_2599_ = lean_ctor_get(v_snd_2576_, 1);
lean_dec(v_unused_2599_);
v___x_2592_ = v_snd_2576_;
v_isShared_2593_ = v_isSharedCheck_2598_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_fst_2590_);
lean_dec(v_snd_2576_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2598_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2594_; lean_object* v___x_2596_; 
v___x_2594_ = lean_box(0);
if (v_isShared_2593_ == 0)
{
lean_ctor_set_tag(v___x_2592_, 1);
lean_ctor_set(v___x_2592_, 1, v___x_2594_);
v___x_2596_ = v___x_2592_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_fst_2590_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
v___jp_2600_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = l_ByteArray_toByteSlice(v___y_2603_, v_lower_2604_, v_upper_2605_);
v___x_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
v___y_2572_ = v___y_2602_;
v_pos_2573_ = v___y_2601_;
v_res_2574_ = v___x_2607_;
goto v___jp_2571_;
}
v___jp_2608_:
{
uint8_t v___x_2615_; 
v___x_2615_ = lean_nat_dec_le(v___y_2612_, v___y_2609_);
if (v___x_2615_ == 0)
{
lean_dec(v___y_2612_);
v___y_2601_ = v___y_2610_;
v___y_2602_ = v___y_2611_;
v___y_2603_ = v___y_2613_;
v_lower_2604_ = v___y_2614_;
v_upper_2605_ = v___y_2609_;
goto v___jp_2600_;
}
else
{
lean_dec(v___y_2609_);
v___y_2601_ = v___y_2610_;
v___y_2602_ = v___y_2611_;
v___y_2603_ = v___y_2613_;
v_lower_2604_ = v___y_2614_;
v_upper_2605_ = v___y_2612_;
goto v___jp_2600_;
}
}
v___jp_2617_:
{
lean_object* v___x_2620_; lean_object* v_snd_2621_; lean_object* v_snd_2622_; uint8_t v___x_2623_; 
lean_inc_ref(v_pos_2619_);
v___x_2620_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2616_, v_maxHeaderValueLength_2484_, v___x_2487_, v_pos_2619_);
v_snd_2621_ = lean_ctor_get(v___x_2620_, 1);
lean_inc(v_snd_2621_);
v_snd_2622_ = lean_ctor_get(v_snd_2621_, 1);
v___x_2623_ = lean_unbox(v_snd_2622_);
if (v___x_2623_ == 0)
{
lean_object* v_fst_2624_; lean_object* v_fst_2625_; lean_object* v_array_2626_; lean_object* v_idx_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; uint8_t v___x_2630_; 
v_fst_2624_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_fst_2624_);
lean_dec_ref(v___x_2620_);
v_fst_2625_ = lean_ctor_get(v_snd_2621_, 0);
lean_inc(v_fst_2625_);
lean_dec(v_snd_2621_);
v_array_2626_ = lean_ctor_get(v_pos_2619_, 0);
lean_inc_ref(v_array_2626_);
v_idx_2627_ = lean_ctor_get(v_pos_2619_, 1);
lean_inc(v_idx_2627_);
lean_dec_ref(v_pos_2619_);
v___x_2628_ = lean_nat_add(v_idx_2627_, v_fst_2624_);
lean_dec(v_fst_2624_);
v___x_2629_ = lean_byte_array_size(v_array_2626_);
v___x_2630_ = lean_nat_dec_le(v_idx_2627_, v___x_2487_);
if (v___x_2630_ == 0)
{
v___y_2609_ = v___x_2629_;
v___y_2610_ = v_fst_2625_;
v___y_2611_ = v___y_2618_;
v___y_2612_ = v___x_2628_;
v___y_2613_ = v_array_2626_;
v___y_2614_ = v_idx_2627_;
goto v___jp_2608_;
}
else
{
lean_dec(v_idx_2627_);
v___y_2609_ = v___x_2629_;
v___y_2610_ = v_fst_2625_;
v___y_2611_ = v___y_2618_;
v___y_2612_ = v___x_2628_;
v___y_2613_ = v_array_2626_;
v___y_2614_ = v___x_2487_;
goto v___jp_2608_;
}
}
else
{
lean_object* v_fst_2631_; lean_object* v_idx_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2643_; 
lean_dec_ref(v___x_2620_);
v_fst_2631_ = lean_ctor_get(v_snd_2621_, 0);
lean_inc(v_fst_2631_);
lean_dec(v_snd_2621_);
v_idx_2632_ = lean_ctor_get(v_pos_2619_, 1);
v_isSharedCheck_2643_ = !lean_is_exclusive(v_pos_2619_);
if (v_isSharedCheck_2643_ == 0)
{
lean_object* v_unused_2644_; 
v_unused_2644_ = lean_ctor_get(v_pos_2619_, 0);
lean_dec(v_unused_2644_);
v___x_2634_ = v_pos_2619_;
v_isShared_2635_ = v_isSharedCheck_2643_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_idx_2632_);
lean_dec(v_pos_2619_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2643_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v_idx_2636_; uint8_t v___x_2637_; 
v_idx_2636_ = lean_ctor_get(v_fst_2631_, 1);
v___x_2637_ = lean_nat_dec_eq(v_idx_2632_, v_idx_2636_);
lean_dec(v_idx_2632_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; lean_object* v___x_2640_; 
lean_dec_ref(v___y_2618_);
v___x_2638_ = lean_box(0);
if (v_isShared_2635_ == 0)
{
lean_ctor_set_tag(v___x_2634_, 1);
lean_ctor_set(v___x_2634_, 1, v___x_2638_);
lean_ctor_set(v___x_2634_, 0, v_fst_2631_);
v___x_2640_ = v___x_2634_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_fst_2631_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v___x_2638_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
else
{
lean_object* v___x_2642_; 
lean_del_object(v___x_2634_);
v___x_2642_ = lean_box(0);
v___y_2572_ = v___y_2618_;
v_pos_2573_ = v_fst_2631_;
v_res_2574_ = v___x_2642_;
goto v___jp_2571_;
}
}
}
}
v___jp_2645_:
{
lean_object* v_array_2647_; lean_object* v_idx_2648_; lean_object* v___x_2649_; uint8_t v___x_2650_; 
v_array_2647_ = lean_ctor_get(v_fst_2560_, 0);
v_idx_2648_ = lean_ctor_get(v_fst_2560_, 1);
v___x_2649_ = lean_byte_array_size(v_array_2647_);
v___x_2650_ = lean_nat_dec_lt(v_idx_2648_, v___x_2649_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2651_; lean_object* v___x_2653_; 
lean_dec_ref(v___y_2646_);
lean_dec_ref(v_array_2565_);
v___x_2651_ = lean_box(0);
if (v_isShared_2569_ == 0)
{
lean_ctor_set_tag(v___x_2568_, 1);
lean_ctor_set(v___x_2568_, 1, v___x_2651_);
lean_ctor_set(v___x_2568_, 0, v_fst_2560_);
v___x_2653_ = v___x_2568_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_fst_2560_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v___x_2651_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
else
{
uint8_t v___x_2655_; uint8_t v_got_2656_; uint8_t v___x_2657_; 
v___x_2655_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2);
v_got_2656_ = lean_byte_array_fget(v_array_2647_, v_idx_2648_);
v___x_2657_ = lean_uint8_dec_eq(v_got_2656_, v___x_2655_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; lean_object* v___x_2660_; 
lean_dec_ref(v___y_2646_);
lean_dec_ref(v_array_2565_);
v___x_2658_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__7);
if (v_isShared_2569_ == 0)
{
lean_ctor_set_tag(v___x_2568_, 1);
lean_ctor_set(v___x_2568_, 1, v___x_2658_);
lean_ctor_set(v___x_2568_, 0, v_fst_2560_);
v___x_2660_ = v___x_2568_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_fst_2560_);
lean_ctor_set(v_reuseFailAlloc_2661_, 1, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
else
{
lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2698_; 
lean_inc(v_idx_2648_);
lean_inc_ref(v_array_2647_);
lean_del_object(v___x_2568_);
v_isSharedCheck_2698_ = !lean_is_exclusive(v_fst_2560_);
if (v_isSharedCheck_2698_ == 0)
{
lean_object* v_unused_2699_; lean_object* v_unused_2700_; 
v_unused_2699_ = lean_ctor_get(v_fst_2560_, 1);
lean_dec(v_unused_2699_);
v_unused_2700_ = lean_ctor_get(v_fst_2560_, 0);
lean_dec(v_unused_2700_);
v___x_2663_ = v_fst_2560_;
v_isShared_2664_ = v_isSharedCheck_2698_;
goto v_resetjp_2662_;
}
else
{
lean_dec(v_fst_2560_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2698_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2668_; 
v___x_2665_ = lean_unsigned_to_nat(1u);
v___x_2666_ = lean_nat_add(v_idx_2648_, v___x_2665_);
lean_dec(v_idx_2648_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 1, v___x_2666_);
v___x_2668_ = v___x_2663_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_array_2647_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v___x_2666_);
v___x_2668_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
lean_object* v___x_2669_; lean_object* v_snd_2670_; lean_object* v_snd_2671_; uint8_t v___x_2672_; 
v___x_2669_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2570_, v_maxSpaceSequence_2485_, v___x_2487_, v___x_2668_);
v_snd_2670_ = lean_ctor_get(v___x_2669_, 1);
lean_inc(v_snd_2670_);
lean_dec_ref(v___x_2669_);
v_snd_2671_ = lean_ctor_get(v_snd_2670_, 1);
v___x_2672_ = lean_unbox(v_snd_2671_);
if (v___x_2672_ == 0)
{
lean_object* v_fst_2673_; lean_object* v_array_2674_; lean_object* v_idx_2675_; lean_object* v_lower_2676_; lean_object* v_upper_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; uint8_t v___x_2680_; 
v_fst_2673_ = lean_ctor_get(v_snd_2670_, 0);
lean_inc(v_fst_2673_);
lean_dec(v_snd_2670_);
v_array_2674_ = lean_ctor_get(v_fst_2673_, 0);
v_idx_2675_ = lean_ctor_get(v_fst_2673_, 1);
v_lower_2676_ = lean_ctor_get(v___y_2646_, 0);
lean_inc(v_lower_2676_);
v_upper_2677_ = lean_ctor_get(v___y_2646_, 1);
lean_inc(v_upper_2677_);
lean_dec_ref(v___y_2646_);
v___x_2678_ = l_ByteArray_toByteSlice(v_array_2565_, v_lower_2676_, v_upper_2677_);
v___x_2679_ = lean_byte_array_size(v_array_2674_);
v___x_2680_ = lean_nat_dec_lt(v_idx_2675_, v___x_2679_);
if (v___x_2680_ == 0)
{
v___y_2618_ = v___x_2678_;
v_pos_2619_ = v_fst_2673_;
goto v___jp_2617_;
}
else
{
uint8_t v___x_2681_; uint32_t v___x_2682_; uint32_t v___x_2683_; uint8_t v___x_2684_; 
v___x_2681_ = lean_byte_array_fget(v_array_2674_, v_idx_2675_);
v___x_2682_ = lean_uint8_to_uint32(v___x_2681_);
v___x_2683_ = 32;
v___x_2684_ = lean_uint32_dec_eq(v___x_2682_, v___x_2683_);
if (v___x_2684_ == 0)
{
uint32_t v___x_2685_; uint8_t v___x_2686_; 
v___x_2685_ = 9;
v___x_2686_ = lean_uint32_dec_eq(v___x_2682_, v___x_2685_);
if (v___x_2686_ == 0)
{
v___y_2618_ = v___x_2678_;
v_pos_2619_ = v_fst_2673_;
goto v___jp_2617_;
}
else
{
lean_dec_ref(v___x_2678_);
v_pos_2476_ = v_fst_2673_;
goto v___jp_2475_;
}
}
else
{
lean_dec_ref(v___x_2678_);
v_pos_2476_ = v_fst_2673_;
goto v___jp_2475_;
}
}
}
else
{
lean_object* v_fst_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2695_; 
lean_dec_ref(v___y_2646_);
lean_dec_ref(v_array_2565_);
v_fst_2687_ = lean_ctor_get(v_snd_2670_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v_snd_2670_);
if (v_isSharedCheck_2695_ == 0)
{
lean_object* v_unused_2696_; 
v_unused_2696_ = lean_ctor_get(v_snd_2670_, 1);
lean_dec(v_unused_2696_);
v___x_2689_ = v_snd_2670_;
v_isShared_2690_ = v_isSharedCheck_2695_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_fst_2687_);
lean_dec(v_snd_2670_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2695_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2691_; lean_object* v___x_2693_; 
v___x_2691_ = lean_box(0);
if (v_isShared_2690_ == 0)
{
lean_ctor_set_tag(v___x_2689_, 1);
lean_ctor_set(v___x_2689_, 1, v___x_2691_);
v___x_2693_ = v___x_2689_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_fst_2687_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v___x_2691_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
}
}
}
}
v___jp_2703_:
{
uint8_t v___x_2705_; 
v___x_2705_ = lean_nat_dec_le(v___x_2701_, v___x_2702_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2707_; 
lean_dec(v___x_2701_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 1, v___x_2702_);
lean_ctor_set(v___x_2562_, 0, v___y_2704_);
v___x_2707_ = v___x_2562_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___y_2704_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v___x_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
v___y_2646_ = v___x_2707_;
goto v___jp_2645_;
}
}
else
{
lean_object* v___x_2710_; 
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 1, v___x_2701_);
lean_ctor_set(v___x_2562_, 0, v___y_2704_);
v___x_2710_ = v___x_2562_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___y_2704_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v___x_2701_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
v___y_2646_ = v___x_2710_;
goto v___jp_2645_;
}
}
}
}
}
else
{
lean_object* v___x_2714_; lean_object* v___x_2716_; 
lean_dec(v_fst_2560_);
lean_dec(v_fst_2559_);
v___x_2714_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_2563_ == 0)
{
lean_ctor_set_tag(v___x_2562_, 1);
lean_ctor_set(v___x_2562_, 1, v___x_2714_);
lean_ctor_set(v___x_2562_, 0, v_a_2474_);
v___x_2716_ = v___x_2562_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2474_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v___x_2714_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
else
{
lean_object* v_fst_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2728_; 
lean_dec_ref(v___x_2555_);
lean_dec_ref(v_a_2474_);
v_fst_2720_ = lean_ctor_get(v_snd_2556_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v_snd_2556_);
if (v_isSharedCheck_2728_ == 0)
{
lean_object* v_unused_2729_; 
v_unused_2729_ = lean_ctor_get(v_snd_2556_, 1);
lean_dec(v_unused_2729_);
v___x_2722_ = v_snd_2556_;
v_isShared_2723_ = v_isSharedCheck_2728_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_fst_2720_);
lean_dec(v_snd_2556_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2728_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2724_; lean_object* v___x_2726_; 
v___x_2724_ = lean_box(0);
if (v_isShared_2723_ == 0)
{
lean_ctor_set_tag(v___x_2722_, 1);
lean_ctor_set(v___x_2722_, 1, v___x_2724_);
v___x_2726_ = v___x_2722_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_fst_2720_);
lean_ctor_set(v_reuseFailAlloc_2727_, 1, v___x_2724_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
v___jp_2475_:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2477_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2478_, 0, v_pos_2476_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
return v___x_2478_;
}
v___jp_2479_:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2482_, 0, v_pos_2480_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
return v___x_2482_;
}
v___jp_2488_:
{
lean_object* v___x_2492_; 
v___x_2492_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___y_2491_, v___y_2490_);
lean_dec(v___y_2491_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_pos_2493_; lean_object* v_res_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2507_; 
v_pos_2493_ = lean_ctor_get(v___x_2492_, 0);
v_res_2494_ = lean_ctor_get(v___x_2492_, 1);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2496_ = v___x_2492_;
v_isShared_2497_ = v_isSharedCheck_2507_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_res_2494_);
lean_inc(v_pos_2493_);
lean_dec(v___x_2492_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2507_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2505_; 
v___x_2498_ = lean_string_utf8_byte_size(v_res_2494_);
lean_inc(v_res_2494_);
v___x_2499_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2499_, 0, v_res_2494_);
lean_ctor_set(v___x_2499_, 1, v___x_2487_);
lean_ctor_set(v___x_2499_, 2, v___x_2498_);
v___x_2500_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(v___x_2499_, v___x_2498_);
lean_dec_ref_known(v___x_2499_, 3);
v___x_2501_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2501_, 0, v_res_2494_);
lean_ctor_set(v___x_2501_, 1, v___x_2487_);
lean_ctor_set(v___x_2501_, 2, v___x_2500_);
v___x_2502_ = l_String_Slice_toString(v___x_2501_);
lean_dec_ref_known(v___x_2501_, 3);
v___x_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___y_2489_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 1, v___x_2503_);
v___x_2505_ = v___x_2496_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_pos_2493_);
lean_ctor_set(v_reuseFailAlloc_2506_, 1, v___x_2503_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
else
{
lean_object* v_pos_2508_; lean_object* v_err_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
lean_dec_ref(v___y_2489_);
v_pos_2508_ = lean_ctor_get(v___x_2492_, 0);
v_err_2509_ = lean_ctor_get(v___x_2492_, 1);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2492_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_err_2509_);
lean_inc(v_pos_2508_);
lean_dec(v___x_2492_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_pos_2508_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_err_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
v___jp_2517_:
{
uint8_t v___x_2521_; 
v___x_2521_ = lean_string_validate_utf8(v___y_2520_);
if (v___x_2521_ == 0)
{
lean_object* v___x_2522_; 
lean_dec_ref(v___y_2520_);
v___x_2522_ = lean_box(0);
v___y_2489_ = v___y_2518_;
v___y_2490_ = v___y_2519_;
v___y_2491_ = v___x_2522_;
goto v___jp_2488_;
}
else
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = lean_string_from_utf8_unchecked(v___y_2520_);
v___x_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2523_);
v___y_2489_ = v___y_2518_;
v___y_2490_ = v___y_2519_;
v___y_2491_ = v___x_2524_;
goto v___jp_2488_;
}
}
v___jp_2525_:
{
lean_object* v___x_2529_; 
v___x_2529_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___y_2528_, v___y_2527_);
lean_dec(v___y_2528_);
if (lean_obj_tag(v___x_2529_) == 0)
{
if (lean_obj_tag(v___y_2526_) == 0)
{
lean_object* v_pos_2530_; lean_object* v_res_2531_; lean_object* v___x_2532_; 
v_pos_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_pos_2530_);
v_res_2531_ = lean_ctor_get(v___x_2529_, 1);
lean_inc(v_res_2531_);
lean_dec_ref_known(v___x_2529_, 2);
v___x_2532_ = l_ByteArray_empty;
v___y_2518_ = v_res_2531_;
v___y_2519_ = v_pos_2530_;
v___y_2520_ = v___x_2532_;
goto v___jp_2517_;
}
else
{
lean_object* v_pos_2533_; lean_object* v_res_2534_; lean_object* v_val_2535_; lean_object* v___x_2536_; 
v_pos_2533_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_pos_2533_);
v_res_2534_ = lean_ctor_get(v___x_2529_, 1);
lean_inc(v_res_2534_);
lean_dec_ref_known(v___x_2529_, 2);
v_val_2535_ = lean_ctor_get(v___y_2526_, 0);
lean_inc(v_val_2535_);
lean_dec_ref_known(v___y_2526_, 1);
v___x_2536_ = l_ByteSlice_toByteArray(v_val_2535_);
v___y_2518_ = v_res_2534_;
v___y_2519_ = v_pos_2533_;
v___y_2520_ = v___x_2536_;
goto v___jp_2517_;
}
}
else
{
lean_object* v_pos_2537_; lean_object* v_err_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec(v___y_2526_);
v_pos_2537_ = lean_ctor_get(v___x_2529_, 0);
v_err_2538_ = lean_ctor_get(v___x_2529_, 1);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2529_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_err_2538_);
lean_inc(v_pos_2537_);
lean_dec(v___x_2529_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_pos_2537_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v_err_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
v___jp_2546_:
{
lean_object* v___x_2550_; uint8_t v___x_2551_; 
v___x_2550_ = l_ByteSlice_toByteArray(v___y_2547_);
v___x_2551_ = lean_string_validate_utf8(v___x_2550_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; 
lean_dec_ref(v___x_2550_);
v___x_2552_ = lean_box(0);
v___y_2526_ = v_res_2549_;
v___y_2527_ = v_pos_2548_;
v___y_2528_ = v___x_2552_;
goto v___jp_2525_;
}
else
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = lean_string_from_utf8_unchecked(v___x_2550_);
v___x_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
v___y_2526_ = v_res_2549_;
v___y_2527_ = v_pos_2548_;
v___y_2528_ = v___x_2554_;
goto v___jp_2525_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___boxed(lean_object* v_limits_2730_, lean_object* v_a_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_2730_, v_a_2731_);
lean_dec_ref(v_limits_2730_);
return v_res_2732_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(lean_object* v_x_2733_, lean_object* v_x_2734_){
_start:
{
if (lean_obj_tag(v_x_2733_) == 0)
{
if (lean_obj_tag(v_x_2734_) == 0)
{
uint8_t v___x_2735_; 
v___x_2735_ = 1;
return v___x_2735_;
}
else
{
uint8_t v___x_2736_; 
v___x_2736_ = 0;
return v___x_2736_;
}
}
else
{
if (lean_obj_tag(v_x_2734_) == 0)
{
uint8_t v___x_2737_; 
v___x_2737_ = 0;
return v___x_2737_;
}
else
{
lean_object* v_val_2738_; lean_object* v_val_2739_; uint8_t v___x_2740_; uint8_t v___x_2741_; uint8_t v___x_2742_; 
v_val_2738_ = lean_ctor_get(v_x_2733_, 0);
v_val_2739_ = lean_ctor_get(v_x_2734_, 0);
v___x_2740_ = lean_unbox(v_val_2738_);
v___x_2741_ = lean_unbox(v_val_2739_);
v___x_2742_ = lean_uint8_dec_eq(v___x_2740_, v___x_2741_);
return v___x_2742_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0___boxed(lean_object* v_x_2743_, lean_object* v_x_2744_){
_start:
{
uint8_t v_res_2745_; lean_object* v_r_2746_; 
v_res_2745_ = l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_x_2743_, v_x_2744_);
lean_dec(v_x_2744_);
lean_dec(v_x_2743_);
v_r_2746_ = lean_box(v_res_2745_);
return v_r_2746_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_parseSingleHeader___closed__0(void){
_start:
{
uint8_t v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2747_ = lean_uint8_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0);
v___x_2748_ = lean_box(v___x_2747_);
v___x_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2748_);
return v___x_2749_;
}
}
static uint8_t _init_l_Std_Http_Protocol_H1_parseSingleHeader___closed__1(void){
_start:
{
uint32_t v___x_2750_; uint8_t v___x_2751_; 
v___x_2750_ = 10;
v___x_2751_ = lean_uint32_to_uint8(v___x_2750_);
return v___x_2751_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_parseSingleHeader___closed__2(void){
_start:
{
uint8_t v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2752_ = lean_uint8_once(&l_Std_Http_Protocol_H1_parseSingleHeader___closed__1, &l_Std_Http_Protocol_H1_parseSingleHeader___closed__1_once, _init_l_Std_Http_Protocol_H1_parseSingleHeader___closed__1);
v___x_2753_ = lean_box(v___x_2752_);
v___x_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader(lean_object* v_limits_2755_, lean_object* v_a_2756_){
_start:
{
lean_object* v_pos_2758_; lean_object* v_res_2759_; lean_object* v___y_2763_; uint8_t v___y_2764_; lean_object* v_pos_2813_; lean_object* v_res_2814_; lean_object* v_array_2819_; lean_object* v_idx_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; 
v_array_2819_ = lean_ctor_get(v_a_2756_, 0);
v_idx_2820_ = lean_ctor_get(v_a_2756_, 1);
v___x_2821_ = lean_byte_array_size(v_array_2819_);
v___x_2822_ = lean_nat_dec_lt(v_idx_2820_, v___x_2821_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; 
v___x_2823_ = lean_box(0);
v_pos_2813_ = v_a_2756_;
v_res_2814_ = v___x_2823_;
goto v___jp_2812_;
}
else
{
uint8_t v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2824_ = lean_byte_array_fget(v_array_2819_, v_idx_2820_);
v___x_2825_ = lean_box(v___x_2824_);
v___x_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
v_pos_2813_ = v_a_2756_;
v_res_2814_ = v___x_2826_;
goto v___jp_2812_;
}
v___jp_2757_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2760_, 0, v_res_2759_);
v___x_2761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2761_, 0, v_pos_2758_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
return v___x_2761_;
}
v___jp_2762_:
{
if (v___y_2764_ == 0)
{
lean_object* v___x_2765_; 
v___x_2765_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_2755_, v___y_2763_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_pos_2766_; lean_object* v_res_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v_pos_2766_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_pos_2766_);
v_res_2767_ = lean_ctor_get(v___x_2765_, 1);
lean_inc(v_res_2767_);
lean_dec_ref_known(v___x_2765_, 2);
v___x_2768_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2769_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2768_, v_pos_2766_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_pos_2770_; 
v_pos_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc(v_pos_2770_);
lean_dec_ref_known(v___x_2769_, 2);
v_pos_2758_ = v_pos_2770_;
v_res_2759_ = v_res_2767_;
goto v___jp_2757_;
}
else
{
lean_object* v_pos_2771_; lean_object* v_err_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_dec(v_res_2767_);
v_pos_2771_ = lean_ctor_get(v___x_2769_, 0);
v_err_2772_ = lean_ctor_get(v___x_2769_, 1);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2769_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_err_2772_);
lean_inc(v_pos_2771_);
lean_dec(v___x_2769_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_pos_2771_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_err_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_pos_2780_; lean_object* v_res_2781_; 
v_pos_2780_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_pos_2780_);
v_res_2781_ = lean_ctor_get(v___x_2765_, 1);
lean_inc(v_res_2781_);
lean_dec_ref_known(v___x_2765_, 2);
v_pos_2758_ = v_pos_2780_;
v_res_2759_ = v_res_2781_;
goto v___jp_2757_;
}
else
{
lean_object* v_pos_2782_; lean_object* v_err_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
v_pos_2782_ = lean_ctor_get(v___x_2765_, 0);
v_err_2783_ = lean_ctor_get(v___x_2765_, 1);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2765_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_err_2783_);
lean_inc(v_pos_2782_);
lean_dec(v___x_2765_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_pos_2782_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v_err_2783_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
}
else
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2792_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2791_, v___y_2763_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_pos_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2801_; 
v_pos_2793_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2801_ == 0)
{
lean_object* v_unused_2802_; 
v_unused_2802_ = lean_ctor_get(v___x_2792_, 1);
lean_dec(v_unused_2802_);
v___x_2795_ = v___x_2792_;
v_isShared_2796_ = v_isSharedCheck_2801_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_pos_2793_);
lean_dec(v___x_2792_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2801_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2797_; lean_object* v___x_2799_; 
v___x_2797_ = lean_box(0);
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 1, v___x_2797_);
v___x_2799_ = v___x_2795_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_pos_2793_);
lean_ctor_set(v_reuseFailAlloc_2800_, 1, v___x_2797_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
else
{
lean_object* v_pos_2803_; lean_object* v_err_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
v_pos_2803_ = lean_ctor_get(v___x_2792_, 0);
v_err_2804_ = lean_ctor_get(v___x_2792_, 1);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2792_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_err_2804_);
lean_inc(v_pos_2803_);
lean_dec(v___x_2792_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_pos_2803_);
lean_ctor_set(v_reuseFailAlloc_2810_, 1, v_err_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
}
v___jp_2812_:
{
lean_object* v___x_2815_; uint8_t v___x_2816_; 
v___x_2815_ = lean_obj_once(&l_Std_Http_Protocol_H1_parseSingleHeader___closed__0, &l_Std_Http_Protocol_H1_parseSingleHeader___closed__0_once, _init_l_Std_Http_Protocol_H1_parseSingleHeader___closed__0);
v___x_2816_ = l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_2814_, v___x_2815_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2817_; uint8_t v___x_2818_; 
v___x_2817_ = lean_obj_once(&l_Std_Http_Protocol_H1_parseSingleHeader___closed__2, &l_Std_Http_Protocol_H1_parseSingleHeader___closed__2_once, _init_l_Std_Http_Protocol_H1_parseSingleHeader___closed__2);
v___x_2818_ = l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_2814_, v___x_2817_);
lean_dec(v_res_2814_);
v___y_2763_ = v_pos_2813_;
v___y_2764_ = v___x_2818_;
goto v___jp_2762_;
}
else
{
lean_dec(v_res_2814_);
v___y_2763_ = v_pos_2813_;
v___y_2764_ = v___x_2816_;
goto v___jp_2762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader___boxed(lean_object* v_limits_2827_, lean_object* v_a_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_2827_, v_a_2828_);
lean_dec_ref(v_limits_2827_);
return v_res_2829_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0(void){
_start:
{
uint32_t v___x_2830_; uint8_t v___x_2831_; 
v___x_2830_ = 92;
v___x_2831_ = lean_uint32_to_uint8(v___x_2830_);
return v___x_2831_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1(void){
_start:
{
uint8_t v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0);
v___x_2833_ = lean_uint8_to_nat(v___x_2832_);
return v___x_2833_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2(void){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1);
v___x_2835_ = l_Nat_reprFast(v___x_2834_);
return v___x_2835_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__3(void){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2836_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2);
v___x_2837_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_2838_ = lean_string_append(v___x_2837_, v___x_2836_);
return v___x_2838_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__4(void){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2839_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__5));
v___x_2840_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__3);
v___x_2841_ = lean_string_append(v___x_2840_, v___x_2839_);
return v___x_2841_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__5(void){
_start:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2842_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__4);
v___x_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2842_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair(lean_object* v_a_2845_){
_start:
{
lean_object* v_array_2846_; lean_object* v_idx_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; 
v_array_2846_ = lean_ctor_get(v_a_2845_, 0);
v_idx_2847_ = lean_ctor_get(v_a_2845_, 1);
v___x_2848_ = lean_byte_array_size(v_array_2846_);
v___x_2849_ = lean_nat_dec_lt(v_idx_2847_, v___x_2848_);
if (v___x_2849_ == 0)
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2850_ = lean_box(0);
v___x_2851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2851_, 0, v_a_2845_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
return v___x_2851_;
}
else
{
uint8_t v___x_2852_; uint8_t v_got_2853_; uint8_t v___x_2854_; 
v___x_2852_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0);
v_got_2853_ = lean_byte_array_fget(v_array_2846_, v_idx_2847_);
v___x_2854_ = lean_uint8_dec_eq(v_got_2853_, v___x_2852_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2855_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__5, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__5_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__5);
v___x_2856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2856_, 0, v_a_2845_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
return v___x_2856_;
}
else
{
lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2891_; 
lean_inc(v_idx_2847_);
lean_inc_ref(v_array_2846_);
v_isSharedCheck_2891_ = !lean_is_exclusive(v_a_2845_);
if (v_isSharedCheck_2891_ == 0)
{
lean_object* v_unused_2892_; lean_object* v_unused_2893_; 
v_unused_2892_ = lean_ctor_get(v_a_2845_, 1);
lean_dec(v_unused_2892_);
v_unused_2893_ = lean_ctor_get(v_a_2845_, 0);
lean_dec(v_unused_2893_);
v___x_2858_ = v_a_2845_;
v_isShared_2859_ = v_isSharedCheck_2891_;
goto v_resetjp_2857_;
}
else
{
lean_dec(v_a_2845_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2891_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; uint8_t v___x_2862_; 
v___x_2860_ = lean_unsigned_to_nat(1u);
v___x_2861_ = lean_nat_add(v_idx_2847_, v___x_2860_);
lean_dec(v_idx_2847_);
v___x_2862_ = lean_nat_dec_lt(v___x_2861_, v___x_2848_);
if (v___x_2862_ == 0)
{
lean_object* v___x_2864_; 
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 1, v___x_2861_);
v___x_2864_ = v___x_2858_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_array_2846_);
lean_ctor_set(v_reuseFailAlloc_2867_, 1, v___x_2861_);
v___x_2864_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2865_ = lean_box(0);
v___x_2866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2864_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
return v___x_2866_;
}
}
else
{
uint8_t v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2871_; 
v___x_2868_ = lean_byte_array_fget(v_array_2846_, v___x_2861_);
v___x_2869_ = lean_nat_add(v___x_2861_, v___x_2860_);
lean_dec(v___x_2861_);
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 1, v___x_2869_);
v___x_2871_ = v___x_2858_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_array_2846_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v___x_2869_);
v___x_2871_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; uint32_t v___x_2874_; uint8_t v___y_2876_; uint32_t v___x_2882_; uint8_t v___x_2883_; 
v___x_2872_ = lean_box(v___x_2868_);
lean_inc_ref(v___x_2871_);
v___x_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2871_);
lean_ctor_set(v___x_2873_, 1, v___x_2872_);
v___x_2874_ = lean_uint8_to_uint32(v___x_2868_);
v___x_2882_ = 9;
v___x_2883_ = lean_uint32_dec_eq(v___x_2874_, v___x_2882_);
if (v___x_2883_ == 0)
{
uint32_t v___x_2884_; uint8_t v___x_2885_; 
v___x_2884_ = 32;
v___x_2885_ = lean_uint32_dec_eq(v___x_2874_, v___x_2884_);
if (v___x_2885_ == 0)
{
uint32_t v___x_2886_; uint8_t v___x_2887_; 
v___x_2886_ = 33;
v___x_2887_ = lean_uint32_dec_le(v___x_2886_, v___x_2874_);
if (v___x_2887_ == 0)
{
v___y_2876_ = v___x_2887_;
goto v___jp_2875_;
}
else
{
uint32_t v___x_2888_; uint8_t v___x_2889_; 
v___x_2888_ = 126;
v___x_2889_ = lean_uint32_dec_le(v___x_2874_, v___x_2888_);
v___y_2876_ = v___x_2889_;
goto v___jp_2875_;
}
}
else
{
lean_dec_ref(v___x_2871_);
return v___x_2873_;
}
}
else
{
lean_dec_ref(v___x_2871_);
return v___x_2873_;
}
v___jp_2875_:
{
if (v___y_2876_ == 0)
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
lean_dec_ref_known(v___x_2873_, 2);
v___x_2877_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__6));
v___x_2878_ = l_Char_quote(v___x_2874_);
v___x_2879_ = lean_string_append(v___x_2877_, v___x_2878_);
lean_dec_ref(v___x_2878_);
v___x_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
v___x_2881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2871_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
return v___x_2881_;
}
else
{
lean_dec_ref(v___x_2871_);
return v___x_2873_;
}
}
}
}
}
}
}
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2(void){
_start:
{
uint32_t v___x_2897_; uint8_t v___x_2898_; 
v___x_2897_ = 34;
v___x_2898_ = lean_uint32_to_uint8(v___x_2897_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(lean_object* v_maxLength_2900_, lean_object* v_buf_2901_, lean_object* v_length_2902_, lean_object* v_a_2903_){
_start:
{
lean_object* v_array_2904_; lean_object* v_idx_2905_; lean_object* v___x_2906_; uint8_t v___x_2907_; 
v_array_2904_ = lean_ctor_get(v_a_2903_, 0);
v_idx_2905_ = lean_ctor_get(v_a_2903_, 1);
v___x_2906_ = lean_byte_array_size(v_array_2904_);
v___x_2907_ = lean_nat_dec_lt(v_idx_2905_, v___x_2906_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2908_; lean_object* v___x_2909_; 
lean_dec(v_length_2902_);
lean_dec_ref(v_buf_2901_);
v___x_2908_ = lean_box(0);
v___x_2909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2909_, 0, v_a_2903_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
return v___x_2909_;
}
else
{
lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2984_; 
lean_inc(v_idx_2905_);
lean_inc_ref(v_array_2904_);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_a_2903_);
if (v_isSharedCheck_2984_ == 0)
{
lean_object* v_unused_2985_; lean_object* v_unused_2986_; 
v_unused_2985_ = lean_ctor_get(v_a_2903_, 1);
lean_dec(v_unused_2985_);
v_unused_2986_ = lean_ctor_get(v_a_2903_, 0);
lean_dec(v_unused_2986_);
v___x_2911_ = v_a_2903_;
v_isShared_2912_ = v_isSharedCheck_2984_;
goto v_resetjp_2910_;
}
else
{
lean_dec(v_a_2903_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2984_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
uint8_t v_c_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v_it_x27_2917_; 
v_c_2913_ = lean_byte_array_fget(v_array_2904_, v_idx_2905_);
v___x_2914_ = lean_unsigned_to_nat(1u);
v___x_2915_ = lean_nat_add(v_idx_2905_, v___x_2914_);
lean_dec(v_idx_2905_);
lean_inc(v___x_2915_);
lean_inc_ref(v_array_2904_);
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 1, v___x_2915_);
v_it_x27_2917_ = v___x_2911_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_array_2904_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v___x_2915_);
v_it_x27_2917_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
uint8_t v___x_2925_; uint8_t v___x_2926_; 
v___x_2925_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2);
v___x_2926_ = lean_uint8_dec_eq(v_c_2913_, v___x_2925_);
if (v___x_2926_ == 0)
{
uint8_t v___x_2927_; uint8_t v___x_2928_; 
v___x_2927_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0);
v___x_2928_ = lean_uint8_dec_eq(v_c_2913_, v___x_2927_);
if (v___x_2928_ == 0)
{
uint32_t v___x_2929_; uint8_t v___y_2931_; uint8_t v___y_2938_; uint32_t v___x_2943_; uint8_t v___x_2944_; 
lean_dec(v___x_2915_);
lean_dec_ref(v_array_2904_);
v___x_2929_ = lean_uint8_to_uint32(v_c_2913_);
v___x_2943_ = 9;
v___x_2944_ = lean_uint32_dec_eq(v___x_2929_, v___x_2943_);
if (v___x_2944_ == 0)
{
uint32_t v___x_2945_; uint8_t v___x_2946_; 
v___x_2945_ = 32;
v___x_2946_ = lean_uint32_dec_eq(v___x_2929_, v___x_2945_);
if (v___x_2946_ == 0)
{
uint32_t v___x_2947_; uint8_t v___x_2948_; 
v___x_2947_ = 33;
v___x_2948_ = lean_uint32_dec_eq(v___x_2929_, v___x_2947_);
if (v___x_2948_ == 0)
{
uint32_t v___x_2949_; uint8_t v___x_2950_; 
v___x_2949_ = 35;
v___x_2950_ = lean_uint32_dec_le(v___x_2949_, v___x_2929_);
if (v___x_2950_ == 0)
{
v___y_2938_ = v___x_2950_;
goto v___jp_2937_;
}
else
{
uint32_t v___x_2951_; uint8_t v___x_2952_; 
v___x_2951_ = 91;
v___x_2952_ = lean_uint32_dec_le(v___x_2929_, v___x_2951_);
v___y_2938_ = v___x_2952_;
goto v___jp_2937_;
}
}
else
{
goto v___jp_2918_;
}
}
else
{
goto v___jp_2918_;
}
}
else
{
goto v___jp_2918_;
}
v___jp_2930_:
{
if (v___y_2931_ == 0)
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
lean_dec(v_length_2902_);
lean_dec_ref(v_buf_2901_);
v___x_2932_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3));
v___x_2933_ = l_Char_quote(v___x_2929_);
v___x_2934_ = lean_string_append(v___x_2932_, v___x_2933_);
lean_dec_ref(v___x_2933_);
v___x_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2934_);
v___x_2936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2936_, 0, v_it_x27_2917_);
lean_ctor_set(v___x_2936_, 1, v___x_2935_);
return v___x_2936_;
}
else
{
goto v___jp_2918_;
}
}
v___jp_2937_:
{
if (v___y_2938_ == 0)
{
uint32_t v___x_2939_; uint8_t v___x_2940_; 
v___x_2939_ = 93;
v___x_2940_ = lean_uint32_dec_le(v___x_2939_, v___x_2929_);
if (v___x_2940_ == 0)
{
v___y_2931_ = v___x_2940_;
goto v___jp_2930_;
}
else
{
uint32_t v___x_2941_; uint8_t v___x_2942_; 
v___x_2941_ = 126;
v___x_2942_ = lean_uint32_dec_le(v___x_2929_, v___x_2941_);
v___y_2931_ = v___x_2942_;
goto v___jp_2930_;
}
}
else
{
goto v___jp_2918_;
}
}
}
else
{
uint8_t v___x_2953_; 
v___x_2953_ = lean_nat_dec_lt(v___x_2915_, v___x_2906_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
lean_dec(v___x_2915_);
lean_dec_ref(v_array_2904_);
lean_dec(v_length_2902_);
lean_dec_ref(v_buf_2901_);
v___x_2954_ = lean_box(0);
v___x_2955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2955_, 0, v_it_x27_2917_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
return v___x_2955_;
}
else
{
uint8_t v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; uint32_t v___x_2966_; uint8_t v___y_2968_; uint32_t v___x_2974_; uint8_t v___x_2975_; 
lean_dec_ref(v_it_x27_2917_);
v___x_2956_ = lean_byte_array_fget(v_array_2904_, v___x_2915_);
v___x_2957_ = lean_nat_add(v___x_2915_, v___x_2914_);
lean_dec(v___x_2915_);
v___x_2958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2958_, 0, v_array_2904_);
lean_ctor_set(v___x_2958_, 1, v___x_2957_);
v___x_2966_ = lean_uint8_to_uint32(v___x_2956_);
v___x_2974_ = 9;
v___x_2975_ = lean_uint32_dec_eq(v___x_2966_, v___x_2974_);
if (v___x_2975_ == 0)
{
uint32_t v___x_2976_; uint8_t v___x_2977_; 
v___x_2976_ = 32;
v___x_2977_ = lean_uint32_dec_eq(v___x_2966_, v___x_2976_);
if (v___x_2977_ == 0)
{
uint32_t v___x_2978_; uint8_t v___x_2979_; 
v___x_2978_ = 33;
v___x_2979_ = lean_uint32_dec_le(v___x_2978_, v___x_2966_);
if (v___x_2979_ == 0)
{
v___y_2968_ = v___x_2979_;
goto v___jp_2967_;
}
else
{
uint32_t v___x_2980_; uint8_t v___x_2981_; 
v___x_2980_ = 126;
v___x_2981_ = lean_uint32_dec_le(v___x_2966_, v___x_2980_);
v___y_2968_ = v___x_2981_;
goto v___jp_2967_;
}
}
else
{
goto v___jp_2959_;
}
}
else
{
goto v___jp_2959_;
}
v___jp_2959_:
{
lean_object* v___x_2960_; uint8_t v___x_2961_; 
v___x_2960_ = lean_nat_add(v_length_2902_, v___x_2914_);
lean_dec(v_length_2902_);
v___x_2961_ = lean_nat_dec_lt(v_maxLength_2900_, v___x_2960_);
if (v___x_2961_ == 0)
{
lean_object* v___x_2962_; 
v___x_2962_ = lean_byte_array_push(v_buf_2901_, v___x_2956_);
v_buf_2901_ = v___x_2962_;
v_length_2902_ = v___x_2960_;
v_a_2903_ = v___x_2958_;
goto _start;
}
else
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_dec(v___x_2960_);
lean_dec_ref(v_buf_2901_);
v___x_2964_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_2965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2958_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
return v___x_2965_;
}
}
v___jp_2967_:
{
if (v___y_2968_ == 0)
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
lean_dec(v_length_2902_);
lean_dec_ref(v_buf_2901_);
v___x_2969_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__6));
v___x_2970_ = l_Char_quote(v___x_2966_);
v___x_2971_ = lean_string_append(v___x_2969_, v___x_2970_);
lean_dec_ref(v___x_2970_);
v___x_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2971_);
v___x_2973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2958_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
return v___x_2973_;
}
else
{
goto v___jp_2959_;
}
}
}
}
}
else
{
lean_object* v___x_2982_; 
lean_dec(v___x_2915_);
lean_dec_ref(v_array_2904_);
lean_dec(v_length_2902_);
v___x_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2982_, 0, v_it_x27_2917_);
lean_ctor_set(v___x_2982_, 1, v_buf_2901_);
return v___x_2982_;
}
v___jp_2918_:
{
lean_object* v___x_2919_; uint8_t v___x_2920_; 
v___x_2919_ = lean_nat_add(v_length_2902_, v___x_2914_);
lean_dec(v_length_2902_);
v___x_2920_ = lean_nat_dec_lt(v_maxLength_2900_, v___x_2919_);
if (v___x_2920_ == 0)
{
lean_object* v___x_2921_; 
v___x_2921_ = lean_byte_array_push(v_buf_2901_, v_c_2913_);
v_buf_2901_ = v___x_2921_;
v_length_2902_ = v___x_2919_;
v_a_2903_ = v_it_x27_2917_;
goto _start;
}
else
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
lean_dec(v___x_2919_);
lean_dec_ref(v_buf_2901_);
v___x_2923_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_2924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2924_, 0, v_it_x27_2917_);
lean_ctor_set(v___x_2924_, 1, v___x_2923_);
return v___x_2924_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___boxed(lean_object* v_maxLength_2987_, lean_object* v_buf_2988_, lean_object* v_length_2989_, lean_object* v_a_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_2987_, v_buf_2988_, v_length_2989_, v_a_2990_);
lean_dec(v_maxLength_2987_);
return v_res_2991_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__0(void){
_start:
{
uint8_t v___x_2992_; lean_object* v___x_2993_; 
v___x_2992_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2);
v___x_2993_ = lean_uint8_to_nat(v___x_2992_);
return v___x_2993_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1(void){
_start:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__0);
v___x_2995_ = l_Nat_reprFast(v___x_2994_);
return v___x_2995_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__2(void){
_start:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2996_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1);
v___x_2997_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_2998_ = lean_string_append(v___x_2997_, v___x_2996_);
return v___x_2998_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__3(void){
_start:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_2999_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__5));
v___x_3000_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__2);
v___x_3001_ = lean_string_append(v___x_3000_, v___x_2999_);
return v___x_3001_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__4(void){
_start:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3002_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__3);
v___x_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(lean_object* v_maxLength_3004_, lean_object* v_a_3005_){
_start:
{
lean_object* v_array_3006_; lean_object* v_idx_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v_array_3006_ = lean_ctor_get(v_a_3005_, 0);
v_idx_3007_ = lean_ctor_get(v_a_3005_, 1);
v___x_3008_ = lean_byte_array_size(v_array_3006_);
v___x_3009_ = lean_nat_dec_lt(v_idx_3007_, v___x_3008_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3010_ = lean_box(0);
v___x_3011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3011_, 0, v_a_3005_);
lean_ctor_set(v___x_3011_, 1, v___x_3010_);
return v___x_3011_;
}
else
{
uint8_t v___x_3012_; uint8_t v_got_3013_; uint8_t v___x_3014_; 
v___x_3012_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2);
v_got_3013_ = lean_byte_array_fget(v_array_3006_, v_idx_3007_);
v___x_3014_ = lean_uint8_dec_eq(v_got_3013_, v___x_3012_);
if (v___x_3014_ == 0)
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__4);
v___x_3016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3016_, 0, v_a_3005_);
lean_ctor_set(v___x_3016_, 1, v___x_3015_);
return v___x_3016_;
}
else
{
lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3045_; 
lean_inc(v_idx_3007_);
lean_inc_ref(v_array_3006_);
v_isSharedCheck_3045_ = !lean_is_exclusive(v_a_3005_);
if (v_isSharedCheck_3045_ == 0)
{
lean_object* v_unused_3046_; lean_object* v_unused_3047_; 
v_unused_3046_ = lean_ctor_get(v_a_3005_, 1);
lean_dec(v_unused_3046_);
v_unused_3047_ = lean_ctor_get(v_a_3005_, 0);
lean_dec(v_unused_3047_);
v___x_3018_ = v_a_3005_;
v_isShared_3019_ = v_isSharedCheck_3045_;
goto v_resetjp_3017_;
}
else
{
lean_dec(v_a_3005_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3045_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3023_; 
v___x_3020_ = lean_unsigned_to_nat(1u);
v___x_3021_ = lean_nat_add(v_idx_3007_, v___x_3020_);
lean_dec(v_idx_3007_);
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 1, v___x_3021_);
v___x_3023_ = v___x_3018_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_array_3006_);
lean_ctor_set(v_reuseFailAlloc_3044_, 1, v___x_3021_);
v___x_3023_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3024_ = l_ByteArray_empty;
v___x_3025_ = lean_unsigned_to_nat(0u);
v___x_3026_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_3004_, v___x_3024_, v___x_3025_, v___x_3023_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_object* v_pos_3027_; lean_object* v_res_3028_; uint8_t v___x_3029_; 
v_pos_3027_ = lean_ctor_get(v___x_3026_, 0);
lean_inc(v_pos_3027_);
v_res_3028_ = lean_ctor_get(v___x_3026_, 1);
lean_inc(v_res_3028_);
lean_dec_ref_known(v___x_3026_, 2);
v___x_3029_ = lean_string_validate_utf8(v_res_3028_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; lean_object* v___x_3031_; 
lean_dec(v_res_3028_);
v___x_3030_ = lean_box(0);
v___x_3031_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_3030_, v_pos_3027_);
return v___x_3031_;
}
else
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3032_ = lean_string_from_utf8_unchecked(v_res_3028_);
v___x_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
v___x_3034_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_3033_, v_pos_3027_);
lean_dec_ref_known(v___x_3033_, 1);
return v___x_3034_;
}
}
else
{
lean_object* v_pos_3035_; lean_object* v_err_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
v_pos_3035_ = lean_ctor_get(v___x_3026_, 0);
v_err_3036_ = lean_ctor_get(v___x_3026_, 1);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_3026_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_err_3036_);
lean_inc(v_pos_3035_);
lean_dec(v___x_3026_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_pos_3035_);
lean_ctor_set(v_reuseFailAlloc_3042_, 1, v_err_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___boxed(lean_object* v_maxLength_3048_, lean_object* v_a_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxLength_3048_, v_a_3049_);
lean_dec(v_maxLength_3048_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(lean_object* v___f_3051_, lean_object* v_maxSpaceSequence_3052_, lean_object* v_x_3053_, lean_object* v___y_3054_){
_start:
{
lean_object* v_pos_3056_; lean_object* v_pos_3060_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v_snd_3065_; lean_object* v_snd_3066_; uint8_t v___x_3067_; 
v___x_3063_ = lean_unsigned_to_nat(0u);
v___x_3064_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3051_, v_maxSpaceSequence_3052_, v___x_3063_, v___y_3054_);
v_snd_3065_ = lean_ctor_get(v___x_3064_, 1);
lean_inc(v_snd_3065_);
lean_dec_ref(v___x_3064_);
v_snd_3066_ = lean_ctor_get(v_snd_3065_, 1);
v___x_3067_ = lean_unbox(v_snd_3066_);
if (v___x_3067_ == 0)
{
lean_object* v_fst_3068_; lean_object* v_array_3069_; lean_object* v_idx_3070_; lean_object* v___x_3071_; uint8_t v___x_3072_; 
v_fst_3068_ = lean_ctor_get(v_snd_3065_, 0);
lean_inc(v_fst_3068_);
lean_dec(v_snd_3065_);
v_array_3069_ = lean_ctor_get(v_fst_3068_, 0);
v_idx_3070_ = lean_ctor_get(v_fst_3068_, 1);
v___x_3071_ = lean_byte_array_size(v_array_3069_);
v___x_3072_ = lean_nat_dec_lt(v_idx_3070_, v___x_3071_);
if (v___x_3072_ == 0)
{
v_pos_3056_ = v_fst_3068_;
goto v___jp_3055_;
}
else
{
uint8_t v___x_3073_; uint32_t v___x_3074_; uint32_t v___x_3075_; uint8_t v___x_3076_; 
v___x_3073_ = lean_byte_array_fget(v_array_3069_, v_idx_3070_);
v___x_3074_ = lean_uint8_to_uint32(v___x_3073_);
v___x_3075_ = 32;
v___x_3076_ = lean_uint32_dec_eq(v___x_3074_, v___x_3075_);
if (v___x_3076_ == 0)
{
uint32_t v___x_3077_; uint8_t v___x_3078_; 
v___x_3077_ = 9;
v___x_3078_ = lean_uint32_dec_eq(v___x_3074_, v___x_3077_);
if (v___x_3078_ == 0)
{
v_pos_3056_ = v_fst_3068_;
goto v___jp_3055_;
}
else
{
v_pos_3060_ = v_fst_3068_;
goto v___jp_3059_;
}
}
else
{
v_pos_3060_ = v_fst_3068_;
goto v___jp_3059_;
}
}
}
else
{
lean_object* v_fst_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3087_; 
v_fst_3079_ = lean_ctor_get(v_snd_3065_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v_snd_3065_);
if (v_isSharedCheck_3087_ == 0)
{
lean_object* v_unused_3088_; 
v_unused_3088_ = lean_ctor_get(v_snd_3065_, 1);
lean_dec(v_unused_3088_);
v___x_3081_ = v_snd_3065_;
v_isShared_3082_ = v_isSharedCheck_3087_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_fst_3079_);
lean_dec(v_snd_3065_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3087_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3083_; lean_object* v___x_3085_; 
v___x_3083_ = lean_box(0);
if (v_isShared_3082_ == 0)
{
lean_ctor_set_tag(v___x_3081_, 1);
lean_ctor_set(v___x_3081_, 1, v___x_3083_);
v___x_3085_ = v___x_3081_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_fst_3079_);
lean_ctor_set(v_reuseFailAlloc_3086_, 1, v___x_3083_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
v___jp_3055_:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = lean_box(0);
v___x_3058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3058_, 0, v_pos_3056_);
lean_ctor_set(v___x_3058_, 1, v___x_3057_);
return v___x_3058_;
}
v___jp_3059_:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3061_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_3062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3062_, 0, v_pos_3060_);
lean_ctor_set(v___x_3062_, 1, v___x_3061_);
return v___x_3062_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2___boxed(lean_object* v___f_3089_, lean_object* v_maxSpaceSequence_3090_, lean_object* v_x_3091_, lean_object* v___y_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_3089_, v_maxSpaceSequence_3090_, v_x_3091_, v___y_3092_);
lean_dec(v_maxSpaceSequence_3090_);
return v_res_3093_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2(void){
_start:
{
uint32_t v___x_3097_; uint8_t v___x_3098_; 
v___x_3097_ = 61;
v___x_3098_ = lean_uint32_to_uint8(v___x_3097_);
return v___x_3098_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3(void){
_start:
{
uint8_t v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2);
v___x_3100_ = lean_uint8_to_nat(v___x_3099_);
return v___x_3100_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4(void){
_start:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3101_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3);
v___x_3102_ = l_Nat_reprFast(v___x_3101_);
return v___x_3102_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5(void){
_start:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3103_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4);
v___x_3104_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_3105_ = lean_string_append(v___x_3104_, v___x_3103_);
return v___x_3105_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6(void){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3106_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__5));
v___x_3107_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5);
v___x_3108_ = lean_string_append(v___x_3107_, v___x_3106_);
return v___x_3108_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7(void){
_start:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3109_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6);
v___x_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3109_);
return v___x_3110_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__10(void){
_start:
{
uint32_t v___x_3114_; uint8_t v___x_3115_; 
v___x_3114_ = 59;
v___x_3115_ = lean_uint32_to_uint8(v___x_3114_);
return v___x_3115_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__11(void){
_start:
{
uint8_t v___x_3116_; lean_object* v___x_3117_; 
v___x_3116_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__10, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__10_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__10);
v___x_3117_ = lean_uint8_to_nat(v___x_3116_);
return v___x_3117_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__12(void){
_start:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3118_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__11, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__11_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__11);
v___x_3119_ = l_Nat_reprFast(v___x_3118_);
return v___x_3119_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__13(void){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3120_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__12, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__12_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__12);
v___x_3121_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_3122_ = lean_string_append(v___x_3121_, v___x_3120_);
return v___x_3122_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__14(void){
_start:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3123_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__5));
v___x_3124_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__13, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__13_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__13);
v___x_3125_ = lean_string_append(v___x_3124_, v___x_3123_);
return v___x_3125_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__15(void){
_start:
{
lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3126_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__14, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__14_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__14);
v___x_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3126_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(lean_object* v_limits_3128_, lean_object* v_a_3129_){
_start:
{
lean_object* v_pos_3131_; lean_object* v_pos_3135_; lean_object* v___y_3139_; lean_object* v_pos_3140_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3172_; lean_object* v_pos_3173_; lean_object* v_res_3174_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v_lower_3180_; lean_object* v_upper_3181_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v_pos_3197_; lean_object* v_pos_3201_; lean_object* v_maxSpaceSequence_3204_; lean_object* v_maxChunkExtNameLength_3205_; lean_object* v_maxChunkExtValueLength_3206_; lean_object* v___f_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v_snd_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3498_; 
v_maxSpaceSequence_3204_ = lean_ctor_get(v_limits_3128_, 8);
v_maxChunkExtNameLength_3205_ = lean_ctor_get(v_limits_3128_, 11);
v_maxChunkExtValueLength_3206_ = lean_ctor_get(v_limits_3128_, 12);
v___f_3207_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0));
v___x_3208_ = lean_unsigned_to_nat(0u);
v___x_3209_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3207_, v_maxSpaceSequence_3204_, v___x_3208_, v_a_3129_);
v_snd_3210_ = lean_ctor_get(v___x_3209_, 1);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3498_ == 0)
{
lean_object* v_unused_3499_; 
v_unused_3499_ = lean_ctor_get(v___x_3209_, 0);
lean_dec(v_unused_3499_);
v___x_3212_ = v___x_3209_;
v_isShared_3213_ = v_isSharedCheck_3498_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_snd_3210_);
lean_dec(v___x_3209_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3498_;
goto v_resetjp_3211_;
}
v___jp_3130_:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3132_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_3133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3133_, 0, v_pos_3131_);
lean_ctor_set(v___x_3133_, 1, v___x_3132_);
return v___x_3133_;
}
v___jp_3134_:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3136_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_3137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3137_, 0, v_pos_3135_);
lean_ctor_set(v___x_3137_, 1, v___x_3136_);
return v___x_3137_;
}
v___jp_3138_:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3141_ = lean_box(0);
v___x_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___y_3139_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3143_, 0, v_pos_3140_);
lean_ctor_set(v___x_3143_, 1, v___x_3142_);
return v___x_3143_;
}
v___jp_3144_:
{
if (lean_obj_tag(v___y_3146_) == 0)
{
lean_object* v_pos_3147_; lean_object* v_res_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3161_; 
v_pos_3147_ = lean_ctor_get(v___y_3146_, 0);
v_res_3148_ = lean_ctor_get(v___y_3146_, 1);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___y_3146_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3150_ = v___y_3146_;
v_isShared_3151_ = v_isSharedCheck_3161_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_res_3148_);
lean_inc(v_pos_3147_);
lean_dec(v___y_3146_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3161_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Std_Http_Chunk_ExtensionValue_ofString_x3f(v_res_3148_);
if (lean_obj_tag(v___x_3152_) == 1)
{
lean_object* v___x_3153_; lean_object* v___x_3155_; 
v___x_3153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3153_, 0, v___y_3145_);
lean_ctor_set(v___x_3153_, 1, v___x_3152_);
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 1, v___x_3153_);
v___x_3155_ = v___x_3150_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_pos_3147_);
lean_ctor_set(v_reuseFailAlloc_3156_, 1, v___x_3153_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
else
{
lean_object* v___x_3157_; lean_object* v___x_3159_; 
lean_dec(v___x_3152_);
lean_dec_ref(v___y_3145_);
v___x_3157_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1));
if (v_isShared_3151_ == 0)
{
lean_ctor_set_tag(v___x_3150_, 1);
lean_ctor_set(v___x_3150_, 1, v___x_3157_);
v___x_3159_ = v___x_3150_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_pos_3147_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v___x_3157_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
else
{
lean_object* v_pos_3162_; lean_object* v_err_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
lean_dec_ref(v___y_3145_);
v_pos_3162_ = lean_ctor_get(v___y_3146_, 0);
v_err_3163_ = lean_ctor_get(v___y_3146_, 1);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___y_3146_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___y_3146_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_err_3163_);
lean_inc(v_pos_3162_);
lean_dec(v___y_3146_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_pos_3162_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v_err_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
v___jp_3171_:
{
lean_object* v___x_3175_; 
v___x_3175_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_3174_, v_pos_3173_);
lean_dec(v_res_3174_);
v___y_3145_ = v___y_3172_;
v___y_3146_ = v___x_3175_;
goto v___jp_3144_;
}
v___jp_3176_:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; uint8_t v___x_3184_; 
v___x_3182_ = l_ByteArray_toByteSlice(v___y_3177_, v_lower_3180_, v_upper_3181_);
v___x_3183_ = l_ByteSlice_toByteArray(v___x_3182_);
v___x_3184_ = lean_string_validate_utf8(v___x_3183_);
if (v___x_3184_ == 0)
{
lean_object* v___x_3185_; 
lean_dec_ref(v___x_3183_);
v___x_3185_ = lean_box(0);
v___y_3172_ = v___y_3179_;
v_pos_3173_ = v___y_3178_;
v_res_3174_ = v___x_3185_;
goto v___jp_3171_;
}
else
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = lean_string_from_utf8_unchecked(v___x_3183_);
v___x_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
v___y_3172_ = v___y_3179_;
v_pos_3173_ = v___y_3178_;
v_res_3174_ = v___x_3187_;
goto v___jp_3171_;
}
}
v___jp_3188_:
{
uint8_t v___x_3195_; 
v___x_3195_ = lean_nat_dec_le(v___y_3191_, v___y_3193_);
if (v___x_3195_ == 0)
{
lean_dec(v___y_3191_);
v___y_3177_ = v___y_3189_;
v___y_3178_ = v___y_3190_;
v___y_3179_ = v___y_3192_;
v_lower_3180_ = v___y_3194_;
v_upper_3181_ = v___y_3193_;
goto v___jp_3176_;
}
else
{
lean_dec(v___y_3193_);
v___y_3177_ = v___y_3189_;
v___y_3178_ = v___y_3190_;
v___y_3179_ = v___y_3192_;
v_lower_3180_ = v___y_3194_;
v_upper_3181_ = v___y_3191_;
goto v___jp_3176_;
}
}
v___jp_3196_:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3198_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_3199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3199_, 0, v_pos_3197_);
lean_ctor_set(v___x_3199_, 1, v___x_3198_);
return v___x_3199_;
}
v___jp_3200_:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3202_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_3203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3203_, 0, v_pos_3201_);
lean_ctor_set(v___x_3203_, 1, v___x_3202_);
return v___x_3203_;
}
v_resetjp_3211_:
{
lean_object* v_snd_3214_; uint8_t v___x_3215_; 
v_snd_3214_ = lean_ctor_get(v_snd_3210_, 1);
v___x_3215_ = lean_unbox(v_snd_3214_);
if (v___x_3215_ == 0)
{
lean_object* v_fst_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3486_; 
v_fst_3216_ = lean_ctor_get(v_snd_3210_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v_snd_3210_);
if (v_isSharedCheck_3486_ == 0)
{
lean_object* v_unused_3487_; 
v_unused_3487_ = lean_ctor_get(v_snd_3210_, 1);
lean_dec(v_unused_3487_);
v___x_3218_ = v_snd_3210_;
v_isShared_3219_ = v_isSharedCheck_3486_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_fst_3216_);
lean_dec(v_snd_3210_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3486_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v_array_3220_; lean_object* v_idx_3221_; lean_object* v___f_3222_; lean_object* v___y_3224_; lean_object* v_pos_3225_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v_pos_3260_; lean_object* v_array_3261_; lean_object* v_idx_3262_; lean_object* v_pos_3318_; lean_object* v_res_3319_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v_lower_3385_; lean_object* v_upper_3386_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v_pos_3401_; lean_object* v_pos_3434_; lean_object* v___x_3478_; uint8_t v___x_3479_; 
v_array_3220_ = lean_ctor_get(v_fst_3216_, 0);
v_idx_3221_ = lean_ctor_get(v_fst_3216_, 1);
v___f_3222_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_3478_ = lean_byte_array_size(v_array_3220_);
v___x_3479_ = lean_nat_dec_lt(v_idx_3221_, v___x_3478_);
if (v___x_3479_ == 0)
{
lean_inc(v_idx_3221_);
lean_inc_ref(v_array_3220_);
v_pos_3434_ = v_fst_3216_;
goto v___jp_3433_;
}
else
{
uint8_t v___x_3480_; uint32_t v___x_3481_; uint32_t v___x_3482_; uint8_t v___x_3483_; 
v___x_3480_ = lean_byte_array_fget(v_array_3220_, v_idx_3221_);
v___x_3481_ = lean_uint8_to_uint32(v___x_3480_);
v___x_3482_ = 32;
v___x_3483_ = lean_uint32_dec_eq(v___x_3481_, v___x_3482_);
if (v___x_3483_ == 0)
{
uint32_t v___x_3484_; uint8_t v___x_3485_; 
v___x_3484_ = 9;
v___x_3485_ = lean_uint32_dec_eq(v___x_3481_, v___x_3484_);
if (v___x_3485_ == 0)
{
lean_inc(v_idx_3221_);
lean_inc_ref(v_array_3220_);
v_pos_3434_ = v_fst_3216_;
goto v___jp_3433_;
}
else
{
lean_del_object(v___x_3218_);
lean_del_object(v___x_3212_);
v_pos_3131_ = v_fst_3216_;
goto v___jp_3130_;
}
}
else
{
lean_del_object(v___x_3218_);
lean_del_object(v___x_3212_);
v_pos_3131_ = v_fst_3216_;
goto v___jp_3130_;
}
}
v___jp_3223_:
{
lean_object* v___x_3226_; 
lean_inc_ref(v_pos_3225_);
v___x_3226_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxChunkExtValueLength_3206_, v_pos_3225_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_dec_ref(v_pos_3225_);
v___y_3145_ = v___y_3224_;
v___y_3146_ = v___x_3226_;
goto v___jp_3144_;
}
else
{
lean_object* v_pos_3227_; lean_object* v_idx_3228_; lean_object* v_array_3229_; lean_object* v_idx_3230_; uint8_t v___x_3231_; 
v_pos_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_pos_3227_);
v_idx_3228_ = lean_ctor_get(v_pos_3225_, 1);
lean_inc(v_idx_3228_);
lean_dec_ref(v_pos_3225_);
v_array_3229_ = lean_ctor_get(v_pos_3227_, 0);
v_idx_3230_ = lean_ctor_get(v_pos_3227_, 1);
v___x_3231_ = lean_nat_dec_eq(v_idx_3228_, v_idx_3230_);
lean_dec(v_idx_3228_);
if (v___x_3231_ == 0)
{
lean_dec(v_pos_3227_);
v___y_3145_ = v___y_3224_;
v___y_3146_ = v___x_3226_;
goto v___jp_3144_;
}
else
{
lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3254_; 
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3254_ == 0)
{
lean_object* v_unused_3255_; lean_object* v_unused_3256_; 
v_unused_3255_ = lean_ctor_get(v___x_3226_, 1);
lean_dec(v_unused_3255_);
v_unused_3256_ = lean_ctor_get(v___x_3226_, 0);
lean_dec(v_unused_3256_);
v___x_3233_ = v___x_3226_;
v_isShared_3234_ = v_isSharedCheck_3254_;
goto v_resetjp_3232_;
}
else
{
lean_dec(v___x_3226_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3254_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3235_; lean_object* v_snd_3236_; lean_object* v_snd_3237_; uint8_t v___x_3238_; 
lean_inc(v_pos_3227_);
v___x_3235_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3222_, v_maxChunkExtValueLength_3206_, v___x_3208_, v_pos_3227_);
v_snd_3236_ = lean_ctor_get(v___x_3235_, 1);
lean_inc(v_snd_3236_);
v_snd_3237_ = lean_ctor_get(v_snd_3236_, 1);
v___x_3238_ = lean_unbox(v_snd_3237_);
if (v___x_3238_ == 0)
{
lean_object* v_fst_3239_; lean_object* v_fst_3240_; uint8_t v___x_3241_; 
v_fst_3239_ = lean_ctor_get(v___x_3235_, 0);
lean_inc(v_fst_3239_);
lean_dec_ref(v___x_3235_);
v_fst_3240_ = lean_ctor_get(v_snd_3236_, 0);
lean_inc(v_fst_3240_);
lean_dec(v_snd_3236_);
v___x_3241_ = lean_nat_dec_eq(v_fst_3239_, v___x_3208_);
if (v___x_3241_ == 0)
{
lean_object* v___x_3242_; lean_object* v___x_3243_; uint8_t v___x_3244_; 
lean_inc(v_idx_3230_);
lean_inc_ref(v_array_3229_);
lean_del_object(v___x_3233_);
lean_dec(v_pos_3227_);
v___x_3242_ = lean_nat_add(v_idx_3230_, v_fst_3239_);
lean_dec(v_fst_3239_);
v___x_3243_ = lean_byte_array_size(v_array_3229_);
v___x_3244_ = lean_nat_dec_le(v_idx_3230_, v___x_3208_);
if (v___x_3244_ == 0)
{
v___y_3189_ = v_array_3229_;
v___y_3190_ = v_fst_3240_;
v___y_3191_ = v___x_3242_;
v___y_3192_ = v___y_3224_;
v___y_3193_ = v___x_3243_;
v___y_3194_ = v_idx_3230_;
goto v___jp_3188_;
}
else
{
lean_dec(v_idx_3230_);
v___y_3189_ = v_array_3229_;
v___y_3190_ = v_fst_3240_;
v___y_3191_ = v___x_3242_;
v___y_3192_ = v___y_3224_;
v___y_3193_ = v___x_3243_;
v___y_3194_ = v___x_3208_;
goto v___jp_3188_;
}
}
else
{
lean_object* v___x_3245_; lean_object* v___x_3247_; 
lean_dec(v_fst_3240_);
lean_dec(v_fst_3239_);
lean_dec_ref(v___y_3224_);
v___x_3245_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 1, v___x_3245_);
v___x_3247_ = v___x_3233_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_pos_3227_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v___x_3245_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
else
{
lean_object* v_fst_3249_; lean_object* v___x_3250_; lean_object* v___x_3252_; 
lean_dec_ref(v___x_3235_);
lean_dec(v_pos_3227_);
lean_dec_ref(v___y_3224_);
v_fst_3249_ = lean_ctor_get(v_snd_3236_, 0);
lean_inc(v_fst_3249_);
lean_dec(v_snd_3236_);
v___x_3250_ = lean_box(0);
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 1, v___x_3250_);
lean_ctor_set(v___x_3233_, 0, v_fst_3249_);
v___x_3252_ = v___x_3233_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_fst_3249_);
lean_ctor_set(v_reuseFailAlloc_3253_, 1, v___x_3250_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
}
}
v___jp_3257_:
{
lean_object* v___x_3263_; uint8_t v___x_3264_; 
v___x_3263_ = lean_byte_array_size(v_array_3261_);
v___x_3264_ = lean_nat_dec_lt(v_idx_3262_, v___x_3263_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3265_; lean_object* v___x_3267_; 
lean_dec(v_idx_3262_);
lean_dec_ref(v_array_3261_);
lean_dec_ref(v___y_3259_);
v___x_3265_ = lean_box(0);
if (v_isShared_3219_ == 0)
{
lean_ctor_set_tag(v___x_3218_, 1);
lean_ctor_set(v___x_3218_, 1, v___x_3265_);
lean_ctor_set(v___x_3218_, 0, v_pos_3260_);
v___x_3267_ = v___x_3218_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_pos_3260_);
lean_ctor_set(v_reuseFailAlloc_3268_, 1, v___x_3265_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
else
{
uint8_t v___x_3269_; uint8_t v_got_3270_; uint8_t v___x_3271_; 
v___x_3269_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2);
v_got_3270_ = lean_byte_array_fget(v_array_3261_, v_idx_3262_);
v___x_3271_ = lean_uint8_dec_eq(v_got_3270_, v___x_3269_);
if (v___x_3271_ == 0)
{
lean_object* v___x_3272_; lean_object* v___x_3274_; 
lean_dec(v_idx_3262_);
lean_dec_ref(v_array_3261_);
lean_dec_ref(v___y_3259_);
v___x_3272_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7);
if (v_isShared_3219_ == 0)
{
lean_ctor_set_tag(v___x_3218_, 1);
lean_ctor_set(v___x_3218_, 1, v___x_3272_);
lean_ctor_set(v___x_3218_, 0, v_pos_3260_);
v___x_3274_ = v___x_3218_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_pos_3260_);
lean_ctor_set(v_reuseFailAlloc_3275_, 1, v___x_3272_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
else
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3279_; 
lean_dec_ref(v_pos_3260_);
v___x_3276_ = lean_unsigned_to_nat(1u);
v___x_3277_ = lean_nat_add(v_idx_3262_, v___x_3276_);
lean_dec(v_idx_3262_);
if (v_isShared_3219_ == 0)
{
lean_ctor_set(v___x_3218_, 1, v___x_3277_);
lean_ctor_set(v___x_3218_, 0, v_array_3261_);
v___x_3279_ = v___x_3218_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_array_3261_);
lean_ctor_set(v_reuseFailAlloc_3316_, 1, v___x_3277_);
v___x_3279_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
lean_object* v___x_3280_; 
v___x_3280_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_3207_, v_maxSpaceSequence_3204_, v___y_3258_, v___x_3279_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_pos_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3305_; 
v_pos_3281_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3305_ == 0)
{
lean_object* v_unused_3306_; 
v_unused_3306_ = lean_ctor_get(v___x_3280_, 1);
lean_dec(v_unused_3306_);
v___x_3283_ = v___x_3280_;
v_isShared_3284_ = v_isSharedCheck_3305_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_pos_3281_);
lean_dec(v___x_3280_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3305_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3285_; lean_object* v_snd_3286_; lean_object* v_snd_3287_; uint8_t v___x_3288_; 
v___x_3285_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3207_, v_maxSpaceSequence_3204_, v___x_3208_, v_pos_3281_);
v_snd_3286_ = lean_ctor_get(v___x_3285_, 1);
lean_inc(v_snd_3286_);
lean_dec_ref(v___x_3285_);
v_snd_3287_ = lean_ctor_get(v_snd_3286_, 1);
v___x_3288_ = lean_unbox(v_snd_3287_);
if (v___x_3288_ == 0)
{
lean_object* v_fst_3289_; lean_object* v_array_3290_; lean_object* v_idx_3291_; lean_object* v___x_3292_; uint8_t v___x_3293_; 
lean_del_object(v___x_3283_);
v_fst_3289_ = lean_ctor_get(v_snd_3286_, 0);
lean_inc(v_fst_3289_);
lean_dec(v_snd_3286_);
v_array_3290_ = lean_ctor_get(v_fst_3289_, 0);
v_idx_3291_ = lean_ctor_get(v_fst_3289_, 1);
v___x_3292_ = lean_byte_array_size(v_array_3290_);
v___x_3293_ = lean_nat_dec_lt(v_idx_3291_, v___x_3292_);
if (v___x_3293_ == 0)
{
v___y_3224_ = v___y_3259_;
v_pos_3225_ = v_fst_3289_;
goto v___jp_3223_;
}
else
{
uint8_t v___x_3294_; uint32_t v___x_3295_; uint32_t v___x_3296_; uint8_t v___x_3297_; 
v___x_3294_ = lean_byte_array_fget(v_array_3290_, v_idx_3291_);
v___x_3295_ = lean_uint8_to_uint32(v___x_3294_);
v___x_3296_ = 32;
v___x_3297_ = lean_uint32_dec_eq(v___x_3295_, v___x_3296_);
if (v___x_3297_ == 0)
{
uint32_t v___x_3298_; uint8_t v___x_3299_; 
v___x_3298_ = 9;
v___x_3299_ = lean_uint32_dec_eq(v___x_3295_, v___x_3298_);
if (v___x_3299_ == 0)
{
v___y_3224_ = v___y_3259_;
v_pos_3225_ = v_fst_3289_;
goto v___jp_3223_;
}
else
{
lean_dec_ref(v___y_3259_);
v_pos_3197_ = v_fst_3289_;
goto v___jp_3196_;
}
}
else
{
lean_dec_ref(v___y_3259_);
v_pos_3197_ = v_fst_3289_;
goto v___jp_3196_;
}
}
}
else
{
lean_object* v_fst_3300_; lean_object* v___x_3301_; lean_object* v___x_3303_; 
lean_dec_ref(v___y_3259_);
v_fst_3300_ = lean_ctor_get(v_snd_3286_, 0);
lean_inc(v_fst_3300_);
lean_dec(v_snd_3286_);
v___x_3301_ = lean_box(0);
if (v_isShared_3284_ == 0)
{
lean_ctor_set_tag(v___x_3283_, 1);
lean_ctor_set(v___x_3283_, 1, v___x_3301_);
lean_ctor_set(v___x_3283_, 0, v_fst_3300_);
v___x_3303_ = v___x_3283_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_fst_3300_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v___x_3301_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
}
}
else
{
lean_object* v_pos_3307_; lean_object* v_err_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3315_; 
lean_dec_ref(v___y_3259_);
v_pos_3307_ = lean_ctor_get(v___x_3280_, 0);
v_err_3308_ = lean_ctor_get(v___x_3280_, 1);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3310_ = v___x_3280_;
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_err_3308_);
lean_inc(v_pos_3307_);
lean_dec(v___x_3280_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_pos_3307_);
lean_ctor_set(v_reuseFailAlloc_3314_, 1, v_err_3308_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
}
}
}
v___jp_3317_:
{
lean_object* v___x_3320_; 
v___x_3320_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_3319_, v_pos_3318_);
lean_dec(v_res_3319_);
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_object* v_pos_3321_; lean_object* v_res_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v_pos_3321_ = lean_ctor_get(v___x_3320_, 0);
lean_inc(v_pos_3321_);
v_res_3322_ = lean_ctor_get(v___x_3320_, 1);
lean_inc(v_res_3322_);
lean_dec_ref_known(v___x_3320_, 2);
v___x_3323_ = lean_box(0);
v___x_3324_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_3207_, v_maxSpaceSequence_3204_, v___x_3323_, v_pos_3321_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_pos_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3362_; 
v_pos_3325_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3362_ == 0)
{
lean_object* v_unused_3363_; 
v_unused_3363_ = lean_ctor_get(v___x_3324_, 1);
lean_dec(v_unused_3363_);
v___x_3327_ = v___x_3324_;
v_isShared_3328_ = v_isSharedCheck_3362_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_pos_3325_);
lean_dec(v___x_3324_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3362_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3329_; 
v___x_3329_ = l_Std_Http_Chunk_ExtensionName_ofString_x3f(v_res_3322_);
if (lean_obj_tag(v___x_3329_) == 1)
{
lean_object* v_val_3330_; lean_object* v_array_3331_; lean_object* v_idx_3332_; lean_object* v___x_3333_; uint8_t v___x_3334_; 
v_val_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_val_3330_);
lean_dec_ref_known(v___x_3329_, 1);
v_array_3331_ = lean_ctor_get(v_pos_3325_, 0);
v_idx_3332_ = lean_ctor_get(v_pos_3325_, 1);
v___x_3333_ = lean_byte_array_size(v_array_3331_);
v___x_3334_ = lean_nat_dec_lt(v_idx_3332_, v___x_3333_);
if (v___x_3334_ == 0)
{
lean_del_object(v___x_3327_);
lean_del_object(v___x_3218_);
v___y_3139_ = v_val_3330_;
v_pos_3140_ = v_pos_3325_;
goto v___jp_3138_;
}
else
{
uint8_t v___x_3335_; uint8_t v___x_3336_; uint8_t v___x_3337_; 
v___x_3335_ = lean_byte_array_fget(v_array_3331_, v_idx_3332_);
v___x_3336_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2);
v___x_3337_ = lean_uint8_dec_eq(v___x_3335_, v___x_3336_);
if (v___x_3337_ == 0)
{
lean_del_object(v___x_3327_);
lean_del_object(v___x_3218_);
v___y_3139_ = v_val_3330_;
v_pos_3140_ = v_pos_3325_;
goto v___jp_3138_;
}
else
{
lean_object* v___x_3338_; lean_object* v_snd_3339_; lean_object* v_snd_3340_; uint8_t v___x_3341_; 
v___x_3338_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3207_, v_maxSpaceSequence_3204_, v___x_3208_, v_pos_3325_);
v_snd_3339_ = lean_ctor_get(v___x_3338_, 1);
lean_inc(v_snd_3339_);
lean_dec_ref(v___x_3338_);
v_snd_3340_ = lean_ctor_get(v_snd_3339_, 1);
v___x_3341_ = lean_unbox(v_snd_3340_);
if (v___x_3341_ == 0)
{
lean_object* v_fst_3342_; lean_object* v_array_3343_; lean_object* v_idx_3344_; lean_object* v___x_3345_; uint8_t v___x_3346_; 
lean_del_object(v___x_3327_);
v_fst_3342_ = lean_ctor_get(v_snd_3339_, 0);
lean_inc(v_fst_3342_);
lean_dec(v_snd_3339_);
v_array_3343_ = lean_ctor_get(v_fst_3342_, 0);
v_idx_3344_ = lean_ctor_get(v_fst_3342_, 1);
v___x_3345_ = lean_byte_array_size(v_array_3343_);
v___x_3346_ = lean_nat_dec_lt(v_idx_3344_, v___x_3345_);
if (v___x_3346_ == 0)
{
lean_inc(v_idx_3344_);
lean_inc_ref(v_array_3343_);
v___y_3258_ = v___x_3323_;
v___y_3259_ = v_val_3330_;
v_pos_3260_ = v_fst_3342_;
v_array_3261_ = v_array_3343_;
v_idx_3262_ = v_idx_3344_;
goto v___jp_3257_;
}
else
{
uint8_t v___x_3347_; uint32_t v___x_3348_; uint32_t v___x_3349_; uint8_t v___x_3350_; 
v___x_3347_ = lean_byte_array_fget(v_array_3343_, v_idx_3344_);
v___x_3348_ = lean_uint8_to_uint32(v___x_3347_);
v___x_3349_ = 32;
v___x_3350_ = lean_uint32_dec_eq(v___x_3348_, v___x_3349_);
if (v___x_3350_ == 0)
{
uint32_t v___x_3351_; uint8_t v___x_3352_; 
v___x_3351_ = 9;
v___x_3352_ = lean_uint32_dec_eq(v___x_3348_, v___x_3351_);
if (v___x_3352_ == 0)
{
lean_inc(v_idx_3344_);
lean_inc_ref(v_array_3343_);
v___y_3258_ = v___x_3323_;
v___y_3259_ = v_val_3330_;
v_pos_3260_ = v_fst_3342_;
v_array_3261_ = v_array_3343_;
v_idx_3262_ = v_idx_3344_;
goto v___jp_3257_;
}
else
{
lean_dec(v_val_3330_);
lean_del_object(v___x_3218_);
v_pos_3201_ = v_fst_3342_;
goto v___jp_3200_;
}
}
else
{
lean_dec(v_val_3330_);
lean_del_object(v___x_3218_);
v_pos_3201_ = v_fst_3342_;
goto v___jp_3200_;
}
}
}
else
{
lean_object* v_fst_3353_; lean_object* v___x_3354_; lean_object* v___x_3356_; 
lean_dec(v_val_3330_);
lean_del_object(v___x_3218_);
v_fst_3353_ = lean_ctor_get(v_snd_3339_, 0);
lean_inc(v_fst_3353_);
lean_dec(v_snd_3339_);
v___x_3354_ = lean_box(0);
if (v_isShared_3328_ == 0)
{
lean_ctor_set_tag(v___x_3327_, 1);
lean_ctor_set(v___x_3327_, 1, v___x_3354_);
lean_ctor_set(v___x_3327_, 0, v_fst_3353_);
v___x_3356_ = v___x_3327_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_fst_3353_);
lean_ctor_set(v_reuseFailAlloc_3357_, 1, v___x_3354_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
}
else
{
lean_object* v___x_3358_; lean_object* v___x_3360_; 
lean_dec(v___x_3329_);
lean_del_object(v___x_3218_);
v___x_3358_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__9));
if (v_isShared_3328_ == 0)
{
lean_ctor_set_tag(v___x_3327_, 1);
lean_ctor_set(v___x_3327_, 1, v___x_3358_);
v___x_3360_ = v___x_3327_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_pos_3325_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v___x_3358_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
else
{
lean_object* v_pos_3364_; lean_object* v_err_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
lean_dec(v_res_3322_);
lean_del_object(v___x_3218_);
v_pos_3364_ = lean_ctor_get(v___x_3324_, 0);
v_err_3365_ = lean_ctor_get(v___x_3324_, 1);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3367_ = v___x_3324_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_err_3365_);
lean_inc(v_pos_3364_);
lean_dec(v___x_3324_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_pos_3364_);
lean_ctor_set(v_reuseFailAlloc_3371_, 1, v_err_3365_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
else
{
lean_object* v_pos_3373_; lean_object* v_err_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
lean_del_object(v___x_3218_);
v_pos_3373_ = lean_ctor_get(v___x_3320_, 0);
v_err_3374_ = lean_ctor_get(v___x_3320_, 1);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3320_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_err_3374_);
lean_inc(v_pos_3373_);
lean_dec(v___x_3320_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3379_; 
if (v_isShared_3377_ == 0)
{
v___x_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_pos_3373_);
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
v___jp_3382_:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; uint8_t v___x_3389_; 
v___x_3387_ = l_ByteArray_toByteSlice(v___y_3384_, v_lower_3385_, v_upper_3386_);
v___x_3388_ = l_ByteSlice_toByteArray(v___x_3387_);
v___x_3389_ = lean_string_validate_utf8(v___x_3388_);
if (v___x_3389_ == 0)
{
lean_object* v___x_3390_; 
lean_dec_ref(v___x_3388_);
v___x_3390_ = lean_box(0);
v_pos_3318_ = v___y_3383_;
v_res_3319_ = v___x_3390_;
goto v___jp_3317_;
}
else
{
lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3391_ = lean_string_from_utf8_unchecked(v___x_3388_);
v___x_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3391_);
v_pos_3318_ = v___y_3383_;
v_res_3319_ = v___x_3392_;
goto v___jp_3317_;
}
}
v___jp_3393_:
{
uint8_t v___x_3399_; 
v___x_3399_ = lean_nat_dec_le(v___y_3395_, v___y_3396_);
if (v___x_3399_ == 0)
{
lean_dec(v___y_3395_);
v___y_3383_ = v___y_3394_;
v___y_3384_ = v___y_3397_;
v_lower_3385_ = v___y_3398_;
v_upper_3386_ = v___y_3396_;
goto v___jp_3382_;
}
else
{
lean_dec(v___y_3396_);
v___y_3383_ = v___y_3394_;
v___y_3384_ = v___y_3397_;
v_lower_3385_ = v___y_3398_;
v_upper_3386_ = v___y_3395_;
goto v___jp_3382_;
}
}
v___jp_3400_:
{
lean_object* v___x_3402_; lean_object* v_snd_3403_; lean_object* v_snd_3404_; uint8_t v___x_3405_; 
lean_inc_ref(v_pos_3401_);
v___x_3402_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3222_, v_maxChunkExtNameLength_3205_, v___x_3208_, v_pos_3401_);
v_snd_3403_ = lean_ctor_get(v___x_3402_, 1);
lean_inc(v_snd_3403_);
v_snd_3404_ = lean_ctor_get(v_snd_3403_, 1);
v___x_3405_ = lean_unbox(v_snd_3404_);
if (v___x_3405_ == 0)
{
lean_object* v_fst_3406_; lean_object* v_fst_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3421_; 
v_fst_3406_ = lean_ctor_get(v___x_3402_, 0);
lean_inc(v_fst_3406_);
lean_dec_ref(v___x_3402_);
v_fst_3407_ = lean_ctor_get(v_snd_3403_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v_snd_3403_);
if (v_isSharedCheck_3421_ == 0)
{
lean_object* v_unused_3422_; 
v_unused_3422_ = lean_ctor_get(v_snd_3403_, 1);
lean_dec(v_unused_3422_);
v___x_3409_ = v_snd_3403_;
v_isShared_3410_ = v_isSharedCheck_3421_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_fst_3407_);
lean_dec(v_snd_3403_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3421_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
uint8_t v___x_3411_; 
v___x_3411_ = lean_nat_dec_eq(v_fst_3406_, v___x_3208_);
if (v___x_3411_ == 0)
{
lean_object* v_array_3412_; lean_object* v_idx_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; uint8_t v___x_3416_; 
lean_del_object(v___x_3409_);
v_array_3412_ = lean_ctor_get(v_pos_3401_, 0);
lean_inc_ref(v_array_3412_);
v_idx_3413_ = lean_ctor_get(v_pos_3401_, 1);
lean_inc(v_idx_3413_);
lean_dec_ref(v_pos_3401_);
v___x_3414_ = lean_nat_add(v_idx_3413_, v_fst_3406_);
lean_dec(v_fst_3406_);
v___x_3415_ = lean_byte_array_size(v_array_3412_);
v___x_3416_ = lean_nat_dec_le(v_idx_3413_, v___x_3208_);
if (v___x_3416_ == 0)
{
v___y_3394_ = v_fst_3407_;
v___y_3395_ = v___x_3414_;
v___y_3396_ = v___x_3415_;
v___y_3397_ = v_array_3412_;
v___y_3398_ = v_idx_3413_;
goto v___jp_3393_;
}
else
{
lean_dec(v_idx_3413_);
v___y_3394_ = v_fst_3407_;
v___y_3395_ = v___x_3414_;
v___y_3396_ = v___x_3415_;
v___y_3397_ = v_array_3412_;
v___y_3398_ = v___x_3208_;
goto v___jp_3393_;
}
}
else
{
lean_object* v___x_3417_; lean_object* v___x_3419_; 
lean_dec(v_fst_3407_);
lean_dec(v_fst_3406_);
lean_del_object(v___x_3218_);
v___x_3417_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_3410_ == 0)
{
lean_ctor_set_tag(v___x_3409_, 1);
lean_ctor_set(v___x_3409_, 1, v___x_3417_);
lean_ctor_set(v___x_3409_, 0, v_pos_3401_);
v___x_3419_ = v___x_3409_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_pos_3401_);
lean_ctor_set(v_reuseFailAlloc_3420_, 1, v___x_3417_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
else
{
lean_object* v_fst_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3431_; 
lean_dec_ref(v___x_3402_);
lean_dec_ref(v_pos_3401_);
lean_del_object(v___x_3218_);
v_fst_3423_ = lean_ctor_get(v_snd_3403_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v_snd_3403_);
if (v_isSharedCheck_3431_ == 0)
{
lean_object* v_unused_3432_; 
v_unused_3432_ = lean_ctor_get(v_snd_3403_, 1);
lean_dec(v_unused_3432_);
v___x_3425_ = v_snd_3403_;
v_isShared_3426_ = v_isSharedCheck_3431_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_fst_3423_);
lean_dec(v_snd_3403_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3431_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3427_; lean_object* v___x_3429_; 
v___x_3427_ = lean_box(0);
if (v_isShared_3426_ == 0)
{
lean_ctor_set_tag(v___x_3425_, 1);
lean_ctor_set(v___x_3425_, 1, v___x_3427_);
v___x_3429_ = v___x_3425_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_fst_3423_);
lean_ctor_set(v_reuseFailAlloc_3430_, 1, v___x_3427_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
v___jp_3433_:
{
lean_object* v___x_3435_; uint8_t v___x_3436_; 
v___x_3435_ = lean_byte_array_size(v_array_3220_);
v___x_3436_ = lean_nat_dec_lt(v_idx_3221_, v___x_3435_);
if (v___x_3436_ == 0)
{
lean_object* v___x_3437_; lean_object* v___x_3439_; 
lean_dec(v_idx_3221_);
lean_dec_ref(v_array_3220_);
lean_del_object(v___x_3218_);
v___x_3437_ = lean_box(0);
if (v_isShared_3213_ == 0)
{
lean_ctor_set_tag(v___x_3212_, 1);
lean_ctor_set(v___x_3212_, 1, v___x_3437_);
lean_ctor_set(v___x_3212_, 0, v_pos_3434_);
v___x_3439_ = v___x_3212_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_pos_3434_);
lean_ctor_set(v_reuseFailAlloc_3440_, 1, v___x_3437_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
else
{
uint8_t v___x_3441_; uint8_t v_got_3442_; uint8_t v___x_3443_; 
v___x_3441_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__10, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__10_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__10);
v_got_3442_ = lean_byte_array_fget(v_array_3220_, v_idx_3221_);
v___x_3443_ = lean_uint8_dec_eq(v_got_3442_, v___x_3441_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3444_; lean_object* v___x_3446_; 
lean_dec(v_idx_3221_);
lean_dec_ref(v_array_3220_);
lean_del_object(v___x_3218_);
v___x_3444_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__15, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__15_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__15);
if (v_isShared_3213_ == 0)
{
lean_ctor_set_tag(v___x_3212_, 1);
lean_ctor_set(v___x_3212_, 1, v___x_3444_);
lean_ctor_set(v___x_3212_, 0, v_pos_3434_);
v___x_3446_ = v___x_3212_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_pos_3434_);
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
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3451_; 
lean_dec_ref(v_pos_3434_);
v___x_3448_ = lean_unsigned_to_nat(1u);
v___x_3449_ = lean_nat_add(v_idx_3221_, v___x_3448_);
lean_dec(v_idx_3221_);
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 1, v___x_3449_);
lean_ctor_set(v___x_3212_, 0, v_array_3220_);
v___x_3451_ = v___x_3212_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_array_3220_);
lean_ctor_set(v_reuseFailAlloc_3477_, 1, v___x_3449_);
v___x_3451_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
lean_object* v___x_3452_; lean_object* v_snd_3453_; lean_object* v_snd_3454_; uint8_t v___x_3455_; 
v___x_3452_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3207_, v_maxSpaceSequence_3204_, v___x_3208_, v___x_3451_);
v_snd_3453_ = lean_ctor_get(v___x_3452_, 1);
lean_inc(v_snd_3453_);
lean_dec_ref(v___x_3452_);
v_snd_3454_ = lean_ctor_get(v_snd_3453_, 1);
v___x_3455_ = lean_unbox(v_snd_3454_);
if (v___x_3455_ == 0)
{
lean_object* v_fst_3456_; lean_object* v_array_3457_; lean_object* v_idx_3458_; lean_object* v___x_3459_; uint8_t v___x_3460_; 
v_fst_3456_ = lean_ctor_get(v_snd_3453_, 0);
lean_inc(v_fst_3456_);
lean_dec(v_snd_3453_);
v_array_3457_ = lean_ctor_get(v_fst_3456_, 0);
v_idx_3458_ = lean_ctor_get(v_fst_3456_, 1);
v___x_3459_ = lean_byte_array_size(v_array_3457_);
v___x_3460_ = lean_nat_dec_lt(v_idx_3458_, v___x_3459_);
if (v___x_3460_ == 0)
{
v_pos_3401_ = v_fst_3456_;
goto v___jp_3400_;
}
else
{
uint8_t v___x_3461_; uint32_t v___x_3462_; uint32_t v___x_3463_; uint8_t v___x_3464_; 
v___x_3461_ = lean_byte_array_fget(v_array_3457_, v_idx_3458_);
v___x_3462_ = lean_uint8_to_uint32(v___x_3461_);
v___x_3463_ = 32;
v___x_3464_ = lean_uint32_dec_eq(v___x_3462_, v___x_3463_);
if (v___x_3464_ == 0)
{
uint32_t v___x_3465_; uint8_t v___x_3466_; 
v___x_3465_ = 9;
v___x_3466_ = lean_uint32_dec_eq(v___x_3462_, v___x_3465_);
if (v___x_3466_ == 0)
{
v_pos_3401_ = v_fst_3456_;
goto v___jp_3400_;
}
else
{
lean_del_object(v___x_3218_);
v_pos_3135_ = v_fst_3456_;
goto v___jp_3134_;
}
}
else
{
lean_del_object(v___x_3218_);
v_pos_3135_ = v_fst_3456_;
goto v___jp_3134_;
}
}
}
else
{
lean_object* v_fst_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3475_; 
lean_del_object(v___x_3218_);
v_fst_3467_ = lean_ctor_get(v_snd_3453_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v_snd_3453_);
if (v_isSharedCheck_3475_ == 0)
{
lean_object* v_unused_3476_; 
v_unused_3476_ = lean_ctor_get(v_snd_3453_, 1);
lean_dec(v_unused_3476_);
v___x_3469_ = v_snd_3453_;
v_isShared_3470_ = v_isSharedCheck_3475_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_fst_3467_);
lean_dec(v_snd_3453_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3475_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3471_ = lean_box(0);
if (v_isShared_3470_ == 0)
{
lean_ctor_set_tag(v___x_3469_, 1);
lean_ctor_set(v___x_3469_, 1, v___x_3471_);
v___x_3473_ = v___x_3469_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_fst_3467_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v___x_3471_);
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
}
}
}
}
else
{
lean_object* v_fst_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3496_; 
lean_del_object(v___x_3212_);
v_fst_3488_ = lean_ctor_get(v_snd_3210_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v_snd_3210_);
if (v_isSharedCheck_3496_ == 0)
{
lean_object* v_unused_3497_; 
v_unused_3497_ = lean_ctor_get(v_snd_3210_, 1);
lean_dec(v_unused_3497_);
v___x_3490_ = v_snd_3210_;
v_isShared_3491_ = v_isSharedCheck_3496_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_fst_3488_);
lean_dec(v_snd_3210_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3496_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3492_; lean_object* v___x_3494_; 
v___x_3492_ = lean_box(0);
if (v_isShared_3491_ == 0)
{
lean_ctor_set_tag(v___x_3490_, 1);
lean_ctor_set(v___x_3490_, 1, v___x_3492_);
v___x_3494_ = v___x_3490_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_fst_3488_);
lean_ctor_set(v_reuseFailAlloc_3495_, 1, v___x_3492_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___boxed(lean_object* v_limits_3500_, lean_object* v_a_3501_){
_start:
{
lean_object* v_res_3502_; 
v_res_3502_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_3500_, v_a_3501_);
lean_dec_ref(v_limits_3500_);
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0(lean_object* v_limits_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v_pos_3506_; lean_object* v_err_3507_; lean_object* v___x_3523_; 
lean_inc_ref(v___y_3504_);
v___x_3523_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_3503_, v___y_3504_);
if (lean_obj_tag(v___x_3523_) == 0)
{
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_pos_3524_; lean_object* v_res_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3533_; 
lean_dec_ref(v___y_3504_);
v_pos_3524_ = lean_ctor_get(v___x_3523_, 0);
v_res_3525_ = lean_ctor_get(v___x_3523_, 1);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3527_ = v___x_3523_;
v_isShared_3528_ = v_isSharedCheck_3533_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_res_3525_);
lean_inc(v_pos_3524_);
lean_dec(v___x_3523_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3533_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3529_; lean_object* v___x_3531_; 
v___x_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3529_, 0, v_res_3525_);
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 1, v___x_3529_);
v___x_3531_ = v___x_3527_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_pos_3524_);
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
else
{
lean_object* v_pos_3534_; lean_object* v_err_3535_; 
v_pos_3534_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_pos_3534_);
v_err_3535_ = lean_ctor_get(v___x_3523_, 1);
lean_inc(v_err_3535_);
lean_dec_ref_known(v___x_3523_, 2);
v_pos_3506_ = v_pos_3534_;
v_err_3507_ = v_err_3535_;
goto v___jp_3505_;
}
}
else
{
lean_object* v_err_3536_; 
v_err_3536_ = lean_ctor_get(v___x_3523_, 1);
lean_inc(v_err_3536_);
lean_dec_ref_known(v___x_3523_, 2);
lean_inc_ref(v___y_3504_);
v_pos_3506_ = v___y_3504_;
v_err_3507_ = v_err_3536_;
goto v___jp_3505_;
}
v___jp_3505_:
{
lean_object* v_idx_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3521_; 
v_idx_3508_ = lean_ctor_get(v___y_3504_, 1);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___y_3504_);
if (v_isSharedCheck_3521_ == 0)
{
lean_object* v_unused_3522_; 
v_unused_3522_ = lean_ctor_get(v___y_3504_, 0);
lean_dec(v_unused_3522_);
v___x_3510_ = v___y_3504_;
v_isShared_3511_ = v_isSharedCheck_3521_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_idx_3508_);
lean_dec(v___y_3504_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3521_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v_idx_3512_; uint8_t v___x_3513_; 
v_idx_3512_ = lean_ctor_get(v_pos_3506_, 1);
v___x_3513_ = lean_nat_dec_eq(v_idx_3508_, v_idx_3512_);
lean_dec(v_idx_3508_);
if (v___x_3513_ == 0)
{
lean_object* v___x_3515_; 
if (v_isShared_3511_ == 0)
{
lean_ctor_set_tag(v___x_3510_, 1);
lean_ctor_set(v___x_3510_, 1, v_err_3507_);
lean_ctor_set(v___x_3510_, 0, v_pos_3506_);
v___x_3515_ = v___x_3510_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_pos_3506_);
lean_ctor_set(v_reuseFailAlloc_3516_, 1, v_err_3507_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
else
{
lean_object* v___x_3517_; lean_object* v___x_3519_; 
lean_dec(v_err_3507_);
v___x_3517_ = lean_box(0);
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 1, v___x_3517_);
lean_ctor_set(v___x_3510_, 0, v_pos_3506_);
v___x_3519_ = v___x_3510_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_pos_3506_);
lean_ctor_set(v_reuseFailAlloc_3520_, 1, v___x_3517_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed(lean_object* v_limits_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l_Std_Http_Protocol_H1_parseChunkSize___lam__0(v_limits_3537_, v___y_3538_);
lean_dec_ref(v_limits_3537_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize(lean_object* v_limits_3540_, lean_object* v_a_3541_){
_start:
{
lean_object* v___x_3542_; 
v___x_3542_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(v_a_3541_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v_pos_3543_; lean_object* v_res_3544_; lean_object* v_maxChunkExtensions_3545_; lean_object* v___f_3546_; lean_object* v___x_3547_; 
v_pos_3543_ = lean_ctor_get(v___x_3542_, 0);
lean_inc(v_pos_3543_);
v_res_3544_ = lean_ctor_get(v___x_3542_, 1);
lean_inc(v_res_3544_);
lean_dec_ref_known(v___x_3542_, 2);
v_maxChunkExtensions_3545_ = lean_ctor_get(v_limits_3540_, 10);
lean_inc(v_maxChunkExtensions_3545_);
v___f_3546_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3546_, 0, v_limits_3540_);
v___x_3547_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___f_3546_, v_maxChunkExtensions_3545_, v_pos_3543_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_pos_3548_; lean_object* v_res_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v_pos_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_pos_3548_);
v_res_3549_ = lean_ctor_get(v___x_3547_, 1);
lean_inc(v_res_3549_);
lean_dec_ref_known(v___x_3547_, 2);
v___x_3550_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3551_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3550_, v_pos_3548_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_pos_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3560_; 
v_pos_3552_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3560_ == 0)
{
lean_object* v_unused_3561_; 
v_unused_3561_ = lean_ctor_get(v___x_3551_, 1);
lean_dec(v_unused_3561_);
v___x_3554_ = v___x_3551_;
v_isShared_3555_ = v_isSharedCheck_3560_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_pos_3552_);
lean_dec(v___x_3551_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3560_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3556_; lean_object* v___x_3558_; 
v___x_3556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3556_, 0, v_res_3544_);
lean_ctor_set(v___x_3556_, 1, v_res_3549_);
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 1, v___x_3556_);
v___x_3558_ = v___x_3554_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_pos_3552_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v___x_3556_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
else
{
lean_object* v_pos_3562_; lean_object* v_err_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
lean_dec(v_res_3549_);
lean_dec(v_res_3544_);
v_pos_3562_ = lean_ctor_get(v___x_3551_, 0);
v_err_3563_ = lean_ctor_get(v___x_3551_, 1);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___x_3551_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_err_3563_);
lean_inc(v_pos_3562_);
lean_dec(v___x_3551_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_pos_3562_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v_err_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
else
{
lean_object* v_pos_3571_; lean_object* v_err_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
lean_dec(v_res_3544_);
v_pos_3571_ = lean_ctor_get(v___x_3547_, 0);
v_err_3572_ = lean_ctor_get(v___x_3547_, 1);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3574_ = v___x_3547_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_err_3572_);
lean_inc(v_pos_3571_);
lean_dec(v___x_3547_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3577_; 
if (v_isShared_3575_ == 0)
{
v___x_3577_ = v___x_3574_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_pos_3571_);
lean_ctor_set(v_reuseFailAlloc_3578_, 1, v_err_3572_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
else
{
lean_object* v_pos_3580_; lean_object* v_err_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_dec_ref(v_limits_3540_);
v_pos_3580_ = lean_ctor_get(v___x_3542_, 0);
v_err_3581_ = lean_ctor_get(v___x_3542_, 1);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3542_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_err_3581_);
lean_inc(v_pos_3580_);
lean_dec(v___x_3542_);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx(lean_object* v_x_3589_){
_start:
{
if (lean_obj_tag(v_x_3589_) == 0)
{
lean_object* v___x_3590_; 
v___x_3590_ = lean_unsigned_to_nat(0u);
return v___x_3590_;
}
else
{
lean_object* v___x_3591_; 
v___x_3591_ = lean_unsigned_to_nat(1u);
return v___x_3591_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___boxed(lean_object* v_x_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l_Std_Http_Protocol_H1_TakeResult_ctorIdx(v_x_3592_);
lean_dec_ref(v_x_3592_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(lean_object* v_t_3594_, lean_object* v_k_3595_){
_start:
{
if (lean_obj_tag(v_t_3594_) == 0)
{
lean_object* v_data_3596_; lean_object* v___x_3597_; 
v_data_3596_ = lean_ctor_get(v_t_3594_, 0);
lean_inc_ref(v_data_3596_);
lean_dec_ref_known(v_t_3594_, 1);
v___x_3597_ = lean_apply_1(v_k_3595_, v_data_3596_);
return v___x_3597_;
}
else
{
lean_object* v_data_3598_; lean_object* v_remaining_3599_; lean_object* v___x_3600_; 
v_data_3598_ = lean_ctor_get(v_t_3594_, 0);
lean_inc_ref(v_data_3598_);
v_remaining_3599_ = lean_ctor_get(v_t_3594_, 1);
lean_inc(v_remaining_3599_);
lean_dec_ref_known(v_t_3594_, 2);
v___x_3600_ = lean_apply_2(v_k_3595_, v_data_3598_, v_remaining_3599_);
return v___x_3600_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim(lean_object* v_motive_3601_, lean_object* v_ctorIdx_3602_, lean_object* v_t_3603_, lean_object* v_h_3604_, lean_object* v_k_3605_){
_start:
{
lean_object* v___x_3606_; 
v___x_3606_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3603_, v_k_3605_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___boxed(lean_object* v_motive_3607_, lean_object* v_ctorIdx_3608_, lean_object* v_t_3609_, lean_object* v_h_3610_, lean_object* v_k_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim(v_motive_3607_, v_ctorIdx_3608_, v_t_3609_, v_h_3610_, v_k_3611_);
lean_dec(v_ctorIdx_3608_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim___redArg(lean_object* v_t_3613_, lean_object* v_complete_3614_){
_start:
{
lean_object* v___x_3615_; 
v___x_3615_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3613_, v_complete_3614_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim(lean_object* v_motive_3616_, lean_object* v_t_3617_, lean_object* v_h_3618_, lean_object* v_complete_3619_){
_start:
{
lean_object* v___x_3620_; 
v___x_3620_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3617_, v_complete_3619_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim___redArg(lean_object* v_t_3621_, lean_object* v_incomplete_3622_){
_start:
{
lean_object* v___x_3623_; 
v___x_3623_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3621_, v_incomplete_3622_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim(lean_object* v_motive_3624_, lean_object* v_t_3625_, lean_object* v_h_3626_, lean_object* v_incomplete_3627_){
_start:
{
lean_object* v___x_3628_; 
v___x_3628_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3625_, v_incomplete_3627_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkPartial(lean_object* v_limits_3629_, lean_object* v_a_3630_){
_start:
{
lean_object* v___x_3631_; 
v___x_3631_ = l_Std_Http_Protocol_H1_parseChunkSize(v_limits_3629_, v_a_3630_);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_object* v_res_3632_; lean_object* v_pos_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3673_; 
v_res_3632_ = lean_ctor_get(v___x_3631_, 1);
v_pos_3633_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3635_ = v___x_3631_;
v_isShared_3636_ = v_isSharedCheck_3673_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_res_3632_);
lean_inc(v_pos_3633_);
lean_dec(v___x_3631_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3673_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v_fst_3637_; lean_object* v_snd_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3672_; 
v_fst_3637_ = lean_ctor_get(v_res_3632_, 0);
v_snd_3638_ = lean_ctor_get(v_res_3632_, 1);
v_isSharedCheck_3672_ = !lean_is_exclusive(v_res_3632_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3640_ = v_res_3632_;
v_isShared_3641_ = v_isSharedCheck_3672_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_snd_3638_);
lean_inc(v_fst_3637_);
lean_dec(v_res_3632_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3672_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3642_; uint8_t v___x_3643_; 
v___x_3642_ = lean_unsigned_to_nat(0u);
v___x_3643_ = lean_nat_dec_eq(v_fst_3637_, v___x_3642_);
if (v___x_3643_ == 0)
{
lean_object* v___x_3644_; 
lean_del_object(v___x_3635_);
v___x_3644_ = l_Std_Internal_Parsec_ByteArray_take(v_fst_3637_, v_pos_3633_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_pos_3645_; lean_object* v_res_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3658_; 
v_pos_3645_ = lean_ctor_get(v___x_3644_, 0);
v_res_3646_ = lean_ctor_get(v___x_3644_, 1);
v_isSharedCheck_3658_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3648_ = v___x_3644_;
v_isShared_3649_ = v_isSharedCheck_3658_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_res_3646_);
lean_inc(v_pos_3645_);
lean_dec(v___x_3644_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3658_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3651_; 
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 1, v_res_3646_);
lean_ctor_set(v___x_3640_, 0, v_snd_3638_);
v___x_3651_ = v___x_3640_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_snd_3638_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v_res_3646_);
v___x_3651_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3655_; 
v___x_3652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3652_, 0, v_fst_3637_);
lean_ctor_set(v___x_3652_, 1, v___x_3651_);
v___x_3653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3652_);
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 1, v___x_3653_);
v___x_3655_ = v___x_3648_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_pos_3645_);
lean_ctor_set(v_reuseFailAlloc_3656_, 1, v___x_3653_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
}
else
{
lean_object* v_pos_3659_; lean_object* v_err_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
lean_del_object(v___x_3640_);
lean_dec(v_snd_3638_);
lean_dec(v_fst_3637_);
v_pos_3659_ = lean_ctor_get(v___x_3644_, 0);
v_err_3660_ = lean_ctor_get(v___x_3644_, 1);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3644_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_err_3660_);
lean_inc(v_pos_3659_);
lean_dec(v___x_3644_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3665_; 
if (v_isShared_3663_ == 0)
{
v___x_3665_ = v___x_3662_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_pos_3659_);
lean_ctor_set(v_reuseFailAlloc_3666_, 1, v_err_3660_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
else
{
lean_object* v___x_3668_; lean_object* v___x_3670_; 
lean_del_object(v___x_3640_);
lean_dec(v_snd_3638_);
lean_dec(v_fst_3637_);
v___x_3668_ = lean_box(0);
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 1, v___x_3668_);
v___x_3670_ = v___x_3635_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_pos_3633_);
lean_ctor_set(v_reuseFailAlloc_3671_, 1, v___x_3668_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
}
}
else
{
lean_object* v_pos_3674_; lean_object* v_err_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3682_; 
v_pos_3674_ = lean_ctor_get(v___x_3631_, 0);
v_err_3675_ = lean_ctor_get(v___x_3631_, 1);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3677_ = v___x_3631_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_err_3675_);
lean_inc(v_pos_3674_);
lean_dec(v___x_3631_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
if (v_isShared_3678_ == 0)
{
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_pos_3674_);
lean_ctor_set(v_reuseFailAlloc_3681_, 1, v_err_3675_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData(lean_object* v_size_3683_, lean_object* v_it_3684_){
_start:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; uint8_t v___x_3687_; 
v___x_3685_ = l_ByteArray_Iterator_remainingBytes(v_it_3684_);
v___x_3686_ = lean_unsigned_to_nat(0u);
v___x_3687_ = lean_nat_dec_eq(v___x_3685_, v___x_3686_);
if (v___x_3687_ == 0)
{
uint8_t v___x_3688_; 
v___x_3688_ = lean_nat_dec_lt(v___x_3685_, v_size_3683_);
if (v___x_3688_ == 0)
{
lean_object* v_array_3689_; lean_object* v_idx_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3709_; 
lean_dec(v___x_3685_);
v_array_3689_ = lean_ctor_get(v_it_3684_, 0);
v_idx_3690_ = lean_ctor_get(v_it_3684_, 1);
v_isSharedCheck_3709_ = !lean_is_exclusive(v_it_3684_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3692_ = v_it_3684_;
v_isShared_3693_ = v_isSharedCheck_3709_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_idx_3690_);
lean_inc(v_array_3689_);
lean_dec(v_it_3684_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3709_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3694_; lean_object* v___x_3696_; 
v___x_3694_ = lean_nat_add(v_idx_3690_, v_size_3683_);
lean_inc(v___x_3694_);
lean_inc_ref(v_array_3689_);
if (v_isShared_3693_ == 0)
{
lean_ctor_set(v___x_3692_, 1, v___x_3694_);
v___x_3696_ = v___x_3692_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_array_3689_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v___x_3694_);
v___x_3696_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
lean_object* v_lower_3698_; lean_object* v_upper_3699_; lean_object* v___x_3703_; lean_object* v___y_3705_; uint8_t v___x_3707_; 
v___x_3703_ = lean_byte_array_size(v_array_3689_);
v___x_3707_ = lean_nat_dec_le(v_idx_3690_, v___x_3686_);
if (v___x_3707_ == 0)
{
v___y_3705_ = v_idx_3690_;
goto v___jp_3704_;
}
else
{
lean_dec(v_idx_3690_);
v___y_3705_ = v___x_3686_;
goto v___jp_3704_;
}
v___jp_3697_:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3700_ = l_ByteArray_toByteSlice(v_array_3689_, v_lower_3698_, v_upper_3699_);
v___x_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3700_);
v___x_3702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3696_);
lean_ctor_set(v___x_3702_, 1, v___x_3701_);
return v___x_3702_;
}
v___jp_3704_:
{
uint8_t v___x_3706_; 
v___x_3706_ = lean_nat_dec_le(v___x_3694_, v___x_3703_);
if (v___x_3706_ == 0)
{
lean_dec(v___x_3694_);
v_lower_3698_ = v___y_3705_;
v_upper_3699_ = v___x_3703_;
goto v___jp_3697_;
}
else
{
v_lower_3698_ = v___y_3705_;
v_upper_3699_ = v___x_3694_;
goto v___jp_3697_;
}
}
}
}
}
else
{
lean_object* v_array_3710_; lean_object* v_idx_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3731_; 
v_array_3710_ = lean_ctor_get(v_it_3684_, 0);
v_idx_3711_ = lean_ctor_get(v_it_3684_, 1);
v_isSharedCheck_3731_ = !lean_is_exclusive(v_it_3684_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3713_ = v_it_3684_;
v_isShared_3714_ = v_isSharedCheck_3731_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_idx_3711_);
lean_inc(v_array_3710_);
lean_dec(v_it_3684_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3731_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3715_; lean_object* v___x_3717_; 
v___x_3715_ = lean_nat_add(v_idx_3711_, v___x_3685_);
lean_inc(v___x_3715_);
lean_inc_ref(v_array_3710_);
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 1, v___x_3715_);
v___x_3717_ = v___x_3713_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_array_3710_);
lean_ctor_set(v_reuseFailAlloc_3730_, 1, v___x_3715_);
v___x_3717_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
lean_object* v_lower_3719_; lean_object* v_upper_3720_; lean_object* v___x_3725_; lean_object* v___y_3727_; uint8_t v___x_3729_; 
v___x_3725_ = lean_byte_array_size(v_array_3710_);
v___x_3729_ = lean_nat_dec_le(v_idx_3711_, v___x_3686_);
if (v___x_3729_ == 0)
{
v___y_3727_ = v_idx_3711_;
goto v___jp_3726_;
}
else
{
lean_dec(v_idx_3711_);
v___y_3727_ = v___x_3686_;
goto v___jp_3726_;
}
v___jp_3718_:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3721_ = l_ByteArray_toByteSlice(v_array_3710_, v_lower_3719_, v_upper_3720_);
v___x_3722_ = lean_nat_sub(v_size_3683_, v___x_3685_);
lean_dec(v___x_3685_);
v___x_3723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3721_);
lean_ctor_set(v___x_3723_, 1, v___x_3722_);
v___x_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3717_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
return v___x_3724_;
}
v___jp_3726_:
{
uint8_t v___x_3728_; 
v___x_3728_ = lean_nat_dec_le(v___x_3715_, v___x_3725_);
if (v___x_3728_ == 0)
{
lean_dec(v___x_3715_);
v_lower_3719_ = v___y_3727_;
v_upper_3720_ = v___x_3725_;
goto v___jp_3718_;
}
else
{
v_lower_3719_ = v___y_3727_;
v_upper_3720_ = v___x_3715_;
goto v___jp_3718_;
}
}
}
}
}
}
else
{
lean_object* v___x_3732_; lean_object* v___x_3733_; 
lean_dec(v___x_3685_);
v___x_3732_ = lean_box(0);
v___x_3733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3733_, 0, v_it_3684_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
return v___x_3733_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData___boxed(lean_object* v_size_3734_, lean_object* v_it_3735_){
_start:
{
lean_object* v_res_3736_; 
v_res_3736_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_3734_, v_it_3735_);
lean_dec(v_size_3734_);
return v_res_3736_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData(lean_object* v_size_3737_, lean_object* v_a_3738_){
_start:
{
lean_object* v___x_3739_; 
v___x_3739_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_3737_, v_a_3738_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v_res_3740_; 
v_res_3740_ = lean_ctor_get(v___x_3739_, 1);
lean_inc(v_res_3740_);
if (lean_obj_tag(v_res_3740_) == 0)
{
lean_object* v_pos_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; 
v_pos_3741_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_pos_3741_);
lean_dec_ref_known(v___x_3739_, 2);
v___x_3742_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3743_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3742_, v_pos_3741_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v_pos_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3751_; 
v_pos_3744_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3751_ == 0)
{
lean_object* v_unused_3752_; 
v_unused_3752_ = lean_ctor_get(v___x_3743_, 1);
lean_dec(v_unused_3752_);
v___x_3746_ = v___x_3743_;
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_pos_3744_);
lean_dec(v___x_3743_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___x_3749_; 
if (v_isShared_3747_ == 0)
{
lean_ctor_set(v___x_3746_, 1, v_res_3740_);
v___x_3749_ = v___x_3746_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_pos_3744_);
lean_ctor_set(v_reuseFailAlloc_3750_, 1, v_res_3740_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
else
{
lean_object* v_pos_3753_; lean_object* v_err_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
lean_dec_ref_known(v_res_3740_, 1);
v_pos_3753_ = lean_ctor_get(v___x_3743_, 0);
v_err_3754_ = lean_ctor_get(v___x_3743_, 1);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3743_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_err_3754_);
lean_inc(v_pos_3753_);
lean_dec(v___x_3743_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_pos_3753_);
lean_ctor_set(v_reuseFailAlloc_3760_, 1, v_err_3754_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
else
{
lean_dec_ref_known(v_res_3740_, 2);
return v___x_3739_;
}
}
else
{
return v___x_3739_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData___boxed(lean_object* v_size_3762_, lean_object* v_a_3763_){
_start:
{
lean_object* v_res_3764_; 
v_res_3764_ = l_Std_Http_Protocol_H1_parseChunkSizedData(v_size_3762_, v_a_3763_);
lean_dec(v_size_3762_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField_spec__0(lean_object* v_s_3765_, lean_object* v_p_3766_){
_start:
{
uint32_t v___y_3768_; lean_object* v___x_3773_; uint8_t v_decide_3774_; 
v___x_3773_ = lean_string_utf8_byte_size(v_s_3765_);
v_decide_3774_ = lean_nat_dec_eq(v_p_3766_, v___x_3773_);
if (v_decide_3774_ == 0)
{
uint32_t v___x_3775_; uint8_t v___y_3777_; uint32_t v___x_3780_; uint8_t v___x_3781_; 
v___x_3775_ = lean_string_utf8_get_fast(v_s_3765_, v_p_3766_);
v___x_3780_ = 65;
v___x_3781_ = lean_uint32_dec_le(v___x_3780_, v___x_3775_);
if (v___x_3781_ == 0)
{
v___y_3777_ = v___x_3781_;
goto v___jp_3776_;
}
else
{
uint32_t v___x_3782_; uint8_t v___x_3783_; 
v___x_3782_ = 90;
v___x_3783_ = lean_uint32_dec_le(v___x_3775_, v___x_3782_);
v___y_3777_ = v___x_3783_;
goto v___jp_3776_;
}
v___jp_3776_:
{
if (v___y_3777_ == 0)
{
v___y_3768_ = v___x_3775_;
goto v___jp_3767_;
}
else
{
uint32_t v___x_3778_; uint32_t v___x_3779_; 
v___x_3778_ = 32;
v___x_3779_ = lean_uint32_add(v___x_3775_, v___x_3778_);
v___y_3768_ = v___x_3779_;
goto v___jp_3767_;
}
}
}
else
{
lean_dec(v_p_3766_);
return v_s_3765_;
}
v___jp_3767_:
{
lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
lean_inc(v_p_3766_);
v___x_3769_ = lean_string_utf8_set(v_s_3765_, v_p_3766_, v___y_3768_);
v___x_3770_ = l_Char_utf8Size(v___y_3768_);
v___x_3771_ = lean_nat_add(v_p_3766_, v___x_3770_);
lean_dec(v___x_3770_);
lean_dec(v_p_3766_);
v_s_3765_ = v___x_3769_;
v_p_3766_ = v___x_3771_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(lean_object* v_name_3796_){
_start:
{
lean_object* v___x_3797_; lean_object* v_n_3798_; lean_object* v___x_3799_; uint8_t v___x_3800_; 
v___x_3797_ = lean_unsigned_to_nat(0u);
v_n_3798_ = l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField_spec__0(v_name_3796_, v___x_3797_);
v___x_3799_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0));
v___x_3800_ = lean_string_dec_eq(v_n_3798_, v___x_3799_);
if (v___x_3800_ == 0)
{
lean_object* v___x_3801_; uint8_t v___x_3802_; 
v___x_3801_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1));
v___x_3802_ = lean_string_dec_eq(v_n_3798_, v___x_3801_);
if (v___x_3802_ == 0)
{
lean_object* v___x_3803_; uint8_t v___x_3804_; 
v___x_3803_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2));
v___x_3804_ = lean_string_dec_eq(v_n_3798_, v___x_3803_);
if (v___x_3804_ == 0)
{
lean_object* v___x_3805_; uint8_t v___x_3806_; 
v___x_3805_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3));
v___x_3806_ = lean_string_dec_eq(v_n_3798_, v___x_3805_);
if (v___x_3806_ == 0)
{
lean_object* v___x_3807_; uint8_t v___x_3808_; 
v___x_3807_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4));
v___x_3808_ = lean_string_dec_eq(v_n_3798_, v___x_3807_);
if (v___x_3808_ == 0)
{
lean_object* v___x_3809_; uint8_t v___x_3810_; 
v___x_3809_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__5));
v___x_3810_ = lean_string_dec_eq(v_n_3798_, v___x_3809_);
if (v___x_3810_ == 0)
{
lean_object* v___x_3811_; uint8_t v___x_3812_; 
v___x_3811_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__6));
v___x_3812_ = lean_string_dec_eq(v_n_3798_, v___x_3811_);
if (v___x_3812_ == 0)
{
lean_object* v___x_3813_; uint8_t v___x_3814_; 
v___x_3813_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__7));
v___x_3814_ = lean_string_dec_eq(v_n_3798_, v___x_3813_);
if (v___x_3814_ == 0)
{
lean_object* v___x_3815_; uint8_t v___x_3816_; 
v___x_3815_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__8));
v___x_3816_ = lean_string_dec_eq(v_n_3798_, v___x_3815_);
if (v___x_3816_ == 0)
{
lean_object* v___x_3817_; uint8_t v___x_3818_; 
v___x_3817_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__9));
v___x_3818_ = lean_string_dec_eq(v_n_3798_, v___x_3817_);
if (v___x_3818_ == 0)
{
lean_object* v___x_3819_; uint8_t v___x_3820_; 
v___x_3819_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__10));
v___x_3820_ = lean_string_dec_eq(v_n_3798_, v___x_3819_);
if (v___x_3820_ == 0)
{
lean_object* v___x_3821_; uint8_t v___x_3822_; 
v___x_3821_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__11));
v___x_3822_ = lean_string_dec_eq(v_n_3798_, v___x_3821_);
lean_dec_ref(v_n_3798_);
return v___x_3822_;
}
else
{
lean_dec_ref(v_n_3798_);
return v___x_3820_;
}
}
else
{
lean_dec_ref(v_n_3798_);
return v___x_3818_;
}
}
else
{
lean_dec_ref(v_n_3798_);
return v___x_3816_;
}
}
else
{
lean_dec_ref(v_n_3798_);
return v___x_3814_;
}
}
else
{
lean_dec_ref(v_n_3798_);
return v___x_3812_;
}
}
else
{
lean_dec_ref(v_n_3798_);
return v___x_3810_;
}
}
else
{
lean_dec_ref(v_n_3798_);
return v___x_3808_;
}
}
else
{
lean_dec_ref(v_n_3798_);
return v___x_3806_;
}
}
else
{
lean_dec_ref(v_n_3798_);
return v___x_3804_;
}
}
else
{
lean_dec_ref(v_n_3798_);
return v___x_3802_;
}
}
else
{
lean_dec_ref(v_n_3798_);
return v___x_3800_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___boxed(lean_object* v_name_3823_){
_start:
{
uint8_t v_res_3824_; lean_object* v_r_3825_; 
v_res_3824_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_name_3823_);
v_r_3825_ = lean_box(v_res_3824_);
return v_r_3825_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader(lean_object* v_limits_3827_, lean_object* v_a_3828_){
_start:
{
lean_object* v___x_3829_; 
v___x_3829_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_3827_, v_a_3828_);
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v_res_3830_; 
v_res_3830_ = lean_ctor_get(v___x_3829_, 1);
lean_inc(v_res_3830_);
if (lean_obj_tag(v_res_3830_) == 1)
{
lean_object* v_val_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3852_; 
v_val_3831_ = lean_ctor_get(v_res_3830_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v_res_3830_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3833_ = v_res_3830_;
v_isShared_3834_ = v_isSharedCheck_3852_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_val_3831_);
lean_dec(v_res_3830_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3852_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v_pos_3835_; lean_object* v_fst_3836_; uint8_t v___x_3837_; 
v_pos_3835_ = lean_ctor_get(v___x_3829_, 0);
lean_inc(v_pos_3835_);
v_fst_3836_ = lean_ctor_get(v_val_3831_, 0);
lean_inc_n(v_fst_3836_, 2);
lean_dec(v_val_3831_);
v___x_3837_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_fst_3836_);
if (v___x_3837_ == 0)
{
lean_dec(v_fst_3836_);
lean_dec(v_pos_3835_);
lean_del_object(v___x_3833_);
return v___x_3829_;
}
else
{
lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3849_; 
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3849_ == 0)
{
lean_object* v_unused_3850_; lean_object* v_unused_3851_; 
v_unused_3850_ = lean_ctor_get(v___x_3829_, 1);
lean_dec(v_unused_3850_);
v_unused_3851_ = lean_ctor_get(v___x_3829_, 0);
lean_dec(v_unused_3851_);
v___x_3839_ = v___x_3829_;
v_isShared_3840_ = v_isSharedCheck_3849_;
goto v_resetjp_3838_;
}
else
{
lean_dec(v___x_3829_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3849_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3844_; 
v___x_3841_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___closed__0));
v___x_3842_ = lean_string_append(v___x_3841_, v_fst_3836_);
lean_dec(v_fst_3836_);
if (v_isShared_3834_ == 0)
{
lean_ctor_set(v___x_3833_, 0, v___x_3842_);
v___x_3844_ = v___x_3833_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v___x_3842_);
v___x_3844_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
lean_object* v___x_3846_; 
if (v_isShared_3840_ == 0)
{
lean_ctor_set_tag(v___x_3839_, 1);
lean_ctor_set(v___x_3839_, 1, v___x_3844_);
v___x_3846_ = v___x_3839_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_pos_3835_);
lean_ctor_set(v_reuseFailAlloc_3847_, 1, v___x_3844_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
}
}
}
else
{
lean_dec(v_res_3830_);
return v___x_3829_;
}
}
else
{
return v___x_3829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___boxed(lean_object* v_limits_3853_, lean_object* v_a_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader(v_limits_3853_, v_a_3854_);
lean_dec_ref(v_limits_3853_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailers(lean_object* v_limits_3856_, lean_object* v_a_3857_){
_start:
{
lean_object* v_maxTrailerHeaders_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; 
v_maxTrailerHeaders_3858_ = lean_ctor_get(v_limits_3856_, 17);
lean_inc(v_maxTrailerHeaders_3858_);
v___x_3859_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___boxed), 2, 1);
lean_closure_set(v___x_3859_, 0, v_limits_3856_);
v___x_3860_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___x_3859_, v_maxTrailerHeaders_3858_, v_a_3857_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_pos_3861_; lean_object* v_res_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
v_pos_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_pos_3861_);
v_res_3862_ = lean_ctor_get(v___x_3860_, 1);
lean_inc(v_res_3862_);
lean_dec_ref_known(v___x_3860_, 2);
v___x_3863_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3864_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3863_, v_pos_3861_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_pos_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3872_; 
v_pos_3865_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3872_ == 0)
{
lean_object* v_unused_3873_; 
v_unused_3873_ = lean_ctor_get(v___x_3864_, 1);
lean_dec(v_unused_3873_);
v___x_3867_ = v___x_3864_;
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_pos_3865_);
lean_dec(v___x_3864_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3870_; 
if (v_isShared_3868_ == 0)
{
lean_ctor_set(v___x_3867_, 1, v_res_3862_);
v___x_3870_ = v___x_3867_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_pos_3865_);
lean_ctor_set(v_reuseFailAlloc_3871_, 1, v_res_3862_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
else
{
lean_object* v_pos_3874_; lean_object* v_err_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3882_; 
lean_dec(v_res_3862_);
v_pos_3874_ = lean_ctor_get(v___x_3864_, 0);
v_err_3875_ = lean_ctor_get(v___x_3864_, 1);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3877_ = v___x_3864_;
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_err_3875_);
lean_inc(v_pos_3874_);
lean_dec(v___x_3864_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3880_; 
if (v_isShared_3878_ == 0)
{
v___x_3880_ = v___x_3877_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_pos_3874_);
lean_ctor_set(v_reuseFailAlloc_3881_, 1, v_err_3875_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
return v___x_3880_;
}
}
}
}
else
{
return v___x_3860_;
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(uint8_t v_c_3883_){
_start:
{
uint32_t v___x_3884_; uint8_t v___y_3886_; uint32_t v___x_3891_; uint8_t v___x_3892_; 
v___x_3884_ = lean_uint8_to_uint32(v_c_3883_);
v___x_3891_ = 33;
v___x_3892_ = lean_uint32_dec_le(v___x_3891_, v___x_3884_);
if (v___x_3892_ == 0)
{
v___y_3886_ = v___x_3892_;
goto v___jp_3885_;
}
else
{
uint32_t v___x_3893_; uint8_t v___x_3894_; 
v___x_3893_ = 126;
v___x_3894_ = lean_uint32_dec_le(v___x_3884_, v___x_3893_);
v___y_3886_ = v___x_3894_;
goto v___jp_3885_;
}
v___jp_3885_:
{
if (v___y_3886_ == 0)
{
uint32_t v___x_3887_; uint8_t v___x_3888_; 
v___x_3887_ = 32;
v___x_3888_ = lean_uint32_dec_eq(v___x_3884_, v___x_3887_);
if (v___x_3888_ == 0)
{
uint32_t v___x_3889_; uint8_t v___x_3890_; 
v___x_3889_ = 9;
v___x_3890_ = lean_uint32_dec_eq(v___x_3884_, v___x_3889_);
return v___x_3890_;
}
else
{
return v___x_3888_;
}
}
else
{
return v___y_3886_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte___boxed(lean_object* v_c_3895_){
_start:
{
uint8_t v_c_boxed_3896_; uint8_t v_res_3897_; lean_object* v_r_3898_; 
v_c_boxed_3896_ = lean_unbox(v_c_3895_);
v_res_3897_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(v_c_boxed_3896_);
v_r_3898_ = lean_box(v_res_3897_);
return v_r_3898_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(lean_object* v_limits_3899_, lean_object* v_a_3900_){
_start:
{
lean_object* v_maxReasonPhraseLength_3901_; lean_object* v___f_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v_snd_3905_; lean_object* v_snd_3906_; uint8_t v___x_3907_; 
v_maxReasonPhraseLength_3901_ = lean_ctor_get(v_limits_3899_, 16);
v___f_3902_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1));
v___x_3903_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_3900_);
v___x_3904_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3902_, v_maxReasonPhraseLength_3901_, v___x_3903_, v_a_3900_);
v_snd_3905_ = lean_ctor_get(v___x_3904_, 1);
lean_inc(v_snd_3905_);
v_snd_3906_ = lean_ctor_get(v_snd_3905_, 1);
v___x_3907_ = lean_unbox(v_snd_3906_);
if (v___x_3907_ == 0)
{
lean_object* v_fst_3908_; lean_object* v_fst_3909_; lean_object* v_array_3910_; lean_object* v_idx_3911_; lean_object* v_lower_3913_; lean_object* v_upper_3914_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___y_3926_; uint8_t v___x_3928_; 
v_fst_3908_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_fst_3908_);
lean_dec_ref(v___x_3904_);
v_fst_3909_ = lean_ctor_get(v_snd_3905_, 0);
lean_inc(v_fst_3909_);
lean_dec(v_snd_3905_);
v_array_3910_ = lean_ctor_get(v_a_3900_, 0);
lean_inc_ref(v_array_3910_);
v_idx_3911_ = lean_ctor_get(v_a_3900_, 1);
lean_inc(v_idx_3911_);
lean_dec_ref(v_a_3900_);
v___x_3923_ = lean_nat_add(v_idx_3911_, v_fst_3908_);
lean_dec(v_fst_3908_);
v___x_3924_ = lean_byte_array_size(v_array_3910_);
v___x_3928_ = lean_nat_dec_le(v_idx_3911_, v___x_3903_);
if (v___x_3928_ == 0)
{
v___y_3926_ = v_idx_3911_;
goto v___jp_3925_;
}
else
{
lean_dec(v_idx_3911_);
v___y_3926_ = v___x_3903_;
goto v___jp_3925_;
}
v___jp_3912_:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; uint8_t v___x_3917_; 
v___x_3915_ = l_ByteArray_toByteSlice(v_array_3910_, v_lower_3913_, v_upper_3914_);
v___x_3916_ = l_ByteSlice_toByteArray(v___x_3915_);
v___x_3917_ = lean_string_validate_utf8(v___x_3916_);
if (v___x_3917_ == 0)
{
lean_object* v___x_3918_; lean_object* v___x_3919_; 
lean_dec_ref(v___x_3916_);
v___x_3918_ = lean_box(0);
v___x_3919_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_3918_, v_fst_3909_);
return v___x_3919_;
}
else
{
lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3920_ = lean_string_from_utf8_unchecked(v___x_3916_);
v___x_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3920_);
v___x_3922_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_3921_, v_fst_3909_);
lean_dec_ref_known(v___x_3921_, 1);
return v___x_3922_;
}
}
v___jp_3925_:
{
uint8_t v___x_3927_; 
v___x_3927_ = lean_nat_dec_le(v___x_3923_, v___x_3924_);
if (v___x_3927_ == 0)
{
lean_dec(v___x_3923_);
v_lower_3913_ = v___y_3926_;
v_upper_3914_ = v___x_3924_;
goto v___jp_3912_;
}
else
{
v_lower_3913_ = v___y_3926_;
v_upper_3914_ = v___x_3923_;
goto v___jp_3912_;
}
}
}
else
{
lean_object* v_fst_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3937_; 
lean_dec_ref(v___x_3904_);
lean_dec_ref(v_a_3900_);
v_fst_3929_ = lean_ctor_get(v_snd_3905_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v_snd_3905_);
if (v_isSharedCheck_3937_ == 0)
{
lean_object* v_unused_3938_; 
v_unused_3938_ = lean_ctor_get(v_snd_3905_, 1);
lean_dec(v_unused_3938_);
v___x_3931_ = v_snd_3905_;
v_isShared_3932_ = v_isSharedCheck_3937_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_fst_3929_);
lean_dec(v_snd_3905_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3937_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3933_; lean_object* v___x_3935_; 
v___x_3933_ = lean_box(0);
if (v_isShared_3932_ == 0)
{
lean_ctor_set_tag(v___x_3931_, 1);
lean_ctor_set(v___x_3931_, 1, v___x_3933_);
v___x_3935_ = v___x_3931_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_fst_3929_);
lean_ctor_set(v_reuseFailAlloc_3936_, 1, v___x_3933_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___boxed(lean_object* v_limits_3939_, lean_object* v_a_3940_){
_start:
{
lean_object* v_res_3941_; 
v_res_3941_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_3939_, v_a_3940_);
lean_dec_ref(v_limits_3939_);
return v_res_3941_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(lean_object* v_x_3942_){
_start:
{
if (lean_obj_tag(v_x_3942_) == 0)
{
uint8_t v___x_3943_; 
v___x_3943_ = 1;
return v___x_3943_;
}
else
{
lean_object* v_head_3944_; lean_object* v_tail_3945_; uint8_t v___y_3947_; uint32_t v___x_3949_; uint32_t v___x_3950_; uint8_t v___x_3951_; 
v_head_3944_ = lean_ctor_get(v_x_3942_, 0);
v_tail_3945_ = lean_ctor_get(v_x_3942_, 1);
v___x_3949_ = 9;
v___x_3950_ = lean_unbox_uint32(v_head_3944_);
v___x_3951_ = lean_uint32_dec_eq(v___x_3950_, v___x_3949_);
if (v___x_3951_ == 0)
{
uint32_t v___x_3952_; uint32_t v___x_3953_; uint8_t v___x_3954_; 
v___x_3952_ = 32;
v___x_3953_ = lean_unbox_uint32(v_head_3944_);
v___x_3954_ = lean_uint32_dec_eq(v___x_3953_, v___x_3952_);
if (v___x_3954_ == 0)
{
uint32_t v___x_3955_; uint32_t v___x_3956_; uint8_t v___x_3957_; 
v___x_3955_ = 33;
v___x_3956_ = lean_unbox_uint32(v_head_3944_);
v___x_3957_ = lean_uint32_dec_le(v___x_3955_, v___x_3956_);
if (v___x_3957_ == 0)
{
v___y_3947_ = v___x_3957_;
goto v___jp_3946_;
}
else
{
uint32_t v___x_3958_; uint32_t v___x_3959_; uint8_t v___x_3960_; 
v___x_3958_ = 126;
v___x_3959_ = lean_unbox_uint32(v_head_3944_);
v___x_3960_ = lean_uint32_dec_le(v___x_3959_, v___x_3958_);
v___y_3947_ = v___x_3960_;
goto v___jp_3946_;
}
}
else
{
v_x_3942_ = v_tail_3945_;
goto _start;
}
}
else
{
v_x_3942_ = v_tail_3945_;
goto _start;
}
v___jp_3946_:
{
if (v___y_3947_ == 0)
{
return v___y_3947_;
}
else
{
v_x_3942_ = v_tail_3945_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0___boxed(lean_object* v_x_3963_){
_start:
{
uint8_t v_res_3964_; lean_object* v_r_3965_; 
v_res_3964_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v_x_3963_);
lean_dec(v_x_3963_);
v_r_3965_ = lean_box(v_res_3964_);
return v_r_3965_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(lean_object* v_limits_3969_, lean_object* v_a_3970_){
_start:
{
lean_object* v___y_3972_; lean_object* v___y_3976_; lean_object* v_pos_3977_; lean_object* v_res_3978_; lean_object* v_array_3986_; lean_object* v_idx_3987_; lean_object* v___x_3988_; uint8_t v___x_3989_; 
v_array_3986_ = lean_ctor_get(v_a_3970_, 0);
v_idx_3987_ = lean_ctor_get(v_a_3970_, 1);
v___x_3988_ = lean_byte_array_size(v_array_3986_);
v___x_3989_ = lean_nat_dec_lt(v_idx_3987_, v___x_3988_);
if (v___x_3989_ == 0)
{
lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3990_ = lean_box(0);
v___x_3991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3991_, 0, v_a_3970_);
lean_ctor_set(v___x_3991_, 1, v___x_3990_);
return v___x_3991_;
}
else
{
uint8_t v_c_3992_; lean_object* v___y_3994_; lean_object* v___y_3995_; uint8_t v___y_3996_; uint8_t v___y_3997_; lean_object* v___y_3998_; uint8_t v___y_3999_; uint8_t v___x_4056_; uint8_t v___x_4057_; uint8_t v___x_4058_; lean_object* v___y_4060_; uint8_t v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; uint8_t v___y_4064_; uint8_t v___y_4076_; 
v_c_3992_ = lean_byte_array_fget(v_array_3986_, v_idx_3987_);
v___x_4056_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3);
v___x_4057_ = lean_uint8_dec_le(v___x_4056_, v_c_3992_);
v___x_4058_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4);
if (v___x_4057_ == 0)
{
v___y_4076_ = v___x_4057_;
goto v___jp_4075_;
}
else
{
uint8_t v___x_4096_; 
v___x_4096_ = lean_uint8_dec_le(v_c_3992_, v___x_4058_);
v___y_4076_ = v___x_4096_;
goto v___jp_4075_;
}
v___jp_3993_:
{
if (v___y_3999_ == 0)
{
lean_object* v___x_4000_; lean_object* v___x_4001_; 
lean_dec(v___y_3998_);
lean_dec_ref(v_array_3986_);
v___x_4000_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_4001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___y_3995_);
lean_ctor_set(v___x_4001_, 1, v___x_4000_);
return v___x_4001_;
}
else
{
lean_object* v___x_4002_; lean_object* v_it_x27_4003_; uint8_t v___x_4004_; 
lean_dec_ref(v___y_3995_);
v___x_4002_ = lean_nat_add(v___y_3998_, v___y_3994_);
lean_dec(v___y_3998_);
lean_inc(v___x_4002_);
lean_inc_ref(v_array_3986_);
v_it_x27_4003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_4003_, 0, v_array_3986_);
lean_ctor_set(v_it_x27_4003_, 1, v___x_4002_);
v___x_4004_ = lean_nat_dec_lt(v___x_4002_, v___x_3988_);
if (v___x_4004_ == 0)
{
lean_object* v___x_4005_; lean_object* v___x_4006_; 
lean_dec(v___x_4002_);
lean_dec_ref(v_array_3986_);
v___x_4005_ = lean_box(0);
v___x_4006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4006_, 0, v_it_x27_4003_);
lean_ctor_set(v___x_4006_, 1, v___x_4005_);
return v___x_4006_;
}
else
{
uint8_t v___x_4007_; uint8_t v_got_4008_; uint8_t v___x_4009_; 
v___x_4007_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v_got_4008_ = lean_byte_array_fget(v_array_3986_, v___x_4002_);
v___x_4009_ = lean_uint8_dec_eq(v_got_4008_, v___x_4007_);
if (v___x_4009_ == 0)
{
lean_object* v___x_4010_; lean_object* v___x_4011_; 
lean_dec(v___x_4002_);
lean_dec_ref(v_array_3986_);
v___x_4010_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7);
v___x_4011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4011_, 0, v_it_x27_4003_);
lean_ctor_set(v___x_4011_, 1, v___x_4010_);
return v___x_4011_;
}
else
{
uint32_t v___x_4012_; uint32_t v___x_4013_; uint32_t v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
lean_dec_ref_known(v_it_x27_4003_, 2);
v___x_4012_ = lean_uint8_to_uint32(v_c_3992_);
v___x_4013_ = lean_uint8_to_uint32(v___y_3997_);
v___x_4014_ = lean_uint8_to_uint32(v___y_3996_);
v___x_4015_ = lean_uint32_to_nat(v___x_4012_);
v___x_4016_ = lean_unsigned_to_nat(48u);
v___x_4017_ = lean_nat_sub(v___x_4015_, v___x_4016_);
lean_dec(v___x_4015_);
v___x_4018_ = lean_unsigned_to_nat(100u);
v___x_4019_ = lean_nat_mul(v___x_4017_, v___x_4018_);
lean_dec(v___x_4017_);
v___x_4020_ = lean_uint32_to_nat(v___x_4013_);
v___x_4021_ = lean_nat_sub(v___x_4020_, v___x_4016_);
lean_dec(v___x_4020_);
v___x_4022_ = lean_unsigned_to_nat(10u);
v___x_4023_ = lean_nat_mul(v___x_4021_, v___x_4022_);
lean_dec(v___x_4021_);
v___x_4024_ = lean_nat_add(v___x_4019_, v___x_4023_);
lean_dec(v___x_4023_);
lean_dec(v___x_4019_);
v___x_4025_ = lean_uint32_to_nat(v___x_4014_);
v___x_4026_ = lean_nat_sub(v___x_4025_, v___x_4016_);
lean_dec(v___x_4025_);
v___x_4027_ = lean_nat_add(v___x_4024_, v___x_4026_);
lean_dec(v___x_4026_);
lean_dec(v___x_4024_);
v___x_4028_ = lean_nat_add(v___x_4002_, v___y_3994_);
lean_dec(v___x_4002_);
v___x_4029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4029_, 0, v_array_3986_);
lean_ctor_set(v___x_4029_, 1, v___x_4028_);
v___x_4030_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_3969_, v___x_4029_);
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v_pos_4031_; lean_object* v_res_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v_pos_4031_ = lean_ctor_get(v___x_4030_, 0);
lean_inc(v_pos_4031_);
v_res_4032_ = lean_ctor_get(v___x_4030_, 1);
lean_inc(v_res_4032_);
lean_dec_ref_known(v___x_4030_, 2);
v___x_4033_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_4034_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_4033_, v_pos_4031_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v_pos_4035_; 
v_pos_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc(v_pos_4035_);
lean_dec_ref_known(v___x_4034_, 2);
v___y_3976_ = v___x_4027_;
v_pos_3977_ = v_pos_4035_;
v_res_3978_ = v_res_4032_;
goto v___jp_3975_;
}
else
{
lean_object* v_pos_4036_; lean_object* v_err_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4044_; 
lean_dec(v_res_4032_);
lean_dec(v___x_4027_);
v_pos_4036_ = lean_ctor_get(v___x_4034_, 0);
v_err_4037_ = lean_ctor_get(v___x_4034_, 1);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4034_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4039_ = v___x_4034_;
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_err_4037_);
lean_inc(v_pos_4036_);
lean_dec(v___x_4034_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_pos_4036_);
lean_ctor_set(v_reuseFailAlloc_4043_, 1, v_err_4037_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v_pos_4045_; lean_object* v_res_4046_; 
v_pos_4045_ = lean_ctor_get(v___x_4030_, 0);
lean_inc(v_pos_4045_);
v_res_4046_ = lean_ctor_get(v___x_4030_, 1);
lean_inc(v_res_4046_);
lean_dec_ref_known(v___x_4030_, 2);
v___y_3976_ = v___x_4027_;
v_pos_3977_ = v_pos_4045_;
v_res_3978_ = v_res_4046_;
goto v___jp_3975_;
}
else
{
lean_object* v_pos_4047_; lean_object* v_err_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4055_; 
lean_dec(v___x_4027_);
v_pos_4047_ = lean_ctor_get(v___x_4030_, 0);
v_err_4048_ = lean_ctor_get(v___x_4030_, 1);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_4030_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4050_ = v___x_4030_;
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_err_4048_);
lean_inc(v_pos_4047_);
lean_dec(v___x_4030_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4053_; 
if (v_isShared_4051_ == 0)
{
v___x_4053_ = v___x_4050_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_pos_4047_);
lean_ctor_set(v_reuseFailAlloc_4054_, 1, v_err_4048_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
}
}
}
}
}
v___jp_4059_:
{
if (v___y_4064_ == 0)
{
lean_object* v___x_4065_; lean_object* v___x_4066_; 
lean_dec(v___y_4063_);
lean_dec_ref(v_array_3986_);
v___x_4065_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_4066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4066_, 0, v___y_4062_);
lean_ctor_set(v___x_4066_, 1, v___x_4065_);
return v___x_4066_;
}
else
{
lean_object* v___x_4067_; lean_object* v_it_x27_4068_; uint8_t v___x_4069_; 
lean_dec_ref(v___y_4062_);
v___x_4067_ = lean_nat_add(v___y_4063_, v___y_4060_);
lean_dec(v___y_4063_);
lean_inc(v___x_4067_);
lean_inc_ref(v_array_3986_);
v_it_x27_4068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_4068_, 0, v_array_3986_);
lean_ctor_set(v_it_x27_4068_, 1, v___x_4067_);
v___x_4069_ = lean_nat_dec_lt(v___x_4067_, v___x_3988_);
if (v___x_4069_ == 0)
{
lean_object* v___x_4070_; lean_object* v___x_4071_; 
lean_dec(v___x_4067_);
lean_dec_ref(v_array_3986_);
v___x_4070_ = lean_box(0);
v___x_4071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4071_, 0, v_it_x27_4068_);
lean_ctor_set(v___x_4071_, 1, v___x_4070_);
return v___x_4071_;
}
else
{
uint8_t v_c_4072_; uint8_t v___x_4073_; 
v_c_4072_ = lean_byte_array_fget(v_array_3986_, v___x_4067_);
v___x_4073_ = lean_uint8_dec_le(v___x_4056_, v_c_4072_);
if (v___x_4073_ == 0)
{
v___y_3994_ = v___y_4060_;
v___y_3995_ = v_it_x27_4068_;
v___y_3996_ = v_c_4072_;
v___y_3997_ = v___y_4061_;
v___y_3998_ = v___x_4067_;
v___y_3999_ = v___x_4073_;
goto v___jp_3993_;
}
else
{
uint8_t v___x_4074_; 
v___x_4074_ = lean_uint8_dec_le(v_c_4072_, v___x_4058_);
v___y_3994_ = v___y_4060_;
v___y_3995_ = v_it_x27_4068_;
v___y_3996_ = v_c_4072_;
v___y_3997_ = v___y_4061_;
v___y_3998_ = v___x_4067_;
v___y_3999_ = v___x_4074_;
goto v___jp_3993_;
}
}
}
}
v___jp_4075_:
{
if (v___y_4076_ == 0)
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_4078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4078_, 0, v_a_3970_);
lean_ctor_set(v___x_4078_, 1, v___x_4077_);
return v___x_4078_;
}
else
{
lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4093_; 
lean_inc(v_idx_3987_);
lean_inc_ref(v_array_3986_);
v_isSharedCheck_4093_ = !lean_is_exclusive(v_a_3970_);
if (v_isSharedCheck_4093_ == 0)
{
lean_object* v_unused_4094_; lean_object* v_unused_4095_; 
v_unused_4094_ = lean_ctor_get(v_a_3970_, 1);
lean_dec(v_unused_4094_);
v_unused_4095_ = lean_ctor_get(v_a_3970_, 0);
lean_dec(v_unused_4095_);
v___x_4080_ = v_a_3970_;
v_isShared_4081_ = v_isSharedCheck_4093_;
goto v_resetjp_4079_;
}
else
{
lean_dec(v_a_3970_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4093_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v_it_x27_4085_; 
v___x_4082_ = lean_unsigned_to_nat(1u);
v___x_4083_ = lean_nat_add(v_idx_3987_, v___x_4082_);
lean_dec(v_idx_3987_);
lean_inc(v___x_4083_);
lean_inc_ref(v_array_3986_);
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 1, v___x_4083_);
v_it_x27_4085_ = v___x_4080_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_array_3986_);
lean_ctor_set(v_reuseFailAlloc_4092_, 1, v___x_4083_);
v_it_x27_4085_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
uint8_t v___x_4086_; 
v___x_4086_ = lean_nat_dec_lt(v___x_4083_, v___x_3988_);
if (v___x_4086_ == 0)
{
lean_object* v___x_4087_; lean_object* v___x_4088_; 
lean_dec(v___x_4083_);
lean_dec_ref(v_array_3986_);
v___x_4087_ = lean_box(0);
v___x_4088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4088_, 0, v_it_x27_4085_);
lean_ctor_set(v___x_4088_, 1, v___x_4087_);
return v___x_4088_;
}
else
{
uint8_t v_c_4089_; uint8_t v___x_4090_; 
v_c_4089_ = lean_byte_array_fget(v_array_3986_, v___x_4083_);
v___x_4090_ = lean_uint8_dec_le(v___x_4056_, v_c_4089_);
if (v___x_4090_ == 0)
{
v___y_4060_ = v___x_4082_;
v___y_4061_ = v_c_4089_;
v___y_4062_ = v_it_x27_4085_;
v___y_4063_ = v___x_4083_;
v___y_4064_ = v___x_4090_;
goto v___jp_4059_;
}
else
{
uint8_t v___x_4091_; 
v___x_4091_ = lean_uint8_dec_le(v_c_4089_, v___x_4058_);
v___y_4060_ = v___x_4082_;
v___y_4061_ = v_c_4089_;
v___y_4062_ = v_it_x27_4085_;
v___y_4063_ = v___x_4083_;
v___y_4064_ = v___x_4091_;
goto v___jp_4059_;
}
}
}
}
}
}
}
v___jp_3971_:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3973_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__1));
v___x_3974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3974_, 0, v___y_3972_);
lean_ctor_set(v___x_3974_, 1, v___x_3973_);
return v___x_3974_;
}
v___jp_3975_:
{
lean_object* v___x_3979_; uint8_t v___x_3980_; 
lean_inc_ref(v_res_3978_);
v___x_3979_ = lean_string_data(v_res_3978_);
v___x_3980_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v___x_3979_);
lean_dec(v___x_3979_);
if (v___x_3980_ == 0)
{
lean_dec_ref(v_res_3978_);
lean_dec(v___y_3976_);
v___y_3972_ = v_pos_3977_;
goto v___jp_3971_;
}
else
{
lean_object* v___x_3981_; uint16_t v___x_3982_; lean_object* v___x_3983_; 
v___x_3981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3981_, 0, v_res_3978_);
v___x_3982_ = lean_uint16_of_nat(v___y_3976_);
lean_dec(v___y_3976_);
v___x_3983_ = l_Std_Http_Status_ofCode(v___x_3981_, v___x_3982_);
if (lean_obj_tag(v___x_3983_) == 1)
{
lean_object* v_val_3984_; lean_object* v___x_3985_; 
v_val_3984_ = lean_ctor_get(v___x_3983_, 0);
lean_inc(v_val_3984_);
lean_dec_ref_known(v___x_3983_, 1);
v___x_3985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3985_, 0, v_pos_3977_);
lean_ctor_set(v___x_3985_, 1, v_val_3984_);
return v___x_3985_;
}
else
{
lean_dec(v___x_3983_);
v___y_3972_ = v_pos_3977_;
goto v___jp_3971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___boxed(lean_object* v_limits_4097_, lean_object* v_a_4098_){
_start:
{
lean_object* v_res_4099_; 
v_res_4099_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_4097_, v_a_4098_);
lean_dec_ref(v_limits_4097_);
return v_res_4099_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine(lean_object* v_limits_4100_, lean_object* v_a_4101_){
_start:
{
lean_object* v___y_4103_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; uint8_t v___y_4110_; uint8_t v___y_4111_; lean_object* v_pos_4123_; lean_object* v_res_4124_; lean_object* v___x_4142_; 
v___x_4142_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_4101_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v_pos_4143_; lean_object* v_res_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4174_; 
v_pos_4143_ = lean_ctor_get(v___x_4142_, 0);
v_res_4144_ = lean_ctor_get(v___x_4142_, 1);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4146_ = v___x_4142_;
v_isShared_4147_ = v_isSharedCheck_4174_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_res_4144_);
lean_inc(v_pos_4143_);
lean_dec(v___x_4142_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4174_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v_array_4148_; lean_object* v_idx_4149_; lean_object* v___x_4150_; uint8_t v___x_4151_; 
v_array_4148_ = lean_ctor_get(v_pos_4143_, 0);
v_idx_4149_ = lean_ctor_get(v_pos_4143_, 1);
v___x_4150_ = lean_byte_array_size(v_array_4148_);
v___x_4151_ = lean_nat_dec_lt(v_idx_4149_, v___x_4150_);
if (v___x_4151_ == 0)
{
lean_object* v___x_4152_; lean_object* v___x_4154_; 
lean_dec(v_res_4144_);
v___x_4152_ = lean_box(0);
if (v_isShared_4147_ == 0)
{
lean_ctor_set_tag(v___x_4146_, 1);
lean_ctor_set(v___x_4146_, 1, v___x_4152_);
v___x_4154_ = v___x_4146_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_pos_4143_);
lean_ctor_set(v_reuseFailAlloc_4155_, 1, v___x_4152_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
return v___x_4154_;
}
}
else
{
uint8_t v___x_4156_; uint8_t v_got_4157_; uint8_t v___x_4158_; 
v___x_4156_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v_got_4157_ = lean_byte_array_fget(v_array_4148_, v_idx_4149_);
v___x_4158_ = lean_uint8_dec_eq(v_got_4157_, v___x_4156_);
if (v___x_4158_ == 0)
{
lean_object* v___x_4159_; lean_object* v___x_4161_; 
lean_dec(v_res_4144_);
v___x_4159_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7);
if (v_isShared_4147_ == 0)
{
lean_ctor_set_tag(v___x_4146_, 1);
lean_ctor_set(v___x_4146_, 1, v___x_4159_);
v___x_4161_ = v___x_4146_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_pos_4143_);
lean_ctor_set(v_reuseFailAlloc_4162_, 1, v___x_4159_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
return v___x_4161_;
}
}
else
{
lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4171_; 
lean_inc(v_idx_4149_);
lean_inc_ref(v_array_4148_);
lean_del_object(v___x_4146_);
v_isSharedCheck_4171_ = !lean_is_exclusive(v_pos_4143_);
if (v_isSharedCheck_4171_ == 0)
{
lean_object* v_unused_4172_; lean_object* v_unused_4173_; 
v_unused_4172_ = lean_ctor_get(v_pos_4143_, 1);
lean_dec(v_unused_4172_);
v_unused_4173_ = lean_ctor_get(v_pos_4143_, 0);
lean_dec(v_unused_4173_);
v___x_4164_ = v_pos_4143_;
v_isShared_4165_ = v_isSharedCheck_4171_;
goto v_resetjp_4163_;
}
else
{
lean_dec(v_pos_4143_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4171_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4169_; 
v___x_4166_ = lean_unsigned_to_nat(1u);
v___x_4167_ = lean_nat_add(v_idx_4149_, v___x_4166_);
lean_dec(v_idx_4149_);
if (v_isShared_4165_ == 0)
{
lean_ctor_set(v___x_4164_, 1, v___x_4167_);
v___x_4169_ = v___x_4164_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_array_4148_);
lean_ctor_set(v_reuseFailAlloc_4170_, 1, v___x_4167_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
v_pos_4123_ = v___x_4169_;
v_res_4124_ = v_res_4144_;
goto v___jp_4122_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v_pos_4175_; lean_object* v_res_4176_; 
v_pos_4175_ = lean_ctor_get(v___x_4142_, 0);
lean_inc(v_pos_4175_);
v_res_4176_ = lean_ctor_get(v___x_4142_, 1);
lean_inc(v_res_4176_);
lean_dec_ref_known(v___x_4142_, 2);
v_pos_4123_ = v_pos_4175_;
v_res_4124_ = v_res_4176_;
goto v___jp_4122_;
}
else
{
lean_object* v_pos_4177_; lean_object* v_err_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4185_; 
v_pos_4177_ = lean_ctor_get(v___x_4142_, 0);
v_err_4178_ = lean_ctor_get(v___x_4142_, 1);
v_isSharedCheck_4185_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4180_ = v___x_4142_;
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_err_4178_);
lean_inc(v_pos_4177_);
lean_dec(v___x_4142_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v___x_4183_; 
if (v_isShared_4181_ == 0)
{
v___x_4183_ = v___x_4180_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v_pos_4177_);
lean_ctor_set(v_reuseFailAlloc_4184_, 1, v_err_4178_);
v___x_4183_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
return v___x_4183_;
}
}
}
}
v___jp_4102_:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4104_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
v___x_4105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4105_, 0, v___y_4103_);
lean_ctor_set(v___x_4105_, 1, v___x_4104_);
return v___x_4105_;
}
v___jp_4106_:
{
if (v___y_4111_ == 0)
{
if (v___y_4110_ == 0)
{
lean_dec(v___y_4109_);
lean_dec(v___y_4107_);
v___y_4103_ = v___y_4108_;
goto v___jp_4102_;
}
else
{
lean_object* v___x_4112_; uint8_t v___x_4113_; 
v___x_4112_ = lean_unsigned_to_nat(0u);
v___x_4113_ = lean_nat_dec_eq(v___y_4109_, v___x_4112_);
lean_dec(v___y_4109_);
if (v___x_4113_ == 0)
{
lean_dec(v___y_4107_);
v___y_4103_ = v___y_4108_;
goto v___jp_4102_;
}
else
{
uint8_t v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4114_ = 0;
v___x_4115_ = l_Std_Http_Headers_empty;
v___x_4116_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4116_, 0, v___y_4107_);
lean_ctor_set(v___x_4116_, 1, v___x_4115_);
lean_ctor_set_uint8(v___x_4116_, sizeof(void*)*2, v___x_4114_);
v___x_4117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4117_, 0, v___y_4108_);
lean_ctor_set(v___x_4117_, 1, v___x_4116_);
return v___x_4117_;
}
}
}
else
{
uint8_t v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; 
lean_dec(v___y_4109_);
v___x_4118_ = 1;
v___x_4119_ = l_Std_Http_Headers_empty;
v___x_4120_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4120_, 0, v___y_4107_);
lean_ctor_set(v___x_4120_, 1, v___x_4119_);
lean_ctor_set_uint8(v___x_4120_, sizeof(void*)*2, v___x_4118_);
v___x_4121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4121_, 0, v___y_4108_);
lean_ctor_set(v___x_4121_, 1, v___x_4120_);
return v___x_4121_;
}
}
v___jp_4122_:
{
lean_object* v_fst_4125_; lean_object* v_snd_4126_; lean_object* v___x_4127_; 
v_fst_4125_ = lean_ctor_get(v_res_4124_, 0);
lean_inc(v_fst_4125_);
v_snd_4126_ = lean_ctor_get(v_res_4124_, 1);
lean_inc(v_snd_4126_);
lean_dec_ref(v_res_4124_);
v___x_4127_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_4100_, v_pos_4123_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_pos_4128_; lean_object* v_res_4129_; lean_object* v___x_4130_; uint8_t v___x_4131_; 
v_pos_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_pos_4128_);
v_res_4129_ = lean_ctor_get(v___x_4127_, 1);
lean_inc(v_res_4129_);
lean_dec_ref_known(v___x_4127_, 2);
v___x_4130_ = lean_unsigned_to_nat(1u);
v___x_4131_ = lean_nat_dec_eq(v_fst_4125_, v___x_4130_);
lean_dec(v_fst_4125_);
if (v___x_4131_ == 0)
{
v___y_4107_ = v_res_4129_;
v___y_4108_ = v_pos_4128_;
v___y_4109_ = v_snd_4126_;
v___y_4110_ = v___x_4131_;
v___y_4111_ = v___x_4131_;
goto v___jp_4106_;
}
else
{
uint8_t v___x_4132_; 
v___x_4132_ = lean_nat_dec_eq(v_snd_4126_, v___x_4130_);
v___y_4107_ = v_res_4129_;
v___y_4108_ = v_pos_4128_;
v___y_4109_ = v_snd_4126_;
v___y_4110_ = v___x_4131_;
v___y_4111_ = v___x_4132_;
goto v___jp_4106_;
}
}
else
{
lean_object* v_pos_4133_; lean_object* v_err_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4141_; 
lean_dec(v_snd_4126_);
lean_dec(v_fst_4125_);
v_pos_4133_ = lean_ctor_get(v___x_4127_, 0);
v_err_4134_ = lean_ctor_get(v___x_4127_, 1);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4136_ = v___x_4127_;
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_err_4134_);
lean_inc(v_pos_4133_);
lean_dec(v___x_4127_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4139_; 
if (v_isShared_4137_ == 0)
{
v___x_4139_ = v___x_4136_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_pos_4133_);
lean_ctor_set(v_reuseFailAlloc_4140_, 1, v_err_4134_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
return v___x_4139_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine___boxed(lean_object* v_limits_4186_, lean_object* v_a_4187_){
_start:
{
lean_object* v_res_4188_; 
v_res_4188_ = l_Std_Http_Protocol_H1_parseStatusLine(v_limits_4186_, v_a_4187_);
lean_dec_ref(v_limits_4186_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion(lean_object* v_limits_4189_, lean_object* v_a_4190_){
_start:
{
lean_object* v_pos_4192_; lean_object* v_res_4193_; lean_object* v___x_4223_; 
v___x_4223_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_4190_);
if (lean_obj_tag(v___x_4223_) == 0)
{
lean_object* v_pos_4224_; lean_object* v_res_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4255_; 
v_pos_4224_ = lean_ctor_get(v___x_4223_, 0);
v_res_4225_ = lean_ctor_get(v___x_4223_, 1);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4223_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4227_ = v___x_4223_;
v_isShared_4228_ = v_isSharedCheck_4255_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_res_4225_);
lean_inc(v_pos_4224_);
lean_dec(v___x_4223_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4255_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v_array_4229_; lean_object* v_idx_4230_; lean_object* v___x_4231_; uint8_t v___x_4232_; 
v_array_4229_ = lean_ctor_get(v_pos_4224_, 0);
v_idx_4230_ = lean_ctor_get(v_pos_4224_, 1);
v___x_4231_ = lean_byte_array_size(v_array_4229_);
v___x_4232_ = lean_nat_dec_lt(v_idx_4230_, v___x_4231_);
if (v___x_4232_ == 0)
{
lean_object* v___x_4233_; lean_object* v___x_4235_; 
lean_dec(v_res_4225_);
v___x_4233_ = lean_box(0);
if (v_isShared_4228_ == 0)
{
lean_ctor_set_tag(v___x_4227_, 1);
lean_ctor_set(v___x_4227_, 1, v___x_4233_);
v___x_4235_ = v___x_4227_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_pos_4224_);
lean_ctor_set(v_reuseFailAlloc_4236_, 1, v___x_4233_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
else
{
uint8_t v___x_4237_; uint8_t v_got_4238_; uint8_t v___x_4239_; 
v___x_4237_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v_got_4238_ = lean_byte_array_fget(v_array_4229_, v_idx_4230_);
v___x_4239_ = lean_uint8_dec_eq(v_got_4238_, v___x_4237_);
if (v___x_4239_ == 0)
{
lean_object* v___x_4240_; lean_object* v___x_4242_; 
lean_dec(v_res_4225_);
v___x_4240_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7);
if (v_isShared_4228_ == 0)
{
lean_ctor_set_tag(v___x_4227_, 1);
lean_ctor_set(v___x_4227_, 1, v___x_4240_);
v___x_4242_ = v___x_4227_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_pos_4224_);
lean_ctor_set(v_reuseFailAlloc_4243_, 1, v___x_4240_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
else
{
lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4252_; 
lean_inc(v_idx_4230_);
lean_inc_ref(v_array_4229_);
lean_del_object(v___x_4227_);
v_isSharedCheck_4252_ = !lean_is_exclusive(v_pos_4224_);
if (v_isSharedCheck_4252_ == 0)
{
lean_object* v_unused_4253_; lean_object* v_unused_4254_; 
v_unused_4253_ = lean_ctor_get(v_pos_4224_, 1);
lean_dec(v_unused_4253_);
v_unused_4254_ = lean_ctor_get(v_pos_4224_, 0);
lean_dec(v_unused_4254_);
v___x_4245_ = v_pos_4224_;
v_isShared_4246_ = v_isSharedCheck_4252_;
goto v_resetjp_4244_;
}
else
{
lean_dec(v_pos_4224_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4252_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4250_; 
v___x_4247_ = lean_unsigned_to_nat(1u);
v___x_4248_ = lean_nat_add(v_idx_4230_, v___x_4247_);
lean_dec(v_idx_4230_);
if (v_isShared_4246_ == 0)
{
lean_ctor_set(v___x_4245_, 1, v___x_4248_);
v___x_4250_ = v___x_4245_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v_array_4229_);
lean_ctor_set(v_reuseFailAlloc_4251_, 1, v___x_4248_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
v_pos_4192_ = v___x_4250_;
v_res_4193_ = v_res_4225_;
goto v___jp_4191_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_4223_) == 0)
{
lean_object* v_pos_4256_; lean_object* v_res_4257_; 
v_pos_4256_ = lean_ctor_get(v___x_4223_, 0);
lean_inc(v_pos_4256_);
v_res_4257_ = lean_ctor_get(v___x_4223_, 1);
lean_inc(v_res_4257_);
lean_dec_ref_known(v___x_4223_, 2);
v_pos_4192_ = v_pos_4256_;
v_res_4193_ = v_res_4257_;
goto v___jp_4191_;
}
else
{
lean_object* v_pos_4258_; lean_object* v_err_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4266_; 
v_pos_4258_ = lean_ctor_get(v___x_4223_, 0);
v_err_4259_ = lean_ctor_get(v___x_4223_, 1);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4223_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4261_ = v___x_4223_;
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_err_4259_);
lean_inc(v_pos_4258_);
lean_dec(v___x_4223_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4264_; 
if (v_isShared_4262_ == 0)
{
v___x_4264_ = v___x_4261_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_pos_4258_);
lean_ctor_set(v_reuseFailAlloc_4265_, 1, v_err_4259_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
}
v___jp_4191_:
{
lean_object* v_fst_4194_; lean_object* v_snd_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4222_; 
v_fst_4194_ = lean_ctor_get(v_res_4193_, 0);
v_snd_4195_ = lean_ctor_get(v_res_4193_, 1);
v_isSharedCheck_4222_ = !lean_is_exclusive(v_res_4193_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4197_ = v_res_4193_;
v_isShared_4198_ = v_isSharedCheck_4222_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_snd_4195_);
lean_inc(v_fst_4194_);
lean_dec(v_res_4193_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4222_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4199_; 
v___x_4199_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_4189_, v_pos_4192_);
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v_pos_4200_; lean_object* v_res_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4212_; 
v_pos_4200_ = lean_ctor_get(v___x_4199_, 0);
v_res_4201_ = lean_ctor_get(v___x_4199_, 1);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4203_ = v___x_4199_;
v_isShared_4204_ = v_isSharedCheck_4212_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_res_4201_);
lean_inc(v_pos_4200_);
lean_dec(v___x_4199_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4212_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4205_; lean_object* v___x_4207_; 
v___x_4205_ = l_Std_Http_Version_ofNumber_x3f(v_fst_4194_, v_snd_4195_);
lean_dec(v_snd_4195_);
lean_dec(v_fst_4194_);
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 1, v___x_4205_);
lean_ctor_set(v___x_4197_, 0, v_res_4201_);
v___x_4207_ = v___x_4197_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_res_4201_);
lean_ctor_set(v_reuseFailAlloc_4211_, 1, v___x_4205_);
v___x_4207_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
lean_object* v___x_4209_; 
if (v_isShared_4204_ == 0)
{
lean_ctor_set(v___x_4203_, 1, v___x_4207_);
v___x_4209_ = v___x_4203_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_pos_4200_);
lean_ctor_set(v_reuseFailAlloc_4210_, 1, v___x_4207_);
v___x_4209_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
return v___x_4209_;
}
}
}
}
else
{
lean_object* v_pos_4213_; lean_object* v_err_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4221_; 
lean_del_object(v___x_4197_);
lean_dec(v_snd_4195_);
lean_dec(v_fst_4194_);
v_pos_4213_ = lean_ctor_get(v___x_4199_, 0);
v_err_4214_ = lean_ctor_get(v___x_4199_, 1);
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4216_ = v___x_4199_;
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_err_4214_);
lean_inc(v_pos_4213_);
lean_dec(v___x_4199_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4219_; 
if (v_isShared_4217_ == 0)
{
v___x_4219_ = v___x_4216_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_pos_4213_);
lean_ctor_set(v_reuseFailAlloc_4220_, 1, v_err_4214_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion___boxed(lean_object* v_limits_4267_, lean_object* v_a_4268_){
_start:
{
lean_object* v_res_4269_; 
v_res_4269_ = l_Std_Http_Protocol_H1_parseStatusLineRawVersion(v_limits_4267_, v_a_4268_);
lean_dec_ref(v_limits_4267_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseLastChunkBody(lean_object* v_limits_4270_, lean_object* v_a_4271_){
_start:
{
lean_object* v_maxTrailerHeaders_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
v_maxTrailerHeaders_4272_ = lean_ctor_get(v_limits_4270_, 17);
lean_inc(v_maxTrailerHeaders_4272_);
v___x_4273_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___boxed), 2, 1);
lean_closure_set(v___x_4273_, 0, v_limits_4270_);
v___x_4274_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___x_4273_, v_maxTrailerHeaders_4272_, v_a_4271_);
if (lean_obj_tag(v___x_4274_) == 0)
{
lean_object* v_pos_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v_pos_4275_ = lean_ctor_get(v___x_4274_, 0);
lean_inc(v_pos_4275_);
lean_dec_ref_known(v___x_4274_, 2);
v___x_4276_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_4277_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_4276_, v_pos_4275_);
return v___x_4277_;
}
else
{
lean_object* v_pos_4278_; lean_object* v_err_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4286_; 
v_pos_4278_ = lean_ctor_get(v___x_4274_, 0);
v_err_4279_ = lean_ctor_get(v___x_4274_, 1);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4281_ = v___x_4274_;
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_err_4279_);
lean_inc(v_pos_4278_);
lean_dec(v___x_4274_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4284_; 
if (v_isShared_4282_ == 0)
{
v___x_4284_ = v___x_4281_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_pos_4278_);
lean_ctor_set(v_reuseFailAlloc_4285_, 1, v_err_4279_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
return v___x_4284_;
}
}
}
}
}
lean_object* runtime_initialize_Std_Internal_Parsec(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec_ByteArray(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Config(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Protocol_H1_Parser(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
