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
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___closed__0;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "too many leading empty lines"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___closed__1_value)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines___boxed(lean_object*, lean_object*);
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
lean_dec_ref(v___x_73_);
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
lean_dec_ref(v___x_73_);
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
static uint8_t _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___closed__0(void){
_start:
{
uint32_t v___x_256_; uint8_t v___x_257_; 
v___x_256_ = 13;
v___x_257_ = lean_uint32_to_uint8(v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0(lean_object* v_limits_261_, lean_object* v_b_262_, lean_object* v___y_263_){
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
lean_ctor_set(v___x_268_, 1, v_b_262_);
return v___x_268_;
}
else
{
uint8_t v___x_269_; uint8_t v___x_270_; uint8_t v___x_271_; 
v___x_269_ = lean_byte_array_fget(v_array_264_, v_idx_265_);
v___x_270_ = lean_uint8_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___closed__0, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___closed__0_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___closed__0);
v___x_271_ = lean_uint8_dec_eq(v___x_269_, v___x_270_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; 
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___y_263_);
lean_ctor_set(v___x_272_, 1, v_b_262_);
return v___x_272_;
}
else
{
lean_object* v_maxLeadingEmptyLines_273_; uint8_t v___x_274_; 
v_maxLeadingEmptyLines_273_ = lean_ctor_get(v_limits_261_, 9);
v___x_274_ = lean_nat_dec_le(v_maxLeadingEmptyLines_273_, v_b_262_);
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
lean_dec_ref(v___x_276_);
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = lean_nat_add(v_b_262_, v___x_278_);
lean_dec(v_b_262_);
v_b_262_ = v___x_279_;
v___y_263_ = v_pos_277_;
goto _start;
}
else
{
lean_object* v_pos_281_; lean_object* v_err_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
lean_dec(v_b_262_);
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
lean_dec(v_b_262_);
v___x_290_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___closed__2));
v___x_291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_291_, 0, v___y_263_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
return v___x_291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___boxed(lean_object* v_limits_292_, lean_object* v_b_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0(v_limits_292_, v_b_293_, v___y_294_);
lean_dec_ref(v_limits_292_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(lean_object* v_limits_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_count_298_; lean_object* v___x_299_; 
v_count_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0(v_limits_296_, v_count_298_, v_a_297_);
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
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0(void){
_start:
{
uint32_t v___x_322_; uint8_t v___x_323_; 
v___x_322_ = 32;
v___x_323_ = lean_uint32_to_uint8(v___x_322_);
return v___x_323_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__2(void){
_start:
{
uint8_t v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v___x_326_ = lean_uint8_to_nat(v___x_325_);
return v___x_326_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__3(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__2);
v___x_328_ = l_Nat_reprFast(v___x_327_);
return v___x_328_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__4(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__3);
v___x_330_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_331_ = lean_string_append(v___x_330_, v___x_329_);
return v___x_331_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__6(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_333_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__5));
v___x_334_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__4);
v___x_335_ = lean_string_append(v___x_334_, v___x_333_);
return v___x_335_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__6, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__6_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__6);
v___x_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp(lean_object* v_a_338_){
_start:
{
lean_object* v_array_339_; lean_object* v_idx_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v_array_339_ = lean_ctor_get(v_a_338_, 0);
v_idx_340_ = lean_ctor_get(v_a_338_, 1);
v___x_341_ = lean_byte_array_size(v_array_339_);
v___x_342_ = lean_nat_dec_lt(v_idx_340_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_box(0);
v___x_344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_344_, 0, v_a_338_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
return v___x_344_;
}
else
{
uint8_t v___x_345_; uint8_t v_got_346_; uint8_t v___x_347_; 
v___x_345_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v_got_346_ = lean_byte_array_fget(v_array_339_, v_idx_340_);
v___x_347_ = lean_uint8_dec_eq(v_got_346_, v___x_345_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7);
v___x_349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_349_, 0, v_a_338_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
return v___x_349_;
}
else
{
lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_360_; 
lean_inc(v_idx_340_);
lean_inc_ref(v_array_339_);
v_isSharedCheck_360_ = !lean_is_exclusive(v_a_338_);
if (v_isSharedCheck_360_ == 0)
{
lean_object* v_unused_361_; lean_object* v_unused_362_; 
v_unused_361_ = lean_ctor_get(v_a_338_, 1);
lean_dec(v_unused_361_);
v_unused_362_ = lean_ctor_get(v_a_338_, 0);
lean_dec(v_unused_362_);
v___x_351_ = v_a_338_;
v_isShared_352_ = v_isSharedCheck_360_;
goto v_resetjp_350_;
}
else
{
lean_dec(v_a_338_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_360_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_353_ = lean_unsigned_to_nat(1u);
v___x_354_ = lean_nat_add(v_idx_340_, v___x_353_);
lean_dec(v_idx_340_);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 1, v___x_354_);
v___x_356_ = v___x_351_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_array_339_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v___x_354_);
v___x_356_ = v_reuseFailAlloc_359_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_box(0);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_356_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
return v___x_358_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows(lean_object* v_limits_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_pos_370_; lean_object* v_maxSpaceSequence_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v_snd_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_408_; 
v_maxSpaceSequence_373_ = lean_ctor_get(v_limits_367_, 8);
v___x_374_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__0));
v___x_375_ = lean_unsigned_to_nat(0u);
v___x_376_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___x_374_, v_maxSpaceSequence_373_, v___x_375_, v_a_368_);
v_snd_377_ = lean_ctor_get(v___x_376_, 1);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; 
v_unused_409_ = lean_ctor_get(v___x_376_, 0);
lean_dec(v_unused_409_);
v___x_379_ = v___x_376_;
v_isShared_380_ = v_isSharedCheck_408_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_snd_377_);
lean_dec(v___x_376_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_408_;
goto v_resetjp_378_;
}
v___jp_369_:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_box(0);
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v_pos_370_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
return v___x_372_;
}
v_resetjp_378_:
{
lean_object* v_fst_381_; lean_object* v_snd_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_407_; 
v_fst_381_ = lean_ctor_get(v_snd_377_, 0);
v_snd_382_ = lean_ctor_get(v_snd_377_, 1);
v_isSharedCheck_407_ = !lean_is_exclusive(v_snd_377_);
if (v_isSharedCheck_407_ == 0)
{
v___x_384_ = v_snd_377_;
v_isShared_385_ = v_isSharedCheck_407_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_snd_382_);
lean_inc(v_fst_381_);
lean_dec(v_snd_377_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_407_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
uint8_t v___y_387_; uint8_t v___x_392_; 
v___x_392_ = lean_unbox(v_snd_382_);
lean_dec(v_snd_382_);
if (v___x_392_ == 0)
{
lean_object* v_array_393_; lean_object* v_idx_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
lean_del_object(v___x_379_);
v_array_393_ = lean_ctor_get(v_fst_381_, 0);
v_idx_394_ = lean_ctor_get(v_fst_381_, 1);
v___x_395_ = lean_byte_array_size(v_array_393_);
v___x_396_ = lean_nat_dec_lt(v_idx_394_, v___x_395_);
if (v___x_396_ == 0)
{
lean_del_object(v___x_384_);
v_pos_370_ = v_fst_381_;
goto v___jp_369_;
}
else
{
uint8_t v___x_397_; uint32_t v___x_398_; uint32_t v___x_399_; uint8_t v___x_400_; 
v___x_397_ = lean_byte_array_fget(v_array_393_, v_idx_394_);
v___x_398_ = lean_uint8_to_uint32(v___x_397_);
v___x_399_ = 32;
v___x_400_ = lean_uint32_dec_eq(v___x_398_, v___x_399_);
if (v___x_400_ == 0)
{
uint32_t v___x_401_; uint8_t v___x_402_; 
v___x_401_ = 9;
v___x_402_ = lean_uint32_dec_eq(v___x_398_, v___x_401_);
if (v___x_402_ == 0)
{
lean_del_object(v___x_384_);
v_pos_370_ = v_fst_381_;
goto v___jp_369_;
}
else
{
v___y_387_ = v___x_396_;
goto v___jp_386_;
}
}
else
{
v___y_387_ = v___x_396_;
goto v___jp_386_;
}
}
}
else
{
lean_object* v___x_403_; lean_object* v___x_405_; 
lean_del_object(v___x_384_);
v___x_403_ = lean_box(0);
if (v_isShared_380_ == 0)
{
lean_ctor_set_tag(v___x_379_, 1);
lean_ctor_set(v___x_379_, 1, v___x_403_);
lean_ctor_set(v___x_379_, 0, v_fst_381_);
v___x_405_ = v___x_379_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_fst_381_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v___x_403_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
v___jp_386_:
{
if (v___y_387_ == 0)
{
lean_del_object(v___x_384_);
v_pos_370_ = v_fst_381_;
goto v___jp_369_;
}
else
{
lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_388_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2));
if (v_isShared_385_ == 0)
{
lean_ctor_set_tag(v___x_384_, 1);
lean_ctor_set(v___x_384_, 1, v___x_388_);
v___x_390_ = v___x_384_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_fst_381_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v___x_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___boxed(lean_object* v_limits_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows(v_limits_410_, v_a_411_);
lean_dec_ref(v_limits_410_);
return v_res_412_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0(void){
_start:
{
uint32_t v___x_413_; uint8_t v___x_414_; 
v___x_413_ = 97;
v___x_414_ = lean_uint32_to_uint8(v___x_413_);
return v___x_414_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__1(void){
_start:
{
uint32_t v___x_415_; uint8_t v___x_416_; 
v___x_415_ = 65;
v___x_416_ = lean_uint32_to_uint8(v___x_415_);
return v___x_416_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__2(void){
_start:
{
uint32_t v___x_417_; uint8_t v___x_418_; 
v___x_417_ = 70;
v___x_418_ = lean_uint32_to_uint8(v___x_417_);
return v___x_418_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3(void){
_start:
{
uint32_t v___x_419_; uint8_t v___x_420_; 
v___x_419_ = 48;
v___x_420_ = lean_uint32_to_uint8(v___x_419_);
return v___x_420_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4(void){
_start:
{
uint32_t v___x_421_; uint8_t v___x_422_; 
v___x_421_ = 57;
v___x_422_ = lean_uint32_to_uint8(v___x_421_);
return v___x_422_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__6(void){
_start:
{
uint32_t v___x_424_; uint8_t v___x_425_; 
v___x_424_ = 102;
v___x_425_ = lean_uint32_to_uint8(v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit(lean_object* v_a_426_){
_start:
{
lean_object* v_array_427_; lean_object* v_idx_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v_array_427_ = lean_ctor_get(v_a_426_, 0);
v_idx_428_ = lean_ctor_get(v_a_426_, 1);
v___x_429_ = lean_byte_array_size(v_array_427_);
v___x_430_ = lean_nat_dec_lt(v_idx_428_, v___x_429_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = lean_box(0);
v___x_432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_432_, 0, v_a_426_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
return v___x_432_;
}
else
{
lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_495_; 
lean_inc(v_idx_428_);
lean_inc_ref(v_array_427_);
v_isSharedCheck_495_ = !lean_is_exclusive(v_a_426_);
if (v_isSharedCheck_495_ == 0)
{
lean_object* v_unused_496_; lean_object* v_unused_497_; 
v_unused_496_ = lean_ctor_get(v_a_426_, 1);
lean_dec(v_unused_496_);
v_unused_497_ = lean_ctor_get(v_a_426_, 0);
lean_dec(v_unused_497_);
v___x_434_ = v_a_426_;
v_isShared_435_ = v_isSharedCheck_495_;
goto v_resetjp_433_;
}
else
{
lean_dec(v_a_426_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_495_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
uint8_t v_c_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v_it_x27_440_; 
v_c_436_ = lean_byte_array_fget(v_array_427_, v_idx_428_);
v___x_437_ = lean_unsigned_to_nat(1u);
v___x_438_ = lean_nat_add(v_idx_428_, v___x_437_);
lean_dec(v_idx_428_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v___x_438_);
v_it_x27_440_ = v___x_434_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_array_427_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v___x_438_);
v_it_x27_440_ = v_reuseFailAlloc_494_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
uint8_t v___y_442_; uint8_t v___y_443_; uint8_t v___y_456_; uint8_t v___y_457_; uint8_t v___y_471_; uint8_t v___y_479_; uint8_t v___y_485_; uint8_t v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3);
v___x_491_ = lean_uint8_dec_le(v___x_490_, v_c_436_);
if (v___x_491_ == 0)
{
v___y_485_ = v___x_491_;
goto v___jp_484_;
}
else
{
uint8_t v___x_492_; uint8_t v___x_493_; 
v___x_492_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4);
v___x_493_ = lean_uint8_dec_le(v_c_436_, v___x_492_);
v___y_485_ = v___x_493_;
goto v___jp_484_;
}
v___jp_441_:
{
if (v___y_443_ == 0)
{
uint8_t v___x_444_; uint8_t v___x_445_; uint8_t v___x_446_; uint8_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_444_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0);
v___x_445_ = lean_uint8_sub(v_c_436_, v___x_444_);
v___x_446_ = 10;
v___x_447_ = lean_uint8_add(v___x_445_, v___x_446_);
v___x_448_ = lean_box(v___x_447_);
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v_it_x27_440_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
return v___x_449_;
}
else
{
uint8_t v___x_450_; uint8_t v___x_451_; uint8_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_450_ = lean_uint8_sub(v_c_436_, v___y_442_);
v___x_451_ = 10;
v___x_452_ = lean_uint8_add(v___x_450_, v___x_451_);
v___x_453_ = lean_box(v___x_452_);
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v_it_x27_440_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
return v___x_454_;
}
}
v___jp_455_:
{
if (v___y_457_ == 0)
{
uint8_t v___x_458_; uint8_t v___x_459_; 
v___x_458_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__1);
v___x_459_ = lean_uint8_dec_le(v___x_458_, v_c_436_);
if (v___x_459_ == 0)
{
v___y_442_ = v___x_458_;
v___y_443_ = v___x_459_;
goto v___jp_441_;
}
else
{
uint8_t v___x_460_; uint8_t v___x_461_; 
v___x_460_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__2);
v___x_461_ = lean_uint8_dec_le(v_c_436_, v___x_460_);
v___y_442_ = v___x_458_;
v___y_443_ = v___x_461_;
goto v___jp_441_;
}
}
else
{
uint8_t v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_462_ = lean_uint8_sub(v_c_436_, v___y_456_);
v___x_463_ = lean_box(v___x_462_);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v_it_x27_440_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
return v___x_464_;
}
}
v___jp_465_:
{
uint8_t v___x_466_; uint8_t v___x_467_; 
v___x_466_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3);
v___x_467_ = lean_uint8_dec_le(v___x_466_, v_c_436_);
if (v___x_467_ == 0)
{
v___y_456_ = v___x_466_;
v___y_457_ = v___x_467_;
goto v___jp_455_;
}
else
{
uint8_t v___x_468_; uint8_t v___x_469_; 
v___x_468_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4);
v___x_469_ = lean_uint8_dec_le(v_c_436_, v___x_468_);
v___y_456_ = v___x_466_;
v___y_457_ = v___x_469_;
goto v___jp_455_;
}
}
v___jp_470_:
{
if (v___y_471_ == 0)
{
lean_object* v___x_472_; uint32_t v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_472_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__5));
v___x_473_ = lean_uint8_to_uint32(v_c_436_);
v___x_474_ = l_Char_quote(v___x_473_);
v___x_475_ = lean_string_append(v___x_472_, v___x_474_);
lean_dec_ref(v___x_474_);
v___x_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
v___x_477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_477_, 0, v_it_x27_440_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
return v___x_477_;
}
else
{
goto v___jp_465_;
}
}
v___jp_478_:
{
if (v___y_479_ == 0)
{
uint8_t v___x_480_; uint8_t v___x_481_; 
v___x_480_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__1);
v___x_481_ = lean_uint8_dec_le(v___x_480_, v_c_436_);
if (v___x_481_ == 0)
{
v___y_471_ = v___x_481_;
goto v___jp_470_;
}
else
{
uint8_t v___x_482_; uint8_t v___x_483_; 
v___x_482_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__2);
v___x_483_ = lean_uint8_dec_le(v_c_436_, v___x_482_);
v___y_471_ = v___x_483_;
goto v___jp_470_;
}
}
else
{
goto v___jp_465_;
}
}
v___jp_484_:
{
if (v___y_485_ == 0)
{
uint8_t v___x_486_; uint8_t v___x_487_; 
v___x_486_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0);
v___x_487_ = lean_uint8_dec_le(v___x_486_, v_c_436_);
if (v___x_487_ == 0)
{
v___y_479_ = v___x_487_;
goto v___jp_478_;
}
else
{
uint8_t v___x_488_; uint8_t v___x_489_; 
v___x_488_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__6, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__6_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__6);
v___x_489_ = lean_uint8_dec_le(v_c_436_, v___x_488_);
v___y_479_ = v___x_489_;
goto v___jp_478_;
}
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
lean_dec_ref(v___x_537_);
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
lean_dec_ref(v___x_537_);
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
lean_object* v_pos_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_647_; 
v_pos_586_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_647_ == 0)
{
lean_object* v_unused_648_; 
v_unused_648_ = lean_ctor_get(v___x_585_, 1);
lean_dec(v_unused_648_);
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_647_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_pos_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_647_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v_array_595_; lean_object* v_idx_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v_array_595_ = lean_ctor_get(v_pos_586_, 0);
v_idx_596_ = lean_ctor_get(v_pos_586_, 1);
v___x_597_ = lean_byte_array_size(v_array_595_);
v___x_598_ = lean_nat_dec_lt(v_idx_596_, v___x_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; 
lean_del_object(v___x_588_);
v___x_599_ = lean_box(0);
v___x_600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_600_, 0, v_pos_586_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
return v___x_600_;
}
else
{
uint8_t v_c_601_; uint8_t v___x_602_; uint8_t v___x_603_; 
v_c_601_ = lean_byte_array_fget(v_array_595_, v_idx_596_);
v___x_602_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3);
v___x_603_ = lean_uint8_dec_le(v___x_602_, v_c_601_);
if (v___x_603_ == 0)
{
goto v___jp_590_;
}
else
{
uint8_t v___x_604_; uint8_t v___x_605_; 
v___x_604_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4);
v___x_605_ = lean_uint8_dec_le(v_c_601_, v___x_604_);
if (v___x_605_ == 0)
{
goto v___jp_590_;
}
else
{
lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_644_; 
lean_inc(v_idx_596_);
lean_inc_ref(v_array_595_);
lean_del_object(v___x_588_);
v_isSharedCheck_644_ = !lean_is_exclusive(v_pos_586_);
if (v_isSharedCheck_644_ == 0)
{
lean_object* v_unused_645_; lean_object* v_unused_646_; 
v_unused_645_ = lean_ctor_get(v_pos_586_, 1);
lean_dec(v_unused_645_);
v_unused_646_ = lean_ctor_get(v_pos_586_, 0);
lean_dec(v_unused_646_);
v___x_607_ = v_pos_586_;
v_isShared_608_ = v_isSharedCheck_644_;
goto v_resetjp_606_;
}
else
{
lean_dec(v_pos_586_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_644_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v_it_x27_612_; 
v___x_609_ = lean_unsigned_to_nat(1u);
v___x_610_ = lean_nat_add(v_idx_596_, v___x_609_);
lean_dec(v_idx_596_);
lean_inc(v___x_610_);
lean_inc_ref(v_array_595_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v___x_610_);
v_it_x27_612_ = v___x_607_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_array_595_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v___x_610_);
v_it_x27_612_ = v_reuseFailAlloc_643_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
uint8_t v___x_613_; 
v___x_613_ = lean_nat_dec_lt(v___x_610_, v___x_597_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; lean_object* v___x_615_; 
lean_dec(v___x_610_);
lean_dec_ref(v_array_595_);
v___x_614_ = lean_box(0);
v___x_615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_615_, 0, v_it_x27_612_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
return v___x_615_;
}
else
{
uint8_t v___x_616_; uint8_t v_got_617_; uint8_t v___x_618_; 
v___x_616_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4);
v_got_617_ = lean_byte_array_fget(v_array_595_, v___x_610_);
v___x_618_ = lean_uint8_dec_eq(v_got_617_, v___x_616_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; lean_object* v___x_620_; 
lean_dec(v___x_610_);
lean_dec_ref(v_array_595_);
v___x_619_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__9, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__9_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__9);
v___x_620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_620_, 0, v_it_x27_612_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
return v___x_620_;
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_626_; 
lean_dec_ref(v_it_x27_612_);
v___x_621_ = lean_nat_add(v___x_610_, v___x_609_);
lean_dec(v___x_610_);
lean_inc(v___x_621_);
lean_inc_ref(v_array_595_);
v___x_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_622_, 0, v_array_595_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_626_ = lean_nat_dec_lt(v___x_621_, v___x_597_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; 
lean_dec(v___x_621_);
lean_dec_ref(v_array_595_);
v___x_627_ = lean_box(0);
v___x_628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_622_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
return v___x_628_;
}
else
{
uint8_t v_c_629_; uint8_t v___x_630_; 
v_c_629_ = lean_byte_array_fget(v_array_595_, v___x_621_);
v___x_630_ = lean_uint8_dec_le(v___x_602_, v_c_629_);
if (v___x_630_ == 0)
{
lean_dec(v___x_621_);
lean_dec_ref(v_array_595_);
goto v___jp_623_;
}
else
{
uint8_t v___x_631_; 
v___x_631_ = lean_uint8_dec_le(v_c_629_, v___x_604_);
if (v___x_631_ == 0)
{
lean_dec(v___x_621_);
lean_dec_ref(v_array_595_);
goto v___jp_623_;
}
else
{
uint32_t v___x_632_; lean_object* v___x_633_; lean_object* v_it_x27_634_; uint32_t v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
lean_dec_ref(v___x_622_);
v___x_632_ = lean_uint8_to_uint32(v_c_601_);
v___x_633_ = lean_nat_add(v___x_621_, v___x_609_);
lean_dec(v___x_621_);
v_it_x27_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_634_, 0, v_array_595_);
lean_ctor_set(v_it_x27_634_, 1, v___x_633_);
v___x_635_ = lean_uint8_to_uint32(v_c_629_);
v___x_636_ = lean_uint32_to_nat(v___x_632_);
v___x_637_ = lean_unsigned_to_nat(48u);
v___x_638_ = lean_nat_sub(v___x_636_, v___x_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_uint32_to_nat(v___x_635_);
v___x_640_ = lean_nat_sub(v___x_639_, v___x_637_);
lean_dec(v___x_639_);
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_638_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v_it_x27_634_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
return v___x_642_;
}
}
}
v___jp_623_:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_622_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
return v___x_625_;
}
}
}
}
}
}
}
}
v___jp_590_:
{
lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_591_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
if (v_isShared_589_ == 0)
{
lean_ctor_set_tag(v___x_588_, 1);
lean_ctor_set(v___x_588_, 1, v___x_591_);
v___x_593_ = v___x_588_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_pos_586_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
else
{
lean_object* v_pos_649_; lean_object* v_err_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
v_pos_649_ = lean_ctor_get(v___x_585_, 0);
v_err_650_ = lean_ctor_get(v___x_585_, 1);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_585_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_err_650_);
lean_inc(v_pos_649_);
lean_dec(v___x_585_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_pos_649_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_err_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersion(lean_object* v_a_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_658_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_res_660_; lean_object* v_pos_661_; lean_object* v_fst_662_; lean_object* v_snd_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_res_660_ = lean_ctor_get(v___x_659_, 1);
lean_inc(v_res_660_);
v_pos_661_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_pos_661_);
lean_dec_ref(v___x_659_);
v_fst_662_ = lean_ctor_get(v_res_660_, 0);
lean_inc(v_fst_662_);
v_snd_663_ = lean_ctor_get(v_res_660_, 1);
lean_inc(v_snd_663_);
lean_dec(v_res_660_);
v___x_664_ = l_Std_Http_Version_ofNumber_x3f(v_fst_662_, v_snd_663_);
lean_dec(v_snd_663_);
lean_dec(v_fst_662_);
v___x_665_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_664_, v_pos_661_);
lean_dec(v___x_664_);
return v___x_665_;
}
else
{
lean_object* v_pos_666_; lean_object* v_err_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
v_pos_666_ = lean_ctor_get(v___x_659_, 0);
v_err_667_ = lean_ctor_get(v___x_659_, 1);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_659_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_err_667_);
lean_inc(v_pos_666_);
lean_dec(v___x_659_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_pos_666_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_err_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(lean_object* v_a_675_, lean_object* v_f_676_, lean_object* v___y_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = lean_apply_1(v_a_675_, v___y_677_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_pos_679_; lean_object* v_res_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_688_; 
v_pos_679_ = lean_ctor_get(v___x_678_, 0);
v_res_680_ = lean_ctor_get(v___x_678_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_688_ == 0)
{
v___x_682_ = v___x_678_;
v_isShared_683_ = v_isSharedCheck_688_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_res_680_);
lean_inc(v_pos_679_);
lean_dec(v___x_678_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_688_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_684_ = lean_apply_1(v_f_676_, v_res_680_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v___x_684_);
v___x_686_ = v___x_682_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_pos_679_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
else
{
lean_object* v_pos_689_; lean_object* v_err_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec(v_f_676_);
v_pos_689_ = lean_ctor_get(v___x_678_, 0);
v_err_690_ = lean_ctor_get(v___x_678_, 1);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_678_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_err_690_);
lean_inc(v_pos_689_);
lean_dec(v___x_678_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_pos_689_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_err_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0(lean_object* v_00_u03b1_698_, lean_object* v_00_u03b2_699_, lean_object* v_a_700_, lean_object* v_f_701_, lean_object* v___y_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v_a_700_, v_f_701_, v___y_702_);
return v___x_703_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0(lean_object* v_x_704_){
_start:
{
uint8_t v___x_705_; 
v___x_705_ = 9;
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0___boxed(lean_object* v_x_706_){
_start:
{
uint8_t v_res_707_; lean_object* v_r_708_; 
v_res_707_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0(v_x_706_);
v_r_708_ = lean_box(v_res_707_);
return v_r_708_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1(lean_object* v_x_709_){
_start:
{
uint8_t v___x_710_; 
v___x_710_ = 32;
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1___boxed(lean_object* v_x_711_){
_start:
{
uint8_t v_res_712_; lean_object* v_r_713_; 
v_res_712_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1(v_x_711_);
v_r_713_ = lean_box(v_res_712_);
return v_r_713_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2(lean_object* v_x_714_){
_start:
{
uint8_t v___x_715_; 
v___x_715_ = 28;
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2___boxed(lean_object* v_x_716_){
_start:
{
uint8_t v_res_717_; lean_object* v_r_718_; 
v_res_717_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2(v_x_716_);
v_r_718_ = lean_box(v_res_717_);
return v_r_718_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3(lean_object* v_x_719_){
_start:
{
uint8_t v___x_720_; 
v___x_720_ = 1;
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3___boxed(lean_object* v_x_721_){
_start:
{
uint8_t v_res_722_; lean_object* v_r_723_; 
v_res_722_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3(v_x_721_);
v_r_723_ = lean_box(v_res_722_);
return v_r_723_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4(lean_object* v_x_724_){
_start:
{
uint8_t v___x_725_; 
v___x_725_ = 5;
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4___boxed(lean_object* v_x_726_){
_start:
{
uint8_t v_res_727_; lean_object* v_r_728_; 
v_res_727_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4(v_x_726_);
v_r_728_ = lean_box(v_res_727_);
return v_r_728_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5(lean_object* v_x_729_){
_start:
{
uint8_t v___x_730_; 
v___x_730_ = 4;
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5___boxed(lean_object* v_x_731_){
_start:
{
uint8_t v_res_732_; lean_object* v_r_733_; 
v_res_732_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5(v_x_731_);
v_r_733_ = lean_box(v_res_732_);
return v_r_733_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6(lean_object* v_x_734_){
_start:
{
uint8_t v___x_735_; 
v___x_735_ = 10;
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6___boxed(lean_object* v_x_736_){
_start:
{
uint8_t v_res_737_; lean_object* v_r_738_; 
v_res_737_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6(v_x_736_);
v_r_738_ = lean_box(v_res_737_);
return v_r_738_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7(lean_object* v_x_739_){
_start:
{
uint8_t v___x_740_; 
v___x_740_ = 12;
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7___boxed(lean_object* v_x_741_){
_start:
{
uint8_t v_res_742_; lean_object* v_r_743_; 
v_res_742_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7(v_x_741_);
v_r_743_ = lean_box(v_res_742_);
return v_r_743_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8(lean_object* v_x_744_){
_start:
{
uint8_t v___x_745_; 
v___x_745_ = 14;
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8___boxed(lean_object* v_x_746_){
_start:
{
uint8_t v_res_747_; lean_object* v_r_748_; 
v_res_747_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8(v_x_746_);
v_r_748_ = lean_box(v_res_747_);
return v_r_748_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9(lean_object* v_x_749_){
_start:
{
uint8_t v___x_750_; 
v___x_750_ = 16;
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9___boxed(lean_object* v_x_751_){
_start:
{
uint8_t v_res_752_; lean_object* v_r_753_; 
v_res_752_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9(v_x_751_);
v_r_753_ = lean_box(v_res_752_);
return v_r_753_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10(lean_object* v_x_754_){
_start:
{
uint8_t v___x_755_; 
v___x_755_ = 18;
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10___boxed(lean_object* v_x_756_){
_start:
{
uint8_t v_res_757_; lean_object* v_r_758_; 
v_res_757_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10(v_x_756_);
v_r_758_ = lean_box(v_res_757_);
return v_r_758_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11(lean_object* v_x_759_){
_start:
{
uint8_t v___x_760_; 
v___x_760_ = 20;
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11___boxed(lean_object* v_x_761_){
_start:
{
uint8_t v_res_762_; lean_object* v_r_763_; 
v_res_762_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11(v_x_761_);
v_r_763_ = lean_box(v_res_762_);
return v_r_763_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12(lean_object* v_x_764_){
_start:
{
uint8_t v___x_765_; 
v___x_765_ = 23;
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12___boxed(lean_object* v_x_766_){
_start:
{
uint8_t v_res_767_; lean_object* v_r_768_; 
v_res_767_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12(v_x_766_);
v_r_768_ = lean_box(v_res_767_);
return v_r_768_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13(lean_object* v_x_769_){
_start:
{
uint8_t v___x_770_; 
v___x_770_ = 22;
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13___boxed(lean_object* v_x_771_){
_start:
{
uint8_t v_res_772_; lean_object* v_r_773_; 
v_res_772_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13(v_x_771_);
v_r_773_ = lean_box(v_res_772_);
return v_r_773_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14(lean_object* v_x_774_){
_start:
{
uint8_t v___x_775_; 
v___x_775_ = 25;
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14___boxed(lean_object* v_x_776_){
_start:
{
uint8_t v_res_777_; lean_object* v_r_778_; 
v_res_777_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14(v_x_776_);
v_r_778_ = lean_box(v_res_777_);
return v_r_778_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15(lean_object* v_x_779_){
_start:
{
uint8_t v___x_780_; 
v___x_780_ = 29;
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15___boxed(lean_object* v_x_781_){
_start:
{
uint8_t v_res_782_; lean_object* v_r_783_; 
v_res_782_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15(v_x_781_);
v_r_783_ = lean_box(v_res_782_);
return v_r_783_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16(lean_object* v_x_784_){
_start:
{
uint8_t v___x_785_; 
v___x_785_ = 33;
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16___boxed(lean_object* v_x_786_){
_start:
{
uint8_t v_res_787_; lean_object* v_r_788_; 
v_res_787_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16(v_x_786_);
v_r_788_ = lean_box(v_res_787_);
return v_r_788_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17(lean_object* v_x_789_){
_start:
{
uint8_t v___x_790_; 
v___x_790_ = 35;
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17___boxed(lean_object* v_x_791_){
_start:
{
uint8_t v_res_792_; lean_object* v_r_793_; 
v_res_792_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17(v_x_791_);
v_r_793_ = lean_box(v_res_792_);
return v_r_793_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18(lean_object* v_x_794_){
_start:
{
uint8_t v___x_795_; 
v___x_795_ = 38;
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18___boxed(lean_object* v_x_796_){
_start:
{
uint8_t v_res_797_; lean_object* v_r_798_; 
v_res_797_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18(v_x_796_);
v_r_798_ = lean_box(v_res_797_);
return v_r_798_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19(lean_object* v_x_799_){
_start:
{
uint8_t v___x_800_; 
v___x_800_ = 39;
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19___boxed(lean_object* v_x_801_){
_start:
{
uint8_t v_res_802_; lean_object* v_r_803_; 
v_res_802_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19(v_x_801_);
v_r_803_ = lean_box(v_res_802_);
return v_r_803_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21(lean_object* v_x_804_){
_start:
{
uint8_t v___x_805_; 
v___x_805_ = 37;
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21___boxed(lean_object* v_x_806_){
_start:
{
uint8_t v_res_807_; lean_object* v_r_808_; 
v_res_807_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21(v_x_806_);
v_r_808_ = lean_box(v_res_807_);
return v_r_808_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20(lean_object* v_x_809_){
_start:
{
uint8_t v___x_810_; 
v___x_810_ = 36;
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20___boxed(lean_object* v_x_811_){
_start:
{
uint8_t v_res_812_; lean_object* v_r_813_; 
v_res_812_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20(v_x_811_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22(lean_object* v_x_814_){
_start:
{
uint8_t v___x_815_; 
v___x_815_ = 34;
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22___boxed(lean_object* v_x_816_){
_start:
{
uint8_t v_res_817_; lean_object* v_r_818_; 
v_res_817_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22(v_x_816_);
v_r_818_ = lean_box(v_res_817_);
return v_r_818_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23(lean_object* v_x_819_){
_start:
{
uint8_t v___x_820_; 
v___x_820_ = 30;
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23___boxed(lean_object* v_x_821_){
_start:
{
uint8_t v_res_822_; lean_object* v_r_823_; 
v_res_822_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23(v_x_821_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24(lean_object* v_x_824_){
_start:
{
uint8_t v___x_825_; 
v___x_825_ = 26;
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24___boxed(lean_object* v_x_826_){
_start:
{
uint8_t v_res_827_; lean_object* v_r_828_; 
v_res_827_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24(v_x_826_);
v_r_828_ = lean_box(v_res_827_);
return v_r_828_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25(lean_object* v_x_829_){
_start:
{
uint8_t v___x_830_; 
v___x_830_ = 24;
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25___boxed(lean_object* v_x_831_){
_start:
{
uint8_t v_res_832_; lean_object* v_r_833_; 
v_res_832_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25(v_x_831_);
v_r_833_ = lean_box(v_res_832_);
return v_r_833_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26(lean_object* v_x_834_){
_start:
{
uint8_t v___x_835_; 
v___x_835_ = 27;
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26___boxed(lean_object* v_x_836_){
_start:
{
uint8_t v_res_837_; lean_object* v_r_838_; 
v_res_837_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26(v_x_836_);
v_r_838_ = lean_box(v_res_837_);
return v_r_838_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27(lean_object* v_x_839_){
_start:
{
uint8_t v___x_840_; 
v___x_840_ = 21;
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27___boxed(lean_object* v_x_841_){
_start:
{
uint8_t v_res_842_; lean_object* v_r_843_; 
v_res_842_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27(v_x_841_);
v_r_843_ = lean_box(v_res_842_);
return v_r_843_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28(lean_object* v_x_844_){
_start:
{
uint8_t v___x_845_; 
v___x_845_ = 19;
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28___boxed(lean_object* v_x_846_){
_start:
{
uint8_t v_res_847_; lean_object* v_r_848_; 
v_res_847_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28(v_x_846_);
v_r_848_ = lean_box(v_res_847_);
return v_r_848_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29(lean_object* v_x_849_){
_start:
{
uint8_t v___x_850_; 
v___x_850_ = 17;
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29___boxed(lean_object* v_x_851_){
_start:
{
uint8_t v_res_852_; lean_object* v_r_853_; 
v_res_852_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29(v_x_851_);
v_r_853_ = lean_box(v_res_852_);
return v_r_853_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30(lean_object* v_x_854_){
_start:
{
uint8_t v___x_855_; 
v___x_855_ = 15;
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30___boxed(lean_object* v_x_856_){
_start:
{
uint8_t v_res_857_; lean_object* v_r_858_; 
v_res_857_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30(v_x_856_);
v_r_858_ = lean_box(v_res_857_);
return v_r_858_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31(lean_object* v_x_859_){
_start:
{
uint8_t v___x_860_; 
v___x_860_ = 13;
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31___boxed(lean_object* v_x_861_){
_start:
{
uint8_t v_res_862_; lean_object* v_r_863_; 
v_res_862_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31(v_x_861_);
v_r_863_ = lean_box(v_res_862_);
return v_r_863_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32(lean_object* v_x_864_){
_start:
{
uint8_t v___x_865_; 
v___x_865_ = 11;
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32___boxed(lean_object* v_x_866_){
_start:
{
uint8_t v_res_867_; lean_object* v_r_868_; 
v_res_867_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32(v_x_866_);
v_r_868_ = lean_box(v_res_867_);
return v_r_868_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33(lean_object* v_x_869_){
_start:
{
uint8_t v___x_870_; 
v___x_870_ = 6;
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33___boxed(lean_object* v_x_871_){
_start:
{
uint8_t v_res_872_; lean_object* v_r_873_; 
v_res_872_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33(v_x_871_);
v_r_873_ = lean_box(v_res_872_);
return v_r_873_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34(lean_object* v_x_874_){
_start:
{
uint8_t v___x_875_; 
v___x_875_ = 3;
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34___boxed(lean_object* v_x_876_){
_start:
{
uint8_t v_res_877_; lean_object* v_r_878_; 
v_res_877_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34(v_x_876_);
v_r_878_ = lean_box(v_res_877_);
return v_r_878_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35(lean_object* v_x_879_){
_start:
{
uint8_t v___x_880_; 
v___x_880_ = 2;
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35___boxed(lean_object* v_x_881_){
_start:
{
uint8_t v_res_882_; lean_object* v_r_883_; 
v_res_882_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35(v_x_881_);
v_r_883_ = lean_box(v_res_882_);
return v_r_883_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36(lean_object* v_x_884_){
_start:
{
uint8_t v___x_885_; 
v___x_885_ = 31;
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36___boxed(lean_object* v_x_886_){
_start:
{
uint8_t v_res_887_; lean_object* v_r_888_; 
v_res_887_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36(v_x_886_);
v_r_888_ = lean_box(v_res_887_);
return v_r_888_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37(lean_object* v_x_889_){
_start:
{
uint8_t v___x_890_; 
v___x_890_ = 0;
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37___boxed(lean_object* v_x_891_){
_start:
{
uint8_t v_res_892_; lean_object* v_r_893_; 
v_res_892_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37(v_x_891_);
v_r_893_ = lean_box(v_res_892_);
return v_r_893_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38(lean_object* v_x_894_){
_start:
{
uint8_t v___x_895_; 
v___x_895_ = 7;
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38___boxed(lean_object* v_x_896_){
_start:
{
uint8_t v_res_897_; lean_object* v_r_898_; 
v_res_897_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38(v_x_896_);
v_r_898_ = lean_box(v_res_897_);
return v_r_898_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39(lean_object* v_x_899_){
_start:
{
uint8_t v___x_900_; 
v___x_900_ = 8;
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39___boxed(lean_object* v_x_901_){
_start:
{
uint8_t v_res_902_; lean_object* v_r_903_; 
v_res_902_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39(v_x_901_);
v_r_903_ = lean_box(v_res_902_);
return v_r_903_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22));
v___x_929_ = lean_string_to_utf8(v___x_928_);
return v___x_929_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23);
v___x_931_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_931_, 0, v___x_930_);
return v___x_931_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26));
v___x_935_ = lean_string_to_utf8(v___x_934_);
return v___x_935_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27);
v___x_937_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_937_, 0, v___x_936_);
return v___x_937_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__29));
v___x_940_ = lean_string_to_utf8(v___x_939_);
return v___x_940_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30);
v___x_942_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_942_, 0, v___x_941_);
return v___x_942_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__33));
v___x_946_ = lean_string_to_utf8(v___x_945_);
return v___x_946_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34);
v___x_948_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_948_, 0, v___x_947_);
return v___x_948_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__36));
v___x_951_ = lean_string_to_utf8(v___x_950_);
return v___x_951_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37);
v___x_953_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__40));
v___x_957_ = lean_string_to_utf8(v___x_956_);
return v___x_957_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41);
v___x_959_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43));
v___x_962_ = lean_string_to_utf8(v___x_961_);
return v___x_962_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44);
v___x_964_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47));
v___x_968_ = lean_string_to_utf8(v___x_967_);
return v___x_968_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48);
v___x_970_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_970_, 0, v___x_969_);
return v___x_970_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50));
v___x_973_ = lean_string_to_utf8(v___x_972_);
return v___x_973_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51);
v___x_975_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54));
v___x_979_ = lean_string_to_utf8(v___x_978_);
return v___x_979_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55);
v___x_981_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_981_, 0, v___x_980_);
return v___x_981_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__57));
v___x_984_ = lean_string_to_utf8(v___x_983_);
return v___x_984_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59(void){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58);
v___x_986_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_986_, 0, v___x_985_);
return v___x_986_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__61));
v___x_990_ = lean_string_to_utf8(v___x_989_);
return v___x_990_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62);
v___x_992_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_992_, 0, v___x_991_);
return v___x_992_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__64));
v___x_995_ = lean_string_to_utf8(v___x_994_);
return v___x_995_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65);
v___x_997_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_997_, 0, v___x_996_);
return v___x_997_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__68));
v___x_1001_ = lean_string_to_utf8(v___x_1000_);
return v___x_1001_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69);
v___x_1003_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1003_, 0, v___x_1002_);
return v___x_1003_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71));
v___x_1006_ = lean_string_to_utf8(v___x_1005_);
return v___x_1006_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72);
v___x_1008_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1008_, 0, v___x_1007_);
return v___x_1008_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75));
v___x_1012_ = lean_string_to_utf8(v___x_1011_);
return v___x_1012_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76);
v___x_1014_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1014_, 0, v___x_1013_);
return v___x_1014_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78));
v___x_1017_ = lean_string_to_utf8(v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79);
v___x_1019_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1019_, 0, v___x_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82));
v___x_1023_ = lean_string_to_utf8(v___x_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83);
v___x_1025_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1025_, 0, v___x_1024_);
return v___x_1025_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__85));
v___x_1028_ = lean_string_to_utf8(v___x_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86);
v___x_1030_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1030_, 0, v___x_1029_);
return v___x_1030_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__89));
v___x_1034_ = lean_string_to_utf8(v___x_1033_);
return v___x_1034_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90);
v___x_1036_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1036_, 0, v___x_1035_);
return v___x_1036_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__92));
v___x_1039_ = lean_string_to_utf8(v___x_1038_);
return v___x_1039_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93);
v___x_1041_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1041_, 0, v___x_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__96));
v___x_1045_ = lean_string_to_utf8(v___x_1044_);
return v___x_1045_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97);
v___x_1047_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1047_, 0, v___x_1046_);
return v___x_1047_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99));
v___x_1050_ = lean_string_to_utf8(v___x_1049_);
return v___x_1050_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100);
v___x_1052_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1052_, 0, v___x_1051_);
return v___x_1052_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103));
v___x_1056_ = lean_string_to_utf8(v___x_1055_);
return v___x_1056_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104);
v___x_1058_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1058_, 0, v___x_1057_);
return v___x_1058_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106));
v___x_1061_ = lean_string_to_utf8(v___x_1060_);
return v___x_1061_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107);
v___x_1063_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110));
v___x_1067_ = lean_string_to_utf8(v___x_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111);
v___x_1069_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1069_, 0, v___x_1068_);
return v___x_1069_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__113));
v___x_1072_ = lean_string_to_utf8(v___x_1071_);
return v___x_1072_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114);
v___x_1074_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1074_, 0, v___x_1073_);
return v___x_1074_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__117));
v___x_1078_ = lean_string_to_utf8(v___x_1077_);
return v___x_1078_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118);
v___x_1080_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1080_, 0, v___x_1079_);
return v___x_1080_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__120));
v___x_1083_ = lean_string_to_utf8(v___x_1082_);
return v___x_1083_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121);
v___x_1085_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1085_, 0, v___x_1084_);
return v___x_1085_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__124));
v___x_1089_ = lean_string_to_utf8(v___x_1088_);
return v___x_1089_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125);
v___x_1091_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1091_, 0, v___x_1090_);
return v___x_1091_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127));
v___x_1094_ = lean_string_to_utf8(v___x_1093_);
return v___x_1094_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128);
v___x_1096_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1096_, 0, v___x_1095_);
return v___x_1096_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131));
v___x_1100_ = lean_string_to_utf8(v___x_1099_);
return v___x_1100_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132);
v___x_1102_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134));
v___x_1105_ = lean_string_to_utf8(v___x_1104_);
return v___x_1105_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135);
v___x_1107_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1107_, 0, v___x_1106_);
return v___x_1107_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138));
v___x_1111_ = lean_string_to_utf8(v___x_1110_);
return v___x_1111_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139);
v___x_1113_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1113_, 0, v___x_1112_);
return v___x_1113_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__141));
v___x_1116_ = lean_string_to_utf8(v___x_1115_);
return v___x_1116_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142);
v___x_1118_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1118_, 0, v___x_1117_);
return v___x_1118_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__145));
v___x_1122_ = lean_string_to_utf8(v___x_1121_);
return v___x_1122_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146);
v___x_1124_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1124_, 0, v___x_1123_);
return v___x_1124_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__148));
v___x_1127_ = lean_string_to_utf8(v___x_1126_);
return v___x_1127_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149);
v___x_1129_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1129_, 0, v___x_1128_);
return v___x_1129_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__152));
v___x_1133_ = lean_string_to_utf8(v___x_1132_);
return v___x_1133_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153);
v___x_1135_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1135_, 0, v___x_1134_);
return v___x_1135_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155));
v___x_1138_ = lean_string_to_utf8(v___x_1137_);
return v___x_1138_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156);
v___x_1140_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1140_, 0, v___x_1139_);
return v___x_1140_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159));
v___x_1144_ = lean_string_to_utf8(v___x_1143_);
return v___x_1144_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160);
v___x_1146_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1146_, 0, v___x_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(lean_object* v_a_1147_){
_start:
{
lean_object* v___f_1148_; lean_object* v___f_1149_; lean_object* v___f_1150_; lean_object* v___f_1151_; lean_object* v___f_1152_; lean_object* v___f_1153_; lean_object* v___f_1154_; lean_object* v___f_1155_; lean_object* v___f_1156_; lean_object* v___f_1157_; lean_object* v___f_1158_; lean_object* v___f_1159_; lean_object* v___f_1160_; lean_object* v___f_1161_; lean_object* v___f_1162_; lean_object* v___f_1163_; lean_object* v___f_1164_; lean_object* v___f_1165_; lean_object* v___f_1166_; lean_object* v___f_1167_; lean_object* v___f_1168_; lean_object* v_idx_1170_; lean_object* v___y_1171_; lean_object* v_pos_1172_; lean_object* v_idx_1173_; lean_object* v_idx_1208_; lean_object* v___y_1209_; lean_object* v_pos_1210_; lean_object* v_idx_1211_; lean_object* v___f_1226_; lean_object* v_idx_1228_; lean_object* v___y_1229_; lean_object* v_pos_1230_; lean_object* v_idx_1231_; lean_object* v_idx_1247_; lean_object* v___y_1248_; lean_object* v_pos_1249_; lean_object* v_idx_1250_; lean_object* v___f_1265_; lean_object* v_idx_1267_; lean_object* v___y_1268_; lean_object* v_pos_1269_; lean_object* v_idx_1270_; lean_object* v_idx_1286_; lean_object* v___y_1287_; lean_object* v_pos_1288_; lean_object* v_idx_1289_; lean_object* v___f_1304_; lean_object* v_idx_1306_; lean_object* v___y_1307_; lean_object* v_pos_1308_; lean_object* v_idx_1309_; lean_object* v_idx_1325_; lean_object* v___y_1326_; lean_object* v_pos_1327_; lean_object* v_idx_1328_; lean_object* v___f_1343_; lean_object* v_idx_1345_; lean_object* v___y_1346_; lean_object* v_pos_1347_; lean_object* v_idx_1348_; lean_object* v_idx_1364_; lean_object* v___y_1365_; lean_object* v_pos_1366_; lean_object* v_idx_1367_; lean_object* v___f_1382_; lean_object* v_idx_1384_; lean_object* v___y_1385_; lean_object* v_pos_1386_; lean_object* v_idx_1387_; lean_object* v_idx_1403_; lean_object* v___y_1404_; lean_object* v_pos_1405_; lean_object* v_idx_1406_; lean_object* v___f_1421_; lean_object* v_idx_1423_; lean_object* v___y_1424_; lean_object* v_pos_1425_; lean_object* v_idx_1426_; lean_object* v_idx_1442_; lean_object* v___y_1443_; lean_object* v_pos_1444_; lean_object* v_idx_1445_; lean_object* v___f_1460_; lean_object* v_idx_1462_; lean_object* v___y_1463_; lean_object* v_pos_1464_; lean_object* v_idx_1465_; lean_object* v_idx_1481_; lean_object* v___y_1482_; lean_object* v_pos_1483_; lean_object* v_idx_1484_; lean_object* v___f_1499_; lean_object* v_idx_1501_; lean_object* v___y_1502_; lean_object* v_pos_1503_; lean_object* v_idx_1504_; lean_object* v_idx_1520_; lean_object* v___y_1521_; lean_object* v_pos_1522_; lean_object* v_idx_1523_; lean_object* v___f_1538_; lean_object* v_idx_1540_; lean_object* v___y_1541_; lean_object* v_pos_1542_; lean_object* v_idx_1543_; lean_object* v_idx_1559_; lean_object* v___y_1560_; lean_object* v_pos_1561_; lean_object* v_idx_1562_; lean_object* v___f_1577_; lean_object* v_idx_1579_; lean_object* v___y_1580_; lean_object* v_pos_1581_; lean_object* v_idx_1582_; lean_object* v_idx_1598_; lean_object* v___y_1599_; lean_object* v_pos_1600_; lean_object* v_idx_1601_; lean_object* v___f_1616_; lean_object* v_idx_1618_; lean_object* v___y_1619_; lean_object* v_pos_1620_; lean_object* v_idx_1621_; lean_object* v_idx_1637_; lean_object* v___y_1638_; lean_object* v_pos_1639_; lean_object* v_idx_1640_; lean_object* v___f_1655_; lean_object* v_idx_1657_; lean_object* v___y_1658_; lean_object* v_pos_1659_; lean_object* v_idx_1660_; lean_object* v_idx_1676_; lean_object* v___y_1677_; lean_object* v_pos_1678_; lean_object* v_idx_1679_; lean_object* v___f_1694_; lean_object* v_idx_1696_; lean_object* v___y_1697_; lean_object* v_pos_1698_; lean_object* v_idx_1699_; lean_object* v_idx_1715_; lean_object* v___y_1716_; lean_object* v_pos_1717_; lean_object* v_idx_1718_; lean_object* v___f_1733_; lean_object* v_idx_1735_; lean_object* v___y_1736_; lean_object* v_pos_1737_; lean_object* v_idx_1738_; lean_object* v_idx_1754_; lean_object* v___y_1755_; lean_object* v_pos_1756_; lean_object* v_idx_1757_; lean_object* v___f_1772_; lean_object* v_idx_1774_; lean_object* v___y_1775_; lean_object* v_pos_1776_; lean_object* v_idx_1777_; lean_object* v_idx_1793_; lean_object* v___y_1794_; lean_object* v_pos_1795_; lean_object* v_idx_1796_; lean_object* v___f_1811_; lean_object* v_idx_1813_; lean_object* v___y_1814_; lean_object* v_pos_1815_; lean_object* v_idx_1816_; lean_object* v_idx_1832_; lean_object* v___y_1833_; lean_object* v_pos_1834_; lean_object* v_idx_1835_; lean_object* v___f_1850_; lean_object* v_idx_1852_; lean_object* v___y_1853_; lean_object* v_pos_1854_; lean_object* v_idx_1855_; lean_object* v_idx_1871_; lean_object* v___y_1872_; lean_object* v_pos_1873_; lean_object* v_idx_1874_; lean_object* v___f_1889_; lean_object* v_idx_1891_; lean_object* v___y_1892_; lean_object* v_pos_1893_; lean_object* v_idx_1894_; lean_object* v_idx_1910_; lean_object* v___y_1911_; lean_object* v_pos_1912_; lean_object* v_idx_1913_; lean_object* v___f_1928_; lean_object* v_idx_1930_; lean_object* v___y_1931_; lean_object* v_pos_1932_; lean_object* v_idx_1933_; lean_object* v___y_1949_; lean_object* v_pos_1950_; lean_object* v___f_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___f_1148_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__0));
v___f_1149_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__1));
v___f_1150_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2));
v___f_1151_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3));
v___f_1152_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4));
v___f_1153_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__5));
v___f_1154_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6));
v___f_1155_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7));
v___f_1156_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__8));
v___f_1157_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__9));
v___f_1158_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10));
v___f_1159_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11));
v___f_1160_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__12));
v___f_1161_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__13));
v___f_1162_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14));
v___f_1163_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15));
v___f_1164_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__16));
v___f_1165_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__17));
v___f_1166_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18));
v___f_1167_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19));
v___f_1168_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___f_1226_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__25));
v___f_1265_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__32));
v___f_1304_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39));
v___f_1343_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46));
v___f_1382_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__53));
v___f_1421_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__60));
v___f_1460_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67));
v___f_1499_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74));
v___f_1538_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__81));
v___f_1577_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__88));
v___f_1616_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95));
v___f_1655_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102));
v___f_1694_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__109));
v___f_1733_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__116));
v___f_1772_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123));
v___f_1811_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130));
v___f_1850_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__137));
v___f_1889_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__144));
v___f_1928_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151));
v___f_1967_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158));
v___x_1968_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161);
lean_inc_ref(v_a_1147_);
v___x_1969_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1968_, v___f_1967_, v_a_1147_);
if (lean_obj_tag(v___x_1969_) == 0)
{
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_dec_ref(v_a_1147_);
return v___x_1969_;
}
else
{
lean_object* v_pos_1970_; 
v_pos_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_pos_1970_);
v___y_1949_ = v___x_1969_;
v_pos_1950_ = v_pos_1970_;
goto v___jp_1948_;
}
}
else
{
lean_object* v_err_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
v_err_1971_ = lean_ctor_get(v___x_1969_, 1);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1978_ == 0)
{
lean_object* v_unused_1979_; 
v_unused_1979_ = lean_ctor_get(v___x_1969_, 0);
lean_dec(v_unused_1979_);
v___x_1973_ = v___x_1969_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_err_1971_);
lean_dec(v___x_1969_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
lean_inc_ref(v_a_1147_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v_a_1147_);
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1147_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_err_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_inc_ref(v_a_1147_);
v___y_1949_ = v___x_1976_;
v_pos_1950_ = v_a_1147_;
goto v___jp_1948_;
}
}
}
v___jp_1169_:
{
uint8_t v___x_1174_; 
v___x_1174_ = lean_nat_dec_eq(v_idx_1170_, v_idx_1173_);
lean_dec(v_idx_1173_);
lean_dec(v_idx_1170_);
if (v___x_1174_ == 0)
{
lean_dec_ref(v_pos_1172_);
return v___y_1171_;
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v_snd_1178_; lean_object* v_snd_1179_; uint8_t v___x_1180_; 
lean_dec_ref(v___y_1171_);
v___x_1175_ = lean_unsigned_to_nat(64u);
v___x_1176_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pos_1172_);
v___x_1177_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1168_, v___x_1175_, v___x_1176_, v_pos_1172_);
v_snd_1178_ = lean_ctor_get(v___x_1177_, 1);
lean_inc(v_snd_1178_);
v_snd_1179_ = lean_ctor_get(v_snd_1178_, 1);
v___x_1180_ = lean_unbox(v_snd_1179_);
if (v___x_1180_ == 0)
{
lean_object* v_fst_1181_; lean_object* v_fst_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1195_; 
v_fst_1181_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_fst_1181_);
lean_dec_ref(v___x_1177_);
v_fst_1182_ = lean_ctor_get(v_snd_1178_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_snd_1178_);
if (v_isSharedCheck_1195_ == 0)
{
lean_object* v_unused_1196_; 
v_unused_1196_ = lean_ctor_get(v_snd_1178_, 1);
lean_dec(v_unused_1196_);
v___x_1184_ = v_snd_1178_;
v_isShared_1185_ = v_isSharedCheck_1195_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_fst_1182_);
lean_dec(v_snd_1178_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1195_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
uint8_t v___x_1186_; 
v___x_1186_ = lean_nat_dec_eq(v_fst_1181_, v___x_1176_);
lean_dec(v_fst_1181_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; lean_object* v___x_1189_; 
lean_dec_ref(v_pos_1172_);
v___x_1187_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__21));
if (v_isShared_1185_ == 0)
{
lean_ctor_set_tag(v___x_1184_, 1);
lean_ctor_set(v___x_1184_, 1, v___x_1187_);
v___x_1189_ = v___x_1184_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_fst_1182_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
else
{
lean_object* v___x_1191_; lean_object* v___x_1193_; 
lean_dec(v_fst_1182_);
v___x_1191_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_1185_ == 0)
{
lean_ctor_set_tag(v___x_1184_, 1);
lean_ctor_set(v___x_1184_, 1, v___x_1191_);
lean_ctor_set(v___x_1184_, 0, v_pos_1172_);
v___x_1193_ = v___x_1184_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_pos_1172_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
else
{
lean_object* v_fst_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1205_; 
lean_dec_ref(v___x_1177_);
lean_dec_ref(v_pos_1172_);
v_fst_1197_ = lean_ctor_get(v_snd_1178_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_snd_1178_);
if (v_isSharedCheck_1205_ == 0)
{
lean_object* v_unused_1206_; 
v_unused_1206_ = lean_ctor_get(v_snd_1178_, 1);
lean_dec(v_unused_1206_);
v___x_1199_ = v_snd_1178_;
v_isShared_1200_ = v_isSharedCheck_1205_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_fst_1197_);
lean_dec(v_snd_1178_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1205_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1201_ = lean_box(0);
if (v_isShared_1200_ == 0)
{
lean_ctor_set_tag(v___x_1199_, 1);
lean_ctor_set(v___x_1199_, 1, v___x_1201_);
v___x_1203_ = v___x_1199_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_fst_1197_);
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
}
v___jp_1207_:
{
uint8_t v___x_1212_; 
v___x_1212_ = lean_nat_dec_eq(v_idx_1208_, v_idx_1211_);
lean_dec(v_idx_1208_);
if (v___x_1212_ == 0)
{
lean_dec(v_idx_1211_);
lean_dec_ref(v_pos_1210_);
return v___y_1209_;
}
else
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
lean_dec_ref(v___y_1209_);
v___x_1213_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24);
lean_inc_ref(v_pos_1210_);
v___x_1214_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1213_, v___f_1167_, v_pos_1210_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_dec_ref(v_pos_1210_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_dec(v_idx_1211_);
return v___x_1214_;
}
else
{
lean_object* v_pos_1215_; lean_object* v_idx_1216_; 
v_pos_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_pos_1215_);
v_idx_1216_ = lean_ctor_get(v_pos_1215_, 1);
lean_inc(v_idx_1216_);
v_idx_1170_ = v_idx_1211_;
v___y_1171_ = v___x_1214_;
v_pos_1172_ = v_pos_1215_;
v_idx_1173_ = v_idx_1216_;
goto v___jp_1169_;
}
}
else
{
lean_object* v_err_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
v_err_1217_ = lean_ctor_get(v___x_1214_, 1);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; 
v_unused_1225_ = lean_ctor_get(v___x_1214_, 0);
lean_dec(v_unused_1225_);
v___x_1219_ = v___x_1214_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_err_1217_);
lean_dec(v___x_1214_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
lean_inc_ref(v_pos_1210_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v_pos_1210_);
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_pos_1210_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_err_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_inc(v_idx_1211_);
v_idx_1170_ = v_idx_1211_;
v___y_1171_ = v___x_1222_;
v_pos_1172_ = v_pos_1210_;
v_idx_1173_ = v_idx_1211_;
goto v___jp_1169_;
}
}
}
}
}
v___jp_1227_:
{
uint8_t v___x_1232_; 
v___x_1232_ = lean_nat_dec_eq(v_idx_1228_, v_idx_1231_);
lean_dec(v_idx_1228_);
if (v___x_1232_ == 0)
{
lean_dec(v_idx_1231_);
lean_dec_ref(v_pos_1230_);
return v___y_1229_;
}
else
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_dec_ref(v___y_1229_);
v___x_1233_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28);
lean_inc_ref(v_pos_1230_);
v___x_1234_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1233_, v___f_1226_, v_pos_1230_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_dec_ref(v_pos_1230_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_dec(v_idx_1231_);
return v___x_1234_;
}
else
{
lean_object* v_pos_1235_; lean_object* v_idx_1236_; 
v_pos_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_pos_1235_);
v_idx_1236_ = lean_ctor_get(v_pos_1235_, 1);
lean_inc(v_idx_1236_);
v_idx_1208_ = v_idx_1231_;
v___y_1209_ = v___x_1234_;
v_pos_1210_ = v_pos_1235_;
v_idx_1211_ = v_idx_1236_;
goto v___jp_1207_;
}
}
else
{
lean_object* v_err_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
v_err_1237_ = lean_ctor_get(v___x_1234_, 1);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1244_ == 0)
{
lean_object* v_unused_1245_; 
v_unused_1245_ = lean_ctor_get(v___x_1234_, 0);
lean_dec(v_unused_1245_);
v___x_1239_ = v___x_1234_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_err_1237_);
lean_dec(v___x_1234_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
lean_inc_ref(v_pos_1230_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v_pos_1230_);
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_pos_1230_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_err_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_inc(v_idx_1231_);
v_idx_1208_ = v_idx_1231_;
v___y_1209_ = v___x_1242_;
v_pos_1210_ = v_pos_1230_;
v_idx_1211_ = v_idx_1231_;
goto v___jp_1207_;
}
}
}
}
}
v___jp_1246_:
{
uint8_t v___x_1251_; 
v___x_1251_ = lean_nat_dec_eq(v_idx_1247_, v_idx_1250_);
lean_dec(v_idx_1247_);
if (v___x_1251_ == 0)
{
lean_dec(v_idx_1250_);
lean_dec_ref(v_pos_1249_);
return v___y_1248_;
}
else
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_dec_ref(v___y_1248_);
v___x_1252_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31);
lean_inc_ref(v_pos_1249_);
v___x_1253_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1252_, v___f_1166_, v_pos_1249_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_dec_ref(v_pos_1249_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_dec(v_idx_1250_);
return v___x_1253_;
}
else
{
lean_object* v_pos_1254_; lean_object* v_idx_1255_; 
v_pos_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_pos_1254_);
v_idx_1255_ = lean_ctor_get(v_pos_1254_, 1);
lean_inc(v_idx_1255_);
v_idx_1228_ = v_idx_1250_;
v___y_1229_ = v___x_1253_;
v_pos_1230_ = v_pos_1254_;
v_idx_1231_ = v_idx_1255_;
goto v___jp_1227_;
}
}
else
{
lean_object* v_err_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
v_err_1256_ = lean_ctor_get(v___x_1253_, 1);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1263_ == 0)
{
lean_object* v_unused_1264_; 
v_unused_1264_ = lean_ctor_get(v___x_1253_, 0);
lean_dec(v_unused_1264_);
v___x_1258_ = v___x_1253_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_err_1256_);
lean_dec(v___x_1253_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
lean_inc_ref(v_pos_1249_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 0, v_pos_1249_);
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_pos_1249_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v_err_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_inc(v_idx_1250_);
v_idx_1228_ = v_idx_1250_;
v___y_1229_ = v___x_1261_;
v_pos_1230_ = v_pos_1249_;
v_idx_1231_ = v_idx_1250_;
goto v___jp_1227_;
}
}
}
}
}
v___jp_1266_:
{
uint8_t v___x_1271_; 
v___x_1271_ = lean_nat_dec_eq(v_idx_1267_, v_idx_1270_);
lean_dec(v_idx_1267_);
if (v___x_1271_ == 0)
{
lean_dec(v_idx_1270_);
lean_dec_ref(v_pos_1269_);
return v___y_1268_;
}
else
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
lean_dec_ref(v___y_1268_);
v___x_1272_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35);
lean_inc_ref(v_pos_1269_);
v___x_1273_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1272_, v___f_1265_, v_pos_1269_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_dec_ref(v_pos_1269_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_dec(v_idx_1270_);
return v___x_1273_;
}
else
{
lean_object* v_pos_1274_; lean_object* v_idx_1275_; 
v_pos_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_pos_1274_);
v_idx_1275_ = lean_ctor_get(v_pos_1274_, 1);
lean_inc(v_idx_1275_);
v_idx_1247_ = v_idx_1270_;
v___y_1248_ = v___x_1273_;
v_pos_1249_ = v_pos_1274_;
v_idx_1250_ = v_idx_1275_;
goto v___jp_1246_;
}
}
else
{
lean_object* v_err_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
v_err_1276_ = lean_ctor_get(v___x_1273_, 1);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1283_ == 0)
{
lean_object* v_unused_1284_; 
v_unused_1284_ = lean_ctor_get(v___x_1273_, 0);
lean_dec(v_unused_1284_);
v___x_1278_ = v___x_1273_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_err_1276_);
lean_dec(v___x_1273_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
lean_inc_ref(v_pos_1269_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v_pos_1269_);
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_pos_1269_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_err_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_inc(v_idx_1270_);
v_idx_1247_ = v_idx_1270_;
v___y_1248_ = v___x_1281_;
v_pos_1249_ = v_pos_1269_;
v_idx_1250_ = v_idx_1270_;
goto v___jp_1246_;
}
}
}
}
}
v___jp_1285_:
{
uint8_t v___x_1290_; 
v___x_1290_ = lean_nat_dec_eq(v_idx_1286_, v_idx_1289_);
lean_dec(v_idx_1286_);
if (v___x_1290_ == 0)
{
lean_dec(v_idx_1289_);
lean_dec_ref(v_pos_1288_);
return v___y_1287_;
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
lean_dec_ref(v___y_1287_);
v___x_1291_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38);
lean_inc_ref(v_pos_1288_);
v___x_1292_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1291_, v___f_1165_, v_pos_1288_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_dec_ref(v_pos_1288_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_dec(v_idx_1289_);
return v___x_1292_;
}
else
{
lean_object* v_pos_1293_; lean_object* v_idx_1294_; 
v_pos_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_pos_1293_);
v_idx_1294_ = lean_ctor_get(v_pos_1293_, 1);
lean_inc(v_idx_1294_);
v_idx_1267_ = v_idx_1289_;
v___y_1268_ = v___x_1292_;
v_pos_1269_ = v_pos_1293_;
v_idx_1270_ = v_idx_1294_;
goto v___jp_1266_;
}
}
else
{
lean_object* v_err_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
v_err_1295_ = lean_ctor_get(v___x_1292_, 1);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1302_ == 0)
{
lean_object* v_unused_1303_; 
v_unused_1303_ = lean_ctor_get(v___x_1292_, 0);
lean_dec(v_unused_1303_);
v___x_1297_ = v___x_1292_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_err_1295_);
lean_dec(v___x_1292_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
lean_inc_ref(v_pos_1288_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v_pos_1288_);
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_pos_1288_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v_err_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_inc(v_idx_1289_);
v_idx_1267_ = v_idx_1289_;
v___y_1268_ = v___x_1300_;
v_pos_1269_ = v_pos_1288_;
v_idx_1270_ = v_idx_1289_;
goto v___jp_1266_;
}
}
}
}
}
v___jp_1305_:
{
uint8_t v___x_1310_; 
v___x_1310_ = lean_nat_dec_eq(v_idx_1306_, v_idx_1309_);
lean_dec(v_idx_1306_);
if (v___x_1310_ == 0)
{
lean_dec(v_idx_1309_);
lean_dec_ref(v_pos_1308_);
return v___y_1307_;
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
lean_dec_ref(v___y_1307_);
v___x_1311_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42);
lean_inc_ref(v_pos_1308_);
v___x_1312_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1311_, v___f_1304_, v_pos_1308_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_dec_ref(v_pos_1308_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_dec(v_idx_1309_);
return v___x_1312_;
}
else
{
lean_object* v_pos_1313_; lean_object* v_idx_1314_; 
v_pos_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_pos_1313_);
v_idx_1314_ = lean_ctor_get(v_pos_1313_, 1);
lean_inc(v_idx_1314_);
v_idx_1286_ = v_idx_1309_;
v___y_1287_ = v___x_1312_;
v_pos_1288_ = v_pos_1313_;
v_idx_1289_ = v_idx_1314_;
goto v___jp_1285_;
}
}
else
{
lean_object* v_err_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
v_err_1315_ = lean_ctor_get(v___x_1312_, 1);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1322_ == 0)
{
lean_object* v_unused_1323_; 
v_unused_1323_ = lean_ctor_get(v___x_1312_, 0);
lean_dec(v_unused_1323_);
v___x_1317_ = v___x_1312_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_err_1315_);
lean_dec(v___x_1312_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
lean_inc_ref(v_pos_1308_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v_pos_1308_);
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_pos_1308_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_err_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
lean_inc(v_idx_1309_);
v_idx_1286_ = v_idx_1309_;
v___y_1287_ = v___x_1320_;
v_pos_1288_ = v_pos_1308_;
v_idx_1289_ = v_idx_1309_;
goto v___jp_1285_;
}
}
}
}
}
v___jp_1324_:
{
uint8_t v___x_1329_; 
v___x_1329_ = lean_nat_dec_eq(v_idx_1325_, v_idx_1328_);
lean_dec(v_idx_1325_);
if (v___x_1329_ == 0)
{
lean_dec(v_idx_1328_);
lean_dec_ref(v_pos_1327_);
return v___y_1326_;
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_dec_ref(v___y_1326_);
v___x_1330_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45);
lean_inc_ref(v_pos_1327_);
v___x_1331_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1330_, v___f_1164_, v_pos_1327_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_dec_ref(v_pos_1327_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_dec(v_idx_1328_);
return v___x_1331_;
}
else
{
lean_object* v_pos_1332_; lean_object* v_idx_1333_; 
v_pos_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_pos_1332_);
v_idx_1333_ = lean_ctor_get(v_pos_1332_, 1);
lean_inc(v_idx_1333_);
v_idx_1306_ = v_idx_1328_;
v___y_1307_ = v___x_1331_;
v_pos_1308_ = v_pos_1332_;
v_idx_1309_ = v_idx_1333_;
goto v___jp_1305_;
}
}
else
{
lean_object* v_err_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
v_err_1334_ = lean_ctor_get(v___x_1331_, 1);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1341_ == 0)
{
lean_object* v_unused_1342_; 
v_unused_1342_ = lean_ctor_get(v___x_1331_, 0);
lean_dec(v_unused_1342_);
v___x_1336_ = v___x_1331_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_err_1334_);
lean_dec(v___x_1331_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
lean_inc_ref(v_pos_1327_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v_pos_1327_);
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_pos_1327_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_err_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_inc(v_idx_1328_);
v_idx_1306_ = v_idx_1328_;
v___y_1307_ = v___x_1339_;
v_pos_1308_ = v_pos_1327_;
v_idx_1309_ = v_idx_1328_;
goto v___jp_1305_;
}
}
}
}
}
v___jp_1344_:
{
uint8_t v___x_1349_; 
v___x_1349_ = lean_nat_dec_eq(v_idx_1345_, v_idx_1348_);
lean_dec(v_idx_1345_);
if (v___x_1349_ == 0)
{
lean_dec(v_idx_1348_);
lean_dec_ref(v_pos_1347_);
return v___y_1346_;
}
else
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
lean_dec_ref(v___y_1346_);
v___x_1350_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49);
lean_inc_ref(v_pos_1347_);
v___x_1351_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1350_, v___f_1343_, v_pos_1347_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_dec_ref(v_pos_1347_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_dec(v_idx_1348_);
return v___x_1351_;
}
else
{
lean_object* v_pos_1352_; lean_object* v_idx_1353_; 
v_pos_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_pos_1352_);
v_idx_1353_ = lean_ctor_get(v_pos_1352_, 1);
lean_inc(v_idx_1353_);
v_idx_1325_ = v_idx_1348_;
v___y_1326_ = v___x_1351_;
v_pos_1327_ = v_pos_1352_;
v_idx_1328_ = v_idx_1353_;
goto v___jp_1324_;
}
}
else
{
lean_object* v_err_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
v_err_1354_ = lean_ctor_get(v___x_1351_, 1);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1361_ == 0)
{
lean_object* v_unused_1362_; 
v_unused_1362_ = lean_ctor_get(v___x_1351_, 0);
lean_dec(v_unused_1362_);
v___x_1356_ = v___x_1351_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_err_1354_);
lean_dec(v___x_1351_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
lean_inc_ref(v_pos_1347_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v_pos_1347_);
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_pos_1347_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_err_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
lean_inc(v_idx_1348_);
v_idx_1325_ = v_idx_1348_;
v___y_1326_ = v___x_1359_;
v_pos_1327_ = v_pos_1347_;
v_idx_1328_ = v_idx_1348_;
goto v___jp_1324_;
}
}
}
}
}
v___jp_1363_:
{
uint8_t v___x_1368_; 
v___x_1368_ = lean_nat_dec_eq(v_idx_1364_, v_idx_1367_);
lean_dec(v_idx_1364_);
if (v___x_1368_ == 0)
{
lean_dec(v_idx_1367_);
lean_dec_ref(v_pos_1366_);
return v___y_1365_;
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
lean_dec_ref(v___y_1365_);
v___x_1369_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52);
lean_inc_ref(v_pos_1366_);
v___x_1370_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1369_, v___f_1163_, v_pos_1366_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_dec_ref(v_pos_1366_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_dec(v_idx_1367_);
return v___x_1370_;
}
else
{
lean_object* v_pos_1371_; lean_object* v_idx_1372_; 
v_pos_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_pos_1371_);
v_idx_1372_ = lean_ctor_get(v_pos_1371_, 1);
lean_inc(v_idx_1372_);
v_idx_1345_ = v_idx_1367_;
v___y_1346_ = v___x_1370_;
v_pos_1347_ = v_pos_1371_;
v_idx_1348_ = v_idx_1372_;
goto v___jp_1344_;
}
}
else
{
lean_object* v_err_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
v_err_1373_ = lean_ctor_get(v___x_1370_, 1);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1380_ == 0)
{
lean_object* v_unused_1381_; 
v_unused_1381_ = lean_ctor_get(v___x_1370_, 0);
lean_dec(v_unused_1381_);
v___x_1375_ = v___x_1370_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_err_1373_);
lean_dec(v___x_1370_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
lean_inc_ref(v_pos_1366_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v_pos_1366_);
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_pos_1366_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_err_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
lean_inc(v_idx_1367_);
v_idx_1345_ = v_idx_1367_;
v___y_1346_ = v___x_1378_;
v_pos_1347_ = v_pos_1366_;
v_idx_1348_ = v_idx_1367_;
goto v___jp_1344_;
}
}
}
}
}
v___jp_1383_:
{
uint8_t v___x_1388_; 
v___x_1388_ = lean_nat_dec_eq(v_idx_1384_, v_idx_1387_);
lean_dec(v_idx_1384_);
if (v___x_1388_ == 0)
{
lean_dec(v_idx_1387_);
lean_dec_ref(v_pos_1386_);
return v___y_1385_;
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_dec_ref(v___y_1385_);
v___x_1389_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56);
lean_inc_ref(v_pos_1386_);
v___x_1390_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1389_, v___f_1382_, v_pos_1386_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_dec_ref(v_pos_1386_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_dec(v_idx_1387_);
return v___x_1390_;
}
else
{
lean_object* v_pos_1391_; lean_object* v_idx_1392_; 
v_pos_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_pos_1391_);
v_idx_1392_ = lean_ctor_get(v_pos_1391_, 1);
lean_inc(v_idx_1392_);
v_idx_1364_ = v_idx_1387_;
v___y_1365_ = v___x_1390_;
v_pos_1366_ = v_pos_1391_;
v_idx_1367_ = v_idx_1392_;
goto v___jp_1363_;
}
}
else
{
lean_object* v_err_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
v_err_1393_ = lean_ctor_get(v___x_1390_, 1);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v___x_1390_, 0);
lean_dec(v_unused_1401_);
v___x_1395_ = v___x_1390_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_err_1393_);
lean_dec(v___x_1390_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
lean_inc_ref(v_pos_1386_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v_pos_1386_);
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_pos_1386_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_err_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_inc(v_idx_1387_);
v_idx_1364_ = v_idx_1387_;
v___y_1365_ = v___x_1398_;
v_pos_1366_ = v_pos_1386_;
v_idx_1367_ = v_idx_1387_;
goto v___jp_1363_;
}
}
}
}
}
v___jp_1402_:
{
uint8_t v___x_1407_; 
v___x_1407_ = lean_nat_dec_eq(v_idx_1403_, v_idx_1406_);
lean_dec(v_idx_1403_);
if (v___x_1407_ == 0)
{
lean_dec(v_idx_1406_);
lean_dec_ref(v_pos_1405_);
return v___y_1404_;
}
else
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
lean_dec_ref(v___y_1404_);
v___x_1408_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59);
lean_inc_ref(v_pos_1405_);
v___x_1409_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1408_, v___f_1162_, v_pos_1405_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_dec_ref(v_pos_1405_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_dec(v_idx_1406_);
return v___x_1409_;
}
else
{
lean_object* v_pos_1410_; lean_object* v_idx_1411_; 
v_pos_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_pos_1410_);
v_idx_1411_ = lean_ctor_get(v_pos_1410_, 1);
lean_inc(v_idx_1411_);
v_idx_1384_ = v_idx_1406_;
v___y_1385_ = v___x_1409_;
v_pos_1386_ = v_pos_1410_;
v_idx_1387_ = v_idx_1411_;
goto v___jp_1383_;
}
}
else
{
lean_object* v_err_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
v_err_1412_ = lean_ctor_get(v___x_1409_, 1);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1419_ == 0)
{
lean_object* v_unused_1420_; 
v_unused_1420_ = lean_ctor_get(v___x_1409_, 0);
lean_dec(v_unused_1420_);
v___x_1414_ = v___x_1409_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_err_1412_);
lean_dec(v___x_1409_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
lean_inc_ref(v_pos_1405_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v_pos_1405_);
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_pos_1405_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_err_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_inc(v_idx_1406_);
v_idx_1384_ = v_idx_1406_;
v___y_1385_ = v___x_1417_;
v_pos_1386_ = v_pos_1405_;
v_idx_1387_ = v_idx_1406_;
goto v___jp_1383_;
}
}
}
}
}
v___jp_1422_:
{
uint8_t v___x_1427_; 
v___x_1427_ = lean_nat_dec_eq(v_idx_1423_, v_idx_1426_);
lean_dec(v_idx_1423_);
if (v___x_1427_ == 0)
{
lean_dec(v_idx_1426_);
lean_dec_ref(v_pos_1425_);
return v___y_1424_;
}
else
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
lean_dec_ref(v___y_1424_);
v___x_1428_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63);
lean_inc_ref(v_pos_1425_);
v___x_1429_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1428_, v___f_1421_, v_pos_1425_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_dec_ref(v_pos_1425_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_dec(v_idx_1426_);
return v___x_1429_;
}
else
{
lean_object* v_pos_1430_; lean_object* v_idx_1431_; 
v_pos_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_pos_1430_);
v_idx_1431_ = lean_ctor_get(v_pos_1430_, 1);
lean_inc(v_idx_1431_);
v_idx_1403_ = v_idx_1426_;
v___y_1404_ = v___x_1429_;
v_pos_1405_ = v_pos_1430_;
v_idx_1406_ = v_idx_1431_;
goto v___jp_1402_;
}
}
else
{
lean_object* v_err_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
v_err_1432_ = lean_ctor_get(v___x_1429_, 1);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1439_ == 0)
{
lean_object* v_unused_1440_; 
v_unused_1440_ = lean_ctor_get(v___x_1429_, 0);
lean_dec(v_unused_1440_);
v___x_1434_ = v___x_1429_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_err_1432_);
lean_dec(v___x_1429_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
lean_inc_ref(v_pos_1425_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v_pos_1425_);
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_pos_1425_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_err_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
lean_inc(v_idx_1426_);
v_idx_1403_ = v_idx_1426_;
v___y_1404_ = v___x_1437_;
v_pos_1405_ = v_pos_1425_;
v_idx_1406_ = v_idx_1426_;
goto v___jp_1402_;
}
}
}
}
}
v___jp_1441_:
{
uint8_t v___x_1446_; 
v___x_1446_ = lean_nat_dec_eq(v_idx_1442_, v_idx_1445_);
lean_dec(v_idx_1442_);
if (v___x_1446_ == 0)
{
lean_dec(v_idx_1445_);
lean_dec_ref(v_pos_1444_);
return v___y_1443_;
}
else
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_dec_ref(v___y_1443_);
v___x_1447_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66);
lean_inc_ref(v_pos_1444_);
v___x_1448_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1447_, v___f_1161_, v_pos_1444_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_dec_ref(v_pos_1444_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_dec(v_idx_1445_);
return v___x_1448_;
}
else
{
lean_object* v_pos_1449_; lean_object* v_idx_1450_; 
v_pos_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_pos_1449_);
v_idx_1450_ = lean_ctor_get(v_pos_1449_, 1);
lean_inc(v_idx_1450_);
v_idx_1423_ = v_idx_1445_;
v___y_1424_ = v___x_1448_;
v_pos_1425_ = v_pos_1449_;
v_idx_1426_ = v_idx_1450_;
goto v___jp_1422_;
}
}
else
{
lean_object* v_err_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
v_err_1451_ = lean_ctor_get(v___x_1448_, 1);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; 
v_unused_1459_ = lean_ctor_get(v___x_1448_, 0);
lean_dec(v_unused_1459_);
v___x_1453_ = v___x_1448_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_err_1451_);
lean_dec(v___x_1448_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
lean_inc_ref(v_pos_1444_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v_pos_1444_);
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_pos_1444_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_err_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_inc(v_idx_1445_);
v_idx_1423_ = v_idx_1445_;
v___y_1424_ = v___x_1456_;
v_pos_1425_ = v_pos_1444_;
v_idx_1426_ = v_idx_1445_;
goto v___jp_1422_;
}
}
}
}
}
v___jp_1461_:
{
uint8_t v___x_1466_; 
v___x_1466_ = lean_nat_dec_eq(v_idx_1462_, v_idx_1465_);
lean_dec(v_idx_1462_);
if (v___x_1466_ == 0)
{
lean_dec(v_idx_1465_);
lean_dec_ref(v_pos_1464_);
return v___y_1463_;
}
else
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
lean_dec_ref(v___y_1463_);
v___x_1467_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70);
lean_inc_ref(v_pos_1464_);
v___x_1468_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1467_, v___f_1460_, v_pos_1464_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_dec_ref(v_pos_1464_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_dec(v_idx_1465_);
return v___x_1468_;
}
else
{
lean_object* v_pos_1469_; lean_object* v_idx_1470_; 
v_pos_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_pos_1469_);
v_idx_1470_ = lean_ctor_get(v_pos_1469_, 1);
lean_inc(v_idx_1470_);
v_idx_1442_ = v_idx_1465_;
v___y_1443_ = v___x_1468_;
v_pos_1444_ = v_pos_1469_;
v_idx_1445_ = v_idx_1470_;
goto v___jp_1441_;
}
}
else
{
lean_object* v_err_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
v_err_1471_ = lean_ctor_get(v___x_1468_, 1);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1478_ == 0)
{
lean_object* v_unused_1479_; 
v_unused_1479_ = lean_ctor_get(v___x_1468_, 0);
lean_dec(v_unused_1479_);
v___x_1473_ = v___x_1468_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_err_1471_);
lean_dec(v___x_1468_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
lean_inc_ref(v_pos_1464_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v_pos_1464_);
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_pos_1464_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_err_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_inc(v_idx_1465_);
v_idx_1442_ = v_idx_1465_;
v___y_1443_ = v___x_1476_;
v_pos_1444_ = v_pos_1464_;
v_idx_1445_ = v_idx_1465_;
goto v___jp_1441_;
}
}
}
}
}
v___jp_1480_:
{
uint8_t v___x_1485_; 
v___x_1485_ = lean_nat_dec_eq(v_idx_1481_, v_idx_1484_);
lean_dec(v_idx_1481_);
if (v___x_1485_ == 0)
{
lean_dec(v_idx_1484_);
lean_dec_ref(v_pos_1483_);
return v___y_1482_;
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_dec_ref(v___y_1482_);
v___x_1486_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73);
lean_inc_ref(v_pos_1483_);
v___x_1487_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1486_, v___f_1160_, v_pos_1483_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_dec_ref(v_pos_1483_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_dec(v_idx_1484_);
return v___x_1487_;
}
else
{
lean_object* v_pos_1488_; lean_object* v_idx_1489_; 
v_pos_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_pos_1488_);
v_idx_1489_ = lean_ctor_get(v_pos_1488_, 1);
lean_inc(v_idx_1489_);
v_idx_1462_ = v_idx_1484_;
v___y_1463_ = v___x_1487_;
v_pos_1464_ = v_pos_1488_;
v_idx_1465_ = v_idx_1489_;
goto v___jp_1461_;
}
}
else
{
lean_object* v_err_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
v_err_1490_ = lean_ctor_get(v___x_1487_, 1);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1497_ == 0)
{
lean_object* v_unused_1498_; 
v_unused_1498_ = lean_ctor_get(v___x_1487_, 0);
lean_dec(v_unused_1498_);
v___x_1492_ = v___x_1487_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_err_1490_);
lean_dec(v___x_1487_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
lean_inc_ref(v_pos_1483_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v_pos_1483_);
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_pos_1483_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v_err_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_inc(v_idx_1484_);
v_idx_1462_ = v_idx_1484_;
v___y_1463_ = v___x_1495_;
v_pos_1464_ = v_pos_1483_;
v_idx_1465_ = v_idx_1484_;
goto v___jp_1461_;
}
}
}
}
}
v___jp_1500_:
{
uint8_t v___x_1505_; 
v___x_1505_ = lean_nat_dec_eq(v_idx_1501_, v_idx_1504_);
lean_dec(v_idx_1501_);
if (v___x_1505_ == 0)
{
lean_dec(v_idx_1504_);
lean_dec_ref(v_pos_1503_);
return v___y_1502_;
}
else
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_dec_ref(v___y_1502_);
v___x_1506_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77);
lean_inc_ref(v_pos_1503_);
v___x_1507_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1506_, v___f_1499_, v_pos_1503_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_dec_ref(v_pos_1503_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_dec(v_idx_1504_);
return v___x_1507_;
}
else
{
lean_object* v_pos_1508_; lean_object* v_idx_1509_; 
v_pos_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_pos_1508_);
v_idx_1509_ = lean_ctor_get(v_pos_1508_, 1);
lean_inc(v_idx_1509_);
v_idx_1481_ = v_idx_1504_;
v___y_1482_ = v___x_1507_;
v_pos_1483_ = v_pos_1508_;
v_idx_1484_ = v_idx_1509_;
goto v___jp_1480_;
}
}
else
{
lean_object* v_err_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
v_err_1510_ = lean_ctor_get(v___x_1507_, 1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1517_ == 0)
{
lean_object* v_unused_1518_; 
v_unused_1518_ = lean_ctor_get(v___x_1507_, 0);
lean_dec(v_unused_1518_);
v___x_1512_ = v___x_1507_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_err_1510_);
lean_dec(v___x_1507_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
lean_inc_ref(v_pos_1503_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v_pos_1503_);
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_pos_1503_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_err_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_inc(v_idx_1504_);
v_idx_1481_ = v_idx_1504_;
v___y_1482_ = v___x_1515_;
v_pos_1483_ = v_pos_1503_;
v_idx_1484_ = v_idx_1504_;
goto v___jp_1480_;
}
}
}
}
}
v___jp_1519_:
{
uint8_t v___x_1524_; 
v___x_1524_ = lean_nat_dec_eq(v_idx_1520_, v_idx_1523_);
lean_dec(v_idx_1520_);
if (v___x_1524_ == 0)
{
lean_dec(v_idx_1523_);
lean_dec_ref(v_pos_1522_);
return v___y_1521_;
}
else
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
lean_dec_ref(v___y_1521_);
v___x_1525_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80);
lean_inc_ref(v_pos_1522_);
v___x_1526_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1525_, v___f_1159_, v_pos_1522_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_dec_ref(v_pos_1522_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_dec(v_idx_1523_);
return v___x_1526_;
}
else
{
lean_object* v_pos_1527_; lean_object* v_idx_1528_; 
v_pos_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_pos_1527_);
v_idx_1528_ = lean_ctor_get(v_pos_1527_, 1);
lean_inc(v_idx_1528_);
v_idx_1501_ = v_idx_1523_;
v___y_1502_ = v___x_1526_;
v_pos_1503_ = v_pos_1527_;
v_idx_1504_ = v_idx_1528_;
goto v___jp_1500_;
}
}
else
{
lean_object* v_err_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
v_err_1529_ = lean_ctor_get(v___x_1526_, 1);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1536_ == 0)
{
lean_object* v_unused_1537_; 
v_unused_1537_ = lean_ctor_get(v___x_1526_, 0);
lean_dec(v_unused_1537_);
v___x_1531_ = v___x_1526_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_err_1529_);
lean_dec(v___x_1526_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
lean_inc_ref(v_pos_1522_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v_pos_1522_);
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_pos_1522_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_err_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_inc(v_idx_1523_);
v_idx_1501_ = v_idx_1523_;
v___y_1502_ = v___x_1534_;
v_pos_1503_ = v_pos_1522_;
v_idx_1504_ = v_idx_1523_;
goto v___jp_1500_;
}
}
}
}
}
v___jp_1539_:
{
uint8_t v___x_1544_; 
v___x_1544_ = lean_nat_dec_eq(v_idx_1540_, v_idx_1543_);
lean_dec(v_idx_1540_);
if (v___x_1544_ == 0)
{
lean_dec(v_idx_1543_);
lean_dec_ref(v_pos_1542_);
return v___y_1541_;
}
else
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
lean_dec_ref(v___y_1541_);
v___x_1545_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84);
lean_inc_ref(v_pos_1542_);
v___x_1546_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1545_, v___f_1538_, v_pos_1542_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_dec_ref(v_pos_1542_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_dec(v_idx_1543_);
return v___x_1546_;
}
else
{
lean_object* v_pos_1547_; lean_object* v_idx_1548_; 
v_pos_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_pos_1547_);
v_idx_1548_ = lean_ctor_get(v_pos_1547_, 1);
lean_inc(v_idx_1548_);
v_idx_1520_ = v_idx_1543_;
v___y_1521_ = v___x_1546_;
v_pos_1522_ = v_pos_1547_;
v_idx_1523_ = v_idx_1548_;
goto v___jp_1519_;
}
}
else
{
lean_object* v_err_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
v_err_1549_ = lean_ctor_get(v___x_1546_, 1);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1556_ == 0)
{
lean_object* v_unused_1557_; 
v_unused_1557_ = lean_ctor_get(v___x_1546_, 0);
lean_dec(v_unused_1557_);
v___x_1551_ = v___x_1546_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_err_1549_);
lean_dec(v___x_1546_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
lean_inc_ref(v_pos_1542_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v_pos_1542_);
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_pos_1542_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_err_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_inc(v_idx_1543_);
v_idx_1520_ = v_idx_1543_;
v___y_1521_ = v___x_1554_;
v_pos_1522_ = v_pos_1542_;
v_idx_1523_ = v_idx_1543_;
goto v___jp_1519_;
}
}
}
}
}
v___jp_1558_:
{
uint8_t v___x_1563_; 
v___x_1563_ = lean_nat_dec_eq(v_idx_1559_, v_idx_1562_);
lean_dec(v_idx_1559_);
if (v___x_1563_ == 0)
{
lean_dec(v_idx_1562_);
lean_dec_ref(v_pos_1561_);
return v___y_1560_;
}
else
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
lean_dec_ref(v___y_1560_);
v___x_1564_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87);
lean_inc_ref(v_pos_1561_);
v___x_1565_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1564_, v___f_1158_, v_pos_1561_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_dec_ref(v_pos_1561_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_dec(v_idx_1562_);
return v___x_1565_;
}
else
{
lean_object* v_pos_1566_; lean_object* v_idx_1567_; 
v_pos_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_pos_1566_);
v_idx_1567_ = lean_ctor_get(v_pos_1566_, 1);
lean_inc(v_idx_1567_);
v_idx_1540_ = v_idx_1562_;
v___y_1541_ = v___x_1565_;
v_pos_1542_ = v_pos_1566_;
v_idx_1543_ = v_idx_1567_;
goto v___jp_1539_;
}
}
else
{
lean_object* v_err_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
v_err_1568_ = lean_ctor_get(v___x_1565_, 1);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1575_ == 0)
{
lean_object* v_unused_1576_; 
v_unused_1576_ = lean_ctor_get(v___x_1565_, 0);
lean_dec(v_unused_1576_);
v___x_1570_ = v___x_1565_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_err_1568_);
lean_dec(v___x_1565_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
lean_inc_ref(v_pos_1561_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v_pos_1561_);
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_pos_1561_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v_err_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_inc(v_idx_1562_);
v_idx_1540_ = v_idx_1562_;
v___y_1541_ = v___x_1573_;
v_pos_1542_ = v_pos_1561_;
v_idx_1543_ = v_idx_1562_;
goto v___jp_1539_;
}
}
}
}
}
v___jp_1578_:
{
uint8_t v___x_1583_; 
v___x_1583_ = lean_nat_dec_eq(v_idx_1579_, v_idx_1582_);
lean_dec(v_idx_1579_);
if (v___x_1583_ == 0)
{
lean_dec(v_idx_1582_);
lean_dec_ref(v_pos_1581_);
return v___y_1580_;
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
lean_dec_ref(v___y_1580_);
v___x_1584_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91);
lean_inc_ref(v_pos_1581_);
v___x_1585_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1584_, v___f_1577_, v_pos_1581_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_dec_ref(v_pos_1581_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_dec(v_idx_1582_);
return v___x_1585_;
}
else
{
lean_object* v_pos_1586_; lean_object* v_idx_1587_; 
v_pos_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_pos_1586_);
v_idx_1587_ = lean_ctor_get(v_pos_1586_, 1);
lean_inc(v_idx_1587_);
v_idx_1559_ = v_idx_1582_;
v___y_1560_ = v___x_1585_;
v_pos_1561_ = v_pos_1586_;
v_idx_1562_ = v_idx_1587_;
goto v___jp_1558_;
}
}
else
{
lean_object* v_err_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
v_err_1588_ = lean_ctor_get(v___x_1585_, 1);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1595_ == 0)
{
lean_object* v_unused_1596_; 
v_unused_1596_ = lean_ctor_get(v___x_1585_, 0);
lean_dec(v_unused_1596_);
v___x_1590_ = v___x_1585_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_err_1588_);
lean_dec(v___x_1585_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
lean_inc_ref(v_pos_1581_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v_pos_1581_);
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_pos_1581_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_err_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_inc(v_idx_1582_);
v_idx_1559_ = v_idx_1582_;
v___y_1560_ = v___x_1593_;
v_pos_1561_ = v_pos_1581_;
v_idx_1562_ = v_idx_1582_;
goto v___jp_1558_;
}
}
}
}
}
v___jp_1597_:
{
uint8_t v___x_1602_; 
v___x_1602_ = lean_nat_dec_eq(v_idx_1598_, v_idx_1601_);
lean_dec(v_idx_1598_);
if (v___x_1602_ == 0)
{
lean_dec(v_idx_1601_);
lean_dec_ref(v_pos_1600_);
return v___y_1599_;
}
else
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_dec_ref(v___y_1599_);
v___x_1603_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94);
lean_inc_ref(v_pos_1600_);
v___x_1604_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1603_, v___f_1157_, v_pos_1600_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_dec_ref(v_pos_1600_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_dec(v_idx_1601_);
return v___x_1604_;
}
else
{
lean_object* v_pos_1605_; lean_object* v_idx_1606_; 
v_pos_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_pos_1605_);
v_idx_1606_ = lean_ctor_get(v_pos_1605_, 1);
lean_inc(v_idx_1606_);
v_idx_1579_ = v_idx_1601_;
v___y_1580_ = v___x_1604_;
v_pos_1581_ = v_pos_1605_;
v_idx_1582_ = v_idx_1606_;
goto v___jp_1578_;
}
}
else
{
lean_object* v_err_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
v_err_1607_ = lean_ctor_get(v___x_1604_, 1);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1614_ == 0)
{
lean_object* v_unused_1615_; 
v_unused_1615_ = lean_ctor_get(v___x_1604_, 0);
lean_dec(v_unused_1615_);
v___x_1609_ = v___x_1604_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_err_1607_);
lean_dec(v___x_1604_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
lean_inc_ref(v_pos_1600_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v_pos_1600_);
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_pos_1600_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_err_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
lean_inc(v_idx_1601_);
v_idx_1579_ = v_idx_1601_;
v___y_1580_ = v___x_1612_;
v_pos_1581_ = v_pos_1600_;
v_idx_1582_ = v_idx_1601_;
goto v___jp_1578_;
}
}
}
}
}
v___jp_1617_:
{
uint8_t v___x_1622_; 
v___x_1622_ = lean_nat_dec_eq(v_idx_1618_, v_idx_1621_);
lean_dec(v_idx_1618_);
if (v___x_1622_ == 0)
{
lean_dec(v_idx_1621_);
lean_dec_ref(v_pos_1620_);
return v___y_1619_;
}
else
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
lean_dec_ref(v___y_1619_);
v___x_1623_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98);
lean_inc_ref(v_pos_1620_);
v___x_1624_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1623_, v___f_1616_, v_pos_1620_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_dec_ref(v_pos_1620_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_dec(v_idx_1621_);
return v___x_1624_;
}
else
{
lean_object* v_pos_1625_; lean_object* v_idx_1626_; 
v_pos_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_pos_1625_);
v_idx_1626_ = lean_ctor_get(v_pos_1625_, 1);
lean_inc(v_idx_1626_);
v_idx_1598_ = v_idx_1621_;
v___y_1599_ = v___x_1624_;
v_pos_1600_ = v_pos_1625_;
v_idx_1601_ = v_idx_1626_;
goto v___jp_1597_;
}
}
else
{
lean_object* v_err_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
v_err_1627_ = lean_ctor_get(v___x_1624_, 1);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1634_ == 0)
{
lean_object* v_unused_1635_; 
v_unused_1635_ = lean_ctor_get(v___x_1624_, 0);
lean_dec(v_unused_1635_);
v___x_1629_ = v___x_1624_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_err_1627_);
lean_dec(v___x_1624_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
lean_inc_ref(v_pos_1620_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v_pos_1620_);
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_pos_1620_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_err_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
lean_inc(v_idx_1621_);
v_idx_1598_ = v_idx_1621_;
v___y_1599_ = v___x_1632_;
v_pos_1600_ = v_pos_1620_;
v_idx_1601_ = v_idx_1621_;
goto v___jp_1597_;
}
}
}
}
}
v___jp_1636_:
{
uint8_t v___x_1641_; 
v___x_1641_ = lean_nat_dec_eq(v_idx_1637_, v_idx_1640_);
lean_dec(v_idx_1637_);
if (v___x_1641_ == 0)
{
lean_dec(v_idx_1640_);
lean_dec_ref(v_pos_1639_);
return v___y_1638_;
}
else
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
lean_dec_ref(v___y_1638_);
v___x_1642_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101);
lean_inc_ref(v_pos_1639_);
v___x_1643_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1642_, v___f_1156_, v_pos_1639_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_dec_ref(v_pos_1639_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_dec(v_idx_1640_);
return v___x_1643_;
}
else
{
lean_object* v_pos_1644_; lean_object* v_idx_1645_; 
v_pos_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_pos_1644_);
v_idx_1645_ = lean_ctor_get(v_pos_1644_, 1);
lean_inc(v_idx_1645_);
v_idx_1618_ = v_idx_1640_;
v___y_1619_ = v___x_1643_;
v_pos_1620_ = v_pos_1644_;
v_idx_1621_ = v_idx_1645_;
goto v___jp_1617_;
}
}
else
{
lean_object* v_err_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
v_err_1646_ = lean_ctor_get(v___x_1643_, 1);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1653_ == 0)
{
lean_object* v_unused_1654_; 
v_unused_1654_ = lean_ctor_get(v___x_1643_, 0);
lean_dec(v_unused_1654_);
v___x_1648_ = v___x_1643_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_err_1646_);
lean_dec(v___x_1643_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
lean_inc_ref(v_pos_1639_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v_pos_1639_);
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_pos_1639_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_err_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_inc(v_idx_1640_);
v_idx_1618_ = v_idx_1640_;
v___y_1619_ = v___x_1651_;
v_pos_1620_ = v_pos_1639_;
v_idx_1621_ = v_idx_1640_;
goto v___jp_1617_;
}
}
}
}
}
v___jp_1656_:
{
uint8_t v___x_1661_; 
v___x_1661_ = lean_nat_dec_eq(v_idx_1657_, v_idx_1660_);
lean_dec(v_idx_1657_);
if (v___x_1661_ == 0)
{
lean_dec(v_idx_1660_);
lean_dec_ref(v_pos_1659_);
return v___y_1658_;
}
else
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
lean_dec_ref(v___y_1658_);
v___x_1662_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105);
lean_inc_ref(v_pos_1659_);
v___x_1663_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1662_, v___f_1655_, v_pos_1659_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_dec_ref(v_pos_1659_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_dec(v_idx_1660_);
return v___x_1663_;
}
else
{
lean_object* v_pos_1664_; lean_object* v_idx_1665_; 
v_pos_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_pos_1664_);
v_idx_1665_ = lean_ctor_get(v_pos_1664_, 1);
lean_inc(v_idx_1665_);
v_idx_1637_ = v_idx_1660_;
v___y_1638_ = v___x_1663_;
v_pos_1639_ = v_pos_1664_;
v_idx_1640_ = v_idx_1665_;
goto v___jp_1636_;
}
}
else
{
lean_object* v_err_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
v_err_1666_ = lean_ctor_get(v___x_1663_, 1);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1673_ == 0)
{
lean_object* v_unused_1674_; 
v_unused_1674_ = lean_ctor_get(v___x_1663_, 0);
lean_dec(v_unused_1674_);
v___x_1668_ = v___x_1663_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_err_1666_);
lean_dec(v___x_1663_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
lean_inc_ref(v_pos_1659_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 0, v_pos_1659_);
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_pos_1659_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_err_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_inc(v_idx_1660_);
v_idx_1637_ = v_idx_1660_;
v___y_1638_ = v___x_1671_;
v_pos_1639_ = v_pos_1659_;
v_idx_1640_ = v_idx_1660_;
goto v___jp_1636_;
}
}
}
}
}
v___jp_1675_:
{
uint8_t v___x_1680_; 
v___x_1680_ = lean_nat_dec_eq(v_idx_1676_, v_idx_1679_);
lean_dec(v_idx_1676_);
if (v___x_1680_ == 0)
{
lean_dec(v_idx_1679_);
lean_dec_ref(v_pos_1678_);
return v___y_1677_;
}
else
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
lean_dec_ref(v___y_1677_);
v___x_1681_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108);
lean_inc_ref(v_pos_1678_);
v___x_1682_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1681_, v___f_1155_, v_pos_1678_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_dec_ref(v_pos_1678_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_dec(v_idx_1679_);
return v___x_1682_;
}
else
{
lean_object* v_pos_1683_; lean_object* v_idx_1684_; 
v_pos_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_pos_1683_);
v_idx_1684_ = lean_ctor_get(v_pos_1683_, 1);
lean_inc(v_idx_1684_);
v_idx_1657_ = v_idx_1679_;
v___y_1658_ = v___x_1682_;
v_pos_1659_ = v_pos_1683_;
v_idx_1660_ = v_idx_1684_;
goto v___jp_1656_;
}
}
else
{
lean_object* v_err_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
v_err_1685_ = lean_ctor_get(v___x_1682_, 1);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1692_ == 0)
{
lean_object* v_unused_1693_; 
v_unused_1693_ = lean_ctor_get(v___x_1682_, 0);
lean_dec(v_unused_1693_);
v___x_1687_ = v___x_1682_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_err_1685_);
lean_dec(v___x_1682_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
lean_inc_ref(v_pos_1678_);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 0, v_pos_1678_);
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_pos_1678_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_err_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
lean_inc(v_idx_1679_);
v_idx_1657_ = v_idx_1679_;
v___y_1658_ = v___x_1690_;
v_pos_1659_ = v_pos_1678_;
v_idx_1660_ = v_idx_1679_;
goto v___jp_1656_;
}
}
}
}
}
v___jp_1695_:
{
uint8_t v___x_1700_; 
v___x_1700_ = lean_nat_dec_eq(v_idx_1696_, v_idx_1699_);
lean_dec(v_idx_1696_);
if (v___x_1700_ == 0)
{
lean_dec(v_idx_1699_);
lean_dec_ref(v_pos_1698_);
return v___y_1697_;
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
lean_dec_ref(v___y_1697_);
v___x_1701_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112);
lean_inc_ref(v_pos_1698_);
v___x_1702_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1701_, v___f_1694_, v_pos_1698_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_dec_ref(v_pos_1698_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_dec(v_idx_1699_);
return v___x_1702_;
}
else
{
lean_object* v_pos_1703_; lean_object* v_idx_1704_; 
v_pos_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_pos_1703_);
v_idx_1704_ = lean_ctor_get(v_pos_1703_, 1);
lean_inc(v_idx_1704_);
v_idx_1676_ = v_idx_1699_;
v___y_1677_ = v___x_1702_;
v_pos_1678_ = v_pos_1703_;
v_idx_1679_ = v_idx_1704_;
goto v___jp_1675_;
}
}
else
{
lean_object* v_err_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
v_err_1705_ = lean_ctor_get(v___x_1702_, 1);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1712_ == 0)
{
lean_object* v_unused_1713_; 
v_unused_1713_ = lean_ctor_get(v___x_1702_, 0);
lean_dec(v_unused_1713_);
v___x_1707_ = v___x_1702_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_err_1705_);
lean_dec(v___x_1702_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
lean_inc_ref(v_pos_1698_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v_pos_1698_);
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_pos_1698_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v_err_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
lean_inc(v_idx_1699_);
v_idx_1676_ = v_idx_1699_;
v___y_1677_ = v___x_1710_;
v_pos_1678_ = v_pos_1698_;
v_idx_1679_ = v_idx_1699_;
goto v___jp_1675_;
}
}
}
}
}
v___jp_1714_:
{
uint8_t v___x_1719_; 
v___x_1719_ = lean_nat_dec_eq(v_idx_1715_, v_idx_1718_);
lean_dec(v_idx_1715_);
if (v___x_1719_ == 0)
{
lean_dec(v_idx_1718_);
lean_dec_ref(v_pos_1717_);
return v___y_1716_;
}
else
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
lean_dec_ref(v___y_1716_);
v___x_1720_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115);
lean_inc_ref(v_pos_1717_);
v___x_1721_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1720_, v___f_1154_, v_pos_1717_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_dec_ref(v_pos_1717_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_dec(v_idx_1718_);
return v___x_1721_;
}
else
{
lean_object* v_pos_1722_; lean_object* v_idx_1723_; 
v_pos_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_pos_1722_);
v_idx_1723_ = lean_ctor_get(v_pos_1722_, 1);
lean_inc(v_idx_1723_);
v_idx_1696_ = v_idx_1718_;
v___y_1697_ = v___x_1721_;
v_pos_1698_ = v_pos_1722_;
v_idx_1699_ = v_idx_1723_;
goto v___jp_1695_;
}
}
else
{
lean_object* v_err_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
v_err_1724_ = lean_ctor_get(v___x_1721_, 1);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1731_ == 0)
{
lean_object* v_unused_1732_; 
v_unused_1732_ = lean_ctor_get(v___x_1721_, 0);
lean_dec(v_unused_1732_);
v___x_1726_ = v___x_1721_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_err_1724_);
lean_dec(v___x_1721_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
lean_inc_ref(v_pos_1717_);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v_pos_1717_);
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_pos_1717_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_err_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_inc(v_idx_1718_);
v_idx_1696_ = v_idx_1718_;
v___y_1697_ = v___x_1729_;
v_pos_1698_ = v_pos_1717_;
v_idx_1699_ = v_idx_1718_;
goto v___jp_1695_;
}
}
}
}
}
v___jp_1734_:
{
uint8_t v___x_1739_; 
v___x_1739_ = lean_nat_dec_eq(v_idx_1735_, v_idx_1738_);
lean_dec(v_idx_1735_);
if (v___x_1739_ == 0)
{
lean_dec(v_idx_1738_);
lean_dec_ref(v_pos_1737_);
return v___y_1736_;
}
else
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
lean_dec_ref(v___y_1736_);
v___x_1740_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119);
lean_inc_ref(v_pos_1737_);
v___x_1741_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1740_, v___f_1733_, v_pos_1737_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_dec_ref(v_pos_1737_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_dec(v_idx_1738_);
return v___x_1741_;
}
else
{
lean_object* v_pos_1742_; lean_object* v_idx_1743_; 
v_pos_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_pos_1742_);
v_idx_1743_ = lean_ctor_get(v_pos_1742_, 1);
lean_inc(v_idx_1743_);
v_idx_1715_ = v_idx_1738_;
v___y_1716_ = v___x_1741_;
v_pos_1717_ = v_pos_1742_;
v_idx_1718_ = v_idx_1743_;
goto v___jp_1714_;
}
}
else
{
lean_object* v_err_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
v_err_1744_ = lean_ctor_get(v___x_1741_, 1);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1751_ == 0)
{
lean_object* v_unused_1752_; 
v_unused_1752_ = lean_ctor_get(v___x_1741_, 0);
lean_dec(v_unused_1752_);
v___x_1746_ = v___x_1741_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_err_1744_);
lean_dec(v___x_1741_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
lean_inc_ref(v_pos_1737_);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 0, v_pos_1737_);
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_pos_1737_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_err_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_inc(v_idx_1738_);
v_idx_1715_ = v_idx_1738_;
v___y_1716_ = v___x_1749_;
v_pos_1717_ = v_pos_1737_;
v_idx_1718_ = v_idx_1738_;
goto v___jp_1714_;
}
}
}
}
}
v___jp_1753_:
{
uint8_t v___x_1758_; 
v___x_1758_ = lean_nat_dec_eq(v_idx_1754_, v_idx_1757_);
lean_dec(v_idx_1754_);
if (v___x_1758_ == 0)
{
lean_dec(v_idx_1757_);
lean_dec_ref(v_pos_1756_);
return v___y_1755_;
}
else
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_dec_ref(v___y_1755_);
v___x_1759_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122);
lean_inc_ref(v_pos_1756_);
v___x_1760_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1759_, v___f_1153_, v_pos_1756_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_dec_ref(v_pos_1756_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_dec(v_idx_1757_);
return v___x_1760_;
}
else
{
lean_object* v_pos_1761_; lean_object* v_idx_1762_; 
v_pos_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_pos_1761_);
v_idx_1762_ = lean_ctor_get(v_pos_1761_, 1);
lean_inc(v_idx_1762_);
v_idx_1735_ = v_idx_1757_;
v___y_1736_ = v___x_1760_;
v_pos_1737_ = v_pos_1761_;
v_idx_1738_ = v_idx_1762_;
goto v___jp_1734_;
}
}
else
{
lean_object* v_err_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
v_err_1763_ = lean_ctor_get(v___x_1760_, 1);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1770_ == 0)
{
lean_object* v_unused_1771_; 
v_unused_1771_ = lean_ctor_get(v___x_1760_, 0);
lean_dec(v_unused_1771_);
v___x_1765_ = v___x_1760_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_err_1763_);
lean_dec(v___x_1760_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
lean_inc_ref(v_pos_1756_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v_pos_1756_);
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_pos_1756_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_err_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
lean_inc(v_idx_1757_);
v_idx_1735_ = v_idx_1757_;
v___y_1736_ = v___x_1768_;
v_pos_1737_ = v_pos_1756_;
v_idx_1738_ = v_idx_1757_;
goto v___jp_1734_;
}
}
}
}
}
v___jp_1773_:
{
uint8_t v___x_1778_; 
v___x_1778_ = lean_nat_dec_eq(v_idx_1774_, v_idx_1777_);
lean_dec(v_idx_1774_);
if (v___x_1778_ == 0)
{
lean_dec(v_idx_1777_);
lean_dec_ref(v_pos_1776_);
return v___y_1775_;
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_dec_ref(v___y_1775_);
v___x_1779_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126);
lean_inc_ref(v_pos_1776_);
v___x_1780_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1779_, v___f_1772_, v_pos_1776_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_dec_ref(v_pos_1776_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_dec(v_idx_1777_);
return v___x_1780_;
}
else
{
lean_object* v_pos_1781_; lean_object* v_idx_1782_; 
v_pos_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_pos_1781_);
v_idx_1782_ = lean_ctor_get(v_pos_1781_, 1);
lean_inc(v_idx_1782_);
v_idx_1754_ = v_idx_1777_;
v___y_1755_ = v___x_1780_;
v_pos_1756_ = v_pos_1781_;
v_idx_1757_ = v_idx_1782_;
goto v___jp_1753_;
}
}
else
{
lean_object* v_err_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
v_err_1783_ = lean_ctor_get(v___x_1780_, 1);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1790_ == 0)
{
lean_object* v_unused_1791_; 
v_unused_1791_ = lean_ctor_get(v___x_1780_, 0);
lean_dec(v_unused_1791_);
v___x_1785_ = v___x_1780_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_err_1783_);
lean_dec(v___x_1780_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
lean_inc_ref(v_pos_1776_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v_pos_1776_);
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_pos_1776_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_err_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
lean_inc(v_idx_1777_);
v_idx_1754_ = v_idx_1777_;
v___y_1755_ = v___x_1788_;
v_pos_1756_ = v_pos_1776_;
v_idx_1757_ = v_idx_1777_;
goto v___jp_1753_;
}
}
}
}
}
v___jp_1792_:
{
uint8_t v___x_1797_; 
v___x_1797_ = lean_nat_dec_eq(v_idx_1793_, v_idx_1796_);
lean_dec(v_idx_1793_);
if (v___x_1797_ == 0)
{
lean_dec(v_idx_1796_);
lean_dec_ref(v_pos_1795_);
return v___y_1794_;
}
else
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
lean_dec_ref(v___y_1794_);
v___x_1798_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129);
lean_inc_ref(v_pos_1795_);
v___x_1799_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1798_, v___f_1152_, v_pos_1795_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_dec_ref(v_pos_1795_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_dec(v_idx_1796_);
return v___x_1799_;
}
else
{
lean_object* v_pos_1800_; lean_object* v_idx_1801_; 
v_pos_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_pos_1800_);
v_idx_1801_ = lean_ctor_get(v_pos_1800_, 1);
lean_inc(v_idx_1801_);
v_idx_1774_ = v_idx_1796_;
v___y_1775_ = v___x_1799_;
v_pos_1776_ = v_pos_1800_;
v_idx_1777_ = v_idx_1801_;
goto v___jp_1773_;
}
}
else
{
lean_object* v_err_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
v_err_1802_ = lean_ctor_get(v___x_1799_, 1);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1809_ == 0)
{
lean_object* v_unused_1810_; 
v_unused_1810_ = lean_ctor_get(v___x_1799_, 0);
lean_dec(v_unused_1810_);
v___x_1804_ = v___x_1799_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_err_1802_);
lean_dec(v___x_1799_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
lean_inc_ref(v_pos_1795_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v_pos_1795_);
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_pos_1795_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_err_1802_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
lean_inc(v_idx_1796_);
v_idx_1774_ = v_idx_1796_;
v___y_1775_ = v___x_1807_;
v_pos_1776_ = v_pos_1795_;
v_idx_1777_ = v_idx_1796_;
goto v___jp_1773_;
}
}
}
}
}
v___jp_1812_:
{
uint8_t v___x_1817_; 
v___x_1817_ = lean_nat_dec_eq(v_idx_1813_, v_idx_1816_);
lean_dec(v_idx_1813_);
if (v___x_1817_ == 0)
{
lean_dec(v_idx_1816_);
lean_dec_ref(v_pos_1815_);
return v___y_1814_;
}
else
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_dec_ref(v___y_1814_);
v___x_1818_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133);
lean_inc_ref(v_pos_1815_);
v___x_1819_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1818_, v___f_1811_, v_pos_1815_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_dec_ref(v_pos_1815_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_dec(v_idx_1816_);
return v___x_1819_;
}
else
{
lean_object* v_pos_1820_; lean_object* v_idx_1821_; 
v_pos_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_pos_1820_);
v_idx_1821_ = lean_ctor_get(v_pos_1820_, 1);
lean_inc(v_idx_1821_);
v_idx_1793_ = v_idx_1816_;
v___y_1794_ = v___x_1819_;
v_pos_1795_ = v_pos_1820_;
v_idx_1796_ = v_idx_1821_;
goto v___jp_1792_;
}
}
else
{
lean_object* v_err_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
v_err_1822_ = lean_ctor_get(v___x_1819_, 1);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1829_ == 0)
{
lean_object* v_unused_1830_; 
v_unused_1830_ = lean_ctor_get(v___x_1819_, 0);
lean_dec(v_unused_1830_);
v___x_1824_ = v___x_1819_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_err_1822_);
lean_dec(v___x_1819_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
lean_inc_ref(v_pos_1815_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v_pos_1815_);
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_pos_1815_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_err_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_inc(v_idx_1816_);
v_idx_1793_ = v_idx_1816_;
v___y_1794_ = v___x_1827_;
v_pos_1795_ = v_pos_1815_;
v_idx_1796_ = v_idx_1816_;
goto v___jp_1792_;
}
}
}
}
}
v___jp_1831_:
{
uint8_t v___x_1836_; 
v___x_1836_ = lean_nat_dec_eq(v_idx_1832_, v_idx_1835_);
lean_dec(v_idx_1832_);
if (v___x_1836_ == 0)
{
lean_dec(v_idx_1835_);
lean_dec_ref(v_pos_1834_);
return v___y_1833_;
}
else
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
lean_dec_ref(v___y_1833_);
v___x_1837_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136);
lean_inc_ref(v_pos_1834_);
v___x_1838_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1837_, v___f_1151_, v_pos_1834_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_dec_ref(v_pos_1834_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_dec(v_idx_1835_);
return v___x_1838_;
}
else
{
lean_object* v_pos_1839_; lean_object* v_idx_1840_; 
v_pos_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_pos_1839_);
v_idx_1840_ = lean_ctor_get(v_pos_1839_, 1);
lean_inc(v_idx_1840_);
v_idx_1813_ = v_idx_1835_;
v___y_1814_ = v___x_1838_;
v_pos_1815_ = v_pos_1839_;
v_idx_1816_ = v_idx_1840_;
goto v___jp_1812_;
}
}
else
{
lean_object* v_err_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
v_err_1841_ = lean_ctor_get(v___x_1838_, 1);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1848_ == 0)
{
lean_object* v_unused_1849_; 
v_unused_1849_ = lean_ctor_get(v___x_1838_, 0);
lean_dec(v_unused_1849_);
v___x_1843_ = v___x_1838_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_err_1841_);
lean_dec(v___x_1838_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
lean_inc_ref(v_pos_1834_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v_pos_1834_);
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_pos_1834_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_err_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_inc(v_idx_1835_);
v_idx_1813_ = v_idx_1835_;
v___y_1814_ = v___x_1846_;
v_pos_1815_ = v_pos_1834_;
v_idx_1816_ = v_idx_1835_;
goto v___jp_1812_;
}
}
}
}
}
v___jp_1851_:
{
uint8_t v___x_1856_; 
v___x_1856_ = lean_nat_dec_eq(v_idx_1852_, v_idx_1855_);
lean_dec(v_idx_1852_);
if (v___x_1856_ == 0)
{
lean_dec(v_idx_1855_);
lean_dec_ref(v_pos_1854_);
return v___y_1853_;
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
lean_dec_ref(v___y_1853_);
v___x_1857_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140);
lean_inc_ref(v_pos_1854_);
v___x_1858_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1857_, v___f_1850_, v_pos_1854_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_dec_ref(v_pos_1854_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_dec(v_idx_1855_);
return v___x_1858_;
}
else
{
lean_object* v_pos_1859_; lean_object* v_idx_1860_; 
v_pos_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_pos_1859_);
v_idx_1860_ = lean_ctor_get(v_pos_1859_, 1);
lean_inc(v_idx_1860_);
v_idx_1832_ = v_idx_1855_;
v___y_1833_ = v___x_1858_;
v_pos_1834_ = v_pos_1859_;
v_idx_1835_ = v_idx_1860_;
goto v___jp_1831_;
}
}
else
{
lean_object* v_err_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
v_err_1861_ = lean_ctor_get(v___x_1858_, 1);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1868_ == 0)
{
lean_object* v_unused_1869_; 
v_unused_1869_ = lean_ctor_get(v___x_1858_, 0);
lean_dec(v_unused_1869_);
v___x_1863_ = v___x_1858_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_err_1861_);
lean_dec(v___x_1858_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
lean_inc_ref(v_pos_1854_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v_pos_1854_);
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_pos_1854_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_err_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
lean_inc(v_idx_1855_);
v_idx_1832_ = v_idx_1855_;
v___y_1833_ = v___x_1866_;
v_pos_1834_ = v_pos_1854_;
v_idx_1835_ = v_idx_1855_;
goto v___jp_1831_;
}
}
}
}
}
v___jp_1870_:
{
uint8_t v___x_1875_; 
v___x_1875_ = lean_nat_dec_eq(v_idx_1871_, v_idx_1874_);
lean_dec(v_idx_1871_);
if (v___x_1875_ == 0)
{
lean_dec(v_idx_1874_);
lean_dec_ref(v_pos_1873_);
return v___y_1872_;
}
else
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
lean_dec_ref(v___y_1872_);
v___x_1876_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143);
lean_inc_ref(v_pos_1873_);
v___x_1877_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1876_, v___f_1150_, v_pos_1873_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_dec_ref(v_pos_1873_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_dec(v_idx_1874_);
return v___x_1877_;
}
else
{
lean_object* v_pos_1878_; lean_object* v_idx_1879_; 
v_pos_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_pos_1878_);
v_idx_1879_ = lean_ctor_get(v_pos_1878_, 1);
lean_inc(v_idx_1879_);
v_idx_1852_ = v_idx_1874_;
v___y_1853_ = v___x_1877_;
v_pos_1854_ = v_pos_1878_;
v_idx_1855_ = v_idx_1879_;
goto v___jp_1851_;
}
}
else
{
lean_object* v_err_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
v_err_1880_ = lean_ctor_get(v___x_1877_, 1);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1887_ == 0)
{
lean_object* v_unused_1888_; 
v_unused_1888_ = lean_ctor_get(v___x_1877_, 0);
lean_dec(v_unused_1888_);
v___x_1882_ = v___x_1877_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_err_1880_);
lean_dec(v___x_1877_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
lean_inc_ref(v_pos_1873_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v_pos_1873_);
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_pos_1873_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_err_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_inc(v_idx_1874_);
v_idx_1852_ = v_idx_1874_;
v___y_1853_ = v___x_1885_;
v_pos_1854_ = v_pos_1873_;
v_idx_1855_ = v_idx_1874_;
goto v___jp_1851_;
}
}
}
}
}
v___jp_1890_:
{
uint8_t v___x_1895_; 
v___x_1895_ = lean_nat_dec_eq(v_idx_1891_, v_idx_1894_);
lean_dec(v_idx_1891_);
if (v___x_1895_ == 0)
{
lean_dec(v_idx_1894_);
lean_dec_ref(v_pos_1893_);
return v___y_1892_;
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_dec_ref(v___y_1892_);
v___x_1896_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147);
lean_inc_ref(v_pos_1893_);
v___x_1897_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1896_, v___f_1889_, v_pos_1893_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_dec_ref(v_pos_1893_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_dec(v_idx_1894_);
return v___x_1897_;
}
else
{
lean_object* v_pos_1898_; lean_object* v_idx_1899_; 
v_pos_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_pos_1898_);
v_idx_1899_ = lean_ctor_get(v_pos_1898_, 1);
lean_inc(v_idx_1899_);
v_idx_1871_ = v_idx_1894_;
v___y_1872_ = v___x_1897_;
v_pos_1873_ = v_pos_1898_;
v_idx_1874_ = v_idx_1899_;
goto v___jp_1870_;
}
}
else
{
lean_object* v_err_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
v_err_1900_ = lean_ctor_get(v___x_1897_, 1);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1907_ == 0)
{
lean_object* v_unused_1908_; 
v_unused_1908_ = lean_ctor_get(v___x_1897_, 0);
lean_dec(v_unused_1908_);
v___x_1902_ = v___x_1897_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_err_1900_);
lean_dec(v___x_1897_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
lean_inc_ref(v_pos_1893_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v_pos_1893_);
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_pos_1893_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v_err_1900_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_inc(v_idx_1894_);
v_idx_1871_ = v_idx_1894_;
v___y_1872_ = v___x_1905_;
v_pos_1873_ = v_pos_1893_;
v_idx_1874_ = v_idx_1894_;
goto v___jp_1870_;
}
}
}
}
}
v___jp_1909_:
{
uint8_t v___x_1914_; 
v___x_1914_ = lean_nat_dec_eq(v_idx_1910_, v_idx_1913_);
lean_dec(v_idx_1910_);
if (v___x_1914_ == 0)
{
lean_dec(v_idx_1913_);
lean_dec_ref(v_pos_1912_);
return v___y_1911_;
}
else
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
lean_dec_ref(v___y_1911_);
v___x_1915_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150);
lean_inc_ref(v_pos_1912_);
v___x_1916_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1915_, v___f_1149_, v_pos_1912_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_dec_ref(v_pos_1912_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_dec(v_idx_1913_);
return v___x_1916_;
}
else
{
lean_object* v_pos_1917_; lean_object* v_idx_1918_; 
v_pos_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_pos_1917_);
v_idx_1918_ = lean_ctor_get(v_pos_1917_, 1);
lean_inc(v_idx_1918_);
v_idx_1891_ = v_idx_1913_;
v___y_1892_ = v___x_1916_;
v_pos_1893_ = v_pos_1917_;
v_idx_1894_ = v_idx_1918_;
goto v___jp_1890_;
}
}
else
{
lean_object* v_err_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
v_err_1919_ = lean_ctor_get(v___x_1916_, 1);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1926_ == 0)
{
lean_object* v_unused_1927_; 
v_unused_1927_ = lean_ctor_get(v___x_1916_, 0);
lean_dec(v_unused_1927_);
v___x_1921_ = v___x_1916_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_err_1919_);
lean_dec(v___x_1916_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
lean_inc_ref(v_pos_1912_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v_pos_1912_);
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_pos_1912_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_err_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_inc(v_idx_1913_);
v_idx_1891_ = v_idx_1913_;
v___y_1892_ = v___x_1924_;
v_pos_1893_ = v_pos_1912_;
v_idx_1894_ = v_idx_1913_;
goto v___jp_1890_;
}
}
}
}
}
v___jp_1929_:
{
uint8_t v___x_1934_; 
v___x_1934_ = lean_nat_dec_eq(v_idx_1930_, v_idx_1933_);
lean_dec(v_idx_1930_);
if (v___x_1934_ == 0)
{
lean_dec(v_idx_1933_);
lean_dec_ref(v_pos_1932_);
return v___y_1931_;
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
lean_dec_ref(v___y_1931_);
v___x_1935_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154);
lean_inc_ref(v_pos_1932_);
v___x_1936_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1935_, v___f_1928_, v_pos_1932_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_dec_ref(v_pos_1932_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_dec(v_idx_1933_);
return v___x_1936_;
}
else
{
lean_object* v_pos_1937_; lean_object* v_idx_1938_; 
v_pos_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_pos_1937_);
v_idx_1938_ = lean_ctor_get(v_pos_1937_, 1);
lean_inc(v_idx_1938_);
v_idx_1910_ = v_idx_1933_;
v___y_1911_ = v___x_1936_;
v_pos_1912_ = v_pos_1937_;
v_idx_1913_ = v_idx_1938_;
goto v___jp_1909_;
}
}
else
{
lean_object* v_err_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
v_err_1939_ = lean_ctor_get(v___x_1936_, 1);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1946_ == 0)
{
lean_object* v_unused_1947_; 
v_unused_1947_ = lean_ctor_get(v___x_1936_, 0);
lean_dec(v_unused_1947_);
v___x_1941_ = v___x_1936_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_err_1939_);
lean_dec(v___x_1936_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
lean_inc_ref(v_pos_1932_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v_pos_1932_);
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_pos_1932_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_err_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_inc(v_idx_1933_);
v_idx_1910_ = v_idx_1933_;
v___y_1911_ = v___x_1944_;
v_pos_1912_ = v_pos_1932_;
v_idx_1913_ = v_idx_1933_;
goto v___jp_1909_;
}
}
}
}
}
v___jp_1948_:
{
lean_object* v_idx_1951_; lean_object* v_idx_1952_; uint8_t v___x_1953_; 
v_idx_1951_ = lean_ctor_get(v_a_1147_, 1);
lean_inc(v_idx_1951_);
lean_dec_ref(v_a_1147_);
v_idx_1952_ = lean_ctor_get(v_pos_1950_, 1);
lean_inc(v_idx_1952_);
v___x_1953_ = lean_nat_dec_eq(v_idx_1951_, v_idx_1952_);
lean_dec(v_idx_1951_);
if (v___x_1953_ == 0)
{
lean_dec(v_idx_1952_);
lean_dec_ref(v_pos_1950_);
return v___y_1949_;
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_dec_ref(v___y_1949_);
v___x_1954_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157);
lean_inc_ref(v_pos_1950_);
v___x_1955_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1954_, v___f_1148_, v_pos_1950_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_dec_ref(v_pos_1950_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_dec(v_idx_1952_);
return v___x_1955_;
}
else
{
lean_object* v_pos_1956_; lean_object* v_idx_1957_; 
v_pos_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_pos_1956_);
v_idx_1957_ = lean_ctor_get(v_pos_1956_, 1);
lean_inc(v_idx_1957_);
v_idx_1930_ = v_idx_1952_;
v___y_1931_ = v___x_1955_;
v_pos_1932_ = v_pos_1956_;
v_idx_1933_ = v_idx_1957_;
goto v___jp_1929_;
}
}
else
{
lean_object* v_err_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
v_err_1958_ = lean_ctor_get(v___x_1955_, 1);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; 
v_unused_1966_ = lean_ctor_get(v___x_1955_, 0);
lean_dec(v_unused_1966_);
v___x_1960_ = v___x_1955_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_err_1958_);
lean_dec(v___x_1955_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
lean_inc_ref(v_pos_1950_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v_pos_1950_);
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_pos_1950_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_err_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
lean_inc(v_idx_1952_);
v_idx_1930_ = v_idx_1952_;
v___y_1931_ = v___x_1963_;
v_pos_1932_ = v_pos_1950_;
v_idx_1933_ = v_idx_1952_;
goto v___jp_1929_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(uint8_t v_b_1980_){
_start:
{
uint8_t v___x_1981_; uint8_t v___x_1982_; 
v___x_1981_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v___x_1982_ = lean_uint8_dec_eq(v_b_1980_, v___x_1981_);
if (v___x_1982_ == 0)
{
uint8_t v___x_1983_; 
v___x_1983_ = 1;
return v___x_1983_;
}
else
{
uint8_t v___x_1984_; 
v___x_1984_ = 0;
return v___x_1984_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0___boxed(lean_object* v_b_1985_){
_start:
{
uint8_t v_b_boxed_1986_; uint8_t v_res_1987_; lean_object* v_r_1988_; 
v_b_boxed_1986_ = lean_unbox(v_b_1985_);
v_res_1987_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(v_b_boxed_1986_);
v_r_1988_ = lean_box(v_res_1987_);
return v_r_1988_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(lean_object* v_limits_1993_, lean_object* v_a_1994_){
_start:
{
lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v_maxUriLength_2000_; lean_object* v___f_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v_snd_2004_; lean_object* v_snd_2005_; uint8_t v___x_2006_; 
v_maxUriLength_2000_ = lean_ctor_get(v_limits_1993_, 4);
v___f_2001_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__0));
v___x_2002_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1994_);
v___x_2003_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2001_, v_maxUriLength_2000_, v___x_2002_, v_a_1994_);
v_snd_2004_ = lean_ctor_get(v___x_2003_, 1);
lean_inc(v_snd_2004_);
v_snd_2005_ = lean_ctor_get(v_snd_2004_, 1);
v___x_2006_ = lean_unbox(v_snd_2005_);
if (v___x_2006_ == 0)
{
lean_object* v_fst_2007_; lean_object* v_fst_2008_; lean_object* v_array_2009_; lean_object* v_idx_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2037_; 
v_fst_2007_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_fst_2007_);
lean_dec_ref(v___x_2003_);
v_fst_2008_ = lean_ctor_get(v_snd_2004_, 0);
lean_inc(v_fst_2008_);
lean_dec(v_snd_2004_);
v_array_2009_ = lean_ctor_get(v_a_1994_, 0);
v_idx_2010_ = lean_ctor_get(v_a_1994_, 1);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_a_1994_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2012_ = v_a_1994_;
v_isShared_2013_ = v_isSharedCheck_2037_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_idx_2010_);
lean_inc(v_array_2009_);
lean_dec(v_a_1994_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2037_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v_lower_2015_; lean_object* v_upper_2016_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___y_2034_; uint8_t v___x_2036_; 
v___x_2031_ = lean_nat_add(v_idx_2010_, v_fst_2007_);
lean_dec(v_fst_2007_);
v___x_2032_ = lean_byte_array_size(v_array_2009_);
v___x_2036_ = lean_nat_dec_le(v_idx_2010_, v___x_2002_);
if (v___x_2036_ == 0)
{
v___y_2034_ = v_idx_2010_;
goto v___jp_2033_;
}
else
{
lean_dec(v_idx_2010_);
v___y_2034_ = v___x_2002_;
goto v___jp_2033_;
}
v___jp_2014_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; uint8_t v___x_2019_; 
v___x_2017_ = l_ByteArray_toByteSlice(v_array_2009_, v_lower_2015_, v_upper_2016_);
v___x_2018_ = l_ByteSlice_size(v___x_2017_);
v___x_2019_ = lean_nat_dec_eq(v___x_2018_, v_maxUriLength_2000_);
lean_dec(v___x_2018_);
if (v___x_2019_ == 0)
{
lean_del_object(v___x_2012_);
v___y_1996_ = v___x_2017_;
v___y_1997_ = v_fst_2008_;
goto v___jp_1995_;
}
else
{
lean_object* v_array_2020_; lean_object* v_idx_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; 
v_array_2020_ = lean_ctor_get(v_fst_2008_, 0);
v_idx_2021_ = lean_ctor_get(v_fst_2008_, 1);
v___x_2022_ = lean_byte_array_size(v_array_2020_);
v___x_2023_ = lean_nat_dec_lt(v_idx_2021_, v___x_2022_);
if (v___x_2023_ == 0)
{
lean_del_object(v___x_2012_);
v___y_1996_ = v___x_2017_;
v___y_1997_ = v_fst_2008_;
goto v___jp_1995_;
}
else
{
uint8_t v___x_2024_; uint8_t v___x_2025_; uint8_t v___x_2026_; 
v___x_2024_ = lean_byte_array_fget(v_array_2020_, v_idx_2021_);
v___x_2025_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v___x_2026_ = lean_uint8_dec_eq(v___x_2024_, v___x_2025_);
if (v___x_2026_ == 0)
{
if (v___x_2023_ == 0)
{
lean_del_object(v___x_2012_);
v___y_1996_ = v___x_2017_;
v___y_1997_ = v_fst_2008_;
goto v___jp_1995_;
}
else
{
if (v___x_2019_ == 0)
{
lean_del_object(v___x_2012_);
v___y_1996_ = v___x_2017_;
v___y_1997_ = v_fst_2008_;
goto v___jp_1995_;
}
else
{
lean_object* v___x_2027_; lean_object* v___x_2029_; 
lean_dec_ref(v___x_2017_);
v___x_2027_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__2));
if (v_isShared_2013_ == 0)
{
lean_ctor_set_tag(v___x_2012_, 1);
lean_ctor_set(v___x_2012_, 1, v___x_2027_);
lean_ctor_set(v___x_2012_, 0, v_fst_2008_);
v___x_2029_ = v___x_2012_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_fst_2008_);
lean_ctor_set(v_reuseFailAlloc_2030_, 1, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
else
{
lean_del_object(v___x_2012_);
v___y_1996_ = v___x_2017_;
v___y_1997_ = v_fst_2008_;
goto v___jp_1995_;
}
}
}
}
v___jp_2033_:
{
uint8_t v___x_2035_; 
v___x_2035_ = lean_nat_dec_le(v___x_2031_, v___x_2032_);
if (v___x_2035_ == 0)
{
lean_dec(v___x_2031_);
v_lower_2015_ = v___y_2034_;
v_upper_2016_ = v___x_2032_;
goto v___jp_2014_;
}
else
{
v_lower_2015_ = v___y_2034_;
v_upper_2016_ = v___x_2031_;
goto v___jp_2014_;
}
}
}
}
else
{
lean_object* v_fst_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2046_; 
lean_dec_ref(v___x_2003_);
lean_dec_ref(v_a_1994_);
v_fst_2038_ = lean_ctor_get(v_snd_2004_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_snd_2004_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; 
v_unused_2047_ = lean_ctor_get(v_snd_2004_, 1);
lean_dec(v_unused_2047_);
v___x_2040_ = v_snd_2004_;
v_isShared_2041_ = v_isSharedCheck_2046_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_fst_2038_);
lean_dec(v_snd_2004_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2046_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2042_ = lean_box(0);
if (v_isShared_2041_ == 0)
{
lean_ctor_set_tag(v___x_2040_, 1);
lean_ctor_set(v___x_2040_, 1, v___x_2042_);
v___x_2044_ = v___x_2040_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_fst_2038_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
v___jp_1995_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = l_ByteSlice_toByteArray(v___y_1996_);
v___x_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___y_1997_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
return v___x_1999_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___boxed(lean_object* v_limits_2048_, lean_object* v_a_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_2048_, v_a_2049_);
lean_dec_ref(v_limits_2048_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0(lean_object* v___x_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v___x_2056_; 
v___x_2056_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_2054_, v___y_2055_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_pos_2057_; lean_object* v_array_2058_; lean_object* v_idx_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; 
v_pos_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_pos_2057_);
v_array_2058_ = lean_ctor_get(v_pos_2057_, 0);
v_idx_2059_ = lean_ctor_get(v_pos_2057_, 1);
v___x_2060_ = lean_byte_array_size(v_array_2058_);
v___x_2061_ = lean_nat_dec_lt(v_idx_2059_, v___x_2060_);
if (v___x_2061_ == 0)
{
lean_dec(v_pos_2057_);
return v___x_2056_;
}
else
{
lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2069_; 
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2069_ == 0)
{
lean_object* v_unused_2070_; lean_object* v_unused_2071_; 
v_unused_2070_ = lean_ctor_get(v___x_2056_, 1);
lean_dec(v_unused_2070_);
v_unused_2071_ = lean_ctor_get(v___x_2056_, 0);
lean_dec(v_unused_2071_);
v___x_2063_ = v___x_2056_;
v_isShared_2064_ = v_isSharedCheck_2069_;
goto v_resetjp_2062_;
}
else
{
lean_dec(v___x_2056_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2069_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2065_; lean_object* v___x_2067_; 
v___x_2065_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__1));
if (v_isShared_2064_ == 0)
{
lean_ctor_set_tag(v___x_2063_, 1);
lean_ctor_set(v___x_2063_, 1, v___x_2065_);
v___x_2067_ = v___x_2063_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_pos_2057_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v___x_2065_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
else
{
return v___x_2056_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(lean_object* v_limits_2082_, lean_object* v_a_2083_){
_start:
{
lean_object* v___y_2085_; lean_object* v_pos_2086_; lean_object* v_res_2087_; lean_object* v_pos_2091_; lean_object* v_res_2092_; lean_object* v___x_2131_; 
v___x_2131_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_2082_, v_a_2083_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_pos_2132_; lean_object* v_res_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2163_; 
v_pos_2132_ = lean_ctor_get(v___x_2131_, 0);
v_res_2133_ = lean_ctor_get(v___x_2131_, 1);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2135_ = v___x_2131_;
v_isShared_2136_ = v_isSharedCheck_2163_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_res_2133_);
lean_inc(v_pos_2132_);
lean_dec(v___x_2131_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2163_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v_array_2137_; lean_object* v_idx_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; 
v_array_2137_ = lean_ctor_get(v_pos_2132_, 0);
v_idx_2138_ = lean_ctor_get(v_pos_2132_, 1);
v___x_2139_ = lean_byte_array_size(v_array_2137_);
v___x_2140_ = lean_nat_dec_lt(v_idx_2138_, v___x_2139_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; lean_object* v___x_2143_; 
lean_dec(v_res_2133_);
v___x_2141_ = lean_box(0);
if (v_isShared_2136_ == 0)
{
lean_ctor_set_tag(v___x_2135_, 1);
lean_ctor_set(v___x_2135_, 1, v___x_2141_);
v___x_2143_ = v___x_2135_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_pos_2132_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
else
{
uint8_t v___x_2145_; uint8_t v_got_2146_; uint8_t v___x_2147_; 
v___x_2145_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v_got_2146_ = lean_byte_array_fget(v_array_2137_, v_idx_2138_);
v___x_2147_ = lean_uint8_dec_eq(v_got_2146_, v___x_2145_);
if (v___x_2147_ == 0)
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
lean_dec(v_res_2133_);
v___x_2148_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7);
if (v_isShared_2136_ == 0)
{
lean_ctor_set_tag(v___x_2135_, 1);
lean_ctor_set(v___x_2135_, 1, v___x_2148_);
v___x_2150_ = v___x_2135_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_pos_2132_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
else
{
lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2160_; 
lean_inc(v_idx_2138_);
lean_inc_ref(v_array_2137_);
lean_del_object(v___x_2135_);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_pos_2132_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; lean_object* v_unused_2162_; 
v_unused_2161_ = lean_ctor_get(v_pos_2132_, 1);
lean_dec(v_unused_2161_);
v_unused_2162_ = lean_ctor_get(v_pos_2132_, 0);
lean_dec(v_unused_2162_);
v___x_2153_ = v_pos_2132_;
v_isShared_2154_ = v_isSharedCheck_2160_;
goto v_resetjp_2152_;
}
else
{
lean_dec(v_pos_2132_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2160_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2155_ = lean_unsigned_to_nat(1u);
v___x_2156_ = lean_nat_add(v_idx_2138_, v___x_2155_);
lean_dec(v_idx_2138_);
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
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_array_2137_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
v_pos_2091_ = v___x_2158_;
v_res_2092_ = v_res_2133_;
goto v___jp_2090_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_pos_2164_; lean_object* v_res_2165_; 
v_pos_2164_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_pos_2164_);
v_res_2165_ = lean_ctor_get(v___x_2131_, 1);
lean_inc(v_res_2165_);
lean_dec_ref(v___x_2131_);
v_pos_2091_ = v_pos_2164_;
v_res_2092_ = v_res_2165_;
goto v___jp_2090_;
}
else
{
lean_object* v_pos_2166_; lean_object* v_err_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
v_pos_2166_ = lean_ctor_get(v___x_2131_, 0);
v_err_2167_ = lean_ctor_get(v___x_2131_, 1);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2131_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_err_2167_);
lean_inc(v_pos_2166_);
lean_dec(v___x_2131_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_pos_2166_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v_err_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
v___jp_2084_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___y_2085_);
lean_ctor_set(v___x_2088_, 1, v_res_2087_);
v___x_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2089_, 0, v_pos_2086_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
return v___x_2089_;
}
v___jp_2090_:
{
lean_object* v___f_2093_; lean_object* v___x_2094_; 
v___f_2093_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___closed__1));
v___x_2094_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_2093_, v_res_2092_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2103_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2103_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2103_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
lean_ctor_set_tag(v___x_2097_, 1);
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2101_; 
v___x_2101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2101_, 0, v_pos_2091_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
return v___x_2101_;
}
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2105_; 
v_a_2104_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2104_);
lean_dec_ref(v___x_2094_);
v___x_2105_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_pos_2091_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_pos_2106_; lean_object* v_res_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v_pos_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_pos_2106_);
v_res_2107_ = lean_ctor_get(v___x_2105_, 1);
lean_inc(v_res_2107_);
lean_dec_ref(v___x_2105_);
v___x_2108_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2109_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2108_, v_pos_2106_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_pos_2110_; 
v_pos_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_pos_2110_);
lean_dec_ref(v___x_2109_);
v___y_2085_ = v_a_2104_;
v_pos_2086_ = v_pos_2110_;
v_res_2087_ = v_res_2107_;
goto v___jp_2084_;
}
else
{
lean_object* v_pos_2111_; lean_object* v_err_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec(v_res_2107_);
lean_dec(v_a_2104_);
v_pos_2111_ = lean_ctor_get(v___x_2109_, 0);
v_err_2112_ = lean_ctor_get(v___x_2109_, 1);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2109_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_err_2112_);
lean_inc(v_pos_2111_);
lean_dec(v___x_2109_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_pos_2111_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v_err_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_pos_2120_; lean_object* v_res_2121_; 
v_pos_2120_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_pos_2120_);
v_res_2121_ = lean_ctor_get(v___x_2105_, 1);
lean_inc(v_res_2121_);
lean_dec_ref(v___x_2105_);
v___y_2085_ = v_a_2104_;
v_pos_2086_ = v_pos_2120_;
v_res_2087_ = v_res_2121_;
goto v___jp_2084_;
}
else
{
lean_object* v_pos_2122_; lean_object* v_err_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec(v_a_2104_);
v_pos_2122_ = lean_ctor_get(v___x_2105_, 0);
v_err_2123_ = lean_ctor_get(v___x_2105_, 1);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2105_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_err_2123_);
lean_inc(v_pos_2122_);
lean_dec(v___x_2105_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___boxed(lean_object* v_limits_2175_, lean_object* v_a_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_2175_, v_a_2176_);
lean_dec_ref(v_limits_2175_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine(lean_object* v_limits_2181_, lean_object* v_a_2182_){
_start:
{
lean_object* v___y_2184_; lean_object* v___y_2188_; uint8_t v___y_2189_; lean_object* v___y_2190_; uint8_t v___y_2191_; lean_object* v___y_2192_; lean_object* v_pos_2200_; uint8_t v_res_2201_; lean_object* v___x_2232_; 
v___x_2232_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_2181_, v_a_2182_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_pos_2233_; lean_object* v___x_2234_; 
v_pos_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_pos_2233_);
lean_dec_ref(v___x_2232_);
v___x_2234_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(v_pos_2233_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_pos_2235_; lean_object* v_res_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2267_; 
v_pos_2235_ = lean_ctor_get(v___x_2234_, 0);
v_res_2236_ = lean_ctor_get(v___x_2234_, 1);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2238_ = v___x_2234_;
v_isShared_2239_ = v_isSharedCheck_2267_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_res_2236_);
lean_inc(v_pos_2235_);
lean_dec(v___x_2234_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2267_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v_array_2240_; lean_object* v_idx_2241_; lean_object* v___x_2242_; uint8_t v___x_2243_; 
v_array_2240_ = lean_ctor_get(v_pos_2235_, 0);
v_idx_2241_ = lean_ctor_get(v_pos_2235_, 1);
v___x_2242_ = lean_byte_array_size(v_array_2240_);
v___x_2243_ = lean_nat_dec_lt(v_idx_2241_, v___x_2242_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; lean_object* v___x_2246_; 
lean_dec(v_res_2236_);
v___x_2244_ = lean_box(0);
if (v_isShared_2239_ == 0)
{
lean_ctor_set_tag(v___x_2238_, 1);
lean_ctor_set(v___x_2238_, 1, v___x_2244_);
v___x_2246_ = v___x_2238_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_pos_2235_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v___x_2244_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
else
{
uint8_t v___x_2248_; uint8_t v_got_2249_; uint8_t v___x_2250_; 
v___x_2248_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v_got_2249_ = lean_byte_array_fget(v_array_2240_, v_idx_2241_);
v___x_2250_ = lean_uint8_dec_eq(v_got_2249_, v___x_2248_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2251_; lean_object* v___x_2253_; 
lean_dec(v_res_2236_);
v___x_2251_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7);
if (v_isShared_2239_ == 0)
{
lean_ctor_set_tag(v___x_2238_, 1);
lean_ctor_set(v___x_2238_, 1, v___x_2251_);
v___x_2253_ = v___x_2238_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_pos_2235_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v___x_2251_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
else
{
lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2264_; 
lean_inc(v_idx_2241_);
lean_inc_ref(v_array_2240_);
lean_del_object(v___x_2238_);
v_isSharedCheck_2264_ = !lean_is_exclusive(v_pos_2235_);
if (v_isSharedCheck_2264_ == 0)
{
lean_object* v_unused_2265_; lean_object* v_unused_2266_; 
v_unused_2265_ = lean_ctor_get(v_pos_2235_, 1);
lean_dec(v_unused_2265_);
v_unused_2266_ = lean_ctor_get(v_pos_2235_, 0);
lean_dec(v_unused_2266_);
v___x_2256_ = v_pos_2235_;
v_isShared_2257_ = v_isSharedCheck_2264_;
goto v_resetjp_2255_;
}
else
{
lean_dec(v_pos_2235_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2264_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2261_; 
v___x_2258_ = lean_unsigned_to_nat(1u);
v___x_2259_ = lean_nat_add(v_idx_2241_, v___x_2258_);
lean_dec(v_idx_2241_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 1, v___x_2259_);
v___x_2261_ = v___x_2256_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_array_2240_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v___x_2259_);
v___x_2261_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
uint8_t v___x_2262_; 
v___x_2262_ = lean_unbox(v_res_2236_);
lean_dec(v_res_2236_);
v_pos_2200_ = v___x_2261_;
v_res_2201_ = v___x_2262_;
goto v___jp_2199_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_pos_2268_; lean_object* v_res_2269_; uint8_t v___x_2270_; 
v_pos_2268_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_pos_2268_);
v_res_2269_ = lean_ctor_get(v___x_2234_, 1);
lean_inc(v_res_2269_);
lean_dec_ref(v___x_2234_);
v___x_2270_ = lean_unbox(v_res_2269_);
lean_dec(v_res_2269_);
v_pos_2200_ = v_pos_2268_;
v_res_2201_ = v___x_2270_;
goto v___jp_2199_;
}
else
{
lean_object* v_pos_2271_; lean_object* v_err_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
v_pos_2271_ = lean_ctor_get(v___x_2234_, 0);
v_err_2272_ = lean_ctor_get(v___x_2234_, 1);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2234_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_err_2272_);
lean_inc(v_pos_2271_);
lean_dec(v___x_2234_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_pos_2271_);
lean_ctor_set(v_reuseFailAlloc_2278_, 1, v_err_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
}
else
{
lean_object* v_pos_2280_; lean_object* v_err_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
v_pos_2280_ = lean_ctor_get(v___x_2232_, 0);
v_err_2281_ = lean_ctor_get(v___x_2232_, 1);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2232_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_err_2281_);
lean_inc(v_pos_2280_);
lean_dec(v___x_2232_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_pos_2280_);
lean_ctor_set(v_reuseFailAlloc_2287_, 1, v_err_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
v___jp_2183_:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
v___x_2186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___y_2184_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
return v___x_2186_;
}
v___jp_2187_:
{
if (v___y_2189_ == 0)
{
lean_dec(v___y_2192_);
lean_dec(v___y_2188_);
v___y_2184_ = v___y_2190_;
goto v___jp_2183_;
}
else
{
lean_object* v___x_2193_; uint8_t v___x_2194_; 
v___x_2193_ = lean_unsigned_to_nat(0u);
v___x_2194_ = lean_nat_dec_eq(v___y_2192_, v___x_2193_);
lean_dec(v___y_2192_);
if (v___x_2194_ == 0)
{
lean_dec(v___y_2188_);
v___y_2184_ = v___y_2190_;
goto v___jp_2183_;
}
else
{
uint8_t v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2195_ = 0;
v___x_2196_ = l_Std_Http_Headers_empty;
v___x_2197_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_2197_, 0, v___y_2188_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
lean_ctor_set_uint8(v___x_2197_, sizeof(void*)*2, v___y_2191_);
lean_ctor_set_uint8(v___x_2197_, sizeof(void*)*2 + 1, v___x_2195_);
v___x_2198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2198_, 0, v___y_2190_);
lean_ctor_set(v___x_2198_, 1, v___x_2197_);
return v___x_2198_;
}
}
}
v___jp_2199_:
{
lean_object* v___x_2202_; 
v___x_2202_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_2181_, v_pos_2200_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_res_2203_; lean_object* v_snd_2204_; lean_object* v_pos_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2221_; 
v_res_2203_ = lean_ctor_get(v___x_2202_, 1);
lean_inc(v_res_2203_);
v_snd_2204_ = lean_ctor_get(v_res_2203_, 1);
lean_inc(v_snd_2204_);
v_pos_2205_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2221_ == 0)
{
lean_object* v_unused_2222_; 
v_unused_2222_ = lean_ctor_get(v___x_2202_, 1);
lean_dec(v_unused_2222_);
v___x_2207_ = v___x_2202_;
v_isShared_2208_ = v_isSharedCheck_2221_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_pos_2205_);
lean_dec(v___x_2202_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2221_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v_fst_2209_; lean_object* v_fst_2210_; lean_object* v_snd_2211_; lean_object* v___x_2212_; uint8_t v___x_2213_; 
v_fst_2209_ = lean_ctor_get(v_res_2203_, 0);
lean_inc(v_fst_2209_);
lean_dec(v_res_2203_);
v_fst_2210_ = lean_ctor_get(v_snd_2204_, 0);
lean_inc(v_fst_2210_);
v_snd_2211_ = lean_ctor_get(v_snd_2204_, 1);
lean_inc(v_snd_2211_);
lean_dec(v_snd_2204_);
v___x_2212_ = lean_unsigned_to_nat(1u);
v___x_2213_ = lean_nat_dec_eq(v_fst_2210_, v___x_2212_);
lean_dec(v_fst_2210_);
if (v___x_2213_ == 0)
{
lean_del_object(v___x_2207_);
v___y_2188_ = v_fst_2209_;
v___y_2189_ = v___x_2213_;
v___y_2190_ = v_pos_2205_;
v___y_2191_ = v_res_2201_;
v___y_2192_ = v_snd_2211_;
goto v___jp_2187_;
}
else
{
uint8_t v___x_2214_; 
v___x_2214_ = lean_nat_dec_eq(v_snd_2211_, v___x_2212_);
if (v___x_2214_ == 0)
{
lean_del_object(v___x_2207_);
v___y_2188_ = v_fst_2209_;
v___y_2189_ = v___x_2213_;
v___y_2190_ = v_pos_2205_;
v___y_2191_ = v_res_2201_;
v___y_2192_ = v_snd_2211_;
goto v___jp_2187_;
}
else
{
uint8_t v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2219_; 
lean_dec(v_snd_2211_);
v___x_2215_ = 1;
v___x_2216_ = l_Std_Http_Headers_empty;
v___x_2217_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_2217_, 0, v_fst_2209_);
lean_ctor_set(v___x_2217_, 1, v___x_2216_);
lean_ctor_set_uint8(v___x_2217_, sizeof(void*)*2, v_res_2201_);
lean_ctor_set_uint8(v___x_2217_, sizeof(void*)*2 + 1, v___x_2215_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 1, v___x_2217_);
v___x_2219_ = v___x_2207_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_pos_2205_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v___x_2217_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
}
else
{
lean_object* v_pos_2223_; lean_object* v_err_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
v_pos_2223_ = lean_ctor_get(v___x_2202_, 0);
v_err_2224_ = lean_ctor_get(v___x_2202_, 1);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2202_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_err_2224_);
lean_inc(v_pos_2223_);
lean_dec(v___x_2202_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_pos_2223_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v_err_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine___boxed(lean_object* v_limits_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Std_Http_Protocol_H1_parseRequestLine(v_limits_2289_, v_a_2290_);
lean_dec_ref(v_limits_2289_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion(lean_object* v_limits_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v_pos_2295_; uint8_t v_res_2296_; lean_object* v___x_2338_; 
v___x_2338_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_2292_, v_a_2293_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_pos_2339_; lean_object* v___x_2340_; 
v_pos_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_pos_2339_);
lean_dec_ref(v___x_2338_);
v___x_2340_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(v_pos_2339_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_pos_2341_; lean_object* v_res_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2373_; 
v_pos_2341_ = lean_ctor_get(v___x_2340_, 0);
v_res_2342_ = lean_ctor_get(v___x_2340_, 1);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2344_ = v___x_2340_;
v_isShared_2345_ = v_isSharedCheck_2373_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_res_2342_);
lean_inc(v_pos_2341_);
lean_dec(v___x_2340_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2373_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v_array_2346_; lean_object* v_idx_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; 
v_array_2346_ = lean_ctor_get(v_pos_2341_, 0);
v_idx_2347_ = lean_ctor_get(v_pos_2341_, 1);
v___x_2348_ = lean_byte_array_size(v_array_2346_);
v___x_2349_ = lean_nat_dec_lt(v_idx_2347_, v___x_2348_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; lean_object* v___x_2352_; 
lean_dec(v_res_2342_);
v___x_2350_ = lean_box(0);
if (v_isShared_2345_ == 0)
{
lean_ctor_set_tag(v___x_2344_, 1);
lean_ctor_set(v___x_2344_, 1, v___x_2350_);
v___x_2352_ = v___x_2344_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_pos_2341_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v___x_2350_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
else
{
uint8_t v___x_2354_; uint8_t v_got_2355_; uint8_t v___x_2356_; 
v___x_2354_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v_got_2355_ = lean_byte_array_fget(v_array_2346_, v_idx_2347_);
v___x_2356_ = lean_uint8_dec_eq(v_got_2355_, v___x_2354_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; lean_object* v___x_2359_; 
lean_dec(v_res_2342_);
v___x_2357_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7);
if (v_isShared_2345_ == 0)
{
lean_ctor_set_tag(v___x_2344_, 1);
lean_ctor_set(v___x_2344_, 1, v___x_2357_);
v___x_2359_ = v___x_2344_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_pos_2341_);
lean_ctor_set(v_reuseFailAlloc_2360_, 1, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
else
{
lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2370_; 
lean_inc(v_idx_2347_);
lean_inc_ref(v_array_2346_);
lean_del_object(v___x_2344_);
v_isSharedCheck_2370_ = !lean_is_exclusive(v_pos_2341_);
if (v_isSharedCheck_2370_ == 0)
{
lean_object* v_unused_2371_; lean_object* v_unused_2372_; 
v_unused_2371_ = lean_ctor_get(v_pos_2341_, 1);
lean_dec(v_unused_2371_);
v_unused_2372_ = lean_ctor_get(v_pos_2341_, 0);
lean_dec(v_unused_2372_);
v___x_2362_ = v_pos_2341_;
v_isShared_2363_ = v_isSharedCheck_2370_;
goto v_resetjp_2361_;
}
else
{
lean_dec(v_pos_2341_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2370_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2367_; 
v___x_2364_ = lean_unsigned_to_nat(1u);
v___x_2365_ = lean_nat_add(v_idx_2347_, v___x_2364_);
lean_dec(v_idx_2347_);
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 1, v___x_2365_);
v___x_2367_ = v___x_2362_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_array_2346_);
lean_ctor_set(v_reuseFailAlloc_2369_, 1, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
uint8_t v___x_2368_; 
v___x_2368_ = lean_unbox(v_res_2342_);
lean_dec(v_res_2342_);
v_pos_2295_ = v___x_2367_;
v_res_2296_ = v___x_2368_;
goto v___jp_2294_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_pos_2374_; lean_object* v_res_2375_; uint8_t v___x_2376_; 
v_pos_2374_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_pos_2374_);
v_res_2375_ = lean_ctor_get(v___x_2340_, 1);
lean_inc(v_res_2375_);
lean_dec_ref(v___x_2340_);
v___x_2376_ = lean_unbox(v_res_2375_);
lean_dec(v_res_2375_);
v_pos_2295_ = v_pos_2374_;
v_res_2296_ = v___x_2376_;
goto v___jp_2294_;
}
else
{
lean_object* v_pos_2377_; lean_object* v_err_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2385_; 
v_pos_2377_ = lean_ctor_get(v___x_2340_, 0);
v_err_2378_ = lean_ctor_get(v___x_2340_, 1);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2380_ = v___x_2340_;
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_err_2378_);
lean_inc(v_pos_2377_);
lean_dec(v___x_2340_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
if (v_isShared_2381_ == 0)
{
v___x_2383_ = v___x_2380_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_pos_2377_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v_err_2378_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
}
else
{
lean_object* v_pos_2386_; lean_object* v_err_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
v_pos_2386_ = lean_ctor_get(v___x_2338_, 0);
v_err_2387_ = lean_ctor_get(v___x_2338_, 1);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2338_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_err_2387_);
lean_inc(v_pos_2386_);
lean_dec(v___x_2338_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_pos_2386_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v_err_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
v___jp_2294_:
{
lean_object* v___x_2297_; 
v___x_2297_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_2292_, v_pos_2295_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_res_2298_; lean_object* v_snd_2299_; lean_object* v_pos_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2327_; 
v_res_2298_ = lean_ctor_get(v___x_2297_, 1);
lean_inc(v_res_2298_);
v_snd_2299_ = lean_ctor_get(v_res_2298_, 1);
lean_inc(v_snd_2299_);
v_pos_2300_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2327_ == 0)
{
lean_object* v_unused_2328_; 
v_unused_2328_ = lean_ctor_get(v___x_2297_, 1);
lean_dec(v_unused_2328_);
v___x_2302_ = v___x_2297_;
v_isShared_2303_ = v_isSharedCheck_2327_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_pos_2300_);
lean_dec(v___x_2297_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2327_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v_fst_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2325_; 
v_fst_2304_ = lean_ctor_get(v_res_2298_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_res_2298_);
if (v_isSharedCheck_2325_ == 0)
{
lean_object* v_unused_2326_; 
v_unused_2326_ = lean_ctor_get(v_res_2298_, 1);
lean_dec(v_unused_2326_);
v___x_2306_ = v_res_2298_;
v_isShared_2307_ = v_isSharedCheck_2325_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_fst_2304_);
lean_dec(v_res_2298_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2325_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v_fst_2308_; lean_object* v_snd_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2324_; 
v_fst_2308_ = lean_ctor_get(v_snd_2299_, 0);
v_snd_2309_ = lean_ctor_get(v_snd_2299_, 1);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_snd_2299_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2311_ = v_snd_2299_;
v_isShared_2312_ = v_isSharedCheck_2324_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_snd_2309_);
lean_inc(v_fst_2308_);
lean_dec(v_snd_2299_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2324_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2313_; lean_object* v___x_2315_; 
v___x_2313_ = l_Std_Http_Version_ofNumber_x3f(v_fst_2308_, v_snd_2309_);
lean_dec(v_snd_2309_);
lean_dec(v_fst_2308_);
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 1, v___x_2313_);
lean_ctor_set(v___x_2311_, 0, v_fst_2304_);
v___x_2315_ = v___x_2311_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_fst_2304_);
lean_ctor_set(v_reuseFailAlloc_2323_, 1, v___x_2313_);
v___x_2315_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
lean_object* v___x_2316_; lean_object* v___x_2318_; 
v___x_2316_ = lean_box(v_res_2296_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 1, v___x_2315_);
lean_ctor_set(v___x_2306_, 0, v___x_2316_);
v___x_2318_ = v___x_2306_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2316_);
lean_ctor_set(v_reuseFailAlloc_2322_, 1, v___x_2315_);
v___x_2318_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
lean_object* v___x_2320_; 
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 1, v___x_2318_);
v___x_2320_ = v___x_2302_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_pos_2300_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v___x_2318_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
}
}
}
else
{
lean_object* v_pos_2329_; lean_object* v_err_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
v_pos_2329_ = lean_ctor_get(v___x_2297_, 0);
v_err_2330_ = lean_ctor_get(v___x_2297_, 1);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2332_ = v___x_2297_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_err_2330_);
lean_inc(v_pos_2329_);
lean_dec(v___x_2297_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_pos_2329_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v_err_2330_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion___boxed(lean_object* v_limits_2395_, lean_object* v_a_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_Std_Http_Protocol_H1_parseRequestLineRawVersion(v_limits_2395_, v_a_2396_);
lean_dec_ref(v_limits_2395_);
return v_res_2397_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(uint8_t v_snd_2398_, uint8_t v___x_2399_, uint8_t v___y_2400_){
_start:
{
uint32_t v___x_2401_; uint32_t v___x_2402_; uint8_t v___x_2403_; 
v___x_2401_ = lean_uint8_to_uint32(v___y_2400_);
v___x_2402_ = 32;
v___x_2403_ = lean_uint32_dec_eq(v___x_2401_, v___x_2402_);
if (v___x_2403_ == 0)
{
uint32_t v___x_2404_; uint8_t v___x_2405_; 
v___x_2404_ = 9;
v___x_2405_ = lean_uint32_dec_eq(v___x_2401_, v___x_2404_);
if (v___x_2405_ == 0)
{
return v_snd_2398_;
}
else
{
return v___x_2399_;
}
}
else
{
return v___x_2399_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed(lean_object* v_snd_2406_, lean_object* v___x_2407_, lean_object* v___y_2408_){
_start:
{
uint8_t v_snd_3191__boxed_2409_; uint8_t v___x_3192__boxed_2410_; uint8_t v___y_3193__boxed_2411_; uint8_t v_res_2412_; lean_object* v_r_2413_; 
v_snd_3191__boxed_2409_ = lean_unbox(v_snd_2406_);
v___x_3192__boxed_2410_ = lean_unbox(v___x_2407_);
v___y_3193__boxed_2411_ = lean_unbox(v___y_2408_);
v_res_2412_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(v_snd_3191__boxed_2409_, v___x_3192__boxed_2410_, v___y_3193__boxed_2411_);
v_r_2413_ = lean_box(v_res_2412_);
return v_r_2413_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0(uint8_t v_snd_2414_, uint8_t v___x_2415_, uint8_t v___y_2416_){
_start:
{
uint32_t v___x_2417_; uint32_t v___x_2423_; uint8_t v___x_2424_; 
v___x_2417_ = lean_uint8_to_uint32(v___y_2416_);
v___x_2423_ = 33;
v___x_2424_ = lean_uint32_dec_le(v___x_2423_, v___x_2417_);
if (v___x_2424_ == 0)
{
goto v___jp_2418_;
}
else
{
uint32_t v___x_2425_; uint8_t v___x_2426_; 
v___x_2425_ = 126;
v___x_2426_ = lean_uint32_dec_le(v___x_2417_, v___x_2425_);
if (v___x_2426_ == 0)
{
goto v___jp_2418_;
}
else
{
return v___x_2415_;
}
}
v___jp_2418_:
{
uint32_t v___x_2419_; uint8_t v___x_2420_; 
v___x_2419_ = 32;
v___x_2420_ = lean_uint32_dec_eq(v___x_2417_, v___x_2419_);
if (v___x_2420_ == 0)
{
uint32_t v___x_2421_; uint8_t v___x_2422_; 
v___x_2421_ = 9;
v___x_2422_ = lean_uint32_dec_eq(v___x_2417_, v___x_2421_);
if (v___x_2422_ == 0)
{
return v_snd_2414_;
}
else
{
return v___x_2415_;
}
}
else
{
return v___x_2415_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0___boxed(lean_object* v_snd_2427_, lean_object* v___x_2428_, lean_object* v___y_2429_){
_start:
{
uint8_t v_snd_3210__boxed_2430_; uint8_t v___x_3211__boxed_2431_; uint8_t v___y_3212__boxed_2432_; uint8_t v_res_2433_; lean_object* v_r_2434_; 
v_snd_3210__boxed_2430_ = lean_unbox(v_snd_2427_);
v___x_3211__boxed_2431_ = lean_unbox(v___x_2428_);
v___y_3212__boxed_2432_ = lean_unbox(v___y_2429_);
v_res_2433_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0(v_snd_3210__boxed_2430_, v___x_3211__boxed_2431_, v___y_3212__boxed_2432_);
v_r_2434_ = lean_box(v_res_2433_);
return v_r_2434_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(lean_object* v_s_2435_, lean_object* v_pos_2436_){
_start:
{
lean_object* v_str_2437_; lean_object* v_startInclusive_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; uint8_t v___x_2442_; 
v_str_2437_ = lean_ctor_get(v_s_2435_, 0);
v_startInclusive_2438_ = lean_ctor_get(v_s_2435_, 1);
v___x_2439_ = lean_nat_add(v_startInclusive_2438_, v_pos_2436_);
v___x_2440_ = lean_nat_sub(v___x_2439_, v_startInclusive_2438_);
v___x_2441_ = lean_unsigned_to_nat(0u);
v___x_2442_ = lean_nat_dec_eq(v___x_2440_, v___x_2441_);
if (v___x_2442_ == 0)
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; uint8_t v___y_2451_; lean_object* v___x_2452_; uint32_t v___x_2453_; uint8_t v___y_2455_; uint32_t v___x_2460_; uint8_t v___x_2461_; 
lean_inc(v_startInclusive_2438_);
lean_inc_ref(v_str_2437_);
v___x_2443_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2443_, 0, v_str_2437_);
lean_ctor_set(v___x_2443_, 1, v_startInclusive_2438_);
lean_ctor_set(v___x_2443_, 2, v___x_2439_);
v___x_2444_ = lean_unsigned_to_nat(1u);
v___x_2445_ = lean_nat_sub(v___x_2440_, v___x_2444_);
lean_dec(v___x_2440_);
v___x_2446_ = l_String_Slice_posLE(v___x_2443_, v___x_2445_);
lean_dec_ref(v___x_2443_);
v___x_2452_ = lean_nat_add(v_startInclusive_2438_, v___x_2446_);
v___x_2453_ = lean_string_utf8_get_fast(v_str_2437_, v___x_2452_);
lean_dec(v___x_2452_);
v___x_2460_ = 32;
v___x_2461_ = lean_uint32_dec_eq(v___x_2453_, v___x_2460_);
if (v___x_2461_ == 0)
{
uint32_t v___x_2462_; uint8_t v___x_2463_; 
v___x_2462_ = 9;
v___x_2463_ = lean_uint32_dec_eq(v___x_2453_, v___x_2462_);
v___y_2455_ = v___x_2463_;
goto v___jp_2454_;
}
else
{
v___y_2455_ = v___x_2461_;
goto v___jp_2454_;
}
v___jp_2447_:
{
uint8_t v___x_2448_; 
v___x_2448_ = lean_nat_dec_lt(v___x_2446_, v_pos_2436_);
if (v___x_2448_ == 0)
{
lean_dec(v___x_2446_);
return v_pos_2436_;
}
else
{
lean_dec(v_pos_2436_);
v_pos_2436_ = v___x_2446_;
goto _start;
}
}
v___jp_2450_:
{
if (v___y_2451_ == 0)
{
lean_dec(v___x_2446_);
return v_pos_2436_;
}
else
{
goto v___jp_2447_;
}
}
v___jp_2454_:
{
if (v___y_2455_ == 0)
{
uint32_t v___x_2456_; uint8_t v___x_2457_; 
v___x_2456_ = 13;
v___x_2457_ = lean_uint32_dec_eq(v___x_2453_, v___x_2456_);
if (v___x_2457_ == 0)
{
uint32_t v___x_2458_; uint8_t v___x_2459_; 
v___x_2458_ = 10;
v___x_2459_ = lean_uint32_dec_eq(v___x_2453_, v___x_2458_);
v___y_2451_ = v___x_2459_;
goto v___jp_2450_;
}
else
{
v___y_2451_ = v___x_2457_;
goto v___jp_2450_;
}
}
else
{
goto v___jp_2447_;
}
}
}
else
{
lean_dec(v___x_2440_);
lean_dec(v___x_2439_);
return v_pos_2436_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0___boxed(lean_object* v_s_2464_, lean_object* v_pos_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(v_s_2464_, v_pos_2465_);
lean_dec_ref(v_s_2464_);
return v_res_2466_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0(void){
_start:
{
uint32_t v___x_2467_; uint8_t v___x_2468_; 
v___x_2467_ = 58;
v___x_2468_ = lean_uint32_to_uint8(v___x_2467_);
return v___x_2468_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1(void){
_start:
{
uint8_t v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0);
v___x_2470_ = lean_uint8_to_nat(v___x_2469_);
return v___x_2470_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2(void){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1);
v___x_2472_ = l_Nat_reprFast(v___x_2471_);
return v___x_2472_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3(void){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2473_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2);
v___x_2474_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_2475_ = lean_string_append(v___x_2474_, v___x_2473_);
return v___x_2475_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2476_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__5));
v___x_2477_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3);
v___x_2478_ = lean_string_append(v___x_2477_, v___x_2476_);
return v___x_2478_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__5(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4);
v___x_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(lean_object* v_limits_2481_, lean_object* v_a_2482_){
_start:
{
lean_object* v_maxHeaderNameLength_2483_; lean_object* v_maxHeaderValueLength_2484_; lean_object* v_maxSpaceSequence_2485_; lean_object* v___f_2486_; lean_object* v___x_2487_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2547_; lean_object* v_pos_2548_; lean_object* v_res_2549_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; uint8_t v___y_2559_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v_pos_2565_; lean_object* v_res_2566_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v_lower_2597_; lean_object* v_upper_2598_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v_pos_2614_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; uint8_t v___y_2645_; lean_object* v___x_2648_; lean_object* v_snd_2649_; lean_object* v_snd_2650_; uint8_t v___x_2651_; 
v_maxHeaderNameLength_2483_ = lean_ctor_get(v_limits_2481_, 6);
v_maxHeaderValueLength_2484_ = lean_ctor_get(v_limits_2481_, 7);
v_maxSpaceSequence_2485_ = lean_ctor_get(v_limits_2481_, 8);
v___f_2486_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_2487_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2482_);
v___x_2648_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2486_, v_maxHeaderNameLength_2483_, v___x_2487_, v_a_2482_);
v_snd_2649_ = lean_ctor_get(v___x_2648_, 1);
lean_inc(v_snd_2649_);
v_snd_2650_ = lean_ctor_get(v_snd_2649_, 1);
v___x_2651_ = lean_unbox(v_snd_2650_);
if (v___x_2651_ == 0)
{
lean_object* v_fst_2652_; lean_object* v_fst_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2742_; 
lean_inc(v_snd_2650_);
v_fst_2652_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_fst_2652_);
lean_dec_ref(v___x_2648_);
v_fst_2653_ = lean_ctor_get(v_snd_2649_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_snd_2649_);
if (v_isSharedCheck_2742_ == 0)
{
lean_object* v_unused_2743_; 
v_unused_2743_ = lean_ctor_get(v_snd_2649_, 1);
lean_dec(v_unused_2743_);
v___x_2655_ = v_snd_2649_;
v_isShared_2656_ = v_isSharedCheck_2742_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_fst_2653_);
lean_dec(v_snd_2649_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2742_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
uint8_t v___x_2657_; 
v___x_2657_ = lean_nat_dec_eq(v_fst_2652_, v___x_2487_);
if (v___x_2657_ == 0)
{
lean_object* v_array_2658_; lean_object* v_idx_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2737_; 
v_array_2658_ = lean_ctor_get(v_a_2482_, 0);
v_idx_2659_ = lean_ctor_get(v_a_2482_, 1);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_a_2482_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2661_ = v_a_2482_;
v_isShared_2662_ = v_isSharedCheck_2737_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_idx_2659_);
lean_inc(v_array_2658_);
lean_dec(v_a_2482_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2737_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___y_2664_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___y_2728_; uint8_t v___x_2736_; 
v___x_2725_ = lean_nat_add(v_idx_2659_, v_fst_2652_);
lean_dec(v_fst_2652_);
v___x_2726_ = lean_byte_array_size(v_array_2658_);
v___x_2736_ = lean_nat_dec_le(v_idx_2659_, v___x_2487_);
if (v___x_2736_ == 0)
{
v___y_2728_ = v_idx_2659_;
goto v___jp_2727_;
}
else
{
lean_dec(v_idx_2659_);
v___y_2728_ = v___x_2487_;
goto v___jp_2727_;
}
v___jp_2663_:
{
lean_object* v_array_2665_; lean_object* v_idx_2666_; lean_object* v___x_2667_; uint8_t v___x_2668_; 
v_array_2665_ = lean_ctor_get(v_fst_2653_, 0);
v_idx_2666_ = lean_ctor_get(v_fst_2653_, 1);
v___x_2667_ = lean_byte_array_size(v_array_2665_);
v___x_2668_ = lean_nat_dec_lt(v_idx_2666_, v___x_2667_);
if (v___x_2668_ == 0)
{
lean_object* v___x_2669_; lean_object* v___x_2671_; 
lean_dec_ref(v___y_2664_);
lean_dec_ref(v_array_2658_);
lean_dec(v_snd_2650_);
v___x_2669_ = lean_box(0);
if (v_isShared_2662_ == 0)
{
lean_ctor_set_tag(v___x_2661_, 1);
lean_ctor_set(v___x_2661_, 1, v___x_2669_);
lean_ctor_set(v___x_2661_, 0, v_fst_2653_);
v___x_2671_ = v___x_2661_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_fst_2653_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v___x_2669_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
else
{
uint8_t v___x_2673_; uint8_t v_got_2674_; uint8_t v___x_2675_; 
v___x_2673_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0);
v_got_2674_ = lean_byte_array_fget(v_array_2665_, v_idx_2666_);
v___x_2675_ = lean_uint8_dec_eq(v_got_2674_, v___x_2673_);
if (v___x_2675_ == 0)
{
lean_object* v___x_2676_; lean_object* v___x_2678_; 
lean_dec_ref(v___y_2664_);
lean_dec_ref(v_array_2658_);
lean_dec(v_snd_2650_);
v___x_2676_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__5, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__5_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__5);
if (v_isShared_2662_ == 0)
{
lean_ctor_set_tag(v___x_2661_, 1);
lean_ctor_set(v___x_2661_, 1, v___x_2676_);
lean_ctor_set(v___x_2661_, 0, v_fst_2653_);
v___x_2678_ = v___x_2661_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_fst_2653_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v___x_2676_);
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
lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2722_; 
lean_inc(v_idx_2666_);
lean_inc_ref(v_array_2665_);
lean_del_object(v___x_2661_);
v_isSharedCheck_2722_ = !lean_is_exclusive(v_fst_2653_);
if (v_isSharedCheck_2722_ == 0)
{
lean_object* v_unused_2723_; lean_object* v_unused_2724_; 
v_unused_2723_ = lean_ctor_get(v_fst_2653_, 1);
lean_dec(v_unused_2723_);
v_unused_2724_ = lean_ctor_get(v_fst_2653_, 0);
lean_dec(v_unused_2724_);
v___x_2681_ = v_fst_2653_;
v_isShared_2682_ = v_isSharedCheck_2722_;
goto v_resetjp_2680_;
}
else
{
lean_dec(v_fst_2653_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2722_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2683_; lean_object* v___f_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2688_; 
v___x_2683_ = lean_box(v___x_2668_);
v___f_2684_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2684_, 0, v_snd_2650_);
lean_closure_set(v___f_2684_, 1, v___x_2683_);
v___x_2685_ = lean_unsigned_to_nat(1u);
v___x_2686_ = lean_nat_add(v_idx_2666_, v___x_2685_);
lean_dec(v_idx_2666_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 1, v___x_2686_);
v___x_2688_ = v___x_2681_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_array_2665_);
lean_ctor_set(v_reuseFailAlloc_2721_, 1, v___x_2686_);
v___x_2688_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
lean_object* v___x_2689_; lean_object* v_snd_2690_; lean_object* v_snd_2691_; uint8_t v___x_2692_; 
v___x_2689_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2684_, v_maxSpaceSequence_2485_, v___x_2487_, v___x_2688_);
v_snd_2690_ = lean_ctor_get(v___x_2689_, 1);
lean_inc(v_snd_2690_);
lean_dec_ref(v___x_2689_);
v_snd_2691_ = lean_ctor_get(v_snd_2690_, 1);
v___x_2692_ = lean_unbox(v_snd_2691_);
if (v___x_2692_ == 0)
{
lean_object* v_fst_2693_; lean_object* v_array_2694_; lean_object* v_idx_2695_; lean_object* v_lower_2696_; lean_object* v_upper_2697_; lean_object* v___x_2698_; lean_object* v___f_2699_; lean_object* v___x_2700_; lean_object* v___f_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; uint8_t v___x_2704_; 
lean_inc_n(v_snd_2691_, 2);
v_fst_2693_ = lean_ctor_get(v_snd_2690_, 0);
lean_inc(v_fst_2693_);
lean_dec(v_snd_2690_);
v_array_2694_ = lean_ctor_get(v_fst_2693_, 0);
v_idx_2695_ = lean_ctor_get(v_fst_2693_, 1);
v_lower_2696_ = lean_ctor_get(v___y_2664_, 0);
lean_inc(v_lower_2696_);
v_upper_2697_ = lean_ctor_get(v___y_2664_, 1);
lean_inc(v_upper_2697_);
lean_dec_ref(v___y_2664_);
v___x_2698_ = lean_box(v___x_2668_);
v___f_2699_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2699_, 0, v_snd_2691_);
lean_closure_set(v___f_2699_, 1, v___x_2698_);
v___x_2700_ = lean_box(v___x_2668_);
v___f_2701_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2701_, 0, v_snd_2691_);
lean_closure_set(v___f_2701_, 1, v___x_2700_);
v___x_2702_ = l_ByteArray_toByteSlice(v_array_2658_, v_lower_2696_, v_upper_2697_);
v___x_2703_ = lean_byte_array_size(v_array_2694_);
v___x_2704_ = lean_nat_dec_lt(v_idx_2695_, v___x_2703_);
if (v___x_2704_ == 0)
{
v___y_2611_ = v___f_2701_;
v___y_2612_ = v___f_2699_;
v___y_2613_ = v___x_2702_;
v_pos_2614_ = v_fst_2693_;
goto v___jp_2610_;
}
else
{
uint8_t v___x_2705_; uint32_t v___x_2706_; uint32_t v___x_2707_; uint8_t v___x_2708_; 
v___x_2705_ = lean_byte_array_fget(v_array_2694_, v_idx_2695_);
v___x_2706_ = lean_uint8_to_uint32(v___x_2705_);
v___x_2707_ = 32;
v___x_2708_ = lean_uint32_dec_eq(v___x_2706_, v___x_2707_);
if (v___x_2708_ == 0)
{
uint32_t v___x_2709_; uint8_t v___x_2710_; 
v___x_2709_ = 9;
v___x_2710_ = lean_uint32_dec_eq(v___x_2706_, v___x_2709_);
if (v___x_2710_ == 0)
{
v___y_2611_ = v___f_2701_;
v___y_2612_ = v___f_2699_;
v___y_2613_ = v___x_2702_;
v_pos_2614_ = v_fst_2693_;
goto v___jp_2610_;
}
else
{
v___y_2641_ = v___f_2701_;
v___y_2642_ = v___f_2699_;
v___y_2643_ = v___x_2702_;
v___y_2644_ = v_fst_2693_;
v___y_2645_ = v___x_2704_;
goto v___jp_2640_;
}
}
else
{
v___y_2641_ = v___f_2701_;
v___y_2642_ = v___f_2699_;
v___y_2643_ = v___x_2702_;
v___y_2644_ = v_fst_2693_;
v___y_2645_ = v___x_2704_;
goto v___jp_2640_;
}
}
}
else
{
lean_object* v_fst_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2719_; 
lean_dec_ref(v___y_2664_);
lean_dec_ref(v_array_2658_);
v_fst_2711_ = lean_ctor_get(v_snd_2690_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v_snd_2690_);
if (v_isSharedCheck_2719_ == 0)
{
lean_object* v_unused_2720_; 
v_unused_2720_ = lean_ctor_get(v_snd_2690_, 1);
lean_dec(v_unused_2720_);
v___x_2713_ = v_snd_2690_;
v_isShared_2714_ = v_isSharedCheck_2719_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_fst_2711_);
lean_dec(v_snd_2690_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2719_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2715_; lean_object* v___x_2717_; 
v___x_2715_ = lean_box(0);
if (v_isShared_2714_ == 0)
{
lean_ctor_set_tag(v___x_2713_, 1);
lean_ctor_set(v___x_2713_, 1, v___x_2715_);
v___x_2717_ = v___x_2713_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_fst_2711_);
lean_ctor_set(v_reuseFailAlloc_2718_, 1, v___x_2715_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
}
}
}
}
v___jp_2727_:
{
uint8_t v___x_2729_; 
v___x_2729_ = lean_nat_dec_le(v___x_2725_, v___x_2726_);
if (v___x_2729_ == 0)
{
lean_object* v___x_2731_; 
lean_dec(v___x_2725_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 1, v___x_2726_);
lean_ctor_set(v___x_2655_, 0, v___y_2728_);
v___x_2731_ = v___x_2655_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___y_2728_);
lean_ctor_set(v_reuseFailAlloc_2732_, 1, v___x_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
v___y_2664_ = v___x_2731_;
goto v___jp_2663_;
}
}
else
{
lean_object* v___x_2734_; 
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 1, v___x_2725_);
lean_ctor_set(v___x_2655_, 0, v___y_2728_);
v___x_2734_ = v___x_2655_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___y_2728_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v___x_2725_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
v___y_2664_ = v___x_2734_;
goto v___jp_2663_;
}
}
}
}
}
else
{
lean_object* v___x_2738_; lean_object* v___x_2740_; 
lean_dec(v_fst_2653_);
lean_dec(v_fst_2652_);
lean_dec(v_snd_2650_);
v___x_2738_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_2656_ == 0)
{
lean_ctor_set_tag(v___x_2655_, 1);
lean_ctor_set(v___x_2655_, 1, v___x_2738_);
lean_ctor_set(v___x_2655_, 0, v_a_2482_);
v___x_2740_ = v___x_2655_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2482_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v___x_2738_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
else
{
lean_object* v_fst_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2752_; 
lean_dec_ref(v___x_2648_);
lean_dec_ref(v_a_2482_);
v_fst_2744_ = lean_ctor_get(v_snd_2649_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v_snd_2649_);
if (v_isSharedCheck_2752_ == 0)
{
lean_object* v_unused_2753_; 
v_unused_2753_ = lean_ctor_get(v_snd_2649_, 1);
lean_dec(v_unused_2753_);
v___x_2746_ = v_snd_2649_;
v_isShared_2747_ = v_isSharedCheck_2752_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_fst_2744_);
lean_dec(v_snd_2649_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2752_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2748_; lean_object* v___x_2750_; 
v___x_2748_ = lean_box(0);
if (v_isShared_2747_ == 0)
{
lean_ctor_set_tag(v___x_2746_, 1);
lean_ctor_set(v___x_2746_, 1, v___x_2748_);
v___x_2750_ = v___x_2746_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_fst_2744_);
lean_ctor_set(v_reuseFailAlloc_2751_, 1, v___x_2748_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
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
lean_dec_ref(v___x_2499_);
v___x_2501_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2501_, 0, v_res_2494_);
lean_ctor_set(v___x_2501_, 1, v___x_2487_);
lean_ctor_set(v___x_2501_, 2, v___x_2500_);
v___x_2502_ = l_String_Slice_toString(v___x_2501_);
lean_dec_ref(v___x_2501_);
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
v___x_2529_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___y_2528_, v___y_2526_);
lean_dec(v___y_2528_);
if (lean_obj_tag(v___x_2529_) == 0)
{
if (lean_obj_tag(v___y_2527_) == 0)
{
lean_object* v_pos_2530_; lean_object* v_res_2531_; lean_object* v___x_2532_; 
v_pos_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_pos_2530_);
v_res_2531_ = lean_ctor_get(v___x_2529_, 1);
lean_inc(v_res_2531_);
lean_dec_ref(v___x_2529_);
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
lean_dec_ref(v___x_2529_);
v_val_2535_ = lean_ctor_get(v___y_2527_, 0);
lean_inc(v_val_2535_);
lean_dec_ref(v___y_2527_);
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
lean_dec(v___y_2527_);
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
v___y_2526_ = v_pos_2548_;
v___y_2527_ = v_res_2549_;
v___y_2528_ = v___x_2552_;
goto v___jp_2525_;
}
else
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = lean_string_from_utf8_unchecked(v___x_2550_);
v___x_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
v___y_2526_ = v_pos_2548_;
v___y_2527_ = v_res_2549_;
v___y_2528_ = v___x_2554_;
goto v___jp_2525_;
}
}
v___jp_2555_:
{
if (v___y_2559_ == 0)
{
v___y_2547_ = v___y_2557_;
v_pos_2548_ = v___y_2558_;
v_res_2549_ = v___y_2556_;
goto v___jp_2546_;
}
else
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2556_);
v___x_2560_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2));
v___x_2561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___y_2558_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
return v___x_2561_;
}
}
v___jp_2562_:
{
lean_object* v___x_2567_; lean_object* v_snd_2568_; lean_object* v_snd_2569_; uint8_t v___x_2570_; 
v___x_2567_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___y_2563_, v_maxSpaceSequence_2485_, v___x_2487_, v_pos_2565_);
v_snd_2568_ = lean_ctor_get(v___x_2567_, 1);
lean_inc(v_snd_2568_);
lean_dec_ref(v___x_2567_);
v_snd_2569_ = lean_ctor_get(v_snd_2568_, 1);
v___x_2570_ = lean_unbox(v_snd_2569_);
if (v___x_2570_ == 0)
{
lean_object* v_fst_2571_; lean_object* v_array_2572_; lean_object* v_idx_2573_; lean_object* v___x_2574_; uint8_t v___x_2575_; 
v_fst_2571_ = lean_ctor_get(v_snd_2568_, 0);
lean_inc(v_fst_2571_);
lean_dec(v_snd_2568_);
v_array_2572_ = lean_ctor_get(v_fst_2571_, 0);
v_idx_2573_ = lean_ctor_get(v_fst_2571_, 1);
v___x_2574_ = lean_byte_array_size(v_array_2572_);
v___x_2575_ = lean_nat_dec_lt(v_idx_2573_, v___x_2574_);
if (v___x_2575_ == 0)
{
v___y_2547_ = v___y_2564_;
v_pos_2548_ = v_fst_2571_;
v_res_2549_ = v_res_2566_;
goto v___jp_2546_;
}
else
{
uint8_t v___x_2576_; uint32_t v___x_2577_; uint32_t v___x_2578_; uint8_t v___x_2579_; 
v___x_2576_ = lean_byte_array_fget(v_array_2572_, v_idx_2573_);
v___x_2577_ = lean_uint8_to_uint32(v___x_2576_);
v___x_2578_ = 32;
v___x_2579_ = lean_uint32_dec_eq(v___x_2577_, v___x_2578_);
if (v___x_2579_ == 0)
{
uint32_t v___x_2580_; uint8_t v___x_2581_; 
v___x_2580_ = 9;
v___x_2581_ = lean_uint32_dec_eq(v___x_2577_, v___x_2580_);
if (v___x_2581_ == 0)
{
v___y_2547_ = v___y_2564_;
v_pos_2548_ = v_fst_2571_;
v_res_2549_ = v_res_2566_;
goto v___jp_2546_;
}
else
{
v___y_2556_ = v_res_2566_;
v___y_2557_ = v___y_2564_;
v___y_2558_ = v_fst_2571_;
v___y_2559_ = v___x_2575_;
goto v___jp_2555_;
}
}
else
{
v___y_2556_ = v_res_2566_;
v___y_2557_ = v___y_2564_;
v___y_2558_ = v_fst_2571_;
v___y_2559_ = v___x_2575_;
goto v___jp_2555_;
}
}
}
else
{
lean_object* v_fst_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2590_; 
lean_dec(v_res_2566_);
lean_dec_ref(v___y_2564_);
v_fst_2582_ = lean_ctor_get(v_snd_2568_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v_snd_2568_);
if (v_isSharedCheck_2590_ == 0)
{
lean_object* v_unused_2591_; 
v_unused_2591_ = lean_ctor_get(v_snd_2568_, 1);
lean_dec(v_unused_2591_);
v___x_2584_ = v_snd_2568_;
v_isShared_2585_ = v_isSharedCheck_2590_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_fst_2582_);
lean_dec(v_snd_2568_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2590_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; lean_object* v___x_2588_; 
v___x_2586_ = lean_box(0);
if (v_isShared_2585_ == 0)
{
lean_ctor_set_tag(v___x_2584_, 1);
lean_ctor_set(v___x_2584_, 1, v___x_2586_);
v___x_2588_ = v___x_2584_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_fst_2582_);
lean_ctor_set(v_reuseFailAlloc_2589_, 1, v___x_2586_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
v___jp_2592_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2599_ = l_ByteArray_toByteSlice(v___y_2596_, v_lower_2597_, v_upper_2598_);
v___x_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
v___y_2563_ = v___y_2593_;
v___y_2564_ = v___y_2595_;
v_pos_2565_ = v___y_2594_;
v_res_2566_ = v___x_2600_;
goto v___jp_2562_;
}
v___jp_2601_:
{
uint8_t v___x_2609_; 
v___x_2609_ = lean_nat_dec_le(v___y_2604_, v___y_2607_);
if (v___x_2609_ == 0)
{
lean_dec(v___y_2604_);
v___y_2593_ = v___y_2602_;
v___y_2594_ = v___y_2603_;
v___y_2595_ = v___y_2605_;
v___y_2596_ = v___y_2606_;
v_lower_2597_ = v___y_2608_;
v_upper_2598_ = v___y_2607_;
goto v___jp_2592_;
}
else
{
lean_dec(v___y_2607_);
v___y_2593_ = v___y_2602_;
v___y_2594_ = v___y_2603_;
v___y_2595_ = v___y_2605_;
v___y_2596_ = v___y_2606_;
v_lower_2597_ = v___y_2608_;
v_upper_2598_ = v___y_2604_;
goto v___jp_2592_;
}
}
v___jp_2610_:
{
lean_object* v___x_2615_; lean_object* v_snd_2616_; lean_object* v_snd_2617_; uint8_t v___x_2618_; 
lean_inc_ref(v_pos_2614_);
v___x_2615_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___y_2612_, v_maxHeaderValueLength_2484_, v___x_2487_, v_pos_2614_);
v_snd_2616_ = lean_ctor_get(v___x_2615_, 1);
lean_inc(v_snd_2616_);
v_snd_2617_ = lean_ctor_get(v_snd_2616_, 1);
v___x_2618_ = lean_unbox(v_snd_2617_);
if (v___x_2618_ == 0)
{
lean_object* v_fst_2619_; lean_object* v_fst_2620_; lean_object* v_array_2621_; lean_object* v_idx_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; uint8_t v___x_2625_; 
v_fst_2619_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_fst_2619_);
lean_dec_ref(v___x_2615_);
v_fst_2620_ = lean_ctor_get(v_snd_2616_, 0);
lean_inc(v_fst_2620_);
lean_dec(v_snd_2616_);
v_array_2621_ = lean_ctor_get(v_pos_2614_, 0);
lean_inc_ref(v_array_2621_);
v_idx_2622_ = lean_ctor_get(v_pos_2614_, 1);
lean_inc(v_idx_2622_);
lean_dec_ref(v_pos_2614_);
v___x_2623_ = lean_nat_add(v_idx_2622_, v_fst_2619_);
lean_dec(v_fst_2619_);
v___x_2624_ = lean_byte_array_size(v_array_2621_);
v___x_2625_ = lean_nat_dec_le(v_idx_2622_, v___x_2487_);
if (v___x_2625_ == 0)
{
v___y_2602_ = v___y_2611_;
v___y_2603_ = v_fst_2620_;
v___y_2604_ = v___x_2623_;
v___y_2605_ = v___y_2613_;
v___y_2606_ = v_array_2621_;
v___y_2607_ = v___x_2624_;
v___y_2608_ = v_idx_2622_;
goto v___jp_2601_;
}
else
{
lean_dec(v_idx_2622_);
v___y_2602_ = v___y_2611_;
v___y_2603_ = v_fst_2620_;
v___y_2604_ = v___x_2623_;
v___y_2605_ = v___y_2613_;
v___y_2606_ = v_array_2621_;
v___y_2607_ = v___x_2624_;
v___y_2608_ = v___x_2487_;
goto v___jp_2601_;
}
}
else
{
lean_object* v_fst_2626_; lean_object* v_idx_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2638_; 
lean_dec_ref(v___x_2615_);
v_fst_2626_ = lean_ctor_get(v_snd_2616_, 0);
lean_inc(v_fst_2626_);
lean_dec(v_snd_2616_);
v_idx_2627_ = lean_ctor_get(v_pos_2614_, 1);
v_isSharedCheck_2638_ = !lean_is_exclusive(v_pos_2614_);
if (v_isSharedCheck_2638_ == 0)
{
lean_object* v_unused_2639_; 
v_unused_2639_ = lean_ctor_get(v_pos_2614_, 0);
lean_dec(v_unused_2639_);
v___x_2629_ = v_pos_2614_;
v_isShared_2630_ = v_isSharedCheck_2638_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_idx_2627_);
lean_dec(v_pos_2614_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2638_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v_idx_2631_; uint8_t v___x_2632_; 
v_idx_2631_ = lean_ctor_get(v_fst_2626_, 1);
v___x_2632_ = lean_nat_dec_eq(v_idx_2627_, v_idx_2631_);
lean_dec(v_idx_2627_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; lean_object* v___x_2635_; 
lean_dec_ref(v___y_2613_);
lean_dec_ref(v___y_2611_);
v___x_2633_ = lean_box(0);
if (v_isShared_2630_ == 0)
{
lean_ctor_set_tag(v___x_2629_, 1);
lean_ctor_set(v___x_2629_, 1, v___x_2633_);
lean_ctor_set(v___x_2629_, 0, v_fst_2626_);
v___x_2635_ = v___x_2629_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_fst_2626_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v___x_2633_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
else
{
lean_object* v___x_2637_; 
lean_del_object(v___x_2629_);
v___x_2637_ = lean_box(0);
v___y_2563_ = v___y_2611_;
v___y_2564_ = v___y_2613_;
v_pos_2565_ = v_fst_2626_;
v_res_2566_ = v___x_2637_;
goto v___jp_2562_;
}
}
}
}
v___jp_2640_:
{
if (v___y_2645_ == 0)
{
v___y_2611_ = v___y_2641_;
v___y_2612_ = v___y_2642_;
v___y_2613_ = v___y_2643_;
v_pos_2614_ = v___y_2644_;
goto v___jp_2610_;
}
else
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
lean_dec_ref(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec_ref(v___y_2641_);
v___x_2646_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2));
v___x_2647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2647_, 0, v___y_2644_);
lean_ctor_set(v___x_2647_, 1, v___x_2646_);
return v___x_2647_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___boxed(lean_object* v_limits_2754_, lean_object* v_a_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_2754_, v_a_2755_);
lean_dec_ref(v_limits_2754_);
return v_res_2756_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(lean_object* v_x_2757_, lean_object* v_x_2758_){
_start:
{
if (lean_obj_tag(v_x_2757_) == 0)
{
if (lean_obj_tag(v_x_2758_) == 0)
{
uint8_t v___x_2759_; 
v___x_2759_ = 1;
return v___x_2759_;
}
else
{
uint8_t v___x_2760_; 
v___x_2760_ = 0;
return v___x_2760_;
}
}
else
{
if (lean_obj_tag(v_x_2758_) == 0)
{
uint8_t v___x_2761_; 
v___x_2761_ = 0;
return v___x_2761_;
}
else
{
lean_object* v_val_2762_; lean_object* v_val_2763_; uint8_t v___x_2764_; uint8_t v___x_2765_; uint8_t v___x_2766_; 
v_val_2762_ = lean_ctor_get(v_x_2757_, 0);
v_val_2763_ = lean_ctor_get(v_x_2758_, 0);
v___x_2764_ = lean_unbox(v_val_2762_);
v___x_2765_ = lean_unbox(v_val_2763_);
v___x_2766_ = lean_uint8_dec_eq(v___x_2764_, v___x_2765_);
return v___x_2766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0___boxed(lean_object* v_x_2767_, lean_object* v_x_2768_){
_start:
{
uint8_t v_res_2769_; lean_object* v_r_2770_; 
v_res_2769_ = l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_x_2767_, v_x_2768_);
lean_dec(v_x_2768_);
lean_dec(v_x_2767_);
v_r_2770_ = lean_box(v_res_2769_);
return v_r_2770_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_parseSingleHeader___closed__0(void){
_start:
{
uint8_t v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2771_ = lean_uint8_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___closed__0, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___closed__0_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___closed__0);
v___x_2772_ = lean_box(v___x_2771_);
v___x_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2772_);
return v___x_2773_;
}
}
static uint8_t _init_l_Std_Http_Protocol_H1_parseSingleHeader___closed__1(void){
_start:
{
uint32_t v___x_2774_; uint8_t v___x_2775_; 
v___x_2774_ = 10;
v___x_2775_ = lean_uint32_to_uint8(v___x_2774_);
return v___x_2775_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_parseSingleHeader___closed__2(void){
_start:
{
uint8_t v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2776_ = lean_uint8_once(&l_Std_Http_Protocol_H1_parseSingleHeader___closed__1, &l_Std_Http_Protocol_H1_parseSingleHeader___closed__1_once, _init_l_Std_Http_Protocol_H1_parseSingleHeader___closed__1);
v___x_2777_ = lean_box(v___x_2776_);
v___x_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2777_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader(lean_object* v_limits_2779_, lean_object* v_a_2780_){
_start:
{
lean_object* v_pos_2782_; lean_object* v_res_2783_; lean_object* v___y_2787_; lean_object* v_pos_2810_; lean_object* v_res_2811_; lean_object* v_array_2842_; lean_object* v_idx_2843_; lean_object* v___x_2844_; uint8_t v___x_2845_; 
v_array_2842_ = lean_ctor_get(v_a_2780_, 0);
v_idx_2843_ = lean_ctor_get(v_a_2780_, 1);
v___x_2844_ = lean_byte_array_size(v_array_2842_);
v___x_2845_ = lean_nat_dec_lt(v_idx_2843_, v___x_2844_);
if (v___x_2845_ == 0)
{
lean_object* v___x_2846_; 
v___x_2846_ = lean_box(0);
v_pos_2810_ = v_a_2780_;
v_res_2811_ = v___x_2846_;
goto v___jp_2809_;
}
else
{
uint8_t v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2847_ = lean_byte_array_fget(v_array_2842_, v_idx_2843_);
v___x_2848_ = lean_box(v___x_2847_);
v___x_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
v_pos_2810_ = v_a_2780_;
v_res_2811_ = v___x_2849_;
goto v___jp_2809_;
}
v___jp_2781_:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2784_, 0, v_res_2783_);
v___x_2785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2785_, 0, v_pos_2782_);
lean_ctor_set(v___x_2785_, 1, v___x_2784_);
return v___x_2785_;
}
v___jp_2786_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2789_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2788_, v___y_2787_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_pos_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2798_; 
v_pos_2790_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2798_ == 0)
{
lean_object* v_unused_2799_; 
v_unused_2799_ = lean_ctor_get(v___x_2789_, 1);
lean_dec(v_unused_2799_);
v___x_2792_ = v___x_2789_;
v_isShared_2793_ = v_isSharedCheck_2798_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_pos_2790_);
lean_dec(v___x_2789_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2798_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2794_; lean_object* v___x_2796_; 
v___x_2794_ = lean_box(0);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 1, v___x_2794_);
v___x_2796_ = v___x_2792_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_pos_2790_);
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
else
{
lean_object* v_pos_2800_; lean_object* v_err_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
v_pos_2800_ = lean_ctor_get(v___x_2789_, 0);
v_err_2801_ = lean_ctor_get(v___x_2789_, 1);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2789_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_err_2801_);
lean_inc(v_pos_2800_);
lean_dec(v___x_2789_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_pos_2800_);
lean_ctor_set(v_reuseFailAlloc_2807_, 1, v_err_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
v___jp_2809_:
{
lean_object* v___x_2812_; uint8_t v___x_2813_; 
v___x_2812_ = lean_obj_once(&l_Std_Http_Protocol_H1_parseSingleHeader___closed__0, &l_Std_Http_Protocol_H1_parseSingleHeader___closed__0_once, _init_l_Std_Http_Protocol_H1_parseSingleHeader___closed__0);
v___x_2813_ = l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_2811_, v___x_2812_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2814_; uint8_t v___x_2815_; 
v___x_2814_ = lean_obj_once(&l_Std_Http_Protocol_H1_parseSingleHeader___closed__2, &l_Std_Http_Protocol_H1_parseSingleHeader___closed__2_once, _init_l_Std_Http_Protocol_H1_parseSingleHeader___closed__2);
v___x_2815_ = l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_2811_, v___x_2814_);
lean_dec(v_res_2811_);
if (v___x_2815_ == 0)
{
lean_object* v___x_2816_; 
v___x_2816_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_2779_, v_pos_2810_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_pos_2817_; lean_object* v_res_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v_pos_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_pos_2817_);
v_res_2818_ = lean_ctor_get(v___x_2816_, 1);
lean_inc(v_res_2818_);
lean_dec_ref(v___x_2816_);
v___x_2819_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2820_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2819_, v_pos_2817_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_pos_2821_; 
v_pos_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_pos_2821_);
lean_dec_ref(v___x_2820_);
v_pos_2782_ = v_pos_2821_;
v_res_2783_ = v_res_2818_;
goto v___jp_2781_;
}
else
{
lean_object* v_pos_2822_; lean_object* v_err_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_dec(v_res_2818_);
v_pos_2822_ = lean_ctor_get(v___x_2820_, 0);
v_err_2823_ = lean_ctor_get(v___x_2820_, 1);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2820_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_err_2823_);
lean_inc(v_pos_2822_);
lean_dec(v___x_2820_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_pos_2822_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v_err_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_pos_2831_; lean_object* v_res_2832_; 
v_pos_2831_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_pos_2831_);
v_res_2832_ = lean_ctor_get(v___x_2816_, 1);
lean_inc(v_res_2832_);
lean_dec_ref(v___x_2816_);
v_pos_2782_ = v_pos_2831_;
v_res_2783_ = v_res_2832_;
goto v___jp_2781_;
}
else
{
lean_object* v_pos_2833_; lean_object* v_err_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
v_pos_2833_ = lean_ctor_get(v___x_2816_, 0);
v_err_2834_ = lean_ctor_get(v___x_2816_, 1);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2816_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_err_2834_);
lean_inc(v_pos_2833_);
lean_dec(v___x_2816_);
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
}
else
{
v___y_2787_ = v_pos_2810_;
goto v___jp_2786_;
}
}
else
{
lean_dec(v_res_2811_);
v___y_2787_ = v_pos_2810_;
goto v___jp_2786_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader___boxed(lean_object* v_limits_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_2850_, v_a_2851_);
lean_dec_ref(v_limits_2850_);
return v_res_2852_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0(void){
_start:
{
uint32_t v___x_2853_; uint8_t v___x_2854_; 
v___x_2853_ = 92;
v___x_2854_ = lean_uint32_to_uint8(v___x_2853_);
return v___x_2854_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1(void){
_start:
{
uint8_t v___x_2855_; lean_object* v___x_2856_; 
v___x_2855_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0);
v___x_2856_ = lean_uint8_to_nat(v___x_2855_);
return v___x_2856_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2(void){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2857_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1);
v___x_2858_ = l_Nat_reprFast(v___x_2857_);
return v___x_2858_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__3(void){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2859_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2);
v___x_2860_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_2861_ = lean_string_append(v___x_2860_, v___x_2859_);
return v___x_2861_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__4(void){
_start:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2862_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__5));
v___x_2863_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__3);
v___x_2864_ = lean_string_append(v___x_2863_, v___x_2862_);
return v___x_2864_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__5(void){
_start:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2865_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__4);
v___x_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair(lean_object* v_a_2868_){
_start:
{
lean_object* v_array_2869_; lean_object* v_idx_2870_; lean_object* v___x_2871_; uint8_t v___x_2872_; 
v_array_2869_ = lean_ctor_get(v_a_2868_, 0);
v_idx_2870_ = lean_ctor_get(v_a_2868_, 1);
v___x_2871_ = lean_byte_array_size(v_array_2869_);
v___x_2872_ = lean_nat_dec_lt(v_idx_2870_, v___x_2871_);
if (v___x_2872_ == 0)
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2873_ = lean_box(0);
v___x_2874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2874_, 0, v_a_2868_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
return v___x_2874_;
}
else
{
uint8_t v___x_2875_; uint8_t v_got_2876_; uint8_t v___x_2877_; 
v___x_2875_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0);
v_got_2876_ = lean_byte_array_fget(v_array_2869_, v_idx_2870_);
v___x_2877_ = lean_uint8_dec_eq(v_got_2876_, v___x_2875_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__5, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__5_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__5);
v___x_2879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2879_, 0, v_a_2868_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
return v___x_2879_;
}
else
{
lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2915_; 
lean_inc(v_idx_2870_);
lean_inc_ref(v_array_2869_);
v_isSharedCheck_2915_ = !lean_is_exclusive(v_a_2868_);
if (v_isSharedCheck_2915_ == 0)
{
lean_object* v_unused_2916_; lean_object* v_unused_2917_; 
v_unused_2916_ = lean_ctor_get(v_a_2868_, 1);
lean_dec(v_unused_2916_);
v_unused_2917_ = lean_ctor_get(v_a_2868_, 0);
lean_dec(v_unused_2917_);
v___x_2881_ = v_a_2868_;
v_isShared_2882_ = v_isSharedCheck_2915_;
goto v_resetjp_2880_;
}
else
{
lean_dec(v_a_2868_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2915_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; uint8_t v___x_2885_; 
v___x_2883_ = lean_unsigned_to_nat(1u);
v___x_2884_ = lean_nat_add(v_idx_2870_, v___x_2883_);
lean_dec(v_idx_2870_);
v___x_2885_ = lean_nat_dec_lt(v___x_2884_, v___x_2871_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2887_; 
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 1, v___x_2884_);
v___x_2887_ = v___x_2881_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_array_2869_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v___x_2884_);
v___x_2887_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2888_ = lean_box(0);
v___x_2889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2887_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
return v___x_2889_;
}
}
else
{
uint8_t v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2894_; 
v___x_2891_ = lean_byte_array_fget(v_array_2869_, v___x_2884_);
v___x_2892_ = lean_nat_add(v___x_2884_, v___x_2883_);
lean_dec(v___x_2884_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 1, v___x_2892_);
v___x_2894_ = v___x_2881_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_array_2869_);
lean_ctor_set(v_reuseFailAlloc_2914_, 1, v___x_2892_);
v___x_2894_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; uint32_t v___x_2897_; uint8_t v___y_2905_; uint32_t v___x_2906_; uint8_t v___x_2907_; 
v___x_2895_ = lean_box(v___x_2891_);
lean_inc_ref(v___x_2894_);
v___x_2896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2894_);
lean_ctor_set(v___x_2896_, 1, v___x_2895_);
v___x_2897_ = lean_uint8_to_uint32(v___x_2891_);
v___x_2906_ = 9;
v___x_2907_ = lean_uint32_dec_eq(v___x_2897_, v___x_2906_);
if (v___x_2907_ == 0)
{
uint32_t v___x_2908_; uint8_t v___x_2909_; 
v___x_2908_ = 32;
v___x_2909_ = lean_uint32_dec_eq(v___x_2897_, v___x_2908_);
if (v___x_2909_ == 0)
{
uint32_t v___x_2910_; uint8_t v___x_2911_; 
v___x_2910_ = 33;
v___x_2911_ = lean_uint32_dec_le(v___x_2910_, v___x_2897_);
if (v___x_2911_ == 0)
{
lean_dec_ref(v___x_2896_);
goto v___jp_2898_;
}
else
{
uint32_t v___x_2912_; uint8_t v___x_2913_; 
v___x_2912_ = 126;
v___x_2913_ = lean_uint32_dec_le(v___x_2897_, v___x_2912_);
if (v___x_2913_ == 0)
{
lean_dec_ref(v___x_2896_);
goto v___jp_2898_;
}
else
{
v___y_2905_ = v___x_2885_;
goto v___jp_2904_;
}
}
}
else
{
v___y_2905_ = v___x_2885_;
goto v___jp_2904_;
}
}
else
{
v___y_2905_ = v___x_2885_;
goto v___jp_2904_;
}
v___jp_2898_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2899_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__6));
v___x_2900_ = l_Char_quote(v___x_2897_);
v___x_2901_ = lean_string_append(v___x_2899_, v___x_2900_);
lean_dec_ref(v___x_2900_);
v___x_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
v___x_2903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2894_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
return v___x_2903_;
}
v___jp_2904_:
{
if (v___y_2905_ == 0)
{
lean_dec_ref(v___x_2896_);
goto v___jp_2898_;
}
else
{
lean_dec_ref(v___x_2894_);
return v___x_2896_;
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
uint32_t v___x_2922_; uint8_t v___x_2923_; 
v___x_2922_ = 34;
v___x_2923_ = lean_uint32_to_uint8(v___x_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(lean_object* v_maxLength_2924_, lean_object* v_buf_2925_, lean_object* v_length_2926_, lean_object* v_a_2927_){
_start:
{
lean_object* v_array_2928_; lean_object* v_idx_2929_; lean_object* v___x_2930_; uint8_t v___x_2931_; 
v_array_2928_ = lean_ctor_get(v_a_2927_, 0);
v_idx_2929_ = lean_ctor_get(v_a_2927_, 1);
v___x_2930_ = lean_byte_array_size(v_array_2928_);
v___x_2931_ = lean_nat_dec_lt(v_idx_2929_, v___x_2930_);
if (v___x_2931_ == 0)
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
lean_dec(v_length_2926_);
lean_dec_ref(v_buf_2925_);
v___x_2932_ = lean_box(0);
v___x_2933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2933_, 0, v_a_2927_);
lean_ctor_set(v___x_2933_, 1, v___x_2932_);
return v___x_2933_;
}
else
{
lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_3007_; 
lean_inc(v_idx_2929_);
lean_inc_ref(v_array_2928_);
v_isSharedCheck_3007_ = !lean_is_exclusive(v_a_2927_);
if (v_isSharedCheck_3007_ == 0)
{
lean_object* v_unused_3008_; lean_object* v_unused_3009_; 
v_unused_3008_ = lean_ctor_get(v_a_2927_, 1);
lean_dec(v_unused_3008_);
v_unused_3009_ = lean_ctor_get(v_a_2927_, 0);
lean_dec(v_unused_3009_);
v___x_2935_ = v_a_2927_;
v_isShared_2936_ = v_isSharedCheck_3007_;
goto v_resetjp_2934_;
}
else
{
lean_dec(v_a_2927_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_3007_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
uint8_t v_c_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v_it_x27_2941_; 
v_c_2937_ = lean_byte_array_fget(v_array_2928_, v_idx_2929_);
v___x_2938_ = lean_unsigned_to_nat(1u);
v___x_2939_ = lean_nat_add(v_idx_2929_, v___x_2938_);
lean_dec(v_idx_2929_);
lean_inc(v___x_2939_);
lean_inc_ref(v_array_2928_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 1, v___x_2939_);
v_it_x27_2941_ = v___x_2935_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_array_2928_);
lean_ctor_set(v_reuseFailAlloc_3006_, 1, v___x_2939_);
v_it_x27_2941_ = v_reuseFailAlloc_3006_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
uint8_t v___y_2950_; uint8_t v___x_2957_; uint8_t v___x_2958_; 
v___x_2957_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3);
v___x_2958_ = lean_uint8_dec_eq(v_c_2937_, v___x_2957_);
if (v___x_2958_ == 0)
{
uint8_t v___x_2959_; uint8_t v___x_2960_; 
v___x_2959_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0);
v___x_2960_ = lean_uint8_dec_eq(v_c_2937_, v___x_2959_);
if (v___x_2960_ == 0)
{
uint32_t v___x_2961_; uint32_t v___x_2967_; uint8_t v___x_2968_; 
lean_dec(v___x_2939_);
lean_dec_ref(v_array_2928_);
v___x_2961_ = lean_uint8_to_uint32(v_c_2937_);
v___x_2967_ = 9;
v___x_2968_ = lean_uint32_dec_eq(v___x_2961_, v___x_2967_);
if (v___x_2968_ == 0)
{
uint32_t v___x_2969_; uint8_t v___x_2970_; 
v___x_2969_ = 32;
v___x_2970_ = lean_uint32_dec_eq(v___x_2961_, v___x_2969_);
if (v___x_2970_ == 0)
{
uint32_t v___x_2971_; uint8_t v___x_2972_; 
v___x_2971_ = 33;
v___x_2972_ = lean_uint32_dec_eq(v___x_2961_, v___x_2971_);
if (v___x_2972_ == 0)
{
uint32_t v___x_2973_; uint8_t v___x_2974_; 
v___x_2973_ = 35;
v___x_2974_ = lean_uint32_dec_le(v___x_2973_, v___x_2961_);
if (v___x_2974_ == 0)
{
goto v___jp_2962_;
}
else
{
uint32_t v___x_2975_; uint8_t v___x_2976_; 
v___x_2975_ = 91;
v___x_2976_ = lean_uint32_dec_le(v___x_2961_, v___x_2975_);
if (v___x_2976_ == 0)
{
goto v___jp_2962_;
}
else
{
goto v___jp_2942_;
}
}
}
else
{
v___y_2950_ = v___x_2931_;
goto v___jp_2949_;
}
}
else
{
v___y_2950_ = v___x_2931_;
goto v___jp_2949_;
}
}
else
{
v___y_2950_ = v___x_2931_;
goto v___jp_2949_;
}
v___jp_2962_:
{
uint32_t v___x_2963_; uint8_t v___x_2964_; 
v___x_2963_ = 93;
v___x_2964_ = lean_uint32_dec_le(v___x_2963_, v___x_2961_);
if (v___x_2964_ == 0)
{
v___y_2950_ = v___x_2960_;
goto v___jp_2949_;
}
else
{
uint32_t v___x_2965_; uint8_t v___x_2966_; 
v___x_2965_ = 126;
v___x_2966_ = lean_uint32_dec_le(v___x_2961_, v___x_2965_);
if (v___x_2966_ == 0)
{
v___y_2950_ = v___x_2960_;
goto v___jp_2949_;
}
else
{
v___y_2950_ = v___x_2931_;
goto v___jp_2949_;
}
}
}
}
else
{
uint8_t v___x_2977_; 
v___x_2977_ = lean_nat_dec_lt(v___x_2939_, v___x_2930_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
lean_dec(v___x_2939_);
lean_dec_ref(v_array_2928_);
lean_dec(v_length_2926_);
lean_dec_ref(v_buf_2925_);
v___x_2978_ = lean_box(0);
v___x_2979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2979_, 0, v_it_x27_2941_);
lean_ctor_set(v___x_2979_, 1, v___x_2978_);
return v___x_2979_;
}
else
{
uint8_t v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; uint32_t v___x_2983_; uint8_t v___y_2985_; uint32_t v___x_2997_; uint8_t v___x_2998_; 
lean_dec_ref(v_it_x27_2941_);
v___x_2980_ = lean_byte_array_fget(v_array_2928_, v___x_2939_);
v___x_2981_ = lean_nat_add(v___x_2939_, v___x_2938_);
lean_dec(v___x_2939_);
v___x_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2982_, 0, v_array_2928_);
lean_ctor_set(v___x_2982_, 1, v___x_2981_);
v___x_2983_ = lean_uint8_to_uint32(v___x_2980_);
v___x_2997_ = 9;
v___x_2998_ = lean_uint32_dec_eq(v___x_2983_, v___x_2997_);
if (v___x_2998_ == 0)
{
uint32_t v___x_2999_; uint8_t v___x_3000_; 
v___x_2999_ = 32;
v___x_3000_ = lean_uint32_dec_eq(v___x_2983_, v___x_2999_);
if (v___x_3000_ == 0)
{
uint32_t v___x_3001_; uint8_t v___x_3002_; 
v___x_3001_ = 33;
v___x_3002_ = lean_uint32_dec_le(v___x_3001_, v___x_2983_);
if (v___x_3002_ == 0)
{
v___y_2985_ = v___x_2958_;
goto v___jp_2984_;
}
else
{
uint32_t v___x_3003_; uint8_t v___x_3004_; 
v___x_3003_ = 126;
v___x_3004_ = lean_uint32_dec_le(v___x_2983_, v___x_3003_);
if (v___x_3004_ == 0)
{
v___y_2985_ = v___x_2958_;
goto v___jp_2984_;
}
else
{
v___y_2985_ = v___x_2977_;
goto v___jp_2984_;
}
}
}
else
{
v___y_2985_ = v___x_2977_;
goto v___jp_2984_;
}
}
else
{
v___y_2985_ = v___x_2977_;
goto v___jp_2984_;
}
v___jp_2984_:
{
if (v___y_2985_ == 0)
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
lean_dec(v_length_2926_);
lean_dec_ref(v_buf_2925_);
v___x_2986_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__6));
v___x_2987_ = l_Char_quote(v___x_2983_);
v___x_2988_ = lean_string_append(v___x_2986_, v___x_2987_);
lean_dec_ref(v___x_2987_);
v___x_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2988_);
v___x_2990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2982_);
lean_ctor_set(v___x_2990_, 1, v___x_2989_);
return v___x_2990_;
}
else
{
lean_object* v___x_2991_; uint8_t v___x_2992_; 
v___x_2991_ = lean_nat_add(v_length_2926_, v___x_2938_);
lean_dec(v_length_2926_);
v___x_2992_ = lean_nat_dec_lt(v_maxLength_2924_, v___x_2991_);
if (v___x_2992_ == 0)
{
lean_object* v___x_2993_; 
v___x_2993_ = lean_byte_array_push(v_buf_2925_, v___x_2980_);
v_buf_2925_ = v___x_2993_;
v_length_2926_ = v___x_2991_;
v_a_2927_ = v___x_2982_;
goto _start;
}
else
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
lean_dec(v___x_2991_);
lean_dec_ref(v_buf_2925_);
v___x_2995_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_2996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2982_);
lean_ctor_set(v___x_2996_, 1, v___x_2995_);
return v___x_2996_;
}
}
}
}
}
}
else
{
lean_object* v___x_3005_; 
lean_dec(v___x_2939_);
lean_dec_ref(v_array_2928_);
lean_dec(v_length_2926_);
v___x_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3005_, 0, v_it_x27_2941_);
lean_ctor_set(v___x_3005_, 1, v_buf_2925_);
return v___x_3005_;
}
v___jp_2942_:
{
lean_object* v___x_2943_; uint8_t v___x_2944_; 
v___x_2943_ = lean_nat_add(v_length_2926_, v___x_2938_);
lean_dec(v_length_2926_);
v___x_2944_ = lean_nat_dec_lt(v_maxLength_2924_, v___x_2943_);
if (v___x_2944_ == 0)
{
lean_object* v___x_2945_; 
v___x_2945_ = lean_byte_array_push(v_buf_2925_, v_c_2937_);
v_buf_2925_ = v___x_2945_;
v_length_2926_ = v___x_2943_;
v_a_2927_ = v_it_x27_2941_;
goto _start;
}
else
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
lean_dec(v___x_2943_);
lean_dec_ref(v_buf_2925_);
v___x_2947_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_2948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2948_, 0, v_it_x27_2941_);
lean_ctor_set(v___x_2948_, 1, v___x_2947_);
return v___x_2948_;
}
}
v___jp_2949_:
{
if (v___y_2950_ == 0)
{
lean_object* v___x_2951_; uint32_t v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
lean_dec(v_length_2926_);
lean_dec_ref(v_buf_2925_);
v___x_2951_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2));
v___x_2952_ = lean_uint8_to_uint32(v_c_2937_);
v___x_2953_ = l_Char_quote(v___x_2952_);
v___x_2954_ = lean_string_append(v___x_2951_, v___x_2953_);
lean_dec_ref(v___x_2953_);
v___x_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
v___x_2956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2956_, 0, v_it_x27_2941_);
lean_ctor_set(v___x_2956_, 1, v___x_2955_);
return v___x_2956_;
}
else
{
goto v___jp_2942_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___boxed(lean_object* v_maxLength_3010_, lean_object* v_buf_3011_, lean_object* v_length_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_3010_, v_buf_3011_, v_length_3012_, v_a_3013_);
lean_dec(v_maxLength_3010_);
return v_res_3014_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__0(void){
_start:
{
uint8_t v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3);
v___x_3016_ = lean_uint8_to_nat(v___x_3015_);
return v___x_3016_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1(void){
_start:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3017_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__0);
v___x_3018_ = l_Nat_reprFast(v___x_3017_);
return v___x_3018_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__2(void){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3019_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1);
v___x_3020_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_3021_ = lean_string_append(v___x_3020_, v___x_3019_);
return v___x_3021_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__3(void){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3022_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__5));
v___x_3023_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__2);
v___x_3024_ = lean_string_append(v___x_3023_, v___x_3022_);
return v___x_3024_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__4(void){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__3);
v___x_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(lean_object* v_maxLength_3027_, lean_object* v_a_3028_){
_start:
{
lean_object* v_array_3029_; lean_object* v_idx_3030_; lean_object* v___x_3031_; uint8_t v___x_3032_; 
v_array_3029_ = lean_ctor_get(v_a_3028_, 0);
v_idx_3030_ = lean_ctor_get(v_a_3028_, 1);
v___x_3031_ = lean_byte_array_size(v_array_3029_);
v___x_3032_ = lean_nat_dec_lt(v_idx_3030_, v___x_3031_);
if (v___x_3032_ == 0)
{
lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3033_ = lean_box(0);
v___x_3034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3034_, 0, v_a_3028_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
return v___x_3034_;
}
else
{
uint8_t v___x_3035_; uint8_t v_got_3036_; uint8_t v___x_3037_; 
v___x_3035_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__3);
v_got_3036_ = lean_byte_array_fget(v_array_3029_, v_idx_3030_);
v___x_3037_ = lean_uint8_dec_eq(v_got_3036_, v___x_3035_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3038_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__4);
v___x_3039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3039_, 0, v_a_3028_);
lean_ctor_set(v___x_3039_, 1, v___x_3038_);
return v___x_3039_;
}
else
{
lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3068_; 
lean_inc(v_idx_3030_);
lean_inc_ref(v_array_3029_);
v_isSharedCheck_3068_ = !lean_is_exclusive(v_a_3028_);
if (v_isSharedCheck_3068_ == 0)
{
lean_object* v_unused_3069_; lean_object* v_unused_3070_; 
v_unused_3069_ = lean_ctor_get(v_a_3028_, 1);
lean_dec(v_unused_3069_);
v_unused_3070_ = lean_ctor_get(v_a_3028_, 0);
lean_dec(v_unused_3070_);
v___x_3041_ = v_a_3028_;
v_isShared_3042_ = v_isSharedCheck_3068_;
goto v_resetjp_3040_;
}
else
{
lean_dec(v_a_3028_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3068_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3046_; 
v___x_3043_ = lean_unsigned_to_nat(1u);
v___x_3044_ = lean_nat_add(v_idx_3030_, v___x_3043_);
lean_dec(v_idx_3030_);
if (v_isShared_3042_ == 0)
{
lean_ctor_set(v___x_3041_, 1, v___x_3044_);
v___x_3046_ = v___x_3041_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_array_3029_);
lean_ctor_set(v_reuseFailAlloc_3067_, 1, v___x_3044_);
v___x_3046_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3047_ = l_ByteArray_empty;
v___x_3048_ = lean_unsigned_to_nat(0u);
v___x_3049_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_3027_, v___x_3047_, v___x_3048_, v___x_3046_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v_pos_3050_; lean_object* v_res_3051_; uint8_t v___x_3052_; 
v_pos_3050_ = lean_ctor_get(v___x_3049_, 0);
lean_inc(v_pos_3050_);
v_res_3051_ = lean_ctor_get(v___x_3049_, 1);
lean_inc(v_res_3051_);
lean_dec_ref(v___x_3049_);
v___x_3052_ = lean_string_validate_utf8(v_res_3051_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
lean_dec(v_res_3051_);
v___x_3053_ = lean_box(0);
v___x_3054_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_3053_, v_pos_3050_);
return v___x_3054_;
}
else
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3055_ = lean_string_from_utf8_unchecked(v_res_3051_);
v___x_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
v___x_3057_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_3056_, v_pos_3050_);
lean_dec_ref(v___x_3056_);
return v___x_3057_;
}
}
else
{
lean_object* v_pos_3058_; lean_object* v_err_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
v_pos_3058_ = lean_ctor_get(v___x_3049_, 0);
v_err_3059_ = lean_ctor_get(v___x_3049_, 1);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___x_3049_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_err_3059_);
lean_inc(v_pos_3058_);
lean_dec(v___x_3049_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___boxed(lean_object* v_maxLength_3071_, lean_object* v_a_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxLength_3071_, v_a_3072_);
lean_dec(v_maxLength_3071_);
return v_res_3073_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__0(uint8_t v___y_3074_){
_start:
{
uint32_t v___x_3075_; uint32_t v___x_3076_; uint8_t v___x_3077_; 
v___x_3075_ = lean_uint8_to_uint32(v___y_3074_);
v___x_3076_ = 32;
v___x_3077_ = lean_uint32_dec_eq(v___x_3075_, v___x_3076_);
if (v___x_3077_ == 0)
{
uint32_t v___x_3078_; uint8_t v___x_3079_; 
v___x_3078_ = 9;
v___x_3079_ = lean_uint32_dec_eq(v___x_3075_, v___x_3078_);
return v___x_3079_;
}
else
{
return v___x_3077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__0___boxed(lean_object* v___y_3080_){
_start:
{
uint8_t v___y_10054__boxed_3081_; uint8_t v_res_3082_; lean_object* v_r_3083_; 
v___y_10054__boxed_3081_ = lean_unbox(v___y_3080_);
v_res_3082_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__0(v___y_10054__boxed_3081_);
v_r_3083_ = lean_box(v_res_3082_);
return v_r_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(lean_object* v___f_3084_, lean_object* v_maxSpaceSequence_3085_, lean_object* v_x_3086_, lean_object* v___y_3087_){
_start:
{
lean_object* v_pos_3089_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v_snd_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3125_; 
v___x_3092_ = lean_unsigned_to_nat(0u);
v___x_3093_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3084_, v_maxSpaceSequence_3085_, v___x_3092_, v___y_3087_);
v_snd_3094_ = lean_ctor_get(v___x_3093_, 1);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3125_ == 0)
{
lean_object* v_unused_3126_; 
v_unused_3126_ = lean_ctor_get(v___x_3093_, 0);
lean_dec(v_unused_3126_);
v___x_3096_ = v___x_3093_;
v_isShared_3097_ = v_isSharedCheck_3125_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_snd_3094_);
lean_dec(v___x_3093_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3125_;
goto v_resetjp_3095_;
}
v___jp_3088_:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = lean_box(0);
v___x_3091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3091_, 0, v_pos_3089_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
return v___x_3091_;
}
v_resetjp_3095_:
{
lean_object* v_fst_3098_; lean_object* v_snd_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3124_; 
v_fst_3098_ = lean_ctor_get(v_snd_3094_, 0);
v_snd_3099_ = lean_ctor_get(v_snd_3094_, 1);
v_isSharedCheck_3124_ = !lean_is_exclusive(v_snd_3094_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3101_ = v_snd_3094_;
v_isShared_3102_ = v_isSharedCheck_3124_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_snd_3099_);
lean_inc(v_fst_3098_);
lean_dec(v_snd_3094_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3124_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
uint8_t v___y_3104_; uint8_t v___x_3109_; 
v___x_3109_ = lean_unbox(v_snd_3099_);
lean_dec(v_snd_3099_);
if (v___x_3109_ == 0)
{
lean_object* v_array_3110_; lean_object* v_idx_3111_; lean_object* v___x_3112_; uint8_t v___x_3113_; 
lean_del_object(v___x_3096_);
v_array_3110_ = lean_ctor_get(v_fst_3098_, 0);
v_idx_3111_ = lean_ctor_get(v_fst_3098_, 1);
v___x_3112_ = lean_byte_array_size(v_array_3110_);
v___x_3113_ = lean_nat_dec_lt(v_idx_3111_, v___x_3112_);
if (v___x_3113_ == 0)
{
lean_del_object(v___x_3101_);
v_pos_3089_ = v_fst_3098_;
goto v___jp_3088_;
}
else
{
uint8_t v___x_3114_; uint32_t v___x_3115_; uint32_t v___x_3116_; uint8_t v___x_3117_; 
v___x_3114_ = lean_byte_array_fget(v_array_3110_, v_idx_3111_);
v___x_3115_ = lean_uint8_to_uint32(v___x_3114_);
v___x_3116_ = 32;
v___x_3117_ = lean_uint32_dec_eq(v___x_3115_, v___x_3116_);
if (v___x_3117_ == 0)
{
uint32_t v___x_3118_; uint8_t v___x_3119_; 
v___x_3118_ = 9;
v___x_3119_ = lean_uint32_dec_eq(v___x_3115_, v___x_3118_);
if (v___x_3119_ == 0)
{
lean_del_object(v___x_3101_);
v_pos_3089_ = v_fst_3098_;
goto v___jp_3088_;
}
else
{
v___y_3104_ = v___x_3113_;
goto v___jp_3103_;
}
}
else
{
v___y_3104_ = v___x_3113_;
goto v___jp_3103_;
}
}
}
else
{
lean_object* v___x_3120_; lean_object* v___x_3122_; 
lean_del_object(v___x_3101_);
v___x_3120_ = lean_box(0);
if (v_isShared_3097_ == 0)
{
lean_ctor_set_tag(v___x_3096_, 1);
lean_ctor_set(v___x_3096_, 1, v___x_3120_);
lean_ctor_set(v___x_3096_, 0, v_fst_3098_);
v___x_3122_ = v___x_3096_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_fst_3098_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v___x_3120_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
v___jp_3103_:
{
if (v___y_3104_ == 0)
{
lean_del_object(v___x_3101_);
v_pos_3089_ = v_fst_3098_;
goto v___jp_3088_;
}
else
{
lean_object* v___x_3105_; lean_object* v___x_3107_; 
v___x_3105_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2));
if (v_isShared_3102_ == 0)
{
lean_ctor_set_tag(v___x_3101_, 1);
lean_ctor_set(v___x_3101_, 1, v___x_3105_);
v___x_3107_ = v___x_3101_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_fst_3098_);
lean_ctor_set(v_reuseFailAlloc_3108_, 1, v___x_3105_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2___boxed(lean_object* v___f_3127_, lean_object* v_maxSpaceSequence_3128_, lean_object* v_x_3129_, lean_object* v___y_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_3127_, v_maxSpaceSequence_3128_, v_x_3129_, v___y_3130_);
lean_dec(v_maxSpaceSequence_3128_);
return v_res_3131_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__1(uint8_t v___x_3132_, uint8_t v___y_3133_){
_start:
{
uint32_t v___x_3134_; uint32_t v___x_3135_; uint8_t v___x_3136_; 
v___x_3134_ = lean_uint8_to_uint32(v___y_3133_);
v___x_3135_ = 32;
v___x_3136_ = lean_uint32_dec_eq(v___x_3134_, v___x_3135_);
if (v___x_3136_ == 0)
{
uint32_t v___x_3137_; uint8_t v___x_3138_; 
v___x_3137_ = 9;
v___x_3138_ = lean_uint32_dec_eq(v___x_3134_, v___x_3137_);
if (v___x_3138_ == 0)
{
return v___x_3138_;
}
else
{
return v___x_3132_;
}
}
else
{
return v___x_3132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__1___boxed(lean_object* v___x_3139_, lean_object* v___y_3140_){
_start:
{
uint8_t v___x_10158__boxed_3141_; uint8_t v___y_10159__boxed_3142_; uint8_t v_res_3143_; lean_object* v_r_3144_; 
v___x_10158__boxed_3141_ = lean_unbox(v___x_3139_);
v___y_10159__boxed_3142_ = lean_unbox(v___y_3140_);
v_res_3143_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__1(v___x_10158__boxed_3141_, v___y_10159__boxed_3142_);
v_r_3144_ = lean_box(v_res_3143_);
return v_r_3144_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__3(uint8_t v___x_3145_, uint8_t v_c_3146_){
_start:
{
uint32_t v___x_3147_; uint8_t v___y_3154_; uint32_t v___x_3159_; uint8_t v___x_3160_; 
v___x_3147_ = lean_uint8_to_uint32(v_c_3146_);
v___x_3159_ = 33;
v___x_3160_ = lean_uint32_dec_eq(v___x_3147_, v___x_3159_);
if (v___x_3160_ == 0)
{
uint32_t v___x_3161_; uint8_t v___x_3162_; 
v___x_3161_ = 35;
v___x_3162_ = lean_uint32_dec_eq(v___x_3147_, v___x_3161_);
if (v___x_3162_ == 0)
{
uint32_t v___x_3163_; uint8_t v___x_3164_; 
v___x_3163_ = 36;
v___x_3164_ = lean_uint32_dec_eq(v___x_3147_, v___x_3163_);
if (v___x_3164_ == 0)
{
uint32_t v___x_3165_; uint8_t v___x_3166_; 
v___x_3165_ = 37;
v___x_3166_ = lean_uint32_dec_eq(v___x_3147_, v___x_3165_);
if (v___x_3166_ == 0)
{
uint32_t v___x_3167_; uint8_t v___x_3168_; 
v___x_3167_ = 38;
v___x_3168_ = lean_uint32_dec_eq(v___x_3147_, v___x_3167_);
if (v___x_3168_ == 0)
{
uint32_t v___x_3169_; uint8_t v___x_3170_; 
v___x_3169_ = 39;
v___x_3170_ = lean_uint32_dec_eq(v___x_3147_, v___x_3169_);
if (v___x_3170_ == 0)
{
uint32_t v___x_3171_; uint8_t v___x_3172_; 
v___x_3171_ = 42;
v___x_3172_ = lean_uint32_dec_eq(v___x_3147_, v___x_3171_);
if (v___x_3172_ == 0)
{
uint32_t v___x_3173_; uint8_t v___x_3174_; 
v___x_3173_ = 43;
v___x_3174_ = lean_uint32_dec_eq(v___x_3147_, v___x_3173_);
if (v___x_3174_ == 0)
{
uint32_t v___x_3175_; uint8_t v___x_3176_; 
v___x_3175_ = 45;
v___x_3176_ = lean_uint32_dec_eq(v___x_3147_, v___x_3175_);
if (v___x_3176_ == 0)
{
uint32_t v___x_3177_; uint8_t v___x_3178_; 
v___x_3177_ = 46;
v___x_3178_ = lean_uint32_dec_eq(v___x_3147_, v___x_3177_);
if (v___x_3178_ == 0)
{
uint32_t v___x_3179_; uint8_t v___x_3180_; 
v___x_3179_ = 94;
v___x_3180_ = lean_uint32_dec_eq(v___x_3147_, v___x_3179_);
if (v___x_3180_ == 0)
{
uint32_t v___x_3181_; uint8_t v___x_3182_; 
v___x_3181_ = 95;
v___x_3182_ = lean_uint32_dec_eq(v___x_3147_, v___x_3181_);
if (v___x_3182_ == 0)
{
uint32_t v___x_3183_; uint8_t v___x_3184_; 
v___x_3183_ = 96;
v___x_3184_ = lean_uint32_dec_eq(v___x_3147_, v___x_3183_);
if (v___x_3184_ == 0)
{
uint32_t v___x_3185_; uint8_t v___x_3186_; 
v___x_3185_ = 124;
v___x_3186_ = lean_uint32_dec_eq(v___x_3147_, v___x_3185_);
if (v___x_3186_ == 0)
{
uint32_t v___x_3187_; uint8_t v___x_3188_; 
v___x_3187_ = 126;
v___x_3188_ = lean_uint32_dec_eq(v___x_3147_, v___x_3187_);
if (v___x_3188_ == 0)
{
uint32_t v___x_3189_; uint8_t v___x_3190_; 
v___x_3189_ = 48;
v___x_3190_ = lean_uint32_dec_le(v___x_3189_, v___x_3147_);
if (v___x_3190_ == 0)
{
v___y_3154_ = v___x_3190_;
goto v___jp_3153_;
}
else
{
uint32_t v___x_3191_; uint8_t v___x_3192_; 
v___x_3191_ = 57;
v___x_3192_ = lean_uint32_dec_le(v___x_3147_, v___x_3191_);
v___y_3154_ = v___x_3192_;
goto v___jp_3153_;
}
}
else
{
return v___x_3145_;
}
}
else
{
return v___x_3145_;
}
}
else
{
return v___x_3145_;
}
}
else
{
return v___x_3145_;
}
}
else
{
return v___x_3145_;
}
}
else
{
return v___x_3145_;
}
}
else
{
return v___x_3145_;
}
}
else
{
return v___x_3145_;
}
}
else
{
return v___x_3145_;
}
}
else
{
return v___x_3145_;
}
}
else
{
return v___x_3145_;
}
}
else
{
return v___x_3145_;
}
}
else
{
return v___x_3145_;
}
}
else
{
return v___x_3145_;
}
}
else
{
return v___x_3145_;
}
v___jp_3148_:
{
uint32_t v___x_3149_; uint8_t v___x_3150_; 
v___x_3149_ = 97;
v___x_3150_ = lean_uint32_dec_le(v___x_3149_, v___x_3147_);
if (v___x_3150_ == 0)
{
return v___x_3150_;
}
else
{
uint32_t v___x_3151_; uint8_t v___x_3152_; 
v___x_3151_ = 122;
v___x_3152_ = lean_uint32_dec_le(v___x_3147_, v___x_3151_);
return v___x_3152_;
}
}
v___jp_3153_:
{
if (v___y_3154_ == 0)
{
uint32_t v___x_3155_; uint8_t v___x_3156_; 
v___x_3155_ = 65;
v___x_3156_ = lean_uint32_dec_le(v___x_3155_, v___x_3147_);
if (v___x_3156_ == 0)
{
goto v___jp_3148_;
}
else
{
uint32_t v___x_3157_; uint8_t v___x_3158_; 
v___x_3157_ = 90;
v___x_3158_ = lean_uint32_dec_le(v___x_3147_, v___x_3157_);
if (v___x_3158_ == 0)
{
goto v___jp_3148_;
}
else
{
return v___x_3145_;
}
}
}
else
{
return v___y_3154_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__3___boxed(lean_object* v___x_3193_, lean_object* v_c_3194_){
_start:
{
uint8_t v___x_10174__boxed_3195_; uint8_t v_c_boxed_3196_; uint8_t v_res_3197_; lean_object* v_r_3198_; 
v___x_10174__boxed_3195_ = lean_unbox(v___x_3193_);
v_c_boxed_3196_ = lean_unbox(v_c_3194_);
v_res_3197_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__3(v___x_10174__boxed_3195_, v_c_boxed_3196_);
v_r_3198_ = lean_box(v_res_3197_);
return v_r_3198_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3(void){
_start:
{
uint32_t v___x_3203_; uint8_t v___x_3204_; 
v___x_3203_ = 61;
v___x_3204_ = lean_uint32_to_uint8(v___x_3203_);
return v___x_3204_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4(void){
_start:
{
uint8_t v___x_3205_; lean_object* v___x_3206_; 
v___x_3205_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3);
v___x_3206_ = lean_uint8_to_nat(v___x_3205_);
return v___x_3206_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5(void){
_start:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3207_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4);
v___x_3208_ = l_Nat_reprFast(v___x_3207_);
return v___x_3208_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6(void){
_start:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3209_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5);
v___x_3210_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_3211_ = lean_string_append(v___x_3210_, v___x_3209_);
return v___x_3211_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7(void){
_start:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3212_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__5));
v___x_3213_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6);
v___x_3214_ = lean_string_append(v___x_3213_, v___x_3212_);
return v___x_3214_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__8(void){
_start:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3215_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7);
v___x_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
return v___x_3216_;
}
}
static uint8_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__11(void){
_start:
{
uint32_t v___x_3220_; uint8_t v___x_3221_; 
v___x_3220_ = 59;
v___x_3221_ = lean_uint32_to_uint8(v___x_3220_);
return v___x_3221_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__12(void){
_start:
{
uint8_t v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__11, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__11_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__11);
v___x_3223_ = lean_uint8_to_nat(v___x_3222_);
return v___x_3223_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__13(void){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__12, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__12_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__12);
v___x_3225_ = l_Nat_reprFast(v___x_3224_);
return v___x_3225_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__14(void){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3226_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__13, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__13_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__13);
v___x_3227_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_3228_ = lean_string_append(v___x_3227_, v___x_3226_);
return v___x_3228_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__15(void){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3229_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__5));
v___x_3230_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__14, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__14_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__14);
v___x_3231_ = lean_string_append(v___x_3230_, v___x_3229_);
return v___x_3231_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__16(void){
_start:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3232_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__15, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__15_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__15);
v___x_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3232_);
return v___x_3233_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(lean_object* v_limits_3234_, lean_object* v_a_3235_){
_start:
{
lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3264_; lean_object* v_pos_3265_; lean_object* v_res_3266_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v_lower_3272_; lean_object* v_upper_3273_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3289_; lean_object* v_pos_3290_; lean_object* v_maxSpaceSequence_3294_; lean_object* v_maxChunkExtNameLength_3295_; lean_object* v_maxChunkExtValueLength_3296_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v_pos_3300_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; uint8_t v___y_3337_; lean_object* v___f_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v_snd_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3621_; 
v_maxSpaceSequence_3294_ = lean_ctor_get(v_limits_3234_, 8);
v_maxChunkExtNameLength_3295_ = lean_ctor_get(v_limits_3234_, 11);
v_maxChunkExtValueLength_3296_ = lean_ctor_get(v_limits_3234_, 12);
v___f_3340_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2));
v___x_3341_ = lean_unsigned_to_nat(0u);
v___x_3342_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3340_, v_maxSpaceSequence_3294_, v___x_3341_, v_a_3235_);
v_snd_3343_ = lean_ctor_get(v___x_3342_, 1);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3621_ == 0)
{
lean_object* v_unused_3622_; 
v_unused_3622_ = lean_ctor_get(v___x_3342_, 0);
lean_dec(v_unused_3622_);
v___x_3345_ = v___x_3342_;
v_isShared_3346_ = v_isSharedCheck_3621_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_snd_3343_);
lean_dec(v___x_3342_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3621_;
goto v_resetjp_3344_;
}
v___jp_3236_:
{
if (lean_obj_tag(v___y_3238_) == 0)
{
lean_object* v_pos_3239_; lean_object* v_res_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3253_; 
v_pos_3239_ = lean_ctor_get(v___y_3238_, 0);
v_res_3240_ = lean_ctor_get(v___y_3238_, 1);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___y_3238_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3242_ = v___y_3238_;
v_isShared_3243_ = v_isSharedCheck_3253_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_res_3240_);
lean_inc(v_pos_3239_);
lean_dec(v___y_3238_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3253_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3244_; 
v___x_3244_ = l_Std_Http_Chunk_ExtensionValue_ofString_x3f(v_res_3240_);
if (lean_obj_tag(v___x_3244_) == 1)
{
lean_object* v___x_3245_; lean_object* v___x_3247_; 
v___x_3245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___y_3237_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 1, v___x_3245_);
v___x_3247_ = v___x_3242_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_pos_3239_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v___x_3245_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
else
{
lean_object* v___x_3249_; lean_object* v___x_3251_; 
lean_dec(v___x_3244_);
lean_dec_ref(v___y_3237_);
v___x_3249_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1));
if (v_isShared_3243_ == 0)
{
lean_ctor_set_tag(v___x_3242_, 1);
lean_ctor_set(v___x_3242_, 1, v___x_3249_);
v___x_3251_ = v___x_3242_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_pos_3239_);
lean_ctor_set(v_reuseFailAlloc_3252_, 1, v___x_3249_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
else
{
lean_object* v_pos_3254_; lean_object* v_err_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_dec_ref(v___y_3237_);
v_pos_3254_ = lean_ctor_get(v___y_3238_, 0);
v_err_3255_ = lean_ctor_get(v___y_3238_, 1);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___y_3238_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___y_3238_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_err_3255_);
lean_inc(v_pos_3254_);
lean_dec(v___y_3238_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_pos_3254_);
lean_ctor_set(v_reuseFailAlloc_3261_, 1, v_err_3255_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
v___jp_3263_:
{
lean_object* v___x_3267_; 
v___x_3267_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_3266_, v_pos_3265_);
lean_dec(v_res_3266_);
v___y_3237_ = v___y_3264_;
v___y_3238_ = v___x_3267_;
goto v___jp_3236_;
}
v___jp_3268_:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; uint8_t v___x_3276_; 
v___x_3274_ = l_ByteArray_toByteSlice(v___y_3269_, v_lower_3272_, v_upper_3273_);
v___x_3275_ = l_ByteSlice_toByteArray(v___x_3274_);
v___x_3276_ = lean_string_validate_utf8(v___x_3275_);
if (v___x_3276_ == 0)
{
lean_object* v___x_3277_; 
lean_dec_ref(v___x_3275_);
v___x_3277_ = lean_box(0);
v___y_3264_ = v___y_3271_;
v_pos_3265_ = v___y_3270_;
v_res_3266_ = v___x_3277_;
goto v___jp_3263_;
}
else
{
lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3278_ = lean_string_from_utf8_unchecked(v___x_3275_);
v___x_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
v___y_3264_ = v___y_3271_;
v_pos_3265_ = v___y_3270_;
v_res_3266_ = v___x_3279_;
goto v___jp_3263_;
}
}
v___jp_3280_:
{
uint8_t v___x_3287_; 
v___x_3287_ = lean_nat_dec_le(v___y_3282_, v___y_3285_);
if (v___x_3287_ == 0)
{
lean_dec(v___y_3282_);
v___y_3269_ = v___y_3281_;
v___y_3270_ = v___y_3283_;
v___y_3271_ = v___y_3284_;
v_lower_3272_ = v___y_3286_;
v_upper_3273_ = v___y_3285_;
goto v___jp_3268_;
}
else
{
lean_dec(v___y_3285_);
v___y_3269_ = v___y_3281_;
v___y_3270_ = v___y_3283_;
v___y_3271_ = v___y_3284_;
v_lower_3272_ = v___y_3286_;
v_upper_3273_ = v___y_3282_;
goto v___jp_3268_;
}
}
v___jp_3288_:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3291_ = lean_box(0);
v___x_3292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___y_3289_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
v___x_3293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3293_, 0, v_pos_3290_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
return v___x_3293_;
}
v___jp_3297_:
{
lean_object* v___x_3301_; 
lean_inc_ref(v_pos_3300_);
v___x_3301_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxChunkExtValueLength_3296_, v_pos_3300_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_dec_ref(v_pos_3300_);
lean_dec_ref(v___y_3298_);
v___y_3237_ = v___y_3299_;
v___y_3238_ = v___x_3301_;
goto v___jp_3236_;
}
else
{
lean_object* v_pos_3302_; lean_object* v_idx_3303_; lean_object* v_array_3304_; lean_object* v_idx_3305_; uint8_t v___x_3306_; 
v_pos_3302_ = lean_ctor_get(v___x_3301_, 0);
lean_inc(v_pos_3302_);
v_idx_3303_ = lean_ctor_get(v_pos_3300_, 1);
lean_inc(v_idx_3303_);
lean_dec_ref(v_pos_3300_);
v_array_3304_ = lean_ctor_get(v_pos_3302_, 0);
v_idx_3305_ = lean_ctor_get(v_pos_3302_, 1);
v___x_3306_ = lean_nat_dec_eq(v_idx_3303_, v_idx_3305_);
lean_dec(v_idx_3303_);
if (v___x_3306_ == 0)
{
lean_dec(v_pos_3302_);
lean_dec_ref(v___y_3298_);
v___y_3237_ = v___y_3299_;
v___y_3238_ = v___x_3301_;
goto v___jp_3236_;
}
else
{
lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3330_; 
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3330_ == 0)
{
lean_object* v_unused_3331_; lean_object* v_unused_3332_; 
v_unused_3331_ = lean_ctor_get(v___x_3301_, 1);
lean_dec(v_unused_3331_);
v_unused_3332_ = lean_ctor_get(v___x_3301_, 0);
lean_dec(v_unused_3332_);
v___x_3308_ = v___x_3301_;
v_isShared_3309_ = v_isSharedCheck_3330_;
goto v_resetjp_3307_;
}
else
{
lean_dec(v___x_3301_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3330_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v_snd_3312_; lean_object* v_snd_3313_; uint8_t v___x_3314_; 
v___x_3310_ = lean_unsigned_to_nat(0u);
lean_inc(v_pos_3302_);
v___x_3311_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___y_3298_, v_maxChunkExtValueLength_3296_, v___x_3310_, v_pos_3302_);
v_snd_3312_ = lean_ctor_get(v___x_3311_, 1);
lean_inc(v_snd_3312_);
v_snd_3313_ = lean_ctor_get(v_snd_3312_, 1);
v___x_3314_ = lean_unbox(v_snd_3313_);
if (v___x_3314_ == 0)
{
lean_object* v_fst_3315_; lean_object* v_fst_3316_; uint8_t v___x_3317_; 
v_fst_3315_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_fst_3315_);
lean_dec_ref(v___x_3311_);
v_fst_3316_ = lean_ctor_get(v_snd_3312_, 0);
lean_inc(v_fst_3316_);
lean_dec(v_snd_3312_);
v___x_3317_ = lean_nat_dec_eq(v_fst_3315_, v___x_3310_);
if (v___x_3317_ == 0)
{
lean_object* v___x_3318_; lean_object* v___x_3319_; uint8_t v___x_3320_; 
lean_inc(v_idx_3305_);
lean_inc_ref(v_array_3304_);
lean_del_object(v___x_3308_);
lean_dec(v_pos_3302_);
v___x_3318_ = lean_nat_add(v_idx_3305_, v_fst_3315_);
lean_dec(v_fst_3315_);
v___x_3319_ = lean_byte_array_size(v_array_3304_);
v___x_3320_ = lean_nat_dec_le(v_idx_3305_, v___x_3310_);
if (v___x_3320_ == 0)
{
v___y_3281_ = v_array_3304_;
v___y_3282_ = v___x_3318_;
v___y_3283_ = v_fst_3316_;
v___y_3284_ = v___y_3299_;
v___y_3285_ = v___x_3319_;
v___y_3286_ = v_idx_3305_;
goto v___jp_3280_;
}
else
{
lean_dec(v_idx_3305_);
v___y_3281_ = v_array_3304_;
v___y_3282_ = v___x_3318_;
v___y_3283_ = v_fst_3316_;
v___y_3284_ = v___y_3299_;
v___y_3285_ = v___x_3319_;
v___y_3286_ = v___x_3310_;
goto v___jp_3280_;
}
}
else
{
lean_object* v___x_3321_; lean_object* v___x_3323_; 
lean_dec(v_fst_3316_);
lean_dec(v_fst_3315_);
lean_dec_ref(v___y_3299_);
v___x_3321_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 1, v___x_3321_);
v___x_3323_ = v___x_3308_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_pos_3302_);
lean_ctor_set(v_reuseFailAlloc_3324_, 1, v___x_3321_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
else
{
lean_object* v_fst_3325_; lean_object* v___x_3326_; lean_object* v___x_3328_; 
lean_dec_ref(v___x_3311_);
lean_dec(v_pos_3302_);
lean_dec_ref(v___y_3299_);
v_fst_3325_ = lean_ctor_get(v_snd_3312_, 0);
lean_inc(v_fst_3325_);
lean_dec(v_snd_3312_);
v___x_3326_ = lean_box(0);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 1, v___x_3326_);
lean_ctor_set(v___x_3308_, 0, v_fst_3325_);
v___x_3328_ = v___x_3308_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_fst_3325_);
lean_ctor_set(v_reuseFailAlloc_3329_, 1, v___x_3326_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
}
}
}
v___jp_3333_:
{
if (v___y_3337_ == 0)
{
v___y_3298_ = v___y_3334_;
v___y_3299_ = v___y_3336_;
v_pos_3300_ = v___y_3335_;
goto v___jp_3297_;
}
else
{
lean_object* v___x_3338_; lean_object* v___x_3339_; 
lean_dec_ref(v___y_3336_);
lean_dec_ref(v___y_3334_);
v___x_3338_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2));
v___x_3339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3339_, 0, v___y_3335_);
lean_ctor_set(v___x_3339_, 1, v___x_3338_);
return v___x_3339_;
}
}
v_resetjp_3344_:
{
lean_object* v_snd_3347_; uint8_t v___x_3348_; 
v_snd_3347_ = lean_ctor_get(v_snd_3343_, 1);
v___x_3348_ = lean_unbox(v_snd_3347_);
if (v___x_3348_ == 0)
{
lean_object* v_fst_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3609_; 
v_fst_3349_ = lean_ctor_get(v_snd_3343_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v_snd_3343_);
if (v_isSharedCheck_3609_ == 0)
{
lean_object* v_unused_3610_; 
v_unused_3610_ = lean_ctor_get(v_snd_3343_, 1);
lean_dec(v_unused_3610_);
v___x_3351_ = v_snd_3343_;
v_isShared_3352_ = v_isSharedCheck_3609_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_fst_3349_);
lean_dec(v_snd_3343_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3609_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v_array_3353_; lean_object* v_idx_3354_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v_pos_3358_; lean_object* v_array_3359_; lean_object* v_idx_3360_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; uint8_t v___y_3423_; lean_object* v_pos_3431_; lean_object* v_res_3432_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v_lower_3500_; lean_object* v_upper_3501_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___f_3515_; lean_object* v_pos_3517_; lean_object* v___y_3550_; uint8_t v___y_3551_; lean_object* v_pos_3555_; lean_object* v_array_3556_; lean_object* v_idx_3557_; uint8_t v___y_3598_; lean_object* v___x_3601_; uint8_t v___x_3602_; 
v_array_3353_ = lean_ctor_get(v_fst_3349_, 0);
v_idx_3354_ = lean_ctor_get(v_fst_3349_, 1);
v___f_3515_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_3601_ = lean_byte_array_size(v_array_3353_);
v___x_3602_ = lean_nat_dec_lt(v_idx_3354_, v___x_3601_);
if (v___x_3602_ == 0)
{
lean_inc(v_idx_3354_);
lean_inc_ref(v_array_3353_);
v_pos_3555_ = v_fst_3349_;
v_array_3556_ = v_array_3353_;
v_idx_3557_ = v_idx_3354_;
goto v___jp_3554_;
}
else
{
uint8_t v___x_3603_; uint32_t v___x_3604_; uint32_t v___x_3605_; uint8_t v___x_3606_; 
v___x_3603_ = lean_byte_array_fget(v_array_3353_, v_idx_3354_);
v___x_3604_ = lean_uint8_to_uint32(v___x_3603_);
v___x_3605_ = 32;
v___x_3606_ = lean_uint32_dec_eq(v___x_3604_, v___x_3605_);
if (v___x_3606_ == 0)
{
uint32_t v___x_3607_; uint8_t v___x_3608_; 
v___x_3607_ = 9;
v___x_3608_ = lean_uint32_dec_eq(v___x_3604_, v___x_3607_);
if (v___x_3608_ == 0)
{
lean_inc(v_idx_3354_);
lean_inc_ref(v_array_3353_);
v_pos_3555_ = v_fst_3349_;
v_array_3556_ = v_array_3353_;
v_idx_3557_ = v_idx_3354_;
goto v___jp_3554_;
}
else
{
v___y_3598_ = v___x_3602_;
goto v___jp_3597_;
}
}
else
{
v___y_3598_ = v___x_3602_;
goto v___jp_3597_;
}
}
v___jp_3355_:
{
lean_object* v___x_3361_; uint8_t v___x_3362_; 
v___x_3361_ = lean_byte_array_size(v_array_3359_);
v___x_3362_ = lean_nat_dec_lt(v_idx_3360_, v___x_3361_);
if (v___x_3362_ == 0)
{
lean_object* v___x_3363_; lean_object* v___x_3365_; 
lean_dec(v_idx_3360_);
lean_dec_ref(v_array_3359_);
lean_dec_ref(v___y_3356_);
v___x_3363_ = lean_box(0);
if (v_isShared_3352_ == 0)
{
lean_ctor_set_tag(v___x_3351_, 1);
lean_ctor_set(v___x_3351_, 1, v___x_3363_);
lean_ctor_set(v___x_3351_, 0, v_pos_3358_);
v___x_3365_ = v___x_3351_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_pos_3358_);
lean_ctor_set(v_reuseFailAlloc_3366_, 1, v___x_3363_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
else
{
uint8_t v___x_3367_; uint8_t v_got_3368_; uint8_t v___x_3369_; 
v___x_3367_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3);
v_got_3368_ = lean_byte_array_fget(v_array_3359_, v_idx_3360_);
v___x_3369_ = lean_uint8_dec_eq(v_got_3368_, v___x_3367_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3370_; lean_object* v___x_3372_; 
lean_dec(v_idx_3360_);
lean_dec_ref(v_array_3359_);
lean_dec_ref(v___y_3356_);
v___x_3370_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__8, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__8_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__8);
if (v_isShared_3352_ == 0)
{
lean_ctor_set_tag(v___x_3351_, 1);
lean_ctor_set(v___x_3351_, 1, v___x_3370_);
lean_ctor_set(v___x_3351_, 0, v_pos_3358_);
v___x_3372_ = v___x_3351_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_pos_3358_);
lean_ctor_set(v_reuseFailAlloc_3373_, 1, v___x_3370_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
else
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3377_; 
lean_dec_ref(v_pos_3358_);
v___x_3374_ = lean_unsigned_to_nat(1u);
v___x_3375_ = lean_nat_add(v_idx_3360_, v___x_3374_);
lean_dec(v_idx_3360_);
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 1, v___x_3375_);
lean_ctor_set(v___x_3351_, 0, v_array_3359_);
v___x_3377_ = v___x_3351_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_array_3359_);
lean_ctor_set(v_reuseFailAlloc_3418_, 1, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3378_; 
v___x_3378_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_3340_, v_maxSpaceSequence_3294_, v___y_3357_, v___x_3377_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_pos_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3407_; 
v_pos_3379_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3407_ == 0)
{
lean_object* v_unused_3408_; 
v_unused_3408_ = lean_ctor_get(v___x_3378_, 1);
lean_dec(v_unused_3408_);
v___x_3381_ = v___x_3378_;
v_isShared_3382_ = v_isSharedCheck_3407_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_pos_3379_);
lean_dec(v___x_3378_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3407_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3383_; lean_object* v___f_3384_; lean_object* v___x_3385_; lean_object* v_snd_3386_; lean_object* v_snd_3387_; uint8_t v___x_3388_; 
v___x_3383_ = lean_box(v___x_3362_);
v___f_3384_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3384_, 0, v___x_3383_);
v___x_3385_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3384_, v_maxSpaceSequence_3294_, v___x_3341_, v_pos_3379_);
v_snd_3386_ = lean_ctor_get(v___x_3385_, 1);
lean_inc(v_snd_3386_);
lean_dec_ref(v___x_3385_);
v_snd_3387_ = lean_ctor_get(v_snd_3386_, 1);
v___x_3388_ = lean_unbox(v_snd_3387_);
if (v___x_3388_ == 0)
{
lean_object* v_fst_3389_; lean_object* v_array_3390_; lean_object* v_idx_3391_; lean_object* v___x_3392_; lean_object* v___f_3393_; lean_object* v___x_3394_; uint8_t v___x_3395_; 
lean_del_object(v___x_3381_);
v_fst_3389_ = lean_ctor_get(v_snd_3386_, 0);
lean_inc(v_fst_3389_);
lean_dec(v_snd_3386_);
v_array_3390_ = lean_ctor_get(v_fst_3389_, 0);
v_idx_3391_ = lean_ctor_get(v_fst_3389_, 1);
v___x_3392_ = lean_box(v___x_3362_);
v___f_3393_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__3___boxed), 2, 1);
lean_closure_set(v___f_3393_, 0, v___x_3392_);
v___x_3394_ = lean_byte_array_size(v_array_3390_);
v___x_3395_ = lean_nat_dec_lt(v_idx_3391_, v___x_3394_);
if (v___x_3395_ == 0)
{
v___y_3298_ = v___f_3393_;
v___y_3299_ = v___y_3356_;
v_pos_3300_ = v_fst_3389_;
goto v___jp_3297_;
}
else
{
uint8_t v___x_3396_; uint32_t v___x_3397_; uint32_t v___x_3398_; uint8_t v___x_3399_; 
v___x_3396_ = lean_byte_array_fget(v_array_3390_, v_idx_3391_);
v___x_3397_ = lean_uint8_to_uint32(v___x_3396_);
v___x_3398_ = 32;
v___x_3399_ = lean_uint32_dec_eq(v___x_3397_, v___x_3398_);
if (v___x_3399_ == 0)
{
uint32_t v___x_3400_; uint8_t v___x_3401_; 
v___x_3400_ = 9;
v___x_3401_ = lean_uint32_dec_eq(v___x_3397_, v___x_3400_);
if (v___x_3401_ == 0)
{
v___y_3298_ = v___f_3393_;
v___y_3299_ = v___y_3356_;
v_pos_3300_ = v_fst_3389_;
goto v___jp_3297_;
}
else
{
v___y_3334_ = v___f_3393_;
v___y_3335_ = v_fst_3389_;
v___y_3336_ = v___y_3356_;
v___y_3337_ = v___x_3395_;
goto v___jp_3333_;
}
}
else
{
v___y_3334_ = v___f_3393_;
v___y_3335_ = v_fst_3389_;
v___y_3336_ = v___y_3356_;
v___y_3337_ = v___x_3395_;
goto v___jp_3333_;
}
}
}
else
{
lean_object* v_fst_3402_; lean_object* v___x_3403_; lean_object* v___x_3405_; 
lean_dec_ref(v___y_3356_);
v_fst_3402_ = lean_ctor_get(v_snd_3386_, 0);
lean_inc(v_fst_3402_);
lean_dec(v_snd_3386_);
v___x_3403_ = lean_box(0);
if (v_isShared_3382_ == 0)
{
lean_ctor_set_tag(v___x_3381_, 1);
lean_ctor_set(v___x_3381_, 1, v___x_3403_);
lean_ctor_set(v___x_3381_, 0, v_fst_3402_);
v___x_3405_ = v___x_3381_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_fst_3402_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v___x_3403_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
else
{
lean_object* v_pos_3409_; lean_object* v_err_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
lean_dec_ref(v___y_3356_);
v_pos_3409_ = lean_ctor_get(v___x_3378_, 0);
v_err_3410_ = lean_ctor_get(v___x_3378_, 1);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3378_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_err_3410_);
lean_inc(v_pos_3409_);
lean_dec(v___x_3378_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_pos_3409_);
lean_ctor_set(v_reuseFailAlloc_3416_, 1, v_err_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
}
}
}
v___jp_3419_:
{
if (v___y_3423_ == 0)
{
lean_object* v_array_3424_; lean_object* v_idx_3425_; 
lean_del_object(v___x_3345_);
v_array_3424_ = lean_ctor_get(v___y_3422_, 0);
lean_inc_ref(v_array_3424_);
v_idx_3425_ = lean_ctor_get(v___y_3422_, 1);
lean_inc(v_idx_3425_);
v___y_3356_ = v___y_3420_;
v___y_3357_ = v___y_3421_;
v_pos_3358_ = v___y_3422_;
v_array_3359_ = v_array_3424_;
v_idx_3360_ = v_idx_3425_;
goto v___jp_3355_;
}
else
{
lean_object* v___x_3426_; lean_object* v___x_3428_; 
lean_dec_ref(v___y_3420_);
lean_del_object(v___x_3351_);
v___x_3426_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2));
if (v_isShared_3346_ == 0)
{
lean_ctor_set_tag(v___x_3345_, 1);
lean_ctor_set(v___x_3345_, 1, v___x_3426_);
lean_ctor_set(v___x_3345_, 0, v___y_3422_);
v___x_3428_ = v___x_3345_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___y_3422_);
lean_ctor_set(v_reuseFailAlloc_3429_, 1, v___x_3426_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
v___jp_3430_:
{
lean_object* v___x_3433_; 
v___x_3433_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_3432_, v_pos_3431_);
lean_dec(v_res_3432_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_pos_3434_; lean_object* v_res_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v_pos_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_pos_3434_);
v_res_3435_ = lean_ctor_get(v___x_3433_, 1);
lean_inc(v_res_3435_);
lean_dec_ref(v___x_3433_);
v___x_3436_ = lean_box(0);
v___x_3437_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_3340_, v_maxSpaceSequence_3294_, v___x_3436_, v_pos_3434_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_pos_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3477_; 
v_pos_3438_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3477_ == 0)
{
lean_object* v_unused_3478_; 
v_unused_3478_ = lean_ctor_get(v___x_3437_, 1);
lean_dec(v_unused_3478_);
v___x_3440_ = v___x_3437_;
v_isShared_3441_ = v_isSharedCheck_3477_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_pos_3438_);
lean_dec(v___x_3437_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3477_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3442_; 
v___x_3442_ = l_Std_Http_Chunk_ExtensionName_ofString_x3f(v_res_3435_);
if (lean_obj_tag(v___x_3442_) == 1)
{
lean_object* v_val_3443_; lean_object* v_array_3444_; lean_object* v_idx_3445_; lean_object* v___x_3446_; uint8_t v___x_3447_; 
v_val_3443_ = lean_ctor_get(v___x_3442_, 0);
lean_inc(v_val_3443_);
lean_dec_ref(v___x_3442_);
v_array_3444_ = lean_ctor_get(v_pos_3438_, 0);
v_idx_3445_ = lean_ctor_get(v_pos_3438_, 1);
v___x_3446_ = lean_byte_array_size(v_array_3444_);
v___x_3447_ = lean_nat_dec_lt(v_idx_3445_, v___x_3446_);
if (v___x_3447_ == 0)
{
lean_del_object(v___x_3440_);
lean_del_object(v___x_3351_);
lean_del_object(v___x_3345_);
v___y_3289_ = v_val_3443_;
v_pos_3290_ = v_pos_3438_;
goto v___jp_3288_;
}
else
{
uint8_t v___x_3448_; uint8_t v___x_3449_; uint8_t v___x_3450_; 
v___x_3448_ = lean_byte_array_fget(v_array_3444_, v_idx_3445_);
v___x_3449_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3);
v___x_3450_ = lean_uint8_dec_eq(v___x_3448_, v___x_3449_);
if (v___x_3450_ == 0)
{
lean_del_object(v___x_3440_);
lean_del_object(v___x_3351_);
lean_del_object(v___x_3345_);
v___y_3289_ = v_val_3443_;
v_pos_3290_ = v_pos_3438_;
goto v___jp_3288_;
}
else
{
lean_object* v___x_3451_; lean_object* v___f_3452_; lean_object* v___x_3453_; lean_object* v_snd_3454_; lean_object* v_snd_3455_; uint8_t v___x_3456_; 
v___x_3451_ = lean_box(v___x_3450_);
v___f_3452_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3452_, 0, v___x_3451_);
v___x_3453_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3452_, v_maxSpaceSequence_3294_, v___x_3341_, v_pos_3438_);
v_snd_3454_ = lean_ctor_get(v___x_3453_, 1);
lean_inc(v_snd_3454_);
lean_dec_ref(v___x_3453_);
v_snd_3455_ = lean_ctor_get(v_snd_3454_, 1);
v___x_3456_ = lean_unbox(v_snd_3455_);
if (v___x_3456_ == 0)
{
lean_object* v_fst_3457_; lean_object* v_array_3458_; lean_object* v_idx_3459_; lean_object* v___x_3460_; uint8_t v___x_3461_; 
lean_del_object(v___x_3440_);
v_fst_3457_ = lean_ctor_get(v_snd_3454_, 0);
lean_inc(v_fst_3457_);
lean_dec(v_snd_3454_);
v_array_3458_ = lean_ctor_get(v_fst_3457_, 0);
v_idx_3459_ = lean_ctor_get(v_fst_3457_, 1);
v___x_3460_ = lean_byte_array_size(v_array_3458_);
v___x_3461_ = lean_nat_dec_lt(v_idx_3459_, v___x_3460_);
if (v___x_3461_ == 0)
{
lean_inc(v_idx_3459_);
lean_inc_ref(v_array_3458_);
lean_del_object(v___x_3345_);
v___y_3356_ = v_val_3443_;
v___y_3357_ = v___x_3436_;
v_pos_3358_ = v_fst_3457_;
v_array_3359_ = v_array_3458_;
v_idx_3360_ = v_idx_3459_;
goto v___jp_3355_;
}
else
{
uint8_t v___x_3462_; uint32_t v___x_3463_; uint32_t v___x_3464_; uint8_t v___x_3465_; 
v___x_3462_ = lean_byte_array_fget(v_array_3458_, v_idx_3459_);
v___x_3463_ = lean_uint8_to_uint32(v___x_3462_);
v___x_3464_ = 32;
v___x_3465_ = lean_uint32_dec_eq(v___x_3463_, v___x_3464_);
if (v___x_3465_ == 0)
{
uint32_t v___x_3466_; uint8_t v___x_3467_; 
v___x_3466_ = 9;
v___x_3467_ = lean_uint32_dec_eq(v___x_3463_, v___x_3466_);
if (v___x_3467_ == 0)
{
lean_inc(v_idx_3459_);
lean_inc_ref(v_array_3458_);
lean_del_object(v___x_3345_);
v___y_3356_ = v_val_3443_;
v___y_3357_ = v___x_3436_;
v_pos_3358_ = v_fst_3457_;
v_array_3359_ = v_array_3458_;
v_idx_3360_ = v_idx_3459_;
goto v___jp_3355_;
}
else
{
v___y_3420_ = v_val_3443_;
v___y_3421_ = v___x_3436_;
v___y_3422_ = v_fst_3457_;
v___y_3423_ = v___x_3461_;
goto v___jp_3419_;
}
}
else
{
v___y_3420_ = v_val_3443_;
v___y_3421_ = v___x_3436_;
v___y_3422_ = v_fst_3457_;
v___y_3423_ = v___x_3461_;
goto v___jp_3419_;
}
}
}
else
{
lean_object* v_fst_3468_; lean_object* v___x_3469_; lean_object* v___x_3471_; 
lean_dec(v_val_3443_);
lean_del_object(v___x_3351_);
lean_del_object(v___x_3345_);
v_fst_3468_ = lean_ctor_get(v_snd_3454_, 0);
lean_inc(v_fst_3468_);
lean_dec(v_snd_3454_);
v___x_3469_ = lean_box(0);
if (v_isShared_3441_ == 0)
{
lean_ctor_set_tag(v___x_3440_, 1);
lean_ctor_set(v___x_3440_, 1, v___x_3469_);
lean_ctor_set(v___x_3440_, 0, v_fst_3468_);
v___x_3471_ = v___x_3440_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_fst_3468_);
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
}
}
else
{
lean_object* v___x_3473_; lean_object* v___x_3475_; 
lean_dec(v___x_3442_);
lean_del_object(v___x_3351_);
lean_del_object(v___x_3345_);
v___x_3473_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__10));
if (v_isShared_3441_ == 0)
{
lean_ctor_set_tag(v___x_3440_, 1);
lean_ctor_set(v___x_3440_, 1, v___x_3473_);
v___x_3475_ = v___x_3440_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_pos_3438_);
lean_ctor_set(v_reuseFailAlloc_3476_, 1, v___x_3473_);
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
else
{
lean_object* v_pos_3479_; lean_object* v_err_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3487_; 
lean_dec(v_res_3435_);
lean_del_object(v___x_3351_);
lean_del_object(v___x_3345_);
v_pos_3479_ = lean_ctor_get(v___x_3437_, 0);
v_err_3480_ = lean_ctor_get(v___x_3437_, 1);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3482_ = v___x_3437_;
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_err_3480_);
lean_inc(v_pos_3479_);
lean_dec(v___x_3437_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3485_; 
if (v_isShared_3483_ == 0)
{
v___x_3485_ = v___x_3482_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_pos_3479_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_err_3480_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
else
{
lean_object* v_pos_3488_; lean_object* v_err_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3496_; 
lean_del_object(v___x_3351_);
lean_del_object(v___x_3345_);
v_pos_3488_ = lean_ctor_get(v___x_3433_, 0);
v_err_3489_ = lean_ctor_get(v___x_3433_, 1);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3491_ = v___x_3433_;
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_err_3489_);
lean_inc(v_pos_3488_);
lean_dec(v___x_3433_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3494_; 
if (v_isShared_3492_ == 0)
{
v___x_3494_ = v___x_3491_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_pos_3488_);
lean_ctor_set(v_reuseFailAlloc_3495_, 1, v_err_3489_);
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
v___jp_3497_:
{
lean_object* v___x_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; 
v___x_3502_ = l_ByteArray_toByteSlice(v___y_3499_, v_lower_3500_, v_upper_3501_);
v___x_3503_ = l_ByteSlice_toByteArray(v___x_3502_);
v___x_3504_ = lean_string_validate_utf8(v___x_3503_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3505_; 
lean_dec_ref(v___x_3503_);
v___x_3505_ = lean_box(0);
v_pos_3431_ = v___y_3498_;
v_res_3432_ = v___x_3505_;
goto v___jp_3430_;
}
else
{
lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3506_ = lean_string_from_utf8_unchecked(v___x_3503_);
v___x_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3506_);
v_pos_3431_ = v___y_3498_;
v_res_3432_ = v___x_3507_;
goto v___jp_3430_;
}
}
v___jp_3508_:
{
uint8_t v___x_3514_; 
v___x_3514_ = lean_nat_dec_le(v___y_3512_, v___y_3511_);
if (v___x_3514_ == 0)
{
lean_dec(v___y_3512_);
v___y_3498_ = v___y_3510_;
v___y_3499_ = v___y_3509_;
v_lower_3500_ = v___y_3513_;
v_upper_3501_ = v___y_3511_;
goto v___jp_3497_;
}
else
{
lean_dec(v___y_3511_);
v___y_3498_ = v___y_3510_;
v___y_3499_ = v___y_3509_;
v_lower_3500_ = v___y_3513_;
v_upper_3501_ = v___y_3512_;
goto v___jp_3497_;
}
}
v___jp_3516_:
{
lean_object* v___x_3518_; lean_object* v_snd_3519_; lean_object* v_snd_3520_; uint8_t v___x_3521_; 
lean_inc_ref(v_pos_3517_);
v___x_3518_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3515_, v_maxChunkExtNameLength_3295_, v___x_3341_, v_pos_3517_);
v_snd_3519_ = lean_ctor_get(v___x_3518_, 1);
lean_inc(v_snd_3519_);
v_snd_3520_ = lean_ctor_get(v_snd_3519_, 1);
v___x_3521_ = lean_unbox(v_snd_3520_);
if (v___x_3521_ == 0)
{
lean_object* v_fst_3522_; lean_object* v_fst_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3537_; 
v_fst_3522_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_fst_3522_);
lean_dec_ref(v___x_3518_);
v_fst_3523_ = lean_ctor_get(v_snd_3519_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v_snd_3519_);
if (v_isSharedCheck_3537_ == 0)
{
lean_object* v_unused_3538_; 
v_unused_3538_ = lean_ctor_get(v_snd_3519_, 1);
lean_dec(v_unused_3538_);
v___x_3525_ = v_snd_3519_;
v_isShared_3526_ = v_isSharedCheck_3537_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_fst_3523_);
lean_dec(v_snd_3519_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3537_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
uint8_t v___x_3527_; 
v___x_3527_ = lean_nat_dec_eq(v_fst_3522_, v___x_3341_);
if (v___x_3527_ == 0)
{
lean_object* v_array_3528_; lean_object* v_idx_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; uint8_t v___x_3532_; 
lean_del_object(v___x_3525_);
v_array_3528_ = lean_ctor_get(v_pos_3517_, 0);
lean_inc_ref(v_array_3528_);
v_idx_3529_ = lean_ctor_get(v_pos_3517_, 1);
lean_inc(v_idx_3529_);
lean_dec_ref(v_pos_3517_);
v___x_3530_ = lean_nat_add(v_idx_3529_, v_fst_3522_);
lean_dec(v_fst_3522_);
v___x_3531_ = lean_byte_array_size(v_array_3528_);
v___x_3532_ = lean_nat_dec_le(v_idx_3529_, v___x_3341_);
if (v___x_3532_ == 0)
{
v___y_3509_ = v_array_3528_;
v___y_3510_ = v_fst_3523_;
v___y_3511_ = v___x_3531_;
v___y_3512_ = v___x_3530_;
v___y_3513_ = v_idx_3529_;
goto v___jp_3508_;
}
else
{
lean_dec(v_idx_3529_);
v___y_3509_ = v_array_3528_;
v___y_3510_ = v_fst_3523_;
v___y_3511_ = v___x_3531_;
v___y_3512_ = v___x_3530_;
v___y_3513_ = v___x_3341_;
goto v___jp_3508_;
}
}
else
{
lean_object* v___x_3533_; lean_object* v___x_3535_; 
lean_dec(v_fst_3523_);
lean_dec(v_fst_3522_);
lean_del_object(v___x_3351_);
lean_del_object(v___x_3345_);
v___x_3533_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_3526_ == 0)
{
lean_ctor_set_tag(v___x_3525_, 1);
lean_ctor_set(v___x_3525_, 1, v___x_3533_);
lean_ctor_set(v___x_3525_, 0, v_pos_3517_);
v___x_3535_ = v___x_3525_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_pos_3517_);
lean_ctor_set(v_reuseFailAlloc_3536_, 1, v___x_3533_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
else
{
lean_object* v_fst_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3547_; 
lean_dec_ref(v___x_3518_);
lean_dec_ref(v_pos_3517_);
lean_del_object(v___x_3351_);
lean_del_object(v___x_3345_);
v_fst_3539_ = lean_ctor_get(v_snd_3519_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v_snd_3519_);
if (v_isSharedCheck_3547_ == 0)
{
lean_object* v_unused_3548_; 
v_unused_3548_ = lean_ctor_get(v_snd_3519_, 1);
lean_dec(v_unused_3548_);
v___x_3541_ = v_snd_3519_;
v_isShared_3542_ = v_isSharedCheck_3547_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_fst_3539_);
lean_dec(v_snd_3519_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3547_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3543_; lean_object* v___x_3545_; 
v___x_3543_ = lean_box(0);
if (v_isShared_3542_ == 0)
{
lean_ctor_set_tag(v___x_3541_, 1);
lean_ctor_set(v___x_3541_, 1, v___x_3543_);
v___x_3545_ = v___x_3541_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_fst_3539_);
lean_ctor_set(v_reuseFailAlloc_3546_, 1, v___x_3543_);
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
v___jp_3549_:
{
if (v___y_3551_ == 0)
{
v_pos_3517_ = v___y_3550_;
goto v___jp_3516_;
}
else
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
lean_del_object(v___x_3351_);
lean_del_object(v___x_3345_);
v___x_3552_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2));
v___x_3553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3553_, 0, v___y_3550_);
lean_ctor_set(v___x_3553_, 1, v___x_3552_);
return v___x_3553_;
}
}
v___jp_3554_:
{
lean_object* v___x_3558_; uint8_t v___x_3559_; 
v___x_3558_ = lean_byte_array_size(v_array_3556_);
v___x_3559_ = lean_nat_dec_lt(v_idx_3557_, v___x_3558_);
if (v___x_3559_ == 0)
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
lean_dec(v_idx_3557_);
lean_dec_ref(v_array_3556_);
lean_del_object(v___x_3351_);
lean_del_object(v___x_3345_);
v___x_3560_ = lean_box(0);
v___x_3561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3561_, 0, v_pos_3555_);
lean_ctor_set(v___x_3561_, 1, v___x_3560_);
return v___x_3561_;
}
else
{
uint8_t v___x_3562_; uint8_t v_got_3563_; uint8_t v___x_3564_; 
v___x_3562_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__11, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__11_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__11);
v_got_3563_ = lean_byte_array_fget(v_array_3556_, v_idx_3557_);
v___x_3564_ = lean_uint8_dec_eq(v_got_3563_, v___x_3562_);
if (v___x_3564_ == 0)
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
lean_dec(v_idx_3557_);
lean_dec_ref(v_array_3556_);
lean_del_object(v___x_3351_);
lean_del_object(v___x_3345_);
v___x_3565_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__16, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__16_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__16);
v___x_3566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3566_, 0, v_pos_3555_);
lean_ctor_set(v___x_3566_, 1, v___x_3565_);
return v___x_3566_;
}
else
{
lean_object* v___x_3567_; lean_object* v___f_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v_snd_3573_; lean_object* v_snd_3574_; uint8_t v___x_3575_; 
lean_dec_ref(v_pos_3555_);
v___x_3567_ = lean_box(v___x_3559_);
v___f_3568_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3568_, 0, v___x_3567_);
v___x_3569_ = lean_unsigned_to_nat(1u);
v___x_3570_ = lean_nat_add(v_idx_3557_, v___x_3569_);
lean_dec(v_idx_3557_);
v___x_3571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3571_, 0, v_array_3556_);
lean_ctor_set(v___x_3571_, 1, v___x_3570_);
v___x_3572_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3568_, v_maxSpaceSequence_3294_, v___x_3341_, v___x_3571_);
v_snd_3573_ = lean_ctor_get(v___x_3572_, 1);
lean_inc(v_snd_3573_);
lean_dec_ref(v___x_3572_);
v_snd_3574_ = lean_ctor_get(v_snd_3573_, 1);
v___x_3575_ = lean_unbox(v_snd_3574_);
if (v___x_3575_ == 0)
{
lean_object* v_fst_3576_; lean_object* v_array_3577_; lean_object* v_idx_3578_; lean_object* v___x_3579_; uint8_t v___x_3580_; 
v_fst_3576_ = lean_ctor_get(v_snd_3573_, 0);
lean_inc(v_fst_3576_);
lean_dec(v_snd_3573_);
v_array_3577_ = lean_ctor_get(v_fst_3576_, 0);
v_idx_3578_ = lean_ctor_get(v_fst_3576_, 1);
v___x_3579_ = lean_byte_array_size(v_array_3577_);
v___x_3580_ = lean_nat_dec_lt(v_idx_3578_, v___x_3579_);
if (v___x_3580_ == 0)
{
v_pos_3517_ = v_fst_3576_;
goto v___jp_3516_;
}
else
{
uint8_t v___x_3581_; uint32_t v___x_3582_; uint32_t v___x_3583_; uint8_t v___x_3584_; 
v___x_3581_ = lean_byte_array_fget(v_array_3577_, v_idx_3578_);
v___x_3582_ = lean_uint8_to_uint32(v___x_3581_);
v___x_3583_ = 32;
v___x_3584_ = lean_uint32_dec_eq(v___x_3582_, v___x_3583_);
if (v___x_3584_ == 0)
{
uint32_t v___x_3585_; uint8_t v___x_3586_; 
v___x_3585_ = 9;
v___x_3586_ = lean_uint32_dec_eq(v___x_3582_, v___x_3585_);
if (v___x_3586_ == 0)
{
v_pos_3517_ = v_fst_3576_;
goto v___jp_3516_;
}
else
{
v___y_3550_ = v_fst_3576_;
v___y_3551_ = v___x_3580_;
goto v___jp_3549_;
}
}
else
{
v___y_3550_ = v_fst_3576_;
v___y_3551_ = v___x_3580_;
goto v___jp_3549_;
}
}
}
else
{
lean_object* v_fst_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3595_; 
lean_del_object(v___x_3351_);
lean_del_object(v___x_3345_);
v_fst_3587_ = lean_ctor_get(v_snd_3573_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v_snd_3573_);
if (v_isSharedCheck_3595_ == 0)
{
lean_object* v_unused_3596_; 
v_unused_3596_ = lean_ctor_get(v_snd_3573_, 1);
lean_dec(v_unused_3596_);
v___x_3589_ = v_snd_3573_;
v_isShared_3590_ = v_isSharedCheck_3595_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_fst_3587_);
lean_dec(v_snd_3573_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3595_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3591_; lean_object* v___x_3593_; 
v___x_3591_ = lean_box(0);
if (v_isShared_3590_ == 0)
{
lean_ctor_set_tag(v___x_3589_, 1);
lean_ctor_set(v___x_3589_, 1, v___x_3591_);
v___x_3593_ = v___x_3589_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_fst_3587_);
lean_ctor_set(v_reuseFailAlloc_3594_, 1, v___x_3591_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
}
}
v___jp_3597_:
{
if (v___y_3598_ == 0)
{
lean_inc(v_idx_3354_);
lean_inc_ref(v_array_3353_);
v_pos_3555_ = v_fst_3349_;
v_array_3556_ = v_array_3353_;
v_idx_3557_ = v_idx_3354_;
goto v___jp_3554_;
}
else
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
lean_del_object(v___x_3351_);
lean_del_object(v___x_3345_);
v___x_3599_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2));
v___x_3600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3600_, 0, v_fst_3349_);
lean_ctor_set(v___x_3600_, 1, v___x_3599_);
return v___x_3600_;
}
}
}
}
else
{
lean_object* v_fst_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3619_; 
lean_del_object(v___x_3345_);
v_fst_3611_ = lean_ctor_get(v_snd_3343_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v_snd_3343_);
if (v_isSharedCheck_3619_ == 0)
{
lean_object* v_unused_3620_; 
v_unused_3620_ = lean_ctor_get(v_snd_3343_, 1);
lean_dec(v_unused_3620_);
v___x_3613_ = v_snd_3343_;
v_isShared_3614_ = v_isSharedCheck_3619_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_fst_3611_);
lean_dec(v_snd_3343_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3619_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3615_; lean_object* v___x_3617_; 
v___x_3615_ = lean_box(0);
if (v_isShared_3614_ == 0)
{
lean_ctor_set_tag(v___x_3613_, 1);
lean_ctor_set(v___x_3613_, 1, v___x_3615_);
v___x_3617_ = v___x_3613_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_fst_3611_);
lean_ctor_set(v_reuseFailAlloc_3618_, 1, v___x_3615_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___boxed(lean_object* v_limits_3623_, lean_object* v_a_3624_){
_start:
{
lean_object* v_res_3625_; 
v_res_3625_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_3623_, v_a_3624_);
lean_dec_ref(v_limits_3623_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0(lean_object* v_limits_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v_pos_3629_; lean_object* v_err_3630_; lean_object* v___x_3646_; 
lean_inc_ref(v___y_3627_);
v___x_3646_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_3626_, v___y_3627_);
if (lean_obj_tag(v___x_3646_) == 0)
{
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_pos_3647_; lean_object* v_res_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3656_; 
lean_dec_ref(v___y_3627_);
v_pos_3647_ = lean_ctor_get(v___x_3646_, 0);
v_res_3648_ = lean_ctor_get(v___x_3646_, 1);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3650_ = v___x_3646_;
v_isShared_3651_ = v_isSharedCheck_3656_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_res_3648_);
lean_inc(v_pos_3647_);
lean_dec(v___x_3646_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3656_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3652_; lean_object* v___x_3654_; 
v___x_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3652_, 0, v_res_3648_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 1, v___x_3652_);
v___x_3654_ = v___x_3650_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_pos_3647_);
lean_ctor_set(v_reuseFailAlloc_3655_, 1, v___x_3652_);
v___x_3654_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
return v___x_3654_;
}
}
}
else
{
lean_object* v_pos_3657_; lean_object* v_err_3658_; 
v_pos_3657_ = lean_ctor_get(v___x_3646_, 0);
lean_inc(v_pos_3657_);
v_err_3658_ = lean_ctor_get(v___x_3646_, 1);
lean_inc(v_err_3658_);
lean_dec_ref(v___x_3646_);
v_pos_3629_ = v_pos_3657_;
v_err_3630_ = v_err_3658_;
goto v___jp_3628_;
}
}
else
{
lean_object* v_err_3659_; 
v_err_3659_ = lean_ctor_get(v___x_3646_, 1);
lean_inc(v_err_3659_);
lean_dec_ref(v___x_3646_);
lean_inc_ref(v___y_3627_);
v_pos_3629_ = v___y_3627_;
v_err_3630_ = v_err_3659_;
goto v___jp_3628_;
}
v___jp_3628_:
{
lean_object* v_idx_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3644_; 
v_idx_3631_ = lean_ctor_get(v___y_3627_, 1);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___y_3627_);
if (v_isSharedCheck_3644_ == 0)
{
lean_object* v_unused_3645_; 
v_unused_3645_ = lean_ctor_get(v___y_3627_, 0);
lean_dec(v_unused_3645_);
v___x_3633_ = v___y_3627_;
v_isShared_3634_ = v_isSharedCheck_3644_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_idx_3631_);
lean_dec(v___y_3627_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3644_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v_idx_3635_; uint8_t v___x_3636_; 
v_idx_3635_ = lean_ctor_get(v_pos_3629_, 1);
v___x_3636_ = lean_nat_dec_eq(v_idx_3631_, v_idx_3635_);
lean_dec(v_idx_3631_);
if (v___x_3636_ == 0)
{
lean_object* v___x_3638_; 
if (v_isShared_3634_ == 0)
{
lean_ctor_set_tag(v___x_3633_, 1);
lean_ctor_set(v___x_3633_, 1, v_err_3630_);
lean_ctor_set(v___x_3633_, 0, v_pos_3629_);
v___x_3638_ = v___x_3633_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_pos_3629_);
lean_ctor_set(v_reuseFailAlloc_3639_, 1, v_err_3630_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
else
{
lean_object* v___x_3640_; lean_object* v___x_3642_; 
lean_dec(v_err_3630_);
v___x_3640_ = lean_box(0);
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 1, v___x_3640_);
lean_ctor_set(v___x_3633_, 0, v_pos_3629_);
v___x_3642_ = v___x_3633_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_pos_3629_);
lean_ctor_set(v_reuseFailAlloc_3643_, 1, v___x_3640_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed(lean_object* v_limits_3660_, lean_object* v___y_3661_){
_start:
{
lean_object* v_res_3662_; 
v_res_3662_ = l_Std_Http_Protocol_H1_parseChunkSize___lam__0(v_limits_3660_, v___y_3661_);
lean_dec_ref(v_limits_3660_);
return v_res_3662_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize(lean_object* v_limits_3663_, lean_object* v_a_3664_){
_start:
{
lean_object* v___x_3665_; 
v___x_3665_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(v_a_3664_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v_pos_3666_; lean_object* v_res_3667_; lean_object* v_maxChunkExtensions_3668_; lean_object* v___f_3669_; lean_object* v___x_3670_; 
v_pos_3666_ = lean_ctor_get(v___x_3665_, 0);
lean_inc(v_pos_3666_);
v_res_3667_ = lean_ctor_get(v___x_3665_, 1);
lean_inc(v_res_3667_);
lean_dec_ref(v___x_3665_);
v_maxChunkExtensions_3668_ = lean_ctor_get(v_limits_3663_, 10);
lean_inc(v_maxChunkExtensions_3668_);
v___f_3669_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3669_, 0, v_limits_3663_);
v___x_3670_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___f_3669_, v_maxChunkExtensions_3668_, v_pos_3666_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_pos_3671_; lean_object* v_res_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v_pos_3671_ = lean_ctor_get(v___x_3670_, 0);
lean_inc(v_pos_3671_);
v_res_3672_ = lean_ctor_get(v___x_3670_, 1);
lean_inc(v_res_3672_);
lean_dec_ref(v___x_3670_);
v___x_3673_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3674_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3673_, v_pos_3671_);
if (lean_obj_tag(v___x_3674_) == 0)
{
lean_object* v_pos_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3683_; 
v_pos_3675_ = lean_ctor_get(v___x_3674_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3674_);
if (v_isSharedCheck_3683_ == 0)
{
lean_object* v_unused_3684_; 
v_unused_3684_ = lean_ctor_get(v___x_3674_, 1);
lean_dec(v_unused_3684_);
v___x_3677_ = v___x_3674_;
v_isShared_3678_ = v_isSharedCheck_3683_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_pos_3675_);
lean_dec(v___x_3674_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3683_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3679_; lean_object* v___x_3681_; 
v___x_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3679_, 0, v_res_3667_);
lean_ctor_set(v___x_3679_, 1, v_res_3672_);
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 1, v___x_3679_);
v___x_3681_ = v___x_3677_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_pos_3675_);
lean_ctor_set(v_reuseFailAlloc_3682_, 1, v___x_3679_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
else
{
lean_object* v_pos_3685_; lean_object* v_err_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
lean_dec(v_res_3672_);
lean_dec(v_res_3667_);
v_pos_3685_ = lean_ctor_get(v___x_3674_, 0);
v_err_3686_ = lean_ctor_get(v___x_3674_, 1);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3674_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3674_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_err_3686_);
lean_inc(v_pos_3685_);
lean_dec(v___x_3674_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_pos_3685_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v_err_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
else
{
lean_object* v_pos_3694_; lean_object* v_err_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
lean_dec(v_res_3667_);
v_pos_3694_ = lean_ctor_get(v___x_3670_, 0);
v_err_3695_ = lean_ctor_get(v___x_3670_, 1);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3697_ = v___x_3670_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_err_3695_);
lean_inc(v_pos_3694_);
lean_dec(v___x_3670_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_pos_3694_);
lean_ctor_set(v_reuseFailAlloc_3701_, 1, v_err_3695_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
else
{
lean_object* v_pos_3703_; lean_object* v_err_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec_ref(v_limits_3663_);
v_pos_3703_ = lean_ctor_get(v___x_3665_, 0);
v_err_3704_ = lean_ctor_get(v___x_3665_, 1);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3665_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_err_3704_);
lean_inc(v_pos_3703_);
lean_dec(v___x_3665_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_pos_3703_);
lean_ctor_set(v_reuseFailAlloc_3710_, 1, v_err_3704_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx(lean_object* v_x_3712_){
_start:
{
if (lean_obj_tag(v_x_3712_) == 0)
{
lean_object* v___x_3713_; 
v___x_3713_ = lean_unsigned_to_nat(0u);
return v___x_3713_;
}
else
{
lean_object* v___x_3714_; 
v___x_3714_ = lean_unsigned_to_nat(1u);
return v___x_3714_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___boxed(lean_object* v_x_3715_){
_start:
{
lean_object* v_res_3716_; 
v_res_3716_ = l_Std_Http_Protocol_H1_TakeResult_ctorIdx(v_x_3715_);
lean_dec_ref(v_x_3715_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(lean_object* v_t_3717_, lean_object* v_k_3718_){
_start:
{
if (lean_obj_tag(v_t_3717_) == 0)
{
lean_object* v_data_3719_; lean_object* v___x_3720_; 
v_data_3719_ = lean_ctor_get(v_t_3717_, 0);
lean_inc_ref(v_data_3719_);
lean_dec_ref(v_t_3717_);
v___x_3720_ = lean_apply_1(v_k_3718_, v_data_3719_);
return v___x_3720_;
}
else
{
lean_object* v_data_3721_; lean_object* v_remaining_3722_; lean_object* v___x_3723_; 
v_data_3721_ = lean_ctor_get(v_t_3717_, 0);
lean_inc_ref(v_data_3721_);
v_remaining_3722_ = lean_ctor_get(v_t_3717_, 1);
lean_inc(v_remaining_3722_);
lean_dec_ref(v_t_3717_);
v___x_3723_ = lean_apply_2(v_k_3718_, v_data_3721_, v_remaining_3722_);
return v___x_3723_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim(lean_object* v_motive_3724_, lean_object* v_ctorIdx_3725_, lean_object* v_t_3726_, lean_object* v_h_3727_, lean_object* v_k_3728_){
_start:
{
lean_object* v___x_3729_; 
v___x_3729_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3726_, v_k_3728_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___boxed(lean_object* v_motive_3730_, lean_object* v_ctorIdx_3731_, lean_object* v_t_3732_, lean_object* v_h_3733_, lean_object* v_k_3734_){
_start:
{
lean_object* v_res_3735_; 
v_res_3735_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim(v_motive_3730_, v_ctorIdx_3731_, v_t_3732_, v_h_3733_, v_k_3734_);
lean_dec(v_ctorIdx_3731_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim___redArg(lean_object* v_t_3736_, lean_object* v_complete_3737_){
_start:
{
lean_object* v___x_3738_; 
v___x_3738_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3736_, v_complete_3737_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim(lean_object* v_motive_3739_, lean_object* v_t_3740_, lean_object* v_h_3741_, lean_object* v_complete_3742_){
_start:
{
lean_object* v___x_3743_; 
v___x_3743_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3740_, v_complete_3742_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim___redArg(lean_object* v_t_3744_, lean_object* v_incomplete_3745_){
_start:
{
lean_object* v___x_3746_; 
v___x_3746_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3744_, v_incomplete_3745_);
return v___x_3746_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim(lean_object* v_motive_3747_, lean_object* v_t_3748_, lean_object* v_h_3749_, lean_object* v_incomplete_3750_){
_start:
{
lean_object* v___x_3751_; 
v___x_3751_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3748_, v_incomplete_3750_);
return v___x_3751_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkPartial(lean_object* v_limits_3752_, lean_object* v_a_3753_){
_start:
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Std_Http_Protocol_H1_parseChunkSize(v_limits_3752_, v_a_3753_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_res_3755_; lean_object* v_pos_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3796_; 
v_res_3755_ = lean_ctor_get(v___x_3754_, 1);
v_pos_3756_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3758_ = v___x_3754_;
v_isShared_3759_ = v_isSharedCheck_3796_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_res_3755_);
lean_inc(v_pos_3756_);
lean_dec(v___x_3754_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3796_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v_fst_3760_; lean_object* v_snd_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3795_; 
v_fst_3760_ = lean_ctor_get(v_res_3755_, 0);
v_snd_3761_ = lean_ctor_get(v_res_3755_, 1);
v_isSharedCheck_3795_ = !lean_is_exclusive(v_res_3755_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3763_ = v_res_3755_;
v_isShared_3764_ = v_isSharedCheck_3795_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_snd_3761_);
lean_inc(v_fst_3760_);
lean_dec(v_res_3755_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3795_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3765_; uint8_t v___x_3766_; 
v___x_3765_ = lean_unsigned_to_nat(0u);
v___x_3766_ = lean_nat_dec_eq(v_fst_3760_, v___x_3765_);
if (v___x_3766_ == 0)
{
lean_object* v___x_3767_; 
lean_del_object(v___x_3758_);
v___x_3767_ = l_Std_Internal_Parsec_ByteArray_take(v_fst_3760_, v_pos_3756_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v_pos_3768_; lean_object* v_res_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3781_; 
v_pos_3768_ = lean_ctor_get(v___x_3767_, 0);
v_res_3769_ = lean_ctor_get(v___x_3767_, 1);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3771_ = v___x_3767_;
v_isShared_3772_ = v_isSharedCheck_3781_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_res_3769_);
lean_inc(v_pos_3768_);
lean_dec(v___x_3767_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3781_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3774_; 
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 1, v_res_3769_);
lean_ctor_set(v___x_3763_, 0, v_snd_3761_);
v___x_3774_ = v___x_3763_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_snd_3761_);
lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_res_3769_);
v___x_3774_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3778_; 
v___x_3775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3775_, 0, v_fst_3760_);
lean_ctor_set(v___x_3775_, 1, v___x_3774_);
v___x_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3775_);
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 1, v___x_3776_);
v___x_3778_ = v___x_3771_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_pos_3768_);
lean_ctor_set(v_reuseFailAlloc_3779_, 1, v___x_3776_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
}
else
{
lean_object* v_pos_3782_; lean_object* v_err_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
lean_del_object(v___x_3763_);
lean_dec(v_snd_3761_);
lean_dec(v_fst_3760_);
v_pos_3782_ = lean_ctor_get(v___x_3767_, 0);
v_err_3783_ = lean_ctor_get(v___x_3767_, 1);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3767_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_err_3783_);
lean_inc(v_pos_3782_);
lean_dec(v___x_3767_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_pos_3782_);
lean_ctor_set(v_reuseFailAlloc_3789_, 1, v_err_3783_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
else
{
lean_object* v___x_3791_; lean_object* v___x_3793_; 
lean_del_object(v___x_3763_);
lean_dec(v_snd_3761_);
lean_dec(v_fst_3760_);
v___x_3791_ = lean_box(0);
if (v_isShared_3759_ == 0)
{
lean_ctor_set(v___x_3758_, 1, v___x_3791_);
v___x_3793_ = v___x_3758_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_pos_3756_);
lean_ctor_set(v_reuseFailAlloc_3794_, 1, v___x_3791_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
}
else
{
lean_object* v_pos_3797_; lean_object* v_err_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
v_pos_3797_ = lean_ctor_get(v___x_3754_, 0);
v_err_3798_ = lean_ctor_get(v___x_3754_, 1);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v___x_3754_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_err_3798_);
lean_inc(v_pos_3797_);
lean_dec(v___x_3754_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3803_; 
if (v_isShared_3801_ == 0)
{
v___x_3803_ = v___x_3800_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_pos_3797_);
lean_ctor_set(v_reuseFailAlloc_3804_, 1, v_err_3798_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData(lean_object* v_size_3806_, lean_object* v_it_3807_){
_start:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; uint8_t v___x_3810_; 
v___x_3808_ = l_ByteArray_Iterator_remainingBytes(v_it_3807_);
v___x_3809_ = lean_unsigned_to_nat(0u);
v___x_3810_ = lean_nat_dec_eq(v___x_3808_, v___x_3809_);
if (v___x_3810_ == 0)
{
uint8_t v___x_3811_; 
v___x_3811_ = lean_nat_dec_lt(v___x_3808_, v_size_3806_);
if (v___x_3811_ == 0)
{
lean_object* v_array_3812_; lean_object* v_idx_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3832_; 
lean_dec(v___x_3808_);
v_array_3812_ = lean_ctor_get(v_it_3807_, 0);
v_idx_3813_ = lean_ctor_get(v_it_3807_, 1);
v_isSharedCheck_3832_ = !lean_is_exclusive(v_it_3807_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3815_ = v_it_3807_;
v_isShared_3816_ = v_isSharedCheck_3832_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_idx_3813_);
lean_inc(v_array_3812_);
lean_dec(v_it_3807_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3832_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3817_; lean_object* v___x_3819_; 
v___x_3817_ = lean_nat_add(v_idx_3813_, v_size_3806_);
lean_inc(v___x_3817_);
lean_inc_ref(v_array_3812_);
if (v_isShared_3816_ == 0)
{
lean_ctor_set(v___x_3815_, 1, v___x_3817_);
v___x_3819_ = v___x_3815_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_array_3812_);
lean_ctor_set(v_reuseFailAlloc_3831_, 1, v___x_3817_);
v___x_3819_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
lean_object* v_lower_3821_; lean_object* v_upper_3822_; lean_object* v___x_3826_; lean_object* v___y_3828_; uint8_t v___x_3830_; 
v___x_3826_ = lean_byte_array_size(v_array_3812_);
v___x_3830_ = lean_nat_dec_le(v_idx_3813_, v___x_3809_);
if (v___x_3830_ == 0)
{
v___y_3828_ = v_idx_3813_;
goto v___jp_3827_;
}
else
{
lean_dec(v_idx_3813_);
v___y_3828_ = v___x_3809_;
goto v___jp_3827_;
}
v___jp_3820_:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; 
v___x_3823_ = l_ByteArray_toByteSlice(v_array_3812_, v_lower_3821_, v_upper_3822_);
v___x_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3823_);
v___x_3825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3819_);
lean_ctor_set(v___x_3825_, 1, v___x_3824_);
return v___x_3825_;
}
v___jp_3827_:
{
uint8_t v___x_3829_; 
v___x_3829_ = lean_nat_dec_le(v___x_3817_, v___x_3826_);
if (v___x_3829_ == 0)
{
lean_dec(v___x_3817_);
v_lower_3821_ = v___y_3828_;
v_upper_3822_ = v___x_3826_;
goto v___jp_3820_;
}
else
{
v_lower_3821_ = v___y_3828_;
v_upper_3822_ = v___x_3817_;
goto v___jp_3820_;
}
}
}
}
}
else
{
lean_object* v_array_3833_; lean_object* v_idx_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3854_; 
v_array_3833_ = lean_ctor_get(v_it_3807_, 0);
v_idx_3834_ = lean_ctor_get(v_it_3807_, 1);
v_isSharedCheck_3854_ = !lean_is_exclusive(v_it_3807_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3836_ = v_it_3807_;
v_isShared_3837_ = v_isSharedCheck_3854_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_idx_3834_);
lean_inc(v_array_3833_);
lean_dec(v_it_3807_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3854_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3838_; lean_object* v___x_3840_; 
v___x_3838_ = lean_nat_add(v_idx_3834_, v___x_3808_);
lean_inc(v___x_3838_);
lean_inc_ref(v_array_3833_);
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 1, v___x_3838_);
v___x_3840_ = v___x_3836_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_array_3833_);
lean_ctor_set(v_reuseFailAlloc_3853_, 1, v___x_3838_);
v___x_3840_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
lean_object* v_lower_3842_; lean_object* v_upper_3843_; lean_object* v___x_3848_; lean_object* v___y_3850_; uint8_t v___x_3852_; 
v___x_3848_ = lean_byte_array_size(v_array_3833_);
v___x_3852_ = lean_nat_dec_le(v_idx_3834_, v___x_3809_);
if (v___x_3852_ == 0)
{
v___y_3850_ = v_idx_3834_;
goto v___jp_3849_;
}
else
{
lean_dec(v_idx_3834_);
v___y_3850_ = v___x_3809_;
goto v___jp_3849_;
}
v___jp_3841_:
{
lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___x_3844_ = l_ByteArray_toByteSlice(v_array_3833_, v_lower_3842_, v_upper_3843_);
v___x_3845_ = lean_nat_sub(v_size_3806_, v___x_3808_);
lean_dec(v___x_3808_);
v___x_3846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3844_);
lean_ctor_set(v___x_3846_, 1, v___x_3845_);
v___x_3847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3840_);
lean_ctor_set(v___x_3847_, 1, v___x_3846_);
return v___x_3847_;
}
v___jp_3849_:
{
uint8_t v___x_3851_; 
v___x_3851_ = lean_nat_dec_le(v___x_3838_, v___x_3848_);
if (v___x_3851_ == 0)
{
lean_dec(v___x_3838_);
v_lower_3842_ = v___y_3850_;
v_upper_3843_ = v___x_3848_;
goto v___jp_3841_;
}
else
{
v_lower_3842_ = v___y_3850_;
v_upper_3843_ = v___x_3838_;
goto v___jp_3841_;
}
}
}
}
}
}
else
{
lean_object* v___x_3855_; lean_object* v___x_3856_; 
lean_dec(v___x_3808_);
v___x_3855_ = lean_box(0);
v___x_3856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3856_, 0, v_it_3807_);
lean_ctor_set(v___x_3856_, 1, v___x_3855_);
return v___x_3856_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData___boxed(lean_object* v_size_3857_, lean_object* v_it_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_3857_, v_it_3858_);
lean_dec(v_size_3857_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData(lean_object* v_size_3860_, lean_object* v_a_3861_){
_start:
{
lean_object* v___x_3862_; 
v___x_3862_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_3860_, v_a_3861_);
if (lean_obj_tag(v___x_3862_) == 0)
{
lean_object* v_res_3863_; 
v_res_3863_ = lean_ctor_get(v___x_3862_, 1);
lean_inc(v_res_3863_);
if (lean_obj_tag(v_res_3863_) == 0)
{
lean_object* v_pos_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
v_pos_3864_ = lean_ctor_get(v___x_3862_, 0);
lean_inc(v_pos_3864_);
lean_dec_ref(v___x_3862_);
v___x_3865_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3866_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3865_, v_pos_3864_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_pos_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3874_; 
v_pos_3867_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3874_ == 0)
{
lean_object* v_unused_3875_; 
v_unused_3875_ = lean_ctor_get(v___x_3866_, 1);
lean_dec(v_unused_3875_);
v___x_3869_ = v___x_3866_;
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_pos_3867_);
lean_dec(v___x_3866_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3872_; 
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 1, v_res_3863_);
v___x_3872_ = v___x_3869_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_pos_3867_);
lean_ctor_set(v_reuseFailAlloc_3873_, 1, v_res_3863_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
else
{
lean_object* v_pos_3876_; lean_object* v_err_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
lean_dec_ref(v_res_3863_);
v_pos_3876_ = lean_ctor_get(v___x_3866_, 0);
v_err_3877_ = lean_ctor_get(v___x_3866_, 1);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3866_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_err_3877_);
lean_inc(v_pos_3876_);
lean_dec(v___x_3866_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_pos_3876_);
lean_ctor_set(v_reuseFailAlloc_3883_, 1, v_err_3877_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
else
{
lean_dec_ref(v_res_3863_);
return v___x_3862_;
}
}
else
{
return v___x_3862_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData___boxed(lean_object* v_size_3885_, lean_object* v_a_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l_Std_Http_Protocol_H1_parseChunkSizedData(v_size_3885_, v_a_3886_);
lean_dec(v_size_3885_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField_spec__0(lean_object* v_s_3888_, lean_object* v_p_3889_){
_start:
{
uint32_t v___y_3891_; lean_object* v___x_3896_; uint8_t v___x_3897_; 
v___x_3896_ = lean_string_utf8_byte_size(v_s_3888_);
v___x_3897_ = lean_nat_dec_eq(v_p_3889_, v___x_3896_);
if (v___x_3897_ == 0)
{
uint32_t v___x_3898_; uint32_t v___x_3899_; uint8_t v___x_3900_; 
v___x_3898_ = lean_string_utf8_get_fast(v_s_3888_, v_p_3889_);
v___x_3899_ = 65;
v___x_3900_ = lean_uint32_dec_le(v___x_3899_, v___x_3898_);
if (v___x_3900_ == 0)
{
v___y_3891_ = v___x_3898_;
goto v___jp_3890_;
}
else
{
uint32_t v___x_3901_; uint8_t v___x_3902_; 
v___x_3901_ = 90;
v___x_3902_ = lean_uint32_dec_le(v___x_3898_, v___x_3901_);
if (v___x_3902_ == 0)
{
v___y_3891_ = v___x_3898_;
goto v___jp_3890_;
}
else
{
uint32_t v___x_3903_; uint32_t v___x_3904_; 
v___x_3903_ = 32;
v___x_3904_ = lean_uint32_add(v___x_3898_, v___x_3903_);
v___y_3891_ = v___x_3904_;
goto v___jp_3890_;
}
}
}
else
{
lean_dec(v_p_3889_);
return v_s_3888_;
}
v___jp_3890_:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
lean_inc(v_p_3889_);
v___x_3892_ = lean_string_utf8_set(v_s_3888_, v_p_3889_, v___y_3891_);
v___x_3893_ = l_Char_utf8Size(v___y_3891_);
v___x_3894_ = lean_nat_add(v_p_3889_, v___x_3893_);
lean_dec(v___x_3893_);
lean_dec(v_p_3889_);
v_s_3888_ = v___x_3892_;
v_p_3889_ = v___x_3894_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(lean_object* v_name_3917_){
_start:
{
lean_object* v___x_3918_; lean_object* v_n_3919_; uint8_t v___y_3921_; lean_object* v___x_3942_; uint8_t v___x_3943_; 
v___x_3918_ = lean_unsigned_to_nat(0u);
v_n_3919_ = l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField_spec__0(v_name_3917_, v___x_3918_);
v___x_3942_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__10));
v___x_3943_ = lean_string_dec_eq(v_n_3919_, v___x_3942_);
if (v___x_3943_ == 0)
{
lean_object* v___x_3944_; uint8_t v___x_3945_; 
v___x_3944_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__11));
v___x_3945_ = lean_string_dec_eq(v_n_3919_, v___x_3944_);
v___y_3921_ = v___x_3945_;
goto v___jp_3920_;
}
else
{
v___y_3921_ = v___x_3943_;
goto v___jp_3920_;
}
v___jp_3920_:
{
if (v___y_3921_ == 0)
{
lean_object* v___x_3922_; uint8_t v___x_3923_; 
v___x_3922_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0));
v___x_3923_ = lean_string_dec_eq(v_n_3919_, v___x_3922_);
if (v___x_3923_ == 0)
{
lean_object* v___x_3924_; uint8_t v___x_3925_; 
v___x_3924_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1));
v___x_3925_ = lean_string_dec_eq(v_n_3919_, v___x_3924_);
if (v___x_3925_ == 0)
{
lean_object* v___x_3926_; uint8_t v___x_3927_; 
v___x_3926_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2));
v___x_3927_ = lean_string_dec_eq(v_n_3919_, v___x_3926_);
if (v___x_3927_ == 0)
{
lean_object* v___x_3928_; uint8_t v___x_3929_; 
v___x_3928_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3));
v___x_3929_ = lean_string_dec_eq(v_n_3919_, v___x_3928_);
if (v___x_3929_ == 0)
{
lean_object* v___x_3930_; uint8_t v___x_3931_; 
v___x_3930_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4));
v___x_3931_ = lean_string_dec_eq(v_n_3919_, v___x_3930_);
if (v___x_3931_ == 0)
{
lean_object* v___x_3932_; uint8_t v___x_3933_; 
v___x_3932_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__5));
v___x_3933_ = lean_string_dec_eq(v_n_3919_, v___x_3932_);
if (v___x_3933_ == 0)
{
lean_object* v___x_3934_; uint8_t v___x_3935_; 
v___x_3934_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__6));
v___x_3935_ = lean_string_dec_eq(v_n_3919_, v___x_3934_);
if (v___x_3935_ == 0)
{
lean_object* v___x_3936_; uint8_t v___x_3937_; 
v___x_3936_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__7));
v___x_3937_ = lean_string_dec_eq(v_n_3919_, v___x_3936_);
if (v___x_3937_ == 0)
{
lean_object* v___x_3938_; uint8_t v___x_3939_; 
v___x_3938_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__8));
v___x_3939_ = lean_string_dec_eq(v_n_3919_, v___x_3938_);
if (v___x_3939_ == 0)
{
lean_object* v___x_3940_; uint8_t v___x_3941_; 
v___x_3940_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__9));
v___x_3941_ = lean_string_dec_eq(v_n_3919_, v___x_3940_);
lean_dec_ref(v_n_3919_);
return v___x_3941_;
}
else
{
lean_dec_ref(v_n_3919_);
return v___x_3939_;
}
}
else
{
lean_dec_ref(v_n_3919_);
return v___x_3937_;
}
}
else
{
lean_dec_ref(v_n_3919_);
return v___x_3935_;
}
}
else
{
lean_dec_ref(v_n_3919_);
return v___x_3933_;
}
}
else
{
lean_dec_ref(v_n_3919_);
return v___x_3931_;
}
}
else
{
lean_dec_ref(v_n_3919_);
return v___x_3929_;
}
}
else
{
lean_dec_ref(v_n_3919_);
return v___x_3927_;
}
}
else
{
lean_dec_ref(v_n_3919_);
return v___x_3925_;
}
}
else
{
lean_dec_ref(v_n_3919_);
return v___x_3923_;
}
}
else
{
lean_dec_ref(v_n_3919_);
return v___y_3921_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___boxed(lean_object* v_name_3946_){
_start:
{
uint8_t v_res_3947_; lean_object* v_r_3948_; 
v_res_3947_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_name_3946_);
v_r_3948_ = lean_box(v_res_3947_);
return v_r_3948_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader(lean_object* v_limits_3950_, lean_object* v_a_3951_){
_start:
{
lean_object* v___x_3952_; 
v___x_3952_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_3950_, v_a_3951_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v_res_3953_; 
v_res_3953_ = lean_ctor_get(v___x_3952_, 1);
lean_inc(v_res_3953_);
if (lean_obj_tag(v_res_3953_) == 1)
{
lean_object* v_val_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3975_; 
v_val_3954_ = lean_ctor_get(v_res_3953_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v_res_3953_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3956_ = v_res_3953_;
v_isShared_3957_ = v_isSharedCheck_3975_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_val_3954_);
lean_dec(v_res_3953_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3975_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v_pos_3958_; lean_object* v_fst_3959_; uint8_t v___x_3960_; 
v_pos_3958_ = lean_ctor_get(v___x_3952_, 0);
lean_inc(v_pos_3958_);
v_fst_3959_ = lean_ctor_get(v_val_3954_, 0);
lean_inc_n(v_fst_3959_, 2);
lean_dec(v_val_3954_);
v___x_3960_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_fst_3959_);
if (v___x_3960_ == 0)
{
lean_dec(v_fst_3959_);
lean_dec(v_pos_3958_);
lean_del_object(v___x_3956_);
return v___x_3952_;
}
else
{
lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3972_; 
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3972_ == 0)
{
lean_object* v_unused_3973_; lean_object* v_unused_3974_; 
v_unused_3973_ = lean_ctor_get(v___x_3952_, 1);
lean_dec(v_unused_3973_);
v_unused_3974_ = lean_ctor_get(v___x_3952_, 0);
lean_dec(v_unused_3974_);
v___x_3962_ = v___x_3952_;
v_isShared_3963_ = v_isSharedCheck_3972_;
goto v_resetjp_3961_;
}
else
{
lean_dec(v___x_3952_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3972_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3967_; 
v___x_3964_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___closed__0));
v___x_3965_ = lean_string_append(v___x_3964_, v_fst_3959_);
lean_dec(v_fst_3959_);
if (v_isShared_3957_ == 0)
{
lean_ctor_set(v___x_3956_, 0, v___x_3965_);
v___x_3967_ = v___x_3956_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v___x_3965_);
v___x_3967_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
lean_object* v___x_3969_; 
if (v_isShared_3963_ == 0)
{
lean_ctor_set_tag(v___x_3962_, 1);
lean_ctor_set(v___x_3962_, 1, v___x_3967_);
v___x_3969_ = v___x_3962_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_pos_3958_);
lean_ctor_set(v_reuseFailAlloc_3970_, 1, v___x_3967_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
}
}
else
{
lean_dec(v_res_3953_);
return v___x_3952_;
}
}
else
{
return v___x_3952_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___boxed(lean_object* v_limits_3976_, lean_object* v_a_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader(v_limits_3976_, v_a_3977_);
lean_dec_ref(v_limits_3976_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailers(lean_object* v_limits_3979_, lean_object* v_a_3980_){
_start:
{
lean_object* v_maxTrailerHeaders_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v_maxTrailerHeaders_3981_ = lean_ctor_get(v_limits_3979_, 17);
lean_inc(v_maxTrailerHeaders_3981_);
v___x_3982_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___boxed), 2, 1);
lean_closure_set(v___x_3982_, 0, v_limits_3979_);
v___x_3983_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___x_3982_, v_maxTrailerHeaders_3981_, v_a_3980_);
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_object* v_pos_3984_; lean_object* v_res_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v_pos_3984_ = lean_ctor_get(v___x_3983_, 0);
lean_inc(v_pos_3984_);
v_res_3985_ = lean_ctor_get(v___x_3983_, 1);
lean_inc(v_res_3985_);
lean_dec_ref(v___x_3983_);
v___x_3986_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3987_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3986_, v_pos_3984_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v_pos_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3995_; 
v_pos_3988_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_3995_ == 0)
{
lean_object* v_unused_3996_; 
v_unused_3996_ = lean_ctor_get(v___x_3987_, 1);
lean_dec(v_unused_3996_);
v___x_3990_ = v___x_3987_;
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_pos_3988_);
lean_dec(v___x_3987_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
lean_ctor_set(v___x_3990_, 1, v_res_3985_);
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_pos_3988_);
lean_ctor_set(v_reuseFailAlloc_3994_, 1, v_res_3985_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
else
{
lean_object* v_pos_3997_; lean_object* v_err_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4005_; 
lean_dec(v_res_3985_);
v_pos_3997_ = lean_ctor_get(v___x_3987_, 0);
v_err_3998_ = lean_ctor_get(v___x_3987_, 1);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_4000_ = v___x_3987_;
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_err_3998_);
lean_inc(v_pos_3997_);
lean_dec(v___x_3987_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4003_; 
if (v_isShared_4001_ == 0)
{
v___x_4003_ = v___x_4000_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_pos_3997_);
lean_ctor_set(v_reuseFailAlloc_4004_, 1, v_err_3998_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
else
{
return v___x_3983_;
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(uint8_t v_c_4006_){
_start:
{
uint32_t v___x_4007_; uint32_t v___x_4013_; uint8_t v___x_4014_; 
v___x_4007_ = lean_uint8_to_uint32(v_c_4006_);
v___x_4013_ = 33;
v___x_4014_ = lean_uint32_dec_le(v___x_4013_, v___x_4007_);
if (v___x_4014_ == 0)
{
goto v___jp_4008_;
}
else
{
uint32_t v___x_4015_; uint8_t v___x_4016_; 
v___x_4015_ = 126;
v___x_4016_ = lean_uint32_dec_le(v___x_4007_, v___x_4015_);
if (v___x_4016_ == 0)
{
goto v___jp_4008_;
}
else
{
return v___x_4016_;
}
}
v___jp_4008_:
{
uint32_t v___x_4009_; uint8_t v___x_4010_; 
v___x_4009_ = 32;
v___x_4010_ = lean_uint32_dec_eq(v___x_4007_, v___x_4009_);
if (v___x_4010_ == 0)
{
uint32_t v___x_4011_; uint8_t v___x_4012_; 
v___x_4011_ = 9;
v___x_4012_ = lean_uint32_dec_eq(v___x_4007_, v___x_4011_);
return v___x_4012_;
}
else
{
return v___x_4010_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte___boxed(lean_object* v_c_4017_){
_start:
{
uint8_t v_c_boxed_4018_; uint8_t v_res_4019_; lean_object* v_r_4020_; 
v_c_boxed_4018_ = lean_unbox(v_c_4017_);
v_res_4019_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(v_c_boxed_4018_);
v_r_4020_ = lean_box(v_res_4019_);
return v_r_4020_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___lam__0(uint8_t v___y_4021_){
_start:
{
uint32_t v___x_4022_; uint32_t v___x_4028_; uint8_t v___x_4029_; 
v___x_4022_ = lean_uint8_to_uint32(v___y_4021_);
v___x_4028_ = 33;
v___x_4029_ = lean_uint32_dec_le(v___x_4028_, v___x_4022_);
if (v___x_4029_ == 0)
{
goto v___jp_4023_;
}
else
{
uint32_t v___x_4030_; uint8_t v___x_4031_; 
v___x_4030_ = 126;
v___x_4031_ = lean_uint32_dec_le(v___x_4022_, v___x_4030_);
if (v___x_4031_ == 0)
{
goto v___jp_4023_;
}
else
{
return v___x_4031_;
}
}
v___jp_4023_:
{
uint32_t v___x_4024_; uint8_t v___x_4025_; 
v___x_4024_ = 32;
v___x_4025_ = lean_uint32_dec_eq(v___x_4022_, v___x_4024_);
if (v___x_4025_ == 0)
{
uint32_t v___x_4026_; uint8_t v___x_4027_; 
v___x_4026_ = 9;
v___x_4027_ = lean_uint32_dec_eq(v___x_4022_, v___x_4026_);
return v___x_4027_;
}
else
{
return v___x_4025_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___lam__0___boxed(lean_object* v___y_4032_){
_start:
{
uint8_t v___y_225__boxed_4033_; uint8_t v_res_4034_; lean_object* v_r_4035_; 
v___y_225__boxed_4033_ = lean_unbox(v___y_4032_);
v_res_4034_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___lam__0(v___y_225__boxed_4033_);
v_r_4035_ = lean_box(v_res_4034_);
return v_r_4035_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(lean_object* v_limits_4037_, lean_object* v_a_4038_){
_start:
{
lean_object* v_maxReasonPhraseLength_4039_; lean_object* v___f_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v_snd_4043_; lean_object* v_snd_4044_; uint8_t v___x_4045_; 
v_maxReasonPhraseLength_4039_ = lean_ctor_get(v_limits_4037_, 16);
v___f_4040_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___closed__0));
v___x_4041_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_4038_);
v___x_4042_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_4040_, v_maxReasonPhraseLength_4039_, v___x_4041_, v_a_4038_);
v_snd_4043_ = lean_ctor_get(v___x_4042_, 1);
lean_inc(v_snd_4043_);
v_snd_4044_ = lean_ctor_get(v_snd_4043_, 1);
v___x_4045_ = lean_unbox(v_snd_4044_);
if (v___x_4045_ == 0)
{
lean_object* v_fst_4046_; lean_object* v_fst_4047_; lean_object* v_array_4048_; lean_object* v_idx_4049_; lean_object* v_lower_4051_; lean_object* v_upper_4052_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___y_4064_; uint8_t v___x_4066_; 
v_fst_4046_ = lean_ctor_get(v___x_4042_, 0);
lean_inc(v_fst_4046_);
lean_dec_ref(v___x_4042_);
v_fst_4047_ = lean_ctor_get(v_snd_4043_, 0);
lean_inc(v_fst_4047_);
lean_dec(v_snd_4043_);
v_array_4048_ = lean_ctor_get(v_a_4038_, 0);
lean_inc_ref(v_array_4048_);
v_idx_4049_ = lean_ctor_get(v_a_4038_, 1);
lean_inc(v_idx_4049_);
lean_dec_ref(v_a_4038_);
v___x_4061_ = lean_nat_add(v_idx_4049_, v_fst_4046_);
lean_dec(v_fst_4046_);
v___x_4062_ = lean_byte_array_size(v_array_4048_);
v___x_4066_ = lean_nat_dec_le(v_idx_4049_, v___x_4041_);
if (v___x_4066_ == 0)
{
v___y_4064_ = v_idx_4049_;
goto v___jp_4063_;
}
else
{
lean_dec(v_idx_4049_);
v___y_4064_ = v___x_4041_;
goto v___jp_4063_;
}
v___jp_4050_:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; uint8_t v___x_4055_; 
v___x_4053_ = l_ByteArray_toByteSlice(v_array_4048_, v_lower_4051_, v_upper_4052_);
v___x_4054_ = l_ByteSlice_toByteArray(v___x_4053_);
v___x_4055_ = lean_string_validate_utf8(v___x_4054_);
if (v___x_4055_ == 0)
{
lean_object* v___x_4056_; lean_object* v___x_4057_; 
lean_dec_ref(v___x_4054_);
v___x_4056_ = lean_box(0);
v___x_4057_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_4056_, v_fst_4047_);
return v___x_4057_;
}
else
{
lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4058_ = lean_string_from_utf8_unchecked(v___x_4054_);
v___x_4059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4058_);
v___x_4060_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_4059_, v_fst_4047_);
lean_dec_ref(v___x_4059_);
return v___x_4060_;
}
}
v___jp_4063_:
{
uint8_t v___x_4065_; 
v___x_4065_ = lean_nat_dec_le(v___x_4061_, v___x_4062_);
if (v___x_4065_ == 0)
{
lean_dec(v___x_4061_);
v_lower_4051_ = v___y_4064_;
v_upper_4052_ = v___x_4062_;
goto v___jp_4050_;
}
else
{
v_lower_4051_ = v___y_4064_;
v_upper_4052_ = v___x_4061_;
goto v___jp_4050_;
}
}
}
else
{
lean_object* v_fst_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4075_; 
lean_dec_ref(v___x_4042_);
lean_dec_ref(v_a_4038_);
v_fst_4067_ = lean_ctor_get(v_snd_4043_, 0);
v_isSharedCheck_4075_ = !lean_is_exclusive(v_snd_4043_);
if (v_isSharedCheck_4075_ == 0)
{
lean_object* v_unused_4076_; 
v_unused_4076_ = lean_ctor_get(v_snd_4043_, 1);
lean_dec(v_unused_4076_);
v___x_4069_ = v_snd_4043_;
v_isShared_4070_ = v_isSharedCheck_4075_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_fst_4067_);
lean_dec(v_snd_4043_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4075_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4071_; lean_object* v___x_4073_; 
v___x_4071_ = lean_box(0);
if (v_isShared_4070_ == 0)
{
lean_ctor_set_tag(v___x_4069_, 1);
lean_ctor_set(v___x_4069_, 1, v___x_4071_);
v___x_4073_ = v___x_4069_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_fst_4067_);
lean_ctor_set(v_reuseFailAlloc_4074_, 1, v___x_4071_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___boxed(lean_object* v_limits_4077_, lean_object* v_a_4078_){
_start:
{
lean_object* v_res_4079_; 
v_res_4079_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_4077_, v_a_4078_);
lean_dec_ref(v_limits_4077_);
return v_res_4079_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(lean_object* v___x_4080_, lean_object* v___x_4081_, lean_object* v_x_4082_){
_start:
{
if (lean_obj_tag(v_x_4082_) == 0)
{
uint8_t v___x_4083_; 
v___x_4083_ = 1;
return v___x_4083_;
}
else
{
lean_object* v_head_4084_; lean_object* v_tail_4085_; uint8_t v___x_4086_; uint32_t v___x_4089_; uint32_t v___x_4090_; uint8_t v___x_4091_; 
v_head_4084_ = lean_ctor_get(v_x_4082_, 0);
v_tail_4085_ = lean_ctor_get(v_x_4082_, 1);
v___x_4086_ = lean_nat_dec_lt(v___x_4080_, v___x_4081_);
v___x_4089_ = 9;
v___x_4090_ = lean_unbox_uint32(v_head_4084_);
v___x_4091_ = lean_uint32_dec_eq(v___x_4090_, v___x_4089_);
if (v___x_4091_ == 0)
{
uint32_t v___x_4092_; uint32_t v___x_4093_; uint8_t v___x_4094_; 
v___x_4092_ = 32;
v___x_4093_ = lean_unbox_uint32(v_head_4084_);
v___x_4094_ = lean_uint32_dec_eq(v___x_4093_, v___x_4092_);
if (v___x_4094_ == 0)
{
uint32_t v___x_4095_; uint32_t v___x_4096_; uint8_t v___x_4097_; 
v___x_4095_ = 33;
v___x_4096_ = lean_unbox_uint32(v_head_4084_);
v___x_4097_ = lean_uint32_dec_le(v___x_4095_, v___x_4096_);
if (v___x_4097_ == 0)
{
return v___x_4097_;
}
else
{
uint32_t v___x_4098_; uint32_t v___x_4099_; uint8_t v___x_4100_; 
v___x_4098_ = 126;
v___x_4099_ = lean_unbox_uint32(v_head_4084_);
v___x_4100_ = lean_uint32_dec_le(v___x_4099_, v___x_4098_);
if (v___x_4100_ == 0)
{
return v___x_4100_;
}
else
{
goto v___jp_4087_;
}
}
}
else
{
goto v___jp_4087_;
}
}
else
{
goto v___jp_4087_;
}
v___jp_4087_:
{
if (v___x_4086_ == 0)
{
return v___x_4086_;
}
else
{
v_x_4082_ = v_tail_4085_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0___boxed(lean_object* v___x_4101_, lean_object* v___x_4102_, lean_object* v_x_4103_){
_start:
{
uint8_t v_res_4104_; lean_object* v_r_4105_; 
v_res_4104_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v___x_4101_, v___x_4102_, v_x_4103_);
lean_dec(v_x_4103_);
lean_dec(v___x_4102_);
lean_dec(v___x_4101_);
v_r_4105_ = lean_box(v_res_4104_);
return v_r_4105_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(lean_object* v_limits_4109_, lean_object* v_a_4110_){
_start:
{
lean_object* v___y_4112_; lean_object* v_array_4118_; lean_object* v_idx_4119_; lean_object* v___x_4120_; uint8_t v___x_4121_; 
v_array_4118_ = lean_ctor_get(v_a_4110_, 0);
v_idx_4119_ = lean_ctor_get(v_a_4110_, 1);
v___x_4120_ = lean_byte_array_size(v_array_4118_);
v___x_4121_ = lean_nat_dec_lt(v_idx_4119_, v___x_4120_);
if (v___x_4121_ == 0)
{
lean_object* v___x_4122_; lean_object* v___x_4123_; 
v___x_4122_ = lean_box(0);
v___x_4123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4123_, 0, v_a_4110_);
lean_ctor_set(v___x_4123_, 1, v___x_4122_);
return v___x_4123_;
}
else
{
uint8_t v_c_4124_; uint8_t v___x_4125_; uint8_t v___x_4126_; 
v_c_4124_ = lean_byte_array_fget(v_array_4118_, v_idx_4119_);
v___x_4125_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__3);
v___x_4126_ = lean_uint8_dec_le(v___x_4125_, v_c_4124_);
if (v___x_4126_ == 0)
{
goto v___jp_4115_;
}
else
{
uint8_t v___x_4127_; uint8_t v___x_4128_; 
v___x_4127_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__4);
v___x_4128_ = lean_uint8_dec_le(v_c_4124_, v___x_4127_);
if (v___x_4128_ == 0)
{
goto v___jp_4115_;
}
else
{
lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4221_; 
lean_inc(v_idx_4119_);
lean_inc_ref(v_array_4118_);
v_isSharedCheck_4221_ = !lean_is_exclusive(v_a_4110_);
if (v_isSharedCheck_4221_ == 0)
{
lean_object* v_unused_4222_; lean_object* v_unused_4223_; 
v_unused_4222_ = lean_ctor_get(v_a_4110_, 1);
lean_dec(v_unused_4222_);
v_unused_4223_ = lean_ctor_get(v_a_4110_, 0);
lean_dec(v_unused_4223_);
v___x_4130_ = v_a_4110_;
v_isShared_4131_ = v_isSharedCheck_4221_;
goto v_resetjp_4129_;
}
else
{
lean_dec(v_a_4110_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4221_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v_it_x27_4135_; 
v___x_4132_ = lean_unsigned_to_nat(1u);
v___x_4133_ = lean_nat_add(v_idx_4119_, v___x_4132_);
lean_dec(v_idx_4119_);
lean_inc(v___x_4133_);
lean_inc_ref(v_array_4118_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set(v___x_4130_, 1, v___x_4133_);
v_it_x27_4135_ = v___x_4130_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_array_4118_);
lean_ctor_set(v_reuseFailAlloc_4220_, 1, v___x_4133_);
v_it_x27_4135_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
uint8_t v___x_4139_; 
v___x_4139_ = lean_nat_dec_lt(v___x_4133_, v___x_4120_);
if (v___x_4139_ == 0)
{
lean_object* v___x_4140_; lean_object* v___x_4141_; 
lean_dec(v___x_4133_);
lean_dec_ref(v_array_4118_);
v___x_4140_ = lean_box(0);
v___x_4141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4141_, 0, v_it_x27_4135_);
lean_ctor_set(v___x_4141_, 1, v___x_4140_);
return v___x_4141_;
}
else
{
uint8_t v_c_4142_; uint8_t v___x_4143_; 
v_c_4142_ = lean_byte_array_fget(v_array_4118_, v___x_4133_);
v___x_4143_ = lean_uint8_dec_le(v___x_4125_, v_c_4142_);
if (v___x_4143_ == 0)
{
lean_dec(v___x_4133_);
lean_dec_ref(v_array_4118_);
goto v___jp_4136_;
}
else
{
uint8_t v___x_4144_; 
v___x_4144_ = lean_uint8_dec_le(v_c_4142_, v___x_4127_);
if (v___x_4144_ == 0)
{
lean_dec(v___x_4133_);
lean_dec_ref(v_array_4118_);
goto v___jp_4136_;
}
else
{
lean_object* v___x_4145_; lean_object* v_it_x27_4146_; uint8_t v___x_4150_; 
lean_dec_ref(v_it_x27_4135_);
v___x_4145_ = lean_nat_add(v___x_4133_, v___x_4132_);
lean_dec(v___x_4133_);
lean_inc(v___x_4145_);
lean_inc_ref(v_array_4118_);
v_it_x27_4146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_4146_, 0, v_array_4118_);
lean_ctor_set(v_it_x27_4146_, 1, v___x_4145_);
v___x_4150_ = lean_nat_dec_lt(v___x_4145_, v___x_4120_);
if (v___x_4150_ == 0)
{
lean_object* v___x_4151_; lean_object* v___x_4152_; 
lean_dec(v___x_4145_);
lean_dec_ref(v_array_4118_);
v___x_4151_ = lean_box(0);
v___x_4152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4152_, 0, v_it_x27_4146_);
lean_ctor_set(v___x_4152_, 1, v___x_4151_);
return v___x_4152_;
}
else
{
uint8_t v_c_4153_; uint8_t v___x_4154_; 
v_c_4153_ = lean_byte_array_fget(v_array_4118_, v___x_4145_);
v___x_4154_ = lean_uint8_dec_le(v___x_4125_, v_c_4153_);
if (v___x_4154_ == 0)
{
lean_dec(v___x_4145_);
lean_dec_ref(v_array_4118_);
goto v___jp_4147_;
}
else
{
uint8_t v___x_4155_; 
v___x_4155_ = lean_uint8_dec_le(v_c_4153_, v___x_4127_);
if (v___x_4155_ == 0)
{
lean_dec(v___x_4145_);
lean_dec_ref(v_array_4118_);
goto v___jp_4147_;
}
else
{
lean_object* v___x_4156_; lean_object* v_it_x27_4157_; uint8_t v___x_4158_; 
lean_dec_ref(v_it_x27_4146_);
v___x_4156_ = lean_nat_add(v___x_4145_, v___x_4132_);
lean_dec(v___x_4145_);
lean_inc(v___x_4156_);
lean_inc_ref(v_array_4118_);
v_it_x27_4157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_4157_, 0, v_array_4118_);
lean_ctor_set(v_it_x27_4157_, 1, v___x_4156_);
v___x_4158_ = lean_nat_dec_lt(v___x_4156_, v___x_4120_);
if (v___x_4158_ == 0)
{
lean_object* v___x_4159_; lean_object* v___x_4160_; 
lean_dec(v___x_4156_);
lean_dec_ref(v_array_4118_);
v___x_4159_ = lean_box(0);
v___x_4160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4160_, 0, v_it_x27_4157_);
lean_ctor_set(v___x_4160_, 1, v___x_4159_);
return v___x_4160_;
}
else
{
uint8_t v___x_4161_; uint8_t v_got_4162_; uint8_t v___x_4163_; 
v___x_4161_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v_got_4162_ = lean_byte_array_fget(v_array_4118_, v___x_4156_);
v___x_4163_ = lean_uint8_dec_eq(v_got_4162_, v___x_4161_);
if (v___x_4163_ == 0)
{
lean_object* v___x_4164_; lean_object* v___x_4165_; 
lean_dec(v___x_4156_);
lean_dec_ref(v_array_4118_);
v___x_4164_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7);
v___x_4165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4165_, 0, v_it_x27_4157_);
lean_ctor_set(v___x_4165_, 1, v___x_4164_);
return v___x_4165_;
}
else
{
uint32_t v___x_4166_; uint32_t v___x_4167_; uint32_t v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v_pos_4183_; lean_object* v_res_4184_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
lean_dec_ref(v_it_x27_4157_);
v___x_4166_ = lean_uint8_to_uint32(v_c_4124_);
v___x_4167_ = lean_uint8_to_uint32(v_c_4142_);
v___x_4168_ = lean_uint8_to_uint32(v_c_4153_);
v___x_4169_ = lean_uint32_to_nat(v___x_4166_);
v___x_4170_ = lean_unsigned_to_nat(48u);
v___x_4171_ = lean_nat_sub(v___x_4169_, v___x_4170_);
lean_dec(v___x_4169_);
v___x_4172_ = lean_unsigned_to_nat(100u);
v___x_4173_ = lean_nat_mul(v___x_4171_, v___x_4172_);
lean_dec(v___x_4171_);
v___x_4174_ = lean_uint32_to_nat(v___x_4167_);
v___x_4175_ = lean_nat_sub(v___x_4174_, v___x_4170_);
lean_dec(v___x_4174_);
v___x_4176_ = lean_unsigned_to_nat(10u);
v___x_4177_ = lean_nat_mul(v___x_4175_, v___x_4176_);
lean_dec(v___x_4175_);
v___x_4178_ = lean_nat_add(v___x_4173_, v___x_4177_);
lean_dec(v___x_4177_);
lean_dec(v___x_4173_);
v___x_4179_ = lean_uint32_to_nat(v___x_4168_);
v___x_4180_ = lean_nat_sub(v___x_4179_, v___x_4170_);
lean_dec(v___x_4179_);
v___x_4181_ = lean_nat_add(v___x_4178_, v___x_4180_);
lean_dec(v___x_4180_);
lean_dec(v___x_4178_);
v___x_4192_ = lean_nat_add(v___x_4156_, v___x_4132_);
v___x_4193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4193_, 0, v_array_4118_);
lean_ctor_set(v___x_4193_, 1, v___x_4192_);
v___x_4194_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_4109_, v___x_4193_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v_pos_4195_; lean_object* v_res_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; 
v_pos_4195_ = lean_ctor_get(v___x_4194_, 0);
lean_inc(v_pos_4195_);
v_res_4196_ = lean_ctor_get(v___x_4194_, 1);
lean_inc(v_res_4196_);
lean_dec_ref(v___x_4194_);
v___x_4197_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_4198_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_4197_, v_pos_4195_);
if (lean_obj_tag(v___x_4198_) == 0)
{
lean_object* v_pos_4199_; 
v_pos_4199_ = lean_ctor_get(v___x_4198_, 0);
lean_inc(v_pos_4199_);
lean_dec_ref(v___x_4198_);
v_pos_4183_ = v_pos_4199_;
v_res_4184_ = v_res_4196_;
goto v___jp_4182_;
}
else
{
lean_object* v_pos_4200_; lean_object* v_err_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4208_; 
lean_dec(v_res_4196_);
lean_dec(v___x_4181_);
lean_dec(v___x_4156_);
v_pos_4200_ = lean_ctor_get(v___x_4198_, 0);
v_err_4201_ = lean_ctor_get(v___x_4198_, 1);
v_isSharedCheck_4208_ = !lean_is_exclusive(v___x_4198_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4203_ = v___x_4198_;
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_err_4201_);
lean_inc(v_pos_4200_);
lean_dec(v___x_4198_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4206_; 
if (v_isShared_4204_ == 0)
{
v___x_4206_ = v___x_4203_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v_pos_4200_);
lean_ctor_set(v_reuseFailAlloc_4207_, 1, v_err_4201_);
v___x_4206_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
return v___x_4206_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v_pos_4209_; lean_object* v_res_4210_; 
v_pos_4209_ = lean_ctor_get(v___x_4194_, 0);
lean_inc(v_pos_4209_);
v_res_4210_ = lean_ctor_get(v___x_4194_, 1);
lean_inc(v_res_4210_);
lean_dec_ref(v___x_4194_);
v_pos_4183_ = v_pos_4209_;
v_res_4184_ = v_res_4210_;
goto v___jp_4182_;
}
else
{
lean_object* v_pos_4211_; lean_object* v_err_4212_; lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4219_; 
lean_dec(v___x_4181_);
lean_dec(v___x_4156_);
v_pos_4211_ = lean_ctor_get(v___x_4194_, 0);
v_err_4212_ = lean_ctor_get(v___x_4194_, 1);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4214_ = v___x_4194_;
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
else
{
lean_inc(v_err_4212_);
lean_inc(v_pos_4211_);
lean_dec(v___x_4194_);
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
v___jp_4182_:
{
lean_object* v___x_4185_; uint8_t v___x_4186_; 
lean_inc_ref(v_res_4184_);
v___x_4185_ = lean_string_data(v_res_4184_);
v___x_4186_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v___x_4156_, v___x_4120_, v___x_4185_);
lean_dec(v___x_4185_);
lean_dec(v___x_4156_);
if (v___x_4186_ == 0)
{
lean_dec_ref(v_res_4184_);
lean_dec(v___x_4181_);
v___y_4112_ = v_pos_4183_;
goto v___jp_4111_;
}
else
{
lean_object* v___x_4187_; uint16_t v___x_4188_; lean_object* v___x_4189_; 
v___x_4187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4187_, 0, v_res_4184_);
v___x_4188_ = lean_uint16_of_nat(v___x_4181_);
lean_dec(v___x_4181_);
v___x_4189_ = l_Std_Http_Status_ofCode(v___x_4187_, v___x_4188_);
if (lean_obj_tag(v___x_4189_) == 1)
{
lean_object* v_val_4190_; lean_object* v___x_4191_; 
v_val_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_val_4190_);
lean_dec_ref(v___x_4189_);
v___x_4191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4191_, 0, v_pos_4183_);
lean_ctor_set(v___x_4191_, 1, v_val_4190_);
return v___x_4191_;
}
else
{
lean_dec(v___x_4189_);
v___y_4112_ = v_pos_4183_;
goto v___jp_4111_;
}
}
}
}
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
v___jp_4136_:
{
lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4137_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_4138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4138_, 0, v_it_x27_4135_);
lean_ctor_set(v___x_4138_, 1, v___x_4137_);
return v___x_4138_;
}
}
}
}
}
}
v___jp_4111_:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4113_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__1));
v___x_4114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4114_, 0, v___y_4112_);
lean_ctor_set(v___x_4114_, 1, v___x_4113_);
return v___x_4114_;
}
v___jp_4115_:
{
lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4116_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_4117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4117_, 0, v_a_4110_);
lean_ctor_set(v___x_4117_, 1, v___x_4116_);
return v___x_4117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___boxed(lean_object* v_limits_4224_, lean_object* v_a_4225_){
_start:
{
lean_object* v_res_4226_; 
v_res_4226_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_4224_, v_a_4225_);
lean_dec_ref(v_limits_4224_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine(lean_object* v_limits_4227_, lean_object* v_a_4228_){
_start:
{
lean_object* v___y_4230_; uint8_t v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v_pos_4245_; lean_object* v_res_4246_; lean_object* v___x_4274_; 
v___x_4274_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_4228_);
if (lean_obj_tag(v___x_4274_) == 0)
{
lean_object* v_pos_4275_; lean_object* v_res_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4306_; 
v_pos_4275_ = lean_ctor_get(v___x_4274_, 0);
v_res_4276_ = lean_ctor_get(v___x_4274_, 1);
v_isSharedCheck_4306_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4278_ = v___x_4274_;
v_isShared_4279_ = v_isSharedCheck_4306_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_res_4276_);
lean_inc(v_pos_4275_);
lean_dec(v___x_4274_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4306_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v_array_4280_; lean_object* v_idx_4281_; lean_object* v___x_4282_; uint8_t v___x_4283_; 
v_array_4280_ = lean_ctor_get(v_pos_4275_, 0);
v_idx_4281_ = lean_ctor_get(v_pos_4275_, 1);
v___x_4282_ = lean_byte_array_size(v_array_4280_);
v___x_4283_ = lean_nat_dec_lt(v_idx_4281_, v___x_4282_);
if (v___x_4283_ == 0)
{
lean_object* v___x_4284_; lean_object* v___x_4286_; 
lean_dec(v_res_4276_);
v___x_4284_ = lean_box(0);
if (v_isShared_4279_ == 0)
{
lean_ctor_set_tag(v___x_4278_, 1);
lean_ctor_set(v___x_4278_, 1, v___x_4284_);
v___x_4286_ = v___x_4278_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_pos_4275_);
lean_ctor_set(v_reuseFailAlloc_4287_, 1, v___x_4284_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
else
{
uint8_t v___x_4288_; uint8_t v_got_4289_; uint8_t v___x_4290_; 
v___x_4288_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v_got_4289_ = lean_byte_array_fget(v_array_4280_, v_idx_4281_);
v___x_4290_ = lean_uint8_dec_eq(v_got_4289_, v___x_4288_);
if (v___x_4290_ == 0)
{
lean_object* v___x_4291_; lean_object* v___x_4293_; 
lean_dec(v_res_4276_);
v___x_4291_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7);
if (v_isShared_4279_ == 0)
{
lean_ctor_set_tag(v___x_4278_, 1);
lean_ctor_set(v___x_4278_, 1, v___x_4291_);
v___x_4293_ = v___x_4278_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_pos_4275_);
lean_ctor_set(v_reuseFailAlloc_4294_, 1, v___x_4291_);
v___x_4293_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
return v___x_4293_;
}
}
else
{
lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4303_; 
lean_inc(v_idx_4281_);
lean_inc_ref(v_array_4280_);
lean_del_object(v___x_4278_);
v_isSharedCheck_4303_ = !lean_is_exclusive(v_pos_4275_);
if (v_isSharedCheck_4303_ == 0)
{
lean_object* v_unused_4304_; lean_object* v_unused_4305_; 
v_unused_4304_ = lean_ctor_get(v_pos_4275_, 1);
lean_dec(v_unused_4304_);
v_unused_4305_ = lean_ctor_get(v_pos_4275_, 0);
lean_dec(v_unused_4305_);
v___x_4296_ = v_pos_4275_;
v_isShared_4297_ = v_isSharedCheck_4303_;
goto v_resetjp_4295_;
}
else
{
lean_dec(v_pos_4275_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4303_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4301_; 
v___x_4298_ = lean_unsigned_to_nat(1u);
v___x_4299_ = lean_nat_add(v_idx_4281_, v___x_4298_);
lean_dec(v_idx_4281_);
if (v_isShared_4297_ == 0)
{
lean_ctor_set(v___x_4296_, 1, v___x_4299_);
v___x_4301_ = v___x_4296_;
goto v_reusejp_4300_;
}
else
{
lean_object* v_reuseFailAlloc_4302_; 
v_reuseFailAlloc_4302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4302_, 0, v_array_4280_);
lean_ctor_set(v_reuseFailAlloc_4302_, 1, v___x_4299_);
v___x_4301_ = v_reuseFailAlloc_4302_;
goto v_reusejp_4300_;
}
v_reusejp_4300_:
{
v_pos_4245_ = v___x_4301_;
v_res_4246_ = v_res_4276_;
goto v___jp_4244_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_4274_) == 0)
{
lean_object* v_pos_4307_; lean_object* v_res_4308_; 
v_pos_4307_ = lean_ctor_get(v___x_4274_, 0);
lean_inc(v_pos_4307_);
v_res_4308_ = lean_ctor_get(v___x_4274_, 1);
lean_inc(v_res_4308_);
lean_dec_ref(v___x_4274_);
v_pos_4245_ = v_pos_4307_;
v_res_4246_ = v_res_4308_;
goto v___jp_4244_;
}
else
{
lean_object* v_pos_4309_; lean_object* v_err_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4317_; 
v_pos_4309_ = lean_ctor_get(v___x_4274_, 0);
v_err_4310_ = lean_ctor_get(v___x_4274_, 1);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4312_ = v___x_4274_;
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_err_4310_);
lean_inc(v_pos_4309_);
lean_dec(v___x_4274_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4315_; 
if (v_isShared_4313_ == 0)
{
v___x_4315_ = v___x_4312_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_pos_4309_);
lean_ctor_set(v_reuseFailAlloc_4316_, 1, v_err_4310_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
}
}
}
}
v___jp_4229_:
{
lean_object* v___x_4231_; lean_object* v___x_4232_; 
v___x_4231_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
v___x_4232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4232_, 0, v___y_4230_);
lean_ctor_set(v___x_4232_, 1, v___x_4231_);
return v___x_4232_;
}
v___jp_4233_:
{
if (v___y_4234_ == 0)
{
lean_dec(v___y_4237_);
lean_dec(v___y_4235_);
v___y_4230_ = v___y_4236_;
goto v___jp_4229_;
}
else
{
lean_object* v___x_4238_; uint8_t v___x_4239_; 
v___x_4238_ = lean_unsigned_to_nat(0u);
v___x_4239_ = lean_nat_dec_eq(v___y_4237_, v___x_4238_);
lean_dec(v___y_4237_);
if (v___x_4239_ == 0)
{
lean_dec(v___y_4235_);
v___y_4230_ = v___y_4236_;
goto v___jp_4229_;
}
else
{
uint8_t v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; 
v___x_4240_ = 0;
v___x_4241_ = l_Std_Http_Headers_empty;
v___x_4242_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4242_, 0, v___y_4235_);
lean_ctor_set(v___x_4242_, 1, v___x_4241_);
lean_ctor_set_uint8(v___x_4242_, sizeof(void*)*2, v___x_4240_);
v___x_4243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4243_, 0, v___y_4236_);
lean_ctor_set(v___x_4243_, 1, v___x_4242_);
return v___x_4243_;
}
}
}
v___jp_4244_:
{
lean_object* v_fst_4247_; lean_object* v_snd_4248_; lean_object* v___x_4249_; 
v_fst_4247_ = lean_ctor_get(v_res_4246_, 0);
lean_inc(v_fst_4247_);
v_snd_4248_ = lean_ctor_get(v_res_4246_, 1);
lean_inc(v_snd_4248_);
lean_dec_ref(v_res_4246_);
v___x_4249_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_4227_, v_pos_4245_);
if (lean_obj_tag(v___x_4249_) == 0)
{
lean_object* v_pos_4250_; lean_object* v_res_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4264_; 
v_pos_4250_ = lean_ctor_get(v___x_4249_, 0);
v_res_4251_ = lean_ctor_get(v___x_4249_, 1);
v_isSharedCheck_4264_ = !lean_is_exclusive(v___x_4249_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4253_ = v___x_4249_;
v_isShared_4254_ = v_isSharedCheck_4264_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_res_4251_);
lean_inc(v_pos_4250_);
lean_dec(v___x_4249_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4264_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4255_; uint8_t v___x_4256_; 
v___x_4255_ = lean_unsigned_to_nat(1u);
v___x_4256_ = lean_nat_dec_eq(v_fst_4247_, v___x_4255_);
lean_dec(v_fst_4247_);
if (v___x_4256_ == 0)
{
lean_del_object(v___x_4253_);
v___y_4234_ = v___x_4256_;
v___y_4235_ = v_res_4251_;
v___y_4236_ = v_pos_4250_;
v___y_4237_ = v_snd_4248_;
goto v___jp_4233_;
}
else
{
uint8_t v___x_4257_; 
v___x_4257_ = lean_nat_dec_eq(v_snd_4248_, v___x_4255_);
if (v___x_4257_ == 0)
{
lean_del_object(v___x_4253_);
v___y_4234_ = v___x_4256_;
v___y_4235_ = v_res_4251_;
v___y_4236_ = v_pos_4250_;
v___y_4237_ = v_snd_4248_;
goto v___jp_4233_;
}
else
{
uint8_t v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4262_; 
lean_dec(v_snd_4248_);
v___x_4258_ = 1;
v___x_4259_ = l_Std_Http_Headers_empty;
v___x_4260_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4260_, 0, v_res_4251_);
lean_ctor_set(v___x_4260_, 1, v___x_4259_);
lean_ctor_set_uint8(v___x_4260_, sizeof(void*)*2, v___x_4258_);
if (v_isShared_4254_ == 0)
{
lean_ctor_set(v___x_4253_, 1, v___x_4260_);
v___x_4262_ = v___x_4253_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v_pos_4250_);
lean_ctor_set(v_reuseFailAlloc_4263_, 1, v___x_4260_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
}
}
}
else
{
lean_object* v_pos_4265_; lean_object* v_err_4266_; lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4273_; 
lean_dec(v_snd_4248_);
lean_dec(v_fst_4247_);
v_pos_4265_ = lean_ctor_get(v___x_4249_, 0);
v_err_4266_ = lean_ctor_get(v___x_4249_, 1);
v_isSharedCheck_4273_ = !lean_is_exclusive(v___x_4249_);
if (v_isSharedCheck_4273_ == 0)
{
v___x_4268_ = v___x_4249_;
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
else
{
lean_inc(v_err_4266_);
lean_inc(v_pos_4265_);
lean_dec(v___x_4249_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v___x_4271_; 
if (v_isShared_4269_ == 0)
{
v___x_4271_ = v___x_4268_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v_pos_4265_);
lean_ctor_set(v_reuseFailAlloc_4272_, 1, v_err_4266_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
return v___x_4271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine___boxed(lean_object* v_limits_4318_, lean_object* v_a_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l_Std_Http_Protocol_H1_parseStatusLine(v_limits_4318_, v_a_4319_);
lean_dec_ref(v_limits_4318_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion(lean_object* v_limits_4321_, lean_object* v_a_4322_){
_start:
{
lean_object* v_pos_4324_; lean_object* v_res_4325_; lean_object* v___x_4355_; 
v___x_4355_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_4322_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_pos_4356_; lean_object* v_res_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4387_; 
v_pos_4356_ = lean_ctor_get(v___x_4355_, 0);
v_res_4357_ = lean_ctor_get(v___x_4355_, 1);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4359_ = v___x_4355_;
v_isShared_4360_ = v_isSharedCheck_4387_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_res_4357_);
lean_inc(v_pos_4356_);
lean_dec(v___x_4355_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4387_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v_array_4361_; lean_object* v_idx_4362_; lean_object* v___x_4363_; uint8_t v___x_4364_; 
v_array_4361_ = lean_ctor_get(v_pos_4356_, 0);
v_idx_4362_ = lean_ctor_get(v_pos_4356_, 1);
v___x_4363_ = lean_byte_array_size(v_array_4361_);
v___x_4364_ = lean_nat_dec_lt(v_idx_4362_, v___x_4363_);
if (v___x_4364_ == 0)
{
lean_object* v___x_4365_; lean_object* v___x_4367_; 
lean_dec(v_res_4357_);
v___x_4365_ = lean_box(0);
if (v_isShared_4360_ == 0)
{
lean_ctor_set_tag(v___x_4359_, 1);
lean_ctor_set(v___x_4359_, 1, v___x_4365_);
v___x_4367_ = v___x_4359_;
goto v_reusejp_4366_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_pos_4356_);
lean_ctor_set(v_reuseFailAlloc_4368_, 1, v___x_4365_);
v___x_4367_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4366_;
}
v_reusejp_4366_:
{
return v___x_4367_;
}
}
else
{
uint8_t v___x_4369_; uint8_t v_got_4370_; uint8_t v___x_4371_; 
v___x_4369_ = lean_uint8_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0);
v_got_4370_ = lean_byte_array_fget(v_array_4361_, v_idx_4362_);
v___x_4371_ = lean_uint8_dec_eq(v_got_4370_, v___x_4369_);
if (v___x_4371_ == 0)
{
lean_object* v___x_4372_; lean_object* v___x_4374_; 
lean_dec(v_res_4357_);
v___x_4372_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__7);
if (v_isShared_4360_ == 0)
{
lean_ctor_set_tag(v___x_4359_, 1);
lean_ctor_set(v___x_4359_, 1, v___x_4372_);
v___x_4374_ = v___x_4359_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4375_; 
v_reuseFailAlloc_4375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4375_, 0, v_pos_4356_);
lean_ctor_set(v_reuseFailAlloc_4375_, 1, v___x_4372_);
v___x_4374_ = v_reuseFailAlloc_4375_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
return v___x_4374_;
}
}
else
{
lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4384_; 
lean_inc(v_idx_4362_);
lean_inc_ref(v_array_4361_);
lean_del_object(v___x_4359_);
v_isSharedCheck_4384_ = !lean_is_exclusive(v_pos_4356_);
if (v_isSharedCheck_4384_ == 0)
{
lean_object* v_unused_4385_; lean_object* v_unused_4386_; 
v_unused_4385_ = lean_ctor_get(v_pos_4356_, 1);
lean_dec(v_unused_4385_);
v_unused_4386_ = lean_ctor_get(v_pos_4356_, 0);
lean_dec(v_unused_4386_);
v___x_4377_ = v_pos_4356_;
v_isShared_4378_ = v_isSharedCheck_4384_;
goto v_resetjp_4376_;
}
else
{
lean_dec(v_pos_4356_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4384_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4382_; 
v___x_4379_ = lean_unsigned_to_nat(1u);
v___x_4380_ = lean_nat_add(v_idx_4362_, v___x_4379_);
lean_dec(v_idx_4362_);
if (v_isShared_4378_ == 0)
{
lean_ctor_set(v___x_4377_, 1, v___x_4380_);
v___x_4382_ = v___x_4377_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_array_4361_);
lean_ctor_set(v_reuseFailAlloc_4383_, 1, v___x_4380_);
v___x_4382_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
v_pos_4324_ = v___x_4382_;
v_res_4325_ = v_res_4357_;
goto v___jp_4323_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_pos_4388_; lean_object* v_res_4389_; 
v_pos_4388_ = lean_ctor_get(v___x_4355_, 0);
lean_inc(v_pos_4388_);
v_res_4389_ = lean_ctor_get(v___x_4355_, 1);
lean_inc(v_res_4389_);
lean_dec_ref(v___x_4355_);
v_pos_4324_ = v_pos_4388_;
v_res_4325_ = v_res_4389_;
goto v___jp_4323_;
}
else
{
lean_object* v_pos_4390_; lean_object* v_err_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4398_; 
v_pos_4390_ = lean_ctor_get(v___x_4355_, 0);
v_err_4391_ = lean_ctor_get(v___x_4355_, 1);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4393_ = v___x_4355_;
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_err_4391_);
lean_inc(v_pos_4390_);
lean_dec(v___x_4355_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4396_; 
if (v_isShared_4394_ == 0)
{
v___x_4396_ = v___x_4393_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_pos_4390_);
lean_ctor_set(v_reuseFailAlloc_4397_, 1, v_err_4391_);
v___x_4396_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
return v___x_4396_;
}
}
}
}
v___jp_4323_:
{
lean_object* v_fst_4326_; lean_object* v_snd_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4354_; 
v_fst_4326_ = lean_ctor_get(v_res_4325_, 0);
v_snd_4327_ = lean_ctor_get(v_res_4325_, 1);
v_isSharedCheck_4354_ = !lean_is_exclusive(v_res_4325_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4329_ = v_res_4325_;
v_isShared_4330_ = v_isSharedCheck_4354_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_snd_4327_);
lean_inc(v_fst_4326_);
lean_dec(v_res_4325_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4354_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
lean_object* v___x_4331_; 
v___x_4331_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_4321_, v_pos_4324_);
if (lean_obj_tag(v___x_4331_) == 0)
{
lean_object* v_pos_4332_; lean_object* v_res_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4344_; 
v_pos_4332_ = lean_ctor_get(v___x_4331_, 0);
v_res_4333_ = lean_ctor_get(v___x_4331_, 1);
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_4331_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4335_ = v___x_4331_;
v_isShared_4336_ = v_isSharedCheck_4344_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_res_4333_);
lean_inc(v_pos_4332_);
lean_dec(v___x_4331_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4344_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v___x_4337_; lean_object* v___x_4339_; 
v___x_4337_ = l_Std_Http_Version_ofNumber_x3f(v_fst_4326_, v_snd_4327_);
lean_dec(v_snd_4327_);
lean_dec(v_fst_4326_);
if (v_isShared_4330_ == 0)
{
lean_ctor_set(v___x_4329_, 1, v___x_4337_);
lean_ctor_set(v___x_4329_, 0, v_res_4333_);
v___x_4339_ = v___x_4329_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_res_4333_);
lean_ctor_set(v_reuseFailAlloc_4343_, 1, v___x_4337_);
v___x_4339_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
lean_object* v___x_4341_; 
if (v_isShared_4336_ == 0)
{
lean_ctor_set(v___x_4335_, 1, v___x_4339_);
v___x_4341_ = v___x_4335_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_pos_4332_);
lean_ctor_set(v_reuseFailAlloc_4342_, 1, v___x_4339_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
return v___x_4341_;
}
}
}
}
else
{
lean_object* v_pos_4345_; lean_object* v_err_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4353_; 
lean_del_object(v___x_4329_);
lean_dec(v_snd_4327_);
lean_dec(v_fst_4326_);
v_pos_4345_ = lean_ctor_get(v___x_4331_, 0);
v_err_4346_ = lean_ctor_get(v___x_4331_, 1);
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_4331_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4348_ = v___x_4331_;
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_err_4346_);
lean_inc(v_pos_4345_);
lean_dec(v___x_4331_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___x_4351_; 
if (v_isShared_4349_ == 0)
{
v___x_4351_ = v___x_4348_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_pos_4345_);
lean_ctor_set(v_reuseFailAlloc_4352_, 1, v_err_4346_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
return v___x_4351_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion___boxed(lean_object* v_limits_4399_, lean_object* v_a_4400_){
_start:
{
lean_object* v_res_4401_; 
v_res_4401_ = l_Std_Http_Protocol_H1_parseStatusLineRawVersion(v_limits_4399_, v_a_4400_);
lean_dec_ref(v_limits_4399_);
return v_res_4401_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseLastChunkBody(lean_object* v_limits_4402_, lean_object* v_a_4403_){
_start:
{
lean_object* v_maxTrailerHeaders_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v_maxTrailerHeaders_4404_ = lean_ctor_get(v_limits_4402_, 17);
lean_inc(v_maxTrailerHeaders_4404_);
v___x_4405_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___boxed), 2, 1);
lean_closure_set(v___x_4405_, 0, v_limits_4402_);
v___x_4406_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___x_4405_, v_maxTrailerHeaders_4404_, v_a_4403_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v_pos_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v_pos_4407_ = lean_ctor_get(v___x_4406_, 0);
lean_inc(v_pos_4407_);
lean_dec_ref(v___x_4406_);
v___x_4408_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_4409_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_4408_, v_pos_4407_);
return v___x_4409_;
}
else
{
lean_object* v_pos_4410_; lean_object* v_err_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
v_pos_4410_ = lean_ctor_get(v___x_4406_, 0);
v_err_4411_ = lean_ctor_get(v___x_4406_, 1);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4406_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_err_4411_);
lean_inc(v_pos_4410_);
lean_dec(v___x_4406_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_pos_4410_);
lean_ctor_set(v_reuseFailAlloc_4417_, 1, v_err_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
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
