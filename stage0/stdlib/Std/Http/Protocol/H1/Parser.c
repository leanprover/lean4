// Lean compiler output
// Module: Std.Http.Protocol.H1.Parser
// Imports: public import Std.Internal.Parsec public import Std.Http.Data public import Std.Internal.Parsec.ByteArray public import Std.Http.Protocol.H1.Config import Init.Data.String.Lossy
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
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_ByteSlice_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint32_t lean_uint8_to_uint32(uint8_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_to_utf8(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_toListImpl(lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
lean_object* l_Std_Http_Status_ofCode(lean_object*, uint16_t);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_toByteSlice(lean_object*, lean_object*, lean_object*);
lean_object* l_ByteSlice_toByteArray(lean_object*);
lean_object* l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Http_Headers_empty;
uint8_t lean_uint8_sub(uint8_t, uint8_t);
uint8_t lean_uint8_add(uint8_t, uint8_t);
lean_object* l_Char_quote(uint32_t);
extern lean_object* l_Std_Http_Method_all;
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_byteslice_beq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
extern lean_object* l_ByteArray_empty;
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_ByteArray_Iterator_remainingBytes(lean_object*);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Chunk_ExtensionValue_ofString_x3f(lean_object*);
lean_object* l_Std_Http_Chunk_ExtensionName_ofString_x3f(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_take(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_Std_Http_Version_ofNumber_x3f(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_optionalUnlessEof___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_optionalUnlessEof(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "too many items: "};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__0_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " > "};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "too many leading empty lines"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0_value)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '32'"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp(lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid space sequence"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "invalid hex digit "};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit(lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "chunk size too large"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "expected hex digit"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__2_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__2_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "HTTP/"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__0_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "digit expected"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__2_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__2_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '46'"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersion(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ACL"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "BASELINE-CONTROL"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "BIND"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CHECKIN"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CHECKOUT"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CONNECT"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COPY"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "DELETE"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GET"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "LABEL"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LINK"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LOCK"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MERGE"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__13_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKACTIVITY"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__14_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKCALENDAR"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__15_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MKCOL"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__16_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "MKREDIRECTREF"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__17_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MKWORKSPACE"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__18_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "MOVE"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__19_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OPTIONS"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__20_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ORDERPATCH"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__21_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PATCH"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__22_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "POST"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__23 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__23_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PRI"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__24_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "PROPFIND"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__25 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__25_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PROPPATCH"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__26 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__26_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PUT"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__27 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__27_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "QUERY"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__28 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__28_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REBIND"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__29 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__29_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REPORT"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__30 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__30_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "SEARCH"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__31 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__31_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "TRACE"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__32 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__32_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNBIND"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__33 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__33_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "UNCHECKOUT"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__34 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__34_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLINK"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__35 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__35_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLOCK"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__36 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__36_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UPDATE"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__37 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__37_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "UPDATEREDIRECTREF"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__38 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__38_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "VERSION-CONTROL"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__39 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__39_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods___closed__0;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "invalid method"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "unrecognized method"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0___boxed(lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "uri too long"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__1_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_requestTargetConfig(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_requestTargetConfig___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_exceedsElementLimits(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_exceedsElementLimits___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "expected end of input"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineParts(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineParts___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_parseRequestLine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "unsupported HTTP version"};
static const lean_object* l_Std_Http_Protocol_H1_parseRequestLine___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_parseRequestLine___closed__0_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_parseRequestLine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_parseRequestLine___closed__0_value)}};
static const lean_object* l_Std_Http_Protocol_H1_parseRequestLine___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_parseRequestLine___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_checkFieldValueLength___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "header value too long"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_checkFieldValueLength___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_checkFieldValueLength___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_checkFieldValueLength___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_checkFieldValueLength___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_checkFieldValueLength___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_checkFieldValueLength___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_checkFieldValueLength(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_checkFieldValueLength___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "header name too long"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '58'"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__5 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__5_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__5_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__6 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__6_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Protocol_H1_parseSingleHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_parseSingleHeader___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_parseSingleHeader___closed__0_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_parseSingleHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(10) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_parseSingleHeader___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_parseSingleHeader___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseObsFoldContinuation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseObsFoldContinuation___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '92'"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "invalid quoted-pair byte: "};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair(lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "quoted-string too long"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid qdtext byte: "};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '34'"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "invalid extension value"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid extension name"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '59'"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "content-length"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__0_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "transfer-encoding"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "host"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__2_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "connection"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__3_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "te"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__4 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__4_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "upgrade"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__5 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__5_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trailer"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__6 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__6_value;
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___boxed(lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "expect"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "authorization"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "max-forwards"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "cache-control"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "content-encoding"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4_value;
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___boxed(lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_parseTrailerHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "forbidden trailer field: "};
static const lean_object* l_Std_Http_Protocol_H1_parseTrailerHeader___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_parseTrailerHeader___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailerHeader(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailerHeader___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar(uint8_t v_c_1_){
_start:
{
uint32_t v___x_2_; uint32_t v___x_10_; uint8_t v___x_11_; 
v___x_2_ = lean_uint8_to_uint32(v_c_1_);
v___x_10_ = 33;
v___x_11_ = lean_uint32_dec_le(v___x_10_, v___x_2_);
if (v___x_11_ == 0)
{
goto v___jp_3_;
}
else
{
uint32_t v___x_12_; uint8_t v___x_13_; 
v___x_12_ = 126;
v___x_13_ = lean_uint32_dec_le(v___x_2_, v___x_12_);
if (v___x_13_ == 0)
{
goto v___jp_3_;
}
else
{
return v___x_13_;
}
}
v___jp_3_:
{
uint32_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = 128;
v___x_5_ = lean_uint32_dec_le(v___x_4_, v___x_2_);
if (v___x_5_ == 0)
{
uint32_t v___x_6_; uint8_t v___x_7_; 
v___x_6_ = 32;
v___x_7_ = lean_uint32_dec_eq(v___x_2_, v___x_6_);
if (v___x_7_ == 0)
{
uint32_t v___x_8_; uint8_t v___x_9_; 
v___x_8_ = 9;
v___x_9_ = lean_uint32_dec_eq(v___x_2_, v___x_8_);
return v___x_9_;
}
else
{
return v___x_7_;
}
}
else
{
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar___boxed(lean_object* v_c_14_){
_start:
{
uint8_t v_c_boxed_15_; uint8_t v_res_16_; lean_object* v_r_17_; 
v_c_boxed_15_ = lean_unbox(v_c_14_);
v_res_16_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar(v_c_boxed_15_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText(uint8_t v_c_18_){
_start:
{
uint32_t v___x_19_; uint32_t v___x_25_; uint8_t v___x_26_; 
v___x_19_ = lean_uint8_to_uint32(v_c_18_);
v___x_25_ = 9;
v___x_26_ = lean_uint32_dec_eq(v___x_19_, v___x_25_);
if (v___x_26_ == 0)
{
uint32_t v___x_27_; uint8_t v___x_28_; 
v___x_27_ = 32;
v___x_28_ = lean_uint32_dec_eq(v___x_19_, v___x_27_);
if (v___x_28_ == 0)
{
uint32_t v___x_29_; uint8_t v___x_30_; 
v___x_29_ = 33;
v___x_30_ = lean_uint32_dec_eq(v___x_19_, v___x_29_);
if (v___x_30_ == 0)
{
uint32_t v___x_31_; uint8_t v___x_32_; 
v___x_31_ = 35;
v___x_32_ = lean_uint32_dec_le(v___x_31_, v___x_19_);
if (v___x_32_ == 0)
{
goto v___jp_20_;
}
else
{
uint32_t v___x_33_; uint8_t v___x_34_; 
v___x_33_ = 91;
v___x_34_ = lean_uint32_dec_le(v___x_19_, v___x_33_);
if (v___x_34_ == 0)
{
goto v___jp_20_;
}
else
{
return v___x_34_;
}
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
v___jp_20_:
{
uint32_t v___x_21_; uint8_t v___x_22_; 
v___x_21_ = 93;
v___x_22_ = lean_uint32_dec_le(v___x_21_, v___x_19_);
if (v___x_22_ == 0)
{
return v___x_22_;
}
else
{
uint32_t v___x_23_; uint8_t v___x_24_; 
v___x_23_ = 126;
v___x_24_ = lean_uint32_dec_le(v___x_19_, v___x_23_);
return v___x_24_;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_optionalUnlessEof___redArg(lean_object* v_p_49_, lean_object* v_it_50_){
_start:
{
lean_object* v___x_51_; 
lean_inc_ref(v_it_50_);
v___x_51_ = lean_apply_1(v_p_49_, v_it_50_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_pos_52_; lean_object* v_res_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_61_; 
lean_dec_ref(v_it_50_);
v_pos_52_ = lean_ctor_get(v___x_51_, 0);
v_res_53_ = lean_ctor_get(v___x_51_, 1);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_61_ == 0)
{
v___x_55_ = v___x_51_;
v_isShared_56_ = v_isSharedCheck_61_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_res_53_);
lean_inc(v_pos_52_);
lean_dec(v___x_51_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_61_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_57_; lean_object* v___x_59_; 
v___x_57_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_57_, 0, v_res_53_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v___x_57_);
v___x_59_ = v___x_55_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_pos_52_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v___x_57_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
else
{
lean_object* v_err_62_; 
v_err_62_ = lean_ctor_get(v___x_51_, 1);
lean_inc(v_err_62_);
if (lean_obj_tag(v_err_62_) == 0)
{
lean_object* v_pos_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_70_; 
lean_dec_ref(v_it_50_);
v_pos_63_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_70_ == 0)
{
lean_object* v_unused_71_; 
v_unused_71_ = lean_ctor_get(v___x_51_, 1);
lean_dec(v_unused_71_);
v___x_65_ = v___x_51_;
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_pos_63_);
lean_dec(v___x_51_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_68_; 
if (v_isShared_66_ == 0)
{
v___x_68_ = v___x_65_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_pos_63_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_err_62_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
else
{
lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_79_; 
lean_dec(v_err_62_);
v_isSharedCheck_79_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_79_ == 0)
{
lean_object* v_unused_80_; lean_object* v_unused_81_; 
v_unused_80_ = lean_ctor_get(v___x_51_, 1);
lean_dec(v_unused_80_);
v_unused_81_ = lean_ctor_get(v___x_51_, 0);
lean_dec(v_unused_81_);
v___x_73_ = v___x_51_;
v_isShared_74_ = v_isSharedCheck_79_;
goto v_resetjp_72_;
}
else
{
lean_dec(v___x_51_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_79_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_75_ = lean_box(0);
if (v_isShared_74_ == 0)
{
lean_ctor_set_tag(v___x_73_, 0);
lean_ctor_set(v___x_73_, 1, v___x_75_);
lean_ctor_set(v___x_73_, 0, v_it_50_);
v___x_77_ = v___x_73_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_it_50_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v___x_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_optionalUnlessEof(lean_object* v_00_u03b1_82_, lean_object* v_p_83_, lean_object* v_it_84_){
_start:
{
lean_object* v___x_85_; 
lean_inc_ref(v_it_84_);
v___x_85_ = lean_apply_1(v_p_83_, v_it_84_);
if (lean_obj_tag(v___x_85_) == 0)
{
lean_object* v_pos_86_; lean_object* v_res_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_95_; 
lean_dec_ref(v_it_84_);
v_pos_86_ = lean_ctor_get(v___x_85_, 0);
v_res_87_ = lean_ctor_get(v___x_85_, 1);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_95_ == 0)
{
v___x_89_ = v___x_85_;
v_isShared_90_ = v_isSharedCheck_95_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_res_87_);
lean_inc(v_pos_86_);
lean_dec(v___x_85_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_95_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v_res_87_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v___x_91_);
v___x_93_ = v___x_89_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_pos_86_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
else
{
lean_object* v_err_96_; 
v_err_96_ = lean_ctor_get(v___x_85_, 1);
lean_inc(v_err_96_);
if (lean_obj_tag(v_err_96_) == 0)
{
lean_object* v_pos_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_104_; 
lean_dec_ref(v_it_84_);
v_pos_97_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; 
v_unused_105_ = lean_ctor_get(v___x_85_, 1);
lean_dec(v_unused_105_);
v___x_99_ = v___x_85_;
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_pos_97_);
lean_dec(v___x_85_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_pos_97_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_err_96_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
else
{
lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_113_; 
lean_dec(v_err_96_);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_113_ == 0)
{
lean_object* v_unused_114_; lean_object* v_unused_115_; 
v_unused_114_ = lean_ctor_get(v___x_85_, 1);
lean_dec(v_unused_114_);
v_unused_115_ = lean_ctor_get(v___x_85_, 0);
lean_dec(v_unused_115_);
v___x_107_ = v___x_85_;
v_isShared_108_ = v_isSharedCheck_113_;
goto v_resetjp_106_;
}
else
{
lean_dec(v___x_85_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_113_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_109_; lean_object* v___x_111_; 
v___x_109_ = lean_box(0);
if (v_isShared_108_ == 0)
{
lean_ctor_set_tag(v___x_107_, 0);
lean_ctor_set(v___x_107_, 1, v___x_109_);
lean_ctor_set(v___x_107_, 0, v_it_84_);
v___x_111_ = v___x_107_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_it_84_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(lean_object* v_parser_118_, lean_object* v_maxCount_119_, lean_object* v_acc_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_122_; 
lean_inc_ref(v_parser_118_);
lean_inc_ref(v_a_121_);
v___x_122_ = lean_apply_1(v_parser_118_, v_a_121_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_res_123_; 
v_res_123_ = lean_ctor_get(v___x_122_, 1);
lean_inc(v_res_123_);
if (lean_obj_tag(v_res_123_) == 0)
{
lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
lean_dec(v_maxCount_119_);
lean_dec_ref(v_parser_118_);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_130_ == 0)
{
lean_object* v_unused_131_; lean_object* v_unused_132_; 
v_unused_131_ = lean_ctor_get(v___x_122_, 1);
lean_dec(v_unused_131_);
v_unused_132_ = lean_ctor_get(v___x_122_, 0);
lean_dec(v_unused_132_);
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v_acc_120_);
lean_ctor_set(v___x_125_, 0, v_a_121_);
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_121_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_acc_120_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
else
{
lean_object* v_pos_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_161_; 
lean_dec_ref(v_a_121_);
v_pos_133_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_161_ == 0)
{
lean_object* v_unused_162_; 
v_unused_162_ = lean_ctor_get(v___x_122_, 1);
lean_dec(v_unused_162_);
v___x_135_ = v___x_122_;
v_isShared_136_ = v_isSharedCheck_161_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_pos_133_);
lean_dec(v___x_122_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_161_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v_val_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_160_; 
v_val_137_ = lean_ctor_get(v_res_123_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v_res_123_);
if (v_isSharedCheck_160_ == 0)
{
v___x_139_ = v_res_123_;
v_isShared_140_ = v_isSharedCheck_160_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_val_137_);
lean_dec(v_res_123_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_160_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_141_ = lean_array_get_size(v_acc_120_);
v___x_142_ = lean_unsigned_to_nat(1u);
v___x_143_ = lean_nat_add(v___x_141_, v___x_142_);
v___x_144_ = lean_nat_dec_lt(v_maxCount_119_, v___x_143_);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; 
lean_dec(v___x_143_);
lean_del_object(v___x_139_);
lean_del_object(v___x_135_);
v___x_145_ = lean_array_push(v_acc_120_, v_val_137_);
v_acc_120_ = v___x_145_;
v_a_121_ = v_pos_133_;
goto _start;
}
else
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_155_; 
lean_dec(v_val_137_);
lean_dec_ref(v_acc_120_);
lean_dec_ref(v_parser_118_);
v___x_147_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__0));
v___x_148_ = l_Nat_reprFast(v___x_143_);
v___x_149_ = lean_string_append(v___x_147_, v___x_148_);
lean_dec_ref(v___x_148_);
v___x_150_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__1));
v___x_151_ = lean_string_append(v___x_149_, v___x_150_);
v___x_152_ = l_Nat_reprFast(v_maxCount_119_);
v___x_153_ = lean_string_append(v___x_151_, v___x_152_);
lean_dec_ref(v___x_152_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 0, v___x_153_);
v___x_155_ = v___x_139_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_153_);
v___x_155_ = v_reuseFailAlloc_159_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_157_; 
if (v_isShared_136_ == 0)
{
lean_ctor_set_tag(v___x_135_, 1);
lean_ctor_set(v___x_135_, 1, v___x_155_);
v___x_157_ = v___x_135_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_pos_133_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
}
}
}
else
{
lean_object* v_err_163_; 
lean_dec(v_maxCount_119_);
lean_dec_ref(v_parser_118_);
v_err_163_ = lean_ctor_get(v___x_122_, 1);
lean_inc(v_err_163_);
if (lean_obj_tag(v_err_163_) == 0)
{
lean_object* v_pos_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
lean_dec_ref(v_a_121_);
lean_dec_ref(v_acc_120_);
v_pos_164_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_171_ == 0)
{
lean_object* v_unused_172_; 
v_unused_172_ = lean_ctor_get(v___x_122_, 1);
lean_dec(v_unused_172_);
v___x_166_ = v___x_122_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_pos_164_);
lean_dec(v___x_122_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_pos_164_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_err_163_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
else
{
lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_179_; 
lean_dec(v_err_163_);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_179_ == 0)
{
lean_object* v_unused_180_; lean_object* v_unused_181_; 
v_unused_180_ = lean_ctor_get(v___x_122_, 1);
lean_dec(v_unused_180_);
v_unused_181_ = lean_ctor_get(v___x_122_, 0);
lean_dec(v_unused_181_);
v___x_174_ = v___x_122_;
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
else
{
lean_dec(v___x_122_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
lean_ctor_set_tag(v___x_174_, 0);
lean_ctor_set(v___x_174_, 1, v_acc_120_);
lean_ctor_set(v___x_174_, 0, v_a_121_);
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_a_121_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_acc_120_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go(lean_object* v_00_u03b1_182_, lean_object* v_parser_183_, lean_object* v_maxCount_184_, lean_object* v_acc_185_, lean_object* v_a_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(v_parser_183_, v_maxCount_184_, v_acc_185_, v_a_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go_match__1_splitter___redArg(lean_object* v_____do__lift_188_, lean_object* v_h__1_189_, lean_object* v_h__2_190_){
_start:
{
if (lean_obj_tag(v_____do__lift_188_) == 0)
{
lean_object* v___x_191_; lean_object* v___x_192_; 
lean_dec(v_h__2_190_);
v___x_191_ = lean_box(0);
v___x_192_ = lean_apply_1(v_h__1_189_, v___x_191_);
return v___x_192_;
}
else
{
lean_object* v_val_193_; lean_object* v___x_194_; 
lean_dec(v_h__1_189_);
v_val_193_ = lean_ctor_get(v_____do__lift_188_, 0);
lean_inc(v_val_193_);
lean_dec_ref_known(v_____do__lift_188_, 1);
v___x_194_ = lean_apply_1(v_h__2_190_, v_val_193_);
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go_match__1_splitter(lean_object* v_00_u03b1_195_, lean_object* v_motive_196_, lean_object* v_____do__lift_197_, lean_object* v_h__1_198_, lean_object* v_h__2_199_){
_start:
{
if (lean_obj_tag(v_____do__lift_197_) == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec(v_h__2_199_);
v___x_200_ = lean_box(0);
v___x_201_ = lean_apply_1(v_h__1_198_, v___x_200_);
return v___x_201_;
}
else
{
lean_object* v_val_202_; lean_object* v___x_203_; 
lean_dec(v_h__1_198_);
v_val_202_ = lean_ctor_get(v_____do__lift_197_, 0);
lean_inc(v_val_202_);
lean_dec_ref_known(v_____do__lift_197_, 1);
v___x_203_ = lean_apply_1(v_h__2_199_, v_val_202_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(lean_object* v_parser_206_, lean_object* v_maxCount_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg___closed__0));
v___x_210_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(v_parser_206_, v_maxCount_207_, v___x_209_, v_a_208_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems(lean_object* v_00_u03b1_211_, lean_object* v_parser_212_, lean_object* v_maxCount_213_, lean_object* v_a_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v_parser_212_, v_maxCount_213_, v_a_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(lean_object* v_x_219_, lean_object* v_a_220_){
_start:
{
if (lean_obj_tag(v_x_219_) == 1)
{
lean_object* v_val_221_; lean_object* v___x_222_; 
v_val_221_ = lean_ctor_get(v_x_219_, 0);
lean_inc(v_val_221_);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v_a_220_);
lean_ctor_set(v___x_222_, 1, v_val_221_);
return v___x_222_;
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___closed__1));
v___x_224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_224_, 0, v_a_220_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___boxed(lean_object* v_x_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_x_225_, v_a_226_);
lean_dec(v_x_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption(lean_object* v_00_u03b1_228_, lean_object* v_x_229_, lean_object* v_a_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_x_229_, v_a_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___boxed(lean_object* v_00_u03b1_232_, lean_object* v_x_233_, lean_object* v_a_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption(v_00_u03b1_232_, v_x_233_, v_a_234_);
lean_dec(v_x_233_);
return v_res_235_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0(uint8_t v_c_236_){
_start:
{
uint32_t v___x_237_; uint32_t v___x_248_; uint8_t v___x_249_; 
v___x_237_ = lean_uint8_to_uint32(v_c_236_);
v___x_248_ = 33;
v___x_249_ = lean_uint32_dec_eq(v___x_237_, v___x_248_);
if (v___x_249_ == 0)
{
uint32_t v___x_250_; uint8_t v___x_251_; 
v___x_250_ = 35;
v___x_251_ = lean_uint32_dec_eq(v___x_237_, v___x_250_);
if (v___x_251_ == 0)
{
uint32_t v___x_252_; uint8_t v___x_253_; 
v___x_252_ = 36;
v___x_253_ = lean_uint32_dec_eq(v___x_237_, v___x_252_);
if (v___x_253_ == 0)
{
uint32_t v___x_254_; uint8_t v___x_255_; 
v___x_254_ = 37;
v___x_255_ = lean_uint32_dec_eq(v___x_237_, v___x_254_);
if (v___x_255_ == 0)
{
uint32_t v___x_256_; uint8_t v___x_257_; 
v___x_256_ = 38;
v___x_257_ = lean_uint32_dec_eq(v___x_237_, v___x_256_);
if (v___x_257_ == 0)
{
uint32_t v___x_258_; uint8_t v___x_259_; 
v___x_258_ = 39;
v___x_259_ = lean_uint32_dec_eq(v___x_237_, v___x_258_);
if (v___x_259_ == 0)
{
uint32_t v___x_260_; uint8_t v___x_261_; 
v___x_260_ = 42;
v___x_261_ = lean_uint32_dec_eq(v___x_237_, v___x_260_);
if (v___x_261_ == 0)
{
uint32_t v___x_262_; uint8_t v___x_263_; 
v___x_262_ = 43;
v___x_263_ = lean_uint32_dec_eq(v___x_237_, v___x_262_);
if (v___x_263_ == 0)
{
uint32_t v___x_264_; uint8_t v___x_265_; 
v___x_264_ = 45;
v___x_265_ = lean_uint32_dec_eq(v___x_237_, v___x_264_);
if (v___x_265_ == 0)
{
uint32_t v___x_266_; uint8_t v___x_267_; 
v___x_266_ = 46;
v___x_267_ = lean_uint32_dec_eq(v___x_237_, v___x_266_);
if (v___x_267_ == 0)
{
uint32_t v___x_268_; uint8_t v___x_269_; 
v___x_268_ = 94;
v___x_269_ = lean_uint32_dec_eq(v___x_237_, v___x_268_);
if (v___x_269_ == 0)
{
uint32_t v___x_270_; uint8_t v___x_271_; 
v___x_270_ = 95;
v___x_271_ = lean_uint32_dec_eq(v___x_237_, v___x_270_);
if (v___x_271_ == 0)
{
uint32_t v___x_272_; uint8_t v___x_273_; 
v___x_272_ = 96;
v___x_273_ = lean_uint32_dec_eq(v___x_237_, v___x_272_);
if (v___x_273_ == 0)
{
uint32_t v___x_274_; uint8_t v___x_275_; 
v___x_274_ = 124;
v___x_275_ = lean_uint32_dec_eq(v___x_237_, v___x_274_);
if (v___x_275_ == 0)
{
uint32_t v___x_276_; uint8_t v___x_277_; 
v___x_276_ = 126;
v___x_277_ = lean_uint32_dec_eq(v___x_237_, v___x_276_);
if (v___x_277_ == 0)
{
uint32_t v___x_278_; uint8_t v___x_279_; 
v___x_278_ = 48;
v___x_279_ = lean_uint32_dec_le(v___x_278_, v___x_237_);
if (v___x_279_ == 0)
{
goto v___jp_243_;
}
else
{
uint32_t v___x_280_; uint8_t v___x_281_; 
v___x_280_ = 57;
v___x_281_ = lean_uint32_dec_le(v___x_237_, v___x_280_);
if (v___x_281_ == 0)
{
goto v___jp_243_;
}
else
{
return v___x_281_;
}
}
}
else
{
return v___x_277_;
}
}
else
{
return v___x_275_;
}
}
else
{
return v___x_273_;
}
}
else
{
return v___x_271_;
}
}
else
{
return v___x_269_;
}
}
else
{
return v___x_267_;
}
}
else
{
return v___x_265_;
}
}
else
{
return v___x_263_;
}
}
else
{
return v___x_261_;
}
}
else
{
return v___x_259_;
}
}
else
{
return v___x_257_;
}
}
else
{
return v___x_255_;
}
}
else
{
return v___x_253_;
}
}
else
{
return v___x_251_;
}
}
else
{
return v___x_249_;
}
v___jp_238_:
{
uint32_t v___x_239_; uint8_t v___x_240_; 
v___x_239_ = 97;
v___x_240_ = lean_uint32_dec_le(v___x_239_, v___x_237_);
if (v___x_240_ == 0)
{
return v___x_240_;
}
else
{
uint32_t v___x_241_; uint8_t v___x_242_; 
v___x_241_ = 122;
v___x_242_ = lean_uint32_dec_le(v___x_237_, v___x_241_);
return v___x_242_;
}
}
v___jp_243_:
{
uint32_t v___x_244_; uint8_t v___x_245_; 
v___x_244_ = 65;
v___x_245_ = lean_uint32_dec_le(v___x_244_, v___x_237_);
if (v___x_245_ == 0)
{
goto v___jp_238_;
}
else
{
uint32_t v___x_246_; uint8_t v___x_247_; 
v___x_246_ = 90;
v___x_247_ = lean_uint32_dec_le(v___x_237_, v___x_246_);
if (v___x_247_ == 0)
{
goto v___jp_238_;
}
else
{
return v___x_247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0___boxed(lean_object* v_c_282_){
_start:
{
uint8_t v_c_boxed_283_; uint8_t v_res_284_; lean_object* v_r_285_; 
v_c_boxed_283_ = lean_unbox(v_c_282_);
v_res_284_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0(v_c_boxed_283_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken(lean_object* v_limit_290_, lean_object* v_a_291_){
_start:
{
lean_object* v___f_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v_snd_295_; lean_object* v_snd_296_; uint8_t v___x_297_; 
v___f_292_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_293_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_291_);
v___x_294_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_292_, v_limit_290_, v___x_293_, v_a_291_);
v_snd_295_ = lean_ctor_get(v___x_294_, 1);
lean_inc(v_snd_295_);
v_snd_296_ = lean_ctor_get(v_snd_295_, 1);
v___x_297_ = lean_unbox(v_snd_296_);
if (v___x_297_ == 0)
{
lean_object* v_fst_298_; lean_object* v_fst_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_327_; 
v_fst_298_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_fst_298_);
lean_dec_ref(v___x_294_);
v_fst_299_ = lean_ctor_get(v_snd_295_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v_snd_295_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; 
v_unused_328_ = lean_ctor_get(v_snd_295_, 1);
lean_dec(v_unused_328_);
v___x_301_ = v_snd_295_;
v_isShared_302_ = v_isSharedCheck_327_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_fst_299_);
lean_dec(v_snd_295_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_327_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
uint8_t v___x_303_; 
v___x_303_ = lean_nat_dec_eq(v_fst_298_, v___x_293_);
if (v___x_303_ == 0)
{
lean_object* v_array_304_; lean_object* v_idx_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_322_; 
lean_del_object(v___x_301_);
v_array_304_ = lean_ctor_get(v_a_291_, 0);
v_idx_305_ = lean_ctor_get(v_a_291_, 1);
v_isSharedCheck_322_ = !lean_is_exclusive(v_a_291_);
if (v_isSharedCheck_322_ == 0)
{
v___x_307_ = v_a_291_;
v_isShared_308_ = v_isSharedCheck_322_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_idx_305_);
lean_inc(v_array_304_);
lean_dec(v_a_291_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_322_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v_lower_310_; lean_object* v_upper_311_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___y_319_; uint8_t v___x_321_; 
v___x_316_ = lean_nat_add(v_idx_305_, v_fst_298_);
lean_dec(v_fst_298_);
v___x_317_ = lean_byte_array_size(v_array_304_);
v___x_321_ = lean_nat_dec_le(v_idx_305_, v___x_293_);
if (v___x_321_ == 0)
{
v___y_319_ = v_idx_305_;
goto v___jp_318_;
}
else
{
lean_dec(v_idx_305_);
v___y_319_ = v___x_293_;
goto v___jp_318_;
}
v___jp_309_:
{
lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_312_ = l_ByteArray_toByteSlice(v_array_304_, v_lower_310_, v_upper_311_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v___x_312_);
lean_ctor_set(v___x_307_, 0, v_fst_299_);
v___x_314_ = v___x_307_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_fst_299_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
v___jp_318_:
{
uint8_t v___x_320_; 
v___x_320_ = lean_nat_dec_le(v___x_316_, v___x_317_);
if (v___x_320_ == 0)
{
lean_dec(v___x_316_);
v_lower_310_ = v___y_319_;
v_upper_311_ = v___x_317_;
goto v___jp_309_;
}
else
{
v_lower_310_ = v___y_319_;
v_upper_311_ = v___x_316_;
goto v___jp_309_;
}
}
}
}
else
{
lean_object* v___x_323_; lean_object* v___x_325_; 
lean_dec(v_fst_299_);
lean_dec(v_fst_298_);
v___x_323_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_302_ == 0)
{
lean_ctor_set_tag(v___x_301_, 1);
lean_ctor_set(v___x_301_, 1, v___x_323_);
lean_ctor_set(v___x_301_, 0, v_a_291_);
v___x_325_ = v___x_301_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_291_);
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
else
{
lean_object* v_fst_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_337_; 
lean_dec_ref(v___x_294_);
lean_dec_ref(v_a_291_);
v_fst_329_ = lean_ctor_get(v_snd_295_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_snd_295_);
if (v_isSharedCheck_337_ == 0)
{
lean_object* v_unused_338_; 
v_unused_338_ = lean_ctor_get(v_snd_295_, 1);
lean_dec(v_unused_338_);
v___x_331_ = v_snd_295_;
v_isShared_332_ = v_isSharedCheck_337_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_fst_329_);
lean_dec(v_snd_295_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_337_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_333_ = lean_box(0);
if (v_isShared_332_ == 0)
{
lean_ctor_set_tag(v___x_331_, 1);
lean_ctor_set(v___x_331_, 1, v___x_333_);
v___x_335_ = v___x_331_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_fst_329_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___boxed(lean_object* v_limit_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken(v_limit_339_, v_a_340_);
lean_dec(v_limit_339_);
return v_res_341_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__0));
v___x_344_ = lean_string_to_utf8(v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf(lean_object* v_a_345_){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_347_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_346_, v_a_345_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(lean_object* v_limits_351_, lean_object* v_a_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_array_354_; lean_object* v_idx_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v_array_354_ = lean_ctor_get(v___y_353_, 0);
v_idx_355_ = lean_ctor_get(v___y_353_, 1);
v___x_356_ = lean_byte_array_size(v_array_354_);
v___x_357_ = lean_nat_dec_lt(v_idx_355_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; 
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___y_353_);
lean_ctor_set(v___x_358_, 1, v_a_352_);
return v___x_358_;
}
else
{
uint8_t v___x_359_; uint8_t v___x_360_; uint8_t v___x_361_; 
v___x_359_ = lean_byte_array_fget(v_array_354_, v_idx_355_);
v___x_360_ = 13;
v___x_361_ = lean_uint8_dec_eq(v___x_359_, v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; 
v___x_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_362_, 0, v___y_353_);
lean_ctor_set(v___x_362_, 1, v_a_352_);
return v___x_362_;
}
else
{
lean_object* v_maxLeadingEmptyLines_363_; uint8_t v___x_364_; 
v_maxLeadingEmptyLines_363_ = lean_ctor_get(v_limits_351_, 11);
v___x_364_ = lean_nat_dec_le(v_maxLeadingEmptyLines_363_, v_a_352_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_366_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_365_, v___y_353_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_pos_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v_pos_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_pos_367_);
lean_dec_ref_known(v___x_366_, 2);
v___x_368_ = lean_unsigned_to_nat(1u);
v___x_369_ = lean_nat_add(v_a_352_, v___x_368_);
lean_dec(v_a_352_);
v_a_352_ = v___x_369_;
v___y_353_ = v_pos_367_;
goto _start;
}
else
{
lean_object* v_pos_371_; lean_object* v_err_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_dec(v_a_352_);
v_pos_371_ = lean_ctor_get(v___x_366_, 0);
v_err_372_ = lean_ctor_get(v___x_366_, 1);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_366_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_err_372_);
lean_inc(v_pos_371_);
lean_dec(v___x_366_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_pos_371_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_err_372_);
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
else
{
lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec(v_a_352_);
v___x_380_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__1));
v___x_381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_381_, 0, v___y_353_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
return v___x_381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___boxed(lean_object* v_limits_382_, lean_object* v_a_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_382_, v_a_383_, v___y_384_);
lean_dec_ref(v_limits_382_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(lean_object* v_limits_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_count_388_; lean_object* v___x_389_; 
v_count_388_ = lean_unsigned_to_nat(0u);
v___x_389_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_386_, v_count_388_, v_a_387_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_pos_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_398_; 
v_pos_390_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_398_ == 0)
{
lean_object* v_unused_399_; 
v_unused_399_ = lean_ctor_get(v___x_389_, 1);
lean_dec(v_unused_399_);
v___x_392_ = v___x_389_;
v_isShared_393_ = v_isSharedCheck_398_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_pos_390_);
lean_dec(v___x_389_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_398_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_394_ = lean_box(0);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 1, v___x_394_);
v___x_396_ = v___x_392_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_pos_390_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v___x_394_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
else
{
lean_object* v_pos_400_; lean_object* v_err_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
v_pos_400_ = lean_ctor_get(v___x_389_, 0);
v_err_401_ = lean_ctor_get(v___x_389_, 1);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_389_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_err_401_);
lean_inc(v_pos_400_);
lean_dec(v___x_389_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_pos_400_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_err_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines___boxed(lean_object* v_limits_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_409_, v_a_410_);
lean_dec_ref(v_limits_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0(lean_object* v_limits_412_, lean_object* v_inst_413_, lean_object* v_a_414_, lean_object* v___y_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_412_, v_a_414_, v___y_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___boxed(lean_object* v_limits_417_, lean_object* v_inst_418_, lean_object* v_a_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0(v_limits_417_, v_inst_418_, v_a_419_, v___y_420_);
lean_dec_ref(v_limits_417_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp(lean_object* v_a_425_){
_start:
{
lean_object* v_array_426_; lean_object* v_idx_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_array_426_ = lean_ctor_get(v_a_425_, 0);
v_idx_427_ = lean_ctor_get(v_a_425_, 1);
v___x_428_ = lean_byte_array_size(v_array_426_);
v___x_429_ = lean_nat_dec_lt(v_idx_427_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_box(0);
v___x_431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_431_, 0, v_a_425_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
return v___x_431_;
}
else
{
uint8_t v___x_432_; uint8_t v_got_433_; uint8_t v___x_434_; 
v___x_432_ = 32;
v_got_433_ = lean_byte_array_fget(v_array_426_, v_idx_427_);
v___x_434_ = lean_uint8_dec_eq(v_got_433_, v___x_432_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_436_, 0, v_a_425_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
return v___x_436_;
}
else
{
lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_447_; 
lean_inc(v_idx_427_);
lean_inc_ref(v_array_426_);
v_isSharedCheck_447_ = !lean_is_exclusive(v_a_425_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; lean_object* v_unused_449_; 
v_unused_448_ = lean_ctor_get(v_a_425_, 1);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v_a_425_, 0);
lean_dec(v_unused_449_);
v___x_438_ = v_a_425_;
v_isShared_439_ = v_isSharedCheck_447_;
goto v_resetjp_437_;
}
else
{
lean_dec(v_a_425_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_447_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_440_ = lean_unsigned_to_nat(1u);
v___x_441_ = lean_nat_add(v_idx_427_, v___x_440_);
lean_dec(v_idx_427_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 1, v___x_441_);
v___x_443_ = v___x_438_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_array_426_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v___x_441_);
v___x_443_ = v_reuseFailAlloc_446_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_box(0);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_443_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
return v___x_445_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows(lean_object* v_limits_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_pos_457_; lean_object* v_pos_461_; lean_object* v_maxSpaceSequence_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v_snd_468_; lean_object* v_snd_469_; uint8_t v___x_470_; 
v_maxSpaceSequence_464_ = lean_ctor_get(v_limits_454_, 10);
v___x_465_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2));
v___x_466_ = lean_unsigned_to_nat(0u);
v___x_467_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___x_465_, v_maxSpaceSequence_464_, v___x_466_, v_a_455_);
v_snd_468_ = lean_ctor_get(v___x_467_, 1);
lean_inc(v_snd_468_);
lean_dec_ref(v___x_467_);
v_snd_469_ = lean_ctor_get(v_snd_468_, 1);
v___x_470_ = lean_unbox(v_snd_469_);
if (v___x_470_ == 0)
{
lean_object* v_fst_471_; lean_object* v_array_472_; lean_object* v_idx_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v_fst_471_ = lean_ctor_get(v_snd_468_, 0);
lean_inc(v_fst_471_);
lean_dec(v_snd_468_);
v_array_472_ = lean_ctor_get(v_fst_471_, 0);
v_idx_473_ = lean_ctor_get(v_fst_471_, 1);
v___x_474_ = lean_byte_array_size(v_array_472_);
v___x_475_ = lean_nat_dec_lt(v_idx_473_, v___x_474_);
if (v___x_475_ == 0)
{
v_pos_457_ = v_fst_471_;
goto v___jp_456_;
}
else
{
uint8_t v___x_476_; uint32_t v___x_477_; uint32_t v___x_478_; uint8_t v___x_479_; 
v___x_476_ = lean_byte_array_fget(v_array_472_, v_idx_473_);
v___x_477_ = lean_uint8_to_uint32(v___x_476_);
v___x_478_ = 32;
v___x_479_ = lean_uint32_dec_eq(v___x_477_, v___x_478_);
if (v___x_479_ == 0)
{
uint32_t v___x_480_; uint8_t v___x_481_; 
v___x_480_ = 9;
v___x_481_ = lean_uint32_dec_eq(v___x_477_, v___x_480_);
if (v___x_481_ == 0)
{
v_pos_457_ = v_fst_471_;
goto v___jp_456_;
}
else
{
v_pos_461_ = v_fst_471_;
goto v___jp_460_;
}
}
else
{
v_pos_461_ = v_fst_471_;
goto v___jp_460_;
}
}
}
else
{
lean_object* v_fst_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_490_; 
v_fst_482_ = lean_ctor_get(v_snd_468_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v_snd_468_);
if (v_isSharedCheck_490_ == 0)
{
lean_object* v_unused_491_; 
v_unused_491_ = lean_ctor_get(v_snd_468_, 1);
lean_dec(v_unused_491_);
v___x_484_ = v_snd_468_;
v_isShared_485_ = v_isSharedCheck_490_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_fst_482_);
lean_dec(v_snd_468_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_490_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_486_ = lean_box(0);
if (v_isShared_485_ == 0)
{
lean_ctor_set_tag(v___x_484_, 1);
lean_ctor_set(v___x_484_, 1, v___x_486_);
v___x_488_ = v___x_484_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_fst_482_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
v___jp_456_:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_box(0);
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v_pos_457_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
return v___x_459_;
}
v___jp_460_:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_463_, 0, v_pos_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
return v___x_463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___boxed(lean_object* v_limits_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows(v_limits_492_, v_a_493_);
lean_dec_ref(v_limits_492_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit(lean_object* v_a_496_){
_start:
{
lean_object* v_array_497_; lean_object* v_idx_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v_array_497_ = lean_ctor_get(v_a_496_, 0);
v_idx_498_ = lean_ctor_get(v_a_496_, 1);
v___x_499_ = lean_byte_array_size(v_array_497_);
v___x_500_ = lean_nat_dec_lt(v_idx_498_, v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_box(0);
v___x_502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_502_, 0, v_a_496_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
return v___x_502_;
}
else
{
lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_558_; 
lean_inc(v_idx_498_);
lean_inc_ref(v_array_497_);
v_isSharedCheck_558_ = !lean_is_exclusive(v_a_496_);
if (v_isSharedCheck_558_ == 0)
{
lean_object* v_unused_559_; lean_object* v_unused_560_; 
v_unused_559_ = lean_ctor_get(v_a_496_, 1);
lean_dec(v_unused_559_);
v_unused_560_ = lean_ctor_get(v_a_496_, 0);
lean_dec(v_unused_560_);
v___x_504_ = v_a_496_;
v_isShared_505_ = v_isSharedCheck_558_;
goto v_resetjp_503_;
}
else
{
lean_dec(v_a_496_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_558_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
uint8_t v_c_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v_it_x27_510_; 
v_c_506_ = lean_byte_array_fget(v_array_497_, v_idx_498_);
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = lean_nat_add(v_idx_498_, v___x_507_);
lean_dec(v_idx_498_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 1, v___x_508_);
v_it_x27_510_ = v___x_504_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_array_497_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v___x_508_);
v_it_x27_510_ = v_reuseFailAlloc_557_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
uint8_t v___x_553_; uint8_t v___x_554_; 
v___x_553_ = 48;
v___x_554_ = lean_uint8_dec_le(v___x_553_, v_c_506_);
if (v___x_554_ == 0)
{
goto v___jp_548_;
}
else
{
uint8_t v___x_555_; uint8_t v___x_556_; 
v___x_555_ = 57;
v___x_556_ = lean_uint8_dec_le(v_c_506_, v___x_555_);
if (v___x_556_ == 0)
{
goto v___jp_548_;
}
else
{
goto v___jp_528_;
}
}
v___jp_511_:
{
uint8_t v___x_512_; uint8_t v___x_513_; uint8_t v___x_514_; uint8_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_512_ = 97;
v___x_513_ = lean_uint8_sub(v_c_506_, v___x_512_);
v___x_514_ = 10;
v___x_515_ = lean_uint8_add(v___x_513_, v___x_514_);
v___x_516_ = lean_box(v___x_515_);
v___x_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_517_, 0, v_it_x27_510_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
return v___x_517_;
}
v___jp_518_:
{
uint8_t v___x_519_; uint8_t v___x_520_; 
v___x_519_ = 65;
v___x_520_ = lean_uint8_dec_le(v___x_519_, v_c_506_);
if (v___x_520_ == 0)
{
goto v___jp_511_;
}
else
{
uint8_t v___x_521_; uint8_t v___x_522_; 
v___x_521_ = 70;
v___x_522_ = lean_uint8_dec_le(v_c_506_, v___x_521_);
if (v___x_522_ == 0)
{
goto v___jp_511_;
}
else
{
uint8_t v___x_523_; uint8_t v___x_524_; uint8_t v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_523_ = lean_uint8_sub(v_c_506_, v___x_519_);
v___x_524_ = 10;
v___x_525_ = lean_uint8_add(v___x_523_, v___x_524_);
v___x_526_ = lean_box(v___x_525_);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v_it_x27_510_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
return v___x_527_;
}
}
}
v___jp_528_:
{
uint8_t v___x_529_; uint8_t v___x_530_; 
v___x_529_ = 48;
v___x_530_ = lean_uint8_dec_le(v___x_529_, v_c_506_);
if (v___x_530_ == 0)
{
goto v___jp_518_;
}
else
{
uint8_t v___x_531_; uint8_t v___x_532_; 
v___x_531_ = 57;
v___x_532_ = lean_uint8_dec_le(v_c_506_, v___x_531_);
if (v___x_532_ == 0)
{
goto v___jp_518_;
}
else
{
uint8_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = lean_uint8_sub(v_c_506_, v___x_529_);
v___x_534_ = lean_box(v___x_533_);
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v_it_x27_510_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
return v___x_535_;
}
}
}
v___jp_536_:
{
lean_object* v___x_537_; uint32_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_537_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0));
v___x_538_ = lean_uint8_to_uint32(v_c_506_);
v___x_539_ = l_Char_quote(v___x_538_);
v___x_540_ = lean_string_append(v___x_537_, v___x_539_);
lean_dec_ref(v___x_539_);
v___x_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
v___x_542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_542_, 0, v_it_x27_510_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
return v___x_542_;
}
v___jp_543_:
{
uint8_t v___x_544_; uint8_t v___x_545_; 
v___x_544_ = 65;
v___x_545_ = lean_uint8_dec_le(v___x_544_, v_c_506_);
if (v___x_545_ == 0)
{
goto v___jp_536_;
}
else
{
uint8_t v___x_546_; uint8_t v___x_547_; 
v___x_546_ = 70;
v___x_547_ = lean_uint8_dec_le(v_c_506_, v___x_546_);
if (v___x_547_ == 0)
{
goto v___jp_536_;
}
else
{
goto v___jp_528_;
}
}
}
v___jp_548_:
{
uint8_t v___x_549_; uint8_t v___x_550_; 
v___x_549_ = 97;
v___x_550_ = lean_uint8_dec_le(v___x_549_, v_c_506_);
if (v___x_550_ == 0)
{
goto v___jp_543_;
}
else
{
uint8_t v___x_551_; uint8_t v___x_552_; 
v___x_551_ = 102;
v___x_552_ = lean_uint8_dec_le(v_c_506_, v___x_551_);
if (v___x_552_ == 0)
{
goto v___jp_543_;
}
else
{
goto v___jp_528_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(lean_object* v_acc_567_, lean_object* v_count_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___x_570_; 
lean_inc_ref(v_a_569_);
v___x_570_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit(v_a_569_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_pos_571_; lean_object* v_res_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_589_; 
lean_dec_ref(v_a_569_);
v_pos_571_ = lean_ctor_get(v___x_570_, 0);
v_res_572_ = lean_ctor_get(v___x_570_, 1);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_589_ == 0)
{
v___x_574_ = v___x_570_;
v_isShared_575_ = v_isSharedCheck_589_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_res_572_);
lean_inc(v_pos_571_);
lean_dec(v___x_570_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_589_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_576_ = lean_unsigned_to_nat(16u);
v___x_577_ = lean_unsigned_to_nat(1u);
v___x_578_ = lean_nat_add(v_count_568_, v___x_577_);
lean_dec(v_count_568_);
v___x_579_ = lean_nat_dec_lt(v___x_576_, v___x_578_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; uint8_t v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
lean_del_object(v___x_574_);
v___x_580_ = lean_nat_mul(v_acc_567_, v___x_576_);
lean_dec(v_acc_567_);
v___x_581_ = lean_unbox(v_res_572_);
lean_dec(v_res_572_);
v___x_582_ = lean_uint8_to_nat(v___x_581_);
v___x_583_ = lean_nat_add(v___x_580_, v___x_582_);
lean_dec(v___x_580_);
v_acc_567_ = v___x_583_;
v_count_568_ = v___x_578_;
v_a_569_ = v_pos_571_;
goto _start;
}
else
{
lean_object* v___x_585_; lean_object* v___x_587_; 
lean_dec(v___x_578_);
lean_dec(v_res_572_);
lean_dec(v_acc_567_);
v___x_585_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__1));
if (v_isShared_575_ == 0)
{
lean_ctor_set_tag(v___x_574_, 1);
lean_ctor_set(v___x_574_, 1, v___x_585_);
v___x_587_ = v___x_574_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_pos_571_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
else
{
lean_object* v_err_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_615_; 
v_err_590_ = lean_ctor_get(v___x_570_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v___x_570_, 0);
lean_dec(v_unused_616_);
v___x_592_ = v___x_570_;
v_isShared_593_ = v_isSharedCheck_615_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_err_590_);
lean_dec(v___x_570_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_615_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v_array_594_; lean_object* v_idx_595_; uint8_t v___x_596_; 
v_array_594_ = lean_ctor_get(v_a_569_, 0);
v_idx_595_ = lean_ctor_get(v_a_569_, 1);
v___x_596_ = lean_nat_dec_eq(v_idx_595_, v_idx_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_598_; 
lean_dec(v_count_568_);
lean_dec(v_acc_567_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v_a_569_);
v___x_598_ = v___x_592_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_569_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_err_590_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
else
{
lean_object* v___x_600_; uint8_t v___x_601_; 
lean_dec(v_err_590_);
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = lean_nat_dec_eq(v_count_568_, v___x_600_);
lean_dec(v_count_568_);
if (v___x_601_ == 0)
{
lean_object* v___x_603_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set_tag(v___x_592_, 0);
lean_ctor_set(v___x_592_, 1, v_acc_567_);
lean_ctor_set(v___x_592_, 0, v_a_569_);
v___x_603_ = v___x_592_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_569_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_acc_567_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
else
{
lean_object* v___x_605_; uint8_t v___x_606_; 
lean_dec(v_acc_567_);
v___x_605_ = lean_byte_array_size(v_array_594_);
v___x_606_ = lean_nat_dec_lt(v_idx_595_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_607_ = lean_box(0);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v___x_607_);
lean_ctor_set(v___x_592_, 0, v_a_569_);
v___x_609_ = v___x_592_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_569_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
else
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__3));
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v___x_611_);
lean_ctor_set(v___x_592_, 0, v_a_569_);
v___x_613_ = v___x_592_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_569_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go_match__1_splitter___redArg(lean_object* v_____do__lift_617_, lean_object* v_h__1_618_, lean_object* v_h__2_619_){
_start:
{
if (lean_obj_tag(v_____do__lift_617_) == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec(v_h__1_618_);
v___x_620_ = lean_box(0);
v___x_621_ = lean_apply_1(v_h__2_619_, v___x_620_);
return v___x_621_;
}
else
{
lean_object* v_val_622_; lean_object* v___x_623_; 
lean_dec(v_h__2_619_);
v_val_622_ = lean_ctor_get(v_____do__lift_617_, 0);
lean_inc(v_val_622_);
lean_dec_ref_known(v_____do__lift_617_, 1);
v___x_623_ = lean_apply_1(v_h__1_618_, v_val_622_);
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go_match__1_splitter(lean_object* v_motive_624_, lean_object* v_____do__lift_625_, lean_object* v_h__1_626_, lean_object* v_h__2_627_){
_start:
{
if (lean_obj_tag(v_____do__lift_625_) == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec(v_h__1_626_);
v___x_628_ = lean_box(0);
v___x_629_ = lean_apply_1(v_h__2_627_, v___x_628_);
return v___x_629_;
}
else
{
lean_object* v_val_630_; lean_object* v___x_631_; 
lean_dec(v_h__2_627_);
v_val_630_ = lean_ctor_get(v_____do__lift_625_, 0);
lean_inc(v_val_630_);
lean_dec_ref_known(v_____do__lift_625_, 1);
v___x_631_ = lean_apply_1(v_h__1_626_, v_val_630_);
return v___x_631_;
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex___lam__0(uint8_t v_x_632_){
_start:
{
uint8_t v___x_633_; uint8_t v___x_634_; 
v___x_633_ = 48;
v___x_634_ = lean_uint8_dec_eq(v_x_632_, v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex___lam__0___boxed(lean_object* v_x_635_){
_start:
{
uint8_t v_x_760__boxed_636_; uint8_t v_res_637_; lean_object* v_r_638_; 
v_x_760__boxed_636_ = lean_unbox(v_x_635_);
v_res_637_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex___lam__0(v_x_760__boxed_636_);
v_r_638_ = lean_box(v_res_637_);
return v_r_638_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(lean_object* v_a_640_){
_start:
{
lean_object* v___f_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v_snd_644_; lean_object* v_fst_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_712_; 
v___f_641_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex___closed__0));
v___x_642_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_640_);
v___x_643_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v___f_641_, v___x_642_, v_a_640_);
v_snd_644_ = lean_ctor_get(v___x_643_, 1);
v_fst_645_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_712_ == 0)
{
v___x_647_ = v___x_643_;
v_isShared_648_ = v_isSharedCheck_712_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_snd_644_);
lean_inc(v_fst_645_);
lean_dec(v___x_643_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_712_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v_fst_649_; lean_object* v_snd_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_711_; 
v_fst_649_ = lean_ctor_get(v_snd_644_, 0);
v_snd_650_ = lean_ctor_get(v_snd_644_, 1);
v_isSharedCheck_711_ = !lean_is_exclusive(v_snd_644_);
if (v_isSharedCheck_711_ == 0)
{
v___x_652_ = v_snd_644_;
v_isShared_653_ = v_isSharedCheck_711_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_snd_650_);
lean_inc(v_fst_649_);
lean_dec(v_snd_644_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_711_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
uint8_t v___y_655_; uint8_t v___y_668_; uint8_t v___x_674_; 
v___x_674_ = lean_unbox(v_snd_650_);
lean_dec(v_snd_650_);
if (v___x_674_ == 0)
{
lean_object* v_array_675_; lean_object* v_idx_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_706_; 
lean_del_object(v___x_647_);
v_array_675_ = lean_ctor_get(v_a_640_, 0);
v_idx_676_ = lean_ctor_get(v_a_640_, 1);
v_isSharedCheck_706_ = !lean_is_exclusive(v_a_640_);
if (v_isSharedCheck_706_ == 0)
{
v___x_678_ = v_a_640_;
v_isShared_679_ = v_isSharedCheck_706_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_idx_676_);
lean_inc(v_array_675_);
lean_dec(v_a_640_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_706_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v_lower_681_; lean_object* v_upper_682_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___y_703_; uint8_t v___x_705_; 
v___x_700_ = lean_nat_add(v_idx_676_, v_fst_645_);
lean_dec(v_fst_645_);
v___x_701_ = lean_byte_array_size(v_array_675_);
v___x_705_ = lean_nat_dec_le(v_idx_676_, v___x_642_);
if (v___x_705_ == 0)
{
v___y_703_ = v_idx_676_;
goto v___jp_702_;
}
else
{
lean_dec(v_idx_676_);
v___y_703_ = v___x_642_;
goto v___jp_702_;
}
v___jp_680_:
{
lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_683_ = l_ByteArray_toByteSlice(v_array_675_, v_lower_681_, v_upper_682_);
v___x_684_ = l_ByteSlice_size(v___x_683_);
lean_dec_ref(v___x_683_);
v___x_685_ = lean_nat_dec_lt(v___x_642_, v___x_684_);
lean_dec(v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; 
lean_del_object(v___x_678_);
lean_del_object(v___x_652_);
v___x_686_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(v___x_642_, v___x_642_, v_fst_649_);
return v___x_686_;
}
else
{
lean_object* v_array_687_; lean_object* v_idx_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v_array_687_ = lean_ctor_get(v_fst_649_, 0);
v_idx_688_ = lean_ctor_get(v_fst_649_, 1);
v___x_689_ = lean_byte_array_size(v_array_687_);
v___x_690_ = lean_nat_dec_lt(v_idx_688_, v___x_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_692_; 
lean_del_object(v___x_652_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 1, v___x_642_);
lean_ctor_set(v___x_678_, 0, v_fst_649_);
v___x_692_ = v___x_678_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_fst_649_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v___x_642_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
else
{
uint8_t v___x_694_; uint8_t v___x_695_; uint8_t v___x_696_; 
lean_del_object(v___x_678_);
v___x_694_ = lean_byte_array_fget(v_array_687_, v_idx_688_);
v___x_695_ = 48;
v___x_696_ = lean_uint8_dec_le(v___x_695_, v___x_694_);
if (v___x_696_ == 0)
{
v___y_668_ = v___x_694_;
goto v___jp_667_;
}
else
{
uint8_t v___x_697_; uint8_t v___x_698_; 
v___x_697_ = 57;
v___x_698_ = lean_uint8_dec_le(v___x_694_, v___x_697_);
if (v___x_698_ == 0)
{
v___y_668_ = v___x_694_;
goto v___jp_667_;
}
else
{
lean_object* v___x_699_; 
lean_del_object(v___x_652_);
v___x_699_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(v___x_642_, v___x_642_, v_fst_649_);
return v___x_699_;
}
}
}
}
}
v___jp_702_:
{
uint8_t v___x_704_; 
v___x_704_ = lean_nat_dec_le(v___x_700_, v___x_701_);
if (v___x_704_ == 0)
{
lean_dec(v___x_700_);
v_lower_681_ = v___y_703_;
v_upper_682_ = v___x_701_;
goto v___jp_680_;
}
else
{
v_lower_681_ = v___y_703_;
v_upper_682_ = v___x_700_;
goto v___jp_680_;
}
}
}
}
else
{
lean_object* v___x_707_; lean_object* v___x_709_; 
lean_del_object(v___x_652_);
lean_dec(v_fst_645_);
lean_dec_ref(v_a_640_);
v___x_707_ = lean_box(0);
if (v_isShared_648_ == 0)
{
lean_ctor_set_tag(v___x_647_, 1);
lean_ctor_set(v___x_647_, 1, v___x_707_);
lean_ctor_set(v___x_647_, 0, v_fst_649_);
v___x_709_ = v___x_647_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_fst_649_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
v___jp_654_:
{
uint8_t v___x_656_; uint8_t v___x_657_; 
v___x_656_ = 65;
v___x_657_ = lean_uint8_dec_le(v___x_656_, v___y_655_);
if (v___x_657_ == 0)
{
lean_object* v___x_659_; 
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 1, v___x_642_);
v___x_659_ = v___x_652_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_fst_649_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v___x_642_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
else
{
uint8_t v___x_661_; uint8_t v___x_662_; 
v___x_661_ = 70;
v___x_662_ = lean_uint8_dec_le(v___y_655_, v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_664_; 
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 1, v___x_642_);
v___x_664_ = v___x_652_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_fst_649_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v___x_642_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
else
{
lean_object* v___x_666_; 
lean_del_object(v___x_652_);
v___x_666_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(v___x_642_, v___x_642_, v_fst_649_);
return v___x_666_;
}
}
}
v___jp_667_:
{
uint8_t v___x_669_; uint8_t v___x_670_; 
v___x_669_ = 97;
v___x_670_ = lean_uint8_dec_le(v___x_669_, v___y_668_);
if (v___x_670_ == 0)
{
v___y_655_ = v___y_668_;
goto v___jp_654_;
}
else
{
uint8_t v___x_671_; uint8_t v___x_672_; 
v___x_671_ = 102;
v___x_672_ = lean_uint8_dec_le(v___y_668_, v___x_671_);
if (v___x_672_ == 0)
{
v___y_655_ = v___y_668_;
goto v___jp_654_;
}
else
{
lean_object* v___x_673_; 
lean_del_object(v___x_652_);
v___x_673_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(v___x_642_, v___x_642_, v_fst_649_);
return v___x_673_;
}
}
}
}
}
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__0));
v___x_715_ = lean_string_to_utf8(v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(lean_object* v_a_722_){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1);
v___x_724_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_723_, v_a_722_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_pos_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_786_; 
v_pos_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_786_ == 0)
{
lean_object* v_unused_787_; 
v_unused_787_ = lean_ctor_get(v___x_724_, 1);
lean_dec(v_unused_787_);
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_786_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_pos_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_786_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v_array_734_; lean_object* v_idx_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v_array_734_ = lean_ctor_get(v_pos_725_, 0);
v_idx_735_ = lean_ctor_get(v_pos_725_, 1);
v___x_736_ = lean_byte_array_size(v_array_734_);
v___x_737_ = lean_nat_dec_lt(v_idx_735_, v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; lean_object* v___x_739_; 
lean_del_object(v___x_727_);
v___x_738_ = lean_box(0);
v___x_739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_739_, 0, v_pos_725_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
return v___x_739_;
}
else
{
uint8_t v_c_740_; uint8_t v___x_741_; uint8_t v___x_742_; 
v_c_740_ = lean_byte_array_fget(v_array_734_, v_idx_735_);
v___x_741_ = 48;
v___x_742_ = lean_uint8_dec_le(v___x_741_, v_c_740_);
if (v___x_742_ == 0)
{
goto v___jp_729_;
}
else
{
uint8_t v___x_743_; uint8_t v___x_744_; 
v___x_743_ = 57;
v___x_744_ = lean_uint8_dec_le(v_c_740_, v___x_743_);
if (v___x_744_ == 0)
{
goto v___jp_729_;
}
else
{
lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_783_; 
lean_inc(v_idx_735_);
lean_inc_ref(v_array_734_);
lean_del_object(v___x_727_);
v_isSharedCheck_783_ = !lean_is_exclusive(v_pos_725_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; lean_object* v_unused_785_; 
v_unused_784_ = lean_ctor_get(v_pos_725_, 1);
lean_dec(v_unused_784_);
v_unused_785_ = lean_ctor_get(v_pos_725_, 0);
lean_dec(v_unused_785_);
v___x_746_ = v_pos_725_;
v_isShared_747_ = v_isSharedCheck_783_;
goto v_resetjp_745_;
}
else
{
lean_dec(v_pos_725_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_783_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v_it_x27_751_; 
v___x_748_ = lean_unsigned_to_nat(1u);
v___x_749_ = lean_nat_add(v_idx_735_, v___x_748_);
lean_dec(v_idx_735_);
lean_inc(v___x_749_);
lean_inc_ref(v_array_734_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v___x_749_);
v_it_x27_751_ = v___x_746_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_array_734_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v___x_749_);
v_it_x27_751_ = v_reuseFailAlloc_782_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
uint8_t v___x_752_; 
v___x_752_ = lean_nat_dec_lt(v___x_749_, v___x_736_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec(v___x_749_);
lean_dec_ref(v_array_734_);
v___x_753_ = lean_box(0);
v___x_754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_754_, 0, v_it_x27_751_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
return v___x_754_;
}
else
{
uint8_t v___x_755_; uint8_t v_got_756_; uint8_t v___x_757_; 
v___x_755_ = 46;
v_got_756_ = lean_byte_array_fget(v_array_734_, v___x_749_);
v___x_757_ = lean_uint8_dec_eq(v_got_756_, v___x_755_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec(v___x_749_);
lean_dec_ref(v_array_734_);
v___x_758_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5));
v___x_759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_759_, 0, v_it_x27_751_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
return v___x_759_;
}
else
{
lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_765_; 
lean_dec_ref(v_it_x27_751_);
v___x_760_ = lean_nat_add(v___x_749_, v___x_748_);
lean_dec(v___x_749_);
lean_inc(v___x_760_);
lean_inc_ref(v_array_734_);
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v_array_734_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_765_ = lean_nat_dec_lt(v___x_760_, v___x_736_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; lean_object* v___x_767_; 
lean_dec(v___x_760_);
lean_dec_ref(v_array_734_);
v___x_766_ = lean_box(0);
v___x_767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_761_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
return v___x_767_;
}
else
{
uint8_t v_c_768_; uint8_t v___x_769_; 
v_c_768_ = lean_byte_array_fget(v_array_734_, v___x_760_);
v___x_769_ = lean_uint8_dec_le(v___x_741_, v_c_768_);
if (v___x_769_ == 0)
{
lean_dec(v___x_760_);
lean_dec_ref(v_array_734_);
goto v___jp_762_;
}
else
{
uint8_t v___x_770_; 
v___x_770_ = lean_uint8_dec_le(v_c_768_, v___x_743_);
if (v___x_770_ == 0)
{
lean_dec(v___x_760_);
lean_dec_ref(v_array_734_);
goto v___jp_762_;
}
else
{
lean_object* v___x_771_; uint32_t v___x_772_; lean_object* v___x_773_; lean_object* v_it_x27_774_; uint32_t v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
lean_dec_ref_known(v___x_761_, 2);
v___x_771_ = lean_unsigned_to_nat(48u);
v___x_772_ = lean_uint8_to_uint32(v_c_740_);
v___x_773_ = lean_nat_add(v___x_760_, v___x_748_);
lean_dec(v___x_760_);
v_it_x27_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_774_, 0, v_array_734_);
lean_ctor_set(v_it_x27_774_, 1, v___x_773_);
v___x_775_ = lean_uint8_to_uint32(v_c_768_);
v___x_776_ = lean_uint32_to_nat(v___x_772_);
v___x_777_ = lean_nat_sub(v___x_776_, v___x_771_);
lean_dec(v___x_776_);
v___x_778_ = lean_uint32_to_nat(v___x_775_);
v___x_779_ = lean_nat_sub(v___x_778_, v___x_771_);
lean_dec(v___x_778_);
v___x_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_777_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v_it_x27_774_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
return v___x_781_;
}
}
}
v___jp_762_:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_761_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
return v___x_764_;
}
}
}
}
}
}
}
}
v___jp_729_:
{
lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_730_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
if (v_isShared_728_ == 0)
{
lean_ctor_set_tag(v___x_727_, 1);
lean_ctor_set(v___x_727_, 1, v___x_730_);
v___x_732_ = v___x_727_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_pos_725_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
else
{
lean_object* v_pos_788_; lean_object* v_err_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
v_pos_788_ = lean_ctor_get(v___x_724_, 0);
v_err_789_ = lean_ctor_get(v___x_724_, 1);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_724_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_err_789_);
lean_inc(v_pos_788_);
lean_dec(v___x_724_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_pos_788_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_err_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersion(lean_object* v_a_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_797_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_res_799_; lean_object* v_pos_800_; lean_object* v_fst_801_; lean_object* v_snd_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v_res_799_ = lean_ctor_get(v___x_798_, 1);
lean_inc(v_res_799_);
v_pos_800_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_pos_800_);
lean_dec_ref_known(v___x_798_, 2);
v_fst_801_ = lean_ctor_get(v_res_799_, 0);
lean_inc(v_fst_801_);
v_snd_802_ = lean_ctor_get(v_res_799_, 1);
lean_inc(v_snd_802_);
lean_dec(v_res_799_);
v___x_803_ = l_Std_Http_Version_ofNumber_x3f(v_fst_801_, v_snd_802_);
lean_dec(v_snd_802_);
lean_dec(v_fst_801_);
v___x_804_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_803_, v_pos_800_);
lean_dec(v___x_803_);
return v___x_804_;
}
else
{
lean_object* v_pos_805_; lean_object* v_err_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
v_pos_805_ = lean_ctor_get(v___x_798_, 0);
v_err_806_ = lean_ctor_get(v___x_798_, 1);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_798_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_err_806_);
lean_inc(v_pos_805_);
lean_dec(v___x_798_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_pos_805_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_err_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0(size_t v_sz_854_, size_t v_i_855_, lean_object* v_bs_856_){
_start:
{
uint8_t v___x_857_; 
v___x_857_ = lean_usize_dec_lt(v_i_855_, v_sz_854_);
if (v___x_857_ == 0)
{
return v_bs_856_;
}
else
{
lean_object* v_v_858_; lean_object* v___x_859_; lean_object* v_bs_x27_860_; lean_object* v___y_862_; uint8_t v___x_871_; 
v_v_858_ = lean_array_uget(v_bs_856_, v_i_855_);
v___x_859_ = lean_unsigned_to_nat(0u);
v_bs_x27_860_ = lean_array_uset(v_bs_856_, v_i_855_, v___x_859_);
v___x_871_ = lean_unbox(v_v_858_);
switch(v___x_871_)
{
case 0:
{
lean_object* v___x_872_; 
v___x_872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__0));
v___y_862_ = v___x_872_;
goto v___jp_861_;
}
case 1:
{
lean_object* v___x_873_; 
v___x_873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__1));
v___y_862_ = v___x_873_;
goto v___jp_861_;
}
case 2:
{
lean_object* v___x_874_; 
v___x_874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__2));
v___y_862_ = v___x_874_;
goto v___jp_861_;
}
case 3:
{
lean_object* v___x_875_; 
v___x_875_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__3));
v___y_862_ = v___x_875_;
goto v___jp_861_;
}
case 4:
{
lean_object* v___x_876_; 
v___x_876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__4));
v___y_862_ = v___x_876_;
goto v___jp_861_;
}
case 5:
{
lean_object* v___x_877_; 
v___x_877_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__5));
v___y_862_ = v___x_877_;
goto v___jp_861_;
}
case 6:
{
lean_object* v___x_878_; 
v___x_878_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__6));
v___y_862_ = v___x_878_;
goto v___jp_861_;
}
case 7:
{
lean_object* v___x_879_; 
v___x_879_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__7));
v___y_862_ = v___x_879_;
goto v___jp_861_;
}
case 8:
{
lean_object* v___x_880_; 
v___x_880_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__8));
v___y_862_ = v___x_880_;
goto v___jp_861_;
}
case 9:
{
lean_object* v___x_881_; 
v___x_881_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__9));
v___y_862_ = v___x_881_;
goto v___jp_861_;
}
case 10:
{
lean_object* v___x_882_; 
v___x_882_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__10));
v___y_862_ = v___x_882_;
goto v___jp_861_;
}
case 11:
{
lean_object* v___x_883_; 
v___x_883_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__11));
v___y_862_ = v___x_883_;
goto v___jp_861_;
}
case 12:
{
lean_object* v___x_884_; 
v___x_884_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__12));
v___y_862_ = v___x_884_;
goto v___jp_861_;
}
case 13:
{
lean_object* v___x_885_; 
v___x_885_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__13));
v___y_862_ = v___x_885_;
goto v___jp_861_;
}
case 14:
{
lean_object* v___x_886_; 
v___x_886_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__14));
v___y_862_ = v___x_886_;
goto v___jp_861_;
}
case 15:
{
lean_object* v___x_887_; 
v___x_887_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__15));
v___y_862_ = v___x_887_;
goto v___jp_861_;
}
case 16:
{
lean_object* v___x_888_; 
v___x_888_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__16));
v___y_862_ = v___x_888_;
goto v___jp_861_;
}
case 17:
{
lean_object* v___x_889_; 
v___x_889_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__17));
v___y_862_ = v___x_889_;
goto v___jp_861_;
}
case 18:
{
lean_object* v___x_890_; 
v___x_890_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__18));
v___y_862_ = v___x_890_;
goto v___jp_861_;
}
case 19:
{
lean_object* v___x_891_; 
v___x_891_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__19));
v___y_862_ = v___x_891_;
goto v___jp_861_;
}
case 20:
{
lean_object* v___x_892_; 
v___x_892_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__20));
v___y_862_ = v___x_892_;
goto v___jp_861_;
}
case 21:
{
lean_object* v___x_893_; 
v___x_893_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__21));
v___y_862_ = v___x_893_;
goto v___jp_861_;
}
case 22:
{
lean_object* v___x_894_; 
v___x_894_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__22));
v___y_862_ = v___x_894_;
goto v___jp_861_;
}
case 23:
{
lean_object* v___x_895_; 
v___x_895_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__23));
v___y_862_ = v___x_895_;
goto v___jp_861_;
}
case 24:
{
lean_object* v___x_896_; 
v___x_896_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__24));
v___y_862_ = v___x_896_;
goto v___jp_861_;
}
case 25:
{
lean_object* v___x_897_; 
v___x_897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__25));
v___y_862_ = v___x_897_;
goto v___jp_861_;
}
case 26:
{
lean_object* v___x_898_; 
v___x_898_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__26));
v___y_862_ = v___x_898_;
goto v___jp_861_;
}
case 27:
{
lean_object* v___x_899_; 
v___x_899_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__27));
v___y_862_ = v___x_899_;
goto v___jp_861_;
}
case 28:
{
lean_object* v___x_900_; 
v___x_900_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__28));
v___y_862_ = v___x_900_;
goto v___jp_861_;
}
case 29:
{
lean_object* v___x_901_; 
v___x_901_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__29));
v___y_862_ = v___x_901_;
goto v___jp_861_;
}
case 30:
{
lean_object* v___x_902_; 
v___x_902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__30));
v___y_862_ = v___x_902_;
goto v___jp_861_;
}
case 31:
{
lean_object* v___x_903_; 
v___x_903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__31));
v___y_862_ = v___x_903_;
goto v___jp_861_;
}
case 32:
{
lean_object* v___x_904_; 
v___x_904_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__32));
v___y_862_ = v___x_904_;
goto v___jp_861_;
}
case 33:
{
lean_object* v___x_905_; 
v___x_905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__33));
v___y_862_ = v___x_905_;
goto v___jp_861_;
}
case 34:
{
lean_object* v___x_906_; 
v___x_906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__34));
v___y_862_ = v___x_906_;
goto v___jp_861_;
}
case 35:
{
lean_object* v___x_907_; 
v___x_907_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__35));
v___y_862_ = v___x_907_;
goto v___jp_861_;
}
case 36:
{
lean_object* v___x_908_; 
v___x_908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__36));
v___y_862_ = v___x_908_;
goto v___jp_861_;
}
case 37:
{
lean_object* v___x_909_; 
v___x_909_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__37));
v___y_862_ = v___x_909_;
goto v___jp_861_;
}
case 38:
{
lean_object* v___x_910_; 
v___x_910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__38));
v___y_862_ = v___x_910_;
goto v___jp_861_;
}
default: 
{
lean_object* v___x_911_; 
v___x_911_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__39));
v___y_862_ = v___x_911_;
goto v___jp_861_;
}
}
v___jp_861_:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; size_t v___x_867_; size_t v___x_868_; lean_object* v___x_869_; 
lean_inc_ref(v___y_862_);
v___x_863_ = lean_string_to_utf8(v___y_862_);
v___x_864_ = lean_byte_array_size(v___x_863_);
v___x_865_ = l_ByteArray_toByteSlice(v___x_863_, v___x_859_, v___x_864_);
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
lean_ctor_set(v___x_866_, 1, v_v_858_);
v___x_867_ = ((size_t)1ULL);
v___x_868_ = lean_usize_add(v_i_855_, v___x_867_);
v___x_869_ = lean_array_uset(v_bs_x27_860_, v_i_855_, v___x_866_);
v_i_855_ = v___x_868_;
v_bs_856_ = v___x_869_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___boxed(lean_object* v_sz_912_, lean_object* v_i_913_, lean_object* v_bs_914_){
_start:
{
size_t v_sz_boxed_915_; size_t v_i_boxed_916_; lean_object* v_res_917_; 
v_sz_boxed_915_ = lean_unbox_usize(v_sz_912_);
lean_dec(v_sz_912_);
v_i_boxed_916_ = lean_unbox_usize(v_i_913_);
lean_dec(v_i_913_);
v_res_917_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0(v_sz_boxed_915_, v_i_boxed_916_, v_bs_914_);
return v_res_917_;
}
}
static size_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods___closed__0(void){
_start:
{
lean_object* v___x_918_; size_t v_sz_919_; 
v___x_918_ = l_Std_Http_Method_all;
v_sz_919_ = lean_array_size(v___x_918_);
return v_sz_919_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods___closed__1(void){
_start:
{
lean_object* v___x_920_; size_t v___x_921_; size_t v_sz_922_; lean_object* v___x_923_; 
v___x_920_ = l_Std_Http_Method_all;
v___x_921_ = ((size_t)0ULL);
v_sz_922_ = lean_usize_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods___closed__0);
v___x_923_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0(v_sz_922_, v___x_921_, v___x_920_);
return v___x_923_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods(void){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods___closed__1);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0(lean_object* v___x_928_, lean_object* v_as_929_, size_t v_sz_930_, size_t v_i_931_, lean_object* v_b_932_){
_start:
{
lean_object* v_a_934_; uint8_t v___x_938_; 
v___x_938_ = lean_usize_dec_lt(v_i_931_, v_sz_930_);
if (v___x_938_ == 0)
{
lean_inc_ref(v_b_932_);
return v_b_932_;
}
else
{
lean_object* v_a_939_; lean_object* v_fst_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
v_a_939_ = lean_array_uget_borrowed(v_as_929_, v_i_931_);
v_fst_940_ = lean_ctor_get(v_a_939_, 0);
v___x_941_ = lean_box(0);
v___x_942_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___closed__0));
v___x_943_ = l_ByteSlice_size(v_fst_940_);
v___x_944_ = l_ByteSlice_size(v___x_928_);
v___x_945_ = lean_nat_dec_eq(v___x_943_, v___x_944_);
lean_dec(v___x_944_);
lean_dec(v___x_943_);
if (v___x_945_ == 0)
{
v_a_934_ = v___x_942_;
goto v___jp_933_;
}
else
{
uint8_t v___x_946_; 
v___x_946_ = lean_byteslice_beq(v_fst_940_, v___x_928_);
if (v___x_946_ == 0)
{
v_a_934_ = v___x_942_;
goto v___jp_933_;
}
else
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
lean_inc(v_a_939_);
v___x_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_947_, 0, v_a_939_);
v___x_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v___x_941_);
return v___x_949_;
}
}
}
v___jp_933_:
{
size_t v___x_935_; size_t v___x_936_; 
v___x_935_ = ((size_t)1ULL);
v___x_936_ = lean_usize_add(v_i_931_, v___x_935_);
v_i_931_ = v___x_936_;
v_b_932_ = v_a_934_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___boxed(lean_object* v___x_950_, lean_object* v_as_951_, lean_object* v_sz_952_, lean_object* v_i_953_, lean_object* v_b_954_){
_start:
{
size_t v_sz_boxed_955_; size_t v_i_boxed_956_; lean_object* v_res_957_; 
v_sz_boxed_955_ = lean_unbox_usize(v_sz_952_);
lean_dec(v_sz_952_);
v_i_boxed_956_ = lean_unbox_usize(v_i_953_);
lean_dec(v_i_953_);
v_res_957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0(v___x_950_, v_as_951_, v_sz_boxed_955_, v_i_boxed_956_, v_b_954_);
lean_dec_ref(v_b_954_);
lean_dec_ref(v_as_951_);
lean_dec_ref(v___x_950_);
return v_res_957_;
}
}
static size_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4(void){
_start:
{
lean_object* v___x_964_; size_t v_sz_965_; 
v___x_964_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods;
v_sz_965_ = lean_array_size(v___x_964_);
return v_sz_965_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(lean_object* v_limits_966_, lean_object* v_a_967_){
_start:
{
lean_object* v___y_969_; lean_object* v_array_970_; lean_object* v_idx_971_; lean_object* v___y_984_; lean_object* v___f_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v_snd_991_; lean_object* v_snd_992_; uint8_t v___x_993_; 
v___f_987_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_988_ = lean_unsigned_to_nat(64u);
v___x_989_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_967_);
v___x_990_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_987_, v___x_988_, v___x_989_, v_a_967_);
v_snd_991_ = lean_ctor_get(v___x_990_, 1);
lean_inc(v_snd_991_);
v_snd_992_ = lean_ctor_get(v_snd_991_, 1);
v___x_993_ = lean_unbox(v_snd_992_);
if (v___x_993_ == 0)
{
lean_object* v_fst_994_; lean_object* v_fst_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1097_; 
v_fst_994_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_fst_994_);
lean_dec_ref(v___x_990_);
v_fst_995_ = lean_ctor_get(v_snd_991_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_snd_991_);
if (v_isSharedCheck_1097_ == 0)
{
lean_object* v_unused_1098_; 
v_unused_1098_ = lean_ctor_get(v_snd_991_, 1);
lean_dec(v_unused_1098_);
v___x_997_ = v_snd_991_;
v_isShared_998_ = v_isSharedCheck_1097_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_fst_995_);
lean_dec(v_snd_991_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1097_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
uint8_t v___x_999_; 
v___x_999_ = lean_nat_dec_eq(v_fst_994_, v___x_989_);
if (v___x_999_ == 0)
{
lean_object* v_array_1000_; lean_object* v_idx_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1092_; 
lean_del_object(v___x_997_);
v_array_1000_ = lean_ctor_get(v_a_967_, 0);
v_idx_1001_ = lean_ctor_get(v_a_967_, 1);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_a_967_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1003_ = v_a_967_;
v_isShared_1004_ = v_isSharedCheck_1092_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_idx_1001_);
lean_inc(v_array_1000_);
lean_dec(v_a_967_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1092_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v_lower_1009_; lean_object* v_upper_1010_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1033_; lean_object* v_lower_1059_; lean_object* v_upper_1060_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___y_1089_; uint8_t v___x_1091_; 
v___x_1086_ = lean_nat_add(v_idx_1001_, v_fst_994_);
lean_dec(v_fst_994_);
v___x_1087_ = lean_byte_array_size(v_array_1000_);
v___x_1091_ = lean_nat_dec_le(v_idx_1001_, v___x_989_);
if (v___x_1091_ == 0)
{
v___y_1089_ = v_idx_1001_;
goto v___jp_1088_;
}
else
{
lean_dec(v_idx_1001_);
v___y_1089_ = v___x_989_;
goto v___jp_1088_;
}
v___jp_1005_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1011_ = l_ByteArray_toByteSlice(v___y_1006_, v_lower_1009_, v_upper_1010_);
v___x_1012_ = l_ByteSlice_size(v___x_1011_);
lean_dec_ref(v___x_1011_);
v___x_1013_ = lean_nat_dec_eq(v___x_1012_, v___y_1008_);
lean_dec(v___x_1012_);
if (v___x_1013_ == 0)
{
lean_del_object(v___x_1003_);
v___y_984_ = v___y_1007_;
goto v___jp_983_;
}
else
{
lean_object* v_array_1014_; lean_object* v_idx_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v_array_1014_ = lean_ctor_get(v___y_1007_, 0);
v_idx_1015_ = lean_ctor_get(v___y_1007_, 1);
v___x_1016_ = lean_byte_array_size(v_array_1014_);
v___x_1017_ = lean_nat_dec_lt(v_idx_1015_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_inc(v_idx_1015_);
lean_inc_ref(v_array_1014_);
lean_del_object(v___x_1003_);
v___y_969_ = v___y_1007_;
v_array_970_ = v_array_1014_;
v_idx_971_ = v_idx_1015_;
goto v___jp_968_;
}
else
{
uint8_t v___x_1018_; uint8_t v___x_1019_; 
v___x_1018_ = lean_byte_array_fget(v_array_1014_, v_idx_1015_);
v___x_1019_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0(v___x_1018_);
if (v___x_1019_ == 0)
{
lean_inc(v_idx_1015_);
lean_inc_ref(v_array_1014_);
lean_del_object(v___x_1003_);
v___y_969_ = v___y_1007_;
v_array_970_ = v_array_1014_;
v_idx_971_ = v_idx_1015_;
goto v___jp_968_;
}
else
{
lean_object* v___x_1020_; lean_object* v___x_1022_; 
v___x_1020_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3));
if (v_isShared_1004_ == 0)
{
lean_ctor_set_tag(v___x_1003_, 1);
lean_ctor_set(v___x_1003_, 1, v___x_1020_);
lean_ctor_set(v___x_1003_, 0, v___y_1007_);
v___x_1022_ = v___x_1003_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___y_1007_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v___x_1020_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
v___jp_1024_:
{
uint8_t v___x_1031_; 
v___x_1031_ = lean_nat_dec_le(v___y_1027_, v___y_1029_);
if (v___x_1031_ == 0)
{
lean_dec(v___y_1027_);
v___y_1006_ = v___y_1025_;
v___y_1007_ = v___y_1026_;
v___y_1008_ = v___y_1028_;
v_lower_1009_ = v___y_1030_;
v_upper_1010_ = v___y_1029_;
goto v___jp_1005_;
}
else
{
lean_dec(v___y_1029_);
v___y_1006_ = v___y_1025_;
v___y_1007_ = v___y_1026_;
v___y_1008_ = v___y_1028_;
v_lower_1009_ = v___y_1030_;
v_upper_1010_ = v___y_1027_;
goto v___jp_1005_;
}
}
v___jp_1032_:
{
lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_1034_ = l_ByteSlice_size(v___y_1033_);
lean_dec_ref(v___y_1033_);
v___x_1035_ = lean_nat_dec_eq(v___x_1034_, v___x_988_);
lean_dec(v___x_1034_);
if (v___x_1035_ == 0)
{
lean_del_object(v___x_1003_);
v___y_984_ = v_fst_995_;
goto v___jp_983_;
}
else
{
lean_object* v_maxStartLineLength_1036_; lean_object* v___x_1037_; lean_object* v_snd_1038_; lean_object* v_snd_1039_; uint8_t v___x_1040_; 
v_maxStartLineLength_1036_ = lean_ctor_get(v_limits_966_, 5);
lean_inc(v_fst_995_);
v___x_1037_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_987_, v_maxStartLineLength_1036_, v___x_989_, v_fst_995_);
v_snd_1038_ = lean_ctor_get(v___x_1037_, 1);
lean_inc(v_snd_1038_);
v_snd_1039_ = lean_ctor_get(v_snd_1038_, 1);
v___x_1040_ = lean_unbox(v_snd_1039_);
if (v___x_1040_ == 0)
{
lean_object* v_fst_1041_; lean_object* v_fst_1042_; lean_object* v_array_1043_; lean_object* v_idx_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; uint8_t v___x_1047_; 
v_fst_1041_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_fst_1041_);
lean_dec_ref(v___x_1037_);
v_fst_1042_ = lean_ctor_get(v_snd_1038_, 0);
lean_inc(v_fst_1042_);
lean_dec(v_snd_1038_);
v_array_1043_ = lean_ctor_get(v_fst_995_, 0);
lean_inc_ref(v_array_1043_);
v_idx_1044_ = lean_ctor_get(v_fst_995_, 1);
lean_inc(v_idx_1044_);
lean_dec(v_fst_995_);
v___x_1045_ = lean_nat_add(v_idx_1044_, v_fst_1041_);
lean_dec(v_fst_1041_);
v___x_1046_ = lean_byte_array_size(v_array_1043_);
v___x_1047_ = lean_nat_dec_le(v_idx_1044_, v___x_989_);
if (v___x_1047_ == 0)
{
v___y_1025_ = v_array_1043_;
v___y_1026_ = v_fst_1042_;
v___y_1027_ = v___x_1045_;
v___y_1028_ = v_maxStartLineLength_1036_;
v___y_1029_ = v___x_1046_;
v___y_1030_ = v_idx_1044_;
goto v___jp_1024_;
}
else
{
lean_dec(v_idx_1044_);
v___y_1025_ = v_array_1043_;
v___y_1026_ = v_fst_1042_;
v___y_1027_ = v___x_1045_;
v___y_1028_ = v_maxStartLineLength_1036_;
v___y_1029_ = v___x_1046_;
v___y_1030_ = v___x_989_;
goto v___jp_1024_;
}
}
else
{
lean_object* v_fst_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1056_; 
lean_dec_ref(v___x_1037_);
lean_del_object(v___x_1003_);
lean_dec(v_fst_995_);
v_fst_1048_ = lean_ctor_get(v_snd_1038_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_snd_1038_);
if (v_isSharedCheck_1056_ == 0)
{
lean_object* v_unused_1057_; 
v_unused_1057_ = lean_ctor_get(v_snd_1038_, 1);
lean_dec(v_unused_1057_);
v___x_1050_ = v_snd_1038_;
v_isShared_1051_ = v_isSharedCheck_1056_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_fst_1048_);
lean_dec(v_snd_1038_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1056_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1052_ = lean_box(0);
if (v_isShared_1051_ == 0)
{
lean_ctor_set_tag(v___x_1050_, 1);
lean_ctor_set(v___x_1050_, 1, v___x_1052_);
v___x_1054_ = v___x_1050_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_fst_1048_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v___x_1052_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
}
v___jp_1058_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; size_t v_sz_1064_; size_t v___x_1065_; lean_object* v___x_1066_; lean_object* v_fst_1067_; 
v___x_1061_ = l_ByteArray_toByteSlice(v_array_1000_, v_lower_1059_, v_upper_1060_);
v___x_1062_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods;
v___x_1063_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___closed__0));
v_sz_1064_ = lean_usize_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4);
v___x_1065_ = ((size_t)0ULL);
v___x_1066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0(v___x_1061_, v___x_1062_, v_sz_1064_, v___x_1065_, v___x_1063_);
v_fst_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_fst_1067_);
lean_dec_ref(v___x_1066_);
if (lean_obj_tag(v_fst_1067_) == 0)
{
v___y_1033_ = v___x_1061_;
goto v___jp_1032_;
}
else
{
lean_object* v_val_1068_; 
v_val_1068_ = lean_ctor_get(v_fst_1067_, 0);
lean_inc(v_val_1068_);
lean_dec_ref_known(v_fst_1067_, 1);
if (lean_obj_tag(v_val_1068_) == 0)
{
v___y_1033_ = v___x_1061_;
goto v___jp_1032_;
}
else
{
lean_object* v_val_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1085_; 
lean_dec_ref(v___x_1061_);
lean_del_object(v___x_1003_);
v_val_1069_ = lean_ctor_get(v_val_1068_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_val_1068_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1071_ = v_val_1068_;
v_isShared_1072_ = v_isSharedCheck_1085_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_val_1069_);
lean_dec(v_val_1068_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1085_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v_snd_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1083_; 
v_snd_1073_ = lean_ctor_get(v_val_1069_, 1);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_val_1069_);
if (v_isSharedCheck_1083_ == 0)
{
lean_object* v_unused_1084_; 
v_unused_1084_ = lean_ctor_get(v_val_1069_, 0);
lean_dec(v_unused_1084_);
v___x_1075_ = v_val_1069_;
v_isShared_1076_ = v_isSharedCheck_1083_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_snd_1073_);
lean_dec(v_val_1069_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1083_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 0, v_snd_1073_);
v___x_1078_ = v___x_1071_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_snd_1073_);
v___x_1078_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1080_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 1, v___x_1078_);
lean_ctor_set(v___x_1075_, 0, v_fst_995_);
v___x_1080_ = v___x_1075_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_fst_995_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
}
}
v___jp_1088_:
{
uint8_t v___x_1090_; 
v___x_1090_ = lean_nat_dec_le(v___x_1086_, v___x_1087_);
if (v___x_1090_ == 0)
{
lean_dec(v___x_1086_);
v_lower_1059_ = v___y_1089_;
v_upper_1060_ = v___x_1087_;
goto v___jp_1058_;
}
else
{
v_lower_1059_ = v___y_1089_;
v_upper_1060_ = v___x_1086_;
goto v___jp_1058_;
}
}
}
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1095_; 
lean_dec(v_fst_995_);
lean_dec(v_fst_994_);
v___x_1093_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_998_ == 0)
{
lean_ctor_set_tag(v___x_997_, 1);
lean_ctor_set(v___x_997_, 1, v___x_1093_);
lean_ctor_set(v___x_997_, 0, v_a_967_);
v___x_1095_ = v___x_997_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_967_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
else
{
lean_object* v_fst_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1107_; 
lean_dec_ref(v___x_990_);
lean_dec_ref(v_a_967_);
v_fst_1099_ = lean_ctor_get(v_snd_991_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_snd_991_);
if (v_isSharedCheck_1107_ == 0)
{
lean_object* v_unused_1108_; 
v_unused_1108_ = lean_ctor_get(v_snd_991_, 1);
lean_dec(v_unused_1108_);
v___x_1101_ = v_snd_991_;
v_isShared_1102_ = v_isSharedCheck_1107_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_fst_1099_);
lean_dec(v_snd_991_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1107_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1103_ = lean_box(0);
if (v_isShared_1102_ == 0)
{
lean_ctor_set_tag(v___x_1101_, 1);
lean_ctor_set(v___x_1101_, 1, v___x_1103_);
v___x_1105_ = v___x_1101_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_fst_1099_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
v___jp_968_:
{
lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_972_ = lean_byte_array_size(v_array_970_);
v___x_973_ = lean_nat_dec_lt(v_idx_971_, v___x_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; lean_object* v___x_975_; 
lean_dec(v_idx_971_);
lean_dec_ref(v_array_970_);
v___x_974_ = lean_box(0);
v___x_975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_975_, 0, v___y_969_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
return v___x_975_;
}
else
{
uint8_t v___x_976_; uint8_t v___x_977_; uint8_t v___x_978_; 
v___x_976_ = lean_byte_array_fget(v_array_970_, v_idx_971_);
lean_dec(v_idx_971_);
lean_dec_ref(v_array_970_);
v___x_977_ = 32;
v___x_978_ = lean_uint8_dec_eq(v___x_976_, v___x_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__1));
v___x_980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_980_, 0, v___y_969_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
return v___x_980_;
}
else
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_box(0);
v___x_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_982_, 0, v___y_969_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
return v___x_982_;
}
}
}
v___jp_983_:
{
lean_object* v_array_985_; lean_object* v_idx_986_; 
v_array_985_ = lean_ctor_get(v___y_984_, 0);
lean_inc_ref(v_array_985_);
v_idx_986_ = lean_ctor_get(v___y_984_, 1);
lean_inc(v_idx_986_);
v___y_969_ = v___y_984_;
v_array_970_ = v_array_985_;
v_idx_971_ = v_idx_986_;
goto v___jp_968_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___boxed(lean_object* v_limits_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(v_limits_1109_, v_a_1110_);
lean_dec_ref(v_limits_1109_);
return v_res_1111_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(uint8_t v___y_1112_){
_start:
{
uint8_t v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = 48;
v___x_1169_ = lean_uint8_dec_le(v___x_1168_, v___y_1112_);
if (v___x_1169_ == 0)
{
goto v___jp_1163_;
}
else
{
uint8_t v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = 57;
v___x_1171_ = lean_uint8_dec_le(v___y_1112_, v___x_1170_);
if (v___x_1171_ == 0)
{
goto v___jp_1163_;
}
else
{
return v___x_1171_;
}
}
v___jp_1113_:
{
uint8_t v___x_1114_; uint8_t v___x_1115_; 
v___x_1114_ = 45;
v___x_1115_ = lean_uint8_dec_eq(v___y_1112_, v___x_1114_);
if (v___x_1115_ == 0)
{
uint8_t v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = 46;
v___x_1117_ = lean_uint8_dec_eq(v___y_1112_, v___x_1116_);
if (v___x_1117_ == 0)
{
uint8_t v___x_1118_; uint8_t v___x_1119_; 
v___x_1118_ = 95;
v___x_1119_ = lean_uint8_dec_eq(v___y_1112_, v___x_1118_);
if (v___x_1119_ == 0)
{
uint8_t v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = 126;
v___x_1121_ = lean_uint8_dec_eq(v___y_1112_, v___x_1120_);
if (v___x_1121_ == 0)
{
uint8_t v___x_1122_; uint8_t v___x_1123_; 
v___x_1122_ = 33;
v___x_1123_ = lean_uint8_dec_eq(v___y_1112_, v___x_1122_);
if (v___x_1123_ == 0)
{
uint8_t v___x_1124_; uint8_t v___x_1125_; 
v___x_1124_ = 36;
v___x_1125_ = lean_uint8_dec_eq(v___y_1112_, v___x_1124_);
if (v___x_1125_ == 0)
{
uint8_t v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = 38;
v___x_1127_ = lean_uint8_dec_eq(v___y_1112_, v___x_1126_);
if (v___x_1127_ == 0)
{
uint8_t v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = 39;
v___x_1129_ = lean_uint8_dec_eq(v___y_1112_, v___x_1128_);
if (v___x_1129_ == 0)
{
uint8_t v___x_1130_; uint8_t v___x_1131_; 
v___x_1130_ = 40;
v___x_1131_ = lean_uint8_dec_eq(v___y_1112_, v___x_1130_);
if (v___x_1131_ == 0)
{
uint8_t v___x_1132_; uint8_t v___x_1133_; 
v___x_1132_ = 41;
v___x_1133_ = lean_uint8_dec_eq(v___y_1112_, v___x_1132_);
if (v___x_1133_ == 0)
{
uint8_t v___x_1134_; uint8_t v___x_1135_; 
v___x_1134_ = 42;
v___x_1135_ = lean_uint8_dec_eq(v___y_1112_, v___x_1134_);
if (v___x_1135_ == 0)
{
uint8_t v___x_1136_; uint8_t v___x_1137_; 
v___x_1136_ = 43;
v___x_1137_ = lean_uint8_dec_eq(v___y_1112_, v___x_1136_);
if (v___x_1137_ == 0)
{
uint8_t v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = 44;
v___x_1139_ = lean_uint8_dec_eq(v___y_1112_, v___x_1138_);
if (v___x_1139_ == 0)
{
uint8_t v___x_1140_; uint8_t v___x_1141_; 
v___x_1140_ = 59;
v___x_1141_ = lean_uint8_dec_eq(v___y_1112_, v___x_1140_);
if (v___x_1141_ == 0)
{
uint8_t v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = 61;
v___x_1143_ = lean_uint8_dec_eq(v___y_1112_, v___x_1142_);
if (v___x_1143_ == 0)
{
uint8_t v___x_1144_; uint8_t v___x_1145_; 
v___x_1144_ = 58;
v___x_1145_ = lean_uint8_dec_eq(v___y_1112_, v___x_1144_);
if (v___x_1145_ == 0)
{
uint8_t v___x_1146_; uint8_t v___x_1147_; 
v___x_1146_ = 64;
v___x_1147_ = lean_uint8_dec_eq(v___y_1112_, v___x_1146_);
if (v___x_1147_ == 0)
{
uint8_t v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = 47;
v___x_1149_ = lean_uint8_dec_eq(v___y_1112_, v___x_1148_);
if (v___x_1149_ == 0)
{
uint8_t v___x_1150_; uint8_t v___x_1151_; 
v___x_1150_ = 63;
v___x_1151_ = lean_uint8_dec_eq(v___y_1112_, v___x_1150_);
if (v___x_1151_ == 0)
{
uint8_t v___x_1152_; uint8_t v___x_1153_; 
v___x_1152_ = 37;
v___x_1153_ = lean_uint8_dec_eq(v___y_1112_, v___x_1152_);
if (v___x_1153_ == 0)
{
uint8_t v___x_1154_; uint8_t v___x_1155_; 
v___x_1154_ = 91;
v___x_1155_ = lean_uint8_dec_eq(v___y_1112_, v___x_1154_);
if (v___x_1155_ == 0)
{
uint8_t v___x_1156_; uint8_t v___x_1157_; 
v___x_1156_ = 93;
v___x_1157_ = lean_uint8_dec_eq(v___y_1112_, v___x_1156_);
return v___x_1157_;
}
else
{
return v___x_1155_;
}
}
else
{
return v___x_1153_;
}
}
else
{
return v___x_1151_;
}
}
else
{
return v___x_1149_;
}
}
else
{
return v___x_1147_;
}
}
else
{
return v___x_1145_;
}
}
else
{
return v___x_1143_;
}
}
else
{
return v___x_1141_;
}
}
else
{
return v___x_1139_;
}
}
else
{
return v___x_1137_;
}
}
else
{
return v___x_1135_;
}
}
else
{
return v___x_1133_;
}
}
else
{
return v___x_1131_;
}
}
else
{
return v___x_1129_;
}
}
else
{
return v___x_1127_;
}
}
else
{
return v___x_1125_;
}
}
else
{
return v___x_1123_;
}
}
else
{
return v___x_1121_;
}
}
else
{
return v___x_1119_;
}
}
else
{
return v___x_1117_;
}
}
else
{
return v___x_1115_;
}
}
v___jp_1158_:
{
uint8_t v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = 65;
v___x_1160_ = lean_uint8_dec_le(v___x_1159_, v___y_1112_);
if (v___x_1160_ == 0)
{
goto v___jp_1113_;
}
else
{
uint8_t v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = 90;
v___x_1162_ = lean_uint8_dec_le(v___y_1112_, v___x_1161_);
if (v___x_1162_ == 0)
{
goto v___jp_1113_;
}
else
{
return v___x_1162_;
}
}
}
v___jp_1163_:
{
uint8_t v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = 97;
v___x_1165_ = lean_uint8_dec_le(v___x_1164_, v___y_1112_);
if (v___x_1165_ == 0)
{
goto v___jp_1158_;
}
else
{
uint8_t v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = 122;
v___x_1167_ = lean_uint8_dec_le(v___y_1112_, v___x_1166_);
if (v___x_1167_ == 0)
{
goto v___jp_1158_;
}
else
{
return v___x_1167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0___boxed(lean_object* v___y_1172_){
_start:
{
uint8_t v___y_1870__boxed_1173_; uint8_t v_res_1174_; lean_object* v_r_1175_; 
v___y_1870__boxed_1173_ = lean_unbox(v___y_1172_);
v_res_1174_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(v___y_1870__boxed_1173_);
v_r_1175_ = lean_box(v_res_1174_);
return v_r_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(lean_object* v_limits_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v_pos_1183_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v_maxUriLength_1191_; lean_object* v___f_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v_snd_1195_; lean_object* v_fst_1196_; lean_object* v_fst_1197_; lean_object* v_snd_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1291_; 
v_maxUriLength_1191_ = lean_ctor_get(v_limits_1180_, 4);
v___f_1192_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__2));
v___x_1193_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1181_);
v___x_1194_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1192_, v_maxUriLength_1191_, v___x_1193_, v_a_1181_);
v_snd_1195_ = lean_ctor_get(v___x_1194_, 1);
lean_inc(v_snd_1195_);
v_fst_1196_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_fst_1196_);
lean_dec_ref(v___x_1194_);
v_fst_1197_ = lean_ctor_get(v_snd_1195_, 0);
v_snd_1198_ = lean_ctor_get(v_snd_1195_, 1);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_snd_1195_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1200_ = v_snd_1195_;
v_isShared_1201_ = v_isSharedCheck_1291_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_snd_1198_);
lean_inc(v_fst_1197_);
lean_dec(v_snd_1195_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1291_;
goto v_resetjp_1199_;
}
v___jp_1182_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__1));
v___x_1185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1185_, 0, v_pos_1183_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
return v___x_1185_;
}
v___jp_1186_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = l_ByteSlice_toByteArray(v___y_1187_);
v___x_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___y_1188_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
return v___x_1190_;
}
v_resetjp_1199_:
{
lean_object* v___y_1203_; uint8_t v___y_1204_; lean_object* v___y_1250_; uint8_t v___y_1251_; lean_object* v___y_1257_; uint8_t v___y_1258_; uint8_t v___x_1263_; 
v___x_1263_ = lean_unbox(v_snd_1198_);
lean_dec(v_snd_1198_);
if (v___x_1263_ == 0)
{
lean_object* v_array_1264_; lean_object* v_idx_1265_; lean_object* v_lower_1267_; lean_object* v_upper_1268_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___y_1284_; uint8_t v___x_1286_; 
lean_del_object(v___x_1200_);
v_array_1264_ = lean_ctor_get(v_a_1181_, 0);
lean_inc_ref(v_array_1264_);
v_idx_1265_ = lean_ctor_get(v_a_1181_, 1);
lean_inc(v_idx_1265_);
lean_dec_ref(v_a_1181_);
v___x_1281_ = lean_nat_add(v_idx_1265_, v_fst_1196_);
lean_dec(v_fst_1196_);
v___x_1282_ = lean_byte_array_size(v_array_1264_);
v___x_1286_ = lean_nat_dec_le(v_idx_1265_, v___x_1193_);
if (v___x_1286_ == 0)
{
v___y_1284_ = v_idx_1265_;
goto v___jp_1283_;
}
else
{
lean_dec(v_idx_1265_);
v___y_1284_ = v___x_1193_;
goto v___jp_1283_;
}
v___jp_1266_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1269_ = l_ByteArray_toByteSlice(v_array_1264_, v_lower_1267_, v_upper_1268_);
v___x_1270_ = l_ByteSlice_size(v___x_1269_);
v___x_1271_ = lean_nat_dec_eq(v___x_1270_, v_maxUriLength_1191_);
lean_dec(v___x_1270_);
if (v___x_1271_ == 0)
{
v___y_1187_ = v___x_1269_;
v___y_1188_ = v_fst_1197_;
goto v___jp_1186_;
}
else
{
lean_object* v_array_1272_; lean_object* v_idx_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v_array_1272_ = lean_ctor_get(v_fst_1197_, 0);
v_idx_1273_ = lean_ctor_get(v_fst_1197_, 1);
v___x_1274_ = lean_byte_array_size(v_array_1272_);
v___x_1275_ = lean_nat_dec_lt(v_idx_1273_, v___x_1274_);
if (v___x_1275_ == 0)
{
v___y_1187_ = v___x_1269_;
v___y_1188_ = v_fst_1197_;
goto v___jp_1186_;
}
else
{
uint8_t v___x_1276_; uint8_t v___x_1277_; uint8_t v___x_1278_; 
v___x_1276_ = lean_byte_array_fget(v_array_1272_, v_idx_1273_);
v___x_1277_ = 48;
v___x_1278_ = lean_uint8_dec_le(v___x_1277_, v___x_1276_);
if (v___x_1278_ == 0)
{
v___y_1257_ = v___x_1269_;
v___y_1258_ = v___x_1276_;
goto v___jp_1256_;
}
else
{
uint8_t v___x_1279_; uint8_t v___x_1280_; 
v___x_1279_ = 57;
v___x_1280_ = lean_uint8_dec_le(v___x_1276_, v___x_1279_);
if (v___x_1280_ == 0)
{
v___y_1257_ = v___x_1269_;
v___y_1258_ = v___x_1276_;
goto v___jp_1256_;
}
else
{
lean_dec_ref(v___x_1269_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
}
}
}
v___jp_1283_:
{
uint8_t v___x_1285_; 
v___x_1285_ = lean_nat_dec_le(v___x_1281_, v___x_1282_);
if (v___x_1285_ == 0)
{
lean_dec(v___x_1281_);
v_lower_1267_ = v___y_1284_;
v_upper_1268_ = v___x_1282_;
goto v___jp_1266_;
}
else
{
v_lower_1267_ = v___y_1284_;
v_upper_1268_ = v___x_1281_;
goto v___jp_1266_;
}
}
}
else
{
lean_object* v___x_1287_; lean_object* v___x_1289_; 
lean_dec(v_fst_1196_);
lean_dec_ref(v_a_1181_);
v___x_1287_ = lean_box(0);
if (v_isShared_1201_ == 0)
{
lean_ctor_set_tag(v___x_1200_, 1);
lean_ctor_set(v___x_1200_, 1, v___x_1287_);
v___x_1289_ = v___x_1200_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_fst_1197_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
v___jp_1202_:
{
uint8_t v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = 45;
v___x_1206_ = lean_uint8_dec_eq(v___y_1204_, v___x_1205_);
if (v___x_1206_ == 0)
{
uint8_t v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = 46;
v___x_1208_ = lean_uint8_dec_eq(v___y_1204_, v___x_1207_);
if (v___x_1208_ == 0)
{
uint8_t v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = 95;
v___x_1210_ = lean_uint8_dec_eq(v___y_1204_, v___x_1209_);
if (v___x_1210_ == 0)
{
uint8_t v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = 126;
v___x_1212_ = lean_uint8_dec_eq(v___y_1204_, v___x_1211_);
if (v___x_1212_ == 0)
{
uint8_t v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = 33;
v___x_1214_ = lean_uint8_dec_eq(v___y_1204_, v___x_1213_);
if (v___x_1214_ == 0)
{
uint8_t v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = 36;
v___x_1216_ = lean_uint8_dec_eq(v___y_1204_, v___x_1215_);
if (v___x_1216_ == 0)
{
uint8_t v___x_1217_; uint8_t v___x_1218_; 
v___x_1217_ = 38;
v___x_1218_ = lean_uint8_dec_eq(v___y_1204_, v___x_1217_);
if (v___x_1218_ == 0)
{
uint8_t v___x_1219_; uint8_t v___x_1220_; 
v___x_1219_ = 39;
v___x_1220_ = lean_uint8_dec_eq(v___y_1204_, v___x_1219_);
if (v___x_1220_ == 0)
{
uint8_t v___x_1221_; uint8_t v___x_1222_; 
v___x_1221_ = 40;
v___x_1222_ = lean_uint8_dec_eq(v___y_1204_, v___x_1221_);
if (v___x_1222_ == 0)
{
uint8_t v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = 41;
v___x_1224_ = lean_uint8_dec_eq(v___y_1204_, v___x_1223_);
if (v___x_1224_ == 0)
{
uint8_t v___x_1225_; uint8_t v___x_1226_; 
v___x_1225_ = 42;
v___x_1226_ = lean_uint8_dec_eq(v___y_1204_, v___x_1225_);
if (v___x_1226_ == 0)
{
uint8_t v___x_1227_; uint8_t v___x_1228_; 
v___x_1227_ = 43;
v___x_1228_ = lean_uint8_dec_eq(v___y_1204_, v___x_1227_);
if (v___x_1228_ == 0)
{
uint8_t v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = 44;
v___x_1230_ = lean_uint8_dec_eq(v___y_1204_, v___x_1229_);
if (v___x_1230_ == 0)
{
uint8_t v___x_1231_; uint8_t v___x_1232_; 
v___x_1231_ = 59;
v___x_1232_ = lean_uint8_dec_eq(v___y_1204_, v___x_1231_);
if (v___x_1232_ == 0)
{
uint8_t v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = 61;
v___x_1234_ = lean_uint8_dec_eq(v___y_1204_, v___x_1233_);
if (v___x_1234_ == 0)
{
uint8_t v___x_1235_; uint8_t v___x_1236_; 
v___x_1235_ = 58;
v___x_1236_ = lean_uint8_dec_eq(v___y_1204_, v___x_1235_);
if (v___x_1236_ == 0)
{
uint8_t v___x_1237_; uint8_t v___x_1238_; 
v___x_1237_ = 64;
v___x_1238_ = lean_uint8_dec_eq(v___y_1204_, v___x_1237_);
if (v___x_1238_ == 0)
{
uint8_t v___x_1239_; uint8_t v___x_1240_; 
v___x_1239_ = 47;
v___x_1240_ = lean_uint8_dec_eq(v___y_1204_, v___x_1239_);
if (v___x_1240_ == 0)
{
uint8_t v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = 63;
v___x_1242_ = lean_uint8_dec_eq(v___y_1204_, v___x_1241_);
if (v___x_1242_ == 0)
{
uint8_t v___x_1243_; uint8_t v___x_1244_; 
v___x_1243_ = 37;
v___x_1244_ = lean_uint8_dec_eq(v___y_1204_, v___x_1243_);
if (v___x_1244_ == 0)
{
uint8_t v___x_1245_; uint8_t v___x_1246_; 
v___x_1245_ = 91;
v___x_1246_ = lean_uint8_dec_eq(v___y_1204_, v___x_1245_);
if (v___x_1246_ == 0)
{
uint8_t v___x_1247_; uint8_t v___x_1248_; 
v___x_1247_ = 93;
v___x_1248_ = lean_uint8_dec_eq(v___y_1204_, v___x_1247_);
if (v___x_1248_ == 0)
{
v___y_1187_ = v___y_1203_;
v___y_1188_ = v_fst_1197_;
goto v___jp_1186_;
}
else
{
lean_dec_ref(v___y_1203_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
else
{
lean_dec_ref(v___y_1203_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
else
{
lean_dec_ref(v___y_1203_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
else
{
lean_dec_ref(v___y_1203_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
else
{
lean_dec_ref(v___y_1203_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
else
{
lean_dec_ref(v___y_1203_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
else
{
lean_dec_ref(v___y_1203_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
else
{
lean_dec_ref(v___y_1203_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
else
{
lean_dec_ref(v___y_1203_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
else
{
lean_dec_ref(v___y_1203_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
else
{
lean_dec_ref(v___y_1203_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
else
{
lean_dec_ref(v___y_1203_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
else
{
lean_dec_ref(v___y_1203_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
else
{
lean_dec_ref(v___y_1203_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
else
{
lean_dec_ref(v___y_1203_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
else
{
lean_dec_ref(v___y_1203_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
else
{
lean_dec_ref(v___y_1203_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
else
{
lean_dec_ref(v___y_1203_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
else
{
lean_dec_ref(v___y_1203_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
else
{
lean_dec_ref(v___y_1203_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
else
{
lean_dec_ref(v___y_1203_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
else
{
lean_dec_ref(v___y_1203_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
v___jp_1249_:
{
uint8_t v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = 65;
v___x_1253_ = lean_uint8_dec_le(v___x_1252_, v___y_1251_);
if (v___x_1253_ == 0)
{
v___y_1203_ = v___y_1250_;
v___y_1204_ = v___y_1251_;
goto v___jp_1202_;
}
else
{
uint8_t v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = 90;
v___x_1255_ = lean_uint8_dec_le(v___y_1251_, v___x_1254_);
if (v___x_1255_ == 0)
{
v___y_1203_ = v___y_1250_;
v___y_1204_ = v___y_1251_;
goto v___jp_1202_;
}
else
{
lean_dec_ref(v___y_1250_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
}
v___jp_1256_:
{
uint8_t v___x_1259_; uint8_t v___x_1260_; 
v___x_1259_ = 97;
v___x_1260_ = lean_uint8_dec_le(v___x_1259_, v___y_1258_);
if (v___x_1260_ == 0)
{
v___y_1250_ = v___y_1257_;
v___y_1251_ = v___y_1258_;
goto v___jp_1249_;
}
else
{
uint8_t v___x_1261_; uint8_t v___x_1262_; 
v___x_1261_ = 122;
v___x_1262_ = lean_uint8_dec_le(v___y_1258_, v___x_1261_);
if (v___x_1262_ == 0)
{
v___y_1250_ = v___y_1257_;
v___y_1251_ = v___y_1258_;
goto v___jp_1249_;
}
else
{
lean_dec_ref(v___y_1257_);
v_pos_1183_ = v_fst_1197_;
goto v___jp_1182_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___boxed(lean_object* v_limits_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_1292_, v_a_1293_);
lean_dec_ref(v_limits_1292_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_requestTargetConfig(lean_object* v_limits_1295_){
_start:
{
lean_object* v_maxUriLength_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v_maxUriLength_1296_ = lean_ctor_get(v_limits_1295_, 4);
v___x_1297_ = lean_unsigned_to_nat(253u);
lean_inc_n(v_maxUriLength_1296_, 8);
v___x_1298_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1298_, 0, v_maxUriLength_1296_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
lean_ctor_set(v___x_1298_, 2, v_maxUriLength_1296_);
lean_ctor_set(v___x_1298_, 3, v_maxUriLength_1296_);
lean_ctor_set(v___x_1298_, 4, v_maxUriLength_1296_);
lean_ctor_set(v___x_1298_, 5, v_maxUriLength_1296_);
lean_ctor_set(v___x_1298_, 6, v_maxUriLength_1296_);
lean_ctor_set(v___x_1298_, 7, v_maxUriLength_1296_);
lean_ctor_set(v___x_1298_, 8, v_maxUriLength_1296_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_requestTargetConfig___boxed(lean_object* v_limits_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_requestTargetConfig(v_limits_1299_);
lean_dec_ref(v_limits_1299_);
return v_res_1300_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_exceedsElementLimits(lean_object* v_limits_1301_, lean_object* v_target_1302_){
_start:
{
lean_object* v___y_1304_; lean_object* v_path_1315_; lean_object* v_query_1316_; 
switch(lean_obj_tag(v_target_1302_))
{
case 0:
{
lean_object* v_path_1322_; lean_object* v_query_1323_; 
v_path_1322_ = lean_ctor_get(v_target_1302_, 0);
v_query_1323_ = lean_ctor_get(v_target_1302_, 1);
v_path_1315_ = v_path_1322_;
v_query_1316_ = v_query_1323_;
goto v___jp_1314_;
}
case 1:
{
lean_object* v_uri_1324_; lean_object* v_path_1325_; lean_object* v_query_1326_; 
v_uri_1324_ = lean_ctor_get(v_target_1302_, 0);
v_path_1325_ = lean_ctor_get(v_uri_1324_, 2);
v_query_1326_ = lean_ctor_get(v_uri_1324_, 3);
v_path_1315_ = v_path_1325_;
v_query_1316_ = v_query_1326_;
goto v___jp_1314_;
}
default: 
{
uint8_t v___x_1327_; 
v___x_1327_ = 0;
return v___x_1327_;
}
}
v___jp_1303_:
{
lean_object* v_maxQueryParams_1305_; 
v_maxQueryParams_1305_ = lean_ctor_get(v_limits_1301_, 7);
if (lean_obj_tag(v_maxQueryParams_1305_) == 0)
{
uint8_t v___x_1306_; 
v___x_1306_ = 0;
return v___x_1306_;
}
else
{
if (lean_obj_tag(v___y_1304_) == 0)
{
lean_object* v_val_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v_val_1307_ = lean_ctor_get(v_maxQueryParams_1305_, 0);
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = lean_nat_dec_lt(v_val_1307_, v___x_1308_);
return v___x_1309_;
}
else
{
lean_object* v_val_1310_; lean_object* v_val_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v_val_1310_ = lean_ctor_get(v_maxQueryParams_1305_, 0);
v_val_1311_ = lean_ctor_get(v___y_1304_, 0);
v___x_1312_ = lean_array_get_size(v_val_1311_);
v___x_1313_ = lean_nat_dec_lt(v_val_1310_, v___x_1312_);
return v___x_1313_;
}
}
}
v___jp_1314_:
{
lean_object* v_maxPathSegments_1317_; 
v_maxPathSegments_1317_ = lean_ctor_get(v_limits_1301_, 6);
if (lean_obj_tag(v_maxPathSegments_1317_) == 0)
{
v___y_1304_ = v_query_1316_;
goto v___jp_1303_;
}
else
{
lean_object* v_val_1318_; lean_object* v_segments_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v_val_1318_ = lean_ctor_get(v_maxPathSegments_1317_, 0);
v_segments_1319_ = lean_ctor_get(v_path_1315_, 0);
v___x_1320_ = lean_array_get_size(v_segments_1319_);
v___x_1321_ = lean_nat_dec_lt(v_val_1318_, v___x_1320_);
if (v___x_1321_ == 0)
{
v___y_1304_ = v_query_1316_;
goto v___jp_1303_;
}
else
{
return v___x_1321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_exceedsElementLimits___boxed(lean_object* v_limits_1328_, lean_object* v_target_1329_){
_start:
{
uint8_t v_res_1330_; lean_object* v_r_1331_; 
v_res_1330_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_exceedsElementLimits(v_limits_1328_, v_target_1329_);
lean_dec(v_target_1329_);
lean_dec_ref(v_limits_1328_);
v_r_1331_ = lean_box(v_res_1330_);
return v_r_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0(lean_object* v___x_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_pos_1338_; lean_object* v_array_1339_; lean_object* v_idx_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; 
v_pos_1338_ = lean_ctor_get(v___x_1337_, 0);
v_array_1339_ = lean_ctor_get(v_pos_1338_, 0);
v_idx_1340_ = lean_ctor_get(v_pos_1338_, 1);
v___x_1341_ = lean_byte_array_size(v_array_1339_);
v___x_1342_ = lean_nat_dec_lt(v_idx_1340_, v___x_1341_);
if (v___x_1342_ == 0)
{
return v___x_1337_;
}
else
{
lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1350_; 
lean_inc(v_pos_1338_);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1350_ == 0)
{
lean_object* v_unused_1351_; lean_object* v_unused_1352_; 
v_unused_1351_ = lean_ctor_get(v___x_1337_, 1);
lean_dec(v_unused_1351_);
v_unused_1352_ = lean_ctor_get(v___x_1337_, 0);
lean_dec(v_unused_1352_);
v___x_1344_ = v___x_1337_;
v_isShared_1345_ = v_isSharedCheck_1350_;
goto v_resetjp_1343_;
}
else
{
lean_dec(v___x_1337_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1350_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1346_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__1));
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 1);
lean_ctor_set(v___x_1344_, 1, v___x_1346_);
v___x_1348_ = v___x_1344_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_pos_1338_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
else
{
return v___x_1337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(lean_object* v_limits_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_pos_1356_; lean_object* v_res_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1440_; 
v_pos_1356_ = lean_ctor_get(v___x_1355_, 0);
v_res_1357_ = lean_ctor_get(v___x_1355_, 1);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1359_ = v___x_1355_;
v_isShared_1360_ = v_isSharedCheck_1440_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_res_1357_);
lean_inc(v_pos_1356_);
lean_dec(v___x_1355_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1440_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v_array_1361_; lean_object* v_idx_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v_array_1361_ = lean_ctor_get(v_pos_1356_, 0);
v_idx_1362_ = lean_ctor_get(v_pos_1356_, 1);
v___x_1363_ = lean_byte_array_size(v_array_1361_);
v___x_1364_ = lean_nat_dec_lt(v_idx_1362_, v___x_1363_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
lean_dec(v_res_1357_);
v___x_1365_ = lean_box(0);
if (v_isShared_1360_ == 0)
{
lean_ctor_set_tag(v___x_1359_, 1);
lean_ctor_set(v___x_1359_, 1, v___x_1365_);
v___x_1367_ = v___x_1359_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_pos_1356_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
else
{
uint8_t v___x_1369_; uint8_t v_got_1370_; uint8_t v___x_1371_; 
v___x_1369_ = 32;
v_got_1370_ = lean_byte_array_fget(v_array_1361_, v_idx_1362_);
v___x_1371_ = lean_uint8_dec_eq(v_got_1370_, v___x_1369_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
lean_dec(v_res_1357_);
v___x_1372_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_1360_ == 0)
{
lean_ctor_set_tag(v___x_1359_, 1);
lean_ctor_set(v___x_1359_, 1, v___x_1372_);
v___x_1374_ = v___x_1359_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_pos_1356_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
else
{
lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1437_; 
lean_inc(v_idx_1362_);
lean_inc_ref(v_array_1361_);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_pos_1356_);
if (v_isSharedCheck_1437_ == 0)
{
lean_object* v_unused_1438_; lean_object* v_unused_1439_; 
v_unused_1438_ = lean_ctor_get(v_pos_1356_, 1);
lean_dec(v_unused_1438_);
v_unused_1439_ = lean_ctor_get(v_pos_1356_, 0);
lean_dec(v_unused_1439_);
v___x_1377_ = v_pos_1356_;
v_isShared_1378_ = v_isSharedCheck_1437_;
goto v_resetjp_1376_;
}
else
{
lean_dec(v_pos_1356_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1437_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1382_; 
v___x_1379_ = lean_unsigned_to_nat(1u);
v___x_1380_ = lean_nat_add(v_idx_1362_, v___x_1379_);
lean_dec(v_idx_1362_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 1, v___x_1380_);
v___x_1382_ = v___x_1377_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_array_1361_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
lean_object* v___x_1383_; lean_object* v___f_1384_; lean_object* v___x_1385_; 
v___x_1383_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_requestTargetConfig(v_limits_1353_);
v___f_1384_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0), 2, 1);
lean_closure_set(v___f_1384_, 0, v___x_1383_);
v___x_1385_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1384_, v_res_1357_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1396_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1388_ = v___x_1385_;
v_isShared_1389_ = v_isSharedCheck_1396_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1385_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1396_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
lean_ctor_set_tag(v___x_1388_, 1);
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1393_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set_tag(v___x_1359_, 1);
lean_ctor_set(v___x_1359_, 1, v___x_1391_);
lean_ctor_set(v___x_1359_, 0, v___x_1382_);
v___x_1393_ = v___x_1359_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
else
{
lean_object* v_a_1397_; uint8_t v___x_1398_; 
v_a_1397_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1397_);
lean_dec_ref_known(v___x_1385_, 1);
v___x_1398_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_exceedsElementLimits(v_limits_1353_, v_a_1397_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; 
lean_del_object(v___x_1359_);
v___x_1399_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v___x_1382_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_pos_1400_; lean_object* v_res_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v_pos_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_pos_1400_);
v_res_1401_ = lean_ctor_get(v___x_1399_, 1);
lean_inc(v_res_1401_);
lean_dec_ref_known(v___x_1399_, 2);
v___x_1402_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_1403_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_1402_, v_pos_1400_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_pos_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1412_; 
v_pos_1404_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; 
v_unused_1413_ = lean_ctor_get(v___x_1403_, 1);
lean_dec(v_unused_1413_);
v___x_1406_ = v___x_1403_;
v_isShared_1407_ = v_isSharedCheck_1412_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_pos_1404_);
lean_dec(v___x_1403_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1412_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1408_, 0, v_a_1397_);
lean_ctor_set(v___x_1408_, 1, v_res_1401_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 1, v___x_1408_);
v___x_1410_ = v___x_1406_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_pos_1404_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
else
{
lean_object* v_pos_1414_; lean_object* v_err_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec(v_res_1401_);
lean_dec(v_a_1397_);
v_pos_1414_ = lean_ctor_get(v___x_1403_, 0);
v_err_1415_ = lean_ctor_get(v___x_1403_, 1);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1403_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_err_1415_);
lean_inc(v_pos_1414_);
lean_dec(v___x_1403_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_pos_1414_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_err_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
else
{
lean_object* v_pos_1423_; lean_object* v_err_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
lean_dec(v_a_1397_);
v_pos_1423_ = lean_ctor_get(v___x_1399_, 0);
v_err_1424_ = lean_ctor_get(v___x_1399_, 1);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1399_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_err_1424_);
lean_inc(v_pos_1423_);
lean_dec(v___x_1399_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_pos_1423_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_err_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
else
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
lean_dec(v_a_1397_);
v___x_1432_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__1));
if (v_isShared_1360_ == 0)
{
lean_ctor_set_tag(v___x_1359_, 1);
lean_ctor_set(v___x_1359_, 1, v___x_1432_);
lean_ctor_set(v___x_1359_, 0, v___x_1382_);
v___x_1434_ = v___x_1359_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
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
lean_object* v_pos_1441_; lean_object* v_err_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
v_pos_1441_ = lean_ctor_get(v___x_1355_, 0);
v_err_1442_ = lean_ctor_get(v___x_1355_, 1);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1355_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_err_1442_);
lean_inc(v_pos_1441_);
lean_dec(v___x_1355_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_pos_1441_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_err_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___boxed(lean_object* v_limits_1450_, lean_object* v_a_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_1450_, v_a_1451_);
lean_dec_ref(v_limits_1450_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineParts(lean_object* v_limits_1453_, lean_object* v_a_1454_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_1453_, v_a_1454_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_pos_1456_; lean_object* v___x_1457_; 
v_pos_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_pos_1456_);
lean_dec_ref_known(v___x_1455_, 2);
v___x_1457_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(v_limits_1453_, v_pos_1456_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_pos_1458_; lean_object* v_res_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1520_; 
v_pos_1458_ = lean_ctor_get(v___x_1457_, 0);
v_res_1459_ = lean_ctor_get(v___x_1457_, 1);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1461_ = v___x_1457_;
v_isShared_1462_ = v_isSharedCheck_1520_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_res_1459_);
lean_inc(v_pos_1458_);
lean_dec(v___x_1457_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1520_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v_array_1463_; lean_object* v_idx_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
v_array_1463_ = lean_ctor_get(v_pos_1458_, 0);
v_idx_1464_ = lean_ctor_get(v_pos_1458_, 1);
v___x_1465_ = lean_byte_array_size(v_array_1463_);
v___x_1466_ = lean_nat_dec_lt(v_idx_1464_, v___x_1465_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; lean_object* v___x_1469_; 
lean_dec(v_res_1459_);
v___x_1467_ = lean_box(0);
if (v_isShared_1462_ == 0)
{
lean_ctor_set_tag(v___x_1461_, 1);
lean_ctor_set(v___x_1461_, 1, v___x_1467_);
v___x_1469_ = v___x_1461_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_pos_1458_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v___x_1467_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
else
{
uint8_t v___x_1471_; uint8_t v_got_1472_; uint8_t v___x_1473_; 
v___x_1471_ = 32;
v_got_1472_ = lean_byte_array_fget(v_array_1463_, v_idx_1464_);
v___x_1473_ = lean_uint8_dec_eq(v_got_1472_, v___x_1471_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; lean_object* v___x_1476_; 
lean_dec(v_res_1459_);
v___x_1474_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_1462_ == 0)
{
lean_ctor_set_tag(v___x_1461_, 1);
lean_ctor_set(v___x_1461_, 1, v___x_1474_);
v___x_1476_ = v___x_1461_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_pos_1458_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
else
{
lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1517_; 
lean_inc(v_idx_1464_);
lean_inc_ref(v_array_1463_);
lean_del_object(v___x_1461_);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_pos_1458_);
if (v_isSharedCheck_1517_ == 0)
{
lean_object* v_unused_1518_; lean_object* v_unused_1519_; 
v_unused_1518_ = lean_ctor_get(v_pos_1458_, 1);
lean_dec(v_unused_1518_);
v_unused_1519_ = lean_ctor_get(v_pos_1458_, 0);
lean_dec(v_unused_1519_);
v___x_1479_ = v_pos_1458_;
v_isShared_1480_ = v_isSharedCheck_1517_;
goto v_resetjp_1478_;
}
else
{
lean_dec(v_pos_1458_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1517_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1481_ = lean_unsigned_to_nat(1u);
v___x_1482_ = lean_nat_add(v_idx_1464_, v___x_1481_);
lean_dec(v_idx_1464_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 1, v___x_1482_);
v___x_1484_ = v___x_1479_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_array_1463_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1485_; 
v___x_1485_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_1453_, v___x_1484_);
if (lean_obj_tag(v___x_1485_) == 0)
{
if (lean_obj_tag(v_res_1459_) == 1)
{
lean_object* v_pos_1486_; lean_object* v_res_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1496_; 
v_pos_1486_ = lean_ctor_get(v___x_1485_, 0);
v_res_1487_ = lean_ctor_get(v___x_1485_, 1);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1489_ = v___x_1485_;
v_isShared_1490_ = v_isSharedCheck_1496_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_res_1487_);
lean_inc(v_pos_1486_);
lean_dec(v___x_1485_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1496_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v_val_1491_; lean_object* v___x_1492_; lean_object* v___x_1494_; 
v_val_1491_ = lean_ctor_get(v_res_1459_, 0);
lean_inc(v_val_1491_);
lean_dec_ref_known(v_res_1459_, 1);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v_val_1491_);
lean_ctor_set(v___x_1492_, 1, v_res_1487_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v___x_1492_);
v___x_1494_ = v___x_1489_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_pos_1486_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v___x_1492_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
else
{
lean_object* v_pos_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1505_; 
lean_dec(v_res_1459_);
v_pos_1497_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; 
v_unused_1506_ = lean_ctor_get(v___x_1485_, 1);
lean_dec(v_unused_1506_);
v___x_1499_ = v___x_1485_;
v_isShared_1500_ = v_isSharedCheck_1505_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_pos_1497_);
lean_dec(v___x_1485_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1505_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1501_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3));
if (v_isShared_1500_ == 0)
{
lean_ctor_set_tag(v___x_1499_, 1);
lean_ctor_set(v___x_1499_, 1, v___x_1501_);
v___x_1503_ = v___x_1499_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_pos_1497_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v___x_1501_);
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
else
{
lean_object* v_pos_1507_; lean_object* v_err_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_dec(v_res_1459_);
v_pos_1507_ = lean_ctor_get(v___x_1485_, 0);
v_err_1508_ = lean_ctor_get(v___x_1485_, 1);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1485_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_err_1508_);
lean_inc(v_pos_1507_);
lean_dec(v___x_1485_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_pos_1507_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_err_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
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
lean_object* v_pos_1521_; lean_object* v_err_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
v_pos_1521_ = lean_ctor_get(v___x_1457_, 0);
v_err_1522_ = lean_ctor_get(v___x_1457_, 1);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1457_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_err_1522_);
lean_inc(v_pos_1521_);
lean_dec(v___x_1457_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_pos_1521_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_err_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
else
{
lean_object* v_pos_1530_; lean_object* v_err_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
v_pos_1530_ = lean_ctor_get(v___x_1455_, 0);
v_err_1531_ = lean_ctor_get(v___x_1455_, 1);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1455_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_err_1531_);
lean_inc(v_pos_1530_);
lean_dec(v___x_1455_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_pos_1530_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_err_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineParts___boxed(lean_object* v_limits_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineParts(v_limits_1539_, v_a_1540_);
lean_dec_ref(v_limits_1539_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine(lean_object* v_limits_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineParts(v_limits_1545_, v_a_1546_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_pos_1548_; lean_object* v_res_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1593_; 
v_pos_1548_ = lean_ctor_get(v___x_1547_, 0);
v_res_1549_ = lean_ctor_get(v___x_1547_, 1);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1551_ = v___x_1547_;
v_isShared_1552_ = v_isSharedCheck_1593_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_res_1549_);
lean_inc(v_pos_1548_);
lean_dec(v___x_1547_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1593_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v_snd_1558_; lean_object* v_snd_1559_; lean_object* v_fst_1560_; lean_object* v_fst_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1591_; 
v_snd_1558_ = lean_ctor_get(v_res_1549_, 1);
lean_inc(v_snd_1558_);
v_snd_1559_ = lean_ctor_get(v_snd_1558_, 1);
lean_inc(v_snd_1559_);
v_fst_1560_ = lean_ctor_get(v_res_1549_, 0);
lean_inc(v_fst_1560_);
lean_dec(v_res_1549_);
v_fst_1561_ = lean_ctor_get(v_snd_1558_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_snd_1558_);
if (v_isSharedCheck_1591_ == 0)
{
lean_object* v_unused_1592_; 
v_unused_1592_ = lean_ctor_get(v_snd_1558_, 1);
lean_dec(v_unused_1592_);
v___x_1563_ = v_snd_1558_;
v_isShared_1564_ = v_isSharedCheck_1591_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_fst_1561_);
lean_dec(v_snd_1558_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1591_;
goto v_resetjp_1562_;
}
v___jp_1553_:
{
lean_object* v___x_1554_; lean_object* v___x_1556_; 
v___x_1554_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
if (v_isShared_1552_ == 0)
{
lean_ctor_set_tag(v___x_1551_, 1);
lean_ctor_set(v___x_1551_, 1, v___x_1554_);
v___x_1556_ = v___x_1551_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_pos_1548_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
v_resetjp_1562_:
{
lean_object* v_fst_1565_; lean_object* v_snd_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1590_; 
v_fst_1565_ = lean_ctor_get(v_snd_1559_, 0);
v_snd_1566_ = lean_ctor_get(v_snd_1559_, 1);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_snd_1559_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1568_ = v_snd_1559_;
v_isShared_1569_ = v_isSharedCheck_1590_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_snd_1566_);
lean_inc(v_fst_1565_);
lean_dec(v_snd_1559_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1590_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1570_ = lean_unsigned_to_nat(1u);
v___x_1571_ = lean_nat_dec_eq(v_fst_1565_, v___x_1570_);
lean_dec(v_fst_1565_);
if (v___x_1571_ == 0)
{
lean_del_object(v___x_1563_);
goto v___jp_1572_;
}
else
{
uint8_t v___x_1582_; 
v___x_1582_ = lean_nat_dec_le(v___x_1570_, v_snd_1566_);
if (v___x_1582_ == 0)
{
lean_del_object(v___x_1563_);
goto v___jp_1572_;
}
else
{
uint8_t v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; lean_object* v___x_1588_; 
lean_del_object(v___x_1568_);
lean_dec(v_snd_1566_);
lean_del_object(v___x_1551_);
v___x_1583_ = 1;
v___x_1584_ = l_Std_Http_Headers_empty;
v___x_1585_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1585_, 0, v_fst_1561_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = lean_unbox(v_fst_1560_);
lean_dec(v_fst_1560_);
lean_ctor_set_uint8(v___x_1585_, sizeof(void*)*2, v___x_1586_);
lean_ctor_set_uint8(v___x_1585_, sizeof(void*)*2 + 1, v___x_1583_);
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 1, v___x_1585_);
lean_ctor_set(v___x_1563_, 0, v_pos_1548_);
v___x_1588_ = v___x_1563_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_pos_1548_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v___x_1585_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
v___jp_1572_:
{
if (v___x_1571_ == 0)
{
lean_del_object(v___x_1568_);
lean_dec(v_snd_1566_);
lean_dec(v_fst_1561_);
lean_dec(v_fst_1560_);
goto v___jp_1553_;
}
else
{
lean_object* v___x_1573_; uint8_t v___x_1574_; 
v___x_1573_ = lean_unsigned_to_nat(0u);
v___x_1574_ = lean_nat_dec_eq(v_snd_1566_, v___x_1573_);
lean_dec(v_snd_1566_);
if (v___x_1574_ == 0)
{
lean_del_object(v___x_1568_);
lean_dec(v_fst_1561_);
lean_dec(v_fst_1560_);
goto v___jp_1553_;
}
else
{
uint8_t v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; uint8_t v___x_1578_; lean_object* v___x_1580_; 
lean_del_object(v___x_1551_);
v___x_1575_ = 0;
v___x_1576_ = l_Std_Http_Headers_empty;
v___x_1577_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1577_, 0, v_fst_1561_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = lean_unbox(v_fst_1560_);
lean_dec(v_fst_1560_);
lean_ctor_set_uint8(v___x_1577_, sizeof(void*)*2, v___x_1578_);
lean_ctor_set_uint8(v___x_1577_, sizeof(void*)*2 + 1, v___x_1575_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 1, v___x_1577_);
lean_ctor_set(v___x_1568_, 0, v_pos_1548_);
v___x_1580_ = v___x_1568_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_pos_1548_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v___x_1577_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
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
lean_object* v_pos_1594_; lean_object* v_err_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
v_pos_1594_ = lean_ctor_get(v___x_1547_, 0);
v_err_1595_ = lean_ctor_get(v___x_1547_, 1);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1547_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_err_1595_);
lean_inc(v_pos_1594_);
lean_dec(v___x_1547_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_pos_1594_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_err_1595_);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine___boxed(lean_object* v_limits_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Std_Http_Protocol_H1_parseRequestLine(v_limits_1603_, v_a_1604_);
lean_dec_ref(v_limits_1603_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion(lean_object* v_limits_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineParts(v_limits_1606_, v_a_1607_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_res_1609_; lean_object* v_snd_1610_; lean_object* v_snd_1611_; lean_object* v_pos_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1644_; 
v_res_1609_ = lean_ctor_get(v___x_1608_, 1);
lean_inc(v_res_1609_);
v_snd_1610_ = lean_ctor_get(v_res_1609_, 1);
lean_inc(v_snd_1610_);
v_snd_1611_ = lean_ctor_get(v_snd_1610_, 1);
lean_inc(v_snd_1611_);
v_pos_1612_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1644_ == 0)
{
lean_object* v_unused_1645_; 
v_unused_1645_ = lean_ctor_get(v___x_1608_, 1);
lean_dec(v_unused_1645_);
v___x_1614_ = v___x_1608_;
v_isShared_1615_ = v_isSharedCheck_1644_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_pos_1612_);
lean_dec(v___x_1608_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1644_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v_fst_1616_; lean_object* v_fst_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1642_; 
v_fst_1616_ = lean_ctor_get(v_res_1609_, 0);
lean_inc(v_fst_1616_);
lean_dec(v_res_1609_);
v_fst_1617_ = lean_ctor_get(v_snd_1610_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_snd_1610_);
if (v_isSharedCheck_1642_ == 0)
{
lean_object* v_unused_1643_; 
v_unused_1643_ = lean_ctor_get(v_snd_1610_, 1);
lean_dec(v_unused_1643_);
v___x_1619_ = v_snd_1610_;
v_isShared_1620_ = v_isSharedCheck_1642_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_fst_1617_);
lean_dec(v_snd_1610_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1642_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v_fst_1621_; lean_object* v_snd_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1641_; 
v_fst_1621_ = lean_ctor_get(v_snd_1611_, 0);
v_snd_1622_ = lean_ctor_get(v_snd_1611_, 1);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_snd_1611_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1624_ = v_snd_1611_;
v_isShared_1625_ = v_isSharedCheck_1641_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_snd_1622_);
lean_inc(v_fst_1621_);
lean_dec(v_snd_1611_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1641_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___y_1627_; lean_object* v___x_1638_; uint8_t v___x_1639_; 
v___x_1638_ = lean_unsigned_to_nat(1u);
v___x_1639_ = lean_nat_dec_eq(v_fst_1621_, v___x_1638_);
if (v___x_1639_ == 0)
{
v___y_1627_ = v_snd_1622_;
goto v___jp_1626_;
}
else
{
uint8_t v___x_1640_; 
v___x_1640_ = lean_nat_dec_le(v_snd_1622_, v___x_1638_);
if (v___x_1640_ == 0)
{
lean_dec(v_snd_1622_);
v___y_1627_ = v___x_1638_;
goto v___jp_1626_;
}
else
{
v___y_1627_ = v_snd_1622_;
goto v___jp_1626_;
}
}
v___jp_1626_:
{
lean_object* v___x_1628_; lean_object* v___x_1630_; 
v___x_1628_ = l_Std_Http_Version_ofNumber_x3f(v_fst_1621_, v___y_1627_);
lean_dec(v___y_1627_);
lean_dec(v_fst_1621_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 1, v___x_1628_);
lean_ctor_set(v___x_1624_, 0, v_fst_1617_);
v___x_1630_ = v___x_1624_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_fst_1617_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1632_; 
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 1, v___x_1630_);
lean_ctor_set(v___x_1619_, 0, v_fst_1616_);
v___x_1632_ = v___x_1619_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_fst_1616_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v___x_1630_);
v___x_1632_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
lean_object* v___x_1634_; 
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 1, v___x_1632_);
v___x_1634_ = v___x_1614_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_pos_1612_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v___x_1632_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
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
lean_object* v_pos_1646_; lean_object* v_err_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
v_pos_1646_ = lean_ctor_get(v___x_1608_, 0);
v_err_1647_ = lean_ctor_get(v___x_1608_, 1);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1608_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_err_1647_);
lean_inc(v_pos_1646_);
lean_dec(v___x_1608_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_pos_1646_);
lean_ctor_set(v_reuseFailAlloc_1653_, 1, v_err_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion___boxed(lean_object* v_limits_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Std_Http_Protocol_H1_parseRequestLineRawVersion(v_limits_1655_, v_a_1656_);
lean_dec_ref(v_limits_1655_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_checkFieldValueLength(lean_object* v_limits_1661_, lean_object* v_value_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v_pos_1665_; lean_object* v_pos_1669_; 
if (lean_obj_tag(v_value_1662_) == 1)
{
lean_object* v_val_1672_; lean_object* v_maxHeaderValueLength_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; 
v_val_1672_ = lean_ctor_get(v_value_1662_, 0);
v_maxHeaderValueLength_1673_ = lean_ctor_get(v_limits_1661_, 9);
v___x_1674_ = l_ByteSlice_size(v_val_1672_);
v___x_1675_ = lean_nat_dec_eq(v___x_1674_, v_maxHeaderValueLength_1673_);
lean_dec(v___x_1674_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = lean_box(0);
v___x_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1677_, 0, v_a_1663_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
return v___x_1677_;
}
else
{
lean_object* v_array_1678_; lean_object* v_idx_1679_; lean_object* v___x_1680_; uint8_t v___x_1681_; 
v_array_1678_ = lean_ctor_get(v_a_1663_, 0);
v_idx_1679_ = lean_ctor_get(v_a_1663_, 1);
v___x_1680_ = lean_byte_array_size(v_array_1678_);
v___x_1681_ = lean_nat_dec_lt(v_idx_1679_, v___x_1680_);
if (v___x_1681_ == 0)
{
v_pos_1669_ = v_a_1663_;
goto v___jp_1668_;
}
else
{
uint8_t v___x_1682_; uint32_t v___x_1683_; uint32_t v___x_1691_; uint8_t v___x_1692_; 
v___x_1682_ = lean_byte_array_fget(v_array_1678_, v_idx_1679_);
v___x_1683_ = lean_uint8_to_uint32(v___x_1682_);
v___x_1691_ = 33;
v___x_1692_ = lean_uint32_dec_le(v___x_1691_, v___x_1683_);
if (v___x_1692_ == 0)
{
goto v___jp_1684_;
}
else
{
uint32_t v___x_1693_; uint8_t v___x_1694_; 
v___x_1693_ = 126;
v___x_1694_ = lean_uint32_dec_le(v___x_1683_, v___x_1693_);
if (v___x_1694_ == 0)
{
goto v___jp_1684_;
}
else
{
v_pos_1665_ = v_a_1663_;
goto v___jp_1664_;
}
}
v___jp_1684_:
{
uint32_t v___x_1685_; uint8_t v___x_1686_; 
v___x_1685_ = 128;
v___x_1686_ = lean_uint32_dec_le(v___x_1685_, v___x_1683_);
if (v___x_1686_ == 0)
{
uint32_t v___x_1687_; uint8_t v___x_1688_; 
v___x_1687_ = 32;
v___x_1688_ = lean_uint32_dec_eq(v___x_1683_, v___x_1687_);
if (v___x_1688_ == 0)
{
uint32_t v___x_1689_; uint8_t v___x_1690_; 
v___x_1689_ = 9;
v___x_1690_ = lean_uint32_dec_eq(v___x_1683_, v___x_1689_);
if (v___x_1690_ == 0)
{
v_pos_1669_ = v_a_1663_;
goto v___jp_1668_;
}
else
{
v_pos_1665_ = v_a_1663_;
goto v___jp_1664_;
}
}
else
{
v_pos_1665_ = v_a_1663_;
goto v___jp_1664_;
}
}
else
{
v_pos_1665_ = v_a_1663_;
goto v___jp_1664_;
}
}
}
}
}
else
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = lean_box(0);
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v_a_1663_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
return v___x_1696_;
}
v___jp_1664_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_checkFieldValueLength___closed__1));
v___x_1667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1667_, 0, v_pos_1665_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
return v___x_1667_;
}
v___jp_1668_:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = lean_box(0);
v___x_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1671_, 0, v_pos_1669_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
return v___x_1671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_checkFieldValueLength___boxed(lean_object* v_limits_1697_, lean_object* v_value_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_checkFieldValueLength(v_limits_1697_, v_value_1698_, v_a_1699_);
lean_dec(v_value_1698_);
lean_dec_ref(v_limits_1697_);
return v_res_1700_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(uint8_t v___y_1701_){
_start:
{
uint32_t v___x_1702_; uint32_t v___x_1703_; uint8_t v___x_1704_; 
v___x_1702_ = lean_uint8_to_uint32(v___y_1701_);
v___x_1703_ = 32;
v___x_1704_ = lean_uint32_dec_eq(v___x_1702_, v___x_1703_);
if (v___x_1704_ == 0)
{
uint32_t v___x_1705_; uint8_t v___x_1706_; 
v___x_1705_ = 9;
v___x_1706_ = lean_uint32_dec_eq(v___x_1702_, v___x_1705_);
return v___x_1706_;
}
else
{
return v___x_1704_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed(lean_object* v___y_1707_){
_start:
{
uint8_t v___y_4884__boxed_1708_; uint8_t v_res_1709_; lean_object* v_r_1710_; 
v___y_4884__boxed_1708_ = lean_unbox(v___y_1707_);
v_res_1709_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(v___y_4884__boxed_1708_);
v_r_1710_ = lean_box(v_res_1709_);
return v_r_1710_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0(uint8_t v___y_1711_){
_start:
{
uint32_t v___x_1712_; uint32_t v___x_1720_; uint8_t v___x_1721_; 
v___x_1712_ = lean_uint8_to_uint32(v___y_1711_);
v___x_1720_ = 33;
v___x_1721_ = lean_uint32_dec_le(v___x_1720_, v___x_1712_);
if (v___x_1721_ == 0)
{
goto v___jp_1713_;
}
else
{
uint32_t v___x_1722_; uint8_t v___x_1723_; 
v___x_1722_ = 126;
v___x_1723_ = lean_uint32_dec_le(v___x_1712_, v___x_1722_);
if (v___x_1723_ == 0)
{
goto v___jp_1713_;
}
else
{
return v___x_1723_;
}
}
v___jp_1713_:
{
uint32_t v___x_1714_; uint8_t v___x_1715_; 
v___x_1714_ = 128;
v___x_1715_ = lean_uint32_dec_le(v___x_1714_, v___x_1712_);
if (v___x_1715_ == 0)
{
uint32_t v___x_1716_; uint8_t v___x_1717_; 
v___x_1716_ = 32;
v___x_1717_ = lean_uint32_dec_eq(v___x_1712_, v___x_1716_);
if (v___x_1717_ == 0)
{
uint32_t v___x_1718_; uint8_t v___x_1719_; 
v___x_1718_ = 9;
v___x_1719_ = lean_uint32_dec_eq(v___x_1712_, v___x_1718_);
return v___x_1719_;
}
else
{
return v___x_1717_;
}
}
else
{
return v___x_1715_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0___boxed(lean_object* v___y_1724_){
_start:
{
uint8_t v___y_4897__boxed_1725_; uint8_t v_res_1726_; lean_object* v_r_1727_; 
v___y_4897__boxed_1725_ = lean_unbox(v___y_1724_);
v_res_1726_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0(v___y_4897__boxed_1725_);
v_r_1727_ = lean_box(v_res_1726_);
return v_r_1727_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(lean_object* v_s_1728_, lean_object* v_pos_1729_){
_start:
{
lean_object* v_str_1730_; lean_object* v_startInclusive_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; uint8_t v_decide_1735_; 
v_str_1730_ = lean_ctor_get(v_s_1728_, 0);
v_startInclusive_1731_ = lean_ctor_get(v_s_1728_, 1);
v___x_1732_ = lean_nat_add(v_startInclusive_1731_, v_pos_1729_);
v___x_1733_ = lean_nat_sub(v___x_1732_, v_startInclusive_1731_);
v___x_1734_ = lean_unsigned_to_nat(0u);
v_decide_1735_ = lean_nat_dec_eq(v___x_1733_, v___x_1734_);
if (v_decide_1735_ == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1744_; uint32_t v___x_1745_; uint32_t v___x_1746_; uint8_t v___x_1747_; 
lean_inc(v_startInclusive_1731_);
lean_inc_ref(v_str_1730_);
v___x_1736_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1736_, 0, v_str_1730_);
lean_ctor_set(v___x_1736_, 1, v_startInclusive_1731_);
lean_ctor_set(v___x_1736_, 2, v___x_1732_);
v___x_1737_ = lean_unsigned_to_nat(1u);
v___x_1738_ = lean_nat_sub(v___x_1733_, v___x_1737_);
lean_dec(v___x_1733_);
v___x_1739_ = l_String_Slice_posLE(v___x_1736_, v___x_1738_);
lean_dec_ref_known(v___x_1736_, 3);
v___x_1744_ = lean_nat_add(v_startInclusive_1731_, v___x_1739_);
v___x_1745_ = lean_string_utf8_get_fast(v_str_1730_, v___x_1744_);
lean_dec(v___x_1744_);
v___x_1746_ = 32;
v___x_1747_ = lean_uint32_dec_eq(v___x_1745_, v___x_1746_);
if (v___x_1747_ == 0)
{
uint32_t v___x_1748_; uint8_t v___x_1749_; 
v___x_1748_ = 9;
v___x_1749_ = lean_uint32_dec_eq(v___x_1745_, v___x_1748_);
if (v___x_1749_ == 0)
{
uint32_t v___x_1750_; uint8_t v___x_1751_; 
v___x_1750_ = 13;
v___x_1751_ = lean_uint32_dec_eq(v___x_1745_, v___x_1750_);
if (v___x_1751_ == 0)
{
uint32_t v___x_1752_; uint8_t v___x_1753_; 
v___x_1752_ = 10;
v___x_1753_ = lean_uint32_dec_eq(v___x_1745_, v___x_1752_);
if (v___x_1753_ == 0)
{
lean_dec(v___x_1739_);
return v_pos_1729_;
}
else
{
goto v___jp_1740_;
}
}
else
{
goto v___jp_1740_;
}
}
else
{
goto v___jp_1740_;
}
}
else
{
goto v___jp_1740_;
}
v___jp_1740_:
{
lean_object* v___x_1741_; uint8_t v___x_1742_; 
v___x_1741_ = lean_nat_add(v___x_1739_, v___x_1737_);
v___x_1742_ = lean_nat_dec_le(v___x_1741_, v_pos_1729_);
lean_dec(v___x_1741_);
if (v___x_1742_ == 0)
{
lean_dec(v___x_1739_);
return v_pos_1729_;
}
else
{
lean_dec(v_pos_1729_);
v_pos_1729_ = v___x_1739_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1733_);
lean_dec(v___x_1732_);
return v_pos_1729_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0___boxed(lean_object* v_s_1754_, lean_object* v_pos_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(v_s_1754_, v_pos_1755_);
lean_dec_ref(v_s_1754_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(lean_object* v_limits_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v_pos_1769_; lean_object* v_pos_1773_; lean_object* v_pos_1777_; lean_object* v_maxHeaderNameLength_1780_; lean_object* v_maxHeaderValueLength_1781_; lean_object* v_maxSpaceSequence_1782_; lean_object* v___f_1783_; lean_object* v___x_1784_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1820_; lean_object* v_pos_1821_; lean_object* v_res_1822_; lean_object* v___x_1839_; lean_object* v_snd_1840_; lean_object* v_snd_1841_; uint8_t v___x_1842_; 
v_maxHeaderNameLength_1780_ = lean_ctor_get(v_limits_1766_, 8);
v_maxHeaderValueLength_1781_ = lean_ctor_get(v_limits_1766_, 9);
v_maxSpaceSequence_1782_ = lean_ctor_get(v_limits_1766_, 10);
v___f_1783_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_1784_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1767_);
v___x_1839_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1783_, v_maxHeaderNameLength_1780_, v___x_1784_, v_a_1767_);
v_snd_1840_ = lean_ctor_get(v___x_1839_, 1);
lean_inc(v_snd_1840_);
v_snd_1841_ = lean_ctor_get(v_snd_1840_, 1);
v___x_1842_ = lean_unbox(v_snd_1841_);
if (v___x_1842_ == 0)
{
lean_object* v_fst_1843_; lean_object* v_fst_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_2054_; 
v_fst_1843_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_fst_1843_);
lean_dec_ref(v___x_1839_);
v_fst_1844_ = lean_ctor_get(v_snd_1840_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_snd_1840_);
if (v_isSharedCheck_2054_ == 0)
{
lean_object* v_unused_2055_; 
v_unused_2055_ = lean_ctor_get(v_snd_1840_, 1);
lean_dec(v_unused_2055_);
v___x_1846_ = v_snd_1840_;
v_isShared_1847_ = v_isSharedCheck_2054_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_fst_1844_);
lean_dec(v_snd_1840_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_2054_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
uint8_t v___x_1848_; 
v___x_1848_ = lean_nat_dec_eq(v_fst_1843_, v___x_1784_);
if (v___x_1848_ == 0)
{
lean_object* v_array_1849_; lean_object* v_idx_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_2049_; 
v_array_1849_ = lean_ctor_get(v_a_1767_, 0);
v_idx_1850_ = lean_ctor_get(v_a_1767_, 1);
v_isSharedCheck_2049_ = !lean_is_exclusive(v_a_1767_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_1852_ = v_a_1767_;
v_isShared_1853_ = v_isSharedCheck_2049_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_idx_1850_);
lean_inc(v_array_1849_);
lean_dec(v_a_1767_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_2049_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___f_1854_; lean_object* v___y_1856_; lean_object* v_pos_1857_; lean_object* v_res_1858_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v_lower_1888_; lean_object* v_upper_1889_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___f_1900_; lean_object* v___y_1902_; lean_object* v_pos_1903_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v_array_1932_; lean_object* v_idx_1933_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; uint32_t v___y_1981_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; uint32_t v___y_1990_; lean_object* v_lower_1996_; lean_object* v_upper_1997_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___y_2046_; uint8_t v___x_2048_; 
v___f_1854_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3));
v___f_1900_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4));
v___x_2043_ = lean_nat_add(v_idx_1850_, v_fst_1843_);
lean_dec(v_fst_1843_);
v___x_2044_ = lean_byte_array_size(v_array_1849_);
v___x_2048_ = lean_nat_dec_le(v_idx_1850_, v___x_1784_);
if (v___x_2048_ == 0)
{
v___y_2046_ = v_idx_1850_;
goto v___jp_2045_;
}
else
{
lean_dec(v_idx_1850_);
v___y_2046_ = v___x_1784_;
goto v___jp_2045_;
}
v___jp_1855_:
{
lean_object* v___x_1859_; lean_object* v_snd_1860_; lean_object* v_snd_1861_; uint8_t v___x_1862_; 
v___x_1859_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1854_, v_maxSpaceSequence_1782_, v___x_1784_, v_pos_1857_);
v_snd_1860_ = lean_ctor_get(v___x_1859_, 1);
lean_inc(v_snd_1860_);
lean_dec_ref(v___x_1859_);
v_snd_1861_ = lean_ctor_get(v_snd_1860_, 1);
v___x_1862_ = lean_unbox(v_snd_1861_);
if (v___x_1862_ == 0)
{
lean_object* v_fst_1863_; lean_object* v_array_1864_; lean_object* v_idx_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
v_fst_1863_ = lean_ctor_get(v_snd_1860_, 0);
lean_inc(v_fst_1863_);
lean_dec(v_snd_1860_);
v_array_1864_ = lean_ctor_get(v_fst_1863_, 0);
v_idx_1865_ = lean_ctor_get(v_fst_1863_, 1);
v___x_1866_ = lean_byte_array_size(v_array_1864_);
v___x_1867_ = lean_nat_dec_lt(v_idx_1865_, v___x_1866_);
if (v___x_1867_ == 0)
{
v___y_1820_ = v___y_1856_;
v_pos_1821_ = v_fst_1863_;
v_res_1822_ = v_res_1858_;
goto v___jp_1819_;
}
else
{
uint8_t v___x_1868_; uint32_t v___x_1869_; uint32_t v___x_1870_; uint8_t v___x_1871_; 
v___x_1868_ = lean_byte_array_fget(v_array_1864_, v_idx_1865_);
v___x_1869_ = lean_uint8_to_uint32(v___x_1868_);
v___x_1870_ = 32;
v___x_1871_ = lean_uint32_dec_eq(v___x_1869_, v___x_1870_);
if (v___x_1871_ == 0)
{
uint32_t v___x_1872_; uint8_t v___x_1873_; 
v___x_1872_ = 9;
v___x_1873_ = lean_uint32_dec_eq(v___x_1869_, v___x_1872_);
if (v___x_1873_ == 0)
{
v___y_1820_ = v___y_1856_;
v_pos_1821_ = v_fst_1863_;
v_res_1822_ = v_res_1858_;
goto v___jp_1819_;
}
else
{
lean_dec(v_res_1858_);
lean_dec_ref(v___y_1856_);
v_pos_1777_ = v_fst_1863_;
goto v___jp_1776_;
}
}
else
{
lean_dec(v_res_1858_);
lean_dec_ref(v___y_1856_);
v_pos_1777_ = v_fst_1863_;
goto v___jp_1776_;
}
}
}
else
{
lean_object* v_fst_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1882_; 
lean_dec(v_res_1858_);
lean_dec_ref(v___y_1856_);
v_fst_1874_ = lean_ctor_get(v_snd_1860_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v_snd_1860_);
if (v_isSharedCheck_1882_ == 0)
{
lean_object* v_unused_1883_; 
v_unused_1883_ = lean_ctor_get(v_snd_1860_, 1);
lean_dec(v_unused_1883_);
v___x_1876_ = v_snd_1860_;
v_isShared_1877_ = v_isSharedCheck_1882_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_fst_1874_);
lean_dec(v_snd_1860_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1882_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1878_ = lean_box(0);
if (v_isShared_1877_ == 0)
{
lean_ctor_set_tag(v___x_1876_, 1);
lean_ctor_set(v___x_1876_, 1, v___x_1878_);
v___x_1880_ = v___x_1876_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_fst_1874_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
v___jp_1884_:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = l_ByteArray_toByteSlice(v___y_1885_, v_lower_1888_, v_upper_1889_);
v___x_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
v___y_1856_ = v___y_1887_;
v_pos_1857_ = v___y_1886_;
v_res_1858_ = v___x_1891_;
goto v___jp_1855_;
}
v___jp_1892_:
{
uint8_t v___x_1899_; 
v___x_1899_ = lean_nat_dec_le(v___y_1897_, v___y_1895_);
if (v___x_1899_ == 0)
{
lean_dec(v___y_1897_);
v___y_1885_ = v___y_1893_;
v___y_1886_ = v___y_1894_;
v___y_1887_ = v___y_1896_;
v_lower_1888_ = v___y_1898_;
v_upper_1889_ = v___y_1895_;
goto v___jp_1884_;
}
else
{
lean_dec(v___y_1895_);
v___y_1885_ = v___y_1893_;
v___y_1886_ = v___y_1894_;
v___y_1887_ = v___y_1896_;
v_lower_1888_ = v___y_1898_;
v_upper_1889_ = v___y_1897_;
goto v___jp_1884_;
}
}
v___jp_1901_:
{
lean_object* v___x_1904_; lean_object* v_snd_1905_; lean_object* v_snd_1906_; uint8_t v___x_1907_; 
lean_inc_ref(v_pos_1903_);
v___x_1904_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1900_, v_maxHeaderValueLength_1781_, v___x_1784_, v_pos_1903_);
v_snd_1905_ = lean_ctor_get(v___x_1904_, 1);
lean_inc(v_snd_1905_);
v_snd_1906_ = lean_ctor_get(v_snd_1905_, 1);
v___x_1907_ = lean_unbox(v_snd_1906_);
if (v___x_1907_ == 0)
{
lean_object* v_fst_1908_; lean_object* v_fst_1909_; lean_object* v_array_1910_; lean_object* v_idx_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; 
v_fst_1908_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_fst_1908_);
lean_dec_ref(v___x_1904_);
v_fst_1909_ = lean_ctor_get(v_snd_1905_, 0);
lean_inc(v_fst_1909_);
lean_dec(v_snd_1905_);
v_array_1910_ = lean_ctor_get(v_pos_1903_, 0);
lean_inc_ref(v_array_1910_);
v_idx_1911_ = lean_ctor_get(v_pos_1903_, 1);
lean_inc(v_idx_1911_);
lean_dec_ref(v_pos_1903_);
v___x_1912_ = lean_nat_add(v_idx_1911_, v_fst_1908_);
lean_dec(v_fst_1908_);
v___x_1913_ = lean_byte_array_size(v_array_1910_);
v___x_1914_ = lean_nat_dec_le(v_idx_1911_, v___x_1784_);
if (v___x_1914_ == 0)
{
v___y_1893_ = v_array_1910_;
v___y_1894_ = v_fst_1909_;
v___y_1895_ = v___x_1913_;
v___y_1896_ = v___y_1902_;
v___y_1897_ = v___x_1912_;
v___y_1898_ = v_idx_1911_;
goto v___jp_1892_;
}
else
{
lean_dec(v_idx_1911_);
v___y_1893_ = v_array_1910_;
v___y_1894_ = v_fst_1909_;
v___y_1895_ = v___x_1913_;
v___y_1896_ = v___y_1902_;
v___y_1897_ = v___x_1912_;
v___y_1898_ = v___x_1784_;
goto v___jp_1892_;
}
}
else
{
lean_object* v_fst_1915_; lean_object* v_idx_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1927_; 
lean_dec_ref(v___x_1904_);
v_fst_1915_ = lean_ctor_get(v_snd_1905_, 0);
lean_inc(v_fst_1915_);
lean_dec(v_snd_1905_);
v_idx_1916_ = lean_ctor_get(v_pos_1903_, 1);
v_isSharedCheck_1927_ = !lean_is_exclusive(v_pos_1903_);
if (v_isSharedCheck_1927_ == 0)
{
lean_object* v_unused_1928_; 
v_unused_1928_ = lean_ctor_get(v_pos_1903_, 0);
lean_dec(v_unused_1928_);
v___x_1918_ = v_pos_1903_;
v_isShared_1919_ = v_isSharedCheck_1927_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_idx_1916_);
lean_dec(v_pos_1903_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1927_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v_idx_1920_; uint8_t v___x_1921_; 
v_idx_1920_ = lean_ctor_get(v_fst_1915_, 1);
v___x_1921_ = lean_nat_dec_eq(v_idx_1916_, v_idx_1920_);
lean_dec(v_idx_1916_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1922_; lean_object* v___x_1924_; 
lean_dec_ref(v___y_1902_);
v___x_1922_ = lean_box(0);
if (v_isShared_1919_ == 0)
{
lean_ctor_set_tag(v___x_1918_, 1);
lean_ctor_set(v___x_1918_, 1, v___x_1922_);
lean_ctor_set(v___x_1918_, 0, v_fst_1915_);
v___x_1924_ = v___x_1918_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_fst_1915_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v___x_1922_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
else
{
lean_object* v___x_1926_; 
lean_del_object(v___x_1918_);
v___x_1926_ = lean_box(0);
v___y_1856_ = v___y_1902_;
v_pos_1857_ = v_fst_1915_;
v_res_1858_ = v___x_1926_;
goto v___jp_1855_;
}
}
}
}
v___jp_1929_:
{
lean_object* v___x_1934_; uint8_t v___x_1935_; 
v___x_1934_ = lean_byte_array_size(v_array_1932_);
v___x_1935_ = lean_nat_dec_lt(v_idx_1933_, v___x_1934_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; lean_object* v___x_1938_; 
lean_dec(v_idx_1933_);
lean_dec_ref(v_array_1932_);
lean_dec_ref(v___y_1930_);
lean_del_object(v___x_1852_);
v___x_1936_ = lean_box(0);
if (v_isShared_1847_ == 0)
{
lean_ctor_set_tag(v___x_1846_, 1);
lean_ctor_set(v___x_1846_, 1, v___x_1936_);
lean_ctor_set(v___x_1846_, 0, v___y_1931_);
v___x_1938_ = v___x_1846_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___y_1931_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
else
{
uint8_t v___x_1940_; uint8_t v_got_1941_; uint8_t v___x_1942_; 
v___x_1940_ = 58;
v_got_1941_ = lean_byte_array_fget(v_array_1932_, v_idx_1933_);
v___x_1942_ = lean_uint8_dec_eq(v_got_1941_, v___x_1940_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; lean_object* v___x_1945_; 
lean_dec(v_idx_1933_);
lean_dec_ref(v_array_1932_);
lean_dec_ref(v___y_1930_);
lean_del_object(v___x_1852_);
v___x_1943_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__6));
if (v_isShared_1847_ == 0)
{
lean_ctor_set_tag(v___x_1846_, 1);
lean_ctor_set(v___x_1846_, 1, v___x_1943_);
lean_ctor_set(v___x_1846_, 0, v___y_1931_);
v___x_1945_ = v___x_1846_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___y_1931_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v___x_1943_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
else
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1950_; 
lean_dec_ref(v___y_1931_);
lean_del_object(v___x_1846_);
v___x_1947_ = lean_unsigned_to_nat(1u);
v___x_1948_ = lean_nat_add(v_idx_1933_, v___x_1947_);
lean_dec(v_idx_1933_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 1, v___x_1948_);
lean_ctor_set(v___x_1852_, 0, v_array_1932_);
v___x_1950_ = v___x_1852_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_array_1932_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v___x_1948_);
v___x_1950_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
lean_object* v___x_1951_; lean_object* v_snd_1952_; lean_object* v_snd_1953_; uint8_t v___x_1954_; 
v___x_1951_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1854_, v_maxSpaceSequence_1782_, v___x_1784_, v___x_1950_);
v_snd_1952_ = lean_ctor_get(v___x_1951_, 1);
lean_inc(v_snd_1952_);
lean_dec_ref(v___x_1951_);
v_snd_1953_ = lean_ctor_get(v_snd_1952_, 1);
v___x_1954_ = lean_unbox(v_snd_1953_);
if (v___x_1954_ == 0)
{
lean_object* v_fst_1955_; lean_object* v_array_1956_; lean_object* v_idx_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; 
v_fst_1955_ = lean_ctor_get(v_snd_1952_, 0);
lean_inc(v_fst_1955_);
lean_dec(v_snd_1952_);
v_array_1956_ = lean_ctor_get(v_fst_1955_, 0);
v_idx_1957_ = lean_ctor_get(v_fst_1955_, 1);
v___x_1958_ = lean_byte_array_size(v_array_1956_);
v___x_1959_ = lean_nat_dec_lt(v_idx_1957_, v___x_1958_);
if (v___x_1959_ == 0)
{
v___y_1902_ = v___y_1930_;
v_pos_1903_ = v_fst_1955_;
goto v___jp_1901_;
}
else
{
uint8_t v___x_1960_; uint32_t v___x_1961_; uint32_t v___x_1962_; uint8_t v___x_1963_; 
v___x_1960_ = lean_byte_array_fget(v_array_1956_, v_idx_1957_);
v___x_1961_ = lean_uint8_to_uint32(v___x_1960_);
v___x_1962_ = 32;
v___x_1963_ = lean_uint32_dec_eq(v___x_1961_, v___x_1962_);
if (v___x_1963_ == 0)
{
uint32_t v___x_1964_; uint8_t v___x_1965_; 
v___x_1964_ = 9;
v___x_1965_ = lean_uint32_dec_eq(v___x_1961_, v___x_1964_);
if (v___x_1965_ == 0)
{
v___y_1902_ = v___y_1930_;
v_pos_1903_ = v_fst_1955_;
goto v___jp_1901_;
}
else
{
lean_dec_ref(v___y_1930_);
v_pos_1773_ = v_fst_1955_;
goto v___jp_1772_;
}
}
else
{
lean_dec_ref(v___y_1930_);
v_pos_1773_ = v_fst_1955_;
goto v___jp_1772_;
}
}
}
else
{
lean_object* v_fst_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1974_; 
lean_dec_ref(v___y_1930_);
v_fst_1966_ = lean_ctor_get(v_snd_1952_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_snd_1952_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; 
v_unused_1975_ = lean_ctor_get(v_snd_1952_, 1);
lean_dec(v_unused_1975_);
v___x_1968_ = v_snd_1952_;
v_isShared_1969_ = v_isSharedCheck_1974_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_fst_1966_);
lean_dec(v_snd_1952_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1974_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1970_; lean_object* v___x_1972_; 
v___x_1970_ = lean_box(0);
if (v_isShared_1969_ == 0)
{
lean_ctor_set_tag(v___x_1968_, 1);
lean_ctor_set(v___x_1968_, 1, v___x_1970_);
v___x_1972_ = v___x_1968_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_fst_1966_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
}
}
}
v___jp_1977_:
{
uint32_t v___x_1982_; uint8_t v___x_1983_; 
v___x_1982_ = 97;
v___x_1983_ = lean_uint32_dec_le(v___x_1982_, v___y_1981_);
if (v___x_1983_ == 0)
{
v___y_1930_ = v___y_1980_;
v___y_1931_ = v_fst_1844_;
v_array_1932_ = v___y_1978_;
v_idx_1933_ = v___y_1979_;
goto v___jp_1929_;
}
else
{
uint32_t v___x_1984_; uint8_t v___x_1985_; 
v___x_1984_ = 122;
v___x_1985_ = lean_uint32_dec_le(v___y_1981_, v___x_1984_);
if (v___x_1985_ == 0)
{
v___y_1930_ = v___y_1980_;
v___y_1931_ = v_fst_1844_;
v_array_1932_ = v___y_1978_;
v_idx_1933_ = v___y_1979_;
goto v___jp_1929_;
}
else
{
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_del_object(v___x_1852_);
lean_del_object(v___x_1846_);
v_pos_1769_ = v_fst_1844_;
goto v___jp_1768_;
}
}
}
v___jp_1986_:
{
uint32_t v___x_1991_; uint8_t v___x_1992_; 
v___x_1991_ = 65;
v___x_1992_ = lean_uint32_dec_le(v___x_1991_, v___y_1990_);
if (v___x_1992_ == 0)
{
v___y_1978_ = v___y_1987_;
v___y_1979_ = v___y_1988_;
v___y_1980_ = v___y_1989_;
v___y_1981_ = v___y_1990_;
goto v___jp_1977_;
}
else
{
uint32_t v___x_1993_; uint8_t v___x_1994_; 
v___x_1993_ = 90;
v___x_1994_ = lean_uint32_dec_le(v___y_1990_, v___x_1993_);
if (v___x_1994_ == 0)
{
v___y_1978_ = v___y_1987_;
v___y_1979_ = v___y_1988_;
v___y_1980_ = v___y_1989_;
v___y_1981_ = v___y_1990_;
goto v___jp_1977_;
}
else
{
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_del_object(v___x_1852_);
lean_del_object(v___x_1846_);
v_pos_1769_ = v_fst_1844_;
goto v___jp_1768_;
}
}
}
v___jp_1995_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
v___x_1998_ = l_ByteArray_toByteSlice(v_array_1849_, v_lower_1996_, v_upper_1997_);
v___x_1999_ = l_ByteSlice_size(v___x_1998_);
v___x_2000_ = lean_nat_dec_eq(v___x_1999_, v_maxHeaderNameLength_1780_);
lean_dec(v___x_1999_);
if (v___x_2000_ == 0)
{
lean_object* v_array_2001_; lean_object* v_idx_2002_; 
v_array_2001_ = lean_ctor_get(v_fst_1844_, 0);
lean_inc_ref(v_array_2001_);
v_idx_2002_ = lean_ctor_get(v_fst_1844_, 1);
lean_inc(v_idx_2002_);
v___y_1930_ = v___x_1998_;
v___y_1931_ = v_fst_1844_;
v_array_1932_ = v_array_2001_;
v_idx_1933_ = v_idx_2002_;
goto v___jp_1929_;
}
else
{
lean_object* v_array_2003_; lean_object* v_idx_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; 
v_array_2003_ = lean_ctor_get(v_fst_1844_, 0);
v_idx_2004_ = lean_ctor_get(v_fst_1844_, 1);
v___x_2005_ = lean_byte_array_size(v_array_2003_);
v___x_2006_ = lean_nat_dec_lt(v_idx_2004_, v___x_2005_);
if (v___x_2006_ == 0)
{
lean_inc(v_idx_2004_);
lean_inc_ref(v_array_2003_);
v___y_1930_ = v___x_1998_;
v___y_1931_ = v_fst_1844_;
v_array_1932_ = v_array_2003_;
v_idx_1933_ = v_idx_2004_;
goto v___jp_1929_;
}
else
{
uint8_t v___x_2007_; uint32_t v___x_2008_; uint32_t v___x_2009_; uint8_t v___x_2010_; 
v___x_2007_ = lean_byte_array_fget(v_array_2003_, v_idx_2004_);
v___x_2008_ = lean_uint8_to_uint32(v___x_2007_);
v___x_2009_ = 33;
v___x_2010_ = lean_uint32_dec_eq(v___x_2008_, v___x_2009_);
if (v___x_2010_ == 0)
{
uint32_t v___x_2011_; uint8_t v___x_2012_; 
v___x_2011_ = 35;
v___x_2012_ = lean_uint32_dec_eq(v___x_2008_, v___x_2011_);
if (v___x_2012_ == 0)
{
uint32_t v___x_2013_; uint8_t v___x_2014_; 
v___x_2013_ = 36;
v___x_2014_ = lean_uint32_dec_eq(v___x_2008_, v___x_2013_);
if (v___x_2014_ == 0)
{
uint32_t v___x_2015_; uint8_t v___x_2016_; 
v___x_2015_ = 37;
v___x_2016_ = lean_uint32_dec_eq(v___x_2008_, v___x_2015_);
if (v___x_2016_ == 0)
{
uint32_t v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = 38;
v___x_2018_ = lean_uint32_dec_eq(v___x_2008_, v___x_2017_);
if (v___x_2018_ == 0)
{
uint32_t v___x_2019_; uint8_t v___x_2020_; 
v___x_2019_ = 39;
v___x_2020_ = lean_uint32_dec_eq(v___x_2008_, v___x_2019_);
if (v___x_2020_ == 0)
{
uint32_t v___x_2021_; uint8_t v___x_2022_; 
v___x_2021_ = 42;
v___x_2022_ = lean_uint32_dec_eq(v___x_2008_, v___x_2021_);
if (v___x_2022_ == 0)
{
uint32_t v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = 43;
v___x_2024_ = lean_uint32_dec_eq(v___x_2008_, v___x_2023_);
if (v___x_2024_ == 0)
{
uint32_t v___x_2025_; uint8_t v___x_2026_; 
v___x_2025_ = 45;
v___x_2026_ = lean_uint32_dec_eq(v___x_2008_, v___x_2025_);
if (v___x_2026_ == 0)
{
uint32_t v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = 46;
v___x_2028_ = lean_uint32_dec_eq(v___x_2008_, v___x_2027_);
if (v___x_2028_ == 0)
{
uint32_t v___x_2029_; uint8_t v___x_2030_; 
v___x_2029_ = 94;
v___x_2030_ = lean_uint32_dec_eq(v___x_2008_, v___x_2029_);
if (v___x_2030_ == 0)
{
uint32_t v___x_2031_; uint8_t v___x_2032_; 
v___x_2031_ = 95;
v___x_2032_ = lean_uint32_dec_eq(v___x_2008_, v___x_2031_);
if (v___x_2032_ == 0)
{
uint32_t v___x_2033_; uint8_t v___x_2034_; 
v___x_2033_ = 96;
v___x_2034_ = lean_uint32_dec_eq(v___x_2008_, v___x_2033_);
if (v___x_2034_ == 0)
{
uint32_t v___x_2035_; uint8_t v___x_2036_; 
v___x_2035_ = 124;
v___x_2036_ = lean_uint32_dec_eq(v___x_2008_, v___x_2035_);
if (v___x_2036_ == 0)
{
uint32_t v___x_2037_; uint8_t v___x_2038_; 
v___x_2037_ = 126;
v___x_2038_ = lean_uint32_dec_eq(v___x_2008_, v___x_2037_);
if (v___x_2038_ == 0)
{
uint32_t v___x_2039_; uint8_t v___x_2040_; 
v___x_2039_ = 48;
v___x_2040_ = lean_uint32_dec_le(v___x_2039_, v___x_2008_);
if (v___x_2040_ == 0)
{
lean_inc(v_idx_2004_);
lean_inc_ref(v_array_2003_);
v___y_1987_ = v_array_2003_;
v___y_1988_ = v_idx_2004_;
v___y_1989_ = v___x_1998_;
v___y_1990_ = v___x_2008_;
goto v___jp_1986_;
}
else
{
uint32_t v___x_2041_; uint8_t v___x_2042_; 
v___x_2041_ = 57;
v___x_2042_ = lean_uint32_dec_le(v___x_2008_, v___x_2041_);
if (v___x_2042_ == 0)
{
lean_inc(v_idx_2004_);
lean_inc_ref(v_array_2003_);
v___y_1987_ = v_array_2003_;
v___y_1988_ = v_idx_2004_;
v___y_1989_ = v___x_1998_;
v___y_1990_ = v___x_2008_;
goto v___jp_1986_;
}
else
{
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1852_);
lean_del_object(v___x_1846_);
v_pos_1769_ = v_fst_1844_;
goto v___jp_1768_;
}
}
}
else
{
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1852_);
lean_del_object(v___x_1846_);
v_pos_1769_ = v_fst_1844_;
goto v___jp_1768_;
}
}
else
{
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1852_);
lean_del_object(v___x_1846_);
v_pos_1769_ = v_fst_1844_;
goto v___jp_1768_;
}
}
else
{
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1852_);
lean_del_object(v___x_1846_);
v_pos_1769_ = v_fst_1844_;
goto v___jp_1768_;
}
}
else
{
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1852_);
lean_del_object(v___x_1846_);
v_pos_1769_ = v_fst_1844_;
goto v___jp_1768_;
}
}
else
{
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1852_);
lean_del_object(v___x_1846_);
v_pos_1769_ = v_fst_1844_;
goto v___jp_1768_;
}
}
else
{
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1852_);
lean_del_object(v___x_1846_);
v_pos_1769_ = v_fst_1844_;
goto v___jp_1768_;
}
}
else
{
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1852_);
lean_del_object(v___x_1846_);
v_pos_1769_ = v_fst_1844_;
goto v___jp_1768_;
}
}
else
{
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1852_);
lean_del_object(v___x_1846_);
v_pos_1769_ = v_fst_1844_;
goto v___jp_1768_;
}
}
else
{
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1852_);
lean_del_object(v___x_1846_);
v_pos_1769_ = v_fst_1844_;
goto v___jp_1768_;
}
}
else
{
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1852_);
lean_del_object(v___x_1846_);
v_pos_1769_ = v_fst_1844_;
goto v___jp_1768_;
}
}
else
{
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1852_);
lean_del_object(v___x_1846_);
v_pos_1769_ = v_fst_1844_;
goto v___jp_1768_;
}
}
else
{
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1852_);
lean_del_object(v___x_1846_);
v_pos_1769_ = v_fst_1844_;
goto v___jp_1768_;
}
}
else
{
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1852_);
lean_del_object(v___x_1846_);
v_pos_1769_ = v_fst_1844_;
goto v___jp_1768_;
}
}
else
{
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1852_);
lean_del_object(v___x_1846_);
v_pos_1769_ = v_fst_1844_;
goto v___jp_1768_;
}
}
else
{
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1852_);
lean_del_object(v___x_1846_);
v_pos_1769_ = v_fst_1844_;
goto v___jp_1768_;
}
}
}
}
v___jp_2045_:
{
uint8_t v___x_2047_; 
v___x_2047_ = lean_nat_dec_le(v___x_2043_, v___x_2044_);
if (v___x_2047_ == 0)
{
lean_dec(v___x_2043_);
v_lower_1996_ = v___y_2046_;
v_upper_1997_ = v___x_2044_;
goto v___jp_1995_;
}
else
{
v_lower_1996_ = v___y_2046_;
v_upper_1997_ = v___x_2043_;
goto v___jp_1995_;
}
}
}
}
else
{
lean_object* v___x_2050_; lean_object* v___x_2052_; 
lean_dec(v_fst_1844_);
lean_dec(v_fst_1843_);
v___x_2050_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_1847_ == 0)
{
lean_ctor_set_tag(v___x_1846_, 1);
lean_ctor_set(v___x_1846_, 1, v___x_2050_);
lean_ctor_set(v___x_1846_, 0, v_a_1767_);
v___x_2052_ = v___x_1846_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_1767_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
else
{
lean_object* v_fst_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2064_; 
lean_dec_ref(v___x_1839_);
lean_dec_ref(v_a_1767_);
v_fst_2056_ = lean_ctor_get(v_snd_1840_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_snd_1840_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; 
v_unused_2065_ = lean_ctor_get(v_snd_1840_, 1);
lean_dec(v_unused_2065_);
v___x_2058_ = v_snd_1840_;
v_isShared_2059_ = v_isSharedCheck_2064_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_fst_2056_);
lean_dec(v_snd_1840_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2064_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; lean_object* v___x_2062_; 
v___x_2060_ = lean_box(0);
if (v_isShared_2059_ == 0)
{
lean_ctor_set_tag(v___x_2058_, 1);
lean_ctor_set(v___x_2058_, 1, v___x_2060_);
v___x_2062_ = v___x_2058_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_fst_2056_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
v___jp_1768_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1));
v___x_1771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1771_, 0, v_pos_1769_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
return v___x_1771_;
}
v___jp_1772_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_1775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1775_, 0, v_pos_1773_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
return v___x_1775_;
}
v___jp_1776_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_1779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1779_, 0, v_pos_1777_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
return v___x_1779_;
}
v___jp_1785_:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1789_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2));
v___x_1790_ = l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go(v___y_1788_, v___x_1784_, v___x_1789_);
lean_dec_ref(v___y_1788_);
v___x_1791_ = lean_string_utf8_byte_size(v___x_1790_);
lean_inc_ref(v___x_1790_);
v___x_1792_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1790_);
lean_ctor_set(v___x_1792_, 1, v___x_1784_);
lean_ctor_set(v___x_1792_, 2, v___x_1791_);
v___x_1793_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(v___x_1792_, v___x_1791_);
lean_dec_ref_known(v___x_1792_, 3);
v___x_1794_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1790_);
lean_ctor_set(v___x_1794_, 1, v___x_1784_);
lean_ctor_set(v___x_1794_, 2, v___x_1793_);
v___x_1795_ = l_String_Slice_toString(v___x_1794_);
lean_dec_ref_known(v___x_1794_, 3);
v___x_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___y_1787_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
v___x_1797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___y_1786_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
return v___x_1797_;
}
v___jp_1798_:
{
lean_object* v___x_1802_; 
v___x_1802_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___y_1801_, v___y_1800_);
lean_dec(v___y_1801_);
if (lean_obj_tag(v___x_1802_) == 0)
{
if (lean_obj_tag(v___y_1799_) == 0)
{
lean_object* v_pos_1803_; lean_object* v_res_1804_; lean_object* v___x_1805_; 
v_pos_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_pos_1803_);
v_res_1804_ = lean_ctor_get(v___x_1802_, 1);
lean_inc(v_res_1804_);
lean_dec_ref_known(v___x_1802_, 2);
v___x_1805_ = l_ByteArray_empty;
v___y_1786_ = v_pos_1803_;
v___y_1787_ = v_res_1804_;
v___y_1788_ = v___x_1805_;
goto v___jp_1785_;
}
else
{
lean_object* v_pos_1806_; lean_object* v_res_1807_; lean_object* v_val_1808_; lean_object* v___x_1809_; 
v_pos_1806_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_pos_1806_);
v_res_1807_ = lean_ctor_get(v___x_1802_, 1);
lean_inc(v_res_1807_);
lean_dec_ref_known(v___x_1802_, 2);
v_val_1808_ = lean_ctor_get(v___y_1799_, 0);
lean_inc(v_val_1808_);
lean_dec_ref_known(v___y_1799_, 1);
v___x_1809_ = l_ByteSlice_toByteArray(v_val_1808_);
v___y_1786_ = v_pos_1806_;
v___y_1787_ = v_res_1807_;
v___y_1788_ = v___x_1809_;
goto v___jp_1785_;
}
}
else
{
lean_object* v_pos_1810_; lean_object* v_err_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec(v___y_1799_);
v_pos_1810_ = lean_ctor_get(v___x_1802_, 0);
v_err_1811_ = lean_ctor_get(v___x_1802_, 1);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1802_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_err_1811_);
lean_inc(v_pos_1810_);
lean_dec(v___x_1802_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_pos_1810_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_err_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
v___jp_1819_:
{
lean_object* v___x_1823_; 
v___x_1823_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_checkFieldValueLength(v_limits_1766_, v_res_1822_, v_pos_1821_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_pos_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
v_pos_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_pos_1824_);
lean_dec_ref_known(v___x_1823_, 2);
v___x_1825_ = l_ByteSlice_toByteArray(v___y_1820_);
v___x_1826_ = lean_string_validate_utf8(v___x_1825_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; 
lean_dec_ref(v___x_1825_);
v___x_1827_ = lean_box(0);
v___y_1799_ = v_res_1822_;
v___y_1800_ = v_pos_1824_;
v___y_1801_ = v___x_1827_;
goto v___jp_1798_;
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1828_ = lean_string_from_utf8_unchecked(v___x_1825_);
v___x_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
v___y_1799_ = v_res_1822_;
v___y_1800_ = v_pos_1824_;
v___y_1801_ = v___x_1829_;
goto v___jp_1798_;
}
}
else
{
lean_object* v_pos_1830_; lean_object* v_err_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
lean_dec(v_res_1822_);
lean_dec_ref(v___y_1820_);
v_pos_1830_ = lean_ctor_get(v___x_1823_, 0);
v_err_1831_ = lean_ctor_get(v___x_1823_, 1);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1823_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_err_1831_);
lean_inc(v_pos_1830_);
lean_dec(v___x_1823_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_pos_1830_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_err_1831_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___boxed(lean_object* v_limits_2066_, lean_object* v_a_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_2066_, v_a_2067_);
lean_dec_ref(v_limits_2066_);
return v_res_2068_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(lean_object* v_x_2069_, lean_object* v_x_2070_){
_start:
{
if (lean_obj_tag(v_x_2069_) == 0)
{
if (lean_obj_tag(v_x_2070_) == 0)
{
uint8_t v___x_2071_; 
v___x_2071_ = 1;
return v___x_2071_;
}
else
{
uint8_t v___x_2072_; 
v___x_2072_ = 0;
return v___x_2072_;
}
}
else
{
if (lean_obj_tag(v_x_2070_) == 0)
{
uint8_t v___x_2073_; 
v___x_2073_ = 0;
return v___x_2073_;
}
else
{
lean_object* v_val_2074_; lean_object* v_val_2075_; uint8_t v___x_2076_; uint8_t v___x_2077_; uint8_t v___x_2078_; 
v_val_2074_ = lean_ctor_get(v_x_2069_, 0);
v_val_2075_ = lean_ctor_get(v_x_2070_, 0);
v___x_2076_ = lean_unbox(v_val_2074_);
v___x_2077_ = lean_unbox(v_val_2075_);
v___x_2078_ = lean_uint8_dec_eq(v___x_2076_, v___x_2077_);
return v___x_2078_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0___boxed(lean_object* v_x_2079_, lean_object* v_x_2080_){
_start:
{
uint8_t v_res_2081_; lean_object* v_r_2082_; 
v_res_2081_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_x_2079_, v_x_2080_);
lean_dec(v_x_2080_);
lean_dec(v_x_2079_);
v_r_2082_ = lean_box(v_res_2081_);
return v_r_2082_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader(lean_object* v_limits_2089_, lean_object* v_a_2090_){
_start:
{
lean_object* v___y_2092_; lean_object* v_pos_2115_; lean_object* v_res_2116_; lean_object* v_array_2154_; lean_object* v_idx_2155_; lean_object* v___x_2156_; uint8_t v___x_2157_; 
v_array_2154_ = lean_ctor_get(v_a_2090_, 0);
v_idx_2155_ = lean_ctor_get(v_a_2090_, 1);
v___x_2156_ = lean_byte_array_size(v_array_2154_);
v___x_2157_ = lean_nat_dec_lt(v_idx_2155_, v___x_2156_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; 
v___x_2158_ = lean_box(0);
v_pos_2115_ = v_a_2090_;
v_res_2116_ = v___x_2158_;
goto v___jp_2114_;
}
else
{
uint8_t v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2159_ = lean_byte_array_fget(v_array_2154_, v_idx_2155_);
v___x_2160_ = lean_box(v___x_2159_);
v___x_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
v_pos_2115_ = v_a_2090_;
v_res_2116_ = v___x_2161_;
goto v___jp_2114_;
}
v___jp_2091_:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2094_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2093_, v___y_2092_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_pos_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2103_; 
v_pos_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2103_ == 0)
{
lean_object* v_unused_2104_; 
v_unused_2104_ = lean_ctor_get(v___x_2094_, 1);
lean_dec(v_unused_2104_);
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2103_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_pos_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2103_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2099_ = lean_box(0);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 1, v___x_2099_);
v___x_2101_ = v___x_2097_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_pos_2095_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
else
{
lean_object* v_pos_2105_; lean_object* v_err_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
v_pos_2105_ = lean_ctor_get(v___x_2094_, 0);
v_err_2106_ = lean_ctor_get(v___x_2094_, 1);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2094_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_err_2106_);
lean_inc(v_pos_2105_);
lean_dec(v___x_2094_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_pos_2105_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_err_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
v___jp_2114_:
{
lean_object* v___x_2117_; uint8_t v___x_2118_; 
v___x_2117_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseSingleHeader___closed__0));
v___x_2118_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_2116_, v___x_2117_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; uint8_t v___x_2120_; 
v___x_2119_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseSingleHeader___closed__1));
v___x_2120_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_2116_, v___x_2119_);
lean_dec(v_res_2116_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; 
v___x_2121_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_2089_, v_pos_2115_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_pos_2122_; lean_object* v_res_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v_pos_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_pos_2122_);
v_res_2123_ = lean_ctor_get(v___x_2121_, 1);
lean_inc(v_res_2123_);
lean_dec_ref_known(v___x_2121_, 2);
v___x_2124_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2125_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2124_, v_pos_2122_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_pos_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2134_; 
v_pos_2126_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2134_ == 0)
{
lean_object* v_unused_2135_; 
v_unused_2135_ = lean_ctor_get(v___x_2125_, 1);
lean_dec(v_unused_2135_);
v___x_2128_ = v___x_2125_;
v_isShared_2129_ = v_isSharedCheck_2134_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_pos_2126_);
lean_dec(v___x_2125_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2134_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2130_, 0, v_res_2123_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 1, v___x_2130_);
v___x_2132_ = v___x_2128_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_pos_2126_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v___x_2130_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
else
{
lean_object* v_pos_2136_; lean_object* v_err_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec(v_res_2123_);
v_pos_2136_ = lean_ctor_get(v___x_2125_, 0);
v_err_2137_ = lean_ctor_get(v___x_2125_, 1);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2125_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_err_2137_);
lean_inc(v_pos_2136_);
lean_dec(v___x_2125_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_pos_2136_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_err_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
else
{
lean_object* v_pos_2145_; lean_object* v_err_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
v_pos_2145_ = lean_ctor_get(v___x_2121_, 0);
v_err_2146_ = lean_ctor_get(v___x_2121_, 1);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2121_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_err_2146_);
lean_inc(v_pos_2145_);
lean_dec(v___x_2121_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_pos_2145_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_err_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
else
{
v___y_2092_ = v_pos_2115_;
goto v___jp_2091_;
}
}
else
{
lean_dec(v_res_2116_);
v___y_2092_ = v_pos_2115_;
goto v___jp_2091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader___boxed(lean_object* v_limits_2162_, lean_object* v_a_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_2162_, v_a_2163_);
lean_dec_ref(v_limits_2162_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseObsFoldContinuation(lean_object* v_limits_2165_, lean_object* v_a_2166_){
_start:
{
lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v_pos_2179_; lean_object* v_res_2180_; lean_object* v_pos_2209_; lean_object* v_pos_2213_; lean_object* v_maxHeaderValueLength_2216_; lean_object* v_maxSpaceSequence_2217_; lean_object* v___f_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v_snd_2221_; lean_object* v_snd_2222_; uint8_t v___x_2223_; 
v_maxHeaderValueLength_2216_ = lean_ctor_get(v_limits_2165_, 9);
v_maxSpaceSequence_2217_ = lean_ctor_get(v_limits_2165_, 10);
v___f_2218_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3));
v___x_2219_ = lean_unsigned_to_nat(0u);
v___x_2220_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2218_, v_maxSpaceSequence_2217_, v___x_2219_, v_a_2166_);
v_snd_2221_ = lean_ctor_get(v___x_2220_, 1);
lean_inc(v_snd_2221_);
lean_dec_ref(v___x_2220_);
v_snd_2222_ = lean_ctor_get(v_snd_2221_, 1);
v___x_2223_ = lean_unbox(v_snd_2222_);
if (v___x_2223_ == 0)
{
lean_object* v_fst_2224_; lean_object* v_array_2225_; lean_object* v_idx_2226_; lean_object* v_pos_2228_; lean_object* v_res_2229_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v_lower_2258_; lean_object* v_upper_2259_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___f_2269_; lean_object* v_pos_2271_; lean_object* v___x_2297_; uint8_t v___x_2298_; 
v_fst_2224_ = lean_ctor_get(v_snd_2221_, 0);
lean_inc(v_fst_2224_);
lean_dec(v_snd_2221_);
v_array_2225_ = lean_ctor_get(v_fst_2224_, 0);
v_idx_2226_ = lean_ctor_get(v_fst_2224_, 1);
v___f_2269_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4));
v___x_2297_ = lean_byte_array_size(v_array_2225_);
v___x_2298_ = lean_nat_dec_lt(v_idx_2226_, v___x_2297_);
if (v___x_2298_ == 0)
{
v_pos_2271_ = v_fst_2224_;
goto v___jp_2270_;
}
else
{
uint8_t v___x_2299_; uint32_t v___x_2300_; uint32_t v___x_2301_; uint8_t v___x_2302_; 
v___x_2299_ = lean_byte_array_fget(v_array_2225_, v_idx_2226_);
v___x_2300_ = lean_uint8_to_uint32(v___x_2299_);
v___x_2301_ = 32;
v___x_2302_ = lean_uint32_dec_eq(v___x_2300_, v___x_2301_);
if (v___x_2302_ == 0)
{
uint32_t v___x_2303_; uint8_t v___x_2304_; 
v___x_2303_ = 9;
v___x_2304_ = lean_uint32_dec_eq(v___x_2300_, v___x_2303_);
if (v___x_2304_ == 0)
{
v_pos_2271_ = v_fst_2224_;
goto v___jp_2270_;
}
else
{
v_pos_2213_ = v_fst_2224_;
goto v___jp_2212_;
}
}
else
{
v_pos_2213_ = v_fst_2224_;
goto v___jp_2212_;
}
}
v___jp_2227_:
{
lean_object* v___x_2230_; lean_object* v_snd_2231_; lean_object* v_snd_2232_; uint8_t v___x_2233_; 
v___x_2230_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2218_, v_maxSpaceSequence_2217_, v___x_2219_, v_pos_2228_);
v_snd_2231_ = lean_ctor_get(v___x_2230_, 1);
lean_inc(v_snd_2231_);
lean_dec_ref(v___x_2230_);
v_snd_2232_ = lean_ctor_get(v_snd_2231_, 1);
v___x_2233_ = lean_unbox(v_snd_2232_);
if (v___x_2233_ == 0)
{
lean_object* v_fst_2234_; lean_object* v_array_2235_; lean_object* v_idx_2236_; lean_object* v___x_2237_; uint8_t v___x_2238_; 
v_fst_2234_ = lean_ctor_get(v_snd_2231_, 0);
lean_inc(v_fst_2234_);
lean_dec(v_snd_2231_);
v_array_2235_ = lean_ctor_get(v_fst_2234_, 0);
v_idx_2236_ = lean_ctor_get(v_fst_2234_, 1);
v___x_2237_ = lean_byte_array_size(v_array_2235_);
v___x_2238_ = lean_nat_dec_lt(v_idx_2236_, v___x_2237_);
if (v___x_2238_ == 0)
{
v_pos_2179_ = v_fst_2234_;
v_res_2180_ = v_res_2229_;
goto v___jp_2178_;
}
else
{
uint8_t v___x_2239_; uint32_t v___x_2240_; uint32_t v___x_2241_; uint8_t v___x_2242_; 
v___x_2239_ = lean_byte_array_fget(v_array_2235_, v_idx_2236_);
v___x_2240_ = lean_uint8_to_uint32(v___x_2239_);
v___x_2241_ = 32;
v___x_2242_ = lean_uint32_dec_eq(v___x_2240_, v___x_2241_);
if (v___x_2242_ == 0)
{
uint32_t v___x_2243_; uint8_t v___x_2244_; 
v___x_2243_ = 9;
v___x_2244_ = lean_uint32_dec_eq(v___x_2240_, v___x_2243_);
if (v___x_2244_ == 0)
{
v_pos_2179_ = v_fst_2234_;
v_res_2180_ = v_res_2229_;
goto v___jp_2178_;
}
else
{
lean_dec(v_res_2229_);
v_pos_2209_ = v_fst_2234_;
goto v___jp_2208_;
}
}
else
{
lean_dec(v_res_2229_);
v_pos_2209_ = v_fst_2234_;
goto v___jp_2208_;
}
}
}
else
{
lean_object* v_fst_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2253_; 
lean_dec(v_res_2229_);
v_fst_2245_ = lean_ctor_get(v_snd_2231_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v_snd_2231_);
if (v_isSharedCheck_2253_ == 0)
{
lean_object* v_unused_2254_; 
v_unused_2254_ = lean_ctor_get(v_snd_2231_, 1);
lean_dec(v_unused_2254_);
v___x_2247_ = v_snd_2231_;
v_isShared_2248_ = v_isSharedCheck_2253_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_fst_2245_);
lean_dec(v_snd_2231_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2253_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2249_; lean_object* v___x_2251_; 
v___x_2249_ = lean_box(0);
if (v_isShared_2248_ == 0)
{
lean_ctor_set_tag(v___x_2247_, 1);
lean_ctor_set(v___x_2247_, 1, v___x_2249_);
v___x_2251_ = v___x_2247_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_fst_2245_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
v___jp_2255_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = l_ByteArray_toByteSlice(v___y_2256_, v_lower_2258_, v_upper_2259_);
v___x_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
v_pos_2228_ = v___y_2257_;
v_res_2229_ = v___x_2261_;
goto v___jp_2227_;
}
v___jp_2262_:
{
uint8_t v___x_2268_; 
v___x_2268_ = lean_nat_dec_le(v___y_2263_, v___y_2265_);
if (v___x_2268_ == 0)
{
lean_dec(v___y_2263_);
v___y_2256_ = v___y_2264_;
v___y_2257_ = v___y_2266_;
v_lower_2258_ = v___y_2267_;
v_upper_2259_ = v___y_2265_;
goto v___jp_2255_;
}
else
{
lean_dec(v___y_2265_);
v___y_2256_ = v___y_2264_;
v___y_2257_ = v___y_2266_;
v_lower_2258_ = v___y_2267_;
v_upper_2259_ = v___y_2263_;
goto v___jp_2255_;
}
}
v___jp_2270_:
{
lean_object* v___x_2272_; lean_object* v_snd_2273_; lean_object* v_snd_2274_; uint8_t v___x_2275_; 
lean_inc_ref(v_pos_2271_);
v___x_2272_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2269_, v_maxHeaderValueLength_2216_, v___x_2219_, v_pos_2271_);
v_snd_2273_ = lean_ctor_get(v___x_2272_, 1);
lean_inc(v_snd_2273_);
v_snd_2274_ = lean_ctor_get(v_snd_2273_, 1);
v___x_2275_ = lean_unbox(v_snd_2274_);
if (v___x_2275_ == 0)
{
lean_object* v_fst_2276_; lean_object* v_fst_2277_; lean_object* v_array_2278_; lean_object* v_idx_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; uint8_t v___x_2282_; 
v_fst_2276_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_fst_2276_);
lean_dec_ref(v___x_2272_);
v_fst_2277_ = lean_ctor_get(v_snd_2273_, 0);
lean_inc(v_fst_2277_);
lean_dec(v_snd_2273_);
v_array_2278_ = lean_ctor_get(v_pos_2271_, 0);
lean_inc_ref(v_array_2278_);
v_idx_2279_ = lean_ctor_get(v_pos_2271_, 1);
lean_inc(v_idx_2279_);
lean_dec_ref(v_pos_2271_);
v___x_2280_ = lean_nat_add(v_idx_2279_, v_fst_2276_);
lean_dec(v_fst_2276_);
v___x_2281_ = lean_byte_array_size(v_array_2278_);
v___x_2282_ = lean_nat_dec_le(v_idx_2279_, v___x_2219_);
if (v___x_2282_ == 0)
{
v___y_2263_ = v___x_2280_;
v___y_2264_ = v_array_2278_;
v___y_2265_ = v___x_2281_;
v___y_2266_ = v_fst_2277_;
v___y_2267_ = v_idx_2279_;
goto v___jp_2262_;
}
else
{
lean_dec(v_idx_2279_);
v___y_2263_ = v___x_2280_;
v___y_2264_ = v_array_2278_;
v___y_2265_ = v___x_2281_;
v___y_2266_ = v_fst_2277_;
v___y_2267_ = v___x_2219_;
goto v___jp_2262_;
}
}
else
{
lean_object* v_fst_2283_; lean_object* v_idx_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2295_; 
lean_dec_ref(v___x_2272_);
v_fst_2283_ = lean_ctor_get(v_snd_2273_, 0);
lean_inc(v_fst_2283_);
lean_dec(v_snd_2273_);
v_idx_2284_ = lean_ctor_get(v_pos_2271_, 1);
v_isSharedCheck_2295_ = !lean_is_exclusive(v_pos_2271_);
if (v_isSharedCheck_2295_ == 0)
{
lean_object* v_unused_2296_; 
v_unused_2296_ = lean_ctor_get(v_pos_2271_, 0);
lean_dec(v_unused_2296_);
v___x_2286_ = v_pos_2271_;
v_isShared_2287_ = v_isSharedCheck_2295_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_idx_2284_);
lean_dec(v_pos_2271_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2295_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v_idx_2288_; uint8_t v___x_2289_; 
v_idx_2288_ = lean_ctor_get(v_fst_2283_, 1);
v___x_2289_ = lean_nat_dec_eq(v_idx_2284_, v_idx_2288_);
lean_dec(v_idx_2284_);
if (v___x_2289_ == 0)
{
lean_object* v___x_2290_; lean_object* v___x_2292_; 
v___x_2290_ = lean_box(0);
if (v_isShared_2287_ == 0)
{
lean_ctor_set_tag(v___x_2286_, 1);
lean_ctor_set(v___x_2286_, 1, v___x_2290_);
lean_ctor_set(v___x_2286_, 0, v_fst_2283_);
v___x_2292_ = v___x_2286_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_fst_2283_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v___x_2290_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
else
{
lean_object* v___x_2294_; 
lean_del_object(v___x_2286_);
v___x_2294_ = lean_box(0);
v_pos_2228_ = v_fst_2283_;
v_res_2229_ = v___x_2294_;
goto v___jp_2227_;
}
}
}
}
}
else
{
lean_object* v_fst_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2313_; 
v_fst_2305_ = lean_ctor_get(v_snd_2221_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v_snd_2221_);
if (v_isSharedCheck_2313_ == 0)
{
lean_object* v_unused_2314_; 
v_unused_2314_ = lean_ctor_get(v_snd_2221_, 1);
lean_dec(v_unused_2314_);
v___x_2307_ = v_snd_2221_;
v_isShared_2308_ = v_isSharedCheck_2313_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_fst_2305_);
lean_dec(v_snd_2221_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2313_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2309_; lean_object* v___x_2311_; 
v___x_2309_ = lean_box(0);
if (v_isShared_2308_ == 0)
{
lean_ctor_set_tag(v___x_2307_, 1);
lean_ctor_set(v___x_2307_, 1, v___x_2309_);
v___x_2311_ = v___x_2307_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_fst_2305_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v___x_2309_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
v___jp_2167_:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2170_ = lean_unsigned_to_nat(0u);
v___x_2171_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2));
v___x_2172_ = l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go(v___y_2169_, v___x_2170_, v___x_2171_);
lean_dec_ref(v___y_2169_);
v___x_2173_ = lean_string_utf8_byte_size(v___x_2172_);
v___x_2174_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2172_);
lean_ctor_set(v___x_2174_, 1, v___x_2170_);
lean_ctor_set(v___x_2174_, 2, v___x_2173_);
v___x_2175_ = l_String_Slice_trimAscii(v___x_2174_);
v___x_2176_ = l_String_Slice_toString(v___x_2175_);
lean_dec_ref(v___x_2175_);
v___x_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___y_2168_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
return v___x_2177_;
}
v___jp_2178_:
{
lean_object* v___x_2181_; 
v___x_2181_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_checkFieldValueLength(v_limits_2165_, v_res_2180_, v_pos_2179_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_pos_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v_pos_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_pos_2182_);
lean_dec_ref_known(v___x_2181_, 2);
v___x_2183_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2184_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2183_, v_pos_2182_);
if (lean_obj_tag(v___x_2184_) == 0)
{
if (lean_obj_tag(v_res_2180_) == 0)
{
lean_object* v_pos_2185_; lean_object* v___x_2186_; 
v_pos_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_pos_2185_);
lean_dec_ref_known(v___x_2184_, 2);
v___x_2186_ = l_ByteArray_empty;
v___y_2168_ = v_pos_2185_;
v___y_2169_ = v___x_2186_;
goto v___jp_2167_;
}
else
{
lean_object* v_pos_2187_; lean_object* v_val_2188_; lean_object* v___x_2189_; 
v_pos_2187_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_pos_2187_);
lean_dec_ref_known(v___x_2184_, 2);
v_val_2188_ = lean_ctor_get(v_res_2180_, 0);
lean_inc(v_val_2188_);
lean_dec_ref_known(v_res_2180_, 1);
v___x_2189_ = l_ByteSlice_toByteArray(v_val_2188_);
v___y_2168_ = v_pos_2187_;
v___y_2169_ = v___x_2189_;
goto v___jp_2167_;
}
}
else
{
lean_object* v_pos_2190_; lean_object* v_err_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec(v_res_2180_);
v_pos_2190_ = lean_ctor_get(v___x_2184_, 0);
v_err_2191_ = lean_ctor_get(v___x_2184_, 1);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2184_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_err_2191_);
lean_inc(v_pos_2190_);
lean_dec(v___x_2184_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_pos_2190_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_err_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
else
{
lean_object* v_pos_2199_; lean_object* v_err_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec(v_res_2180_);
v_pos_2199_ = lean_ctor_get(v___x_2181_, 0);
v_err_2200_ = lean_ctor_get(v___x_2181_, 1);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2181_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_err_2200_);
lean_inc(v_pos_2199_);
lean_dec(v___x_2181_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_pos_2199_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_err_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
v___jp_2208_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2210_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2211_, 0, v_pos_2209_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
return v___x_2211_;
}
v___jp_2212_:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2214_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2215_, 0, v_pos_2213_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
return v___x_2215_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseObsFoldContinuation___boxed(lean_object* v_limits_2315_, lean_object* v_a_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Std_Http_Protocol_H1_parseObsFoldContinuation(v_limits_2315_, v_a_2316_);
lean_dec_ref(v_limits_2315_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair(lean_object* v_a_2322_){
_start:
{
lean_object* v_array_2323_; lean_object* v_idx_2324_; lean_object* v___x_2325_; uint8_t v___x_2326_; 
v_array_2323_ = lean_ctor_get(v_a_2322_, 0);
v_idx_2324_ = lean_ctor_get(v_a_2322_, 1);
v___x_2325_ = lean_byte_array_size(v_array_2323_);
v___x_2326_ = lean_nat_dec_lt(v_idx_2324_, v___x_2325_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = lean_box(0);
v___x_2328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2328_, 0, v_a_2322_);
lean_ctor_set(v___x_2328_, 1, v___x_2327_);
return v___x_2328_;
}
else
{
uint8_t v___x_2329_; uint8_t v_got_2330_; uint8_t v___x_2331_; 
v___x_2329_ = 92;
v_got_2330_ = lean_byte_array_fget(v_array_2323_, v_idx_2324_);
v___x_2331_ = lean_uint8_dec_eq(v_got_2330_, v___x_2329_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1));
v___x_2333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2333_, 0, v_a_2322_);
lean_ctor_set(v___x_2333_, 1, v___x_2332_);
return v___x_2333_;
}
else
{
lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2367_; 
lean_inc(v_idx_2324_);
lean_inc_ref(v_array_2323_);
v_isSharedCheck_2367_ = !lean_is_exclusive(v_a_2322_);
if (v_isSharedCheck_2367_ == 0)
{
lean_object* v_unused_2368_; lean_object* v_unused_2369_; 
v_unused_2368_ = lean_ctor_get(v_a_2322_, 1);
lean_dec(v_unused_2368_);
v_unused_2369_ = lean_ctor_get(v_a_2322_, 0);
lean_dec(v_unused_2369_);
v___x_2335_ = v_a_2322_;
v_isShared_2336_ = v_isSharedCheck_2367_;
goto v_resetjp_2334_;
}
else
{
lean_dec(v_a_2322_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2367_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; uint8_t v___x_2339_; 
v___x_2337_ = lean_unsigned_to_nat(1u);
v___x_2338_ = lean_nat_add(v_idx_2324_, v___x_2337_);
lean_dec(v_idx_2324_);
v___x_2339_ = lean_nat_dec_lt(v___x_2338_, v___x_2325_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2341_; 
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 1, v___x_2338_);
v___x_2341_ = v___x_2335_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_array_2323_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v___x_2338_);
v___x_2341_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = lean_box(0);
v___x_2343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2341_);
lean_ctor_set(v___x_2343_, 1, v___x_2342_);
return v___x_2343_;
}
}
else
{
uint8_t v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2348_; 
v___x_2345_ = lean_byte_array_fget(v_array_2323_, v___x_2338_);
v___x_2346_ = lean_nat_add(v___x_2338_, v___x_2337_);
lean_dec(v___x_2338_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 1, v___x_2346_);
v___x_2348_ = v___x_2335_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_array_2323_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v___x_2346_);
v___x_2348_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; uint32_t v___x_2351_; uint32_t v___x_2358_; uint8_t v___x_2359_; 
v___x_2349_ = lean_box(v___x_2345_);
lean_inc_ref(v___x_2348_);
v___x_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2348_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
v___x_2351_ = lean_uint8_to_uint32(v___x_2345_);
v___x_2358_ = 9;
v___x_2359_ = lean_uint32_dec_eq(v___x_2351_, v___x_2358_);
if (v___x_2359_ == 0)
{
uint32_t v___x_2360_; uint8_t v___x_2361_; 
v___x_2360_ = 32;
v___x_2361_ = lean_uint32_dec_eq(v___x_2351_, v___x_2360_);
if (v___x_2361_ == 0)
{
uint32_t v___x_2362_; uint8_t v___x_2363_; 
v___x_2362_ = 33;
v___x_2363_ = lean_uint32_dec_le(v___x_2362_, v___x_2351_);
if (v___x_2363_ == 0)
{
lean_dec_ref_known(v___x_2350_, 2);
goto v___jp_2352_;
}
else
{
uint32_t v___x_2364_; uint8_t v___x_2365_; 
v___x_2364_ = 126;
v___x_2365_ = lean_uint32_dec_le(v___x_2351_, v___x_2364_);
if (v___x_2365_ == 0)
{
lean_dec_ref_known(v___x_2350_, 2);
goto v___jp_2352_;
}
else
{
lean_dec_ref(v___x_2348_);
return v___x_2350_;
}
}
}
else
{
lean_dec_ref(v___x_2348_);
return v___x_2350_;
}
}
else
{
lean_dec_ref(v___x_2348_);
return v___x_2350_;
}
v___jp_2352_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2353_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2));
v___x_2354_ = l_Char_quote(v___x_2351_);
v___x_2355_ = lean_string_append(v___x_2353_, v___x_2354_);
lean_dec_ref(v___x_2354_);
v___x_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
v___x_2357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2348_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
return v___x_2357_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(lean_object* v_maxLength_2374_, lean_object* v_buf_2375_, lean_object* v_length_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v_array_2378_; lean_object* v_idx_2379_; lean_object* v___x_2380_; uint8_t v___x_2381_; 
v_array_2378_ = lean_ctor_get(v_a_2377_, 0);
v_idx_2379_ = lean_ctor_get(v_a_2377_, 1);
v___x_2380_ = lean_byte_array_size(v_array_2378_);
v___x_2381_ = lean_nat_dec_lt(v_idx_2379_, v___x_2380_);
if (v___x_2381_ == 0)
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
lean_dec(v_length_2376_);
lean_dec_ref(v_buf_2375_);
v___x_2382_ = lean_box(0);
v___x_2383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2383_, 0, v_a_2377_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
return v___x_2383_;
}
else
{
lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2460_; 
lean_inc(v_idx_2379_);
lean_inc_ref(v_array_2378_);
v_isSharedCheck_2460_ = !lean_is_exclusive(v_a_2377_);
if (v_isSharedCheck_2460_ == 0)
{
lean_object* v_unused_2461_; lean_object* v_unused_2462_; 
v_unused_2461_ = lean_ctor_get(v_a_2377_, 1);
lean_dec(v_unused_2461_);
v_unused_2462_ = lean_ctor_get(v_a_2377_, 0);
lean_dec(v_unused_2462_);
v___x_2385_ = v_a_2377_;
v_isShared_2386_ = v_isSharedCheck_2460_;
goto v_resetjp_2384_;
}
else
{
lean_dec(v_a_2377_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2460_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
uint8_t v_c_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v_it_x27_2391_; 
v_c_2387_ = lean_byte_array_fget(v_array_2378_, v_idx_2379_);
v___x_2388_ = lean_unsigned_to_nat(1u);
v___x_2389_ = lean_nat_add(v_idx_2379_, v___x_2388_);
lean_dec(v_idx_2379_);
lean_inc(v___x_2389_);
lean_inc_ref(v_array_2378_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 1, v___x_2389_);
v_it_x27_2391_ = v___x_2385_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_array_2378_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v___x_2389_);
v_it_x27_2391_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
uint8_t v___x_2408_; uint8_t v___x_2409_; 
v___x_2408_ = 34;
v___x_2409_ = lean_uint8_dec_eq(v_c_2387_, v___x_2408_);
if (v___x_2409_ == 0)
{
uint8_t v___x_2410_; uint8_t v___x_2411_; 
v___x_2410_ = 92;
v___x_2411_ = lean_uint8_dec_eq(v_c_2387_, v___x_2410_);
if (v___x_2411_ == 0)
{
uint32_t v___x_2412_; uint32_t v___x_2418_; uint8_t v___x_2419_; 
lean_dec(v___x_2389_);
lean_dec_ref(v_array_2378_);
v___x_2412_ = lean_uint8_to_uint32(v_c_2387_);
v___x_2418_ = 9;
v___x_2419_ = lean_uint32_dec_eq(v___x_2412_, v___x_2418_);
if (v___x_2419_ == 0)
{
uint32_t v___x_2420_; uint8_t v___x_2421_; 
v___x_2420_ = 32;
v___x_2421_ = lean_uint32_dec_eq(v___x_2412_, v___x_2420_);
if (v___x_2421_ == 0)
{
uint32_t v___x_2422_; uint8_t v___x_2423_; 
v___x_2422_ = 33;
v___x_2423_ = lean_uint32_dec_eq(v___x_2412_, v___x_2422_);
if (v___x_2423_ == 0)
{
uint32_t v___x_2424_; uint8_t v___x_2425_; 
v___x_2424_ = 35;
v___x_2425_ = lean_uint32_dec_le(v___x_2424_, v___x_2412_);
if (v___x_2425_ == 0)
{
goto v___jp_2413_;
}
else
{
uint32_t v___x_2426_; uint8_t v___x_2427_; 
v___x_2426_ = 91;
v___x_2427_ = lean_uint32_dec_le(v___x_2412_, v___x_2426_);
if (v___x_2427_ == 0)
{
goto v___jp_2413_;
}
else
{
goto v___jp_2392_;
}
}
}
else
{
goto v___jp_2392_;
}
}
else
{
goto v___jp_2392_;
}
}
else
{
goto v___jp_2392_;
}
v___jp_2413_:
{
uint32_t v___x_2414_; uint8_t v___x_2415_; 
v___x_2414_ = 93;
v___x_2415_ = lean_uint32_dec_le(v___x_2414_, v___x_2412_);
if (v___x_2415_ == 0)
{
goto v___jp_2399_;
}
else
{
uint32_t v___x_2416_; uint8_t v___x_2417_; 
v___x_2416_ = 126;
v___x_2417_ = lean_uint32_dec_le(v___x_2412_, v___x_2416_);
if (v___x_2417_ == 0)
{
goto v___jp_2399_;
}
else
{
goto v___jp_2392_;
}
}
}
}
else
{
uint8_t v___x_2428_; 
v___x_2428_ = lean_nat_dec_lt(v___x_2389_, v___x_2380_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2429_; lean_object* v___x_2430_; 
lean_dec(v___x_2389_);
lean_dec_ref(v_array_2378_);
lean_dec(v_length_2376_);
lean_dec_ref(v_buf_2375_);
v___x_2429_ = lean_box(0);
v___x_2430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2430_, 0, v_it_x27_2391_);
lean_ctor_set(v___x_2430_, 1, v___x_2429_);
return v___x_2430_;
}
else
{
uint8_t v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; uint32_t v___x_2441_; uint32_t v___x_2450_; uint8_t v___x_2451_; 
lean_dec_ref(v_it_x27_2391_);
v___x_2431_ = lean_byte_array_fget(v_array_2378_, v___x_2389_);
v___x_2432_ = lean_nat_add(v___x_2389_, v___x_2388_);
lean_dec(v___x_2389_);
v___x_2433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2433_, 0, v_array_2378_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2441_ = lean_uint8_to_uint32(v___x_2431_);
v___x_2450_ = 9;
v___x_2451_ = lean_uint32_dec_eq(v___x_2441_, v___x_2450_);
if (v___x_2451_ == 0)
{
uint32_t v___x_2452_; uint8_t v___x_2453_; 
v___x_2452_ = 32;
v___x_2453_ = lean_uint32_dec_eq(v___x_2441_, v___x_2452_);
if (v___x_2453_ == 0)
{
uint32_t v___x_2454_; uint8_t v___x_2455_; 
v___x_2454_ = 33;
v___x_2455_ = lean_uint32_dec_le(v___x_2454_, v___x_2441_);
if (v___x_2455_ == 0)
{
goto v___jp_2442_;
}
else
{
uint32_t v___x_2456_; uint8_t v___x_2457_; 
v___x_2456_ = 126;
v___x_2457_ = lean_uint32_dec_le(v___x_2441_, v___x_2456_);
if (v___x_2457_ == 0)
{
goto v___jp_2442_;
}
else
{
goto v___jp_2434_;
}
}
}
else
{
goto v___jp_2434_;
}
}
else
{
goto v___jp_2434_;
}
v___jp_2434_:
{
lean_object* v___x_2435_; uint8_t v___x_2436_; 
v___x_2435_ = lean_nat_add(v_length_2376_, v___x_2388_);
lean_dec(v_length_2376_);
v___x_2436_ = lean_nat_dec_lt(v_maxLength_2374_, v___x_2435_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2437_; 
v___x_2437_ = lean_byte_array_push(v_buf_2375_, v___x_2431_);
v_buf_2375_ = v___x_2437_;
v_length_2376_ = v___x_2435_;
v_a_2377_ = v___x_2433_;
goto _start;
}
else
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
lean_dec(v___x_2435_);
lean_dec_ref(v_buf_2375_);
v___x_2439_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_2440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2433_);
lean_ctor_set(v___x_2440_, 1, v___x_2439_);
return v___x_2440_;
}
}
v___jp_2442_:
{
uint8_t v___x_2443_; uint8_t v___x_2444_; 
v___x_2443_ = 128;
v___x_2444_ = lean_uint8_dec_le(v___x_2443_, v___x_2431_);
if (v___x_2444_ == 0)
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
lean_dec(v_length_2376_);
lean_dec_ref(v_buf_2375_);
v___x_2445_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2));
v___x_2446_ = l_Char_quote(v___x_2441_);
v___x_2447_ = lean_string_append(v___x_2445_, v___x_2446_);
lean_dec_ref(v___x_2446_);
v___x_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
v___x_2449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2433_);
lean_ctor_set(v___x_2449_, 1, v___x_2448_);
return v___x_2449_;
}
else
{
goto v___jp_2434_;
}
}
}
}
}
else
{
lean_object* v___x_2458_; 
lean_dec(v___x_2389_);
lean_dec_ref(v_array_2378_);
lean_dec(v_length_2376_);
v___x_2458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2458_, 0, v_it_x27_2391_);
lean_ctor_set(v___x_2458_, 1, v_buf_2375_);
return v___x_2458_;
}
v___jp_2392_:
{
lean_object* v___x_2393_; uint8_t v___x_2394_; 
v___x_2393_ = lean_nat_add(v_length_2376_, v___x_2388_);
lean_dec(v_length_2376_);
v___x_2394_ = lean_nat_dec_lt(v_maxLength_2374_, v___x_2393_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; 
v___x_2395_ = lean_byte_array_push(v_buf_2375_, v_c_2387_);
v_buf_2375_ = v___x_2395_;
v_length_2376_ = v___x_2393_;
v_a_2377_ = v_it_x27_2391_;
goto _start;
}
else
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
lean_dec(v___x_2393_);
lean_dec_ref(v_buf_2375_);
v___x_2397_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_2398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2398_, 0, v_it_x27_2391_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
return v___x_2398_;
}
}
v___jp_2399_:
{
uint8_t v___x_2400_; uint8_t v___x_2401_; 
v___x_2400_ = 128;
v___x_2401_ = lean_uint8_dec_le(v___x_2400_, v_c_2387_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2402_; uint32_t v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
lean_dec(v_length_2376_);
lean_dec_ref(v_buf_2375_);
v___x_2402_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2));
v___x_2403_ = lean_uint8_to_uint32(v_c_2387_);
v___x_2404_ = l_Char_quote(v___x_2403_);
v___x_2405_ = lean_string_append(v___x_2402_, v___x_2404_);
lean_dec_ref(v___x_2404_);
v___x_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
v___x_2407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2407_, 0, v_it_x27_2391_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
return v___x_2407_;
}
else
{
goto v___jp_2392_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___boxed(lean_object* v_maxLength_2463_, lean_object* v_buf_2464_, lean_object* v_length_2465_, lean_object* v_a_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_2463_, v_buf_2464_, v_length_2465_, v_a_2466_);
lean_dec(v_maxLength_2463_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(lean_object* v_maxLength_2471_, lean_object* v_a_2472_){
_start:
{
lean_object* v_array_2473_; lean_object* v_idx_2474_; lean_object* v___x_2475_; uint8_t v___x_2476_; 
v_array_2473_ = lean_ctor_get(v_a_2472_, 0);
v_idx_2474_ = lean_ctor_get(v_a_2472_, 1);
v___x_2475_ = lean_byte_array_size(v_array_2473_);
v___x_2476_ = lean_nat_dec_lt(v_idx_2474_, v___x_2475_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2477_ = lean_box(0);
v___x_2478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2478_, 0, v_a_2472_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
return v___x_2478_;
}
else
{
uint8_t v___x_2479_; uint8_t v_got_2480_; uint8_t v___x_2481_; 
v___x_2479_ = 34;
v_got_2480_ = lean_byte_array_fget(v_array_2473_, v_idx_2474_);
v___x_2481_ = lean_uint8_dec_eq(v_got_2480_, v___x_2479_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1));
v___x_2483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2483_, 0, v_a_2472_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
return v___x_2483_;
}
else
{
lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2495_; 
lean_inc(v_idx_2474_);
lean_inc_ref(v_array_2473_);
v_isSharedCheck_2495_ = !lean_is_exclusive(v_a_2472_);
if (v_isSharedCheck_2495_ == 0)
{
lean_object* v_unused_2496_; lean_object* v_unused_2497_; 
v_unused_2496_ = lean_ctor_get(v_a_2472_, 1);
lean_dec(v_unused_2496_);
v_unused_2497_ = lean_ctor_get(v_a_2472_, 0);
lean_dec(v_unused_2497_);
v___x_2485_ = v_a_2472_;
v_isShared_2486_ = v_isSharedCheck_2495_;
goto v_resetjp_2484_;
}
else
{
lean_dec(v_a_2472_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2495_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2490_; 
v___x_2487_ = lean_unsigned_to_nat(1u);
v___x_2488_ = lean_nat_add(v_idx_2474_, v___x_2487_);
lean_dec(v_idx_2474_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 1, v___x_2488_);
v___x_2490_ = v___x_2485_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_array_2473_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v___x_2488_);
v___x_2490_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2491_ = l_ByteArray_empty;
v___x_2492_ = lean_unsigned_to_nat(0u);
v___x_2493_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_2471_, v___x_2491_, v___x_2492_, v___x_2490_);
return v___x_2493_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___boxed(lean_object* v_maxLength_2498_, lean_object* v_a_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxLength_2498_, v_a_2499_);
lean_dec(v_maxLength_2498_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(lean_object* v_limits_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v_pos_2513_; lean_object* v___y_2517_; lean_object* v_pos_2518_; lean_object* v_res_2519_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v_lower_2550_; lean_object* v_upper_2551_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2567_; lean_object* v___y_2571_; lean_object* v_pos_2572_; lean_object* v_pos_2578_; lean_object* v_pos_2582_; lean_object* v_maxSpaceSequence_2585_; lean_object* v_maxChunkExtNameLength_2586_; lean_object* v_maxChunkExtValueLength_2587_; lean_object* v___f_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v_snd_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2876_; 
v_maxSpaceSequence_2585_ = lean_ctor_get(v_limits_2510_, 10);
v_maxChunkExtNameLength_2586_ = lean_ctor_get(v_limits_2510_, 13);
v_maxChunkExtValueLength_2587_ = lean_ctor_get(v_limits_2510_, 14);
v___f_2588_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3));
v___x_2589_ = lean_unsigned_to_nat(0u);
v___x_2590_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2588_, v_maxSpaceSequence_2585_, v___x_2589_, v_a_2511_);
v_snd_2591_ = lean_ctor_get(v___x_2590_, 1);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2876_ == 0)
{
lean_object* v_unused_2877_; 
v_unused_2877_ = lean_ctor_get(v___x_2590_, 0);
lean_dec(v_unused_2877_);
v___x_2593_ = v___x_2590_;
v_isShared_2594_ = v_isSharedCheck_2876_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_snd_2591_);
lean_dec(v___x_2590_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2876_;
goto v_resetjp_2592_;
}
v___jp_2512_:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2515_, 0, v_pos_2513_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
return v___x_2515_;
}
v___jp_2516_:
{
lean_object* v___x_2520_; 
v___x_2520_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_2519_, v_pos_2518_);
lean_dec(v_res_2519_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_pos_2521_; lean_object* v_res_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2536_; 
v_pos_2521_ = lean_ctor_get(v___x_2520_, 0);
v_res_2522_ = lean_ctor_get(v___x_2520_, 1);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2524_ = v___x_2520_;
v_isShared_2525_ = v_isSharedCheck_2536_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_res_2522_);
lean_inc(v_pos_2521_);
lean_dec(v___x_2520_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2536_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Std_Http_Chunk_ExtensionValue_ofString_x3f(v_res_2522_);
if (lean_obj_tag(v___x_2526_) == 1)
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2530_; 
v___x_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___y_2517_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
v___x_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 1, v___x_2528_);
v___x_2530_ = v___x_2524_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_pos_2521_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v___x_2528_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
else
{
lean_object* v___x_2532_; lean_object* v___x_2534_; 
lean_dec(v___x_2526_);
lean_dec_ref(v___y_2517_);
v___x_2532_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1));
if (v_isShared_2525_ == 0)
{
lean_ctor_set_tag(v___x_2524_, 1);
lean_ctor_set(v___x_2524_, 1, v___x_2532_);
v___x_2534_ = v___x_2524_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_pos_2521_);
lean_ctor_set(v_reuseFailAlloc_2535_, 1, v___x_2532_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
else
{
lean_object* v_pos_2537_; lean_object* v_err_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec_ref(v___y_2517_);
v_pos_2537_ = lean_ctor_get(v___x_2520_, 0);
v_err_2538_ = lean_ctor_get(v___x_2520_, 1);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2520_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_err_2538_);
lean_inc(v_pos_2537_);
lean_dec(v___x_2520_);
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
lean_object* v___x_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; 
v___x_2552_ = l_ByteArray_toByteSlice(v___y_2547_, v_lower_2550_, v_upper_2551_);
v___x_2553_ = l_ByteSlice_toByteArray(v___x_2552_);
v___x_2554_ = lean_string_validate_utf8(v___x_2553_);
if (v___x_2554_ == 0)
{
lean_object* v___x_2555_; 
lean_dec_ref(v___x_2553_);
v___x_2555_ = lean_box(0);
v___y_2517_ = v___y_2549_;
v_pos_2518_ = v___y_2548_;
v_res_2519_ = v___x_2555_;
goto v___jp_2516_;
}
else
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2556_ = lean_string_from_utf8_unchecked(v___x_2553_);
v___x_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2556_);
v___y_2517_ = v___y_2549_;
v_pos_2518_ = v___y_2548_;
v_res_2519_ = v___x_2557_;
goto v___jp_2516_;
}
}
v___jp_2558_:
{
uint8_t v___x_2565_; 
v___x_2565_ = lean_nat_dec_le(v___y_2562_, v___y_2560_);
if (v___x_2565_ == 0)
{
lean_dec(v___y_2562_);
v___y_2547_ = v___y_2559_;
v___y_2548_ = v___y_2561_;
v___y_2549_ = v___y_2563_;
v_lower_2550_ = v___y_2564_;
v_upper_2551_ = v___y_2560_;
goto v___jp_2546_;
}
else
{
lean_dec(v___y_2560_);
v___y_2547_ = v___y_2559_;
v___y_2548_ = v___y_2561_;
v___y_2549_ = v___y_2563_;
v_lower_2550_ = v___y_2564_;
v_upper_2551_ = v___y_2562_;
goto v___jp_2546_;
}
}
v___jp_2566_:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2568_ = lean_box(0);
v___x_2569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2569_, 0, v___y_2567_);
lean_ctor_set(v___x_2569_, 1, v___x_2568_);
return v___x_2569_;
}
v___jp_2570_:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2573_ = lean_box(0);
v___x_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___y_2571_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v___x_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
v___x_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2576_, 0, v_pos_2572_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
return v___x_2576_;
}
v___jp_2577_:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2579_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2580_, 0, v_pos_2578_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
return v___x_2580_;
}
v___jp_2581_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2584_, 0, v_pos_2582_);
lean_ctor_set(v___x_2584_, 1, v___x_2583_);
return v___x_2584_;
}
v_resetjp_2592_:
{
lean_object* v_snd_2595_; uint8_t v___x_2596_; 
v_snd_2595_ = lean_ctor_get(v_snd_2591_, 1);
v___x_2596_ = lean_unbox(v_snd_2595_);
if (v___x_2596_ == 0)
{
lean_object* v_fst_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2869_; 
v_fst_2597_ = lean_ctor_get(v_snd_2591_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v_snd_2591_);
if (v_isSharedCheck_2869_ == 0)
{
lean_object* v_unused_2870_; 
v_unused_2870_ = lean_ctor_get(v_snd_2591_, 1);
lean_dec(v_unused_2870_);
v___x_2599_ = v_snd_2591_;
v_isShared_2600_ = v_isSharedCheck_2869_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_fst_2597_);
lean_dec(v_snd_2591_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2869_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v_array_2601_; lean_object* v_idx_2602_; lean_object* v___f_2603_; lean_object* v___y_2605_; lean_object* v_pos_2606_; lean_object* v___y_2639_; lean_object* v_pos_2640_; lean_object* v_array_2641_; lean_object* v_idx_2642_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v_pos_2684_; lean_object* v_array_2685_; lean_object* v_idx_2686_; lean_object* v_pos_2727_; lean_object* v_res_2728_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v_lower_2774_; lean_object* v_upper_2775_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v_pos_2790_; lean_object* v_pos_2823_; lean_object* v___x_2861_; uint8_t v___x_2862_; 
v_array_2601_ = lean_ctor_get(v_fst_2597_, 0);
v_idx_2602_ = lean_ctor_get(v_fst_2597_, 1);
v___f_2603_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_2861_ = lean_byte_array_size(v_array_2601_);
v___x_2862_ = lean_nat_dec_lt(v_idx_2602_, v___x_2861_);
if (v___x_2862_ == 0)
{
lean_inc(v_idx_2602_);
lean_inc_ref(v_array_2601_);
v_pos_2823_ = v_fst_2597_;
goto v___jp_2822_;
}
else
{
uint8_t v___x_2863_; uint32_t v___x_2864_; uint32_t v___x_2865_; uint8_t v___x_2866_; 
v___x_2863_ = lean_byte_array_fget(v_array_2601_, v_idx_2602_);
v___x_2864_ = lean_uint8_to_uint32(v___x_2863_);
v___x_2865_ = 32;
v___x_2866_ = lean_uint32_dec_eq(v___x_2864_, v___x_2865_);
if (v___x_2866_ == 0)
{
uint32_t v___x_2867_; uint8_t v___x_2868_; 
v___x_2867_ = 9;
v___x_2868_ = lean_uint32_dec_eq(v___x_2864_, v___x_2867_);
if (v___x_2868_ == 0)
{
lean_inc(v_idx_2602_);
lean_inc_ref(v_array_2601_);
v_pos_2823_ = v_fst_2597_;
goto v___jp_2822_;
}
else
{
lean_del_object(v___x_2599_);
lean_del_object(v___x_2593_);
v_pos_2582_ = v_fst_2597_;
goto v___jp_2581_;
}
}
else
{
lean_del_object(v___x_2599_);
lean_del_object(v___x_2593_);
v_pos_2582_ = v_fst_2597_;
goto v___jp_2581_;
}
}
v___jp_2604_:
{
lean_object* v___x_2607_; lean_object* v_snd_2608_; lean_object* v_snd_2609_; uint8_t v___x_2610_; 
lean_inc_ref(v_pos_2606_);
v___x_2607_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2603_, v_maxChunkExtValueLength_2587_, v___x_2589_, v_pos_2606_);
v_snd_2608_ = lean_ctor_get(v___x_2607_, 1);
lean_inc(v_snd_2608_);
v_snd_2609_ = lean_ctor_get(v_snd_2608_, 1);
v___x_2610_ = lean_unbox(v_snd_2609_);
if (v___x_2610_ == 0)
{
lean_object* v_fst_2611_; lean_object* v_fst_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2626_; 
v_fst_2611_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_fst_2611_);
lean_dec_ref(v___x_2607_);
v_fst_2612_ = lean_ctor_get(v_snd_2608_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v_snd_2608_);
if (v_isSharedCheck_2626_ == 0)
{
lean_object* v_unused_2627_; 
v_unused_2627_ = lean_ctor_get(v_snd_2608_, 1);
lean_dec(v_unused_2627_);
v___x_2614_ = v_snd_2608_;
v_isShared_2615_ = v_isSharedCheck_2626_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_fst_2612_);
lean_dec(v_snd_2608_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2626_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
uint8_t v___x_2616_; 
v___x_2616_ = lean_nat_dec_eq(v_fst_2611_, v___x_2589_);
if (v___x_2616_ == 0)
{
lean_object* v_array_2617_; lean_object* v_idx_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; 
lean_del_object(v___x_2614_);
v_array_2617_ = lean_ctor_get(v_pos_2606_, 0);
lean_inc_ref(v_array_2617_);
v_idx_2618_ = lean_ctor_get(v_pos_2606_, 1);
lean_inc(v_idx_2618_);
lean_dec_ref(v_pos_2606_);
v___x_2619_ = lean_nat_add(v_idx_2618_, v_fst_2611_);
lean_dec(v_fst_2611_);
v___x_2620_ = lean_byte_array_size(v_array_2617_);
v___x_2621_ = lean_nat_dec_le(v_idx_2618_, v___x_2589_);
if (v___x_2621_ == 0)
{
v___y_2559_ = v_array_2617_;
v___y_2560_ = v___x_2620_;
v___y_2561_ = v_fst_2612_;
v___y_2562_ = v___x_2619_;
v___y_2563_ = v___y_2605_;
v___y_2564_ = v_idx_2618_;
goto v___jp_2558_;
}
else
{
lean_dec(v_idx_2618_);
v___y_2559_ = v_array_2617_;
v___y_2560_ = v___x_2620_;
v___y_2561_ = v_fst_2612_;
v___y_2562_ = v___x_2619_;
v___y_2563_ = v___y_2605_;
v___y_2564_ = v___x_2589_;
goto v___jp_2558_;
}
}
else
{
lean_object* v___x_2622_; lean_object* v___x_2624_; 
lean_dec(v_fst_2612_);
lean_dec(v_fst_2611_);
lean_dec_ref(v___y_2605_);
v___x_2622_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_2615_ == 0)
{
lean_ctor_set_tag(v___x_2614_, 1);
lean_ctor_set(v___x_2614_, 1, v___x_2622_);
lean_ctor_set(v___x_2614_, 0, v_pos_2606_);
v___x_2624_ = v___x_2614_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_pos_2606_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v___x_2622_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
else
{
lean_object* v_fst_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2636_; 
lean_dec_ref(v___x_2607_);
lean_dec_ref(v_pos_2606_);
lean_dec_ref(v___y_2605_);
v_fst_2628_ = lean_ctor_get(v_snd_2608_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v_snd_2608_);
if (v_isSharedCheck_2636_ == 0)
{
lean_object* v_unused_2637_; 
v_unused_2637_ = lean_ctor_get(v_snd_2608_, 1);
lean_dec(v_unused_2637_);
v___x_2630_ = v_snd_2608_;
v_isShared_2631_ = v_isSharedCheck_2636_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_fst_2628_);
lean_dec(v_snd_2608_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2636_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; lean_object* v___x_2634_; 
v___x_2632_ = lean_box(0);
if (v_isShared_2631_ == 0)
{
lean_ctor_set_tag(v___x_2630_, 1);
lean_ctor_set(v___x_2630_, 1, v___x_2632_);
v___x_2634_ = v___x_2630_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_fst_2628_);
lean_ctor_set(v_reuseFailAlloc_2635_, 1, v___x_2632_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
v___jp_2638_:
{
lean_object* v___x_2643_; uint8_t v___x_2644_; 
v___x_2643_ = lean_byte_array_size(v_array_2641_);
v___x_2644_ = lean_nat_dec_lt(v_idx_2642_, v___x_2643_);
if (v___x_2644_ == 0)
{
lean_dec(v_idx_2642_);
lean_dec_ref(v_array_2641_);
lean_del_object(v___x_2599_);
v___y_2605_ = v___y_2639_;
v_pos_2606_ = v_pos_2640_;
goto v___jp_2604_;
}
else
{
uint8_t v___x_2645_; uint8_t v___x_2646_; uint8_t v___x_2647_; 
v___x_2645_ = lean_byte_array_fget(v_array_2641_, v_idx_2642_);
lean_dec(v_idx_2642_);
lean_dec_ref(v_array_2641_);
v___x_2646_ = 34;
v___x_2647_ = lean_uint8_dec_eq(v___x_2645_, v___x_2646_);
if (v___x_2647_ == 0)
{
lean_del_object(v___x_2599_);
v___y_2605_ = v___y_2639_;
v_pos_2606_ = v_pos_2640_;
goto v___jp_2604_;
}
else
{
lean_object* v___x_2648_; 
v___x_2648_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxChunkExtValueLength_2587_, v_pos_2640_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_pos_2649_; lean_object* v_res_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2671_; 
v_pos_2649_ = lean_ctor_get(v___x_2648_, 0);
v_res_2650_ = lean_ctor_get(v___x_2648_, 1);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2652_ = v___x_2648_;
v_isShared_2653_ = v_isSharedCheck_2671_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_res_2650_);
lean_inc(v_pos_2649_);
lean_dec(v___x_2648_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2671_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
uint8_t v___x_2654_; 
v___x_2654_ = lean_string_validate_utf8(v_res_2650_);
if (v___x_2654_ == 0)
{
lean_del_object(v___x_2652_);
lean_dec(v_res_2650_);
lean_dec_ref(v___y_2639_);
lean_del_object(v___x_2599_);
v___y_2567_ = v_pos_2649_;
goto v___jp_2566_;
}
else
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2655_ = lean_string_from_utf8_unchecked(v_res_2650_);
v___x_2656_ = l_Std_Http_Chunk_ExtensionValue_ofString_x3f(v___x_2655_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_del_object(v___x_2652_);
lean_dec_ref(v___y_2639_);
lean_del_object(v___x_2599_);
v___y_2567_ = v_pos_2649_;
goto v___jp_2566_;
}
else
{
lean_object* v___x_2658_; 
lean_inc_ref(v___x_2656_);
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 1, v___x_2656_);
lean_ctor_set(v___x_2599_, 0, v___y_2639_);
v___x_2658_ = v___x_2599_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___y_2639_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v___x_2656_);
v___x_2658_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2668_; 
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2668_ == 0)
{
lean_object* v_unused_2669_; 
v_unused_2669_ = lean_ctor_get(v___x_2656_, 0);
lean_dec(v_unused_2669_);
v___x_2660_ = v___x_2656_;
v_isShared_2661_ = v_isSharedCheck_2668_;
goto v_resetjp_2659_;
}
else
{
lean_dec(v___x_2656_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2668_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v___x_2658_);
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2658_);
v___x_2663_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
lean_object* v___x_2665_; 
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 1, v___x_2663_);
v___x_2665_ = v___x_2652_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_pos_2649_);
lean_ctor_set(v_reuseFailAlloc_2666_, 1, v___x_2663_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
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
lean_object* v_pos_2672_; lean_object* v_err_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
lean_dec_ref(v___y_2639_);
lean_del_object(v___x_2599_);
v_pos_2672_ = lean_ctor_get(v___x_2648_, 0);
v_err_2673_ = lean_ctor_get(v___x_2648_, 1);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2675_ = v___x_2648_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_err_2673_);
lean_inc(v_pos_2672_);
lean_dec(v___x_2648_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_pos_2672_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v_err_2673_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
}
}
v___jp_2681_:
{
lean_object* v___x_2687_; uint8_t v___x_2688_; 
v___x_2687_ = lean_byte_array_size(v_array_2685_);
v___x_2688_ = lean_nat_dec_lt(v_idx_2686_, v___x_2687_);
if (v___x_2688_ == 0)
{
lean_object* v___x_2689_; lean_object* v___x_2691_; 
lean_dec(v_idx_2686_);
lean_dec_ref(v_array_2685_);
lean_dec_ref(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_del_object(v___x_2599_);
v___x_2689_ = lean_box(0);
if (v_isShared_2594_ == 0)
{
lean_ctor_set_tag(v___x_2593_, 1);
lean_ctor_set(v___x_2593_, 1, v___x_2689_);
lean_ctor_set(v___x_2593_, 0, v_pos_2684_);
v___x_2691_ = v___x_2593_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_pos_2684_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v___x_2689_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
else
{
uint8_t v___x_2693_; uint8_t v_got_2694_; uint8_t v___x_2695_; 
lean_dec_ref(v_pos_2684_);
v___x_2693_ = 61;
v_got_2694_ = lean_byte_array_fget(v_array_2685_, v_idx_2686_);
v___x_2695_ = lean_uint8_dec_eq(v_got_2694_, v___x_2693_);
if (v___x_2695_ == 0)
{
lean_dec(v_idx_2686_);
lean_dec_ref(v_array_2685_);
lean_del_object(v___x_2599_);
lean_del_object(v___x_2593_);
v___y_2571_ = v___y_2683_;
v_pos_2572_ = v___y_2682_;
goto v___jp_2570_;
}
else
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2699_; 
lean_dec_ref(v___y_2682_);
v___x_2696_ = lean_unsigned_to_nat(1u);
v___x_2697_ = lean_nat_add(v_idx_2686_, v___x_2696_);
lean_dec(v_idx_2686_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 1, v___x_2697_);
lean_ctor_set(v___x_2593_, 0, v_array_2685_);
v___x_2699_ = v___x_2593_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_array_2685_);
lean_ctor_set(v_reuseFailAlloc_2725_, 1, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
lean_object* v___x_2700_; lean_object* v_snd_2701_; lean_object* v_snd_2702_; uint8_t v___x_2703_; 
v___x_2700_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2588_, v_maxSpaceSequence_2585_, v___x_2589_, v___x_2699_);
v_snd_2701_ = lean_ctor_get(v___x_2700_, 1);
lean_inc(v_snd_2701_);
lean_dec_ref(v___x_2700_);
v_snd_2702_ = lean_ctor_get(v_snd_2701_, 1);
v___x_2703_ = lean_unbox(v_snd_2702_);
if (v___x_2703_ == 0)
{
lean_object* v_fst_2704_; lean_object* v_array_2705_; lean_object* v_idx_2706_; lean_object* v___x_2707_; uint8_t v___x_2708_; 
v_fst_2704_ = lean_ctor_get(v_snd_2701_, 0);
lean_inc(v_fst_2704_);
lean_dec(v_snd_2701_);
v_array_2705_ = lean_ctor_get(v_fst_2704_, 0);
v_idx_2706_ = lean_ctor_get(v_fst_2704_, 1);
v___x_2707_ = lean_byte_array_size(v_array_2705_);
v___x_2708_ = lean_nat_dec_lt(v_idx_2706_, v___x_2707_);
if (v___x_2708_ == 0)
{
lean_inc(v_idx_2706_);
lean_inc_ref(v_array_2705_);
v___y_2639_ = v___y_2683_;
v_pos_2640_ = v_fst_2704_;
v_array_2641_ = v_array_2705_;
v_idx_2642_ = v_idx_2706_;
goto v___jp_2638_;
}
else
{
uint8_t v___x_2709_; uint32_t v___x_2710_; uint32_t v___x_2711_; uint8_t v___x_2712_; 
v___x_2709_ = lean_byte_array_fget(v_array_2705_, v_idx_2706_);
v___x_2710_ = lean_uint8_to_uint32(v___x_2709_);
v___x_2711_ = 32;
v___x_2712_ = lean_uint32_dec_eq(v___x_2710_, v___x_2711_);
if (v___x_2712_ == 0)
{
uint32_t v___x_2713_; uint8_t v___x_2714_; 
v___x_2713_ = 9;
v___x_2714_ = lean_uint32_dec_eq(v___x_2710_, v___x_2713_);
if (v___x_2714_ == 0)
{
lean_inc(v_idx_2706_);
lean_inc_ref(v_array_2705_);
v___y_2639_ = v___y_2683_;
v_pos_2640_ = v_fst_2704_;
v_array_2641_ = v_array_2705_;
v_idx_2642_ = v_idx_2706_;
goto v___jp_2638_;
}
else
{
lean_dec_ref(v___y_2683_);
lean_del_object(v___x_2599_);
v_pos_2513_ = v_fst_2704_;
goto v___jp_2512_;
}
}
else
{
lean_dec_ref(v___y_2683_);
lean_del_object(v___x_2599_);
v_pos_2513_ = v_fst_2704_;
goto v___jp_2512_;
}
}
}
else
{
lean_object* v_fst_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2723_; 
lean_dec_ref(v___y_2683_);
lean_del_object(v___x_2599_);
v_fst_2715_ = lean_ctor_get(v_snd_2701_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v_snd_2701_);
if (v_isSharedCheck_2723_ == 0)
{
lean_object* v_unused_2724_; 
v_unused_2724_ = lean_ctor_get(v_snd_2701_, 1);
lean_dec(v_unused_2724_);
v___x_2717_ = v_snd_2701_;
v_isShared_2718_ = v_isSharedCheck_2723_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_fst_2715_);
lean_dec(v_snd_2701_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2723_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2719_; lean_object* v___x_2721_; 
v___x_2719_ = lean_box(0);
if (v_isShared_2718_ == 0)
{
lean_ctor_set_tag(v___x_2717_, 1);
lean_ctor_set(v___x_2717_, 1, v___x_2719_);
v___x_2721_ = v___x_2717_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_fst_2715_);
lean_ctor_set(v_reuseFailAlloc_2722_, 1, v___x_2719_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
}
}
}
v___jp_2726_:
{
lean_object* v___x_2729_; 
v___x_2729_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_2728_, v_pos_2727_);
lean_dec(v_res_2728_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_pos_2730_; lean_object* v_res_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2761_; 
v_pos_2730_ = lean_ctor_get(v___x_2729_, 0);
v_res_2731_ = lean_ctor_get(v___x_2729_, 1);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2733_ = v___x_2729_;
v_isShared_2734_ = v_isSharedCheck_2761_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_res_2731_);
lean_inc(v_pos_2730_);
lean_dec(v___x_2729_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2761_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2735_; 
v___x_2735_ = l_Std_Http_Chunk_ExtensionName_ofString_x3f(v_res_2731_);
if (lean_obj_tag(v___x_2735_) == 1)
{
lean_object* v_val_2736_; lean_object* v___x_2737_; lean_object* v_snd_2738_; lean_object* v_snd_2739_; uint8_t v___x_2740_; 
v_val_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_val_2736_);
lean_dec_ref_known(v___x_2735_, 1);
lean_inc(v_pos_2730_);
v___x_2737_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2588_, v_maxSpaceSequence_2585_, v___x_2589_, v_pos_2730_);
v_snd_2738_ = lean_ctor_get(v___x_2737_, 1);
lean_inc(v_snd_2738_);
lean_dec_ref(v___x_2737_);
v_snd_2739_ = lean_ctor_get(v_snd_2738_, 1);
v___x_2740_ = lean_unbox(v_snd_2739_);
if (v___x_2740_ == 0)
{
lean_object* v_fst_2741_; lean_object* v_array_2742_; lean_object* v_idx_2743_; lean_object* v___x_2744_; uint8_t v___x_2745_; 
lean_del_object(v___x_2733_);
v_fst_2741_ = lean_ctor_get(v_snd_2738_, 0);
lean_inc(v_fst_2741_);
lean_dec(v_snd_2738_);
v_array_2742_ = lean_ctor_get(v_fst_2741_, 0);
lean_inc_ref(v_array_2742_);
v_idx_2743_ = lean_ctor_get(v_fst_2741_, 1);
lean_inc(v_idx_2743_);
v___x_2744_ = lean_byte_array_size(v_array_2742_);
v___x_2745_ = lean_nat_dec_lt(v_idx_2743_, v___x_2744_);
if (v___x_2745_ == 0)
{
v___y_2682_ = v_pos_2730_;
v___y_2683_ = v_val_2736_;
v_pos_2684_ = v_fst_2741_;
v_array_2685_ = v_array_2742_;
v_idx_2686_ = v_idx_2743_;
goto v___jp_2681_;
}
else
{
uint8_t v___x_2746_; uint32_t v___x_2747_; uint32_t v___x_2748_; uint8_t v___x_2749_; 
v___x_2746_ = lean_byte_array_fget(v_array_2742_, v_idx_2743_);
v___x_2747_ = lean_uint8_to_uint32(v___x_2746_);
v___x_2748_ = 32;
v___x_2749_ = lean_uint32_dec_eq(v___x_2747_, v___x_2748_);
if (v___x_2749_ == 0)
{
uint32_t v___x_2750_; uint8_t v___x_2751_; 
v___x_2750_ = 9;
v___x_2751_ = lean_uint32_dec_eq(v___x_2747_, v___x_2750_);
if (v___x_2751_ == 0)
{
v___y_2682_ = v_pos_2730_;
v___y_2683_ = v_val_2736_;
v_pos_2684_ = v_fst_2741_;
v_array_2685_ = v_array_2742_;
v_idx_2686_ = v_idx_2743_;
goto v___jp_2681_;
}
else
{
lean_dec(v_idx_2743_);
lean_dec_ref(v_array_2742_);
lean_dec(v_fst_2741_);
lean_del_object(v___x_2599_);
lean_del_object(v___x_2593_);
v___y_2571_ = v_val_2736_;
v_pos_2572_ = v_pos_2730_;
goto v___jp_2570_;
}
}
else
{
lean_dec(v_idx_2743_);
lean_dec_ref(v_array_2742_);
lean_dec(v_fst_2741_);
lean_del_object(v___x_2599_);
lean_del_object(v___x_2593_);
v___y_2571_ = v_val_2736_;
v_pos_2572_ = v_pos_2730_;
goto v___jp_2570_;
}
}
}
else
{
lean_object* v_fst_2752_; lean_object* v___x_2753_; lean_object* v___x_2755_; 
lean_dec(v_val_2736_);
lean_dec(v_pos_2730_);
lean_del_object(v___x_2599_);
lean_del_object(v___x_2593_);
v_fst_2752_ = lean_ctor_get(v_snd_2738_, 0);
lean_inc(v_fst_2752_);
lean_dec(v_snd_2738_);
v___x_2753_ = lean_box(0);
if (v_isShared_2734_ == 0)
{
lean_ctor_set_tag(v___x_2733_, 1);
lean_ctor_set(v___x_2733_, 1, v___x_2753_);
lean_ctor_set(v___x_2733_, 0, v_fst_2752_);
v___x_2755_ = v___x_2733_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_fst_2752_);
lean_ctor_set(v_reuseFailAlloc_2756_, 1, v___x_2753_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
else
{
lean_object* v___x_2757_; lean_object* v___x_2759_; 
lean_dec(v___x_2735_);
lean_del_object(v___x_2599_);
lean_del_object(v___x_2593_);
v___x_2757_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3));
if (v_isShared_2734_ == 0)
{
lean_ctor_set_tag(v___x_2733_, 1);
lean_ctor_set(v___x_2733_, 1, v___x_2757_);
v___x_2759_ = v___x_2733_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_pos_2730_);
lean_ctor_set(v_reuseFailAlloc_2760_, 1, v___x_2757_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
else
{
lean_object* v_pos_2762_; lean_object* v_err_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_del_object(v___x_2599_);
lean_del_object(v___x_2593_);
v_pos_2762_ = lean_ctor_get(v___x_2729_, 0);
v_err_2763_ = lean_ctor_get(v___x_2729_, 1);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2729_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_err_2763_);
lean_inc(v_pos_2762_);
lean_dec(v___x_2729_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_pos_2762_);
lean_ctor_set(v_reuseFailAlloc_2769_, 1, v_err_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
v___jp_2771_:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; uint8_t v___x_2778_; 
v___x_2776_ = l_ByteArray_toByteSlice(v___y_2772_, v_lower_2774_, v_upper_2775_);
v___x_2777_ = l_ByteSlice_toByteArray(v___x_2776_);
v___x_2778_ = lean_string_validate_utf8(v___x_2777_);
if (v___x_2778_ == 0)
{
lean_object* v___x_2779_; 
lean_dec_ref(v___x_2777_);
v___x_2779_ = lean_box(0);
v_pos_2727_ = v___y_2773_;
v_res_2728_ = v___x_2779_;
goto v___jp_2726_;
}
else
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2780_ = lean_string_from_utf8_unchecked(v___x_2777_);
v___x_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2780_);
v_pos_2727_ = v___y_2773_;
v_res_2728_ = v___x_2781_;
goto v___jp_2726_;
}
}
v___jp_2782_:
{
uint8_t v___x_2788_; 
v___x_2788_ = lean_nat_dec_le(v___y_2784_, v___y_2783_);
if (v___x_2788_ == 0)
{
lean_dec(v___y_2784_);
v___y_2772_ = v___y_2785_;
v___y_2773_ = v___y_2786_;
v_lower_2774_ = v___y_2787_;
v_upper_2775_ = v___y_2783_;
goto v___jp_2771_;
}
else
{
lean_dec(v___y_2783_);
v___y_2772_ = v___y_2785_;
v___y_2773_ = v___y_2786_;
v_lower_2774_ = v___y_2787_;
v_upper_2775_ = v___y_2784_;
goto v___jp_2771_;
}
}
v___jp_2789_:
{
lean_object* v___x_2791_; lean_object* v_snd_2792_; lean_object* v_snd_2793_; uint8_t v___x_2794_; 
lean_inc_ref(v_pos_2790_);
v___x_2791_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2603_, v_maxChunkExtNameLength_2586_, v___x_2589_, v_pos_2790_);
v_snd_2792_ = lean_ctor_get(v___x_2791_, 1);
lean_inc(v_snd_2792_);
v_snd_2793_ = lean_ctor_get(v_snd_2792_, 1);
v___x_2794_ = lean_unbox(v_snd_2793_);
if (v___x_2794_ == 0)
{
lean_object* v_fst_2795_; lean_object* v_fst_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2810_; 
v_fst_2795_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_fst_2795_);
lean_dec_ref(v___x_2791_);
v_fst_2796_ = lean_ctor_get(v_snd_2792_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v_snd_2792_);
if (v_isSharedCheck_2810_ == 0)
{
lean_object* v_unused_2811_; 
v_unused_2811_ = lean_ctor_get(v_snd_2792_, 1);
lean_dec(v_unused_2811_);
v___x_2798_ = v_snd_2792_;
v_isShared_2799_ = v_isSharedCheck_2810_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_fst_2796_);
lean_dec(v_snd_2792_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2810_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
uint8_t v___x_2800_; 
v___x_2800_ = lean_nat_dec_eq(v_fst_2795_, v___x_2589_);
if (v___x_2800_ == 0)
{
lean_object* v_array_2801_; lean_object* v_idx_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; uint8_t v___x_2805_; 
lean_del_object(v___x_2798_);
v_array_2801_ = lean_ctor_get(v_pos_2790_, 0);
lean_inc_ref(v_array_2801_);
v_idx_2802_ = lean_ctor_get(v_pos_2790_, 1);
lean_inc(v_idx_2802_);
lean_dec_ref(v_pos_2790_);
v___x_2803_ = lean_nat_add(v_idx_2802_, v_fst_2795_);
lean_dec(v_fst_2795_);
v___x_2804_ = lean_byte_array_size(v_array_2801_);
v___x_2805_ = lean_nat_dec_le(v_idx_2802_, v___x_2589_);
if (v___x_2805_ == 0)
{
v___y_2783_ = v___x_2804_;
v___y_2784_ = v___x_2803_;
v___y_2785_ = v_array_2801_;
v___y_2786_ = v_fst_2796_;
v___y_2787_ = v_idx_2802_;
goto v___jp_2782_;
}
else
{
lean_dec(v_idx_2802_);
v___y_2783_ = v___x_2804_;
v___y_2784_ = v___x_2803_;
v___y_2785_ = v_array_2801_;
v___y_2786_ = v_fst_2796_;
v___y_2787_ = v___x_2589_;
goto v___jp_2782_;
}
}
else
{
lean_object* v___x_2806_; lean_object* v___x_2808_; 
lean_dec(v_fst_2796_);
lean_dec(v_fst_2795_);
lean_del_object(v___x_2599_);
lean_del_object(v___x_2593_);
v___x_2806_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_2799_ == 0)
{
lean_ctor_set_tag(v___x_2798_, 1);
lean_ctor_set(v___x_2798_, 1, v___x_2806_);
lean_ctor_set(v___x_2798_, 0, v_pos_2790_);
v___x_2808_ = v___x_2798_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_pos_2790_);
lean_ctor_set(v_reuseFailAlloc_2809_, 1, v___x_2806_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
}
else
{
lean_object* v_fst_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2820_; 
lean_dec_ref(v___x_2791_);
lean_dec_ref(v_pos_2790_);
lean_del_object(v___x_2599_);
lean_del_object(v___x_2593_);
v_fst_2812_ = lean_ctor_get(v_snd_2792_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v_snd_2792_);
if (v_isSharedCheck_2820_ == 0)
{
lean_object* v_unused_2821_; 
v_unused_2821_ = lean_ctor_get(v_snd_2792_, 1);
lean_dec(v_unused_2821_);
v___x_2814_ = v_snd_2792_;
v_isShared_2815_ = v_isSharedCheck_2820_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_fst_2812_);
lean_dec(v_snd_2792_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2820_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2816_; lean_object* v___x_2818_; 
v___x_2816_ = lean_box(0);
if (v_isShared_2815_ == 0)
{
lean_ctor_set_tag(v___x_2814_, 1);
lean_ctor_set(v___x_2814_, 1, v___x_2816_);
v___x_2818_ = v___x_2814_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_fst_2812_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v___x_2816_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
v___jp_2822_:
{
lean_object* v___x_2824_; uint8_t v___x_2825_; 
v___x_2824_ = lean_byte_array_size(v_array_2601_);
v___x_2825_ = lean_nat_dec_lt(v_idx_2602_, v___x_2824_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
lean_dec(v_idx_2602_);
lean_dec_ref(v_array_2601_);
lean_del_object(v___x_2599_);
lean_del_object(v___x_2593_);
v___x_2826_ = lean_box(0);
v___x_2827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2827_, 0, v_pos_2823_);
lean_ctor_set(v___x_2827_, 1, v___x_2826_);
return v___x_2827_;
}
else
{
uint8_t v___x_2828_; uint8_t v_got_2829_; uint8_t v___x_2830_; 
v___x_2828_ = 59;
v_got_2829_ = lean_byte_array_fget(v_array_2601_, v_idx_2602_);
v___x_2830_ = lean_uint8_dec_eq(v_got_2829_, v___x_2828_);
if (v___x_2830_ == 0)
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
lean_dec(v_idx_2602_);
lean_dec_ref(v_array_2601_);
lean_del_object(v___x_2599_);
lean_del_object(v___x_2593_);
v___x_2831_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5));
v___x_2832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2832_, 0, v_pos_2823_);
lean_ctor_set(v___x_2832_, 1, v___x_2831_);
return v___x_2832_;
}
else
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v_snd_2837_; lean_object* v_snd_2838_; uint8_t v___x_2839_; 
lean_dec_ref(v_pos_2823_);
v___x_2833_ = lean_unsigned_to_nat(1u);
v___x_2834_ = lean_nat_add(v_idx_2602_, v___x_2833_);
lean_dec(v_idx_2602_);
v___x_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2835_, 0, v_array_2601_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
v___x_2836_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2588_, v_maxSpaceSequence_2585_, v___x_2589_, v___x_2835_);
v_snd_2837_ = lean_ctor_get(v___x_2836_, 1);
lean_inc(v_snd_2837_);
lean_dec_ref(v___x_2836_);
v_snd_2838_ = lean_ctor_get(v_snd_2837_, 1);
v___x_2839_ = lean_unbox(v_snd_2838_);
if (v___x_2839_ == 0)
{
lean_object* v_fst_2840_; lean_object* v_array_2841_; lean_object* v_idx_2842_; lean_object* v___x_2843_; uint8_t v___x_2844_; 
v_fst_2840_ = lean_ctor_get(v_snd_2837_, 0);
lean_inc(v_fst_2840_);
lean_dec(v_snd_2837_);
v_array_2841_ = lean_ctor_get(v_fst_2840_, 0);
v_idx_2842_ = lean_ctor_get(v_fst_2840_, 1);
v___x_2843_ = lean_byte_array_size(v_array_2841_);
v___x_2844_ = lean_nat_dec_lt(v_idx_2842_, v___x_2843_);
if (v___x_2844_ == 0)
{
v_pos_2790_ = v_fst_2840_;
goto v___jp_2789_;
}
else
{
uint8_t v___x_2845_; uint32_t v___x_2846_; uint32_t v___x_2847_; uint8_t v___x_2848_; 
v___x_2845_ = lean_byte_array_fget(v_array_2841_, v_idx_2842_);
v___x_2846_ = lean_uint8_to_uint32(v___x_2845_);
v___x_2847_ = 32;
v___x_2848_ = lean_uint32_dec_eq(v___x_2846_, v___x_2847_);
if (v___x_2848_ == 0)
{
uint32_t v___x_2849_; uint8_t v___x_2850_; 
v___x_2849_ = 9;
v___x_2850_ = lean_uint32_dec_eq(v___x_2846_, v___x_2849_);
if (v___x_2850_ == 0)
{
v_pos_2790_ = v_fst_2840_;
goto v___jp_2789_;
}
else
{
lean_del_object(v___x_2599_);
lean_del_object(v___x_2593_);
v_pos_2578_ = v_fst_2840_;
goto v___jp_2577_;
}
}
else
{
lean_del_object(v___x_2599_);
lean_del_object(v___x_2593_);
v_pos_2578_ = v_fst_2840_;
goto v___jp_2577_;
}
}
}
else
{
lean_object* v_fst_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2859_; 
lean_del_object(v___x_2599_);
lean_del_object(v___x_2593_);
v_fst_2851_ = lean_ctor_get(v_snd_2837_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v_snd_2837_);
if (v_isSharedCheck_2859_ == 0)
{
lean_object* v_unused_2860_; 
v_unused_2860_ = lean_ctor_get(v_snd_2837_, 1);
lean_dec(v_unused_2860_);
v___x_2853_ = v_snd_2837_;
v_isShared_2854_ = v_isSharedCheck_2859_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_fst_2851_);
lean_dec(v_snd_2837_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2859_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2855_; lean_object* v___x_2857_; 
v___x_2855_ = lean_box(0);
if (v_isShared_2854_ == 0)
{
lean_ctor_set_tag(v___x_2853_, 1);
lean_ctor_set(v___x_2853_, 1, v___x_2855_);
v___x_2857_ = v___x_2853_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_fst_2851_);
lean_ctor_set(v_reuseFailAlloc_2858_, 1, v___x_2855_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
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
lean_object* v_fst_2871_; lean_object* v___x_2872_; lean_object* v___x_2874_; 
v_fst_2871_ = lean_ctor_get(v_snd_2591_, 0);
lean_inc(v_fst_2871_);
lean_dec(v_snd_2591_);
v___x_2872_ = lean_box(0);
if (v_isShared_2594_ == 0)
{
lean_ctor_set_tag(v___x_2593_, 1);
lean_ctor_set(v___x_2593_, 1, v___x_2872_);
lean_ctor_set(v___x_2593_, 0, v_fst_2871_);
v___x_2874_ = v___x_2593_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_fst_2871_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___boxed(lean_object* v_limits_2878_, lean_object* v_a_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_2878_, v_a_2879_);
lean_dec_ref(v_limits_2878_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0(lean_object* v_limits_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_2881_, v___y_2882_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_pos_2884_; lean_object* v_res_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2893_; 
v_pos_2884_ = lean_ctor_get(v___x_2883_, 0);
v_res_2885_ = lean_ctor_get(v___x_2883_, 1);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2887_ = v___x_2883_;
v_isShared_2888_ = v_isSharedCheck_2893_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_res_2885_);
lean_inc(v_pos_2884_);
lean_dec(v___x_2883_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2893_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2889_; lean_object* v___x_2891_; 
v___x_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2889_, 0, v_res_2885_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 1, v___x_2889_);
v___x_2891_ = v___x_2887_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_pos_2884_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v___x_2889_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
else
{
lean_object* v_pos_2894_; lean_object* v_err_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
v_pos_2894_ = lean_ctor_get(v___x_2883_, 0);
v_err_2895_ = lean_ctor_get(v___x_2883_, 1);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2883_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_err_2895_);
lean_inc(v_pos_2894_);
lean_dec(v___x_2883_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_pos_2894_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v_err_2895_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed(lean_object* v_limits_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Std_Http_Protocol_H1_parseChunkSize___lam__0(v_limits_2903_, v___y_2904_);
lean_dec_ref(v_limits_2903_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0_spec__0(lean_object* v_as_2906_, size_t v_i_2907_, size_t v_stop_2908_, lean_object* v_b_2909_){
_start:
{
lean_object* v___y_2911_; uint8_t v___x_2915_; 
v___x_2915_ = lean_usize_dec_eq(v_i_2907_, v_stop_2908_);
if (v___x_2915_ == 0)
{
lean_object* v___x_2916_; 
v___x_2916_ = lean_array_uget_borrowed(v_as_2906_, v_i_2907_);
if (lean_obj_tag(v___x_2916_) == 0)
{
v___y_2911_ = v_b_2909_;
goto v___jp_2910_;
}
else
{
lean_object* v_val_2917_; lean_object* v___x_2918_; 
v_val_2917_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_val_2917_);
v___x_2918_ = lean_array_push(v_b_2909_, v_val_2917_);
v___y_2911_ = v___x_2918_;
goto v___jp_2910_;
}
}
else
{
return v_b_2909_;
}
v___jp_2910_:
{
size_t v___x_2912_; size_t v___x_2913_; 
v___x_2912_ = ((size_t)1ULL);
v___x_2913_ = lean_usize_add(v_i_2907_, v___x_2912_);
v_i_2907_ = v___x_2913_;
v_b_2909_ = v___y_2911_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0_spec__0___boxed(lean_object* v_as_2919_, lean_object* v_i_2920_, lean_object* v_stop_2921_, lean_object* v_b_2922_){
_start:
{
size_t v_i_boxed_2923_; size_t v_stop_boxed_2924_; lean_object* v_res_2925_; 
v_i_boxed_2923_ = lean_unbox_usize(v_i_2920_);
lean_dec(v_i_2920_);
v_stop_boxed_2924_ = lean_unbox_usize(v_stop_2921_);
lean_dec(v_stop_2921_);
v_res_2925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0_spec__0(v_as_2919_, v_i_boxed_2923_, v_stop_boxed_2924_, v_b_2922_);
lean_dec_ref(v_as_2919_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0(lean_object* v_as_2928_, lean_object* v_start_2929_, lean_object* v_stop_2930_){
_start:
{
lean_object* v___x_2931_; uint8_t v___x_2932_; 
v___x_2931_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0___closed__0));
v___x_2932_ = lean_nat_dec_lt(v_start_2929_, v_stop_2930_);
if (v___x_2932_ == 0)
{
return v___x_2931_;
}
else
{
lean_object* v___x_2933_; uint8_t v___x_2934_; 
v___x_2933_ = lean_array_get_size(v_as_2928_);
v___x_2934_ = lean_nat_dec_le(v_stop_2930_, v___x_2933_);
if (v___x_2934_ == 0)
{
uint8_t v___x_2935_; 
v___x_2935_ = lean_nat_dec_lt(v_start_2929_, v___x_2933_);
if (v___x_2935_ == 0)
{
return v___x_2931_;
}
else
{
size_t v___x_2936_; size_t v___x_2937_; lean_object* v___x_2938_; 
v___x_2936_ = lean_usize_of_nat(v_start_2929_);
v___x_2937_ = lean_usize_of_nat(v___x_2933_);
v___x_2938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0_spec__0(v_as_2928_, v___x_2936_, v___x_2937_, v___x_2931_);
return v___x_2938_;
}
}
else
{
size_t v___x_2939_; size_t v___x_2940_; lean_object* v___x_2941_; 
v___x_2939_ = lean_usize_of_nat(v_start_2929_);
v___x_2940_ = lean_usize_of_nat(v_stop_2930_);
v___x_2941_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0_spec__0(v_as_2928_, v___x_2939_, v___x_2940_, v___x_2931_);
return v___x_2941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0___boxed(lean_object* v_as_2942_, lean_object* v_start_2943_, lean_object* v_stop_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0(v_as_2942_, v_start_2943_, v_stop_2944_);
lean_dec(v_stop_2944_);
lean_dec(v_start_2943_);
lean_dec_ref(v_as_2942_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize(lean_object* v_limits_2946_, lean_object* v_a_2947_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(v_a_2947_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_pos_2949_; lean_object* v_res_2950_; lean_object* v_maxChunkExtensions_2951_; lean_object* v___f_2952_; lean_object* v___x_2953_; 
v_pos_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_pos_2949_);
v_res_2950_ = lean_ctor_get(v___x_2948_, 1);
lean_inc(v_res_2950_);
lean_dec_ref_known(v___x_2948_, 2);
v_maxChunkExtensions_2951_ = lean_ctor_get(v_limits_2946_, 12);
lean_inc(v_maxChunkExtensions_2951_);
v___f_2952_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2952_, 0, v_limits_2946_);
v___x_2953_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___f_2952_, v_maxChunkExtensions_2951_, v_pos_2949_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_pos_2954_; lean_object* v_res_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v_pos_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_pos_2954_);
v_res_2955_ = lean_ctor_get(v___x_2953_, 1);
lean_inc(v_res_2955_);
lean_dec_ref_known(v___x_2953_, 2);
v___x_2956_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2957_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2956_, v_pos_2954_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_pos_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2969_; 
v_pos_2958_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2969_ == 0)
{
lean_object* v_unused_2970_; 
v_unused_2970_ = lean_ctor_get(v___x_2957_, 1);
lean_dec(v_unused_2970_);
v___x_2960_ = v___x_2957_;
v_isShared_2961_ = v_isSharedCheck_2969_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_pos_2958_);
lean_dec(v___x_2957_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2969_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2967_; 
v___x_2962_ = lean_unsigned_to_nat(0u);
v___x_2963_ = lean_array_get_size(v_res_2955_);
v___x_2964_ = l_Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0(v_res_2955_, v___x_2962_, v___x_2963_);
lean_dec(v_res_2955_);
v___x_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2965_, 0, v_res_2950_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 1, v___x_2965_);
v___x_2967_ = v___x_2960_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_pos_2958_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v___x_2965_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
else
{
lean_object* v_pos_2971_; lean_object* v_err_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
lean_dec(v_res_2955_);
lean_dec(v_res_2950_);
v_pos_2971_ = lean_ctor_get(v___x_2957_, 0);
v_err_2972_ = lean_ctor_get(v___x_2957_, 1);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2957_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_err_2972_);
lean_inc(v_pos_2971_);
lean_dec(v___x_2957_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_pos_2971_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v_err_2972_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
else
{
lean_object* v_pos_2980_; lean_object* v_err_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
lean_dec(v_res_2950_);
v_pos_2980_ = lean_ctor_get(v___x_2953_, 0);
v_err_2981_ = lean_ctor_get(v___x_2953_, 1);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2953_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_err_2981_);
lean_inc(v_pos_2980_);
lean_dec(v___x_2953_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_pos_2980_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v_err_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
else
{
lean_object* v_pos_2989_; lean_object* v_err_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
lean_dec_ref(v_limits_2946_);
v_pos_2989_ = lean_ctor_get(v___x_2948_, 0);
v_err_2990_ = lean_ctor_get(v___x_2948_, 1);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2948_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_err_2990_);
lean_inc(v_pos_2989_);
lean_dec(v___x_2948_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_pos_2989_);
lean_ctor_set(v_reuseFailAlloc_2996_, 1, v_err_2990_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl(lean_object* v_x_2998_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = lean_obj_tag_nat(v_x_2998_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl___boxed(lean_object* v_x_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl(v_x_3000_);
lean_dec_ref(v_x_3000_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(lean_object* v_t_3002_, lean_object* v_k_3003_){
_start:
{
if (lean_obj_tag(v_t_3002_) == 0)
{
lean_object* v_data_3004_; lean_object* v___x_3005_; 
v_data_3004_ = lean_ctor_get(v_t_3002_, 0);
lean_inc_ref(v_data_3004_);
lean_dec_ref_known(v_t_3002_, 1);
v___x_3005_ = lean_apply_1(v_k_3003_, v_data_3004_);
return v___x_3005_;
}
else
{
lean_object* v_data_3006_; lean_object* v_remaining_3007_; lean_object* v___x_3008_; 
v_data_3006_ = lean_ctor_get(v_t_3002_, 0);
lean_inc_ref(v_data_3006_);
v_remaining_3007_ = lean_ctor_get(v_t_3002_, 1);
lean_inc(v_remaining_3007_);
lean_dec_ref_known(v_t_3002_, 2);
v___x_3008_ = lean_apply_2(v_k_3003_, v_data_3006_, v_remaining_3007_);
return v___x_3008_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim(lean_object* v_motive_3009_, lean_object* v_ctorIdx_3010_, lean_object* v_t_3011_, lean_object* v_h_3012_, lean_object* v_k_3013_){
_start:
{
lean_object* v___x_3014_; 
v___x_3014_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3011_, v_k_3013_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___boxed(lean_object* v_motive_3015_, lean_object* v_ctorIdx_3016_, lean_object* v_t_3017_, lean_object* v_h_3018_, lean_object* v_k_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim(v_motive_3015_, v_ctorIdx_3016_, v_t_3017_, v_h_3018_, v_k_3019_);
lean_dec(v_ctorIdx_3016_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim___redArg(lean_object* v_t_3021_, lean_object* v_complete_3022_){
_start:
{
lean_object* v___x_3023_; 
v___x_3023_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3021_, v_complete_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim(lean_object* v_motive_3024_, lean_object* v_t_3025_, lean_object* v_h_3026_, lean_object* v_complete_3027_){
_start:
{
lean_object* v___x_3028_; 
v___x_3028_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3025_, v_complete_3027_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim___redArg(lean_object* v_t_3029_, lean_object* v_incomplete_3030_){
_start:
{
lean_object* v___x_3031_; 
v___x_3031_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3029_, v_incomplete_3030_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim(lean_object* v_motive_3032_, lean_object* v_t_3033_, lean_object* v_h_3034_, lean_object* v_incomplete_3035_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3033_, v_incomplete_3035_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkPartial(lean_object* v_limits_3037_, lean_object* v_a_3038_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l_Std_Http_Protocol_H1_parseChunkSize(v_limits_3037_, v_a_3038_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_object* v_res_3040_; lean_object* v_pos_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3081_; 
v_res_3040_ = lean_ctor_get(v___x_3039_, 1);
v_pos_3041_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3043_ = v___x_3039_;
v_isShared_3044_ = v_isSharedCheck_3081_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_res_3040_);
lean_inc(v_pos_3041_);
lean_dec(v___x_3039_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3081_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v_fst_3045_; lean_object* v_snd_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3080_; 
v_fst_3045_ = lean_ctor_get(v_res_3040_, 0);
v_snd_3046_ = lean_ctor_get(v_res_3040_, 1);
v_isSharedCheck_3080_ = !lean_is_exclusive(v_res_3040_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3048_ = v_res_3040_;
v_isShared_3049_ = v_isSharedCheck_3080_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_snd_3046_);
lean_inc(v_fst_3045_);
lean_dec(v_res_3040_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3080_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3050_; uint8_t v___x_3051_; 
v___x_3050_ = lean_unsigned_to_nat(0u);
v___x_3051_ = lean_nat_dec_eq(v_fst_3045_, v___x_3050_);
if (v___x_3051_ == 0)
{
lean_object* v___x_3052_; 
lean_del_object(v___x_3043_);
v___x_3052_ = l_Std_Internal_Parsec_ByteArray_take(v_fst_3045_, v_pos_3041_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_pos_3053_; lean_object* v_res_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3066_; 
v_pos_3053_ = lean_ctor_get(v___x_3052_, 0);
v_res_3054_ = lean_ctor_get(v___x_3052_, 1);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3056_ = v___x_3052_;
v_isShared_3057_ = v_isSharedCheck_3066_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_res_3054_);
lean_inc(v_pos_3053_);
lean_dec(v___x_3052_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3066_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3049_ == 0)
{
lean_ctor_set(v___x_3048_, 1, v_res_3054_);
lean_ctor_set(v___x_3048_, 0, v_snd_3046_);
v___x_3059_ = v___x_3048_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_snd_3046_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v_res_3054_);
v___x_3059_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3063_; 
v___x_3060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3060_, 0, v_fst_3045_);
lean_ctor_set(v___x_3060_, 1, v___x_3059_);
v___x_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3060_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 1, v___x_3061_);
v___x_3063_ = v___x_3056_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_pos_3053_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v___x_3061_);
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
else
{
lean_object* v_pos_3067_; lean_object* v_err_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_del_object(v___x_3048_);
lean_dec(v_snd_3046_);
lean_dec(v_fst_3045_);
v_pos_3067_ = lean_ctor_get(v___x_3052_, 0);
v_err_3068_ = lean_ctor_get(v___x_3052_, 1);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_3052_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_err_3068_);
lean_inc(v_pos_3067_);
lean_dec(v___x_3052_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_pos_3067_);
lean_ctor_set(v_reuseFailAlloc_3074_, 1, v_err_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
else
{
lean_object* v___x_3076_; lean_object* v___x_3078_; 
lean_del_object(v___x_3048_);
lean_dec(v_snd_3046_);
lean_dec(v_fst_3045_);
v___x_3076_ = lean_box(0);
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 1, v___x_3076_);
v___x_3078_ = v___x_3043_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_pos_3041_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v___x_3076_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
}
else
{
lean_object* v_pos_3082_; lean_object* v_err_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
v_pos_3082_ = lean_ctor_get(v___x_3039_, 0);
v_err_3083_ = lean_ctor_get(v___x_3039_, 1);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_3039_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_err_3083_);
lean_inc(v_pos_3082_);
lean_dec(v___x_3039_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_pos_3082_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v_err_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData(lean_object* v_size_3091_, lean_object* v_it_3092_){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; uint8_t v___x_3095_; 
v___x_3093_ = l_ByteArray_Iterator_remainingBytes(v_it_3092_);
v___x_3094_ = lean_unsigned_to_nat(0u);
v___x_3095_ = lean_nat_dec_eq(v___x_3093_, v___x_3094_);
if (v___x_3095_ == 0)
{
uint8_t v___x_3096_; 
v___x_3096_ = lean_nat_dec_lt(v___x_3093_, v_size_3091_);
if (v___x_3096_ == 0)
{
lean_object* v_array_3097_; lean_object* v_idx_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3117_; 
lean_dec(v___x_3093_);
v_array_3097_ = lean_ctor_get(v_it_3092_, 0);
v_idx_3098_ = lean_ctor_get(v_it_3092_, 1);
v_isSharedCheck_3117_ = !lean_is_exclusive(v_it_3092_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3100_ = v_it_3092_;
v_isShared_3101_ = v_isSharedCheck_3117_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_idx_3098_);
lean_inc(v_array_3097_);
lean_dec(v_it_3092_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3117_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3102_; lean_object* v___x_3104_; 
v___x_3102_ = lean_nat_add(v_idx_3098_, v_size_3091_);
lean_inc(v___x_3102_);
lean_inc_ref(v_array_3097_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 1, v___x_3102_);
v___x_3104_ = v___x_3100_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_array_3097_);
lean_ctor_set(v_reuseFailAlloc_3116_, 1, v___x_3102_);
v___x_3104_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
lean_object* v_lower_3106_; lean_object* v_upper_3107_; lean_object* v___x_3111_; lean_object* v___y_3113_; uint8_t v___x_3115_; 
v___x_3111_ = lean_byte_array_size(v_array_3097_);
v___x_3115_ = lean_nat_dec_le(v_idx_3098_, v___x_3094_);
if (v___x_3115_ == 0)
{
v___y_3113_ = v_idx_3098_;
goto v___jp_3112_;
}
else
{
lean_dec(v_idx_3098_);
v___y_3113_ = v___x_3094_;
goto v___jp_3112_;
}
v___jp_3105_:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3108_ = l_ByteArray_toByteSlice(v_array_3097_, v_lower_3106_, v_upper_3107_);
v___x_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
v___x_3110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3104_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
return v___x_3110_;
}
v___jp_3112_:
{
uint8_t v___x_3114_; 
v___x_3114_ = lean_nat_dec_le(v___x_3102_, v___x_3111_);
if (v___x_3114_ == 0)
{
lean_dec(v___x_3102_);
v_lower_3106_ = v___y_3113_;
v_upper_3107_ = v___x_3111_;
goto v___jp_3105_;
}
else
{
v_lower_3106_ = v___y_3113_;
v_upper_3107_ = v___x_3102_;
goto v___jp_3105_;
}
}
}
}
}
else
{
lean_object* v_array_3118_; lean_object* v_idx_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3139_; 
v_array_3118_ = lean_ctor_get(v_it_3092_, 0);
v_idx_3119_ = lean_ctor_get(v_it_3092_, 1);
v_isSharedCheck_3139_ = !lean_is_exclusive(v_it_3092_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3121_ = v_it_3092_;
v_isShared_3122_ = v_isSharedCheck_3139_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_idx_3119_);
lean_inc(v_array_3118_);
lean_dec(v_it_3092_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3139_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3123_; lean_object* v___x_3125_; 
v___x_3123_ = lean_nat_add(v_idx_3119_, v___x_3093_);
lean_inc(v___x_3123_);
lean_inc_ref(v_array_3118_);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 1, v___x_3123_);
v___x_3125_ = v___x_3121_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_array_3118_);
lean_ctor_set(v_reuseFailAlloc_3138_, 1, v___x_3123_);
v___x_3125_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
lean_object* v_lower_3127_; lean_object* v_upper_3128_; lean_object* v___x_3133_; lean_object* v___y_3135_; uint8_t v___x_3137_; 
v___x_3133_ = lean_byte_array_size(v_array_3118_);
v___x_3137_ = lean_nat_dec_le(v_idx_3119_, v___x_3094_);
if (v___x_3137_ == 0)
{
v___y_3135_ = v_idx_3119_;
goto v___jp_3134_;
}
else
{
lean_dec(v_idx_3119_);
v___y_3135_ = v___x_3094_;
goto v___jp_3134_;
}
v___jp_3126_:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3129_ = l_ByteArray_toByteSlice(v_array_3118_, v_lower_3127_, v_upper_3128_);
v___x_3130_ = lean_nat_sub(v_size_3091_, v___x_3093_);
lean_dec(v___x_3093_);
v___x_3131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3129_);
lean_ctor_set(v___x_3131_, 1, v___x_3130_);
v___x_3132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3125_);
lean_ctor_set(v___x_3132_, 1, v___x_3131_);
return v___x_3132_;
}
v___jp_3134_:
{
uint8_t v___x_3136_; 
v___x_3136_ = lean_nat_dec_le(v___x_3123_, v___x_3133_);
if (v___x_3136_ == 0)
{
lean_dec(v___x_3123_);
v_lower_3127_ = v___y_3135_;
v_upper_3128_ = v___x_3133_;
goto v___jp_3126_;
}
else
{
v_lower_3127_ = v___y_3135_;
v_upper_3128_ = v___x_3123_;
goto v___jp_3126_;
}
}
}
}
}
}
else
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
lean_dec(v___x_3093_);
v___x_3140_ = lean_box(0);
v___x_3141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3141_, 0, v_it_3092_);
lean_ctor_set(v___x_3141_, 1, v___x_3140_);
return v___x_3141_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData___boxed(lean_object* v_size_3142_, lean_object* v_it_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_3142_, v_it_3143_);
lean_dec(v_size_3142_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData(lean_object* v_size_3145_, lean_object* v_a_3146_){
_start:
{
lean_object* v___x_3147_; 
v___x_3147_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_3145_, v_a_3146_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_res_3148_; 
v_res_3148_ = lean_ctor_get(v___x_3147_, 1);
if (lean_obj_tag(v_res_3148_) == 0)
{
lean_object* v_pos_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
lean_inc_ref(v_res_3148_);
v_pos_3149_ = lean_ctor_get(v___x_3147_, 0);
lean_inc(v_pos_3149_);
lean_dec_ref_known(v___x_3147_, 2);
v___x_3150_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3151_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3150_, v_pos_3149_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_pos_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
v_pos_3152_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3159_ == 0)
{
lean_object* v_unused_3160_; 
v_unused_3160_ = lean_ctor_get(v___x_3151_, 1);
lean_dec(v_unused_3160_);
v___x_3154_ = v___x_3151_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_pos_3152_);
lean_dec(v___x_3151_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
lean_ctor_set(v___x_3154_, 1, v_res_3148_);
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_pos_3152_);
lean_ctor_set(v_reuseFailAlloc_3158_, 1, v_res_3148_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
else
{
lean_object* v_pos_3161_; lean_object* v_err_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec_ref_known(v_res_3148_, 1);
v_pos_3161_ = lean_ctor_get(v___x_3151_, 0);
v_err_3162_ = lean_ctor_get(v___x_3151_, 1);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3151_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_err_3162_);
lean_inc(v_pos_3161_);
lean_dec(v___x_3151_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_pos_3161_);
lean_ctor_set(v_reuseFailAlloc_3168_, 1, v_err_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
else
{
return v___x_3147_;
}
}
else
{
return v___x_3147_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData___boxed(lean_object* v_size_3170_, lean_object* v_a_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Std_Http_Protocol_H1_parseChunkSizedData(v_size_3170_, v_a_3171_);
lean_dec(v_size_3170_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField_spec__0(lean_object* v_s_3173_, lean_object* v_p_3174_){
_start:
{
lean_object* v___y_3176_; lean_object* v___y_3177_; uint32_t v___y_3181_; lean_object* v___x_3193_; uint8_t v_decide_3194_; 
v___x_3193_ = lean_string_utf8_byte_size(v_s_3173_);
v_decide_3194_ = lean_nat_dec_eq(v_p_3174_, v___x_3193_);
if (v_decide_3194_ == 0)
{
uint32_t v___x_3195_; uint32_t v___x_3196_; uint8_t v___x_3197_; 
v___x_3195_ = lean_string_utf8_get_fast(v_s_3173_, v_p_3174_);
v___x_3196_ = 65;
v___x_3197_ = lean_uint32_dec_le(v___x_3196_, v___x_3195_);
if (v___x_3197_ == 0)
{
v___y_3181_ = v___x_3195_;
goto v___jp_3180_;
}
else
{
uint32_t v___x_3198_; uint8_t v___x_3199_; 
v___x_3198_ = 90;
v___x_3199_ = lean_uint32_dec_le(v___x_3195_, v___x_3198_);
if (v___x_3199_ == 0)
{
v___y_3181_ = v___x_3195_;
goto v___jp_3180_;
}
else
{
uint32_t v___x_3200_; uint32_t v___x_3201_; 
v___x_3200_ = 32;
v___x_3201_ = lean_uint32_add(v___x_3195_, v___x_3200_);
v___y_3181_ = v___x_3201_;
goto v___jp_3180_;
}
}
}
else
{
lean_dec(v_p_3174_);
return v_s_3173_;
}
v___jp_3175_:
{
lean_object* v___x_3178_; 
v___x_3178_ = lean_nat_add(v_p_3174_, v___y_3177_);
lean_dec(v_p_3174_);
v_s_3173_ = v___y_3176_;
v_p_3174_ = v___x_3178_;
goto _start;
}
v___jp_3180_:
{
lean_object* v___x_3182_; uint32_t v___x_3183_; uint8_t v___x_3184_; 
lean_inc(v_p_3174_);
v___x_3182_ = lean_string_utf8_set(v_s_3173_, v_p_3174_, v___y_3181_);
v___x_3183_ = 127;
v___x_3184_ = lean_uint32_dec_le(v___y_3181_, v___x_3183_);
if (v___x_3184_ == 0)
{
uint32_t v___x_3185_; uint8_t v___x_3186_; 
v___x_3185_ = 2047;
v___x_3186_ = lean_uint32_dec_le(v___y_3181_, v___x_3185_);
if (v___x_3186_ == 0)
{
uint32_t v___x_3187_; uint8_t v___x_3188_; 
v___x_3187_ = 65535;
v___x_3188_ = lean_uint32_dec_le(v___y_3181_, v___x_3187_);
if (v___x_3188_ == 0)
{
lean_object* v___x_3189_; 
v___x_3189_ = lean_unsigned_to_nat(4u);
v___y_3176_ = v___x_3182_;
v___y_3177_ = v___x_3189_;
goto v___jp_3175_;
}
else
{
lean_object* v___x_3190_; 
v___x_3190_ = lean_unsigned_to_nat(3u);
v___y_3176_ = v___x_3182_;
v___y_3177_ = v___x_3190_;
goto v___jp_3175_;
}
}
else
{
lean_object* v___x_3191_; 
v___x_3191_ = lean_unsigned_to_nat(2u);
v___y_3176_ = v___x_3182_;
v___y_3177_ = v___x_3191_;
goto v___jp_3175_;
}
}
else
{
lean_object* v___x_3192_; 
v___x_3192_ = lean_unsigned_to_nat(1u);
v___y_3176_ = v___x_3182_;
v___y_3177_ = v___x_3192_;
goto v___jp_3175_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField(lean_object* v_name_3209_){
_start:
{
lean_object* v___x_3210_; lean_object* v_n_3211_; lean_object* v___x_3212_; uint8_t v___x_3213_; 
v___x_3210_ = lean_unsigned_to_nat(0u);
v_n_3211_ = l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField_spec__0(v_name_3209_, v___x_3210_);
v___x_3212_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__0));
v___x_3213_ = lean_string_dec_eq(v_n_3211_, v___x_3212_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; uint8_t v___x_3215_; 
v___x_3214_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__1));
v___x_3215_ = lean_string_dec_eq(v_n_3211_, v___x_3214_);
if (v___x_3215_ == 0)
{
lean_object* v___x_3216_; uint8_t v___x_3217_; 
v___x_3216_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__2));
v___x_3217_ = lean_string_dec_eq(v_n_3211_, v___x_3216_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3218_; uint8_t v___x_3219_; 
v___x_3218_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__3));
v___x_3219_ = lean_string_dec_eq(v_n_3211_, v___x_3218_);
if (v___x_3219_ == 0)
{
lean_object* v___x_3220_; uint8_t v___x_3221_; 
v___x_3220_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__4));
v___x_3221_ = lean_string_dec_eq(v_n_3211_, v___x_3220_);
if (v___x_3221_ == 0)
{
lean_object* v___x_3222_; uint8_t v___x_3223_; 
v___x_3222_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__5));
v___x_3223_ = lean_string_dec_eq(v_n_3211_, v___x_3222_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; uint8_t v___x_3225_; 
v___x_3224_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__6));
v___x_3225_ = lean_string_dec_eq(v_n_3211_, v___x_3224_);
lean_dec_ref(v_n_3211_);
return v___x_3225_;
}
else
{
lean_dec_ref(v_n_3211_);
return v___x_3223_;
}
}
else
{
lean_dec_ref(v_n_3211_);
return v___x_3221_;
}
}
else
{
lean_dec_ref(v_n_3211_);
return v___x_3219_;
}
}
else
{
lean_dec_ref(v_n_3211_);
return v___x_3217_;
}
}
else
{
lean_dec_ref(v_n_3211_);
return v___x_3215_;
}
}
else
{
lean_dec_ref(v_n_3211_);
return v___x_3213_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___boxed(lean_object* v_name_3226_){
_start:
{
uint8_t v_res_3227_; lean_object* v_r_3228_; 
v_res_3227_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField(v_name_3226_);
v_r_3228_ = lean_box(v_res_3227_);
return v_r_3228_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(lean_object* v_name_3234_){
_start:
{
lean_object* v___x_3235_; lean_object* v_n_3236_; uint8_t v___x_3237_; 
v___x_3235_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_name_3234_);
v_n_3236_ = l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField_spec__0(v_name_3234_, v___x_3235_);
v___x_3237_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField(v_name_3234_);
if (v___x_3237_ == 0)
{
lean_object* v___x_3238_; uint8_t v___x_3239_; 
v___x_3238_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0));
v___x_3239_ = lean_string_dec_eq(v_n_3236_, v___x_3238_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; uint8_t v___x_3241_; 
v___x_3240_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1));
v___x_3241_ = lean_string_dec_eq(v_n_3236_, v___x_3240_);
if (v___x_3241_ == 0)
{
lean_object* v___x_3242_; uint8_t v___x_3243_; 
v___x_3242_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2));
v___x_3243_ = lean_string_dec_eq(v_n_3236_, v___x_3242_);
if (v___x_3243_ == 0)
{
lean_object* v___x_3244_; uint8_t v___x_3245_; 
v___x_3244_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3));
v___x_3245_ = lean_string_dec_eq(v_n_3236_, v___x_3244_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3246_; uint8_t v___x_3247_; 
v___x_3246_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4));
v___x_3247_ = lean_string_dec_eq(v_n_3236_, v___x_3246_);
lean_dec_ref(v_n_3236_);
return v___x_3247_;
}
else
{
lean_dec_ref(v_n_3236_);
return v___x_3245_;
}
}
else
{
lean_dec_ref(v_n_3236_);
return v___x_3243_;
}
}
else
{
lean_dec_ref(v_n_3236_);
return v___x_3241_;
}
}
else
{
lean_dec_ref(v_n_3236_);
return v___x_3239_;
}
}
else
{
lean_dec_ref(v_n_3236_);
return v___x_3237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___boxed(lean_object* v_name_3248_){
_start:
{
uint8_t v_res_3249_; lean_object* v_r_3250_; 
v_res_3249_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_name_3248_);
v_r_3250_ = lean_box(v_res_3249_);
return v_r_3250_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailerHeader(lean_object* v_limits_3252_, uint8_t v_strict_3253_, lean_object* v_a_3254_){
_start:
{
lean_object* v___x_3255_; 
v___x_3255_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_3252_, v_a_3254_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v_res_3256_; 
v_res_3256_ = lean_ctor_get(v___x_3255_, 1);
lean_inc(v_res_3256_);
if (lean_obj_tag(v_res_3256_) == 1)
{
lean_object* v_val_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3279_; 
v_val_3257_ = lean_ctor_get(v_res_3256_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v_res_3256_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3259_ = v_res_3256_;
v_isShared_3260_ = v_isSharedCheck_3279_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_val_3257_);
lean_dec(v_res_3256_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3279_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v_pos_3261_; lean_object* v_fst_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3277_; 
v_pos_3261_ = lean_ctor_get(v___x_3255_, 0);
v_fst_3262_ = lean_ctor_get(v_val_3257_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v_val_3257_);
if (v_isSharedCheck_3277_ == 0)
{
lean_object* v_unused_3278_; 
v_unused_3278_ = lean_ctor_get(v_val_3257_, 1);
lean_dec(v_unused_3278_);
v___x_3264_ = v_val_3257_;
v_isShared_3265_ = v_isSharedCheck_3277_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_fst_3262_);
lean_dec(v_val_3257_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3277_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
uint8_t v___x_3275_; 
lean_inc(v_fst_3262_);
v___x_3275_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField(v_fst_3262_);
if (v___x_3275_ == 0)
{
if (v_strict_3253_ == 0)
{
lean_del_object(v___x_3264_);
lean_dec(v_fst_3262_);
lean_del_object(v___x_3259_);
return v___x_3255_;
}
else
{
uint8_t v___x_3276_; 
lean_inc(v_fst_3262_);
v___x_3276_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_fst_3262_);
if (v___x_3276_ == 0)
{
lean_del_object(v___x_3264_);
lean_dec(v_fst_3262_);
lean_del_object(v___x_3259_);
return v___x_3255_;
}
else
{
lean_inc(v_pos_3261_);
lean_dec_ref_known(v___x_3255_, 2);
goto v___jp_3266_;
}
}
}
else
{
lean_inc(v_pos_3261_);
lean_dec_ref_known(v___x_3255_, 2);
goto v___jp_3266_;
}
v___jp_3266_:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3270_; 
v___x_3267_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseTrailerHeader___closed__0));
v___x_3268_ = lean_string_append(v___x_3267_, v_fst_3262_);
lean_dec(v_fst_3262_);
if (v_isShared_3260_ == 0)
{
lean_ctor_set(v___x_3259_, 0, v___x_3268_);
v___x_3270_ = v___x_3259_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3268_);
v___x_3270_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
lean_object* v___x_3272_; 
if (v_isShared_3265_ == 0)
{
lean_ctor_set_tag(v___x_3264_, 1);
lean_ctor_set(v___x_3264_, 1, v___x_3270_);
lean_ctor_set(v___x_3264_, 0, v_pos_3261_);
v___x_3272_ = v___x_3264_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_pos_3261_);
lean_ctor_set(v_reuseFailAlloc_3273_, 1, v___x_3270_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
}
}
}
else
{
lean_dec(v_res_3256_);
return v___x_3255_;
}
}
else
{
return v___x_3255_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailerHeader___boxed(lean_object* v_limits_3280_, lean_object* v_strict_3281_, lean_object* v_a_3282_){
_start:
{
uint8_t v_strict_boxed_3283_; lean_object* v_res_3284_; 
v_strict_boxed_3283_ = lean_unbox(v_strict_3281_);
v_res_3284_ = l_Std_Http_Protocol_H1_parseTrailerHeader(v_limits_3280_, v_strict_boxed_3283_, v_a_3282_);
lean_dec_ref(v_limits_3280_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailers(lean_object* v_limits_3285_, lean_object* v_a_3286_){
_start:
{
lean_object* v_maxTrailerHeaders_3287_; uint8_t v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v_maxTrailerHeaders_3287_ = lean_ctor_get(v_limits_3285_, 19);
lean_inc(v_maxTrailerHeaders_3287_);
v___x_3288_ = 1;
v___x_3289_ = lean_box(v___x_3288_);
v___x_3290_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_parseTrailerHeader___boxed), 3, 2);
lean_closure_set(v___x_3290_, 0, v_limits_3285_);
lean_closure_set(v___x_3290_, 1, v___x_3289_);
v___x_3291_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___x_3290_, v_maxTrailerHeaders_3287_, v_a_3286_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v_pos_3292_; lean_object* v_res_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v_pos_3292_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_pos_3292_);
v_res_3293_ = lean_ctor_get(v___x_3291_, 1);
lean_inc(v_res_3293_);
lean_dec_ref_known(v___x_3291_, 2);
v___x_3294_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3295_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3294_, v_pos_3292_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_object* v_pos_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3303_; 
v_pos_3296_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3303_ == 0)
{
lean_object* v_unused_3304_; 
v_unused_3304_ = lean_ctor_get(v___x_3295_, 1);
lean_dec(v_unused_3304_);
v___x_3298_ = v___x_3295_;
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_pos_3296_);
lean_dec(v___x_3295_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3301_; 
if (v_isShared_3299_ == 0)
{
lean_ctor_set(v___x_3298_, 1, v_res_3293_);
v___x_3301_ = v___x_3298_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_pos_3296_);
lean_ctor_set(v_reuseFailAlloc_3302_, 1, v_res_3293_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
else
{
lean_object* v_pos_3305_; lean_object* v_err_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3313_; 
lean_dec(v_res_3293_);
v_pos_3305_ = lean_ctor_get(v___x_3295_, 0);
v_err_3306_ = lean_ctor_get(v___x_3295_, 1);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3308_ = v___x_3295_;
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_err_3306_);
lean_inc(v_pos_3305_);
lean_dec(v___x_3295_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3311_; 
if (v_isShared_3309_ == 0)
{
v___x_3311_ = v___x_3308_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_pos_3305_);
lean_ctor_set(v_reuseFailAlloc_3312_, 1, v_err_3306_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
}
else
{
return v___x_3291_;
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(uint8_t v_c_3314_){
_start:
{
uint32_t v___x_3315_; uint32_t v___x_3323_; uint8_t v___x_3324_; 
v___x_3315_ = lean_uint8_to_uint32(v_c_3314_);
v___x_3323_ = 33;
v___x_3324_ = lean_uint32_dec_le(v___x_3323_, v___x_3315_);
if (v___x_3324_ == 0)
{
goto v___jp_3316_;
}
else
{
uint32_t v___x_3325_; uint8_t v___x_3326_; 
v___x_3325_ = 126;
v___x_3326_ = lean_uint32_dec_le(v___x_3315_, v___x_3325_);
if (v___x_3326_ == 0)
{
goto v___jp_3316_;
}
else
{
return v___x_3326_;
}
}
v___jp_3316_:
{
uint32_t v___x_3317_; uint8_t v___x_3318_; 
v___x_3317_ = 128;
v___x_3318_ = lean_uint32_dec_le(v___x_3317_, v___x_3315_);
if (v___x_3318_ == 0)
{
uint32_t v___x_3319_; uint8_t v___x_3320_; 
v___x_3319_ = 32;
v___x_3320_ = lean_uint32_dec_eq(v___x_3315_, v___x_3319_);
if (v___x_3320_ == 0)
{
uint32_t v___x_3321_; uint8_t v___x_3322_; 
v___x_3321_ = 9;
v___x_3322_ = lean_uint32_dec_eq(v___x_3315_, v___x_3321_);
return v___x_3322_;
}
else
{
return v___x_3320_;
}
}
else
{
return v___x_3318_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte___boxed(lean_object* v_c_3327_){
_start:
{
uint8_t v_c_boxed_3328_; uint8_t v_res_3329_; lean_object* v_r_3330_; 
v_c_boxed_3328_ = lean_unbox(v_c_3327_);
v_res_3329_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(v_c_boxed_3328_);
v_r_3330_ = lean_box(v_res_3329_);
return v_r_3330_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(lean_object* v_limits_3331_, lean_object* v_a_3332_){
_start:
{
lean_object* v_maxReasonPhraseLength_3333_; lean_object* v___f_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v_snd_3337_; lean_object* v_snd_3338_; uint8_t v___x_3339_; 
v_maxReasonPhraseLength_3333_ = lean_ctor_get(v_limits_3331_, 18);
v___f_3334_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4));
v___x_3335_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_3332_);
v___x_3336_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3334_, v_maxReasonPhraseLength_3333_, v___x_3335_, v_a_3332_);
v_snd_3337_ = lean_ctor_get(v___x_3336_, 1);
lean_inc(v_snd_3337_);
v_snd_3338_ = lean_ctor_get(v_snd_3337_, 1);
v___x_3339_ = lean_unbox(v_snd_3338_);
if (v___x_3339_ == 0)
{
lean_object* v_fst_3340_; lean_object* v_fst_3341_; lean_object* v_array_3342_; lean_object* v_idx_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3363_; 
v_fst_3340_ = lean_ctor_get(v___x_3336_, 0);
lean_inc(v_fst_3340_);
lean_dec_ref(v___x_3336_);
v_fst_3341_ = lean_ctor_get(v_snd_3337_, 0);
lean_inc(v_fst_3341_);
lean_dec(v_snd_3337_);
v_array_3342_ = lean_ctor_get(v_a_3332_, 0);
v_idx_3343_ = lean_ctor_get(v_a_3332_, 1);
v_isSharedCheck_3363_ = !lean_is_exclusive(v_a_3332_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3345_ = v_a_3332_;
v_isShared_3346_ = v_isSharedCheck_3363_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_idx_3343_);
lean_inc(v_array_3342_);
lean_dec(v_a_3332_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3363_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v_lower_3348_; lean_object* v_upper_3349_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___y_3360_; uint8_t v___x_3362_; 
v___x_3357_ = lean_nat_add(v_idx_3343_, v_fst_3340_);
lean_dec(v_fst_3340_);
v___x_3358_ = lean_byte_array_size(v_array_3342_);
v___x_3362_ = lean_nat_dec_le(v_idx_3343_, v___x_3335_);
if (v___x_3362_ == 0)
{
v___y_3360_ = v_idx_3343_;
goto v___jp_3359_;
}
else
{
lean_dec(v_idx_3343_);
v___y_3360_ = v___x_3335_;
goto v___jp_3359_;
}
v___jp_3347_:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3355_; 
v___x_3350_ = l_ByteArray_toByteSlice(v_array_3342_, v_lower_3348_, v_upper_3349_);
v___x_3351_ = l_ByteSlice_toByteArray(v___x_3350_);
v___x_3352_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2));
v___x_3353_ = l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go(v___x_3351_, v___x_3335_, v___x_3352_);
lean_dec_ref(v___x_3351_);
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 1, v___x_3353_);
lean_ctor_set(v___x_3345_, 0, v_fst_3341_);
v___x_3355_ = v___x_3345_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_fst_3341_);
lean_ctor_set(v_reuseFailAlloc_3356_, 1, v___x_3353_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
v___jp_3359_:
{
uint8_t v___x_3361_; 
v___x_3361_ = lean_nat_dec_le(v___x_3357_, v___x_3358_);
if (v___x_3361_ == 0)
{
lean_dec(v___x_3357_);
v_lower_3348_ = v___y_3360_;
v_upper_3349_ = v___x_3358_;
goto v___jp_3347_;
}
else
{
v_lower_3348_ = v___y_3360_;
v_upper_3349_ = v___x_3357_;
goto v___jp_3347_;
}
}
}
}
else
{
lean_object* v_fst_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3372_; 
lean_dec_ref(v___x_3336_);
lean_dec_ref(v_a_3332_);
v_fst_3364_ = lean_ctor_get(v_snd_3337_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v_snd_3337_);
if (v_isSharedCheck_3372_ == 0)
{
lean_object* v_unused_3373_; 
v_unused_3373_ = lean_ctor_get(v_snd_3337_, 1);
lean_dec(v_unused_3373_);
v___x_3366_ = v_snd_3337_;
v_isShared_3367_ = v_isSharedCheck_3372_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_fst_3364_);
lean_dec(v_snd_3337_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3372_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3368_; lean_object* v___x_3370_; 
v___x_3368_ = lean_box(0);
if (v_isShared_3367_ == 0)
{
lean_ctor_set_tag(v___x_3366_, 1);
lean_ctor_set(v___x_3366_, 1, v___x_3368_);
v___x_3370_ = v___x_3366_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_fst_3364_);
lean_ctor_set(v_reuseFailAlloc_3371_, 1, v___x_3368_);
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
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___boxed(lean_object* v_limits_3374_, lean_object* v_a_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_3374_, v_a_3375_);
lean_dec_ref(v_limits_3374_);
return v_res_3376_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(lean_object* v_x_3377_){
_start:
{
if (lean_obj_tag(v_x_3377_) == 0)
{
uint8_t v___x_3378_; 
v___x_3378_ = 1;
return v___x_3378_;
}
else
{
lean_object* v_head_3379_; lean_object* v_tail_3380_; uint32_t v___x_3386_; uint32_t v___x_3387_; uint8_t v___x_3388_; 
v_head_3379_ = lean_ctor_get(v_x_3377_, 0);
v_tail_3380_ = lean_ctor_get(v_x_3377_, 1);
v___x_3386_ = 9;
v___x_3387_ = lean_unbox_uint32(v_head_3379_);
v___x_3388_ = lean_uint32_dec_eq(v___x_3387_, v___x_3386_);
if (v___x_3388_ == 0)
{
uint32_t v___x_3389_; uint32_t v___x_3390_; uint8_t v___x_3391_; 
v___x_3389_ = 32;
v___x_3390_ = lean_unbox_uint32(v_head_3379_);
v___x_3391_ = lean_uint32_dec_eq(v___x_3390_, v___x_3389_);
if (v___x_3391_ == 0)
{
uint32_t v___x_3392_; uint32_t v___x_3393_; uint8_t v___x_3394_; 
v___x_3392_ = 33;
v___x_3393_ = lean_unbox_uint32(v_head_3379_);
v___x_3394_ = lean_uint32_dec_le(v___x_3392_, v___x_3393_);
if (v___x_3394_ == 0)
{
goto v___jp_3381_;
}
else
{
uint32_t v___x_3395_; uint32_t v___x_3396_; uint8_t v___x_3397_; 
v___x_3395_ = 126;
v___x_3396_ = lean_unbox_uint32(v_head_3379_);
v___x_3397_ = lean_uint32_dec_le(v___x_3396_, v___x_3395_);
if (v___x_3397_ == 0)
{
goto v___jp_3381_;
}
else
{
v_x_3377_ = v_tail_3380_;
goto _start;
}
}
}
else
{
v_x_3377_ = v_tail_3380_;
goto _start;
}
}
else
{
v_x_3377_ = v_tail_3380_;
goto _start;
}
v___jp_3381_:
{
uint32_t v___x_3382_; uint32_t v___x_3383_; uint8_t v___x_3384_; 
v___x_3382_ = 128;
v___x_3383_ = lean_unbox_uint32(v_head_3379_);
v___x_3384_ = lean_uint32_dec_le(v___x_3382_, v___x_3383_);
if (v___x_3384_ == 0)
{
return v___x_3384_;
}
else
{
v_x_3377_ = v_tail_3380_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0___boxed(lean_object* v_x_3401_){
_start:
{
uint8_t v_res_3402_; lean_object* v_r_3403_; 
v_res_3402_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v_x_3401_);
lean_dec(v_x_3401_);
v_r_3403_ = lean_box(v_res_3402_);
return v_r_3403_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(lean_object* v_limits_3407_, lean_object* v_a_3408_){
_start:
{
lean_object* v___y_3413_; lean_object* v___y_3417_; lean_object* v_array_3420_; lean_object* v_idx_3421_; lean_object* v___x_3422_; uint8_t v___x_3423_; 
v_array_3420_ = lean_ctor_get(v_a_3408_, 0);
v_idx_3421_ = lean_ctor_get(v_a_3408_, 1);
v___x_3422_ = lean_byte_array_size(v_array_3420_);
v___x_3423_ = lean_nat_dec_lt(v_idx_3421_, v___x_3422_);
if (v___x_3423_ == 0)
{
lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3424_ = lean_box(0);
v___x_3425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3425_, 0, v_a_3408_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
return v___x_3425_;
}
else
{
uint8_t v_c_3426_; uint8_t v___x_3427_; uint8_t v___x_3428_; 
v_c_3426_ = lean_byte_array_fget(v_array_3420_, v_idx_3421_);
v___x_3427_ = 48;
v___x_3428_ = lean_uint8_dec_le(v___x_3427_, v_c_3426_);
if (v___x_3428_ == 0)
{
goto v___jp_3409_;
}
else
{
uint8_t v___x_3429_; uint8_t v___x_3430_; 
v___x_3429_ = 57;
v___x_3430_ = lean_uint8_dec_le(v_c_3426_, v___x_3429_);
if (v___x_3430_ == 0)
{
goto v___jp_3409_;
}
else
{
lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3530_; 
lean_inc(v_idx_3421_);
lean_inc_ref(v_array_3420_);
v_isSharedCheck_3530_ = !lean_is_exclusive(v_a_3408_);
if (v_isSharedCheck_3530_ == 0)
{
lean_object* v_unused_3531_; lean_object* v_unused_3532_; 
v_unused_3531_ = lean_ctor_get(v_a_3408_, 1);
lean_dec(v_unused_3531_);
v_unused_3532_ = lean_ctor_get(v_a_3408_, 0);
lean_dec(v_unused_3532_);
v___x_3432_ = v_a_3408_;
v_isShared_3433_ = v_isSharedCheck_3530_;
goto v_resetjp_3431_;
}
else
{
lean_dec(v_a_3408_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3530_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v_it_x27_3437_; 
v___x_3434_ = lean_unsigned_to_nat(1u);
v___x_3435_ = lean_nat_add(v_idx_3421_, v___x_3434_);
lean_dec(v_idx_3421_);
lean_inc(v___x_3435_);
lean_inc_ref(v_array_3420_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v___x_3435_);
v_it_x27_3437_ = v___x_3432_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_array_3420_);
lean_ctor_set(v_reuseFailAlloc_3529_, 1, v___x_3435_);
v_it_x27_3437_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
uint8_t v___x_3441_; 
v___x_3441_ = lean_nat_dec_lt(v___x_3435_, v___x_3422_);
if (v___x_3441_ == 0)
{
lean_object* v___x_3442_; lean_object* v___x_3443_; 
lean_dec(v___x_3435_);
lean_dec_ref(v_array_3420_);
v___x_3442_ = lean_box(0);
v___x_3443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3443_, 0, v_it_x27_3437_);
lean_ctor_set(v___x_3443_, 1, v___x_3442_);
return v___x_3443_;
}
else
{
uint8_t v_c_3444_; uint8_t v___x_3445_; 
v_c_3444_ = lean_byte_array_fget(v_array_3420_, v___x_3435_);
v___x_3445_ = lean_uint8_dec_le(v___x_3427_, v_c_3444_);
if (v___x_3445_ == 0)
{
lean_dec(v___x_3435_);
lean_dec_ref(v_array_3420_);
goto v___jp_3438_;
}
else
{
uint8_t v___x_3446_; 
v___x_3446_ = lean_uint8_dec_le(v_c_3444_, v___x_3429_);
if (v___x_3446_ == 0)
{
lean_dec(v___x_3435_);
lean_dec_ref(v_array_3420_);
goto v___jp_3438_;
}
else
{
lean_object* v___x_3447_; lean_object* v_it_x27_3448_; uint8_t v___x_3452_; 
lean_dec_ref(v_it_x27_3437_);
v___x_3447_ = lean_nat_add(v___x_3435_, v___x_3434_);
lean_dec(v___x_3435_);
lean_inc(v___x_3447_);
lean_inc_ref(v_array_3420_);
v_it_x27_3448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3448_, 0, v_array_3420_);
lean_ctor_set(v_it_x27_3448_, 1, v___x_3447_);
v___x_3452_ = lean_nat_dec_lt(v___x_3447_, v___x_3422_);
if (v___x_3452_ == 0)
{
lean_object* v___x_3453_; lean_object* v___x_3454_; 
lean_dec(v___x_3447_);
lean_dec_ref(v_array_3420_);
v___x_3453_ = lean_box(0);
v___x_3454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3454_, 0, v_it_x27_3448_);
lean_ctor_set(v___x_3454_, 1, v___x_3453_);
return v___x_3454_;
}
else
{
uint8_t v_c_3455_; uint8_t v___x_3456_; 
v_c_3455_ = lean_byte_array_fget(v_array_3420_, v___x_3447_);
v___x_3456_ = lean_uint8_dec_le(v___x_3427_, v_c_3455_);
if (v___x_3456_ == 0)
{
lean_dec(v___x_3447_);
lean_dec_ref(v_array_3420_);
goto v___jp_3449_;
}
else
{
uint8_t v___x_3457_; 
v___x_3457_ = lean_uint8_dec_le(v_c_3455_, v___x_3429_);
if (v___x_3457_ == 0)
{
lean_dec(v___x_3447_);
lean_dec_ref(v_array_3420_);
goto v___jp_3449_;
}
else
{
lean_object* v___x_3458_; uint32_t v___x_3459_; uint32_t v___x_3460_; lean_object* v___x_3461_; lean_object* v_it_x27_3462_; uint32_t v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v_pos_3509_; lean_object* v_idx_3510_; lean_object* v_err_3511_; uint8_t v___x_3515_; 
lean_dec_ref_known(v_it_x27_3448_, 2);
v___x_3458_ = lean_unsigned_to_nat(48u);
v___x_3459_ = lean_uint8_to_uint32(v_c_3426_);
v___x_3460_ = lean_uint8_to_uint32(v_c_3444_);
v___x_3461_ = lean_nat_add(v___x_3447_, v___x_3434_);
lean_dec(v___x_3447_);
lean_inc(v___x_3461_);
lean_inc_ref(v_array_3420_);
v_it_x27_3462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3462_, 0, v_array_3420_);
lean_ctor_set(v_it_x27_3462_, 1, v___x_3461_);
v___x_3463_ = lean_uint8_to_uint32(v_c_3455_);
v___x_3464_ = lean_uint32_to_nat(v___x_3459_);
v___x_3465_ = lean_nat_sub(v___x_3464_, v___x_3458_);
lean_dec(v___x_3464_);
v___x_3466_ = lean_unsigned_to_nat(100u);
v___x_3467_ = lean_nat_mul(v___x_3465_, v___x_3466_);
lean_dec(v___x_3465_);
v___x_3468_ = lean_uint32_to_nat(v___x_3460_);
v___x_3469_ = lean_nat_sub(v___x_3468_, v___x_3458_);
lean_dec(v___x_3468_);
v___x_3470_ = lean_unsigned_to_nat(10u);
v___x_3471_ = lean_nat_mul(v___x_3469_, v___x_3470_);
lean_dec(v___x_3469_);
v___x_3472_ = lean_nat_add(v___x_3467_, v___x_3471_);
lean_dec(v___x_3471_);
lean_dec(v___x_3467_);
v___x_3473_ = lean_uint32_to_nat(v___x_3463_);
v___x_3474_ = lean_nat_sub(v___x_3473_, v___x_3458_);
lean_dec(v___x_3473_);
v___x_3475_ = lean_nat_add(v___x_3472_, v___x_3474_);
lean_dec(v___x_3474_);
lean_dec(v___x_3472_);
v___x_3515_ = lean_nat_dec_lt(v___x_3461_, v___x_3422_);
if (v___x_3515_ == 0)
{
lean_object* v___x_3516_; 
lean_dec_ref(v_array_3420_);
v___x_3516_ = lean_box(0);
lean_inc(v___x_3461_);
v_pos_3509_ = v_it_x27_3462_;
v_idx_3510_ = v___x_3461_;
v_err_3511_ = v___x_3516_;
goto v___jp_3508_;
}
else
{
uint8_t v___x_3517_; uint8_t v_got_3518_; uint8_t v___x_3519_; 
v___x_3517_ = 32;
v_got_3518_ = lean_byte_array_fget(v_array_3420_, v___x_3461_);
v___x_3519_ = lean_uint8_dec_eq(v_got_3518_, v___x_3517_);
if (v___x_3519_ == 0)
{
lean_object* v___x_3520_; 
lean_dec_ref(v_array_3420_);
v___x_3520_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
lean_inc(v___x_3461_);
v_pos_3509_ = v_it_x27_3462_;
v_idx_3510_ = v___x_3461_;
v_err_3511_ = v___x_3520_;
goto v___jp_3508_;
}
else
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
lean_dec_ref_known(v_it_x27_3462_, 2);
v___x_3521_ = lean_nat_add(v___x_3461_, v___x_3434_);
v___x_3522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3522_, 0, v_array_3420_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
v___x_3523_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_3407_, v___x_3522_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_pos_3524_; lean_object* v_res_3525_; 
lean_dec(v___x_3461_);
v_pos_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_pos_3524_);
v_res_3525_ = lean_ctor_get(v___x_3523_, 1);
lean_inc(v_res_3525_);
lean_dec_ref_known(v___x_3523_, 2);
v___y_3477_ = v_pos_3524_;
v___y_3478_ = v_res_3525_;
goto v___jp_3476_;
}
else
{
lean_object* v_pos_3526_; lean_object* v___x_3527_; lean_object* v_idx_3528_; 
v_pos_3526_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_pos_3526_);
lean_dec_ref_known(v___x_3523_, 2);
v___x_3527_ = lean_box(0);
v_idx_3528_ = lean_ctor_get(v_pos_3526_, 1);
lean_inc(v_idx_3528_);
v_pos_3509_ = v_pos_3526_;
v_idx_3510_ = v_idx_3528_;
v_err_3511_ = v___x_3527_;
goto v___jp_3508_;
}
}
}
v___jp_3476_:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3479_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3480_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3479_, v___y_3477_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_pos_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3497_; 
v_pos_3481_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3497_ == 0)
{
lean_object* v_unused_3498_; 
v_unused_3498_ = lean_ctor_get(v___x_3480_, 1);
lean_dec(v_unused_3498_);
v___x_3483_ = v___x_3480_;
v_isShared_3484_ = v_isSharedCheck_3497_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_pos_3481_);
lean_dec(v___x_3480_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3497_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
uint8_t v___x_3485_; 
v___x_3485_ = lean_nat_dec_lt(v___x_3475_, v___x_3466_);
if (v___x_3485_ == 0)
{
lean_object* v___x_3486_; uint8_t v___x_3487_; 
v___x_3486_ = lean_unsigned_to_nat(600u);
v___x_3487_ = lean_nat_dec_le(v___x_3486_, v___x_3475_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; uint8_t v___x_3489_; 
lean_inc_ref(v___y_3478_);
v___x_3488_ = l_String_toListImpl(v___y_3478_);
v___x_3489_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v___x_3488_);
lean_dec(v___x_3488_);
if (v___x_3489_ == 0)
{
lean_del_object(v___x_3483_);
lean_dec_ref(v___y_3478_);
lean_dec(v___x_3475_);
v___y_3417_ = v_pos_3481_;
goto v___jp_3416_;
}
else
{
lean_object* v___x_3490_; uint16_t v___x_3491_; lean_object* v___x_3492_; 
v___x_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3490_, 0, v___y_3478_);
v___x_3491_ = lean_uint16_of_nat(v___x_3475_);
lean_dec(v___x_3475_);
v___x_3492_ = l_Std_Http_Status_ofCode(v___x_3490_, v___x_3491_);
if (lean_obj_tag(v___x_3492_) == 1)
{
lean_object* v_val_3493_; lean_object* v___x_3495_; 
v_val_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_val_3493_);
lean_dec_ref_known(v___x_3492_, 1);
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 1, v_val_3493_);
v___x_3495_ = v___x_3483_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_pos_3481_);
lean_ctor_set(v_reuseFailAlloc_3496_, 1, v_val_3493_);
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
lean_dec(v___x_3492_);
lean_del_object(v___x_3483_);
v___y_3417_ = v_pos_3481_;
goto v___jp_3416_;
}
}
}
else
{
lean_del_object(v___x_3483_);
lean_dec_ref(v___y_3478_);
lean_dec(v___x_3475_);
v___y_3413_ = v_pos_3481_;
goto v___jp_3412_;
}
}
else
{
lean_del_object(v___x_3483_);
lean_dec_ref(v___y_3478_);
lean_dec(v___x_3475_);
v___y_3413_ = v_pos_3481_;
goto v___jp_3412_;
}
}
}
else
{
lean_object* v_pos_3499_; lean_object* v_err_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3507_; 
lean_dec_ref(v___y_3478_);
lean_dec(v___x_3475_);
v_pos_3499_ = lean_ctor_get(v___x_3480_, 0);
v_err_3500_ = lean_ctor_get(v___x_3480_, 1);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3502_ = v___x_3480_;
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_err_3500_);
lean_inc(v_pos_3499_);
lean_dec(v___x_3480_);
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
uint8_t v___x_3512_; 
v___x_3512_ = lean_nat_dec_eq(v___x_3461_, v_idx_3510_);
lean_dec(v_idx_3510_);
lean_dec(v___x_3461_);
if (v___x_3512_ == 0)
{
lean_object* v___x_3513_; 
lean_dec(v___x_3475_);
lean_inc(v_err_3511_);
v___x_3513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3513_, 0, v_pos_3509_);
lean_ctor_set(v___x_3513_, 1, v_err_3511_);
return v___x_3513_;
}
else
{
lean_object* v___x_3514_; 
v___x_3514_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2));
v___y_3477_ = v_pos_3509_;
v___y_3478_ = v___x_3514_;
goto v___jp_3476_;
}
}
}
}
}
v___jp_3449_:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3450_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3451_, 0, v_it_x27_3448_);
lean_ctor_set(v___x_3451_, 1, v___x_3450_);
return v___x_3451_;
}
}
}
}
v___jp_3438_:
{
lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3439_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3440_, 0, v_it_x27_3437_);
lean_ctor_set(v___x_3440_, 1, v___x_3439_);
return v___x_3440_;
}
}
}
}
}
}
v___jp_3409_:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3410_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3411_, 0, v_a_3408_);
lean_ctor_set(v___x_3411_, 1, v___x_3410_);
return v___x_3411_;
}
v___jp_3412_:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3414_ = lean_box(52);
v___x_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___y_3413_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
return v___x_3415_;
}
v___jp_3416_:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3418_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__1));
v___x_3419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3419_, 0, v___y_3417_);
lean_ctor_set(v___x_3419_, 1, v___x_3418_);
return v___x_3419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___boxed(lean_object* v_limits_3533_, lean_object* v_a_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_3533_, v_a_3534_);
lean_dec_ref(v_limits_3533_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine(lean_object* v_limits_3536_, lean_object* v_a_3537_){
_start:
{
lean_object* v___x_3538_; 
v___x_3538_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_3537_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_pos_3539_; lean_object* v_res_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3614_; 
v_pos_3539_ = lean_ctor_get(v___x_3538_, 0);
v_res_3540_ = lean_ctor_get(v___x_3538_, 1);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3542_ = v___x_3538_;
v_isShared_3543_ = v_isSharedCheck_3614_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_res_3540_);
lean_inc(v_pos_3539_);
lean_dec(v___x_3538_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3614_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v_array_3544_; lean_object* v_idx_3545_; lean_object* v___x_3546_; uint8_t v___x_3547_; 
v_array_3544_ = lean_ctor_get(v_pos_3539_, 0);
v_idx_3545_ = lean_ctor_get(v_pos_3539_, 1);
v___x_3546_ = lean_byte_array_size(v_array_3544_);
v___x_3547_ = lean_nat_dec_lt(v_idx_3545_, v___x_3546_);
if (v___x_3547_ == 0)
{
lean_object* v___x_3548_; lean_object* v___x_3550_; 
lean_dec(v_res_3540_);
v___x_3548_ = lean_box(0);
if (v_isShared_3543_ == 0)
{
lean_ctor_set_tag(v___x_3542_, 1);
lean_ctor_set(v___x_3542_, 1, v___x_3548_);
v___x_3550_ = v___x_3542_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_pos_3539_);
lean_ctor_set(v_reuseFailAlloc_3551_, 1, v___x_3548_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
else
{
uint8_t v___x_3552_; uint8_t v_got_3553_; uint8_t v___x_3554_; 
v___x_3552_ = 32;
v_got_3553_ = lean_byte_array_fget(v_array_3544_, v_idx_3545_);
v___x_3554_ = lean_uint8_dec_eq(v_got_3553_, v___x_3552_);
if (v___x_3554_ == 0)
{
lean_object* v___x_3555_; lean_object* v___x_3557_; 
lean_dec(v_res_3540_);
v___x_3555_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_3543_ == 0)
{
lean_ctor_set_tag(v___x_3542_, 1);
lean_ctor_set(v___x_3542_, 1, v___x_3555_);
v___x_3557_ = v___x_3542_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_pos_3539_);
lean_ctor_set(v_reuseFailAlloc_3558_, 1, v___x_3555_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
return v___x_3557_;
}
}
else
{
lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3611_; 
lean_inc(v_idx_3545_);
lean_inc_ref(v_array_3544_);
v_isSharedCheck_3611_ = !lean_is_exclusive(v_pos_3539_);
if (v_isSharedCheck_3611_ == 0)
{
lean_object* v_unused_3612_; lean_object* v_unused_3613_; 
v_unused_3612_ = lean_ctor_get(v_pos_3539_, 1);
lean_dec(v_unused_3612_);
v_unused_3613_ = lean_ctor_get(v_pos_3539_, 0);
lean_dec(v_unused_3613_);
v___x_3560_ = v_pos_3539_;
v_isShared_3561_ = v_isSharedCheck_3611_;
goto v_resetjp_3559_;
}
else
{
lean_dec(v_pos_3539_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3611_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v_fst_3562_; lean_object* v_snd_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3610_; 
v_fst_3562_ = lean_ctor_get(v_res_3540_, 0);
v_snd_3563_ = lean_ctor_get(v_res_3540_, 1);
v_isSharedCheck_3610_ = !lean_is_exclusive(v_res_3540_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3565_ = v_res_3540_;
v_isShared_3566_ = v_isSharedCheck_3610_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_snd_3563_);
lean_inc(v_fst_3562_);
lean_dec(v_res_3540_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3610_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3570_; 
v___x_3567_ = lean_unsigned_to_nat(1u);
v___x_3568_ = lean_nat_add(v_idx_3545_, v___x_3567_);
lean_dec(v_idx_3545_);
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 1, v___x_3568_);
v___x_3570_ = v___x_3560_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_array_3544_);
lean_ctor_set(v_reuseFailAlloc_3609_, 1, v___x_3568_);
v___x_3570_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
lean_object* v___x_3571_; 
v___x_3571_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_3536_, v___x_3570_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_pos_3572_; lean_object* v_res_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3599_; 
v_pos_3572_ = lean_ctor_get(v___x_3571_, 0);
v_res_3573_ = lean_ctor_get(v___x_3571_, 1);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3575_ = v___x_3571_;
v_isShared_3576_ = v_isSharedCheck_3599_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_res_3573_);
lean_inc(v_pos_3572_);
lean_dec(v___x_3571_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3599_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
uint8_t v___x_3582_; 
v___x_3582_ = lean_nat_dec_eq(v_fst_3562_, v___x_3567_);
lean_dec(v_fst_3562_);
if (v___x_3582_ == 0)
{
lean_del_object(v___x_3565_);
goto v___jp_3583_;
}
else
{
uint8_t v___x_3592_; 
v___x_3592_ = lean_nat_dec_le(v___x_3567_, v_snd_3563_);
if (v___x_3592_ == 0)
{
lean_del_object(v___x_3565_);
goto v___jp_3583_;
}
else
{
uint8_t v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3597_; 
lean_del_object(v___x_3575_);
lean_dec(v_snd_3563_);
lean_del_object(v___x_3542_);
v___x_3593_ = 1;
v___x_3594_ = l_Std_Http_Headers_empty;
v___x_3595_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3595_, 0, v_res_3573_);
lean_ctor_set(v___x_3595_, 1, v___x_3594_);
lean_ctor_set_uint8(v___x_3595_, sizeof(void*)*2, v___x_3593_);
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 1, v___x_3595_);
lean_ctor_set(v___x_3565_, 0, v_pos_3572_);
v___x_3597_ = v___x_3565_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_pos_3572_);
lean_ctor_set(v_reuseFailAlloc_3598_, 1, v___x_3595_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
v___jp_3577_:
{
lean_object* v___x_3578_; lean_object* v___x_3580_; 
v___x_3578_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
if (v_isShared_3576_ == 0)
{
lean_ctor_set_tag(v___x_3575_, 1);
lean_ctor_set(v___x_3575_, 1, v___x_3578_);
v___x_3580_ = v___x_3575_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_pos_3572_);
lean_ctor_set(v_reuseFailAlloc_3581_, 1, v___x_3578_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
v___jp_3583_:
{
if (v___x_3582_ == 0)
{
lean_dec(v_res_3573_);
lean_dec(v_snd_3563_);
lean_del_object(v___x_3542_);
goto v___jp_3577_;
}
else
{
lean_object* v___x_3584_; uint8_t v___x_3585_; 
v___x_3584_ = lean_unsigned_to_nat(0u);
v___x_3585_ = lean_nat_dec_eq(v_snd_3563_, v___x_3584_);
lean_dec(v_snd_3563_);
if (v___x_3585_ == 0)
{
lean_dec(v_res_3573_);
lean_del_object(v___x_3542_);
goto v___jp_3577_;
}
else
{
uint8_t v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3590_; 
lean_del_object(v___x_3575_);
v___x_3586_ = 0;
v___x_3587_ = l_Std_Http_Headers_empty;
v___x_3588_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3588_, 0, v_res_3573_);
lean_ctor_set(v___x_3588_, 1, v___x_3587_);
lean_ctor_set_uint8(v___x_3588_, sizeof(void*)*2, v___x_3586_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 1, v___x_3588_);
lean_ctor_set(v___x_3542_, 0, v_pos_3572_);
v___x_3590_ = v___x_3542_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_pos_3572_);
lean_ctor_set(v_reuseFailAlloc_3591_, 1, v___x_3588_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
}
}
else
{
lean_object* v_pos_3600_; lean_object* v_err_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3608_; 
lean_del_object(v___x_3565_);
lean_dec(v_snd_3563_);
lean_dec(v_fst_3562_);
lean_del_object(v___x_3542_);
v_pos_3600_ = lean_ctor_get(v___x_3571_, 0);
v_err_3601_ = lean_ctor_get(v___x_3571_, 1);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3603_ = v___x_3571_;
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_err_3601_);
lean_inc(v_pos_3600_);
lean_dec(v___x_3571_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_pos_3600_);
lean_ctor_set(v_reuseFailAlloc_3607_, 1, v_err_3601_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
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
lean_object* v_pos_3615_; lean_object* v_err_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3623_; 
v_pos_3615_ = lean_ctor_get(v___x_3538_, 0);
v_err_3616_ = lean_ctor_get(v___x_3538_, 1);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3618_ = v___x_3538_;
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_err_3616_);
lean_inc(v_pos_3615_);
lean_dec(v___x_3538_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
if (v_isShared_3619_ == 0)
{
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_pos_3615_);
lean_ctor_set(v_reuseFailAlloc_3622_, 1, v_err_3616_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine___boxed(lean_object* v_limits_3624_, lean_object* v_a_3625_){
_start:
{
lean_object* v_res_3626_; 
v_res_3626_ = l_Std_Http_Protocol_H1_parseStatusLine(v_limits_3624_, v_a_3625_);
lean_dec_ref(v_limits_3624_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion(lean_object* v_limits_3627_, lean_object* v_a_3628_){
_start:
{
lean_object* v___x_3629_; 
v___x_3629_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_3628_);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_object* v_pos_3630_; lean_object* v_res_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3694_; 
v_pos_3630_ = lean_ctor_get(v___x_3629_, 0);
v_res_3631_ = lean_ctor_get(v___x_3629_, 1);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3633_ = v___x_3629_;
v_isShared_3634_ = v_isSharedCheck_3694_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_res_3631_);
lean_inc(v_pos_3630_);
lean_dec(v___x_3629_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3694_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v_array_3635_; lean_object* v_idx_3636_; lean_object* v___x_3637_; uint8_t v___x_3638_; 
v_array_3635_ = lean_ctor_get(v_pos_3630_, 0);
v_idx_3636_ = lean_ctor_get(v_pos_3630_, 1);
v___x_3637_ = lean_byte_array_size(v_array_3635_);
v___x_3638_ = lean_nat_dec_lt(v_idx_3636_, v___x_3637_);
if (v___x_3638_ == 0)
{
lean_object* v___x_3639_; lean_object* v___x_3641_; 
lean_dec(v_res_3631_);
v___x_3639_ = lean_box(0);
if (v_isShared_3634_ == 0)
{
lean_ctor_set_tag(v___x_3633_, 1);
lean_ctor_set(v___x_3633_, 1, v___x_3639_);
v___x_3641_ = v___x_3633_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_pos_3630_);
lean_ctor_set(v_reuseFailAlloc_3642_, 1, v___x_3639_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
else
{
uint8_t v___x_3643_; uint8_t v_got_3644_; uint8_t v___x_3645_; 
v___x_3643_ = 32;
v_got_3644_ = lean_byte_array_fget(v_array_3635_, v_idx_3636_);
v___x_3645_ = lean_uint8_dec_eq(v_got_3644_, v___x_3643_);
if (v___x_3645_ == 0)
{
lean_object* v___x_3646_; lean_object* v___x_3648_; 
lean_dec(v_res_3631_);
v___x_3646_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_3634_ == 0)
{
lean_ctor_set_tag(v___x_3633_, 1);
lean_ctor_set(v___x_3633_, 1, v___x_3646_);
v___x_3648_ = v___x_3633_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_pos_3630_);
lean_ctor_set(v_reuseFailAlloc_3649_, 1, v___x_3646_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
else
{
lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3691_; 
lean_inc(v_idx_3636_);
lean_inc_ref(v_array_3635_);
lean_del_object(v___x_3633_);
v_isSharedCheck_3691_ = !lean_is_exclusive(v_pos_3630_);
if (v_isSharedCheck_3691_ == 0)
{
lean_object* v_unused_3692_; lean_object* v_unused_3693_; 
v_unused_3692_ = lean_ctor_get(v_pos_3630_, 1);
lean_dec(v_unused_3692_);
v_unused_3693_ = lean_ctor_get(v_pos_3630_, 0);
lean_dec(v_unused_3693_);
v___x_3651_ = v_pos_3630_;
v_isShared_3652_ = v_isSharedCheck_3691_;
goto v_resetjp_3650_;
}
else
{
lean_dec(v_pos_3630_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3691_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v_fst_3653_; lean_object* v_snd_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3690_; 
v_fst_3653_ = lean_ctor_get(v_res_3631_, 0);
v_snd_3654_ = lean_ctor_get(v_res_3631_, 1);
v_isSharedCheck_3690_ = !lean_is_exclusive(v_res_3631_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3656_ = v_res_3631_;
v_isShared_3657_ = v_isSharedCheck_3690_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_snd_3654_);
lean_inc(v_fst_3653_);
lean_dec(v_res_3631_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3690_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3661_; 
v___x_3658_ = lean_unsigned_to_nat(1u);
v___x_3659_ = lean_nat_add(v_idx_3636_, v___x_3658_);
lean_dec(v_idx_3636_);
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 1, v___x_3659_);
v___x_3661_ = v___x_3651_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_array_3635_);
lean_ctor_set(v_reuseFailAlloc_3689_, 1, v___x_3659_);
v___x_3661_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
lean_object* v___x_3662_; 
v___x_3662_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_3627_, v___x_3661_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v_pos_3663_; lean_object* v_res_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3679_; 
v_pos_3663_ = lean_ctor_get(v___x_3662_, 0);
v_res_3664_ = lean_ctor_get(v___x_3662_, 1);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3666_ = v___x_3662_;
v_isShared_3667_ = v_isSharedCheck_3679_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_res_3664_);
lean_inc(v_pos_3663_);
lean_dec(v___x_3662_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3679_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___y_3669_; uint8_t v___x_3677_; 
v___x_3677_ = lean_nat_dec_eq(v_fst_3653_, v___x_3658_);
if (v___x_3677_ == 0)
{
v___y_3669_ = v_snd_3654_;
goto v___jp_3668_;
}
else
{
uint8_t v___x_3678_; 
v___x_3678_ = lean_nat_dec_le(v_snd_3654_, v___x_3658_);
if (v___x_3678_ == 0)
{
lean_dec(v_snd_3654_);
v___y_3669_ = v___x_3658_;
goto v___jp_3668_;
}
else
{
v___y_3669_ = v_snd_3654_;
goto v___jp_3668_;
}
}
v___jp_3668_:
{
lean_object* v___x_3670_; lean_object* v___x_3672_; 
v___x_3670_ = l_Std_Http_Version_ofNumber_x3f(v_fst_3653_, v___y_3669_);
lean_dec(v___y_3669_);
lean_dec(v_fst_3653_);
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 1, v___x_3670_);
lean_ctor_set(v___x_3656_, 0, v_res_3664_);
v___x_3672_ = v___x_3656_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_res_3664_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v___x_3670_);
v___x_3672_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
lean_object* v___x_3674_; 
if (v_isShared_3667_ == 0)
{
lean_ctor_set(v___x_3666_, 1, v___x_3672_);
v___x_3674_ = v___x_3666_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_pos_3663_);
lean_ctor_set(v_reuseFailAlloc_3675_, 1, v___x_3672_);
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
else
{
lean_object* v_pos_3680_; lean_object* v_err_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_del_object(v___x_3656_);
lean_dec(v_snd_3654_);
lean_dec(v_fst_3653_);
v_pos_3680_ = lean_ctor_get(v___x_3662_, 0);
v_err_3681_ = lean_ctor_get(v___x_3662_, 1);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3662_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_err_3681_);
lean_inc(v_pos_3680_);
lean_dec(v___x_3662_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_pos_3680_);
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
}
}
}
}
}
else
{
lean_object* v_pos_3695_; lean_object* v_err_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
v_pos_3695_ = lean_ctor_get(v___x_3629_, 0);
v_err_3696_ = lean_ctor_get(v___x_3629_, 1);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3629_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_err_3696_);
lean_inc(v_pos_3695_);
lean_dec(v___x_3629_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_pos_3695_);
lean_ctor_set(v_reuseFailAlloc_3702_, 1, v_err_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion___boxed(lean_object* v_limits_3704_, lean_object* v_a_3705_){
_start:
{
lean_object* v_res_3706_; 
v_res_3706_ = l_Std_Http_Protocol_H1_parseStatusLineRawVersion(v_limits_3704_, v_a_3705_);
lean_dec_ref(v_limits_3704_);
return v_res_3706_;
}
}
lean_object* runtime_initialize_Std_Internal_Parsec(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec_ByteArray(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Config(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lossy(uint8_t builtin);
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
res = runtime_initialize_Init_Data_String_Lossy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods = _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods();
lean_mark_persistent(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods);
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
lean_object* initialize_Init_Data_String_Lossy(uint8_t builtin);
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
res = initialize_Init_Data_String_Lossy(builtin);
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
