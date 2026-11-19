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
lean_object* l_String_toListImpl(lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
lean_object* l_Std_Http_Status_ofCode(lean_object*, uint16_t);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_toByteSlice(lean_object*, lean_object*, lean_object*);
lean_object* l_ByteSlice_toByteArray(lean_object*);
lean_object* l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Headers_empty;
uint8_t lean_uint8_sub(uint8_t, uint8_t);
uint8_t lean_uint8_add(uint8_t, uint8_t);
lean_object* l_Char_quote(uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
extern lean_object* l_ByteArray_empty;
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
extern lean_object* l_Std_Http_Method_all;
size_t lean_array_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_ByteArray_Iterator_remainingBytes(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_byteslice_beq(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "invalid extension value"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '61'"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid extension name"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '59'"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7_value;
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
v_maxLeadingEmptyLines_363_ = lean_ctor_get(v_limits_351_, 9);
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
v_maxSpaceSequence_464_ = lean_ctor_get(v_limits_454_, 8);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(lean_object* v_a_966_){
_start:
{
lean_object* v___f_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v_snd_971_; lean_object* v_fst_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_1093_; 
v___f_967_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_968_ = lean_unsigned_to_nat(64u);
v___x_969_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_966_);
v___x_970_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_967_, v___x_968_, v___x_969_, v_a_966_);
v_snd_971_ = lean_ctor_get(v___x_970_, 1);
v_fst_972_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_974_ = v___x_970_;
v_isShared_975_ = v_isSharedCheck_1093_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_snd_971_);
lean_inc(v_fst_972_);
lean_dec(v___x_970_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_1093_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v_fst_976_; lean_object* v_snd_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1092_; 
v_fst_976_ = lean_ctor_get(v_snd_971_, 0);
v_snd_977_ = lean_ctor_get(v_snd_971_, 1);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_snd_971_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_979_ = v_snd_971_;
v_isShared_980_ = v_isSharedCheck_1092_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_snd_977_);
lean_inc(v_fst_976_);
lean_dec(v_snd_971_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1092_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
uint32_t v___y_992_; uint32_t v___y_998_; uint8_t v___x_1050_; 
v___x_1050_ = lean_unbox(v_snd_977_);
lean_dec(v_snd_977_);
if (v___x_1050_ == 0)
{
uint8_t v___x_1051_; 
v___x_1051_ = lean_nat_dec_eq(v_fst_972_, v___x_969_);
if (v___x_1051_ == 0)
{
lean_object* v_array_1052_; lean_object* v_idx_1053_; lean_object* v_lower_1055_; lean_object* v_upper_1056_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___y_1085_; uint8_t v___x_1087_; 
v_array_1052_ = lean_ctor_get(v_a_966_, 0);
lean_inc_ref(v_array_1052_);
v_idx_1053_ = lean_ctor_get(v_a_966_, 1);
lean_inc(v_idx_1053_);
lean_dec_ref(v_a_966_);
v___x_1082_ = lean_nat_add(v_idx_1053_, v_fst_972_);
lean_dec(v_fst_972_);
v___x_1083_ = lean_byte_array_size(v_array_1052_);
v___x_1087_ = lean_nat_dec_le(v_idx_1053_, v___x_969_);
if (v___x_1087_ == 0)
{
v___y_1085_ = v_idx_1053_;
goto v___jp_1084_;
}
else
{
lean_dec(v_idx_1053_);
v___y_1085_ = v___x_969_;
goto v___jp_1084_;
}
v___jp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; size_t v_sz_1060_; size_t v___x_1061_; lean_object* v___x_1062_; lean_object* v_fst_1063_; 
v___x_1057_ = l_ByteArray_toByteSlice(v_array_1052_, v_lower_1055_, v_upper_1056_);
v___x_1058_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods;
v___x_1059_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___closed__0));
v_sz_1060_ = lean_usize_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4);
v___x_1061_ = ((size_t)0ULL);
v___x_1062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0(v___x_1057_, v___x_1058_, v_sz_1060_, v___x_1061_, v___x_1059_);
lean_dec_ref(v___x_1057_);
v_fst_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_fst_1063_);
lean_dec_ref(v___x_1062_);
if (lean_obj_tag(v_fst_1063_) == 0)
{
goto v___jp_1003_;
}
else
{
lean_object* v_val_1064_; 
v_val_1064_ = lean_ctor_get(v_fst_1063_, 0);
lean_inc(v_val_1064_);
lean_dec_ref_known(v_fst_1063_, 1);
if (lean_obj_tag(v_val_1064_) == 0)
{
goto v___jp_1003_;
}
else
{
lean_object* v_val_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1081_; 
lean_del_object(v___x_979_);
lean_del_object(v___x_974_);
v_val_1065_ = lean_ctor_get(v_val_1064_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_val_1064_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1067_ = v_val_1064_;
v_isShared_1068_ = v_isSharedCheck_1081_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_val_1065_);
lean_dec(v_val_1064_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1081_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v_snd_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1079_; 
v_snd_1069_ = lean_ctor_get(v_val_1065_, 1);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_val_1065_);
if (v_isSharedCheck_1079_ == 0)
{
lean_object* v_unused_1080_; 
v_unused_1080_ = lean_ctor_get(v_val_1065_, 0);
lean_dec(v_unused_1080_);
v___x_1071_ = v_val_1065_;
v_isShared_1072_ = v_isSharedCheck_1079_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_snd_1069_);
lean_dec(v_val_1065_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1079_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v_snd_1069_);
v___x_1074_ = v___x_1067_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_snd_1069_);
v___x_1074_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1076_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 1, v___x_1074_);
lean_ctor_set(v___x_1071_, 0, v_fst_976_);
v___x_1076_ = v___x_1071_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_fst_976_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
}
}
}
v___jp_1084_:
{
uint8_t v___x_1086_; 
v___x_1086_ = lean_nat_dec_le(v___x_1082_, v___x_1083_);
if (v___x_1086_ == 0)
{
lean_dec(v___x_1082_);
v_lower_1055_ = v___y_1085_;
v_upper_1056_ = v___x_1083_;
goto v___jp_1054_;
}
else
{
v_lower_1055_ = v___y_1085_;
v_upper_1056_ = v___x_1082_;
goto v___jp_1054_;
}
}
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_del_object(v___x_979_);
lean_dec(v_fst_976_);
lean_del_object(v___x_974_);
lean_dec(v_fst_972_);
v___x_1088_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
v___x_1089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1089_, 0, v_a_966_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
return v___x_1089_;
}
}
else
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_del_object(v___x_979_);
lean_del_object(v___x_974_);
lean_dec(v_fst_972_);
lean_dec_ref(v_a_966_);
v___x_1090_ = lean_box(0);
v___x_1091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1091_, 0, v_fst_976_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
return v___x_1091_;
}
v___jp_981_:
{
lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_982_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__1));
if (v_isShared_980_ == 0)
{
lean_ctor_set_tag(v___x_979_, 1);
lean_ctor_set(v___x_979_, 1, v___x_982_);
v___x_984_ = v___x_979_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_fst_976_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v___x_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
v___jp_986_:
{
lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_987_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3));
if (v_isShared_975_ == 0)
{
lean_ctor_set_tag(v___x_974_, 1);
lean_ctor_set(v___x_974_, 1, v___x_987_);
lean_ctor_set(v___x_974_, 0, v_fst_976_);
v___x_989_ = v___x_974_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_fst_976_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v___x_987_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
v___jp_991_:
{
uint32_t v___x_993_; uint8_t v___x_994_; 
v___x_993_ = 97;
v___x_994_ = lean_uint32_dec_le(v___x_993_, v___y_992_);
if (v___x_994_ == 0)
{
lean_del_object(v___x_974_);
goto v___jp_981_;
}
else
{
uint32_t v___x_995_; uint8_t v___x_996_; 
v___x_995_ = 122;
v___x_996_ = lean_uint32_dec_le(v___y_992_, v___x_995_);
if (v___x_996_ == 0)
{
lean_del_object(v___x_974_);
goto v___jp_981_;
}
else
{
lean_del_object(v___x_979_);
goto v___jp_986_;
}
}
}
v___jp_997_:
{
uint32_t v___x_999_; uint8_t v___x_1000_; 
v___x_999_ = 65;
v___x_1000_ = lean_uint32_dec_le(v___x_999_, v___y_998_);
if (v___x_1000_ == 0)
{
v___y_992_ = v___y_998_;
goto v___jp_991_;
}
else
{
uint32_t v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = 90;
v___x_1002_ = lean_uint32_dec_le(v___y_998_, v___x_1001_);
if (v___x_1002_ == 0)
{
v___y_992_ = v___y_998_;
goto v___jp_991_;
}
else
{
lean_del_object(v___x_979_);
goto v___jp_986_;
}
}
}
v___jp_1003_:
{
lean_object* v_array_1004_; lean_object* v_idx_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v_array_1004_ = lean_ctor_get(v_fst_976_, 0);
v_idx_1005_ = lean_ctor_get(v_fst_976_, 1);
v___x_1006_ = lean_byte_array_size(v_array_1004_);
v___x_1007_ = lean_nat_dec_lt(v_idx_1005_, v___x_1006_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_del_object(v___x_979_);
lean_del_object(v___x_974_);
v___x_1008_ = lean_box(0);
v___x_1009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1009_, 0, v_fst_976_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
return v___x_1009_;
}
else
{
uint8_t v___x_1010_; uint8_t v___x_1011_; uint8_t v___x_1012_; 
v___x_1010_ = lean_byte_array_fget(v_array_1004_, v_idx_1005_);
v___x_1011_ = 32;
v___x_1012_ = lean_uint8_dec_eq(v___x_1010_, v___x_1011_);
if (v___x_1012_ == 0)
{
uint32_t v___x_1013_; uint32_t v___x_1014_; uint8_t v___x_1015_; 
v___x_1013_ = lean_uint8_to_uint32(v___x_1010_);
v___x_1014_ = 33;
v___x_1015_ = lean_uint32_dec_eq(v___x_1013_, v___x_1014_);
if (v___x_1015_ == 0)
{
uint32_t v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = 35;
v___x_1017_ = lean_uint32_dec_eq(v___x_1013_, v___x_1016_);
if (v___x_1017_ == 0)
{
uint32_t v___x_1018_; uint8_t v___x_1019_; 
v___x_1018_ = 36;
v___x_1019_ = lean_uint32_dec_eq(v___x_1013_, v___x_1018_);
if (v___x_1019_ == 0)
{
uint32_t v___x_1020_; uint8_t v___x_1021_; 
v___x_1020_ = 37;
v___x_1021_ = lean_uint32_dec_eq(v___x_1013_, v___x_1020_);
if (v___x_1021_ == 0)
{
uint32_t v___x_1022_; uint8_t v___x_1023_; 
v___x_1022_ = 38;
v___x_1023_ = lean_uint32_dec_eq(v___x_1013_, v___x_1022_);
if (v___x_1023_ == 0)
{
uint32_t v___x_1024_; uint8_t v___x_1025_; 
v___x_1024_ = 39;
v___x_1025_ = lean_uint32_dec_eq(v___x_1013_, v___x_1024_);
if (v___x_1025_ == 0)
{
uint32_t v___x_1026_; uint8_t v___x_1027_; 
v___x_1026_ = 42;
v___x_1027_ = lean_uint32_dec_eq(v___x_1013_, v___x_1026_);
if (v___x_1027_ == 0)
{
uint32_t v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = 43;
v___x_1029_ = lean_uint32_dec_eq(v___x_1013_, v___x_1028_);
if (v___x_1029_ == 0)
{
uint32_t v___x_1030_; uint8_t v___x_1031_; 
v___x_1030_ = 45;
v___x_1031_ = lean_uint32_dec_eq(v___x_1013_, v___x_1030_);
if (v___x_1031_ == 0)
{
uint32_t v___x_1032_; uint8_t v___x_1033_; 
v___x_1032_ = 46;
v___x_1033_ = lean_uint32_dec_eq(v___x_1013_, v___x_1032_);
if (v___x_1033_ == 0)
{
uint32_t v___x_1034_; uint8_t v___x_1035_; 
v___x_1034_ = 94;
v___x_1035_ = lean_uint32_dec_eq(v___x_1013_, v___x_1034_);
if (v___x_1035_ == 0)
{
uint32_t v___x_1036_; uint8_t v___x_1037_; 
v___x_1036_ = 95;
v___x_1037_ = lean_uint32_dec_eq(v___x_1013_, v___x_1036_);
if (v___x_1037_ == 0)
{
uint32_t v___x_1038_; uint8_t v___x_1039_; 
v___x_1038_ = 96;
v___x_1039_ = lean_uint32_dec_eq(v___x_1013_, v___x_1038_);
if (v___x_1039_ == 0)
{
uint32_t v___x_1040_; uint8_t v___x_1041_; 
v___x_1040_ = 124;
v___x_1041_ = lean_uint32_dec_eq(v___x_1013_, v___x_1040_);
if (v___x_1041_ == 0)
{
uint32_t v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = 126;
v___x_1043_ = lean_uint32_dec_eq(v___x_1013_, v___x_1042_);
if (v___x_1043_ == 0)
{
uint32_t v___x_1044_; uint8_t v___x_1045_; 
v___x_1044_ = 48;
v___x_1045_ = lean_uint32_dec_le(v___x_1044_, v___x_1013_);
if (v___x_1045_ == 0)
{
v___y_998_ = v___x_1013_;
goto v___jp_997_;
}
else
{
uint32_t v___x_1046_; uint8_t v___x_1047_; 
v___x_1046_ = 57;
v___x_1047_ = lean_uint32_dec_le(v___x_1013_, v___x_1046_);
if (v___x_1047_ == 0)
{
v___y_998_ = v___x_1013_;
goto v___jp_997_;
}
else
{
lean_del_object(v___x_979_);
goto v___jp_986_;
}
}
}
else
{
lean_del_object(v___x_979_);
goto v___jp_986_;
}
}
else
{
lean_del_object(v___x_979_);
goto v___jp_986_;
}
}
else
{
lean_del_object(v___x_979_);
goto v___jp_986_;
}
}
else
{
lean_del_object(v___x_979_);
goto v___jp_986_;
}
}
else
{
lean_del_object(v___x_979_);
goto v___jp_986_;
}
}
else
{
lean_del_object(v___x_979_);
goto v___jp_986_;
}
}
else
{
lean_del_object(v___x_979_);
goto v___jp_986_;
}
}
else
{
lean_del_object(v___x_979_);
goto v___jp_986_;
}
}
else
{
lean_del_object(v___x_979_);
goto v___jp_986_;
}
}
else
{
lean_del_object(v___x_979_);
goto v___jp_986_;
}
}
else
{
lean_del_object(v___x_979_);
goto v___jp_986_;
}
}
else
{
lean_del_object(v___x_979_);
goto v___jp_986_;
}
}
else
{
lean_del_object(v___x_979_);
goto v___jp_986_;
}
}
else
{
lean_del_object(v___x_979_);
goto v___jp_986_;
}
}
else
{
lean_del_object(v___x_979_);
goto v___jp_986_;
}
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_del_object(v___x_979_);
lean_del_object(v___x_974_);
v___x_1048_ = lean_box(0);
v___x_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1049_, 0, v_fst_976_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
return v___x_1049_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(uint8_t v___y_1094_){
_start:
{
uint8_t v___x_1150_; uint8_t v___x_1151_; 
v___x_1150_ = 48;
v___x_1151_ = lean_uint8_dec_le(v___x_1150_, v___y_1094_);
if (v___x_1151_ == 0)
{
goto v___jp_1145_;
}
else
{
uint8_t v___x_1152_; uint8_t v___x_1153_; 
v___x_1152_ = 57;
v___x_1153_ = lean_uint8_dec_le(v___y_1094_, v___x_1152_);
if (v___x_1153_ == 0)
{
goto v___jp_1145_;
}
else
{
return v___x_1153_;
}
}
v___jp_1095_:
{
uint8_t v___x_1096_; uint8_t v___x_1097_; 
v___x_1096_ = 45;
v___x_1097_ = lean_uint8_dec_eq(v___y_1094_, v___x_1096_);
if (v___x_1097_ == 0)
{
uint8_t v___x_1098_; uint8_t v___x_1099_; 
v___x_1098_ = 46;
v___x_1099_ = lean_uint8_dec_eq(v___y_1094_, v___x_1098_);
if (v___x_1099_ == 0)
{
uint8_t v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = 95;
v___x_1101_ = lean_uint8_dec_eq(v___y_1094_, v___x_1100_);
if (v___x_1101_ == 0)
{
uint8_t v___x_1102_; uint8_t v___x_1103_; 
v___x_1102_ = 126;
v___x_1103_ = lean_uint8_dec_eq(v___y_1094_, v___x_1102_);
if (v___x_1103_ == 0)
{
uint8_t v___x_1104_; uint8_t v___x_1105_; 
v___x_1104_ = 33;
v___x_1105_ = lean_uint8_dec_eq(v___y_1094_, v___x_1104_);
if (v___x_1105_ == 0)
{
uint8_t v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = 36;
v___x_1107_ = lean_uint8_dec_eq(v___y_1094_, v___x_1106_);
if (v___x_1107_ == 0)
{
uint8_t v___x_1108_; uint8_t v___x_1109_; 
v___x_1108_ = 38;
v___x_1109_ = lean_uint8_dec_eq(v___y_1094_, v___x_1108_);
if (v___x_1109_ == 0)
{
uint8_t v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = 39;
v___x_1111_ = lean_uint8_dec_eq(v___y_1094_, v___x_1110_);
if (v___x_1111_ == 0)
{
uint8_t v___x_1112_; uint8_t v___x_1113_; 
v___x_1112_ = 40;
v___x_1113_ = lean_uint8_dec_eq(v___y_1094_, v___x_1112_);
if (v___x_1113_ == 0)
{
uint8_t v___x_1114_; uint8_t v___x_1115_; 
v___x_1114_ = 41;
v___x_1115_ = lean_uint8_dec_eq(v___y_1094_, v___x_1114_);
if (v___x_1115_ == 0)
{
uint8_t v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = 42;
v___x_1117_ = lean_uint8_dec_eq(v___y_1094_, v___x_1116_);
if (v___x_1117_ == 0)
{
uint8_t v___x_1118_; uint8_t v___x_1119_; 
v___x_1118_ = 43;
v___x_1119_ = lean_uint8_dec_eq(v___y_1094_, v___x_1118_);
if (v___x_1119_ == 0)
{
uint8_t v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = 44;
v___x_1121_ = lean_uint8_dec_eq(v___y_1094_, v___x_1120_);
if (v___x_1121_ == 0)
{
uint8_t v___x_1122_; uint8_t v___x_1123_; 
v___x_1122_ = 59;
v___x_1123_ = lean_uint8_dec_eq(v___y_1094_, v___x_1122_);
if (v___x_1123_ == 0)
{
uint8_t v___x_1124_; uint8_t v___x_1125_; 
v___x_1124_ = 61;
v___x_1125_ = lean_uint8_dec_eq(v___y_1094_, v___x_1124_);
if (v___x_1125_ == 0)
{
uint8_t v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = 58;
v___x_1127_ = lean_uint8_dec_eq(v___y_1094_, v___x_1126_);
if (v___x_1127_ == 0)
{
uint8_t v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = 64;
v___x_1129_ = lean_uint8_dec_eq(v___y_1094_, v___x_1128_);
if (v___x_1129_ == 0)
{
uint8_t v___x_1130_; uint8_t v___x_1131_; 
v___x_1130_ = 47;
v___x_1131_ = lean_uint8_dec_eq(v___y_1094_, v___x_1130_);
if (v___x_1131_ == 0)
{
uint8_t v___x_1132_; uint8_t v___x_1133_; 
v___x_1132_ = 63;
v___x_1133_ = lean_uint8_dec_eq(v___y_1094_, v___x_1132_);
if (v___x_1133_ == 0)
{
uint8_t v___x_1134_; uint8_t v___x_1135_; 
v___x_1134_ = 37;
v___x_1135_ = lean_uint8_dec_eq(v___y_1094_, v___x_1134_);
if (v___x_1135_ == 0)
{
uint8_t v___x_1136_; uint8_t v___x_1137_; 
v___x_1136_ = 91;
v___x_1137_ = lean_uint8_dec_eq(v___y_1094_, v___x_1136_);
if (v___x_1137_ == 0)
{
uint8_t v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = 93;
v___x_1139_ = lean_uint8_dec_eq(v___y_1094_, v___x_1138_);
return v___x_1139_;
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
else
{
return v___x_1113_;
}
}
else
{
return v___x_1111_;
}
}
else
{
return v___x_1109_;
}
}
else
{
return v___x_1107_;
}
}
else
{
return v___x_1105_;
}
}
else
{
return v___x_1103_;
}
}
else
{
return v___x_1101_;
}
}
else
{
return v___x_1099_;
}
}
else
{
return v___x_1097_;
}
}
v___jp_1140_:
{
uint8_t v___x_1141_; uint8_t v___x_1142_; 
v___x_1141_ = 65;
v___x_1142_ = lean_uint8_dec_le(v___x_1141_, v___y_1094_);
if (v___x_1142_ == 0)
{
goto v___jp_1095_;
}
else
{
uint8_t v___x_1143_; uint8_t v___x_1144_; 
v___x_1143_ = 90;
v___x_1144_ = lean_uint8_dec_le(v___y_1094_, v___x_1143_);
if (v___x_1144_ == 0)
{
goto v___jp_1095_;
}
else
{
return v___x_1144_;
}
}
}
v___jp_1145_:
{
uint8_t v___x_1146_; uint8_t v___x_1147_; 
v___x_1146_ = 97;
v___x_1147_ = lean_uint8_dec_le(v___x_1146_, v___y_1094_);
if (v___x_1147_ == 0)
{
goto v___jp_1140_;
}
else
{
uint8_t v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = 122;
v___x_1149_ = lean_uint8_dec_le(v___y_1094_, v___x_1148_);
if (v___x_1149_ == 0)
{
goto v___jp_1140_;
}
else
{
return v___x_1149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0___boxed(lean_object* v___y_1154_){
_start:
{
uint8_t v___y_1870__boxed_1155_; uint8_t v_res_1156_; lean_object* v_r_1157_; 
v___y_1870__boxed_1155_ = lean_unbox(v___y_1154_);
v_res_1156_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(v___y_1870__boxed_1155_);
v_r_1157_ = lean_box(v_res_1156_);
return v_r_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(lean_object* v_limits_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v_pos_1165_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v_maxUriLength_1173_; lean_object* v___f_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v_snd_1177_; lean_object* v_fst_1178_; lean_object* v_fst_1179_; lean_object* v_snd_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1273_; 
v_maxUriLength_1173_ = lean_ctor_get(v_limits_1162_, 4);
v___f_1174_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__2));
v___x_1175_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1163_);
v___x_1176_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1174_, v_maxUriLength_1173_, v___x_1175_, v_a_1163_);
v_snd_1177_ = lean_ctor_get(v___x_1176_, 1);
lean_inc(v_snd_1177_);
v_fst_1178_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_fst_1178_);
lean_dec_ref(v___x_1176_);
v_fst_1179_ = lean_ctor_get(v_snd_1177_, 0);
v_snd_1180_ = lean_ctor_get(v_snd_1177_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_snd_1177_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1182_ = v_snd_1177_;
v_isShared_1183_ = v_isSharedCheck_1273_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_snd_1180_);
lean_inc(v_fst_1179_);
lean_dec(v_snd_1177_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1273_;
goto v_resetjp_1181_;
}
v___jp_1164_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__1));
v___x_1167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1167_, 0, v_pos_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
return v___x_1167_;
}
v___jp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = l_ByteSlice_toByteArray(v___y_1169_);
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___y_1170_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
return v___x_1172_;
}
v_resetjp_1181_:
{
lean_object* v___y_1185_; uint8_t v___y_1186_; lean_object* v___y_1232_; uint8_t v___y_1233_; lean_object* v___y_1239_; uint8_t v___y_1240_; uint8_t v___x_1245_; 
v___x_1245_ = lean_unbox(v_snd_1180_);
lean_dec(v_snd_1180_);
if (v___x_1245_ == 0)
{
lean_object* v_array_1246_; lean_object* v_idx_1247_; lean_object* v_lower_1249_; lean_object* v_upper_1250_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___y_1266_; uint8_t v___x_1268_; 
lean_del_object(v___x_1182_);
v_array_1246_ = lean_ctor_get(v_a_1163_, 0);
lean_inc_ref(v_array_1246_);
v_idx_1247_ = lean_ctor_get(v_a_1163_, 1);
lean_inc(v_idx_1247_);
lean_dec_ref(v_a_1163_);
v___x_1263_ = lean_nat_add(v_idx_1247_, v_fst_1178_);
lean_dec(v_fst_1178_);
v___x_1264_ = lean_byte_array_size(v_array_1246_);
v___x_1268_ = lean_nat_dec_le(v_idx_1247_, v___x_1175_);
if (v___x_1268_ == 0)
{
v___y_1266_ = v_idx_1247_;
goto v___jp_1265_;
}
else
{
lean_dec(v_idx_1247_);
v___y_1266_ = v___x_1175_;
goto v___jp_1265_;
}
v___jp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1251_ = l_ByteArray_toByteSlice(v_array_1246_, v_lower_1249_, v_upper_1250_);
v___x_1252_ = l_ByteSlice_size(v___x_1251_);
v___x_1253_ = lean_nat_dec_eq(v___x_1252_, v_maxUriLength_1173_);
lean_dec(v___x_1252_);
if (v___x_1253_ == 0)
{
v___y_1169_ = v___x_1251_;
v___y_1170_ = v_fst_1179_;
goto v___jp_1168_;
}
else
{
lean_object* v_array_1254_; lean_object* v_idx_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; 
v_array_1254_ = lean_ctor_get(v_fst_1179_, 0);
v_idx_1255_ = lean_ctor_get(v_fst_1179_, 1);
v___x_1256_ = lean_byte_array_size(v_array_1254_);
v___x_1257_ = lean_nat_dec_lt(v_idx_1255_, v___x_1256_);
if (v___x_1257_ == 0)
{
v___y_1169_ = v___x_1251_;
v___y_1170_ = v_fst_1179_;
goto v___jp_1168_;
}
else
{
uint8_t v___x_1258_; uint8_t v___x_1259_; uint8_t v___x_1260_; 
v___x_1258_ = lean_byte_array_fget(v_array_1254_, v_idx_1255_);
v___x_1259_ = 48;
v___x_1260_ = lean_uint8_dec_le(v___x_1259_, v___x_1258_);
if (v___x_1260_ == 0)
{
v___y_1239_ = v___x_1251_;
v___y_1240_ = v___x_1258_;
goto v___jp_1238_;
}
else
{
uint8_t v___x_1261_; uint8_t v___x_1262_; 
v___x_1261_ = 57;
v___x_1262_ = lean_uint8_dec_le(v___x_1258_, v___x_1261_);
if (v___x_1262_ == 0)
{
v___y_1239_ = v___x_1251_;
v___y_1240_ = v___x_1258_;
goto v___jp_1238_;
}
else
{
lean_dec_ref(v___x_1251_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
}
}
}
v___jp_1265_:
{
uint8_t v___x_1267_; 
v___x_1267_ = lean_nat_dec_le(v___x_1263_, v___x_1264_);
if (v___x_1267_ == 0)
{
lean_dec(v___x_1263_);
v_lower_1249_ = v___y_1266_;
v_upper_1250_ = v___x_1264_;
goto v___jp_1248_;
}
else
{
v_lower_1249_ = v___y_1266_;
v_upper_1250_ = v___x_1263_;
goto v___jp_1248_;
}
}
}
else
{
lean_object* v___x_1269_; lean_object* v___x_1271_; 
lean_dec(v_fst_1178_);
lean_dec_ref(v_a_1163_);
v___x_1269_ = lean_box(0);
if (v_isShared_1183_ == 0)
{
lean_ctor_set_tag(v___x_1182_, 1);
lean_ctor_set(v___x_1182_, 1, v___x_1269_);
v___x_1271_ = v___x_1182_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_fst_1179_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
v___jp_1184_:
{
uint8_t v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = 45;
v___x_1188_ = lean_uint8_dec_eq(v___y_1186_, v___x_1187_);
if (v___x_1188_ == 0)
{
uint8_t v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = 46;
v___x_1190_ = lean_uint8_dec_eq(v___y_1186_, v___x_1189_);
if (v___x_1190_ == 0)
{
uint8_t v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = 95;
v___x_1192_ = lean_uint8_dec_eq(v___y_1186_, v___x_1191_);
if (v___x_1192_ == 0)
{
uint8_t v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = 126;
v___x_1194_ = lean_uint8_dec_eq(v___y_1186_, v___x_1193_);
if (v___x_1194_ == 0)
{
uint8_t v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = 33;
v___x_1196_ = lean_uint8_dec_eq(v___y_1186_, v___x_1195_);
if (v___x_1196_ == 0)
{
uint8_t v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = 36;
v___x_1198_ = lean_uint8_dec_eq(v___y_1186_, v___x_1197_);
if (v___x_1198_ == 0)
{
uint8_t v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = 38;
v___x_1200_ = lean_uint8_dec_eq(v___y_1186_, v___x_1199_);
if (v___x_1200_ == 0)
{
uint8_t v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = 39;
v___x_1202_ = lean_uint8_dec_eq(v___y_1186_, v___x_1201_);
if (v___x_1202_ == 0)
{
uint8_t v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = 40;
v___x_1204_ = lean_uint8_dec_eq(v___y_1186_, v___x_1203_);
if (v___x_1204_ == 0)
{
uint8_t v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = 41;
v___x_1206_ = lean_uint8_dec_eq(v___y_1186_, v___x_1205_);
if (v___x_1206_ == 0)
{
uint8_t v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = 42;
v___x_1208_ = lean_uint8_dec_eq(v___y_1186_, v___x_1207_);
if (v___x_1208_ == 0)
{
uint8_t v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = 43;
v___x_1210_ = lean_uint8_dec_eq(v___y_1186_, v___x_1209_);
if (v___x_1210_ == 0)
{
uint8_t v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = 44;
v___x_1212_ = lean_uint8_dec_eq(v___y_1186_, v___x_1211_);
if (v___x_1212_ == 0)
{
uint8_t v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = 59;
v___x_1214_ = lean_uint8_dec_eq(v___y_1186_, v___x_1213_);
if (v___x_1214_ == 0)
{
uint8_t v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = 61;
v___x_1216_ = lean_uint8_dec_eq(v___y_1186_, v___x_1215_);
if (v___x_1216_ == 0)
{
uint8_t v___x_1217_; uint8_t v___x_1218_; 
v___x_1217_ = 58;
v___x_1218_ = lean_uint8_dec_eq(v___y_1186_, v___x_1217_);
if (v___x_1218_ == 0)
{
uint8_t v___x_1219_; uint8_t v___x_1220_; 
v___x_1219_ = 64;
v___x_1220_ = lean_uint8_dec_eq(v___y_1186_, v___x_1219_);
if (v___x_1220_ == 0)
{
uint8_t v___x_1221_; uint8_t v___x_1222_; 
v___x_1221_ = 47;
v___x_1222_ = lean_uint8_dec_eq(v___y_1186_, v___x_1221_);
if (v___x_1222_ == 0)
{
uint8_t v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = 63;
v___x_1224_ = lean_uint8_dec_eq(v___y_1186_, v___x_1223_);
if (v___x_1224_ == 0)
{
uint8_t v___x_1225_; uint8_t v___x_1226_; 
v___x_1225_ = 37;
v___x_1226_ = lean_uint8_dec_eq(v___y_1186_, v___x_1225_);
if (v___x_1226_ == 0)
{
uint8_t v___x_1227_; uint8_t v___x_1228_; 
v___x_1227_ = 91;
v___x_1228_ = lean_uint8_dec_eq(v___y_1186_, v___x_1227_);
if (v___x_1228_ == 0)
{
uint8_t v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = 93;
v___x_1230_ = lean_uint8_dec_eq(v___y_1186_, v___x_1229_);
if (v___x_1230_ == 0)
{
v___y_1169_ = v___y_1185_;
v___y_1170_ = v_fst_1179_;
goto v___jp_1168_;
}
else
{
lean_dec_ref(v___y_1185_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
else
{
lean_dec_ref(v___y_1185_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
else
{
lean_dec_ref(v___y_1185_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
else
{
lean_dec_ref(v___y_1185_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
else
{
lean_dec_ref(v___y_1185_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
else
{
lean_dec_ref(v___y_1185_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
else
{
lean_dec_ref(v___y_1185_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
else
{
lean_dec_ref(v___y_1185_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
else
{
lean_dec_ref(v___y_1185_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
else
{
lean_dec_ref(v___y_1185_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
else
{
lean_dec_ref(v___y_1185_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
else
{
lean_dec_ref(v___y_1185_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
else
{
lean_dec_ref(v___y_1185_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
else
{
lean_dec_ref(v___y_1185_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
else
{
lean_dec_ref(v___y_1185_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
else
{
lean_dec_ref(v___y_1185_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
else
{
lean_dec_ref(v___y_1185_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
else
{
lean_dec_ref(v___y_1185_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
else
{
lean_dec_ref(v___y_1185_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
else
{
lean_dec_ref(v___y_1185_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
else
{
lean_dec_ref(v___y_1185_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
else
{
lean_dec_ref(v___y_1185_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
v___jp_1231_:
{
uint8_t v___x_1234_; uint8_t v___x_1235_; 
v___x_1234_ = 65;
v___x_1235_ = lean_uint8_dec_le(v___x_1234_, v___y_1233_);
if (v___x_1235_ == 0)
{
v___y_1185_ = v___y_1232_;
v___y_1186_ = v___y_1233_;
goto v___jp_1184_;
}
else
{
uint8_t v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = 90;
v___x_1237_ = lean_uint8_dec_le(v___y_1233_, v___x_1236_);
if (v___x_1237_ == 0)
{
v___y_1185_ = v___y_1232_;
v___y_1186_ = v___y_1233_;
goto v___jp_1184_;
}
else
{
lean_dec_ref(v___y_1232_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
}
v___jp_1238_:
{
uint8_t v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = 97;
v___x_1242_ = lean_uint8_dec_le(v___x_1241_, v___y_1240_);
if (v___x_1242_ == 0)
{
v___y_1232_ = v___y_1239_;
v___y_1233_ = v___y_1240_;
goto v___jp_1231_;
}
else
{
uint8_t v___x_1243_; uint8_t v___x_1244_; 
v___x_1243_ = 122;
v___x_1244_ = lean_uint8_dec_le(v___y_1240_, v___x_1243_);
if (v___x_1244_ == 0)
{
v___y_1232_ = v___y_1239_;
v___y_1233_ = v___y_1240_;
goto v___jp_1231_;
}
else
{
lean_dec_ref(v___y_1239_);
v_pos_1165_ = v_fst_1179_;
goto v___jp_1164_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___boxed(lean_object* v_limits_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_1274_, v_a_1275_);
lean_dec_ref(v_limits_1274_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_requestTargetConfig(lean_object* v_limits_1277_){
_start:
{
lean_object* v_maxUriLength_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v_maxUriLength_1278_ = lean_ctor_get(v_limits_1277_, 4);
v___x_1279_ = lean_unsigned_to_nat(253u);
lean_inc_n(v_maxUriLength_1278_, 8);
v___x_1280_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1280_, 0, v_maxUriLength_1278_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
lean_ctor_set(v___x_1280_, 2, v_maxUriLength_1278_);
lean_ctor_set(v___x_1280_, 3, v_maxUriLength_1278_);
lean_ctor_set(v___x_1280_, 4, v_maxUriLength_1278_);
lean_ctor_set(v___x_1280_, 5, v_maxUriLength_1278_);
lean_ctor_set(v___x_1280_, 6, v_maxUriLength_1278_);
lean_ctor_set(v___x_1280_, 7, v_maxUriLength_1278_);
lean_ctor_set(v___x_1280_, 8, v_maxUriLength_1278_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_requestTargetConfig___boxed(lean_object* v_limits_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_requestTargetConfig(v_limits_1281_);
lean_dec_ref(v_limits_1281_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0(lean_object* v___x_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_1286_, v___y_1287_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_pos_1289_; lean_object* v_array_1290_; lean_object* v_idx_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v_pos_1289_ = lean_ctor_get(v___x_1288_, 0);
v_array_1290_ = lean_ctor_get(v_pos_1289_, 0);
v_idx_1291_ = lean_ctor_get(v_pos_1289_, 1);
v___x_1292_ = lean_byte_array_size(v_array_1290_);
v___x_1293_ = lean_nat_dec_lt(v_idx_1291_, v___x_1292_);
if (v___x_1293_ == 0)
{
return v___x_1288_;
}
else
{
lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1301_; 
lean_inc(v_pos_1289_);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1301_ == 0)
{
lean_object* v_unused_1302_; lean_object* v_unused_1303_; 
v_unused_1302_ = lean_ctor_get(v___x_1288_, 1);
lean_dec(v_unused_1302_);
v_unused_1303_ = lean_ctor_get(v___x_1288_, 0);
lean_dec(v_unused_1303_);
v___x_1295_ = v___x_1288_;
v_isShared_1296_ = v_isSharedCheck_1301_;
goto v_resetjp_1294_;
}
else
{
lean_dec(v___x_1288_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1301_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1297_; lean_object* v___x_1299_; 
v___x_1297_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__1));
if (v_isShared_1296_ == 0)
{
lean_ctor_set_tag(v___x_1295_, 1);
lean_ctor_set(v___x_1295_, 1, v___x_1297_);
v___x_1299_ = v___x_1295_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_pos_1289_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
else
{
return v___x_1288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(lean_object* v_limits_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_1304_, v_a_1305_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_pos_1307_; lean_object* v_res_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1386_; 
v_pos_1307_ = lean_ctor_get(v___x_1306_, 0);
v_res_1308_ = lean_ctor_get(v___x_1306_, 1);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1310_ = v___x_1306_;
v_isShared_1311_ = v_isSharedCheck_1386_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_res_1308_);
lean_inc(v_pos_1307_);
lean_dec(v___x_1306_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1386_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v_array_1312_; lean_object* v_idx_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v_array_1312_ = lean_ctor_get(v_pos_1307_, 0);
v_idx_1313_ = lean_ctor_get(v_pos_1307_, 1);
v___x_1314_ = lean_byte_array_size(v_array_1312_);
v___x_1315_ = lean_nat_dec_lt(v_idx_1313_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; lean_object* v___x_1318_; 
lean_dec(v_res_1308_);
v___x_1316_ = lean_box(0);
if (v_isShared_1311_ == 0)
{
lean_ctor_set_tag(v___x_1310_, 1);
lean_ctor_set(v___x_1310_, 1, v___x_1316_);
v___x_1318_ = v___x_1310_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_pos_1307_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
else
{
uint8_t v___x_1320_; uint8_t v_got_1321_; uint8_t v___x_1322_; 
v___x_1320_ = 32;
v_got_1321_ = lean_byte_array_fget(v_array_1312_, v_idx_1313_);
v___x_1322_ = lean_uint8_dec_eq(v_got_1321_, v___x_1320_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; lean_object* v___x_1325_; 
lean_dec(v_res_1308_);
v___x_1323_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_1311_ == 0)
{
lean_ctor_set_tag(v___x_1310_, 1);
lean_ctor_set(v___x_1310_, 1, v___x_1323_);
v___x_1325_ = v___x_1310_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_pos_1307_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
else
{
lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1383_; 
lean_inc(v_idx_1313_);
lean_inc_ref(v_array_1312_);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_pos_1307_);
if (v_isSharedCheck_1383_ == 0)
{
lean_object* v_unused_1384_; lean_object* v_unused_1385_; 
v_unused_1384_ = lean_ctor_get(v_pos_1307_, 1);
lean_dec(v_unused_1384_);
v_unused_1385_ = lean_ctor_get(v_pos_1307_, 0);
lean_dec(v_unused_1385_);
v___x_1328_ = v_pos_1307_;
v_isShared_1329_ = v_isSharedCheck_1383_;
goto v_resetjp_1327_;
}
else
{
lean_dec(v_pos_1307_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1383_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1330_ = lean_unsigned_to_nat(1u);
v___x_1331_ = lean_nat_add(v_idx_1313_, v___x_1330_);
lean_dec(v_idx_1313_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 1, v___x_1331_);
v___x_1333_ = v___x_1328_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_array_1312_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1334_; lean_object* v___f_1335_; lean_object* v___x_1336_; 
v___x_1334_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_requestTargetConfig(v_limits_1304_);
v___f_1335_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0), 2, 1);
lean_closure_set(v___f_1335_, 0, v___x_1334_);
v___x_1336_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1335_, v_res_1308_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1347_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1339_ = v___x_1336_;
v_isShared_1340_ = v_isSharedCheck_1347_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1336_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1347_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
lean_ctor_set_tag(v___x_1339_, 1);
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1344_; 
if (v_isShared_1311_ == 0)
{
lean_ctor_set_tag(v___x_1310_, 1);
lean_ctor_set(v___x_1310_, 1, v___x_1342_);
lean_ctor_set(v___x_1310_, 0, v___x_1333_);
v___x_1344_ = v___x_1310_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1333_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1349_; 
lean_del_object(v___x_1310_);
v_a_1348_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1336_, 1);
v___x_1349_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v___x_1333_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_pos_1350_; lean_object* v_res_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v_pos_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_pos_1350_);
v_res_1351_ = lean_ctor_get(v___x_1349_, 1);
lean_inc(v_res_1351_);
lean_dec_ref_known(v___x_1349_, 2);
v___x_1352_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_1353_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_1352_, v_pos_1350_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_pos_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1362_; 
v_pos_1354_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1362_ == 0)
{
lean_object* v_unused_1363_; 
v_unused_1363_ = lean_ctor_get(v___x_1353_, 1);
lean_dec(v_unused_1363_);
v___x_1356_ = v___x_1353_;
v_isShared_1357_ = v_isSharedCheck_1362_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_pos_1354_);
lean_dec(v___x_1353_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1362_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1358_, 0, v_a_1348_);
lean_ctor_set(v___x_1358_, 1, v_res_1351_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 1, v___x_1358_);
v___x_1360_ = v___x_1356_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_pos_1354_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
else
{
lean_object* v_pos_1364_; lean_object* v_err_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec(v_res_1351_);
lean_dec(v_a_1348_);
v_pos_1364_ = lean_ctor_get(v___x_1353_, 0);
v_err_1365_ = lean_ctor_get(v___x_1353_, 1);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1353_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_err_1365_);
lean_inc(v_pos_1364_);
lean_dec(v___x_1353_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_pos_1364_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_err_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
else
{
lean_object* v_pos_1373_; lean_object* v_err_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_dec(v_a_1348_);
v_pos_1373_ = lean_ctor_get(v___x_1349_, 0);
v_err_1374_ = lean_ctor_get(v___x_1349_, 1);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1349_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_err_1374_);
lean_inc(v_pos_1373_);
lean_dec(v___x_1349_);
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
}
}
}
}
}
}
else
{
lean_object* v_pos_1387_; lean_object* v_err_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
v_pos_1387_ = lean_ctor_get(v___x_1306_, 0);
v_err_1388_ = lean_ctor_get(v___x_1306_, 1);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1306_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_err_1388_);
lean_inc(v_pos_1387_);
lean_dec(v___x_1306_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_pos_1387_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_err_1388_);
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
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___boxed(lean_object* v_limits_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_1396_, v_a_1397_);
lean_dec_ref(v_limits_1396_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineParts(lean_object* v_limits_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_1399_, v_a_1400_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_pos_1402_; lean_object* v___x_1403_; 
v_pos_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_pos_1402_);
lean_dec_ref_known(v___x_1401_, 2);
v___x_1403_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(v_pos_1402_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_pos_1404_; lean_object* v_res_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1466_; 
v_pos_1404_ = lean_ctor_get(v___x_1403_, 0);
v_res_1405_ = lean_ctor_get(v___x_1403_, 1);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1407_ = v___x_1403_;
v_isShared_1408_ = v_isSharedCheck_1466_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_res_1405_);
lean_inc(v_pos_1404_);
lean_dec(v___x_1403_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1466_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v_array_1409_; lean_object* v_idx_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v_array_1409_ = lean_ctor_get(v_pos_1404_, 0);
v_idx_1410_ = lean_ctor_get(v_pos_1404_, 1);
v___x_1411_ = lean_byte_array_size(v_array_1409_);
v___x_1412_ = lean_nat_dec_lt(v_idx_1410_, v___x_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; lean_object* v___x_1415_; 
lean_dec(v_res_1405_);
v___x_1413_ = lean_box(0);
if (v_isShared_1408_ == 0)
{
lean_ctor_set_tag(v___x_1407_, 1);
lean_ctor_set(v___x_1407_, 1, v___x_1413_);
v___x_1415_ = v___x_1407_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_pos_1404_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
else
{
uint8_t v___x_1417_; uint8_t v_got_1418_; uint8_t v___x_1419_; 
v___x_1417_ = 32;
v_got_1418_ = lean_byte_array_fget(v_array_1409_, v_idx_1410_);
v___x_1419_ = lean_uint8_dec_eq(v_got_1418_, v___x_1417_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; lean_object* v___x_1422_; 
lean_dec(v_res_1405_);
v___x_1420_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_1408_ == 0)
{
lean_ctor_set_tag(v___x_1407_, 1);
lean_ctor_set(v___x_1407_, 1, v___x_1420_);
v___x_1422_ = v___x_1407_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_pos_1404_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
else
{
lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1463_; 
lean_inc(v_idx_1410_);
lean_inc_ref(v_array_1409_);
lean_del_object(v___x_1407_);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_pos_1404_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; lean_object* v_unused_1465_; 
v_unused_1464_ = lean_ctor_get(v_pos_1404_, 1);
lean_dec(v_unused_1464_);
v_unused_1465_ = lean_ctor_get(v_pos_1404_, 0);
lean_dec(v_unused_1465_);
v___x_1425_ = v_pos_1404_;
v_isShared_1426_ = v_isSharedCheck_1463_;
goto v_resetjp_1424_;
}
else
{
lean_dec(v_pos_1404_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1463_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1427_ = lean_unsigned_to_nat(1u);
v___x_1428_ = lean_nat_add(v_idx_1410_, v___x_1427_);
lean_dec(v_idx_1410_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 1, v___x_1428_);
v___x_1430_ = v___x_1425_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_array_1409_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
lean_object* v___x_1431_; 
v___x_1431_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_1399_, v___x_1430_);
if (lean_obj_tag(v___x_1431_) == 0)
{
if (lean_obj_tag(v_res_1405_) == 1)
{
lean_object* v_pos_1432_; lean_object* v_res_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1442_; 
v_pos_1432_ = lean_ctor_get(v___x_1431_, 0);
v_res_1433_ = lean_ctor_get(v___x_1431_, 1);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1435_ = v___x_1431_;
v_isShared_1436_ = v_isSharedCheck_1442_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_res_1433_);
lean_inc(v_pos_1432_);
lean_dec(v___x_1431_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1442_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v_val_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
v_val_1437_ = lean_ctor_get(v_res_1405_, 0);
lean_inc(v_val_1437_);
lean_dec_ref_known(v_res_1405_, 1);
v___x_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1438_, 0, v_val_1437_);
lean_ctor_set(v___x_1438_, 1, v_res_1433_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 1, v___x_1438_);
v___x_1440_ = v___x_1435_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_pos_1432_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
else
{
lean_object* v_pos_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1451_; 
lean_dec(v_res_1405_);
v_pos_1443_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1451_ == 0)
{
lean_object* v_unused_1452_; 
v_unused_1452_ = lean_ctor_get(v___x_1431_, 1);
lean_dec(v_unused_1452_);
v___x_1445_ = v___x_1431_;
v_isShared_1446_ = v_isSharedCheck_1451_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_pos_1443_);
lean_dec(v___x_1431_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1451_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1447_; lean_object* v___x_1449_; 
v___x_1447_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3));
if (v_isShared_1446_ == 0)
{
lean_ctor_set_tag(v___x_1445_, 1);
lean_ctor_set(v___x_1445_, 1, v___x_1447_);
v___x_1449_ = v___x_1445_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_pos_1443_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
else
{
lean_object* v_pos_1453_; lean_object* v_err_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec(v_res_1405_);
v_pos_1453_ = lean_ctor_get(v___x_1431_, 0);
v_err_1454_ = lean_ctor_get(v___x_1431_, 1);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1431_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_err_1454_);
lean_inc(v_pos_1453_);
lean_dec(v___x_1431_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_pos_1453_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_err_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
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
lean_object* v_pos_1467_; lean_object* v_err_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
v_pos_1467_ = lean_ctor_get(v___x_1403_, 0);
v_err_1468_ = lean_ctor_get(v___x_1403_, 1);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1403_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_err_1468_);
lean_inc(v_pos_1467_);
lean_dec(v___x_1403_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_pos_1467_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v_err_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
else
{
lean_object* v_pos_1476_; lean_object* v_err_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
v_pos_1476_ = lean_ctor_get(v___x_1401_, 0);
v_err_1477_ = lean_ctor_get(v___x_1401_, 1);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1401_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_err_1477_);
lean_inc(v_pos_1476_);
lean_dec(v___x_1401_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_pos_1476_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_err_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineParts___boxed(lean_object* v_limits_1485_, lean_object* v_a_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineParts(v_limits_1485_, v_a_1486_);
lean_dec_ref(v_limits_1485_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine(lean_object* v_limits_1491_, lean_object* v_a_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineParts(v_limits_1491_, v_a_1492_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_pos_1494_; lean_object* v_res_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1539_; 
v_pos_1494_ = lean_ctor_get(v___x_1493_, 0);
v_res_1495_ = lean_ctor_get(v___x_1493_, 1);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1497_ = v___x_1493_;
v_isShared_1498_ = v_isSharedCheck_1539_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_res_1495_);
lean_inc(v_pos_1494_);
lean_dec(v___x_1493_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1539_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v_snd_1504_; lean_object* v_snd_1505_; lean_object* v_fst_1506_; lean_object* v_fst_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1537_; 
v_snd_1504_ = lean_ctor_get(v_res_1495_, 1);
lean_inc(v_snd_1504_);
v_snd_1505_ = lean_ctor_get(v_snd_1504_, 1);
lean_inc(v_snd_1505_);
v_fst_1506_ = lean_ctor_get(v_res_1495_, 0);
lean_inc(v_fst_1506_);
lean_dec(v_res_1495_);
v_fst_1507_ = lean_ctor_get(v_snd_1504_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_snd_1504_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; 
v_unused_1538_ = lean_ctor_get(v_snd_1504_, 1);
lean_dec(v_unused_1538_);
v___x_1509_ = v_snd_1504_;
v_isShared_1510_ = v_isSharedCheck_1537_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_fst_1507_);
lean_dec(v_snd_1504_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1537_;
goto v_resetjp_1508_;
}
v___jp_1499_:
{
lean_object* v___x_1500_; lean_object* v___x_1502_; 
v___x_1500_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
if (v_isShared_1498_ == 0)
{
lean_ctor_set_tag(v___x_1497_, 1);
lean_ctor_set(v___x_1497_, 1, v___x_1500_);
v___x_1502_ = v___x_1497_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_pos_1494_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v___x_1500_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
v_resetjp_1508_:
{
lean_object* v_fst_1511_; lean_object* v_snd_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1536_; 
v_fst_1511_ = lean_ctor_get(v_snd_1505_, 0);
v_snd_1512_ = lean_ctor_get(v_snd_1505_, 1);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_snd_1505_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1514_ = v_snd_1505_;
v_isShared_1515_ = v_isSharedCheck_1536_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_snd_1512_);
lean_inc(v_fst_1511_);
lean_dec(v_snd_1505_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1536_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; uint8_t v___x_1517_; 
v___x_1516_ = lean_unsigned_to_nat(1u);
v___x_1517_ = lean_nat_dec_eq(v_fst_1511_, v___x_1516_);
lean_dec(v_fst_1511_);
if (v___x_1517_ == 0)
{
lean_del_object(v___x_1509_);
goto v___jp_1518_;
}
else
{
uint8_t v___x_1528_; 
v___x_1528_ = lean_nat_dec_le(v___x_1516_, v_snd_1512_);
if (v___x_1528_ == 0)
{
lean_del_object(v___x_1509_);
goto v___jp_1518_;
}
else
{
uint8_t v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; lean_object* v___x_1534_; 
lean_del_object(v___x_1514_);
lean_dec(v_snd_1512_);
lean_del_object(v___x_1497_);
v___x_1529_ = 1;
v___x_1530_ = l_Std_Http_Headers_empty;
v___x_1531_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1531_, 0, v_fst_1507_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = lean_unbox(v_fst_1506_);
lean_dec(v_fst_1506_);
lean_ctor_set_uint8(v___x_1531_, sizeof(void*)*2, v___x_1532_);
lean_ctor_set_uint8(v___x_1531_, sizeof(void*)*2 + 1, v___x_1529_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 1, v___x_1531_);
lean_ctor_set(v___x_1509_, 0, v_pos_1494_);
v___x_1534_ = v___x_1509_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_pos_1494_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v___x_1531_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
v___jp_1518_:
{
if (v___x_1517_ == 0)
{
lean_del_object(v___x_1514_);
lean_dec(v_snd_1512_);
lean_dec(v_fst_1507_);
lean_dec(v_fst_1506_);
goto v___jp_1499_;
}
else
{
lean_object* v___x_1519_; uint8_t v___x_1520_; 
v___x_1519_ = lean_unsigned_to_nat(0u);
v___x_1520_ = lean_nat_dec_eq(v_snd_1512_, v___x_1519_);
lean_dec(v_snd_1512_);
if (v___x_1520_ == 0)
{
lean_del_object(v___x_1514_);
lean_dec(v_fst_1507_);
lean_dec(v_fst_1506_);
goto v___jp_1499_;
}
else
{
uint8_t v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; uint8_t v___x_1524_; lean_object* v___x_1526_; 
lean_del_object(v___x_1497_);
v___x_1521_ = 0;
v___x_1522_ = l_Std_Http_Headers_empty;
v___x_1523_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1523_, 0, v_fst_1507_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
v___x_1524_ = lean_unbox(v_fst_1506_);
lean_dec(v_fst_1506_);
lean_ctor_set_uint8(v___x_1523_, sizeof(void*)*2, v___x_1524_);
lean_ctor_set_uint8(v___x_1523_, sizeof(void*)*2 + 1, v___x_1521_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 1, v___x_1523_);
lean_ctor_set(v___x_1514_, 0, v_pos_1494_);
v___x_1526_ = v___x_1514_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_pos_1494_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v___x_1523_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
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
lean_object* v_pos_1540_; lean_object* v_err_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
v_pos_1540_ = lean_ctor_get(v___x_1493_, 0);
v_err_1541_ = lean_ctor_get(v___x_1493_, 1);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1493_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_err_1541_);
lean_inc(v_pos_1540_);
lean_dec(v___x_1493_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_pos_1540_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_err_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine___boxed(lean_object* v_limits_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Std_Http_Protocol_H1_parseRequestLine(v_limits_1549_, v_a_1550_);
lean_dec_ref(v_limits_1549_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion(lean_object* v_limits_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineParts(v_limits_1552_, v_a_1553_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_res_1555_; lean_object* v_snd_1556_; lean_object* v_snd_1557_; lean_object* v_pos_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1590_; 
v_res_1555_ = lean_ctor_get(v___x_1554_, 1);
lean_inc(v_res_1555_);
v_snd_1556_ = lean_ctor_get(v_res_1555_, 1);
lean_inc(v_snd_1556_);
v_snd_1557_ = lean_ctor_get(v_snd_1556_, 1);
lean_inc(v_snd_1557_);
v_pos_1558_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; 
v_unused_1591_ = lean_ctor_get(v___x_1554_, 1);
lean_dec(v_unused_1591_);
v___x_1560_ = v___x_1554_;
v_isShared_1561_ = v_isSharedCheck_1590_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_pos_1558_);
lean_dec(v___x_1554_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1590_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v_fst_1562_; lean_object* v_fst_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1588_; 
v_fst_1562_ = lean_ctor_get(v_res_1555_, 0);
lean_inc(v_fst_1562_);
lean_dec(v_res_1555_);
v_fst_1563_ = lean_ctor_get(v_snd_1556_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v_snd_1556_);
if (v_isSharedCheck_1588_ == 0)
{
lean_object* v_unused_1589_; 
v_unused_1589_ = lean_ctor_get(v_snd_1556_, 1);
lean_dec(v_unused_1589_);
v___x_1565_ = v_snd_1556_;
v_isShared_1566_ = v_isSharedCheck_1588_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_fst_1563_);
lean_dec(v_snd_1556_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1588_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v_fst_1567_; lean_object* v_snd_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1587_; 
v_fst_1567_ = lean_ctor_get(v_snd_1557_, 0);
v_snd_1568_ = lean_ctor_get(v_snd_1557_, 1);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_snd_1557_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1570_ = v_snd_1557_;
v_isShared_1571_ = v_isSharedCheck_1587_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_snd_1568_);
lean_inc(v_fst_1567_);
lean_dec(v_snd_1557_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1587_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___y_1573_; lean_object* v___x_1584_; uint8_t v___x_1585_; 
v___x_1584_ = lean_unsigned_to_nat(1u);
v___x_1585_ = lean_nat_dec_eq(v_fst_1567_, v___x_1584_);
if (v___x_1585_ == 0)
{
v___y_1573_ = v_snd_1568_;
goto v___jp_1572_;
}
else
{
uint8_t v___x_1586_; 
v___x_1586_ = lean_nat_dec_le(v_snd_1568_, v___x_1584_);
if (v___x_1586_ == 0)
{
lean_dec(v_snd_1568_);
v___y_1573_ = v___x_1584_;
goto v___jp_1572_;
}
else
{
v___y_1573_ = v_snd_1568_;
goto v___jp_1572_;
}
}
v___jp_1572_:
{
lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1574_ = l_Std_Http_Version_ofNumber_x3f(v_fst_1567_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec(v_fst_1567_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 1, v___x_1574_);
lean_ctor_set(v___x_1570_, 0, v_fst_1563_);
v___x_1576_ = v___x_1570_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_fst_1563_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1578_; 
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 1, v___x_1576_);
lean_ctor_set(v___x_1565_, 0, v_fst_1562_);
v___x_1578_ = v___x_1565_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_fst_1562_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v___x_1580_; 
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 1, v___x_1578_);
v___x_1580_ = v___x_1560_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_pos_1558_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v___x_1578_);
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
lean_object* v_pos_1592_; lean_object* v_err_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
v_pos_1592_ = lean_ctor_get(v___x_1554_, 0);
v_err_1593_ = lean_ctor_get(v___x_1554_, 1);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1554_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_err_1593_);
lean_inc(v_pos_1592_);
lean_dec(v___x_1554_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_pos_1592_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_err_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion___boxed(lean_object* v_limits_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Std_Http_Protocol_H1_parseRequestLineRawVersion(v_limits_1601_, v_a_1602_);
lean_dec_ref(v_limits_1601_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_checkFieldValueLength(lean_object* v_limits_1607_, lean_object* v_value_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v_pos_1611_; lean_object* v_pos_1615_; 
if (lean_obj_tag(v_value_1608_) == 1)
{
lean_object* v_val_1618_; lean_object* v_maxHeaderValueLength_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
v_val_1618_ = lean_ctor_get(v_value_1608_, 0);
v_maxHeaderValueLength_1619_ = lean_ctor_get(v_limits_1607_, 7);
v___x_1620_ = l_ByteSlice_size(v_val_1618_);
v___x_1621_ = lean_nat_dec_eq(v___x_1620_, v_maxHeaderValueLength_1619_);
lean_dec(v___x_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = lean_box(0);
v___x_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1623_, 0, v_a_1609_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
return v___x_1623_;
}
else
{
lean_object* v_array_1624_; lean_object* v_idx_1625_; lean_object* v___x_1626_; uint8_t v___x_1627_; 
v_array_1624_ = lean_ctor_get(v_a_1609_, 0);
v_idx_1625_ = lean_ctor_get(v_a_1609_, 1);
v___x_1626_ = lean_byte_array_size(v_array_1624_);
v___x_1627_ = lean_nat_dec_lt(v_idx_1625_, v___x_1626_);
if (v___x_1627_ == 0)
{
v_pos_1615_ = v_a_1609_;
goto v___jp_1614_;
}
else
{
uint8_t v___x_1628_; uint32_t v___x_1629_; uint32_t v___x_1637_; uint8_t v___x_1638_; 
v___x_1628_ = lean_byte_array_fget(v_array_1624_, v_idx_1625_);
v___x_1629_ = lean_uint8_to_uint32(v___x_1628_);
v___x_1637_ = 33;
v___x_1638_ = lean_uint32_dec_le(v___x_1637_, v___x_1629_);
if (v___x_1638_ == 0)
{
goto v___jp_1630_;
}
else
{
uint32_t v___x_1639_; uint8_t v___x_1640_; 
v___x_1639_ = 126;
v___x_1640_ = lean_uint32_dec_le(v___x_1629_, v___x_1639_);
if (v___x_1640_ == 0)
{
goto v___jp_1630_;
}
else
{
v_pos_1611_ = v_a_1609_;
goto v___jp_1610_;
}
}
v___jp_1630_:
{
uint32_t v___x_1631_; uint8_t v___x_1632_; 
v___x_1631_ = 128;
v___x_1632_ = lean_uint32_dec_le(v___x_1631_, v___x_1629_);
if (v___x_1632_ == 0)
{
uint32_t v___x_1633_; uint8_t v___x_1634_; 
v___x_1633_ = 32;
v___x_1634_ = lean_uint32_dec_eq(v___x_1629_, v___x_1633_);
if (v___x_1634_ == 0)
{
uint32_t v___x_1635_; uint8_t v___x_1636_; 
v___x_1635_ = 9;
v___x_1636_ = lean_uint32_dec_eq(v___x_1629_, v___x_1635_);
if (v___x_1636_ == 0)
{
v_pos_1615_ = v_a_1609_;
goto v___jp_1614_;
}
else
{
v_pos_1611_ = v_a_1609_;
goto v___jp_1610_;
}
}
else
{
v_pos_1611_ = v_a_1609_;
goto v___jp_1610_;
}
}
else
{
v_pos_1611_ = v_a_1609_;
goto v___jp_1610_;
}
}
}
}
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = lean_box(0);
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v_a_1609_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
return v___x_1642_;
}
v___jp_1610_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_checkFieldValueLength___closed__1));
v___x_1613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1613_, 0, v_pos_1611_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
return v___x_1613_;
}
v___jp_1614_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = lean_box(0);
v___x_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1617_, 0, v_pos_1615_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
return v___x_1617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_checkFieldValueLength___boxed(lean_object* v_limits_1643_, lean_object* v_value_1644_, lean_object* v_a_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_checkFieldValueLength(v_limits_1643_, v_value_1644_, v_a_1645_);
lean_dec(v_value_1644_);
lean_dec_ref(v_limits_1643_);
return v_res_1646_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(uint8_t v___y_1647_){
_start:
{
uint32_t v___x_1648_; uint32_t v___x_1649_; uint8_t v___x_1650_; 
v___x_1648_ = lean_uint8_to_uint32(v___y_1647_);
v___x_1649_ = 32;
v___x_1650_ = lean_uint32_dec_eq(v___x_1648_, v___x_1649_);
if (v___x_1650_ == 0)
{
uint32_t v___x_1651_; uint8_t v___x_1652_; 
v___x_1651_ = 9;
v___x_1652_ = lean_uint32_dec_eq(v___x_1648_, v___x_1651_);
return v___x_1652_;
}
else
{
return v___x_1650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed(lean_object* v___y_1653_){
_start:
{
uint8_t v___y_4884__boxed_1654_; uint8_t v_res_1655_; lean_object* v_r_1656_; 
v___y_4884__boxed_1654_ = lean_unbox(v___y_1653_);
v_res_1655_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(v___y_4884__boxed_1654_);
v_r_1656_ = lean_box(v_res_1655_);
return v_r_1656_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0(uint8_t v___y_1657_){
_start:
{
uint32_t v___x_1658_; uint32_t v___x_1666_; uint8_t v___x_1667_; 
v___x_1658_ = lean_uint8_to_uint32(v___y_1657_);
v___x_1666_ = 33;
v___x_1667_ = lean_uint32_dec_le(v___x_1666_, v___x_1658_);
if (v___x_1667_ == 0)
{
goto v___jp_1659_;
}
else
{
uint32_t v___x_1668_; uint8_t v___x_1669_; 
v___x_1668_ = 126;
v___x_1669_ = lean_uint32_dec_le(v___x_1658_, v___x_1668_);
if (v___x_1669_ == 0)
{
goto v___jp_1659_;
}
else
{
return v___x_1669_;
}
}
v___jp_1659_:
{
uint32_t v___x_1660_; uint8_t v___x_1661_; 
v___x_1660_ = 128;
v___x_1661_ = lean_uint32_dec_le(v___x_1660_, v___x_1658_);
if (v___x_1661_ == 0)
{
uint32_t v___x_1662_; uint8_t v___x_1663_; 
v___x_1662_ = 32;
v___x_1663_ = lean_uint32_dec_eq(v___x_1658_, v___x_1662_);
if (v___x_1663_ == 0)
{
uint32_t v___x_1664_; uint8_t v___x_1665_; 
v___x_1664_ = 9;
v___x_1665_ = lean_uint32_dec_eq(v___x_1658_, v___x_1664_);
return v___x_1665_;
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0___boxed(lean_object* v___y_1670_){
_start:
{
uint8_t v___y_4897__boxed_1671_; uint8_t v_res_1672_; lean_object* v_r_1673_; 
v___y_4897__boxed_1671_ = lean_unbox(v___y_1670_);
v_res_1672_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0(v___y_4897__boxed_1671_);
v_r_1673_ = lean_box(v_res_1672_);
return v_r_1673_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(lean_object* v_s_1674_, lean_object* v_pos_1675_){
_start:
{
lean_object* v_str_1676_; lean_object* v_startInclusive_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; uint8_t v_decide_1681_; 
v_str_1676_ = lean_ctor_get(v_s_1674_, 0);
v_startInclusive_1677_ = lean_ctor_get(v_s_1674_, 1);
v___x_1678_ = lean_nat_add(v_startInclusive_1677_, v_pos_1675_);
v___x_1679_ = lean_nat_sub(v___x_1678_, v_startInclusive_1677_);
v___x_1680_ = lean_unsigned_to_nat(0u);
v_decide_1681_ = lean_nat_dec_eq(v___x_1679_, v___x_1680_);
if (v_decide_1681_ == 0)
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1690_; uint32_t v___x_1691_; uint32_t v___x_1692_; uint8_t v___x_1693_; 
lean_inc(v_startInclusive_1677_);
lean_inc_ref(v_str_1676_);
v___x_1682_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1682_, 0, v_str_1676_);
lean_ctor_set(v___x_1682_, 1, v_startInclusive_1677_);
lean_ctor_set(v___x_1682_, 2, v___x_1678_);
v___x_1683_ = lean_unsigned_to_nat(1u);
v___x_1684_ = lean_nat_sub(v___x_1679_, v___x_1683_);
lean_dec(v___x_1679_);
v___x_1685_ = l_String_Slice_posLE(v___x_1682_, v___x_1684_);
lean_dec_ref_known(v___x_1682_, 3);
v___x_1690_ = lean_nat_add(v_startInclusive_1677_, v___x_1685_);
v___x_1691_ = lean_string_utf8_get_fast(v_str_1676_, v___x_1690_);
lean_dec(v___x_1690_);
v___x_1692_ = 32;
v___x_1693_ = lean_uint32_dec_eq(v___x_1691_, v___x_1692_);
if (v___x_1693_ == 0)
{
uint32_t v___x_1694_; uint8_t v___x_1695_; 
v___x_1694_ = 9;
v___x_1695_ = lean_uint32_dec_eq(v___x_1691_, v___x_1694_);
if (v___x_1695_ == 0)
{
uint32_t v___x_1696_; uint8_t v___x_1697_; 
v___x_1696_ = 13;
v___x_1697_ = lean_uint32_dec_eq(v___x_1691_, v___x_1696_);
if (v___x_1697_ == 0)
{
uint32_t v___x_1698_; uint8_t v___x_1699_; 
v___x_1698_ = 10;
v___x_1699_ = lean_uint32_dec_eq(v___x_1691_, v___x_1698_);
if (v___x_1699_ == 0)
{
lean_dec(v___x_1685_);
return v_pos_1675_;
}
else
{
goto v___jp_1686_;
}
}
else
{
goto v___jp_1686_;
}
}
else
{
goto v___jp_1686_;
}
}
else
{
goto v___jp_1686_;
}
v___jp_1686_:
{
lean_object* v___x_1687_; uint8_t v___x_1688_; 
v___x_1687_ = lean_nat_add(v___x_1685_, v___x_1683_);
v___x_1688_ = lean_nat_dec_le(v___x_1687_, v_pos_1675_);
lean_dec(v___x_1687_);
if (v___x_1688_ == 0)
{
lean_dec(v___x_1685_);
return v_pos_1675_;
}
else
{
lean_dec(v_pos_1675_);
v_pos_1675_ = v___x_1685_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1679_);
lean_dec(v___x_1678_);
return v_pos_1675_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0___boxed(lean_object* v_s_1700_, lean_object* v_pos_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(v_s_1700_, v_pos_1701_);
lean_dec_ref(v_s_1700_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(lean_object* v_limits_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v_pos_1715_; lean_object* v_pos_1719_; lean_object* v_pos_1723_; lean_object* v_maxHeaderNameLength_1726_; lean_object* v_maxHeaderValueLength_1727_; lean_object* v_maxSpaceSequence_1728_; lean_object* v___f_1729_; lean_object* v___x_1730_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1766_; lean_object* v_pos_1767_; lean_object* v_res_1768_; lean_object* v___x_1785_; lean_object* v_snd_1786_; lean_object* v_snd_1787_; uint8_t v___x_1788_; 
v_maxHeaderNameLength_1726_ = lean_ctor_get(v_limits_1712_, 6);
v_maxHeaderValueLength_1727_ = lean_ctor_get(v_limits_1712_, 7);
v_maxSpaceSequence_1728_ = lean_ctor_get(v_limits_1712_, 8);
v___f_1729_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_1730_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1713_);
v___x_1785_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1729_, v_maxHeaderNameLength_1726_, v___x_1730_, v_a_1713_);
v_snd_1786_ = lean_ctor_get(v___x_1785_, 1);
lean_inc(v_snd_1786_);
v_snd_1787_ = lean_ctor_get(v_snd_1786_, 1);
v___x_1788_ = lean_unbox(v_snd_1787_);
if (v___x_1788_ == 0)
{
lean_object* v_fst_1789_; lean_object* v_fst_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_2000_; 
v_fst_1789_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_fst_1789_);
lean_dec_ref(v___x_1785_);
v_fst_1790_ = lean_ctor_get(v_snd_1786_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v_snd_1786_);
if (v_isSharedCheck_2000_ == 0)
{
lean_object* v_unused_2001_; 
v_unused_2001_ = lean_ctor_get(v_snd_1786_, 1);
lean_dec(v_unused_2001_);
v___x_1792_ = v_snd_1786_;
v_isShared_1793_ = v_isSharedCheck_2000_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_fst_1790_);
lean_dec(v_snd_1786_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_2000_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
uint8_t v___x_1794_; 
v___x_1794_ = lean_nat_dec_eq(v_fst_1789_, v___x_1730_);
if (v___x_1794_ == 0)
{
lean_object* v_array_1795_; lean_object* v_idx_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1995_; 
v_array_1795_ = lean_ctor_get(v_a_1713_, 0);
v_idx_1796_ = lean_ctor_get(v_a_1713_, 1);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_a_1713_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1798_ = v_a_1713_;
v_isShared_1799_ = v_isSharedCheck_1995_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_idx_1796_);
lean_inc(v_array_1795_);
lean_dec(v_a_1713_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1995_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___f_1800_; lean_object* v___y_1802_; lean_object* v_pos_1803_; lean_object* v_res_1804_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v_lower_1834_; lean_object* v_upper_1835_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___f_1846_; lean_object* v___y_1848_; lean_object* v_pos_1849_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v_array_1878_; lean_object* v_idx_1879_; lean_object* v___y_1924_; lean_object* v___y_1925_; uint32_t v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1933_; lean_object* v___y_1934_; uint32_t v___y_1935_; lean_object* v___y_1936_; lean_object* v_lower_1942_; lean_object* v_upper_1943_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___y_1992_; uint8_t v___x_1994_; 
v___f_1800_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3));
v___f_1846_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4));
v___x_1989_ = lean_nat_add(v_idx_1796_, v_fst_1789_);
lean_dec(v_fst_1789_);
v___x_1990_ = lean_byte_array_size(v_array_1795_);
v___x_1994_ = lean_nat_dec_le(v_idx_1796_, v___x_1730_);
if (v___x_1994_ == 0)
{
v___y_1992_ = v_idx_1796_;
goto v___jp_1991_;
}
else
{
lean_dec(v_idx_1796_);
v___y_1992_ = v___x_1730_;
goto v___jp_1991_;
}
v___jp_1801_:
{
lean_object* v___x_1805_; lean_object* v_snd_1806_; lean_object* v_snd_1807_; uint8_t v___x_1808_; 
v___x_1805_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1800_, v_maxSpaceSequence_1728_, v___x_1730_, v_pos_1803_);
v_snd_1806_ = lean_ctor_get(v___x_1805_, 1);
lean_inc(v_snd_1806_);
lean_dec_ref(v___x_1805_);
v_snd_1807_ = lean_ctor_get(v_snd_1806_, 1);
v___x_1808_ = lean_unbox(v_snd_1807_);
if (v___x_1808_ == 0)
{
lean_object* v_fst_1809_; lean_object* v_array_1810_; lean_object* v_idx_1811_; lean_object* v___x_1812_; uint8_t v___x_1813_; 
v_fst_1809_ = lean_ctor_get(v_snd_1806_, 0);
lean_inc(v_fst_1809_);
lean_dec(v_snd_1806_);
v_array_1810_ = lean_ctor_get(v_fst_1809_, 0);
v_idx_1811_ = lean_ctor_get(v_fst_1809_, 1);
v___x_1812_ = lean_byte_array_size(v_array_1810_);
v___x_1813_ = lean_nat_dec_lt(v_idx_1811_, v___x_1812_);
if (v___x_1813_ == 0)
{
v___y_1766_ = v___y_1802_;
v_pos_1767_ = v_fst_1809_;
v_res_1768_ = v_res_1804_;
goto v___jp_1765_;
}
else
{
uint8_t v___x_1814_; uint32_t v___x_1815_; uint32_t v___x_1816_; uint8_t v___x_1817_; 
v___x_1814_ = lean_byte_array_fget(v_array_1810_, v_idx_1811_);
v___x_1815_ = lean_uint8_to_uint32(v___x_1814_);
v___x_1816_ = 32;
v___x_1817_ = lean_uint32_dec_eq(v___x_1815_, v___x_1816_);
if (v___x_1817_ == 0)
{
uint32_t v___x_1818_; uint8_t v___x_1819_; 
v___x_1818_ = 9;
v___x_1819_ = lean_uint32_dec_eq(v___x_1815_, v___x_1818_);
if (v___x_1819_ == 0)
{
v___y_1766_ = v___y_1802_;
v_pos_1767_ = v_fst_1809_;
v_res_1768_ = v_res_1804_;
goto v___jp_1765_;
}
else
{
lean_dec(v_res_1804_);
lean_dec_ref(v___y_1802_);
v_pos_1723_ = v_fst_1809_;
goto v___jp_1722_;
}
}
else
{
lean_dec(v_res_1804_);
lean_dec_ref(v___y_1802_);
v_pos_1723_ = v_fst_1809_;
goto v___jp_1722_;
}
}
}
else
{
lean_object* v_fst_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1828_; 
lean_dec(v_res_1804_);
lean_dec_ref(v___y_1802_);
v_fst_1820_ = lean_ctor_get(v_snd_1806_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v_snd_1806_);
if (v_isSharedCheck_1828_ == 0)
{
lean_object* v_unused_1829_; 
v_unused_1829_ = lean_ctor_get(v_snd_1806_, 1);
lean_dec(v_unused_1829_);
v___x_1822_ = v_snd_1806_;
v_isShared_1823_ = v_isSharedCheck_1828_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_fst_1820_);
lean_dec(v_snd_1806_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1828_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1824_ = lean_box(0);
if (v_isShared_1823_ == 0)
{
lean_ctor_set_tag(v___x_1822_, 1);
lean_ctor_set(v___x_1822_, 1, v___x_1824_);
v___x_1826_ = v___x_1822_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_fst_1820_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
v___jp_1830_:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = l_ByteArray_toByteSlice(v___y_1831_, v_lower_1834_, v_upper_1835_);
v___x_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
v___y_1802_ = v___y_1832_;
v_pos_1803_ = v___y_1833_;
v_res_1804_ = v___x_1837_;
goto v___jp_1801_;
}
v___jp_1838_:
{
uint8_t v___x_1845_; 
v___x_1845_ = lean_nat_dec_le(v___y_1843_, v___y_1840_);
if (v___x_1845_ == 0)
{
lean_dec(v___y_1843_);
v___y_1831_ = v___y_1839_;
v___y_1832_ = v___y_1841_;
v___y_1833_ = v___y_1842_;
v_lower_1834_ = v___y_1844_;
v_upper_1835_ = v___y_1840_;
goto v___jp_1830_;
}
else
{
lean_dec(v___y_1840_);
v___y_1831_ = v___y_1839_;
v___y_1832_ = v___y_1841_;
v___y_1833_ = v___y_1842_;
v_lower_1834_ = v___y_1844_;
v_upper_1835_ = v___y_1843_;
goto v___jp_1830_;
}
}
v___jp_1847_:
{
lean_object* v___x_1850_; lean_object* v_snd_1851_; lean_object* v_snd_1852_; uint8_t v___x_1853_; 
lean_inc_ref(v_pos_1849_);
v___x_1850_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1846_, v_maxHeaderValueLength_1727_, v___x_1730_, v_pos_1849_);
v_snd_1851_ = lean_ctor_get(v___x_1850_, 1);
lean_inc(v_snd_1851_);
v_snd_1852_ = lean_ctor_get(v_snd_1851_, 1);
v___x_1853_ = lean_unbox(v_snd_1852_);
if (v___x_1853_ == 0)
{
lean_object* v_fst_1854_; lean_object* v_fst_1855_; lean_object* v_array_1856_; lean_object* v_idx_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; uint8_t v___x_1860_; 
v_fst_1854_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_fst_1854_);
lean_dec_ref(v___x_1850_);
v_fst_1855_ = lean_ctor_get(v_snd_1851_, 0);
lean_inc(v_fst_1855_);
lean_dec(v_snd_1851_);
v_array_1856_ = lean_ctor_get(v_pos_1849_, 0);
lean_inc_ref(v_array_1856_);
v_idx_1857_ = lean_ctor_get(v_pos_1849_, 1);
lean_inc(v_idx_1857_);
lean_dec_ref(v_pos_1849_);
v___x_1858_ = lean_nat_add(v_idx_1857_, v_fst_1854_);
lean_dec(v_fst_1854_);
v___x_1859_ = lean_byte_array_size(v_array_1856_);
v___x_1860_ = lean_nat_dec_le(v_idx_1857_, v___x_1730_);
if (v___x_1860_ == 0)
{
v___y_1839_ = v_array_1856_;
v___y_1840_ = v___x_1859_;
v___y_1841_ = v___y_1848_;
v___y_1842_ = v_fst_1855_;
v___y_1843_ = v___x_1858_;
v___y_1844_ = v_idx_1857_;
goto v___jp_1838_;
}
else
{
lean_dec(v_idx_1857_);
v___y_1839_ = v_array_1856_;
v___y_1840_ = v___x_1859_;
v___y_1841_ = v___y_1848_;
v___y_1842_ = v_fst_1855_;
v___y_1843_ = v___x_1858_;
v___y_1844_ = v___x_1730_;
goto v___jp_1838_;
}
}
else
{
lean_object* v_fst_1861_; lean_object* v_idx_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1873_; 
lean_dec_ref(v___x_1850_);
v_fst_1861_ = lean_ctor_get(v_snd_1851_, 0);
lean_inc(v_fst_1861_);
lean_dec(v_snd_1851_);
v_idx_1862_ = lean_ctor_get(v_pos_1849_, 1);
v_isSharedCheck_1873_ = !lean_is_exclusive(v_pos_1849_);
if (v_isSharedCheck_1873_ == 0)
{
lean_object* v_unused_1874_; 
v_unused_1874_ = lean_ctor_get(v_pos_1849_, 0);
lean_dec(v_unused_1874_);
v___x_1864_ = v_pos_1849_;
v_isShared_1865_ = v_isSharedCheck_1873_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_idx_1862_);
lean_dec(v_pos_1849_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1873_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v_idx_1866_; uint8_t v___x_1867_; 
v_idx_1866_ = lean_ctor_get(v_fst_1861_, 1);
v___x_1867_ = lean_nat_dec_eq(v_idx_1862_, v_idx_1866_);
lean_dec(v_idx_1862_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; lean_object* v___x_1870_; 
lean_dec_ref(v___y_1848_);
v___x_1868_ = lean_box(0);
if (v_isShared_1865_ == 0)
{
lean_ctor_set_tag(v___x_1864_, 1);
lean_ctor_set(v___x_1864_, 1, v___x_1868_);
lean_ctor_set(v___x_1864_, 0, v_fst_1861_);
v___x_1870_ = v___x_1864_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_fst_1861_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v___x_1868_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
else
{
lean_object* v___x_1872_; 
lean_del_object(v___x_1864_);
v___x_1872_ = lean_box(0);
v___y_1802_ = v___y_1848_;
v_pos_1803_ = v_fst_1861_;
v_res_1804_ = v___x_1872_;
goto v___jp_1801_;
}
}
}
}
v___jp_1875_:
{
lean_object* v___x_1880_; uint8_t v___x_1881_; 
v___x_1880_ = lean_byte_array_size(v_array_1878_);
v___x_1881_ = lean_nat_dec_lt(v_idx_1879_, v___x_1880_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1884_; 
lean_dec(v_idx_1879_);
lean_dec_ref(v_array_1878_);
lean_dec_ref(v___y_1876_);
lean_del_object(v___x_1798_);
v___x_1882_ = lean_box(0);
if (v_isShared_1793_ == 0)
{
lean_ctor_set_tag(v___x_1792_, 1);
lean_ctor_set(v___x_1792_, 1, v___x_1882_);
lean_ctor_set(v___x_1792_, 0, v___y_1877_);
v___x_1884_ = v___x_1792_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___y_1877_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
else
{
uint8_t v___x_1886_; uint8_t v_got_1887_; uint8_t v___x_1888_; 
v___x_1886_ = 58;
v_got_1887_ = lean_byte_array_fget(v_array_1878_, v_idx_1879_);
v___x_1888_ = lean_uint8_dec_eq(v_got_1887_, v___x_1886_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; lean_object* v___x_1891_; 
lean_dec(v_idx_1879_);
lean_dec_ref(v_array_1878_);
lean_dec_ref(v___y_1876_);
lean_del_object(v___x_1798_);
v___x_1889_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__6));
if (v_isShared_1793_ == 0)
{
lean_ctor_set_tag(v___x_1792_, 1);
lean_ctor_set(v___x_1792_, 1, v___x_1889_);
lean_ctor_set(v___x_1792_, 0, v___y_1877_);
v___x_1891_ = v___x_1792_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___y_1877_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v___x_1889_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
else
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1896_; 
lean_dec_ref(v___y_1877_);
lean_del_object(v___x_1792_);
v___x_1893_ = lean_unsigned_to_nat(1u);
v___x_1894_ = lean_nat_add(v_idx_1879_, v___x_1893_);
lean_dec(v_idx_1879_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 1, v___x_1894_);
lean_ctor_set(v___x_1798_, 0, v_array_1878_);
v___x_1896_ = v___x_1798_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_array_1878_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1897_; lean_object* v_snd_1898_; lean_object* v_snd_1899_; uint8_t v___x_1900_; 
v___x_1897_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1800_, v_maxSpaceSequence_1728_, v___x_1730_, v___x_1896_);
v_snd_1898_ = lean_ctor_get(v___x_1897_, 1);
lean_inc(v_snd_1898_);
lean_dec_ref(v___x_1897_);
v_snd_1899_ = lean_ctor_get(v_snd_1898_, 1);
v___x_1900_ = lean_unbox(v_snd_1899_);
if (v___x_1900_ == 0)
{
lean_object* v_fst_1901_; lean_object* v_array_1902_; lean_object* v_idx_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; 
v_fst_1901_ = lean_ctor_get(v_snd_1898_, 0);
lean_inc(v_fst_1901_);
lean_dec(v_snd_1898_);
v_array_1902_ = lean_ctor_get(v_fst_1901_, 0);
v_idx_1903_ = lean_ctor_get(v_fst_1901_, 1);
v___x_1904_ = lean_byte_array_size(v_array_1902_);
v___x_1905_ = lean_nat_dec_lt(v_idx_1903_, v___x_1904_);
if (v___x_1905_ == 0)
{
v___y_1848_ = v___y_1876_;
v_pos_1849_ = v_fst_1901_;
goto v___jp_1847_;
}
else
{
uint8_t v___x_1906_; uint32_t v___x_1907_; uint32_t v___x_1908_; uint8_t v___x_1909_; 
v___x_1906_ = lean_byte_array_fget(v_array_1902_, v_idx_1903_);
v___x_1907_ = lean_uint8_to_uint32(v___x_1906_);
v___x_1908_ = 32;
v___x_1909_ = lean_uint32_dec_eq(v___x_1907_, v___x_1908_);
if (v___x_1909_ == 0)
{
uint32_t v___x_1910_; uint8_t v___x_1911_; 
v___x_1910_ = 9;
v___x_1911_ = lean_uint32_dec_eq(v___x_1907_, v___x_1910_);
if (v___x_1911_ == 0)
{
v___y_1848_ = v___y_1876_;
v_pos_1849_ = v_fst_1901_;
goto v___jp_1847_;
}
else
{
lean_dec_ref(v___y_1876_);
v_pos_1719_ = v_fst_1901_;
goto v___jp_1718_;
}
}
else
{
lean_dec_ref(v___y_1876_);
v_pos_1719_ = v_fst_1901_;
goto v___jp_1718_;
}
}
}
else
{
lean_object* v_fst_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1920_; 
lean_dec_ref(v___y_1876_);
v_fst_1912_ = lean_ctor_get(v_snd_1898_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_snd_1898_);
if (v_isSharedCheck_1920_ == 0)
{
lean_object* v_unused_1921_; 
v_unused_1921_ = lean_ctor_get(v_snd_1898_, 1);
lean_dec(v_unused_1921_);
v___x_1914_ = v_snd_1898_;
v_isShared_1915_ = v_isSharedCheck_1920_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_fst_1912_);
lean_dec(v_snd_1898_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1920_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1916_; lean_object* v___x_1918_; 
v___x_1916_ = lean_box(0);
if (v_isShared_1915_ == 0)
{
lean_ctor_set_tag(v___x_1914_, 1);
lean_ctor_set(v___x_1914_, 1, v___x_1916_);
v___x_1918_ = v___x_1914_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_fst_1912_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
}
}
v___jp_1923_:
{
uint32_t v___x_1928_; uint8_t v___x_1929_; 
v___x_1928_ = 97;
v___x_1929_ = lean_uint32_dec_le(v___x_1928_, v___y_1926_);
if (v___x_1929_ == 0)
{
v___y_1876_ = v___y_1924_;
v___y_1877_ = v_fst_1790_;
v_array_1878_ = v___y_1927_;
v_idx_1879_ = v___y_1925_;
goto v___jp_1875_;
}
else
{
uint32_t v___x_1930_; uint8_t v___x_1931_; 
v___x_1930_ = 122;
v___x_1931_ = lean_uint32_dec_le(v___y_1926_, v___x_1930_);
if (v___x_1931_ == 0)
{
v___y_1876_ = v___y_1924_;
v___y_1877_ = v_fst_1790_;
v_array_1878_ = v___y_1927_;
v_idx_1879_ = v___y_1925_;
goto v___jp_1875_;
}
else
{
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_del_object(v___x_1798_);
lean_del_object(v___x_1792_);
v_pos_1715_ = v_fst_1790_;
goto v___jp_1714_;
}
}
}
v___jp_1932_:
{
uint32_t v___x_1937_; uint8_t v___x_1938_; 
v___x_1937_ = 65;
v___x_1938_ = lean_uint32_dec_le(v___x_1937_, v___y_1935_);
if (v___x_1938_ == 0)
{
v___y_1924_ = v___y_1933_;
v___y_1925_ = v___y_1934_;
v___y_1926_ = v___y_1935_;
v___y_1927_ = v___y_1936_;
goto v___jp_1923_;
}
else
{
uint32_t v___x_1939_; uint8_t v___x_1940_; 
v___x_1939_ = 90;
v___x_1940_ = lean_uint32_dec_le(v___y_1935_, v___x_1939_);
if (v___x_1940_ == 0)
{
v___y_1924_ = v___y_1933_;
v___y_1925_ = v___y_1934_;
v___y_1926_ = v___y_1935_;
v___y_1927_ = v___y_1936_;
goto v___jp_1923_;
}
else
{
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_del_object(v___x_1798_);
lean_del_object(v___x_1792_);
v_pos_1715_ = v_fst_1790_;
goto v___jp_1714_;
}
}
}
v___jp_1941_:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; uint8_t v___x_1946_; 
v___x_1944_ = l_ByteArray_toByteSlice(v_array_1795_, v_lower_1942_, v_upper_1943_);
v___x_1945_ = l_ByteSlice_size(v___x_1944_);
v___x_1946_ = lean_nat_dec_eq(v___x_1945_, v_maxHeaderNameLength_1726_);
lean_dec(v___x_1945_);
if (v___x_1946_ == 0)
{
lean_object* v_array_1947_; lean_object* v_idx_1948_; 
v_array_1947_ = lean_ctor_get(v_fst_1790_, 0);
lean_inc_ref(v_array_1947_);
v_idx_1948_ = lean_ctor_get(v_fst_1790_, 1);
lean_inc(v_idx_1948_);
v___y_1876_ = v___x_1944_;
v___y_1877_ = v_fst_1790_;
v_array_1878_ = v_array_1947_;
v_idx_1879_ = v_idx_1948_;
goto v___jp_1875_;
}
else
{
lean_object* v_array_1949_; lean_object* v_idx_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v_array_1949_ = lean_ctor_get(v_fst_1790_, 0);
v_idx_1950_ = lean_ctor_get(v_fst_1790_, 1);
v___x_1951_ = lean_byte_array_size(v_array_1949_);
v___x_1952_ = lean_nat_dec_lt(v_idx_1950_, v___x_1951_);
if (v___x_1952_ == 0)
{
lean_inc(v_idx_1950_);
lean_inc_ref(v_array_1949_);
v___y_1876_ = v___x_1944_;
v___y_1877_ = v_fst_1790_;
v_array_1878_ = v_array_1949_;
v_idx_1879_ = v_idx_1950_;
goto v___jp_1875_;
}
else
{
uint8_t v___x_1953_; uint32_t v___x_1954_; uint32_t v___x_1955_; uint8_t v___x_1956_; 
v___x_1953_ = lean_byte_array_fget(v_array_1949_, v_idx_1950_);
v___x_1954_ = lean_uint8_to_uint32(v___x_1953_);
v___x_1955_ = 33;
v___x_1956_ = lean_uint32_dec_eq(v___x_1954_, v___x_1955_);
if (v___x_1956_ == 0)
{
uint32_t v___x_1957_; uint8_t v___x_1958_; 
v___x_1957_ = 35;
v___x_1958_ = lean_uint32_dec_eq(v___x_1954_, v___x_1957_);
if (v___x_1958_ == 0)
{
uint32_t v___x_1959_; uint8_t v___x_1960_; 
v___x_1959_ = 36;
v___x_1960_ = lean_uint32_dec_eq(v___x_1954_, v___x_1959_);
if (v___x_1960_ == 0)
{
uint32_t v___x_1961_; uint8_t v___x_1962_; 
v___x_1961_ = 37;
v___x_1962_ = lean_uint32_dec_eq(v___x_1954_, v___x_1961_);
if (v___x_1962_ == 0)
{
uint32_t v___x_1963_; uint8_t v___x_1964_; 
v___x_1963_ = 38;
v___x_1964_ = lean_uint32_dec_eq(v___x_1954_, v___x_1963_);
if (v___x_1964_ == 0)
{
uint32_t v___x_1965_; uint8_t v___x_1966_; 
v___x_1965_ = 39;
v___x_1966_ = lean_uint32_dec_eq(v___x_1954_, v___x_1965_);
if (v___x_1966_ == 0)
{
uint32_t v___x_1967_; uint8_t v___x_1968_; 
v___x_1967_ = 42;
v___x_1968_ = lean_uint32_dec_eq(v___x_1954_, v___x_1967_);
if (v___x_1968_ == 0)
{
uint32_t v___x_1969_; uint8_t v___x_1970_; 
v___x_1969_ = 43;
v___x_1970_ = lean_uint32_dec_eq(v___x_1954_, v___x_1969_);
if (v___x_1970_ == 0)
{
uint32_t v___x_1971_; uint8_t v___x_1972_; 
v___x_1971_ = 45;
v___x_1972_ = lean_uint32_dec_eq(v___x_1954_, v___x_1971_);
if (v___x_1972_ == 0)
{
uint32_t v___x_1973_; uint8_t v___x_1974_; 
v___x_1973_ = 46;
v___x_1974_ = lean_uint32_dec_eq(v___x_1954_, v___x_1973_);
if (v___x_1974_ == 0)
{
uint32_t v___x_1975_; uint8_t v___x_1976_; 
v___x_1975_ = 94;
v___x_1976_ = lean_uint32_dec_eq(v___x_1954_, v___x_1975_);
if (v___x_1976_ == 0)
{
uint32_t v___x_1977_; uint8_t v___x_1978_; 
v___x_1977_ = 95;
v___x_1978_ = lean_uint32_dec_eq(v___x_1954_, v___x_1977_);
if (v___x_1978_ == 0)
{
uint32_t v___x_1979_; uint8_t v___x_1980_; 
v___x_1979_ = 96;
v___x_1980_ = lean_uint32_dec_eq(v___x_1954_, v___x_1979_);
if (v___x_1980_ == 0)
{
uint32_t v___x_1981_; uint8_t v___x_1982_; 
v___x_1981_ = 124;
v___x_1982_ = lean_uint32_dec_eq(v___x_1954_, v___x_1981_);
if (v___x_1982_ == 0)
{
uint32_t v___x_1983_; uint8_t v___x_1984_; 
v___x_1983_ = 126;
v___x_1984_ = lean_uint32_dec_eq(v___x_1954_, v___x_1983_);
if (v___x_1984_ == 0)
{
uint32_t v___x_1985_; uint8_t v___x_1986_; 
v___x_1985_ = 48;
v___x_1986_ = lean_uint32_dec_le(v___x_1985_, v___x_1954_);
if (v___x_1986_ == 0)
{
lean_inc_ref(v_array_1949_);
lean_inc(v_idx_1950_);
v___y_1933_ = v___x_1944_;
v___y_1934_ = v_idx_1950_;
v___y_1935_ = v___x_1954_;
v___y_1936_ = v_array_1949_;
goto v___jp_1932_;
}
else
{
uint32_t v___x_1987_; uint8_t v___x_1988_; 
v___x_1987_ = 57;
v___x_1988_ = lean_uint32_dec_le(v___x_1954_, v___x_1987_);
if (v___x_1988_ == 0)
{
lean_inc_ref(v_array_1949_);
lean_inc(v_idx_1950_);
v___y_1933_ = v___x_1944_;
v___y_1934_ = v_idx_1950_;
v___y_1935_ = v___x_1954_;
v___y_1936_ = v_array_1949_;
goto v___jp_1932_;
}
else
{
lean_dec_ref(v___x_1944_);
lean_del_object(v___x_1798_);
lean_del_object(v___x_1792_);
v_pos_1715_ = v_fst_1790_;
goto v___jp_1714_;
}
}
}
else
{
lean_dec_ref(v___x_1944_);
lean_del_object(v___x_1798_);
lean_del_object(v___x_1792_);
v_pos_1715_ = v_fst_1790_;
goto v___jp_1714_;
}
}
else
{
lean_dec_ref(v___x_1944_);
lean_del_object(v___x_1798_);
lean_del_object(v___x_1792_);
v_pos_1715_ = v_fst_1790_;
goto v___jp_1714_;
}
}
else
{
lean_dec_ref(v___x_1944_);
lean_del_object(v___x_1798_);
lean_del_object(v___x_1792_);
v_pos_1715_ = v_fst_1790_;
goto v___jp_1714_;
}
}
else
{
lean_dec_ref(v___x_1944_);
lean_del_object(v___x_1798_);
lean_del_object(v___x_1792_);
v_pos_1715_ = v_fst_1790_;
goto v___jp_1714_;
}
}
else
{
lean_dec_ref(v___x_1944_);
lean_del_object(v___x_1798_);
lean_del_object(v___x_1792_);
v_pos_1715_ = v_fst_1790_;
goto v___jp_1714_;
}
}
else
{
lean_dec_ref(v___x_1944_);
lean_del_object(v___x_1798_);
lean_del_object(v___x_1792_);
v_pos_1715_ = v_fst_1790_;
goto v___jp_1714_;
}
}
else
{
lean_dec_ref(v___x_1944_);
lean_del_object(v___x_1798_);
lean_del_object(v___x_1792_);
v_pos_1715_ = v_fst_1790_;
goto v___jp_1714_;
}
}
else
{
lean_dec_ref(v___x_1944_);
lean_del_object(v___x_1798_);
lean_del_object(v___x_1792_);
v_pos_1715_ = v_fst_1790_;
goto v___jp_1714_;
}
}
else
{
lean_dec_ref(v___x_1944_);
lean_del_object(v___x_1798_);
lean_del_object(v___x_1792_);
v_pos_1715_ = v_fst_1790_;
goto v___jp_1714_;
}
}
else
{
lean_dec_ref(v___x_1944_);
lean_del_object(v___x_1798_);
lean_del_object(v___x_1792_);
v_pos_1715_ = v_fst_1790_;
goto v___jp_1714_;
}
}
else
{
lean_dec_ref(v___x_1944_);
lean_del_object(v___x_1798_);
lean_del_object(v___x_1792_);
v_pos_1715_ = v_fst_1790_;
goto v___jp_1714_;
}
}
else
{
lean_dec_ref(v___x_1944_);
lean_del_object(v___x_1798_);
lean_del_object(v___x_1792_);
v_pos_1715_ = v_fst_1790_;
goto v___jp_1714_;
}
}
else
{
lean_dec_ref(v___x_1944_);
lean_del_object(v___x_1798_);
lean_del_object(v___x_1792_);
v_pos_1715_ = v_fst_1790_;
goto v___jp_1714_;
}
}
else
{
lean_dec_ref(v___x_1944_);
lean_del_object(v___x_1798_);
lean_del_object(v___x_1792_);
v_pos_1715_ = v_fst_1790_;
goto v___jp_1714_;
}
}
else
{
lean_dec_ref(v___x_1944_);
lean_del_object(v___x_1798_);
lean_del_object(v___x_1792_);
v_pos_1715_ = v_fst_1790_;
goto v___jp_1714_;
}
}
}
}
v___jp_1991_:
{
uint8_t v___x_1993_; 
v___x_1993_ = lean_nat_dec_le(v___x_1989_, v___x_1990_);
if (v___x_1993_ == 0)
{
lean_dec(v___x_1989_);
v_lower_1942_ = v___y_1992_;
v_upper_1943_ = v___x_1990_;
goto v___jp_1941_;
}
else
{
v_lower_1942_ = v___y_1992_;
v_upper_1943_ = v___x_1989_;
goto v___jp_1941_;
}
}
}
}
else
{
lean_object* v___x_1996_; lean_object* v___x_1998_; 
lean_dec(v_fst_1790_);
lean_dec(v_fst_1789_);
v___x_1996_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_1793_ == 0)
{
lean_ctor_set_tag(v___x_1792_, 1);
lean_ctor_set(v___x_1792_, 1, v___x_1996_);
lean_ctor_set(v___x_1792_, 0, v_a_1713_);
v___x_1998_ = v___x_1792_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1713_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
else
{
lean_object* v_fst_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2010_; 
lean_dec_ref(v___x_1785_);
lean_dec_ref(v_a_1713_);
v_fst_2002_ = lean_ctor_get(v_snd_1786_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_snd_1786_);
if (v_isSharedCheck_2010_ == 0)
{
lean_object* v_unused_2011_; 
v_unused_2011_ = lean_ctor_get(v_snd_1786_, 1);
lean_dec(v_unused_2011_);
v___x_2004_ = v_snd_1786_;
v_isShared_2005_ = v_isSharedCheck_2010_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_fst_2002_);
lean_dec(v_snd_1786_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2010_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2006_; lean_object* v___x_2008_; 
v___x_2006_ = lean_box(0);
if (v_isShared_2005_ == 0)
{
lean_ctor_set_tag(v___x_2004_, 1);
lean_ctor_set(v___x_2004_, 1, v___x_2006_);
v___x_2008_ = v___x_2004_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_fst_2002_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
v___jp_1714_:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1));
v___x_1717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1717_, 0, v_pos_1715_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
return v___x_1717_;
}
v___jp_1718_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_1721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1721_, 0, v_pos_1719_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
return v___x_1721_;
}
v___jp_1722_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_1725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1725_, 0, v_pos_1723_);
lean_ctor_set(v___x_1725_, 1, v___x_1724_);
return v___x_1725_;
}
v___jp_1731_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1735_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2));
v___x_1736_ = l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go(v___y_1734_, v___x_1730_, v___x_1735_);
lean_dec_ref(v___y_1734_);
v___x_1737_ = lean_string_utf8_byte_size(v___x_1736_);
lean_inc_ref(v___x_1736_);
v___x_1738_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1736_);
lean_ctor_set(v___x_1738_, 1, v___x_1730_);
lean_ctor_set(v___x_1738_, 2, v___x_1737_);
v___x_1739_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(v___x_1738_, v___x_1737_);
lean_dec_ref_known(v___x_1738_, 3);
v___x_1740_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1736_);
lean_ctor_set(v___x_1740_, 1, v___x_1730_);
lean_ctor_set(v___x_1740_, 2, v___x_1739_);
v___x_1741_ = l_String_Slice_toString(v___x_1740_);
lean_dec_ref_known(v___x_1740_, 3);
v___x_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___y_1733_);
lean_ctor_set(v___x_1742_, 1, v___x_1741_);
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___y_1732_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
return v___x_1743_;
}
v___jp_1744_:
{
lean_object* v___x_1748_; 
v___x_1748_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___y_1747_, v___y_1745_);
lean_dec(v___y_1747_);
if (lean_obj_tag(v___x_1748_) == 0)
{
if (lean_obj_tag(v___y_1746_) == 0)
{
lean_object* v_pos_1749_; lean_object* v_res_1750_; lean_object* v___x_1751_; 
v_pos_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_pos_1749_);
v_res_1750_ = lean_ctor_get(v___x_1748_, 1);
lean_inc(v_res_1750_);
lean_dec_ref_known(v___x_1748_, 2);
v___x_1751_ = l_ByteArray_empty;
v___y_1732_ = v_pos_1749_;
v___y_1733_ = v_res_1750_;
v___y_1734_ = v___x_1751_;
goto v___jp_1731_;
}
else
{
lean_object* v_pos_1752_; lean_object* v_res_1753_; lean_object* v_val_1754_; lean_object* v___x_1755_; 
v_pos_1752_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_pos_1752_);
v_res_1753_ = lean_ctor_get(v___x_1748_, 1);
lean_inc(v_res_1753_);
lean_dec_ref_known(v___x_1748_, 2);
v_val_1754_ = lean_ctor_get(v___y_1746_, 0);
lean_inc(v_val_1754_);
lean_dec_ref_known(v___y_1746_, 1);
v___x_1755_ = l_ByteSlice_toByteArray(v_val_1754_);
v___y_1732_ = v_pos_1752_;
v___y_1733_ = v_res_1753_;
v___y_1734_ = v___x_1755_;
goto v___jp_1731_;
}
}
else
{
lean_object* v_pos_1756_; lean_object* v_err_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_dec(v___y_1746_);
v_pos_1756_ = lean_ctor_get(v___x_1748_, 0);
v_err_1757_ = lean_ctor_get(v___x_1748_, 1);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1748_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_err_1757_);
lean_inc(v_pos_1756_);
lean_dec(v___x_1748_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_pos_1756_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v_err_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
v___jp_1765_:
{
lean_object* v___x_1769_; 
v___x_1769_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_checkFieldValueLength(v_limits_1712_, v_res_1768_, v_pos_1767_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_pos_1770_; lean_object* v___x_1771_; uint8_t v___x_1772_; 
v_pos_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_pos_1770_);
lean_dec_ref_known(v___x_1769_, 2);
v___x_1771_ = l_ByteSlice_toByteArray(v___y_1766_);
v___x_1772_ = lean_string_validate_utf8(v___x_1771_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; 
lean_dec_ref(v___x_1771_);
v___x_1773_ = lean_box(0);
v___y_1745_ = v_pos_1770_;
v___y_1746_ = v_res_1768_;
v___y_1747_ = v___x_1773_;
goto v___jp_1744_;
}
else
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = lean_string_from_utf8_unchecked(v___x_1771_);
v___x_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
v___y_1745_ = v_pos_1770_;
v___y_1746_ = v_res_1768_;
v___y_1747_ = v___x_1775_;
goto v___jp_1744_;
}
}
else
{
lean_object* v_pos_1776_; lean_object* v_err_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_dec(v_res_1768_);
lean_dec_ref(v___y_1766_);
v_pos_1776_ = lean_ctor_get(v___x_1769_, 0);
v_err_1777_ = lean_ctor_get(v___x_1769_, 1);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1769_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_err_1777_);
lean_inc(v_pos_1776_);
lean_dec(v___x_1769_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_pos_1776_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_err_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___boxed(lean_object* v_limits_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_2012_, v_a_2013_);
lean_dec_ref(v_limits_2012_);
return v_res_2014_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(lean_object* v_x_2015_, lean_object* v_x_2016_){
_start:
{
if (lean_obj_tag(v_x_2015_) == 0)
{
if (lean_obj_tag(v_x_2016_) == 0)
{
uint8_t v___x_2017_; 
v___x_2017_ = 1;
return v___x_2017_;
}
else
{
uint8_t v___x_2018_; 
v___x_2018_ = 0;
return v___x_2018_;
}
}
else
{
if (lean_obj_tag(v_x_2016_) == 0)
{
uint8_t v___x_2019_; 
v___x_2019_ = 0;
return v___x_2019_;
}
else
{
lean_object* v_val_2020_; lean_object* v_val_2021_; uint8_t v___x_2022_; uint8_t v___x_2023_; uint8_t v___x_2024_; 
v_val_2020_ = lean_ctor_get(v_x_2015_, 0);
v_val_2021_ = lean_ctor_get(v_x_2016_, 0);
v___x_2022_ = lean_unbox(v_val_2020_);
v___x_2023_ = lean_unbox(v_val_2021_);
v___x_2024_ = lean_uint8_dec_eq(v___x_2022_, v___x_2023_);
return v___x_2024_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0___boxed(lean_object* v_x_2025_, lean_object* v_x_2026_){
_start:
{
uint8_t v_res_2027_; lean_object* v_r_2028_; 
v_res_2027_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_x_2025_, v_x_2026_);
lean_dec(v_x_2026_);
lean_dec(v_x_2025_);
v_r_2028_ = lean_box(v_res_2027_);
return v_r_2028_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader(lean_object* v_limits_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v___y_2038_; lean_object* v_pos_2061_; lean_object* v_res_2062_; lean_object* v_array_2100_; lean_object* v_idx_2101_; lean_object* v___x_2102_; uint8_t v___x_2103_; 
v_array_2100_ = lean_ctor_get(v_a_2036_, 0);
v_idx_2101_ = lean_ctor_get(v_a_2036_, 1);
v___x_2102_ = lean_byte_array_size(v_array_2100_);
v___x_2103_ = lean_nat_dec_lt(v_idx_2101_, v___x_2102_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; 
v___x_2104_ = lean_box(0);
v_pos_2061_ = v_a_2036_;
v_res_2062_ = v___x_2104_;
goto v___jp_2060_;
}
else
{
uint8_t v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2105_ = lean_byte_array_fget(v_array_2100_, v_idx_2101_);
v___x_2106_ = lean_box(v___x_2105_);
v___x_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
v_pos_2061_ = v_a_2036_;
v_res_2062_ = v___x_2107_;
goto v___jp_2060_;
}
v___jp_2037_:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2039_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2040_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2039_, v___y_2038_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_pos_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2049_; 
v_pos_2041_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2049_ == 0)
{
lean_object* v_unused_2050_; 
v_unused_2050_ = lean_ctor_get(v___x_2040_, 1);
lean_dec(v_unused_2050_);
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2049_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_pos_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2049_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v___x_2047_; 
v___x_2045_ = lean_box(0);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 1, v___x_2045_);
v___x_2047_ = v___x_2043_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_pos_2041_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
else
{
lean_object* v_pos_2051_; lean_object* v_err_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
v_pos_2051_ = lean_ctor_get(v___x_2040_, 0);
v_err_2052_ = lean_ctor_get(v___x_2040_, 1);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2040_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_err_2052_);
lean_inc(v_pos_2051_);
lean_dec(v___x_2040_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_pos_2051_);
lean_ctor_set(v_reuseFailAlloc_2058_, 1, v_err_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
v___jp_2060_:
{
lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2063_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseSingleHeader___closed__0));
v___x_2064_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_2062_, v___x_2063_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; uint8_t v___x_2066_; 
v___x_2065_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseSingleHeader___closed__1));
v___x_2066_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_2062_, v___x_2065_);
lean_dec(v_res_2062_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; 
v___x_2067_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_2035_, v_pos_2061_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_pos_2068_; lean_object* v_res_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v_pos_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_pos_2068_);
v_res_2069_ = lean_ctor_get(v___x_2067_, 1);
lean_inc(v_res_2069_);
lean_dec_ref_known(v___x_2067_, 2);
v___x_2070_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2071_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2070_, v_pos_2068_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_pos_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2080_; 
v_pos_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2080_ == 0)
{
lean_object* v_unused_2081_; 
v_unused_2081_ = lean_ctor_get(v___x_2071_, 1);
lean_dec(v_unused_2081_);
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2080_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_pos_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2080_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2076_, 0, v_res_2069_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 1, v___x_2076_);
v___x_2078_ = v___x_2074_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_pos_2072_);
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
else
{
lean_object* v_pos_2082_; lean_object* v_err_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec(v_res_2069_);
v_pos_2082_ = lean_ctor_get(v___x_2071_, 0);
v_err_2083_ = lean_ctor_get(v___x_2071_, 1);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2071_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_err_2083_);
lean_inc(v_pos_2082_);
lean_dec(v___x_2071_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_pos_2082_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v_err_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
else
{
lean_object* v_pos_2091_; lean_object* v_err_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
v_pos_2091_ = lean_ctor_get(v___x_2067_, 0);
v_err_2092_ = lean_ctor_get(v___x_2067_, 1);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2067_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_err_2092_);
lean_inc(v_pos_2091_);
lean_dec(v___x_2067_);
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
else
{
v___y_2038_ = v_pos_2061_;
goto v___jp_2037_;
}
}
else
{
lean_dec(v_res_2062_);
v___y_2038_ = v_pos_2061_;
goto v___jp_2037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader___boxed(lean_object* v_limits_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_2108_, v_a_2109_);
lean_dec_ref(v_limits_2108_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseObsFoldContinuation(lean_object* v_limits_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v_pos_2125_; lean_object* v_res_2126_; lean_object* v_pos_2155_; lean_object* v_pos_2159_; lean_object* v_maxHeaderValueLength_2162_; lean_object* v_maxSpaceSequence_2163_; lean_object* v___f_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v_snd_2167_; lean_object* v_snd_2168_; uint8_t v___x_2169_; 
v_maxHeaderValueLength_2162_ = lean_ctor_get(v_limits_2111_, 7);
v_maxSpaceSequence_2163_ = lean_ctor_get(v_limits_2111_, 8);
v___f_2164_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3));
v___x_2165_ = lean_unsigned_to_nat(0u);
v___x_2166_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2164_, v_maxSpaceSequence_2163_, v___x_2165_, v_a_2112_);
v_snd_2167_ = lean_ctor_get(v___x_2166_, 1);
lean_inc(v_snd_2167_);
lean_dec_ref(v___x_2166_);
v_snd_2168_ = lean_ctor_get(v_snd_2167_, 1);
v___x_2169_ = lean_unbox(v_snd_2168_);
if (v___x_2169_ == 0)
{
lean_object* v_fst_2170_; lean_object* v_array_2171_; lean_object* v_idx_2172_; lean_object* v_pos_2174_; lean_object* v_res_2175_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v_lower_2204_; lean_object* v_upper_2205_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___f_2215_; lean_object* v_pos_2217_; lean_object* v___x_2243_; uint8_t v___x_2244_; 
v_fst_2170_ = lean_ctor_get(v_snd_2167_, 0);
lean_inc(v_fst_2170_);
lean_dec(v_snd_2167_);
v_array_2171_ = lean_ctor_get(v_fst_2170_, 0);
v_idx_2172_ = lean_ctor_get(v_fst_2170_, 1);
v___f_2215_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4));
v___x_2243_ = lean_byte_array_size(v_array_2171_);
v___x_2244_ = lean_nat_dec_lt(v_idx_2172_, v___x_2243_);
if (v___x_2244_ == 0)
{
v_pos_2217_ = v_fst_2170_;
goto v___jp_2216_;
}
else
{
uint8_t v___x_2245_; uint32_t v___x_2246_; uint32_t v___x_2247_; uint8_t v___x_2248_; 
v___x_2245_ = lean_byte_array_fget(v_array_2171_, v_idx_2172_);
v___x_2246_ = lean_uint8_to_uint32(v___x_2245_);
v___x_2247_ = 32;
v___x_2248_ = lean_uint32_dec_eq(v___x_2246_, v___x_2247_);
if (v___x_2248_ == 0)
{
uint32_t v___x_2249_; uint8_t v___x_2250_; 
v___x_2249_ = 9;
v___x_2250_ = lean_uint32_dec_eq(v___x_2246_, v___x_2249_);
if (v___x_2250_ == 0)
{
v_pos_2217_ = v_fst_2170_;
goto v___jp_2216_;
}
else
{
v_pos_2159_ = v_fst_2170_;
goto v___jp_2158_;
}
}
else
{
v_pos_2159_ = v_fst_2170_;
goto v___jp_2158_;
}
}
v___jp_2173_:
{
lean_object* v___x_2176_; lean_object* v_snd_2177_; lean_object* v_snd_2178_; uint8_t v___x_2179_; 
v___x_2176_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2164_, v_maxSpaceSequence_2163_, v___x_2165_, v_pos_2174_);
v_snd_2177_ = lean_ctor_get(v___x_2176_, 1);
lean_inc(v_snd_2177_);
lean_dec_ref(v___x_2176_);
v_snd_2178_ = lean_ctor_get(v_snd_2177_, 1);
v___x_2179_ = lean_unbox(v_snd_2178_);
if (v___x_2179_ == 0)
{
lean_object* v_fst_2180_; lean_object* v_array_2181_; lean_object* v_idx_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; 
v_fst_2180_ = lean_ctor_get(v_snd_2177_, 0);
lean_inc(v_fst_2180_);
lean_dec(v_snd_2177_);
v_array_2181_ = lean_ctor_get(v_fst_2180_, 0);
v_idx_2182_ = lean_ctor_get(v_fst_2180_, 1);
v___x_2183_ = lean_byte_array_size(v_array_2181_);
v___x_2184_ = lean_nat_dec_lt(v_idx_2182_, v___x_2183_);
if (v___x_2184_ == 0)
{
v_pos_2125_ = v_fst_2180_;
v_res_2126_ = v_res_2175_;
goto v___jp_2124_;
}
else
{
uint8_t v___x_2185_; uint32_t v___x_2186_; uint32_t v___x_2187_; uint8_t v___x_2188_; 
v___x_2185_ = lean_byte_array_fget(v_array_2181_, v_idx_2182_);
v___x_2186_ = lean_uint8_to_uint32(v___x_2185_);
v___x_2187_ = 32;
v___x_2188_ = lean_uint32_dec_eq(v___x_2186_, v___x_2187_);
if (v___x_2188_ == 0)
{
uint32_t v___x_2189_; uint8_t v___x_2190_; 
v___x_2189_ = 9;
v___x_2190_ = lean_uint32_dec_eq(v___x_2186_, v___x_2189_);
if (v___x_2190_ == 0)
{
v_pos_2125_ = v_fst_2180_;
v_res_2126_ = v_res_2175_;
goto v___jp_2124_;
}
else
{
lean_dec(v_res_2175_);
v_pos_2155_ = v_fst_2180_;
goto v___jp_2154_;
}
}
else
{
lean_dec(v_res_2175_);
v_pos_2155_ = v_fst_2180_;
goto v___jp_2154_;
}
}
}
else
{
lean_object* v_fst_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2199_; 
lean_dec(v_res_2175_);
v_fst_2191_ = lean_ctor_get(v_snd_2177_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_snd_2177_);
if (v_isSharedCheck_2199_ == 0)
{
lean_object* v_unused_2200_; 
v_unused_2200_ = lean_ctor_get(v_snd_2177_, 1);
lean_dec(v_unused_2200_);
v___x_2193_ = v_snd_2177_;
v_isShared_2194_ = v_isSharedCheck_2199_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_fst_2191_);
lean_dec(v_snd_2177_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2199_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2195_ = lean_box(0);
if (v_isShared_2194_ == 0)
{
lean_ctor_set_tag(v___x_2193_, 1);
lean_ctor_set(v___x_2193_, 1, v___x_2195_);
v___x_2197_ = v___x_2193_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_fst_2191_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v___x_2195_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
v___jp_2201_:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = l_ByteArray_toByteSlice(v___y_2203_, v_lower_2204_, v_upper_2205_);
v___x_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
v_pos_2174_ = v___y_2202_;
v_res_2175_ = v___x_2207_;
goto v___jp_2173_;
}
v___jp_2208_:
{
uint8_t v___x_2214_; 
v___x_2214_ = lean_nat_dec_le(v___y_2210_, v___y_2209_);
if (v___x_2214_ == 0)
{
lean_dec(v___y_2210_);
v___y_2202_ = v___y_2212_;
v___y_2203_ = v___y_2211_;
v_lower_2204_ = v___y_2213_;
v_upper_2205_ = v___y_2209_;
goto v___jp_2201_;
}
else
{
lean_dec(v___y_2209_);
v___y_2202_ = v___y_2212_;
v___y_2203_ = v___y_2211_;
v_lower_2204_ = v___y_2213_;
v_upper_2205_ = v___y_2210_;
goto v___jp_2201_;
}
}
v___jp_2216_:
{
lean_object* v___x_2218_; lean_object* v_snd_2219_; lean_object* v_snd_2220_; uint8_t v___x_2221_; 
lean_inc_ref(v_pos_2217_);
v___x_2218_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2215_, v_maxHeaderValueLength_2162_, v___x_2165_, v_pos_2217_);
v_snd_2219_ = lean_ctor_get(v___x_2218_, 1);
lean_inc(v_snd_2219_);
v_snd_2220_ = lean_ctor_get(v_snd_2219_, 1);
v___x_2221_ = lean_unbox(v_snd_2220_);
if (v___x_2221_ == 0)
{
lean_object* v_fst_2222_; lean_object* v_fst_2223_; lean_object* v_array_2224_; lean_object* v_idx_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; uint8_t v___x_2228_; 
v_fst_2222_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_fst_2222_);
lean_dec_ref(v___x_2218_);
v_fst_2223_ = lean_ctor_get(v_snd_2219_, 0);
lean_inc(v_fst_2223_);
lean_dec(v_snd_2219_);
v_array_2224_ = lean_ctor_get(v_pos_2217_, 0);
lean_inc_ref(v_array_2224_);
v_idx_2225_ = lean_ctor_get(v_pos_2217_, 1);
lean_inc(v_idx_2225_);
lean_dec_ref(v_pos_2217_);
v___x_2226_ = lean_nat_add(v_idx_2225_, v_fst_2222_);
lean_dec(v_fst_2222_);
v___x_2227_ = lean_byte_array_size(v_array_2224_);
v___x_2228_ = lean_nat_dec_le(v_idx_2225_, v___x_2165_);
if (v___x_2228_ == 0)
{
v___y_2209_ = v___x_2227_;
v___y_2210_ = v___x_2226_;
v___y_2211_ = v_array_2224_;
v___y_2212_ = v_fst_2223_;
v___y_2213_ = v_idx_2225_;
goto v___jp_2208_;
}
else
{
lean_dec(v_idx_2225_);
v___y_2209_ = v___x_2227_;
v___y_2210_ = v___x_2226_;
v___y_2211_ = v_array_2224_;
v___y_2212_ = v_fst_2223_;
v___y_2213_ = v___x_2165_;
goto v___jp_2208_;
}
}
else
{
lean_object* v_fst_2229_; lean_object* v_idx_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2241_; 
lean_dec_ref(v___x_2218_);
v_fst_2229_ = lean_ctor_get(v_snd_2219_, 0);
lean_inc(v_fst_2229_);
lean_dec(v_snd_2219_);
v_idx_2230_ = lean_ctor_get(v_pos_2217_, 1);
v_isSharedCheck_2241_ = !lean_is_exclusive(v_pos_2217_);
if (v_isSharedCheck_2241_ == 0)
{
lean_object* v_unused_2242_; 
v_unused_2242_ = lean_ctor_get(v_pos_2217_, 0);
lean_dec(v_unused_2242_);
v___x_2232_ = v_pos_2217_;
v_isShared_2233_ = v_isSharedCheck_2241_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_idx_2230_);
lean_dec(v_pos_2217_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2241_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v_idx_2234_; uint8_t v___x_2235_; 
v_idx_2234_ = lean_ctor_get(v_fst_2229_, 1);
v___x_2235_ = lean_nat_dec_eq(v_idx_2230_, v_idx_2234_);
lean_dec(v_idx_2230_);
if (v___x_2235_ == 0)
{
lean_object* v___x_2236_; lean_object* v___x_2238_; 
v___x_2236_ = lean_box(0);
if (v_isShared_2233_ == 0)
{
lean_ctor_set_tag(v___x_2232_, 1);
lean_ctor_set(v___x_2232_, 1, v___x_2236_);
lean_ctor_set(v___x_2232_, 0, v_fst_2229_);
v___x_2238_ = v___x_2232_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_fst_2229_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v___x_2236_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
else
{
lean_object* v___x_2240_; 
lean_del_object(v___x_2232_);
v___x_2240_ = lean_box(0);
v_pos_2174_ = v_fst_2229_;
v_res_2175_ = v___x_2240_;
goto v___jp_2173_;
}
}
}
}
}
else
{
lean_object* v_fst_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2259_; 
v_fst_2251_ = lean_ctor_get(v_snd_2167_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_snd_2167_);
if (v_isSharedCheck_2259_ == 0)
{
lean_object* v_unused_2260_; 
v_unused_2260_ = lean_ctor_get(v_snd_2167_, 1);
lean_dec(v_unused_2260_);
v___x_2253_ = v_snd_2167_;
v_isShared_2254_ = v_isSharedCheck_2259_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_fst_2251_);
lean_dec(v_snd_2167_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2259_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2255_; lean_object* v___x_2257_; 
v___x_2255_ = lean_box(0);
if (v_isShared_2254_ == 0)
{
lean_ctor_set_tag(v___x_2253_, 1);
lean_ctor_set(v___x_2253_, 1, v___x_2255_);
v___x_2257_ = v___x_2253_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_fst_2251_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v___x_2255_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
v___jp_2113_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2116_ = lean_unsigned_to_nat(0u);
v___x_2117_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2));
v___x_2118_ = l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go(v___y_2115_, v___x_2116_, v___x_2117_);
lean_dec_ref(v___y_2115_);
v___x_2119_ = lean_string_utf8_byte_size(v___x_2118_);
v___x_2120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2118_);
lean_ctor_set(v___x_2120_, 1, v___x_2116_);
lean_ctor_set(v___x_2120_, 2, v___x_2119_);
v___x_2121_ = l_String_Slice_trimAscii(v___x_2120_);
v___x_2122_ = l_String_Slice_toString(v___x_2121_);
lean_dec_ref(v___x_2121_);
v___x_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___y_2114_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
return v___x_2123_;
}
v___jp_2124_:
{
lean_object* v___x_2127_; 
v___x_2127_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_checkFieldValueLength(v_limits_2111_, v_res_2126_, v_pos_2125_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_pos_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v_pos_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_pos_2128_);
lean_dec_ref_known(v___x_2127_, 2);
v___x_2129_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2130_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2129_, v_pos_2128_);
if (lean_obj_tag(v___x_2130_) == 0)
{
if (lean_obj_tag(v_res_2126_) == 0)
{
lean_object* v_pos_2131_; lean_object* v___x_2132_; 
v_pos_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_pos_2131_);
lean_dec_ref_known(v___x_2130_, 2);
v___x_2132_ = l_ByteArray_empty;
v___y_2114_ = v_pos_2131_;
v___y_2115_ = v___x_2132_;
goto v___jp_2113_;
}
else
{
lean_object* v_pos_2133_; lean_object* v_val_2134_; lean_object* v___x_2135_; 
v_pos_2133_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_pos_2133_);
lean_dec_ref_known(v___x_2130_, 2);
v_val_2134_ = lean_ctor_get(v_res_2126_, 0);
lean_inc(v_val_2134_);
lean_dec_ref_known(v_res_2126_, 1);
v___x_2135_ = l_ByteSlice_toByteArray(v_val_2134_);
v___y_2114_ = v_pos_2133_;
v___y_2115_ = v___x_2135_;
goto v___jp_2113_;
}
}
else
{
lean_object* v_pos_2136_; lean_object* v_err_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec(v_res_2126_);
v_pos_2136_ = lean_ctor_get(v___x_2130_, 0);
v_err_2137_ = lean_ctor_get(v___x_2130_, 1);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2130_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_err_2137_);
lean_inc(v_pos_2136_);
lean_dec(v___x_2130_);
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
lean_dec(v_res_2126_);
v_pos_2145_ = lean_ctor_get(v___x_2127_, 0);
v_err_2146_ = lean_ctor_get(v___x_2127_, 1);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2127_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_err_2146_);
lean_inc(v_pos_2145_);
lean_dec(v___x_2127_);
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
v___jp_2154_:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2157_, 0, v_pos_2155_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
return v___x_2157_;
}
v___jp_2158_:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2161_, 0, v_pos_2159_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
return v___x_2161_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseObsFoldContinuation___boxed(lean_object* v_limits_2261_, lean_object* v_a_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Std_Http_Protocol_H1_parseObsFoldContinuation(v_limits_2261_, v_a_2262_);
lean_dec_ref(v_limits_2261_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair(lean_object* v_a_2268_){
_start:
{
lean_object* v_array_2269_; lean_object* v_idx_2270_; lean_object* v___x_2271_; uint8_t v___x_2272_; 
v_array_2269_ = lean_ctor_get(v_a_2268_, 0);
v_idx_2270_ = lean_ctor_get(v_a_2268_, 1);
v___x_2271_ = lean_byte_array_size(v_array_2269_);
v___x_2272_ = lean_nat_dec_lt(v_idx_2270_, v___x_2271_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = lean_box(0);
v___x_2274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2274_, 0, v_a_2268_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
return v___x_2274_;
}
else
{
uint8_t v___x_2275_; uint8_t v_got_2276_; uint8_t v___x_2277_; 
v___x_2275_ = 92;
v_got_2276_ = lean_byte_array_fget(v_array_2269_, v_idx_2270_);
v___x_2277_ = lean_uint8_dec_eq(v_got_2276_, v___x_2275_);
if (v___x_2277_ == 0)
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1));
v___x_2279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2279_, 0, v_a_2268_);
lean_ctor_set(v___x_2279_, 1, v___x_2278_);
return v___x_2279_;
}
else
{
lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2313_; 
lean_inc(v_idx_2270_);
lean_inc_ref(v_array_2269_);
v_isSharedCheck_2313_ = !lean_is_exclusive(v_a_2268_);
if (v_isSharedCheck_2313_ == 0)
{
lean_object* v_unused_2314_; lean_object* v_unused_2315_; 
v_unused_2314_ = lean_ctor_get(v_a_2268_, 1);
lean_dec(v_unused_2314_);
v_unused_2315_ = lean_ctor_get(v_a_2268_, 0);
lean_dec(v_unused_2315_);
v___x_2281_ = v_a_2268_;
v_isShared_2282_ = v_isSharedCheck_2313_;
goto v_resetjp_2280_;
}
else
{
lean_dec(v_a_2268_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2313_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; uint8_t v___x_2285_; 
v___x_2283_ = lean_unsigned_to_nat(1u);
v___x_2284_ = lean_nat_add(v_idx_2270_, v___x_2283_);
lean_dec(v_idx_2270_);
v___x_2285_ = lean_nat_dec_lt(v___x_2284_, v___x_2271_);
if (v___x_2285_ == 0)
{
lean_object* v___x_2287_; 
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 1, v___x_2284_);
v___x_2287_ = v___x_2281_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_array_2269_);
lean_ctor_set(v_reuseFailAlloc_2290_, 1, v___x_2284_);
v___x_2287_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = lean_box(0);
v___x_2289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2287_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
return v___x_2289_;
}
}
else
{
uint8_t v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2294_; 
v___x_2291_ = lean_byte_array_fget(v_array_2269_, v___x_2284_);
v___x_2292_ = lean_nat_add(v___x_2284_, v___x_2283_);
lean_dec(v___x_2284_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 1, v___x_2292_);
v___x_2294_ = v___x_2281_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_array_2269_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v___x_2292_);
v___x_2294_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; uint32_t v___x_2297_; uint32_t v___x_2304_; uint8_t v___x_2305_; 
v___x_2295_ = lean_box(v___x_2291_);
lean_inc_ref(v___x_2294_);
v___x_2296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2294_);
lean_ctor_set(v___x_2296_, 1, v___x_2295_);
v___x_2297_ = lean_uint8_to_uint32(v___x_2291_);
v___x_2304_ = 9;
v___x_2305_ = lean_uint32_dec_eq(v___x_2297_, v___x_2304_);
if (v___x_2305_ == 0)
{
uint32_t v___x_2306_; uint8_t v___x_2307_; 
v___x_2306_ = 32;
v___x_2307_ = lean_uint32_dec_eq(v___x_2297_, v___x_2306_);
if (v___x_2307_ == 0)
{
uint32_t v___x_2308_; uint8_t v___x_2309_; 
v___x_2308_ = 33;
v___x_2309_ = lean_uint32_dec_le(v___x_2308_, v___x_2297_);
if (v___x_2309_ == 0)
{
lean_dec_ref_known(v___x_2296_, 2);
goto v___jp_2298_;
}
else
{
uint32_t v___x_2310_; uint8_t v___x_2311_; 
v___x_2310_ = 126;
v___x_2311_ = lean_uint32_dec_le(v___x_2297_, v___x_2310_);
if (v___x_2311_ == 0)
{
lean_dec_ref_known(v___x_2296_, 2);
goto v___jp_2298_;
}
else
{
lean_dec_ref(v___x_2294_);
return v___x_2296_;
}
}
}
else
{
lean_dec_ref(v___x_2294_);
return v___x_2296_;
}
}
else
{
lean_dec_ref(v___x_2294_);
return v___x_2296_;
}
v___jp_2298_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2299_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2));
v___x_2300_ = l_Char_quote(v___x_2297_);
v___x_2301_ = lean_string_append(v___x_2299_, v___x_2300_);
lean_dec_ref(v___x_2300_);
v___x_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
v___x_2303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2294_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
return v___x_2303_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(lean_object* v_maxLength_2320_, lean_object* v_buf_2321_, lean_object* v_length_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v_array_2324_; lean_object* v_idx_2325_; lean_object* v___x_2326_; uint8_t v___x_2327_; 
v_array_2324_ = lean_ctor_get(v_a_2323_, 0);
v_idx_2325_ = lean_ctor_get(v_a_2323_, 1);
v___x_2326_ = lean_byte_array_size(v_array_2324_);
v___x_2327_ = lean_nat_dec_lt(v_idx_2325_, v___x_2326_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
lean_dec(v_length_2322_);
lean_dec_ref(v_buf_2321_);
v___x_2328_ = lean_box(0);
v___x_2329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2329_, 0, v_a_2323_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
return v___x_2329_;
}
else
{
lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2406_; 
lean_inc(v_idx_2325_);
lean_inc_ref(v_array_2324_);
v_isSharedCheck_2406_ = !lean_is_exclusive(v_a_2323_);
if (v_isSharedCheck_2406_ == 0)
{
lean_object* v_unused_2407_; lean_object* v_unused_2408_; 
v_unused_2407_ = lean_ctor_get(v_a_2323_, 1);
lean_dec(v_unused_2407_);
v_unused_2408_ = lean_ctor_get(v_a_2323_, 0);
lean_dec(v_unused_2408_);
v___x_2331_ = v_a_2323_;
v_isShared_2332_ = v_isSharedCheck_2406_;
goto v_resetjp_2330_;
}
else
{
lean_dec(v_a_2323_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2406_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
uint8_t v_c_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v_it_x27_2337_; 
v_c_2333_ = lean_byte_array_fget(v_array_2324_, v_idx_2325_);
v___x_2334_ = lean_unsigned_to_nat(1u);
v___x_2335_ = lean_nat_add(v_idx_2325_, v___x_2334_);
lean_dec(v_idx_2325_);
lean_inc(v___x_2335_);
lean_inc_ref(v_array_2324_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 1, v___x_2335_);
v_it_x27_2337_ = v___x_2331_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_array_2324_);
lean_ctor_set(v_reuseFailAlloc_2405_, 1, v___x_2335_);
v_it_x27_2337_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
uint8_t v___x_2354_; uint8_t v___x_2355_; 
v___x_2354_ = 34;
v___x_2355_ = lean_uint8_dec_eq(v_c_2333_, v___x_2354_);
if (v___x_2355_ == 0)
{
uint8_t v___x_2356_; uint8_t v___x_2357_; 
v___x_2356_ = 92;
v___x_2357_ = lean_uint8_dec_eq(v_c_2333_, v___x_2356_);
if (v___x_2357_ == 0)
{
uint32_t v___x_2358_; uint32_t v___x_2364_; uint8_t v___x_2365_; 
lean_dec(v___x_2335_);
lean_dec_ref(v_array_2324_);
v___x_2358_ = lean_uint8_to_uint32(v_c_2333_);
v___x_2364_ = 9;
v___x_2365_ = lean_uint32_dec_eq(v___x_2358_, v___x_2364_);
if (v___x_2365_ == 0)
{
uint32_t v___x_2366_; uint8_t v___x_2367_; 
v___x_2366_ = 32;
v___x_2367_ = lean_uint32_dec_eq(v___x_2358_, v___x_2366_);
if (v___x_2367_ == 0)
{
uint32_t v___x_2368_; uint8_t v___x_2369_; 
v___x_2368_ = 33;
v___x_2369_ = lean_uint32_dec_eq(v___x_2358_, v___x_2368_);
if (v___x_2369_ == 0)
{
uint32_t v___x_2370_; uint8_t v___x_2371_; 
v___x_2370_ = 35;
v___x_2371_ = lean_uint32_dec_le(v___x_2370_, v___x_2358_);
if (v___x_2371_ == 0)
{
goto v___jp_2359_;
}
else
{
uint32_t v___x_2372_; uint8_t v___x_2373_; 
v___x_2372_ = 91;
v___x_2373_ = lean_uint32_dec_le(v___x_2358_, v___x_2372_);
if (v___x_2373_ == 0)
{
goto v___jp_2359_;
}
else
{
goto v___jp_2338_;
}
}
}
else
{
goto v___jp_2338_;
}
}
else
{
goto v___jp_2338_;
}
}
else
{
goto v___jp_2338_;
}
v___jp_2359_:
{
uint32_t v___x_2360_; uint8_t v___x_2361_; 
v___x_2360_ = 93;
v___x_2361_ = lean_uint32_dec_le(v___x_2360_, v___x_2358_);
if (v___x_2361_ == 0)
{
goto v___jp_2345_;
}
else
{
uint32_t v___x_2362_; uint8_t v___x_2363_; 
v___x_2362_ = 126;
v___x_2363_ = lean_uint32_dec_le(v___x_2358_, v___x_2362_);
if (v___x_2363_ == 0)
{
goto v___jp_2345_;
}
else
{
goto v___jp_2338_;
}
}
}
}
else
{
uint8_t v___x_2374_; 
v___x_2374_ = lean_nat_dec_lt(v___x_2335_, v___x_2326_);
if (v___x_2374_ == 0)
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
lean_dec(v___x_2335_);
lean_dec_ref(v_array_2324_);
lean_dec(v_length_2322_);
lean_dec_ref(v_buf_2321_);
v___x_2375_ = lean_box(0);
v___x_2376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2376_, 0, v_it_x27_2337_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
return v___x_2376_;
}
else
{
uint8_t v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; uint32_t v___x_2387_; uint32_t v___x_2396_; uint8_t v___x_2397_; 
lean_dec_ref(v_it_x27_2337_);
v___x_2377_ = lean_byte_array_fget(v_array_2324_, v___x_2335_);
v___x_2378_ = lean_nat_add(v___x_2335_, v___x_2334_);
lean_dec(v___x_2335_);
v___x_2379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2379_, 0, v_array_2324_);
lean_ctor_set(v___x_2379_, 1, v___x_2378_);
v___x_2387_ = lean_uint8_to_uint32(v___x_2377_);
v___x_2396_ = 9;
v___x_2397_ = lean_uint32_dec_eq(v___x_2387_, v___x_2396_);
if (v___x_2397_ == 0)
{
uint32_t v___x_2398_; uint8_t v___x_2399_; 
v___x_2398_ = 32;
v___x_2399_ = lean_uint32_dec_eq(v___x_2387_, v___x_2398_);
if (v___x_2399_ == 0)
{
uint32_t v___x_2400_; uint8_t v___x_2401_; 
v___x_2400_ = 33;
v___x_2401_ = lean_uint32_dec_le(v___x_2400_, v___x_2387_);
if (v___x_2401_ == 0)
{
goto v___jp_2388_;
}
else
{
uint32_t v___x_2402_; uint8_t v___x_2403_; 
v___x_2402_ = 126;
v___x_2403_ = lean_uint32_dec_le(v___x_2387_, v___x_2402_);
if (v___x_2403_ == 0)
{
goto v___jp_2388_;
}
else
{
goto v___jp_2380_;
}
}
}
else
{
goto v___jp_2380_;
}
}
else
{
goto v___jp_2380_;
}
v___jp_2380_:
{
lean_object* v___x_2381_; uint8_t v___x_2382_; 
v___x_2381_ = lean_nat_add(v_length_2322_, v___x_2334_);
lean_dec(v_length_2322_);
v___x_2382_ = lean_nat_dec_lt(v_maxLength_2320_, v___x_2381_);
if (v___x_2382_ == 0)
{
lean_object* v___x_2383_; 
v___x_2383_ = lean_byte_array_push(v_buf_2321_, v___x_2377_);
v_buf_2321_ = v___x_2383_;
v_length_2322_ = v___x_2381_;
v_a_2323_ = v___x_2379_;
goto _start;
}
else
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
lean_dec(v___x_2381_);
lean_dec_ref(v_buf_2321_);
v___x_2385_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_2386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2379_);
lean_ctor_set(v___x_2386_, 1, v___x_2385_);
return v___x_2386_;
}
}
v___jp_2388_:
{
uint8_t v___x_2389_; uint8_t v___x_2390_; 
v___x_2389_ = 128;
v___x_2390_ = lean_uint8_dec_le(v___x_2389_, v___x_2377_);
if (v___x_2390_ == 0)
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
lean_dec(v_length_2322_);
lean_dec_ref(v_buf_2321_);
v___x_2391_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2));
v___x_2392_ = l_Char_quote(v___x_2387_);
v___x_2393_ = lean_string_append(v___x_2391_, v___x_2392_);
lean_dec_ref(v___x_2392_);
v___x_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
v___x_2395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2379_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
return v___x_2395_;
}
else
{
goto v___jp_2380_;
}
}
}
}
}
else
{
lean_object* v___x_2404_; 
lean_dec(v___x_2335_);
lean_dec_ref(v_array_2324_);
lean_dec(v_length_2322_);
v___x_2404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2404_, 0, v_it_x27_2337_);
lean_ctor_set(v___x_2404_, 1, v_buf_2321_);
return v___x_2404_;
}
v___jp_2338_:
{
lean_object* v___x_2339_; uint8_t v___x_2340_; 
v___x_2339_ = lean_nat_add(v_length_2322_, v___x_2334_);
lean_dec(v_length_2322_);
v___x_2340_ = lean_nat_dec_lt(v_maxLength_2320_, v___x_2339_);
if (v___x_2340_ == 0)
{
lean_object* v___x_2341_; 
v___x_2341_ = lean_byte_array_push(v_buf_2321_, v_c_2333_);
v_buf_2321_ = v___x_2341_;
v_length_2322_ = v___x_2339_;
v_a_2323_ = v_it_x27_2337_;
goto _start;
}
else
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
lean_dec(v___x_2339_);
lean_dec_ref(v_buf_2321_);
v___x_2343_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_2344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2344_, 0, v_it_x27_2337_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
return v___x_2344_;
}
}
v___jp_2345_:
{
uint8_t v___x_2346_; uint8_t v___x_2347_; 
v___x_2346_ = 128;
v___x_2347_ = lean_uint8_dec_le(v___x_2346_, v_c_2333_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; uint32_t v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
lean_dec(v_length_2322_);
lean_dec_ref(v_buf_2321_);
v___x_2348_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2));
v___x_2349_ = lean_uint8_to_uint32(v_c_2333_);
v___x_2350_ = l_Char_quote(v___x_2349_);
v___x_2351_ = lean_string_append(v___x_2348_, v___x_2350_);
lean_dec_ref(v___x_2350_);
v___x_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
v___x_2353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2353_, 0, v_it_x27_2337_);
lean_ctor_set(v___x_2353_, 1, v___x_2352_);
return v___x_2353_;
}
else
{
goto v___jp_2338_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___boxed(lean_object* v_maxLength_2409_, lean_object* v_buf_2410_, lean_object* v_length_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_2409_, v_buf_2410_, v_length_2411_, v_a_2412_);
lean_dec(v_maxLength_2409_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(lean_object* v_maxLength_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v_array_2419_; lean_object* v_idx_2420_; lean_object* v___x_2421_; uint8_t v___x_2422_; 
v_array_2419_ = lean_ctor_get(v_a_2418_, 0);
v_idx_2420_ = lean_ctor_get(v_a_2418_, 1);
v___x_2421_ = lean_byte_array_size(v_array_2419_);
v___x_2422_ = lean_nat_dec_lt(v_idx_2420_, v___x_2421_);
if (v___x_2422_ == 0)
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2423_ = lean_box(0);
v___x_2424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2424_, 0, v_a_2418_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
return v___x_2424_;
}
else
{
uint8_t v___x_2425_; uint8_t v_got_2426_; uint8_t v___x_2427_; 
v___x_2425_ = 34;
v_got_2426_ = lean_byte_array_fget(v_array_2419_, v_idx_2420_);
v___x_2427_ = lean_uint8_dec_eq(v_got_2426_, v___x_2425_);
if (v___x_2427_ == 0)
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1));
v___x_2429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2429_, 0, v_a_2418_);
lean_ctor_set(v___x_2429_, 1, v___x_2428_);
return v___x_2429_;
}
else
{
lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2441_; 
lean_inc(v_idx_2420_);
lean_inc_ref(v_array_2419_);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_a_2418_);
if (v_isSharedCheck_2441_ == 0)
{
lean_object* v_unused_2442_; lean_object* v_unused_2443_; 
v_unused_2442_ = lean_ctor_get(v_a_2418_, 1);
lean_dec(v_unused_2442_);
v_unused_2443_ = lean_ctor_get(v_a_2418_, 0);
lean_dec(v_unused_2443_);
v___x_2431_ = v_a_2418_;
v_isShared_2432_ = v_isSharedCheck_2441_;
goto v_resetjp_2430_;
}
else
{
lean_dec(v_a_2418_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2441_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2436_; 
v___x_2433_ = lean_unsigned_to_nat(1u);
v___x_2434_ = lean_nat_add(v_idx_2420_, v___x_2433_);
lean_dec(v_idx_2420_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 1, v___x_2434_);
v___x_2436_ = v___x_2431_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_array_2419_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2437_ = l_ByteArray_empty;
v___x_2438_ = lean_unsigned_to_nat(0u);
v___x_2439_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_2417_, v___x_2437_, v___x_2438_, v___x_2436_);
return v___x_2439_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___boxed(lean_object* v_maxLength_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxLength_2444_, v_a_2445_);
lean_dec(v_maxLength_2444_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(lean_object* v___f_2447_, lean_object* v_maxSpaceSequence_2448_, lean_object* v_x_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v_pos_2452_; lean_object* v_pos_2456_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v_snd_2461_; lean_object* v_snd_2462_; uint8_t v___x_2463_; 
v___x_2459_ = lean_unsigned_to_nat(0u);
v___x_2460_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2447_, v_maxSpaceSequence_2448_, v___x_2459_, v___y_2450_);
v_snd_2461_ = lean_ctor_get(v___x_2460_, 1);
lean_inc(v_snd_2461_);
lean_dec_ref(v___x_2460_);
v_snd_2462_ = lean_ctor_get(v_snd_2461_, 1);
v___x_2463_ = lean_unbox(v_snd_2462_);
if (v___x_2463_ == 0)
{
lean_object* v_fst_2464_; lean_object* v_array_2465_; lean_object* v_idx_2466_; lean_object* v___x_2467_; uint8_t v___x_2468_; 
v_fst_2464_ = lean_ctor_get(v_snd_2461_, 0);
lean_inc(v_fst_2464_);
lean_dec(v_snd_2461_);
v_array_2465_ = lean_ctor_get(v_fst_2464_, 0);
v_idx_2466_ = lean_ctor_get(v_fst_2464_, 1);
v___x_2467_ = lean_byte_array_size(v_array_2465_);
v___x_2468_ = lean_nat_dec_lt(v_idx_2466_, v___x_2467_);
if (v___x_2468_ == 0)
{
v_pos_2452_ = v_fst_2464_;
goto v___jp_2451_;
}
else
{
uint8_t v___x_2469_; uint32_t v___x_2470_; uint32_t v___x_2471_; uint8_t v___x_2472_; 
v___x_2469_ = lean_byte_array_fget(v_array_2465_, v_idx_2466_);
v___x_2470_ = lean_uint8_to_uint32(v___x_2469_);
v___x_2471_ = 32;
v___x_2472_ = lean_uint32_dec_eq(v___x_2470_, v___x_2471_);
if (v___x_2472_ == 0)
{
uint32_t v___x_2473_; uint8_t v___x_2474_; 
v___x_2473_ = 9;
v___x_2474_ = lean_uint32_dec_eq(v___x_2470_, v___x_2473_);
if (v___x_2474_ == 0)
{
v_pos_2452_ = v_fst_2464_;
goto v___jp_2451_;
}
else
{
v_pos_2456_ = v_fst_2464_;
goto v___jp_2455_;
}
}
else
{
v_pos_2456_ = v_fst_2464_;
goto v___jp_2455_;
}
}
}
else
{
lean_object* v_fst_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2483_; 
v_fst_2475_ = lean_ctor_get(v_snd_2461_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v_snd_2461_);
if (v_isSharedCheck_2483_ == 0)
{
lean_object* v_unused_2484_; 
v_unused_2484_ = lean_ctor_get(v_snd_2461_, 1);
lean_dec(v_unused_2484_);
v___x_2477_ = v_snd_2461_;
v_isShared_2478_ = v_isSharedCheck_2483_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_fst_2475_);
lean_dec(v_snd_2461_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2483_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2479_; lean_object* v___x_2481_; 
v___x_2479_ = lean_box(0);
if (v_isShared_2478_ == 0)
{
lean_ctor_set_tag(v___x_2477_, 1);
lean_ctor_set(v___x_2477_, 1, v___x_2479_);
v___x_2481_ = v___x_2477_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_fst_2475_);
lean_ctor_set(v_reuseFailAlloc_2482_, 1, v___x_2479_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
v___jp_2451_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = lean_box(0);
v___x_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2454_, 0, v_pos_2452_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
return v___x_2454_;
}
v___jp_2455_:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2458_, 0, v_pos_2456_);
lean_ctor_set(v___x_2458_, 1, v___x_2457_);
return v___x_2458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2___boxed(lean_object* v___f_2485_, lean_object* v_maxSpaceSequence_2486_, lean_object* v_x_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_2485_, v_maxSpaceSequence_2486_, v_x_2487_, v___y_2488_);
lean_dec(v_maxSpaceSequence_2486_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(lean_object* v_limits_2502_, lean_object* v_a_2503_){
_start:
{
lean_object* v_pos_2505_; lean_object* v_pos_2509_; lean_object* v___y_2513_; lean_object* v_pos_2514_; lean_object* v___y_2520_; lean_object* v___y_2524_; lean_object* v_pos_2525_; lean_object* v_res_2526_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v_lower_2557_; lean_object* v_upper_2558_; lean_object* v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v_pos_2574_; lean_object* v_maxSpaceSequence_2577_; lean_object* v_maxChunkExtNameLength_2578_; lean_object* v_maxChunkExtValueLength_2579_; lean_object* v___f_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v_snd_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2875_; 
v_maxSpaceSequence_2577_ = lean_ctor_get(v_limits_2502_, 8);
v_maxChunkExtNameLength_2578_ = lean_ctor_get(v_limits_2502_, 11);
v_maxChunkExtValueLength_2579_ = lean_ctor_get(v_limits_2502_, 12);
v___f_2580_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3));
v___x_2581_ = lean_unsigned_to_nat(0u);
v___x_2582_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2580_, v_maxSpaceSequence_2577_, v___x_2581_, v_a_2503_);
v_snd_2583_ = lean_ctor_get(v___x_2582_, 1);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2875_ == 0)
{
lean_object* v_unused_2876_; 
v_unused_2876_ = lean_ctor_get(v___x_2582_, 0);
lean_dec(v_unused_2876_);
v___x_2585_ = v___x_2582_;
v_isShared_2586_ = v_isSharedCheck_2875_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_snd_2583_);
lean_dec(v___x_2582_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2875_;
goto v_resetjp_2584_;
}
v___jp_2504_:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2506_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2507_, 0, v_pos_2505_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
return v___x_2507_;
}
v___jp_2508_:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2511_, 0, v_pos_2509_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
return v___x_2511_;
}
v___jp_2512_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2515_ = lean_box(0);
v___x_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___y_2513_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
v___x_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2516_);
v___x_2518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2518_, 0, v_pos_2514_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
return v___x_2518_;
}
v___jp_2519_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = lean_box(0);
v___x_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___y_2520_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
return v___x_2522_;
}
v___jp_2523_:
{
lean_object* v___x_2527_; 
v___x_2527_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_2526_, v_pos_2525_);
lean_dec(v_res_2526_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_pos_2528_; lean_object* v_res_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2543_; 
v_pos_2528_ = lean_ctor_get(v___x_2527_, 0);
v_res_2529_ = lean_ctor_get(v___x_2527_, 1);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2531_ = v___x_2527_;
v_isShared_2532_ = v_isSharedCheck_2543_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_res_2529_);
lean_inc(v_pos_2528_);
lean_dec(v___x_2527_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2543_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2533_; 
v___x_2533_ = l_Std_Http_Chunk_ExtensionValue_ofString_x3f(v_res_2529_);
if (lean_obj_tag(v___x_2533_) == 1)
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2537_; 
v___x_2534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___y_2524_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
v___x_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2534_);
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 1, v___x_2535_);
v___x_2537_ = v___x_2531_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_pos_2528_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v___x_2535_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
else
{
lean_object* v___x_2539_; lean_object* v___x_2541_; 
lean_dec(v___x_2533_);
lean_dec_ref(v___y_2524_);
v___x_2539_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1));
if (v_isShared_2532_ == 0)
{
lean_ctor_set_tag(v___x_2531_, 1);
lean_ctor_set(v___x_2531_, 1, v___x_2539_);
v___x_2541_ = v___x_2531_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_pos_2528_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v___x_2539_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
else
{
lean_object* v_pos_2544_; lean_object* v_err_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec_ref(v___y_2524_);
v_pos_2544_ = lean_ctor_get(v___x_2527_, 0);
v_err_2545_ = lean_ctor_get(v___x_2527_, 1);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2527_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_err_2545_);
lean_inc(v_pos_2544_);
lean_dec(v___x_2527_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_pos_2544_);
lean_ctor_set(v_reuseFailAlloc_2551_, 1, v_err_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
v___jp_2553_:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; uint8_t v___x_2561_; 
v___x_2559_ = l_ByteArray_toByteSlice(v___y_2555_, v_lower_2557_, v_upper_2558_);
v___x_2560_ = l_ByteSlice_toByteArray(v___x_2559_);
v___x_2561_ = lean_string_validate_utf8(v___x_2560_);
if (v___x_2561_ == 0)
{
lean_object* v___x_2562_; 
lean_dec_ref(v___x_2560_);
v___x_2562_ = lean_box(0);
v___y_2524_ = v___y_2556_;
v_pos_2525_ = v___y_2554_;
v_res_2526_ = v___x_2562_;
goto v___jp_2523_;
}
else
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = lean_string_from_utf8_unchecked(v___x_2560_);
v___x_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2563_);
v___y_2524_ = v___y_2556_;
v_pos_2525_ = v___y_2554_;
v_res_2526_ = v___x_2564_;
goto v___jp_2523_;
}
}
v___jp_2565_:
{
uint8_t v___x_2572_; 
v___x_2572_ = lean_nat_dec_le(v___y_2570_, v___y_2569_);
if (v___x_2572_ == 0)
{
lean_dec(v___y_2570_);
v___y_2554_ = v___y_2567_;
v___y_2555_ = v___y_2566_;
v___y_2556_ = v___y_2568_;
v_lower_2557_ = v___y_2571_;
v_upper_2558_ = v___y_2569_;
goto v___jp_2553_;
}
else
{
lean_dec(v___y_2569_);
v___y_2554_ = v___y_2567_;
v___y_2555_ = v___y_2566_;
v___y_2556_ = v___y_2568_;
v_lower_2557_ = v___y_2571_;
v_upper_2558_ = v___y_2570_;
goto v___jp_2553_;
}
}
v___jp_2573_:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2575_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2576_, 0, v_pos_2574_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
return v___x_2576_;
}
v_resetjp_2584_:
{
lean_object* v_snd_2587_; uint8_t v___x_2588_; 
v_snd_2587_ = lean_ctor_get(v_snd_2583_, 1);
v___x_2588_ = lean_unbox(v_snd_2587_);
if (v___x_2588_ == 0)
{
lean_object* v_fst_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2868_; 
v_fst_2589_ = lean_ctor_get(v_snd_2583_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v_snd_2583_);
if (v_isSharedCheck_2868_ == 0)
{
lean_object* v_unused_2869_; 
v_unused_2869_ = lean_ctor_get(v_snd_2583_, 1);
lean_dec(v_unused_2869_);
v___x_2591_ = v_snd_2583_;
v_isShared_2592_ = v_isSharedCheck_2868_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_fst_2589_);
lean_dec(v_snd_2583_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2868_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v_array_2593_; lean_object* v_idx_2594_; lean_object* v___f_2595_; lean_object* v___y_2597_; lean_object* v_pos_2598_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v_pos_2633_; lean_object* v_array_2634_; lean_object* v_idx_2635_; lean_object* v_pos_2706_; lean_object* v_res_2707_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v_lower_2773_; lean_object* v_upper_2774_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v_pos_2789_; lean_object* v_pos_2822_; lean_object* v___x_2860_; uint8_t v___x_2861_; 
v_array_2593_ = lean_ctor_get(v_fst_2589_, 0);
v_idx_2594_ = lean_ctor_get(v_fst_2589_, 1);
v___f_2595_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_2860_ = lean_byte_array_size(v_array_2593_);
v___x_2861_ = lean_nat_dec_lt(v_idx_2594_, v___x_2860_);
if (v___x_2861_ == 0)
{
lean_inc(v_idx_2594_);
lean_inc_ref(v_array_2593_);
v_pos_2822_ = v_fst_2589_;
goto v___jp_2821_;
}
else
{
uint8_t v___x_2862_; uint32_t v___x_2863_; uint32_t v___x_2864_; uint8_t v___x_2865_; 
v___x_2862_ = lean_byte_array_fget(v_array_2593_, v_idx_2594_);
v___x_2863_ = lean_uint8_to_uint32(v___x_2862_);
v___x_2864_ = 32;
v___x_2865_ = lean_uint32_dec_eq(v___x_2863_, v___x_2864_);
if (v___x_2865_ == 0)
{
uint32_t v___x_2866_; uint8_t v___x_2867_; 
v___x_2866_ = 9;
v___x_2867_ = lean_uint32_dec_eq(v___x_2863_, v___x_2866_);
if (v___x_2867_ == 0)
{
lean_inc(v_idx_2594_);
lean_inc_ref(v_array_2593_);
v_pos_2822_ = v_fst_2589_;
goto v___jp_2821_;
}
else
{
lean_del_object(v___x_2591_);
lean_del_object(v___x_2585_);
v_pos_2505_ = v_fst_2589_;
goto v___jp_2504_;
}
}
else
{
lean_del_object(v___x_2591_);
lean_del_object(v___x_2585_);
v_pos_2505_ = v_fst_2589_;
goto v___jp_2504_;
}
}
v___jp_2596_:
{
lean_object* v___x_2599_; lean_object* v_snd_2600_; lean_object* v_snd_2601_; uint8_t v___x_2602_; 
lean_inc_ref(v_pos_2598_);
v___x_2599_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2595_, v_maxChunkExtValueLength_2579_, v___x_2581_, v_pos_2598_);
v_snd_2600_ = lean_ctor_get(v___x_2599_, 1);
lean_inc(v_snd_2600_);
v_snd_2601_ = lean_ctor_get(v_snd_2600_, 1);
v___x_2602_ = lean_unbox(v_snd_2601_);
if (v___x_2602_ == 0)
{
lean_object* v_fst_2603_; lean_object* v_fst_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2618_; 
v_fst_2603_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_fst_2603_);
lean_dec_ref(v___x_2599_);
v_fst_2604_ = lean_ctor_get(v_snd_2600_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v_snd_2600_);
if (v_isSharedCheck_2618_ == 0)
{
lean_object* v_unused_2619_; 
v_unused_2619_ = lean_ctor_get(v_snd_2600_, 1);
lean_dec(v_unused_2619_);
v___x_2606_ = v_snd_2600_;
v_isShared_2607_ = v_isSharedCheck_2618_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_fst_2604_);
lean_dec(v_snd_2600_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2618_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
uint8_t v___x_2608_; 
v___x_2608_ = lean_nat_dec_eq(v_fst_2603_, v___x_2581_);
if (v___x_2608_ == 0)
{
lean_object* v_array_2609_; lean_object* v_idx_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; uint8_t v___x_2613_; 
lean_del_object(v___x_2606_);
v_array_2609_ = lean_ctor_get(v_pos_2598_, 0);
lean_inc_ref(v_array_2609_);
v_idx_2610_ = lean_ctor_get(v_pos_2598_, 1);
lean_inc(v_idx_2610_);
lean_dec_ref(v_pos_2598_);
v___x_2611_ = lean_nat_add(v_idx_2610_, v_fst_2603_);
lean_dec(v_fst_2603_);
v___x_2612_ = lean_byte_array_size(v_array_2609_);
v___x_2613_ = lean_nat_dec_le(v_idx_2610_, v___x_2581_);
if (v___x_2613_ == 0)
{
v___y_2566_ = v_array_2609_;
v___y_2567_ = v_fst_2604_;
v___y_2568_ = v___y_2597_;
v___y_2569_ = v___x_2612_;
v___y_2570_ = v___x_2611_;
v___y_2571_ = v_idx_2610_;
goto v___jp_2565_;
}
else
{
lean_dec(v_idx_2610_);
v___y_2566_ = v_array_2609_;
v___y_2567_ = v_fst_2604_;
v___y_2568_ = v___y_2597_;
v___y_2569_ = v___x_2612_;
v___y_2570_ = v___x_2611_;
v___y_2571_ = v___x_2581_;
goto v___jp_2565_;
}
}
else
{
lean_object* v___x_2614_; lean_object* v___x_2616_; 
lean_dec(v_fst_2604_);
lean_dec(v_fst_2603_);
lean_dec_ref(v___y_2597_);
v___x_2614_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_2607_ == 0)
{
lean_ctor_set_tag(v___x_2606_, 1);
lean_ctor_set(v___x_2606_, 1, v___x_2614_);
lean_ctor_set(v___x_2606_, 0, v_pos_2598_);
v___x_2616_ = v___x_2606_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_pos_2598_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v___x_2614_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
else
{
lean_object* v_fst_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2628_; 
lean_dec_ref(v___x_2599_);
lean_dec_ref(v_pos_2598_);
lean_dec_ref(v___y_2597_);
v_fst_2620_ = lean_ctor_get(v_snd_2600_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v_snd_2600_);
if (v_isSharedCheck_2628_ == 0)
{
lean_object* v_unused_2629_; 
v_unused_2629_ = lean_ctor_get(v_snd_2600_, 1);
lean_dec(v_unused_2629_);
v___x_2622_ = v_snd_2600_;
v_isShared_2623_ = v_isSharedCheck_2628_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_fst_2620_);
lean_dec(v_snd_2600_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2628_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2624_ = lean_box(0);
if (v_isShared_2623_ == 0)
{
lean_ctor_set_tag(v___x_2622_, 1);
lean_ctor_set(v___x_2622_, 1, v___x_2624_);
v___x_2626_ = v___x_2622_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_fst_2620_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
v___jp_2630_:
{
lean_object* v___x_2636_; uint8_t v___x_2637_; 
v___x_2636_ = lean_byte_array_size(v_array_2634_);
v___x_2637_ = lean_nat_dec_lt(v_idx_2635_, v___x_2636_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; lean_object* v___x_2640_; 
lean_dec(v_idx_2635_);
lean_dec_ref(v_array_2634_);
lean_dec_ref(v___y_2631_);
lean_del_object(v___x_2591_);
v___x_2638_ = lean_box(0);
if (v_isShared_2586_ == 0)
{
lean_ctor_set_tag(v___x_2585_, 1);
lean_ctor_set(v___x_2585_, 1, v___x_2638_);
lean_ctor_set(v___x_2585_, 0, v_pos_2633_);
v___x_2640_ = v___x_2585_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_pos_2633_);
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
uint8_t v___x_2642_; uint8_t v_got_2643_; uint8_t v___x_2644_; 
v___x_2642_ = 61;
v_got_2643_ = lean_byte_array_fget(v_array_2634_, v_idx_2635_);
v___x_2644_ = lean_uint8_dec_eq(v_got_2643_, v___x_2642_);
if (v___x_2644_ == 0)
{
lean_object* v___x_2645_; lean_object* v___x_2647_; 
lean_dec(v_idx_2635_);
lean_dec_ref(v_array_2634_);
lean_dec_ref(v___y_2631_);
lean_del_object(v___x_2591_);
v___x_2645_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3));
if (v_isShared_2586_ == 0)
{
lean_ctor_set_tag(v___x_2585_, 1);
lean_ctor_set(v___x_2585_, 1, v___x_2645_);
lean_ctor_set(v___x_2585_, 0, v_pos_2633_);
v___x_2647_ = v___x_2585_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_pos_2633_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v___x_2645_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
else
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2652_; 
lean_dec_ref(v_pos_2633_);
v___x_2649_ = lean_unsigned_to_nat(1u);
v___x_2650_ = lean_nat_add(v_idx_2635_, v___x_2649_);
lean_dec(v_idx_2635_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 1, v___x_2650_);
lean_ctor_set(v___x_2585_, 0, v_array_2634_);
v___x_2652_ = v___x_2585_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_array_2634_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v___x_2650_);
v___x_2652_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
lean_object* v___x_2653_; 
v___x_2653_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_2580_, v_maxSpaceSequence_2577_, v___y_2632_, v___x_2652_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_pos_2654_; lean_object* v_array_2655_; lean_object* v_idx_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; 
v_pos_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_pos_2654_);
lean_dec_ref_known(v___x_2653_, 2);
v_array_2655_ = lean_ctor_get(v_pos_2654_, 0);
v_idx_2656_ = lean_ctor_get(v_pos_2654_, 1);
v___x_2657_ = lean_byte_array_size(v_array_2655_);
v___x_2658_ = lean_nat_dec_lt(v_idx_2656_, v___x_2657_);
if (v___x_2658_ == 0)
{
lean_del_object(v___x_2591_);
v___y_2597_ = v___y_2631_;
v_pos_2598_ = v_pos_2654_;
goto v___jp_2596_;
}
else
{
uint8_t v___x_2659_; uint8_t v___x_2660_; uint8_t v___x_2661_; 
v___x_2659_ = lean_byte_array_fget(v_array_2655_, v_idx_2656_);
v___x_2660_ = 34;
v___x_2661_ = lean_uint8_dec_eq(v___x_2659_, v___x_2660_);
if (v___x_2661_ == 0)
{
lean_del_object(v___x_2591_);
v___y_2597_ = v___y_2631_;
v_pos_2598_ = v_pos_2654_;
goto v___jp_2596_;
}
else
{
lean_object* v___x_2662_; 
v___x_2662_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxChunkExtValueLength_2579_, v_pos_2654_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_pos_2663_; lean_object* v_res_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2685_; 
v_pos_2663_ = lean_ctor_get(v___x_2662_, 0);
v_res_2664_ = lean_ctor_get(v___x_2662_, 1);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2666_ = v___x_2662_;
v_isShared_2667_ = v_isSharedCheck_2685_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_res_2664_);
lean_inc(v_pos_2663_);
lean_dec(v___x_2662_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2685_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
uint8_t v___x_2668_; 
v___x_2668_ = lean_string_validate_utf8(v_res_2664_);
if (v___x_2668_ == 0)
{
lean_del_object(v___x_2666_);
lean_dec(v_res_2664_);
lean_dec_ref(v___y_2631_);
lean_del_object(v___x_2591_);
v___y_2520_ = v_pos_2663_;
goto v___jp_2519_;
}
else
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2669_ = lean_string_from_utf8_unchecked(v_res_2664_);
v___x_2670_ = l_Std_Http_Chunk_ExtensionValue_ofString_x3f(v___x_2669_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_del_object(v___x_2666_);
lean_dec_ref(v___y_2631_);
lean_del_object(v___x_2591_);
v___y_2520_ = v_pos_2663_;
goto v___jp_2519_;
}
else
{
lean_object* v___x_2672_; 
lean_inc_ref(v___x_2670_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 1, v___x_2670_);
lean_ctor_set(v___x_2591_, 0, v___y_2631_);
v___x_2672_ = v___x_2591_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___y_2631_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2682_; 
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2682_ == 0)
{
lean_object* v_unused_2683_; 
v_unused_2683_ = lean_ctor_get(v___x_2670_, 0);
lean_dec(v_unused_2683_);
v___x_2674_ = v___x_2670_;
v_isShared_2675_ = v_isSharedCheck_2682_;
goto v_resetjp_2673_;
}
else
{
lean_dec(v___x_2670_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2682_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v___x_2672_);
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2672_);
v___x_2677_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
lean_object* v___x_2679_; 
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 1, v___x_2677_);
v___x_2679_ = v___x_2666_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_pos_2663_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v___x_2677_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
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
lean_object* v_pos_2686_; lean_object* v_err_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
lean_dec_ref(v___y_2631_);
lean_del_object(v___x_2591_);
v_pos_2686_ = lean_ctor_get(v___x_2662_, 0);
v_err_2687_ = lean_ctor_get(v___x_2662_, 1);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___x_2662_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_err_2687_);
lean_inc(v_pos_2686_);
lean_dec(v___x_2662_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_pos_2686_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v_err_2687_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
}
}
else
{
lean_object* v_pos_2695_; lean_object* v_err_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_dec_ref(v___y_2631_);
lean_del_object(v___x_2591_);
v_pos_2695_ = lean_ctor_get(v___x_2653_, 0);
v_err_2696_ = lean_ctor_get(v___x_2653_, 1);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2653_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_err_2696_);
lean_inc(v_pos_2695_);
lean_dec(v___x_2653_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_pos_2695_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v_err_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
}
}
}
v___jp_2705_:
{
lean_object* v___x_2708_; 
v___x_2708_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_2707_, v_pos_2706_);
lean_dec(v_res_2707_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v_pos_2709_; lean_object* v_res_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v_pos_2709_ = lean_ctor_get(v___x_2708_, 0);
lean_inc(v_pos_2709_);
v_res_2710_ = lean_ctor_get(v___x_2708_, 1);
lean_inc(v_res_2710_);
lean_dec_ref_known(v___x_2708_, 2);
v___x_2711_ = lean_box(0);
v___x_2712_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_2580_, v_maxSpaceSequence_2577_, v___x_2711_, v_pos_2709_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_pos_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2750_; 
v_pos_2713_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2750_ == 0)
{
lean_object* v_unused_2751_; 
v_unused_2751_ = lean_ctor_get(v___x_2712_, 1);
lean_dec(v_unused_2751_);
v___x_2715_ = v___x_2712_;
v_isShared_2716_ = v_isSharedCheck_2750_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_pos_2713_);
lean_dec(v___x_2712_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2750_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2717_; 
v___x_2717_ = l_Std_Http_Chunk_ExtensionName_ofString_x3f(v_res_2710_);
if (lean_obj_tag(v___x_2717_) == 1)
{
lean_object* v_val_2718_; lean_object* v_array_2719_; lean_object* v_idx_2720_; lean_object* v___x_2721_; uint8_t v___x_2722_; 
v_val_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_val_2718_);
lean_dec_ref_known(v___x_2717_, 1);
v_array_2719_ = lean_ctor_get(v_pos_2713_, 0);
v_idx_2720_ = lean_ctor_get(v_pos_2713_, 1);
v___x_2721_ = lean_byte_array_size(v_array_2719_);
v___x_2722_ = lean_nat_dec_lt(v_idx_2720_, v___x_2721_);
if (v___x_2722_ == 0)
{
lean_del_object(v___x_2715_);
lean_del_object(v___x_2591_);
lean_del_object(v___x_2585_);
v___y_2513_ = v_val_2718_;
v_pos_2514_ = v_pos_2713_;
goto v___jp_2512_;
}
else
{
uint8_t v___x_2723_; uint8_t v___x_2724_; uint8_t v___x_2725_; 
v___x_2723_ = lean_byte_array_fget(v_array_2719_, v_idx_2720_);
v___x_2724_ = 61;
v___x_2725_ = lean_uint8_dec_eq(v___x_2723_, v___x_2724_);
if (v___x_2725_ == 0)
{
lean_del_object(v___x_2715_);
lean_del_object(v___x_2591_);
lean_del_object(v___x_2585_);
v___y_2513_ = v_val_2718_;
v_pos_2514_ = v_pos_2713_;
goto v___jp_2512_;
}
else
{
lean_object* v___x_2726_; lean_object* v_snd_2727_; lean_object* v_snd_2728_; uint8_t v___x_2729_; 
v___x_2726_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2580_, v_maxSpaceSequence_2577_, v___x_2581_, v_pos_2713_);
v_snd_2727_ = lean_ctor_get(v___x_2726_, 1);
lean_inc(v_snd_2727_);
lean_dec_ref(v___x_2726_);
v_snd_2728_ = lean_ctor_get(v_snd_2727_, 1);
v___x_2729_ = lean_unbox(v_snd_2728_);
if (v___x_2729_ == 0)
{
lean_object* v_fst_2730_; lean_object* v_array_2731_; lean_object* v_idx_2732_; lean_object* v___x_2733_; uint8_t v___x_2734_; 
lean_del_object(v___x_2715_);
v_fst_2730_ = lean_ctor_get(v_snd_2727_, 0);
lean_inc(v_fst_2730_);
lean_dec(v_snd_2727_);
v_array_2731_ = lean_ctor_get(v_fst_2730_, 0);
v_idx_2732_ = lean_ctor_get(v_fst_2730_, 1);
v___x_2733_ = lean_byte_array_size(v_array_2731_);
v___x_2734_ = lean_nat_dec_lt(v_idx_2732_, v___x_2733_);
if (v___x_2734_ == 0)
{
lean_inc(v_idx_2732_);
lean_inc_ref(v_array_2731_);
v___y_2631_ = v_val_2718_;
v___y_2632_ = v___x_2711_;
v_pos_2633_ = v_fst_2730_;
v_array_2634_ = v_array_2731_;
v_idx_2635_ = v_idx_2732_;
goto v___jp_2630_;
}
else
{
uint8_t v___x_2735_; uint32_t v___x_2736_; uint32_t v___x_2737_; uint8_t v___x_2738_; 
v___x_2735_ = lean_byte_array_fget(v_array_2731_, v_idx_2732_);
v___x_2736_ = lean_uint8_to_uint32(v___x_2735_);
v___x_2737_ = 32;
v___x_2738_ = lean_uint32_dec_eq(v___x_2736_, v___x_2737_);
if (v___x_2738_ == 0)
{
uint32_t v___x_2739_; uint8_t v___x_2740_; 
v___x_2739_ = 9;
v___x_2740_ = lean_uint32_dec_eq(v___x_2736_, v___x_2739_);
if (v___x_2740_ == 0)
{
lean_inc(v_idx_2732_);
lean_inc_ref(v_array_2731_);
v___y_2631_ = v_val_2718_;
v___y_2632_ = v___x_2711_;
v_pos_2633_ = v_fst_2730_;
v_array_2634_ = v_array_2731_;
v_idx_2635_ = v_idx_2732_;
goto v___jp_2630_;
}
else
{
lean_dec(v_val_2718_);
lean_del_object(v___x_2591_);
lean_del_object(v___x_2585_);
v_pos_2574_ = v_fst_2730_;
goto v___jp_2573_;
}
}
else
{
lean_dec(v_val_2718_);
lean_del_object(v___x_2591_);
lean_del_object(v___x_2585_);
v_pos_2574_ = v_fst_2730_;
goto v___jp_2573_;
}
}
}
else
{
lean_object* v_fst_2741_; lean_object* v___x_2742_; lean_object* v___x_2744_; 
lean_dec(v_val_2718_);
lean_del_object(v___x_2591_);
lean_del_object(v___x_2585_);
v_fst_2741_ = lean_ctor_get(v_snd_2727_, 0);
lean_inc(v_fst_2741_);
lean_dec(v_snd_2727_);
v___x_2742_ = lean_box(0);
if (v_isShared_2716_ == 0)
{
lean_ctor_set_tag(v___x_2715_, 1);
lean_ctor_set(v___x_2715_, 1, v___x_2742_);
lean_ctor_set(v___x_2715_, 0, v_fst_2741_);
v___x_2744_ = v___x_2715_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_fst_2741_);
lean_ctor_set(v_reuseFailAlloc_2745_, 1, v___x_2742_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
}
else
{
lean_object* v___x_2746_; lean_object* v___x_2748_; 
lean_dec(v___x_2717_);
lean_del_object(v___x_2591_);
lean_del_object(v___x_2585_);
v___x_2746_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5));
if (v_isShared_2716_ == 0)
{
lean_ctor_set_tag(v___x_2715_, 1);
lean_ctor_set(v___x_2715_, 1, v___x_2746_);
v___x_2748_ = v___x_2715_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_pos_2713_);
lean_ctor_set(v_reuseFailAlloc_2749_, 1, v___x_2746_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
lean_object* v_pos_2752_; lean_object* v_err_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
lean_dec(v_res_2710_);
lean_del_object(v___x_2591_);
lean_del_object(v___x_2585_);
v_pos_2752_ = lean_ctor_get(v___x_2712_, 0);
v_err_2753_ = lean_ctor_get(v___x_2712_, 1);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2712_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_err_2753_);
lean_inc(v_pos_2752_);
lean_dec(v___x_2712_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_pos_2752_);
lean_ctor_set(v_reuseFailAlloc_2759_, 1, v_err_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
else
{
lean_object* v_pos_2761_; lean_object* v_err_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_del_object(v___x_2591_);
lean_del_object(v___x_2585_);
v_pos_2761_ = lean_ctor_get(v___x_2708_, 0);
v_err_2762_ = lean_ctor_get(v___x_2708_, 1);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2708_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_err_2762_);
lean_inc(v_pos_2761_);
lean_dec(v___x_2708_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_pos_2761_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v_err_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
v___jp_2770_:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; uint8_t v___x_2777_; 
v___x_2775_ = l_ByteArray_toByteSlice(v___y_2771_, v_lower_2773_, v_upper_2774_);
v___x_2776_ = l_ByteSlice_toByteArray(v___x_2775_);
v___x_2777_ = lean_string_validate_utf8(v___x_2776_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2778_; 
lean_dec_ref(v___x_2776_);
v___x_2778_ = lean_box(0);
v_pos_2706_ = v___y_2772_;
v_res_2707_ = v___x_2778_;
goto v___jp_2705_;
}
else
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = lean_string_from_utf8_unchecked(v___x_2776_);
v___x_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2779_);
v_pos_2706_ = v___y_2772_;
v_res_2707_ = v___x_2780_;
goto v___jp_2705_;
}
}
v___jp_2781_:
{
uint8_t v___x_2787_; 
v___x_2787_ = lean_nat_dec_le(v___y_2785_, v___y_2783_);
if (v___x_2787_ == 0)
{
lean_dec(v___y_2785_);
v___y_2771_ = v___y_2782_;
v___y_2772_ = v___y_2784_;
v_lower_2773_ = v___y_2786_;
v_upper_2774_ = v___y_2783_;
goto v___jp_2770_;
}
else
{
lean_dec(v___y_2783_);
v___y_2771_ = v___y_2782_;
v___y_2772_ = v___y_2784_;
v_lower_2773_ = v___y_2786_;
v_upper_2774_ = v___y_2785_;
goto v___jp_2770_;
}
}
v___jp_2788_:
{
lean_object* v___x_2790_; lean_object* v_snd_2791_; lean_object* v_snd_2792_; uint8_t v___x_2793_; 
lean_inc_ref(v_pos_2789_);
v___x_2790_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2595_, v_maxChunkExtNameLength_2578_, v___x_2581_, v_pos_2789_);
v_snd_2791_ = lean_ctor_get(v___x_2790_, 1);
lean_inc(v_snd_2791_);
v_snd_2792_ = lean_ctor_get(v_snd_2791_, 1);
v___x_2793_ = lean_unbox(v_snd_2792_);
if (v___x_2793_ == 0)
{
lean_object* v_fst_2794_; lean_object* v_fst_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2809_; 
v_fst_2794_ = lean_ctor_get(v___x_2790_, 0);
lean_inc(v_fst_2794_);
lean_dec_ref(v___x_2790_);
v_fst_2795_ = lean_ctor_get(v_snd_2791_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v_snd_2791_);
if (v_isSharedCheck_2809_ == 0)
{
lean_object* v_unused_2810_; 
v_unused_2810_ = lean_ctor_get(v_snd_2791_, 1);
lean_dec(v_unused_2810_);
v___x_2797_ = v_snd_2791_;
v_isShared_2798_ = v_isSharedCheck_2809_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_fst_2795_);
lean_dec(v_snd_2791_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2809_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
uint8_t v___x_2799_; 
v___x_2799_ = lean_nat_dec_eq(v_fst_2794_, v___x_2581_);
if (v___x_2799_ == 0)
{
lean_object* v_array_2800_; lean_object* v_idx_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; uint8_t v___x_2804_; 
lean_del_object(v___x_2797_);
v_array_2800_ = lean_ctor_get(v_pos_2789_, 0);
lean_inc_ref(v_array_2800_);
v_idx_2801_ = lean_ctor_get(v_pos_2789_, 1);
lean_inc(v_idx_2801_);
lean_dec_ref(v_pos_2789_);
v___x_2802_ = lean_nat_add(v_idx_2801_, v_fst_2794_);
lean_dec(v_fst_2794_);
v___x_2803_ = lean_byte_array_size(v_array_2800_);
v___x_2804_ = lean_nat_dec_le(v_idx_2801_, v___x_2581_);
if (v___x_2804_ == 0)
{
v___y_2782_ = v_array_2800_;
v___y_2783_ = v___x_2803_;
v___y_2784_ = v_fst_2795_;
v___y_2785_ = v___x_2802_;
v___y_2786_ = v_idx_2801_;
goto v___jp_2781_;
}
else
{
lean_dec(v_idx_2801_);
v___y_2782_ = v_array_2800_;
v___y_2783_ = v___x_2803_;
v___y_2784_ = v_fst_2795_;
v___y_2785_ = v___x_2802_;
v___y_2786_ = v___x_2581_;
goto v___jp_2781_;
}
}
else
{
lean_object* v___x_2805_; lean_object* v___x_2807_; 
lean_dec(v_fst_2795_);
lean_dec(v_fst_2794_);
lean_del_object(v___x_2591_);
lean_del_object(v___x_2585_);
v___x_2805_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_2798_ == 0)
{
lean_ctor_set_tag(v___x_2797_, 1);
lean_ctor_set(v___x_2797_, 1, v___x_2805_);
lean_ctor_set(v___x_2797_, 0, v_pos_2789_);
v___x_2807_ = v___x_2797_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_pos_2789_);
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
}
else
{
lean_object* v_fst_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2819_; 
lean_dec_ref(v___x_2790_);
lean_dec_ref(v_pos_2789_);
lean_del_object(v___x_2591_);
lean_del_object(v___x_2585_);
v_fst_2811_ = lean_ctor_get(v_snd_2791_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v_snd_2791_);
if (v_isSharedCheck_2819_ == 0)
{
lean_object* v_unused_2820_; 
v_unused_2820_ = lean_ctor_get(v_snd_2791_, 1);
lean_dec(v_unused_2820_);
v___x_2813_ = v_snd_2791_;
v_isShared_2814_ = v_isSharedCheck_2819_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_fst_2811_);
lean_dec(v_snd_2791_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2819_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2815_; lean_object* v___x_2817_; 
v___x_2815_ = lean_box(0);
if (v_isShared_2814_ == 0)
{
lean_ctor_set_tag(v___x_2813_, 1);
lean_ctor_set(v___x_2813_, 1, v___x_2815_);
v___x_2817_ = v___x_2813_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_fst_2811_);
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
}
v___jp_2821_:
{
lean_object* v___x_2823_; uint8_t v___x_2824_; 
v___x_2823_ = lean_byte_array_size(v_array_2593_);
v___x_2824_ = lean_nat_dec_lt(v_idx_2594_, v___x_2823_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
lean_dec(v_idx_2594_);
lean_dec_ref(v_array_2593_);
lean_del_object(v___x_2591_);
lean_del_object(v___x_2585_);
v___x_2825_ = lean_box(0);
v___x_2826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2826_, 0, v_pos_2822_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
return v___x_2826_;
}
else
{
uint8_t v___x_2827_; uint8_t v_got_2828_; uint8_t v___x_2829_; 
v___x_2827_ = 59;
v_got_2828_ = lean_byte_array_fget(v_array_2593_, v_idx_2594_);
v___x_2829_ = lean_uint8_dec_eq(v_got_2828_, v___x_2827_);
if (v___x_2829_ == 0)
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
lean_dec(v_idx_2594_);
lean_dec_ref(v_array_2593_);
lean_del_object(v___x_2591_);
lean_del_object(v___x_2585_);
v___x_2830_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7));
v___x_2831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2831_, 0, v_pos_2822_);
lean_ctor_set(v___x_2831_, 1, v___x_2830_);
return v___x_2831_;
}
else
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v_snd_2836_; lean_object* v_snd_2837_; uint8_t v___x_2838_; 
lean_dec_ref(v_pos_2822_);
v___x_2832_ = lean_unsigned_to_nat(1u);
v___x_2833_ = lean_nat_add(v_idx_2594_, v___x_2832_);
lean_dec(v_idx_2594_);
v___x_2834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2834_, 0, v_array_2593_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
v___x_2835_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2580_, v_maxSpaceSequence_2577_, v___x_2581_, v___x_2834_);
v_snd_2836_ = lean_ctor_get(v___x_2835_, 1);
lean_inc(v_snd_2836_);
lean_dec_ref(v___x_2835_);
v_snd_2837_ = lean_ctor_get(v_snd_2836_, 1);
v___x_2838_ = lean_unbox(v_snd_2837_);
if (v___x_2838_ == 0)
{
lean_object* v_fst_2839_; lean_object* v_array_2840_; lean_object* v_idx_2841_; lean_object* v___x_2842_; uint8_t v___x_2843_; 
v_fst_2839_ = lean_ctor_get(v_snd_2836_, 0);
lean_inc(v_fst_2839_);
lean_dec(v_snd_2836_);
v_array_2840_ = lean_ctor_get(v_fst_2839_, 0);
v_idx_2841_ = lean_ctor_get(v_fst_2839_, 1);
v___x_2842_ = lean_byte_array_size(v_array_2840_);
v___x_2843_ = lean_nat_dec_lt(v_idx_2841_, v___x_2842_);
if (v___x_2843_ == 0)
{
v_pos_2789_ = v_fst_2839_;
goto v___jp_2788_;
}
else
{
uint8_t v___x_2844_; uint32_t v___x_2845_; uint32_t v___x_2846_; uint8_t v___x_2847_; 
v___x_2844_ = lean_byte_array_fget(v_array_2840_, v_idx_2841_);
v___x_2845_ = lean_uint8_to_uint32(v___x_2844_);
v___x_2846_ = 32;
v___x_2847_ = lean_uint32_dec_eq(v___x_2845_, v___x_2846_);
if (v___x_2847_ == 0)
{
uint32_t v___x_2848_; uint8_t v___x_2849_; 
v___x_2848_ = 9;
v___x_2849_ = lean_uint32_dec_eq(v___x_2845_, v___x_2848_);
if (v___x_2849_ == 0)
{
v_pos_2789_ = v_fst_2839_;
goto v___jp_2788_;
}
else
{
lean_del_object(v___x_2591_);
lean_del_object(v___x_2585_);
v_pos_2509_ = v_fst_2839_;
goto v___jp_2508_;
}
}
else
{
lean_del_object(v___x_2591_);
lean_del_object(v___x_2585_);
v_pos_2509_ = v_fst_2839_;
goto v___jp_2508_;
}
}
}
else
{
lean_object* v_fst_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2858_; 
lean_del_object(v___x_2591_);
lean_del_object(v___x_2585_);
v_fst_2850_ = lean_ctor_get(v_snd_2836_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v_snd_2836_);
if (v_isSharedCheck_2858_ == 0)
{
lean_object* v_unused_2859_; 
v_unused_2859_ = lean_ctor_get(v_snd_2836_, 1);
lean_dec(v_unused_2859_);
v___x_2852_ = v_snd_2836_;
v_isShared_2853_ = v_isSharedCheck_2858_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_fst_2850_);
lean_dec(v_snd_2836_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2858_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2854_; lean_object* v___x_2856_; 
v___x_2854_ = lean_box(0);
if (v_isShared_2853_ == 0)
{
lean_ctor_set_tag(v___x_2852_, 1);
lean_ctor_set(v___x_2852_, 1, v___x_2854_);
v___x_2856_ = v___x_2852_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_fst_2850_);
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
}
}
}
}
}
else
{
lean_object* v_fst_2870_; lean_object* v___x_2871_; lean_object* v___x_2873_; 
v_fst_2870_ = lean_ctor_get(v_snd_2583_, 0);
lean_inc(v_fst_2870_);
lean_dec(v_snd_2583_);
v___x_2871_ = lean_box(0);
if (v_isShared_2586_ == 0)
{
lean_ctor_set_tag(v___x_2585_, 1);
lean_ctor_set(v___x_2585_, 1, v___x_2871_);
lean_ctor_set(v___x_2585_, 0, v_fst_2870_);
v___x_2873_ = v___x_2585_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_fst_2870_);
lean_ctor_set(v_reuseFailAlloc_2874_, 1, v___x_2871_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___boxed(lean_object* v_limits_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_2877_, v_a_2878_);
lean_dec_ref(v_limits_2877_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0(lean_object* v_limits_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v___x_2882_; 
v___x_2882_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_2880_, v___y_2881_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_pos_2883_; lean_object* v_res_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2892_; 
v_pos_2883_ = lean_ctor_get(v___x_2882_, 0);
v_res_2884_ = lean_ctor_get(v___x_2882_, 1);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2886_ = v___x_2882_;
v_isShared_2887_ = v_isSharedCheck_2892_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_res_2884_);
lean_inc(v_pos_2883_);
lean_dec(v___x_2882_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2892_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2888_; lean_object* v___x_2890_; 
v___x_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2888_, 0, v_res_2884_);
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 1, v___x_2888_);
v___x_2890_ = v___x_2886_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_pos_2883_);
lean_ctor_set(v_reuseFailAlloc_2891_, 1, v___x_2888_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
else
{
lean_object* v_pos_2893_; lean_object* v_err_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
v_pos_2893_ = lean_ctor_get(v___x_2882_, 0);
v_err_2894_ = lean_ctor_get(v___x_2882_, 1);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2882_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_err_2894_);
lean_inc(v_pos_2893_);
lean_dec(v___x_2882_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_pos_2893_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v_err_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed(lean_object* v_limits_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Std_Http_Protocol_H1_parseChunkSize___lam__0(v_limits_2902_, v___y_2903_);
lean_dec_ref(v_limits_2902_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0_spec__0(lean_object* v_as_2905_, size_t v_i_2906_, size_t v_stop_2907_, lean_object* v_b_2908_){
_start:
{
lean_object* v___y_2910_; uint8_t v___x_2914_; 
v___x_2914_ = lean_usize_dec_eq(v_i_2906_, v_stop_2907_);
if (v___x_2914_ == 0)
{
lean_object* v___x_2915_; 
v___x_2915_ = lean_array_uget_borrowed(v_as_2905_, v_i_2906_);
if (lean_obj_tag(v___x_2915_) == 0)
{
v___y_2910_ = v_b_2908_;
goto v___jp_2909_;
}
else
{
lean_object* v_val_2916_; lean_object* v___x_2917_; 
v_val_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_val_2916_);
v___x_2917_ = lean_array_push(v_b_2908_, v_val_2916_);
v___y_2910_ = v___x_2917_;
goto v___jp_2909_;
}
}
else
{
return v_b_2908_;
}
v___jp_2909_:
{
size_t v___x_2911_; size_t v___x_2912_; 
v___x_2911_ = ((size_t)1ULL);
v___x_2912_ = lean_usize_add(v_i_2906_, v___x_2911_);
v_i_2906_ = v___x_2912_;
v_b_2908_ = v___y_2910_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0_spec__0___boxed(lean_object* v_as_2918_, lean_object* v_i_2919_, lean_object* v_stop_2920_, lean_object* v_b_2921_){
_start:
{
size_t v_i_boxed_2922_; size_t v_stop_boxed_2923_; lean_object* v_res_2924_; 
v_i_boxed_2922_ = lean_unbox_usize(v_i_2919_);
lean_dec(v_i_2919_);
v_stop_boxed_2923_ = lean_unbox_usize(v_stop_2920_);
lean_dec(v_stop_2920_);
v_res_2924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0_spec__0(v_as_2918_, v_i_boxed_2922_, v_stop_boxed_2923_, v_b_2921_);
lean_dec_ref(v_as_2918_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0(lean_object* v_as_2927_, lean_object* v_start_2928_, lean_object* v_stop_2929_){
_start:
{
lean_object* v___x_2930_; uint8_t v___x_2931_; 
v___x_2930_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0___closed__0));
v___x_2931_ = lean_nat_dec_lt(v_start_2928_, v_stop_2929_);
if (v___x_2931_ == 0)
{
return v___x_2930_;
}
else
{
lean_object* v___x_2932_; uint8_t v___x_2933_; 
v___x_2932_ = lean_array_get_size(v_as_2927_);
v___x_2933_ = lean_nat_dec_le(v_stop_2929_, v___x_2932_);
if (v___x_2933_ == 0)
{
uint8_t v___x_2934_; 
v___x_2934_ = lean_nat_dec_lt(v_start_2928_, v___x_2932_);
if (v___x_2934_ == 0)
{
return v___x_2930_;
}
else
{
size_t v___x_2935_; size_t v___x_2936_; lean_object* v___x_2937_; 
v___x_2935_ = lean_usize_of_nat(v_start_2928_);
v___x_2936_ = lean_usize_of_nat(v___x_2932_);
v___x_2937_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0_spec__0(v_as_2927_, v___x_2935_, v___x_2936_, v___x_2930_);
return v___x_2937_;
}
}
else
{
size_t v___x_2938_; size_t v___x_2939_; lean_object* v___x_2940_; 
v___x_2938_ = lean_usize_of_nat(v_start_2928_);
v___x_2939_ = lean_usize_of_nat(v_stop_2929_);
v___x_2940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0_spec__0(v_as_2927_, v___x_2938_, v___x_2939_, v___x_2930_);
return v___x_2940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0___boxed(lean_object* v_as_2941_, lean_object* v_start_2942_, lean_object* v_stop_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0(v_as_2941_, v_start_2942_, v_stop_2943_);
lean_dec(v_stop_2943_);
lean_dec(v_start_2942_);
lean_dec_ref(v_as_2941_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize(lean_object* v_limits_2945_, lean_object* v_a_2946_){
_start:
{
lean_object* v___x_2947_; 
v___x_2947_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(v_a_2946_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_pos_2948_; lean_object* v_res_2949_; lean_object* v_maxChunkExtensions_2950_; lean_object* v___f_2951_; lean_object* v___x_2952_; 
v_pos_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_pos_2948_);
v_res_2949_ = lean_ctor_get(v___x_2947_, 1);
lean_inc(v_res_2949_);
lean_dec_ref_known(v___x_2947_, 2);
v_maxChunkExtensions_2950_ = lean_ctor_get(v_limits_2945_, 10);
lean_inc(v_maxChunkExtensions_2950_);
v___f_2951_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2951_, 0, v_limits_2945_);
v___x_2952_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___f_2951_, v_maxChunkExtensions_2950_, v_pos_2948_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_pos_2953_; lean_object* v_res_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v_pos_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_pos_2953_);
v_res_2954_ = lean_ctor_get(v___x_2952_, 1);
lean_inc(v_res_2954_);
lean_dec_ref_known(v___x_2952_, 2);
v___x_2955_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2956_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2955_, v_pos_2953_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_pos_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2968_; 
v_pos_2957_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2968_ == 0)
{
lean_object* v_unused_2969_; 
v_unused_2969_ = lean_ctor_get(v___x_2956_, 1);
lean_dec(v_unused_2969_);
v___x_2959_ = v___x_2956_;
v_isShared_2960_ = v_isSharedCheck_2968_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_pos_2957_);
lean_dec(v___x_2956_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2968_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2966_; 
v___x_2961_ = lean_unsigned_to_nat(0u);
v___x_2962_ = lean_array_get_size(v_res_2954_);
v___x_2963_ = l_Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0(v_res_2954_, v___x_2961_, v___x_2962_);
lean_dec(v_res_2954_);
v___x_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2964_, 0, v_res_2949_);
lean_ctor_set(v___x_2964_, 1, v___x_2963_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 1, v___x_2964_);
v___x_2966_ = v___x_2959_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_pos_2957_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v___x_2964_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
else
{
lean_object* v_pos_2970_; lean_object* v_err_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
lean_dec(v_res_2954_);
lean_dec(v_res_2949_);
v_pos_2970_ = lean_ctor_get(v___x_2956_, 0);
v_err_2971_ = lean_ctor_get(v___x_2956_, 1);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2956_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_err_2971_);
lean_inc(v_pos_2970_);
lean_dec(v___x_2956_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_pos_2970_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v_err_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
else
{
lean_object* v_pos_2979_; lean_object* v_err_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
lean_dec(v_res_2949_);
v_pos_2979_ = lean_ctor_get(v___x_2952_, 0);
v_err_2980_ = lean_ctor_get(v___x_2952_, 1);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2982_ = v___x_2952_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_err_2980_);
lean_inc(v_pos_2979_);
lean_dec(v___x_2952_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_pos_2979_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_err_2980_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
else
{
lean_object* v_pos_2988_; lean_object* v_err_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec_ref(v_limits_2945_);
v_pos_2988_ = lean_ctor_get(v___x_2947_, 0);
v_err_2989_ = lean_ctor_get(v___x_2947_, 1);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2947_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_err_2989_);
lean_inc(v_pos_2988_);
lean_dec(v___x_2947_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_pos_2988_);
lean_ctor_set(v_reuseFailAlloc_2995_, 1, v_err_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl(lean_object* v_x_2997_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = lean_obj_tag_nat(v_x_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl___boxed(lean_object* v_x_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl(v_x_2999_);
lean_dec_ref(v_x_2999_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(lean_object* v_t_3001_, lean_object* v_k_3002_){
_start:
{
if (lean_obj_tag(v_t_3001_) == 0)
{
lean_object* v_data_3003_; lean_object* v___x_3004_; 
v_data_3003_ = lean_ctor_get(v_t_3001_, 0);
lean_inc_ref(v_data_3003_);
lean_dec_ref_known(v_t_3001_, 1);
v___x_3004_ = lean_apply_1(v_k_3002_, v_data_3003_);
return v___x_3004_;
}
else
{
lean_object* v_data_3005_; lean_object* v_remaining_3006_; lean_object* v___x_3007_; 
v_data_3005_ = lean_ctor_get(v_t_3001_, 0);
lean_inc_ref(v_data_3005_);
v_remaining_3006_ = lean_ctor_get(v_t_3001_, 1);
lean_inc(v_remaining_3006_);
lean_dec_ref_known(v_t_3001_, 2);
v___x_3007_ = lean_apply_2(v_k_3002_, v_data_3005_, v_remaining_3006_);
return v___x_3007_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim(lean_object* v_motive_3008_, lean_object* v_ctorIdx_3009_, lean_object* v_t_3010_, lean_object* v_h_3011_, lean_object* v_k_3012_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3010_, v_k_3012_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___boxed(lean_object* v_motive_3014_, lean_object* v_ctorIdx_3015_, lean_object* v_t_3016_, lean_object* v_h_3017_, lean_object* v_k_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim(v_motive_3014_, v_ctorIdx_3015_, v_t_3016_, v_h_3017_, v_k_3018_);
lean_dec(v_ctorIdx_3015_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim___redArg(lean_object* v_t_3020_, lean_object* v_complete_3021_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3020_, v_complete_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim(lean_object* v_motive_3023_, lean_object* v_t_3024_, lean_object* v_h_3025_, lean_object* v_complete_3026_){
_start:
{
lean_object* v___x_3027_; 
v___x_3027_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3024_, v_complete_3026_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim___redArg(lean_object* v_t_3028_, lean_object* v_incomplete_3029_){
_start:
{
lean_object* v___x_3030_; 
v___x_3030_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3028_, v_incomplete_3029_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim(lean_object* v_motive_3031_, lean_object* v_t_3032_, lean_object* v_h_3033_, lean_object* v_incomplete_3034_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3032_, v_incomplete_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkPartial(lean_object* v_limits_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v___x_3038_; 
v___x_3038_ = l_Std_Http_Protocol_H1_parseChunkSize(v_limits_3036_, v_a_3037_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_res_3039_; lean_object* v_pos_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3080_; 
v_res_3039_ = lean_ctor_get(v___x_3038_, 1);
v_pos_3040_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3042_ = v___x_3038_;
v_isShared_3043_ = v_isSharedCheck_3080_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_res_3039_);
lean_inc(v_pos_3040_);
lean_dec(v___x_3038_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3080_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v_fst_3044_; lean_object* v_snd_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3079_; 
v_fst_3044_ = lean_ctor_get(v_res_3039_, 0);
v_snd_3045_ = lean_ctor_get(v_res_3039_, 1);
v_isSharedCheck_3079_ = !lean_is_exclusive(v_res_3039_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3047_ = v_res_3039_;
v_isShared_3048_ = v_isSharedCheck_3079_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_snd_3045_);
lean_inc(v_fst_3044_);
lean_dec(v_res_3039_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3079_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3049_; uint8_t v___x_3050_; 
v___x_3049_ = lean_unsigned_to_nat(0u);
v___x_3050_ = lean_nat_dec_eq(v_fst_3044_, v___x_3049_);
if (v___x_3050_ == 0)
{
lean_object* v___x_3051_; 
lean_del_object(v___x_3042_);
v___x_3051_ = l_Std_Internal_Parsec_ByteArray_take(v_fst_3044_, v_pos_3040_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v_pos_3052_; lean_object* v_res_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3065_; 
v_pos_3052_ = lean_ctor_get(v___x_3051_, 0);
v_res_3053_ = lean_ctor_get(v___x_3051_, 1);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3055_ = v___x_3051_;
v_isShared_3056_ = v_isSharedCheck_3065_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_res_3053_);
lean_inc(v_pos_3052_);
lean_dec(v___x_3051_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3065_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 1, v_res_3053_);
lean_ctor_set(v___x_3047_, 0, v_snd_3045_);
v___x_3058_ = v___x_3047_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_snd_3045_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v_res_3053_);
v___x_3058_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3062_; 
v___x_3059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3059_, 0, v_fst_3044_);
lean_ctor_set(v___x_3059_, 1, v___x_3058_);
v___x_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3059_);
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 1, v___x_3060_);
v___x_3062_ = v___x_3055_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_pos_3052_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v___x_3060_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
}
else
{
lean_object* v_pos_3066_; lean_object* v_err_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_del_object(v___x_3047_);
lean_dec(v_snd_3045_);
lean_dec(v_fst_3044_);
v_pos_3066_ = lean_ctor_get(v___x_3051_, 0);
v_err_3067_ = lean_ctor_get(v___x_3051_, 1);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_3051_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_err_3067_);
lean_inc(v_pos_3066_);
lean_dec(v___x_3051_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_pos_3066_);
lean_ctor_set(v_reuseFailAlloc_3073_, 1, v_err_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
else
{
lean_object* v___x_3075_; lean_object* v___x_3077_; 
lean_del_object(v___x_3047_);
lean_dec(v_snd_3045_);
lean_dec(v_fst_3044_);
v___x_3075_ = lean_box(0);
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 1, v___x_3075_);
v___x_3077_ = v___x_3042_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_pos_3040_);
lean_ctor_set(v_reuseFailAlloc_3078_, 1, v___x_3075_);
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
else
{
lean_object* v_pos_3081_; lean_object* v_err_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3089_; 
v_pos_3081_ = lean_ctor_get(v___x_3038_, 0);
v_err_3082_ = lean_ctor_get(v___x_3038_, 1);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3084_ = v___x_3038_;
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_err_3082_);
lean_inc(v_pos_3081_);
lean_dec(v___x_3038_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3087_; 
if (v_isShared_3085_ == 0)
{
v___x_3087_ = v___x_3084_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_pos_3081_);
lean_ctor_set(v_reuseFailAlloc_3088_, 1, v_err_3082_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData(lean_object* v_size_3090_, lean_object* v_it_3091_){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; uint8_t v___x_3094_; 
v___x_3092_ = l_ByteArray_Iterator_remainingBytes(v_it_3091_);
v___x_3093_ = lean_unsigned_to_nat(0u);
v___x_3094_ = lean_nat_dec_eq(v___x_3092_, v___x_3093_);
if (v___x_3094_ == 0)
{
uint8_t v___x_3095_; 
v___x_3095_ = lean_nat_dec_lt(v___x_3092_, v_size_3090_);
if (v___x_3095_ == 0)
{
lean_object* v_array_3096_; lean_object* v_idx_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3116_; 
lean_dec(v___x_3092_);
v_array_3096_ = lean_ctor_get(v_it_3091_, 0);
v_idx_3097_ = lean_ctor_get(v_it_3091_, 1);
v_isSharedCheck_3116_ = !lean_is_exclusive(v_it_3091_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3099_ = v_it_3091_;
v_isShared_3100_ = v_isSharedCheck_3116_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_idx_3097_);
lean_inc(v_array_3096_);
lean_dec(v_it_3091_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3116_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3101_; lean_object* v___x_3103_; 
v___x_3101_ = lean_nat_add(v_idx_3097_, v_size_3090_);
lean_inc(v___x_3101_);
lean_inc_ref(v_array_3096_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 1, v___x_3101_);
v___x_3103_ = v___x_3099_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_array_3096_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v___x_3101_);
v___x_3103_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
lean_object* v_lower_3105_; lean_object* v_upper_3106_; lean_object* v___x_3110_; lean_object* v___y_3112_; uint8_t v___x_3114_; 
v___x_3110_ = lean_byte_array_size(v_array_3096_);
v___x_3114_ = lean_nat_dec_le(v_idx_3097_, v___x_3093_);
if (v___x_3114_ == 0)
{
v___y_3112_ = v_idx_3097_;
goto v___jp_3111_;
}
else
{
lean_dec(v_idx_3097_);
v___y_3112_ = v___x_3093_;
goto v___jp_3111_;
}
v___jp_3104_:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3107_ = l_ByteArray_toByteSlice(v_array_3096_, v_lower_3105_, v_upper_3106_);
v___x_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
v___x_3109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3103_);
lean_ctor_set(v___x_3109_, 1, v___x_3108_);
return v___x_3109_;
}
v___jp_3111_:
{
uint8_t v___x_3113_; 
v___x_3113_ = lean_nat_dec_le(v___x_3101_, v___x_3110_);
if (v___x_3113_ == 0)
{
lean_dec(v___x_3101_);
v_lower_3105_ = v___y_3112_;
v_upper_3106_ = v___x_3110_;
goto v___jp_3104_;
}
else
{
v_lower_3105_ = v___y_3112_;
v_upper_3106_ = v___x_3101_;
goto v___jp_3104_;
}
}
}
}
}
else
{
lean_object* v_array_3117_; lean_object* v_idx_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3138_; 
v_array_3117_ = lean_ctor_get(v_it_3091_, 0);
v_idx_3118_ = lean_ctor_get(v_it_3091_, 1);
v_isSharedCheck_3138_ = !lean_is_exclusive(v_it_3091_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3120_ = v_it_3091_;
v_isShared_3121_ = v_isSharedCheck_3138_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_idx_3118_);
lean_inc(v_array_3117_);
lean_dec(v_it_3091_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3138_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3122_; lean_object* v___x_3124_; 
v___x_3122_ = lean_nat_add(v_idx_3118_, v___x_3092_);
lean_inc(v___x_3122_);
lean_inc_ref(v_array_3117_);
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 1, v___x_3122_);
v___x_3124_ = v___x_3120_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_array_3117_);
lean_ctor_set(v_reuseFailAlloc_3137_, 1, v___x_3122_);
v___x_3124_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
lean_object* v_lower_3126_; lean_object* v_upper_3127_; lean_object* v___x_3132_; lean_object* v___y_3134_; uint8_t v___x_3136_; 
v___x_3132_ = lean_byte_array_size(v_array_3117_);
v___x_3136_ = lean_nat_dec_le(v_idx_3118_, v___x_3093_);
if (v___x_3136_ == 0)
{
v___y_3134_ = v_idx_3118_;
goto v___jp_3133_;
}
else
{
lean_dec(v_idx_3118_);
v___y_3134_ = v___x_3093_;
goto v___jp_3133_;
}
v___jp_3125_:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3128_ = l_ByteArray_toByteSlice(v_array_3117_, v_lower_3126_, v_upper_3127_);
v___x_3129_ = lean_nat_sub(v_size_3090_, v___x_3092_);
lean_dec(v___x_3092_);
v___x_3130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3128_);
lean_ctor_set(v___x_3130_, 1, v___x_3129_);
v___x_3131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3124_);
lean_ctor_set(v___x_3131_, 1, v___x_3130_);
return v___x_3131_;
}
v___jp_3133_:
{
uint8_t v___x_3135_; 
v___x_3135_ = lean_nat_dec_le(v___x_3122_, v___x_3132_);
if (v___x_3135_ == 0)
{
lean_dec(v___x_3122_);
v_lower_3126_ = v___y_3134_;
v_upper_3127_ = v___x_3132_;
goto v___jp_3125_;
}
else
{
v_lower_3126_ = v___y_3134_;
v_upper_3127_ = v___x_3122_;
goto v___jp_3125_;
}
}
}
}
}
}
else
{
lean_object* v___x_3139_; lean_object* v___x_3140_; 
lean_dec(v___x_3092_);
v___x_3139_ = lean_box(0);
v___x_3140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3140_, 0, v_it_3091_);
lean_ctor_set(v___x_3140_, 1, v___x_3139_);
return v___x_3140_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData___boxed(lean_object* v_size_3141_, lean_object* v_it_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_3141_, v_it_3142_);
lean_dec(v_size_3141_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData(lean_object* v_size_3144_, lean_object* v_a_3145_){
_start:
{
lean_object* v___x_3146_; 
v___x_3146_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_3144_, v_a_3145_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_res_3147_; 
v_res_3147_ = lean_ctor_get(v___x_3146_, 1);
if (lean_obj_tag(v_res_3147_) == 0)
{
lean_object* v_pos_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
lean_inc_ref(v_res_3147_);
v_pos_3148_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_pos_3148_);
lean_dec_ref_known(v___x_3146_, 2);
v___x_3149_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3150_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3149_, v_pos_3148_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v_pos_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3158_; 
v_pos_3151_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3158_ == 0)
{
lean_object* v_unused_3159_; 
v_unused_3159_ = lean_ctor_get(v___x_3150_, 1);
lean_dec(v_unused_3159_);
v___x_3153_ = v___x_3150_;
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_pos_3151_);
lean_dec(v___x_3150_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3156_; 
if (v_isShared_3154_ == 0)
{
lean_ctor_set(v___x_3153_, 1, v_res_3147_);
v___x_3156_ = v___x_3153_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_pos_3151_);
lean_ctor_set(v_reuseFailAlloc_3157_, 1, v_res_3147_);
v___x_3156_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
return v___x_3156_;
}
}
}
else
{
lean_object* v_pos_3160_; lean_object* v_err_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
lean_dec_ref_known(v_res_3147_, 1);
v_pos_3160_ = lean_ctor_get(v___x_3150_, 0);
v_err_3161_ = lean_ctor_get(v___x_3150_, 1);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_3150_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_err_3161_);
lean_inc(v_pos_3160_);
lean_dec(v___x_3150_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_pos_3160_);
lean_ctor_set(v_reuseFailAlloc_3167_, 1, v_err_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
}
else
{
return v___x_3146_;
}
}
else
{
return v___x_3146_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData___boxed(lean_object* v_size_3169_, lean_object* v_a_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_Std_Http_Protocol_H1_parseChunkSizedData(v_size_3169_, v_a_3170_);
lean_dec(v_size_3169_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField_spec__0(lean_object* v_s_3172_, lean_object* v_p_3173_){
_start:
{
lean_object* v___y_3175_; lean_object* v___y_3176_; uint32_t v___y_3180_; lean_object* v___x_3192_; uint8_t v_decide_3193_; 
v___x_3192_ = lean_string_utf8_byte_size(v_s_3172_);
v_decide_3193_ = lean_nat_dec_eq(v_p_3173_, v___x_3192_);
if (v_decide_3193_ == 0)
{
uint32_t v___x_3194_; uint32_t v___x_3195_; uint8_t v___x_3196_; 
v___x_3194_ = lean_string_utf8_get_fast(v_s_3172_, v_p_3173_);
v___x_3195_ = 65;
v___x_3196_ = lean_uint32_dec_le(v___x_3195_, v___x_3194_);
if (v___x_3196_ == 0)
{
v___y_3180_ = v___x_3194_;
goto v___jp_3179_;
}
else
{
uint32_t v___x_3197_; uint8_t v___x_3198_; 
v___x_3197_ = 90;
v___x_3198_ = lean_uint32_dec_le(v___x_3194_, v___x_3197_);
if (v___x_3198_ == 0)
{
v___y_3180_ = v___x_3194_;
goto v___jp_3179_;
}
else
{
uint32_t v___x_3199_; uint32_t v___x_3200_; 
v___x_3199_ = 32;
v___x_3200_ = lean_uint32_add(v___x_3194_, v___x_3199_);
v___y_3180_ = v___x_3200_;
goto v___jp_3179_;
}
}
}
else
{
lean_dec(v_p_3173_);
return v_s_3172_;
}
v___jp_3174_:
{
lean_object* v___x_3177_; 
v___x_3177_ = lean_nat_add(v_p_3173_, v___y_3176_);
lean_dec(v_p_3173_);
v_s_3172_ = v___y_3175_;
v_p_3173_ = v___x_3177_;
goto _start;
}
v___jp_3179_:
{
lean_object* v___x_3181_; uint32_t v___x_3182_; uint8_t v___x_3183_; 
lean_inc(v_p_3173_);
v___x_3181_ = lean_string_utf8_set(v_s_3172_, v_p_3173_, v___y_3180_);
v___x_3182_ = 127;
v___x_3183_ = lean_uint32_dec_le(v___y_3180_, v___x_3182_);
if (v___x_3183_ == 0)
{
uint32_t v___x_3184_; uint8_t v___x_3185_; 
v___x_3184_ = 2047;
v___x_3185_ = lean_uint32_dec_le(v___y_3180_, v___x_3184_);
if (v___x_3185_ == 0)
{
uint32_t v___x_3186_; uint8_t v___x_3187_; 
v___x_3186_ = 65535;
v___x_3187_ = lean_uint32_dec_le(v___y_3180_, v___x_3186_);
if (v___x_3187_ == 0)
{
lean_object* v___x_3188_; 
v___x_3188_ = lean_unsigned_to_nat(4u);
v___y_3175_ = v___x_3181_;
v___y_3176_ = v___x_3188_;
goto v___jp_3174_;
}
else
{
lean_object* v___x_3189_; 
v___x_3189_ = lean_unsigned_to_nat(3u);
v___y_3175_ = v___x_3181_;
v___y_3176_ = v___x_3189_;
goto v___jp_3174_;
}
}
else
{
lean_object* v___x_3190_; 
v___x_3190_ = lean_unsigned_to_nat(2u);
v___y_3175_ = v___x_3181_;
v___y_3176_ = v___x_3190_;
goto v___jp_3174_;
}
}
else
{
lean_object* v___x_3191_; 
v___x_3191_ = lean_unsigned_to_nat(1u);
v___y_3175_ = v___x_3181_;
v___y_3176_ = v___x_3191_;
goto v___jp_3174_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField(lean_object* v_name_3208_){
_start:
{
lean_object* v___x_3209_; lean_object* v_n_3210_; lean_object* v___x_3211_; uint8_t v___x_3212_; 
v___x_3209_ = lean_unsigned_to_nat(0u);
v_n_3210_ = l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField_spec__0(v_name_3208_, v___x_3209_);
v___x_3211_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__0));
v___x_3212_ = lean_string_dec_eq(v_n_3210_, v___x_3211_);
if (v___x_3212_ == 0)
{
lean_object* v___x_3213_; uint8_t v___x_3214_; 
v___x_3213_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__1));
v___x_3214_ = lean_string_dec_eq(v_n_3210_, v___x_3213_);
if (v___x_3214_ == 0)
{
lean_object* v___x_3215_; uint8_t v___x_3216_; 
v___x_3215_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__2));
v___x_3216_ = lean_string_dec_eq(v_n_3210_, v___x_3215_);
if (v___x_3216_ == 0)
{
lean_object* v___x_3217_; uint8_t v___x_3218_; 
v___x_3217_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__3));
v___x_3218_ = lean_string_dec_eq(v_n_3210_, v___x_3217_);
if (v___x_3218_ == 0)
{
lean_object* v___x_3219_; uint8_t v___x_3220_; 
v___x_3219_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__4));
v___x_3220_ = lean_string_dec_eq(v_n_3210_, v___x_3219_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; uint8_t v___x_3222_; 
v___x_3221_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__5));
v___x_3222_ = lean_string_dec_eq(v_n_3210_, v___x_3221_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; uint8_t v___x_3224_; 
v___x_3223_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__6));
v___x_3224_ = lean_string_dec_eq(v_n_3210_, v___x_3223_);
lean_dec_ref(v_n_3210_);
return v___x_3224_;
}
else
{
lean_dec_ref(v_n_3210_);
return v___x_3222_;
}
}
else
{
lean_dec_ref(v_n_3210_);
return v___x_3220_;
}
}
else
{
lean_dec_ref(v_n_3210_);
return v___x_3218_;
}
}
else
{
lean_dec_ref(v_n_3210_);
return v___x_3216_;
}
}
else
{
lean_dec_ref(v_n_3210_);
return v___x_3214_;
}
}
else
{
lean_dec_ref(v_n_3210_);
return v___x_3212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___boxed(lean_object* v_name_3225_){
_start:
{
uint8_t v_res_3226_; lean_object* v_r_3227_; 
v_res_3226_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField(v_name_3225_);
v_r_3227_ = lean_box(v_res_3226_);
return v_r_3227_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(lean_object* v_name_3233_){
_start:
{
lean_object* v___x_3234_; lean_object* v_n_3235_; uint8_t v___x_3236_; 
v___x_3234_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_name_3233_);
v_n_3235_ = l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField_spec__0(v_name_3233_, v___x_3234_);
v___x_3236_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField(v_name_3233_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3237_; uint8_t v___x_3238_; 
v___x_3237_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0));
v___x_3238_ = lean_string_dec_eq(v_n_3235_, v___x_3237_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3239_; uint8_t v___x_3240_; 
v___x_3239_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1));
v___x_3240_ = lean_string_dec_eq(v_n_3235_, v___x_3239_);
if (v___x_3240_ == 0)
{
lean_object* v___x_3241_; uint8_t v___x_3242_; 
v___x_3241_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2));
v___x_3242_ = lean_string_dec_eq(v_n_3235_, v___x_3241_);
if (v___x_3242_ == 0)
{
lean_object* v___x_3243_; uint8_t v___x_3244_; 
v___x_3243_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3));
v___x_3244_ = lean_string_dec_eq(v_n_3235_, v___x_3243_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; uint8_t v___x_3246_; 
v___x_3245_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4));
v___x_3246_ = lean_string_dec_eq(v_n_3235_, v___x_3245_);
lean_dec_ref(v_n_3235_);
return v___x_3246_;
}
else
{
lean_dec_ref(v_n_3235_);
return v___x_3244_;
}
}
else
{
lean_dec_ref(v_n_3235_);
return v___x_3242_;
}
}
else
{
lean_dec_ref(v_n_3235_);
return v___x_3240_;
}
}
else
{
lean_dec_ref(v_n_3235_);
return v___x_3238_;
}
}
else
{
lean_dec_ref(v_n_3235_);
return v___x_3236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___boxed(lean_object* v_name_3247_){
_start:
{
uint8_t v_res_3248_; lean_object* v_r_3249_; 
v_res_3248_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_name_3247_);
v_r_3249_ = lean_box(v_res_3248_);
return v_r_3249_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailerHeader(lean_object* v_limits_3251_, uint8_t v_strict_3252_, lean_object* v_a_3253_){
_start:
{
lean_object* v___x_3254_; 
v___x_3254_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_3251_, v_a_3253_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_res_3255_; 
v_res_3255_ = lean_ctor_get(v___x_3254_, 1);
lean_inc(v_res_3255_);
if (lean_obj_tag(v_res_3255_) == 1)
{
lean_object* v_val_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3278_; 
v_val_3256_ = lean_ctor_get(v_res_3255_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v_res_3255_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3258_ = v_res_3255_;
v_isShared_3259_ = v_isSharedCheck_3278_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_val_3256_);
lean_dec(v_res_3255_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3278_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v_pos_3260_; lean_object* v_fst_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3276_; 
v_pos_3260_ = lean_ctor_get(v___x_3254_, 0);
v_fst_3261_ = lean_ctor_get(v_val_3256_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v_val_3256_);
if (v_isSharedCheck_3276_ == 0)
{
lean_object* v_unused_3277_; 
v_unused_3277_ = lean_ctor_get(v_val_3256_, 1);
lean_dec(v_unused_3277_);
v___x_3263_ = v_val_3256_;
v_isShared_3264_ = v_isSharedCheck_3276_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_fst_3261_);
lean_dec(v_val_3256_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3276_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
uint8_t v___x_3274_; 
lean_inc(v_fst_3261_);
v___x_3274_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField(v_fst_3261_);
if (v___x_3274_ == 0)
{
if (v_strict_3252_ == 0)
{
lean_del_object(v___x_3263_);
lean_dec(v_fst_3261_);
lean_del_object(v___x_3258_);
return v___x_3254_;
}
else
{
uint8_t v___x_3275_; 
lean_inc(v_fst_3261_);
v___x_3275_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_fst_3261_);
if (v___x_3275_ == 0)
{
lean_del_object(v___x_3263_);
lean_dec(v_fst_3261_);
lean_del_object(v___x_3258_);
return v___x_3254_;
}
else
{
lean_inc(v_pos_3260_);
lean_dec_ref_known(v___x_3254_, 2);
goto v___jp_3265_;
}
}
}
else
{
lean_inc(v_pos_3260_);
lean_dec_ref_known(v___x_3254_, 2);
goto v___jp_3265_;
}
v___jp_3265_:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3269_; 
v___x_3266_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseTrailerHeader___closed__0));
v___x_3267_ = lean_string_append(v___x_3266_, v_fst_3261_);
lean_dec(v_fst_3261_);
if (v_isShared_3259_ == 0)
{
lean_ctor_set(v___x_3258_, 0, v___x_3267_);
v___x_3269_ = v___x_3258_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3267_);
v___x_3269_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
lean_object* v___x_3271_; 
if (v_isShared_3264_ == 0)
{
lean_ctor_set_tag(v___x_3263_, 1);
lean_ctor_set(v___x_3263_, 1, v___x_3269_);
lean_ctor_set(v___x_3263_, 0, v_pos_3260_);
v___x_3271_ = v___x_3263_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_pos_3260_);
lean_ctor_set(v_reuseFailAlloc_3272_, 1, v___x_3269_);
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
}
}
else
{
lean_dec(v_res_3255_);
return v___x_3254_;
}
}
else
{
return v___x_3254_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailerHeader___boxed(lean_object* v_limits_3279_, lean_object* v_strict_3280_, lean_object* v_a_3281_){
_start:
{
uint8_t v_strict_boxed_3282_; lean_object* v_res_3283_; 
v_strict_boxed_3282_ = lean_unbox(v_strict_3280_);
v_res_3283_ = l_Std_Http_Protocol_H1_parseTrailerHeader(v_limits_3279_, v_strict_boxed_3282_, v_a_3281_);
lean_dec_ref(v_limits_3279_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailers(lean_object* v_limits_3284_, lean_object* v_a_3285_){
_start:
{
lean_object* v_maxTrailerHeaders_3286_; uint8_t v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v_maxTrailerHeaders_3286_ = lean_ctor_get(v_limits_3284_, 17);
lean_inc(v_maxTrailerHeaders_3286_);
v___x_3287_ = 1;
v___x_3288_ = lean_box(v___x_3287_);
v___x_3289_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_parseTrailerHeader___boxed), 3, 2);
lean_closure_set(v___x_3289_, 0, v_limits_3284_);
lean_closure_set(v___x_3289_, 1, v___x_3288_);
v___x_3290_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___x_3289_, v_maxTrailerHeaders_3286_, v_a_3285_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v_pos_3291_; lean_object* v_res_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v_pos_3291_ = lean_ctor_get(v___x_3290_, 0);
lean_inc(v_pos_3291_);
v_res_3292_ = lean_ctor_get(v___x_3290_, 1);
lean_inc(v_res_3292_);
lean_dec_ref_known(v___x_3290_, 2);
v___x_3293_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3294_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3293_, v_pos_3291_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_pos_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
v_pos_3295_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3302_ == 0)
{
lean_object* v_unused_3303_; 
v_unused_3303_ = lean_ctor_get(v___x_3294_, 1);
lean_dec(v_unused_3303_);
v___x_3297_ = v___x_3294_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_pos_3295_);
lean_dec(v___x_3294_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 1, v_res_3292_);
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_pos_3295_);
lean_ctor_set(v_reuseFailAlloc_3301_, 1, v_res_3292_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
else
{
lean_object* v_pos_3304_; lean_object* v_err_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3312_; 
lean_dec(v_res_3292_);
v_pos_3304_ = lean_ctor_get(v___x_3294_, 0);
v_err_3305_ = lean_ctor_get(v___x_3294_, 1);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3307_ = v___x_3294_;
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_err_3305_);
lean_inc(v_pos_3304_);
lean_dec(v___x_3294_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3310_; 
if (v_isShared_3308_ == 0)
{
v___x_3310_ = v___x_3307_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_pos_3304_);
lean_ctor_set(v_reuseFailAlloc_3311_, 1, v_err_3305_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
}
else
{
return v___x_3290_;
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(uint8_t v_c_3313_){
_start:
{
uint32_t v___x_3314_; uint32_t v___x_3322_; uint8_t v___x_3323_; 
v___x_3314_ = lean_uint8_to_uint32(v_c_3313_);
v___x_3322_ = 33;
v___x_3323_ = lean_uint32_dec_le(v___x_3322_, v___x_3314_);
if (v___x_3323_ == 0)
{
goto v___jp_3315_;
}
else
{
uint32_t v___x_3324_; uint8_t v___x_3325_; 
v___x_3324_ = 126;
v___x_3325_ = lean_uint32_dec_le(v___x_3314_, v___x_3324_);
if (v___x_3325_ == 0)
{
goto v___jp_3315_;
}
else
{
return v___x_3325_;
}
}
v___jp_3315_:
{
uint32_t v___x_3316_; uint8_t v___x_3317_; 
v___x_3316_ = 128;
v___x_3317_ = lean_uint32_dec_le(v___x_3316_, v___x_3314_);
if (v___x_3317_ == 0)
{
uint32_t v___x_3318_; uint8_t v___x_3319_; 
v___x_3318_ = 32;
v___x_3319_ = lean_uint32_dec_eq(v___x_3314_, v___x_3318_);
if (v___x_3319_ == 0)
{
uint32_t v___x_3320_; uint8_t v___x_3321_; 
v___x_3320_ = 9;
v___x_3321_ = lean_uint32_dec_eq(v___x_3314_, v___x_3320_);
return v___x_3321_;
}
else
{
return v___x_3319_;
}
}
else
{
return v___x_3317_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte___boxed(lean_object* v_c_3326_){
_start:
{
uint8_t v_c_boxed_3327_; uint8_t v_res_3328_; lean_object* v_r_3329_; 
v_c_boxed_3327_ = lean_unbox(v_c_3326_);
v_res_3328_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(v_c_boxed_3327_);
v_r_3329_ = lean_box(v_res_3328_);
return v_r_3329_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(lean_object* v_limits_3330_, lean_object* v_a_3331_){
_start:
{
lean_object* v_maxReasonPhraseLength_3332_; lean_object* v___f_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v_snd_3336_; lean_object* v_snd_3337_; uint8_t v___x_3338_; 
v_maxReasonPhraseLength_3332_ = lean_ctor_get(v_limits_3330_, 16);
v___f_3333_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4));
v___x_3334_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_3331_);
v___x_3335_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3333_, v_maxReasonPhraseLength_3332_, v___x_3334_, v_a_3331_);
v_snd_3336_ = lean_ctor_get(v___x_3335_, 1);
lean_inc(v_snd_3336_);
v_snd_3337_ = lean_ctor_get(v_snd_3336_, 1);
v___x_3338_ = lean_unbox(v_snd_3337_);
if (v___x_3338_ == 0)
{
lean_object* v_fst_3339_; lean_object* v_fst_3340_; lean_object* v_array_3341_; lean_object* v_idx_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3362_; 
v_fst_3339_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_fst_3339_);
lean_dec_ref(v___x_3335_);
v_fst_3340_ = lean_ctor_get(v_snd_3336_, 0);
lean_inc(v_fst_3340_);
lean_dec(v_snd_3336_);
v_array_3341_ = lean_ctor_get(v_a_3331_, 0);
v_idx_3342_ = lean_ctor_get(v_a_3331_, 1);
v_isSharedCheck_3362_ = !lean_is_exclusive(v_a_3331_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3344_ = v_a_3331_;
v_isShared_3345_ = v_isSharedCheck_3362_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_idx_3342_);
lean_inc(v_array_3341_);
lean_dec(v_a_3331_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3362_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v_lower_3347_; lean_object* v_upper_3348_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___y_3359_; uint8_t v___x_3361_; 
v___x_3356_ = lean_nat_add(v_idx_3342_, v_fst_3339_);
lean_dec(v_fst_3339_);
v___x_3357_ = lean_byte_array_size(v_array_3341_);
v___x_3361_ = lean_nat_dec_le(v_idx_3342_, v___x_3334_);
if (v___x_3361_ == 0)
{
v___y_3359_ = v_idx_3342_;
goto v___jp_3358_;
}
else
{
lean_dec(v_idx_3342_);
v___y_3359_ = v___x_3334_;
goto v___jp_3358_;
}
v___jp_3346_:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3354_; 
v___x_3349_ = l_ByteArray_toByteSlice(v_array_3341_, v_lower_3347_, v_upper_3348_);
v___x_3350_ = l_ByteSlice_toByteArray(v___x_3349_);
v___x_3351_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2));
v___x_3352_ = l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go(v___x_3350_, v___x_3334_, v___x_3351_);
lean_dec_ref(v___x_3350_);
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 1, v___x_3352_);
lean_ctor_set(v___x_3344_, 0, v_fst_3340_);
v___x_3354_ = v___x_3344_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_fst_3340_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v___x_3352_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
v___jp_3358_:
{
uint8_t v___x_3360_; 
v___x_3360_ = lean_nat_dec_le(v___x_3356_, v___x_3357_);
if (v___x_3360_ == 0)
{
lean_dec(v___x_3356_);
v_lower_3347_ = v___y_3359_;
v_upper_3348_ = v___x_3357_;
goto v___jp_3346_;
}
else
{
v_lower_3347_ = v___y_3359_;
v_upper_3348_ = v___x_3356_;
goto v___jp_3346_;
}
}
}
}
else
{
lean_object* v_fst_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3371_; 
lean_dec_ref(v___x_3335_);
lean_dec_ref(v_a_3331_);
v_fst_3363_ = lean_ctor_get(v_snd_3336_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v_snd_3336_);
if (v_isSharedCheck_3371_ == 0)
{
lean_object* v_unused_3372_; 
v_unused_3372_ = lean_ctor_get(v_snd_3336_, 1);
lean_dec(v_unused_3372_);
v___x_3365_ = v_snd_3336_;
v_isShared_3366_ = v_isSharedCheck_3371_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_fst_3363_);
lean_dec(v_snd_3336_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3371_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3367_; lean_object* v___x_3369_; 
v___x_3367_ = lean_box(0);
if (v_isShared_3366_ == 0)
{
lean_ctor_set_tag(v___x_3365_, 1);
lean_ctor_set(v___x_3365_, 1, v___x_3367_);
v___x_3369_ = v___x_3365_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_fst_3363_);
lean_ctor_set(v_reuseFailAlloc_3370_, 1, v___x_3367_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___boxed(lean_object* v_limits_3373_, lean_object* v_a_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_3373_, v_a_3374_);
lean_dec_ref(v_limits_3373_);
return v_res_3375_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(lean_object* v_x_3376_){
_start:
{
if (lean_obj_tag(v_x_3376_) == 0)
{
uint8_t v___x_3377_; 
v___x_3377_ = 1;
return v___x_3377_;
}
else
{
lean_object* v_head_3378_; lean_object* v_tail_3379_; uint32_t v___x_3385_; uint32_t v___x_3386_; uint8_t v___x_3387_; 
v_head_3378_ = lean_ctor_get(v_x_3376_, 0);
v_tail_3379_ = lean_ctor_get(v_x_3376_, 1);
v___x_3385_ = 9;
v___x_3386_ = lean_unbox_uint32(v_head_3378_);
v___x_3387_ = lean_uint32_dec_eq(v___x_3386_, v___x_3385_);
if (v___x_3387_ == 0)
{
uint32_t v___x_3388_; uint32_t v___x_3389_; uint8_t v___x_3390_; 
v___x_3388_ = 32;
v___x_3389_ = lean_unbox_uint32(v_head_3378_);
v___x_3390_ = lean_uint32_dec_eq(v___x_3389_, v___x_3388_);
if (v___x_3390_ == 0)
{
uint32_t v___x_3391_; uint32_t v___x_3392_; uint8_t v___x_3393_; 
v___x_3391_ = 33;
v___x_3392_ = lean_unbox_uint32(v_head_3378_);
v___x_3393_ = lean_uint32_dec_le(v___x_3391_, v___x_3392_);
if (v___x_3393_ == 0)
{
goto v___jp_3380_;
}
else
{
uint32_t v___x_3394_; uint32_t v___x_3395_; uint8_t v___x_3396_; 
v___x_3394_ = 126;
v___x_3395_ = lean_unbox_uint32(v_head_3378_);
v___x_3396_ = lean_uint32_dec_le(v___x_3395_, v___x_3394_);
if (v___x_3396_ == 0)
{
goto v___jp_3380_;
}
else
{
v_x_3376_ = v_tail_3379_;
goto _start;
}
}
}
else
{
v_x_3376_ = v_tail_3379_;
goto _start;
}
}
else
{
v_x_3376_ = v_tail_3379_;
goto _start;
}
v___jp_3380_:
{
uint32_t v___x_3381_; uint32_t v___x_3382_; uint8_t v___x_3383_; 
v___x_3381_ = 128;
v___x_3382_ = lean_unbox_uint32(v_head_3378_);
v___x_3383_ = lean_uint32_dec_le(v___x_3381_, v___x_3382_);
if (v___x_3383_ == 0)
{
return v___x_3383_;
}
else
{
v_x_3376_ = v_tail_3379_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0___boxed(lean_object* v_x_3400_){
_start:
{
uint8_t v_res_3401_; lean_object* v_r_3402_; 
v_res_3401_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v_x_3400_);
lean_dec(v_x_3400_);
v_r_3402_ = lean_box(v_res_3401_);
return v_r_3402_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(lean_object* v_limits_3406_, lean_object* v_a_3407_){
_start:
{
lean_object* v___y_3412_; lean_object* v_array_3415_; lean_object* v_idx_3416_; lean_object* v___x_3417_; uint8_t v___x_3418_; 
v_array_3415_ = lean_ctor_get(v_a_3407_, 0);
v_idx_3416_ = lean_ctor_get(v_a_3407_, 1);
v___x_3417_ = lean_byte_array_size(v_array_3415_);
v___x_3418_ = lean_nat_dec_lt(v_idx_3416_, v___x_3417_);
if (v___x_3418_ == 0)
{
lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3419_ = lean_box(0);
v___x_3420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3420_, 0, v_a_3407_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
return v___x_3420_;
}
else
{
uint8_t v_c_3421_; uint8_t v___x_3422_; uint8_t v___x_3423_; 
v_c_3421_ = lean_byte_array_fget(v_array_3415_, v_idx_3416_);
v___x_3422_ = 48;
v___x_3423_ = lean_uint8_dec_le(v___x_3422_, v_c_3421_);
if (v___x_3423_ == 0)
{
goto v___jp_3408_;
}
else
{
uint8_t v___x_3424_; uint8_t v___x_3425_; 
v___x_3424_ = 57;
v___x_3425_ = lean_uint8_dec_le(v_c_3421_, v___x_3424_);
if (v___x_3425_ == 0)
{
goto v___jp_3408_;
}
else
{
lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3527_; 
lean_inc(v_idx_3416_);
lean_inc_ref(v_array_3415_);
v_isSharedCheck_3527_ = !lean_is_exclusive(v_a_3407_);
if (v_isSharedCheck_3527_ == 0)
{
lean_object* v_unused_3528_; lean_object* v_unused_3529_; 
v_unused_3528_ = lean_ctor_get(v_a_3407_, 1);
lean_dec(v_unused_3528_);
v_unused_3529_ = lean_ctor_get(v_a_3407_, 0);
lean_dec(v_unused_3529_);
v___x_3427_ = v_a_3407_;
v_isShared_3428_ = v_isSharedCheck_3527_;
goto v_resetjp_3426_;
}
else
{
lean_dec(v_a_3407_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3527_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v_it_x27_3432_; 
v___x_3429_ = lean_unsigned_to_nat(1u);
v___x_3430_ = lean_nat_add(v_idx_3416_, v___x_3429_);
lean_dec(v_idx_3416_);
lean_inc(v___x_3430_);
lean_inc_ref(v_array_3415_);
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 1, v___x_3430_);
v_it_x27_3432_ = v___x_3427_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_array_3415_);
lean_ctor_set(v_reuseFailAlloc_3526_, 1, v___x_3430_);
v_it_x27_3432_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
uint8_t v___x_3436_; 
v___x_3436_ = lean_nat_dec_lt(v___x_3430_, v___x_3417_);
if (v___x_3436_ == 0)
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
lean_dec(v___x_3430_);
lean_dec_ref(v_array_3415_);
v___x_3437_ = lean_box(0);
v___x_3438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3438_, 0, v_it_x27_3432_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
return v___x_3438_;
}
else
{
uint8_t v_c_3439_; uint8_t v___x_3440_; 
v_c_3439_ = lean_byte_array_fget(v_array_3415_, v___x_3430_);
v___x_3440_ = lean_uint8_dec_le(v___x_3422_, v_c_3439_);
if (v___x_3440_ == 0)
{
lean_dec(v___x_3430_);
lean_dec_ref(v_array_3415_);
goto v___jp_3433_;
}
else
{
uint8_t v___x_3441_; 
v___x_3441_ = lean_uint8_dec_le(v_c_3439_, v___x_3424_);
if (v___x_3441_ == 0)
{
lean_dec(v___x_3430_);
lean_dec_ref(v_array_3415_);
goto v___jp_3433_;
}
else
{
lean_object* v___x_3442_; lean_object* v_it_x27_3443_; uint8_t v___x_3447_; 
lean_dec_ref(v_it_x27_3432_);
v___x_3442_ = lean_nat_add(v___x_3430_, v___x_3429_);
lean_dec(v___x_3430_);
lean_inc(v___x_3442_);
lean_inc_ref(v_array_3415_);
v_it_x27_3443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3443_, 0, v_array_3415_);
lean_ctor_set(v_it_x27_3443_, 1, v___x_3442_);
v___x_3447_ = lean_nat_dec_lt(v___x_3442_, v___x_3417_);
if (v___x_3447_ == 0)
{
lean_object* v___x_3448_; lean_object* v___x_3449_; 
lean_dec(v___x_3442_);
lean_dec_ref(v_array_3415_);
v___x_3448_ = lean_box(0);
v___x_3449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3449_, 0, v_it_x27_3443_);
lean_ctor_set(v___x_3449_, 1, v___x_3448_);
return v___x_3449_;
}
else
{
uint8_t v_c_3450_; uint8_t v___x_3451_; 
v_c_3450_ = lean_byte_array_fget(v_array_3415_, v___x_3442_);
v___x_3451_ = lean_uint8_dec_le(v___x_3422_, v_c_3450_);
if (v___x_3451_ == 0)
{
lean_dec(v___x_3442_);
lean_dec_ref(v_array_3415_);
goto v___jp_3444_;
}
else
{
uint8_t v___x_3452_; 
v___x_3452_ = lean_uint8_dec_le(v_c_3450_, v___x_3424_);
if (v___x_3452_ == 0)
{
lean_dec(v___x_3442_);
lean_dec_ref(v_array_3415_);
goto v___jp_3444_;
}
else
{
lean_object* v___x_3453_; uint32_t v___x_3454_; uint32_t v___x_3455_; lean_object* v___x_3456_; lean_object* v_it_x27_3457_; uint32_t v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v_pos_3506_; lean_object* v_idx_3507_; lean_object* v_err_3508_; uint8_t v___x_3512_; 
lean_dec_ref_known(v_it_x27_3443_, 2);
v___x_3453_ = lean_unsigned_to_nat(48u);
v___x_3454_ = lean_uint8_to_uint32(v_c_3421_);
v___x_3455_ = lean_uint8_to_uint32(v_c_3439_);
v___x_3456_ = lean_nat_add(v___x_3442_, v___x_3429_);
lean_dec(v___x_3442_);
lean_inc(v___x_3456_);
lean_inc_ref(v_array_3415_);
v_it_x27_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3457_, 0, v_array_3415_);
lean_ctor_set(v_it_x27_3457_, 1, v___x_3456_);
v___x_3458_ = lean_uint8_to_uint32(v_c_3450_);
v___x_3459_ = lean_uint32_to_nat(v___x_3454_);
v___x_3460_ = lean_nat_sub(v___x_3459_, v___x_3453_);
lean_dec(v___x_3459_);
v___x_3461_ = lean_unsigned_to_nat(100u);
v___x_3462_ = lean_nat_mul(v___x_3460_, v___x_3461_);
lean_dec(v___x_3460_);
v___x_3463_ = lean_uint32_to_nat(v___x_3455_);
v___x_3464_ = lean_nat_sub(v___x_3463_, v___x_3453_);
lean_dec(v___x_3463_);
v___x_3465_ = lean_unsigned_to_nat(10u);
v___x_3466_ = lean_nat_mul(v___x_3464_, v___x_3465_);
lean_dec(v___x_3464_);
v___x_3467_ = lean_nat_add(v___x_3462_, v___x_3466_);
lean_dec(v___x_3466_);
lean_dec(v___x_3462_);
v___x_3468_ = lean_uint32_to_nat(v___x_3458_);
v___x_3469_ = lean_nat_sub(v___x_3468_, v___x_3453_);
lean_dec(v___x_3468_);
v___x_3470_ = lean_nat_add(v___x_3467_, v___x_3469_);
lean_dec(v___x_3469_);
lean_dec(v___x_3467_);
v___x_3512_ = lean_nat_dec_lt(v___x_3456_, v___x_3417_);
if (v___x_3512_ == 0)
{
lean_object* v___x_3513_; 
lean_dec_ref(v_array_3415_);
v___x_3513_ = lean_box(0);
lean_inc(v___x_3456_);
v_pos_3506_ = v_it_x27_3457_;
v_idx_3507_ = v___x_3456_;
v_err_3508_ = v___x_3513_;
goto v___jp_3505_;
}
else
{
uint8_t v___x_3514_; uint8_t v_got_3515_; uint8_t v___x_3516_; 
v___x_3514_ = 32;
v_got_3515_ = lean_byte_array_fget(v_array_3415_, v___x_3456_);
v___x_3516_ = lean_uint8_dec_eq(v_got_3515_, v___x_3514_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; 
lean_dec_ref(v_array_3415_);
v___x_3517_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
lean_inc(v___x_3456_);
v_pos_3506_ = v_it_x27_3457_;
v_idx_3507_ = v___x_3456_;
v_err_3508_ = v___x_3517_;
goto v___jp_3505_;
}
else
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
lean_dec_ref_known(v_it_x27_3457_, 2);
v___x_3518_ = lean_nat_add(v___x_3456_, v___x_3429_);
v___x_3519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3519_, 0, v_array_3415_);
lean_ctor_set(v___x_3519_, 1, v___x_3518_);
v___x_3520_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_3406_, v___x_3519_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_pos_3521_; lean_object* v_res_3522_; 
lean_dec(v___x_3456_);
v_pos_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_pos_3521_);
v_res_3522_ = lean_ctor_get(v___x_3520_, 1);
lean_inc(v_res_3522_);
lean_dec_ref_known(v___x_3520_, 2);
v___y_3472_ = v_pos_3521_;
v___y_3473_ = v_res_3522_;
goto v___jp_3471_;
}
else
{
lean_object* v_pos_3523_; lean_object* v___x_3524_; lean_object* v_idx_3525_; 
v_pos_3523_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_pos_3523_);
lean_dec_ref_known(v___x_3520_, 2);
v___x_3524_ = lean_box(0);
v_idx_3525_ = lean_ctor_get(v_pos_3523_, 1);
lean_inc(v_idx_3525_);
v_pos_3506_ = v_pos_3523_;
v_idx_3507_ = v_idx_3525_;
v_err_3508_ = v___x_3524_;
goto v___jp_3505_;
}
}
}
v___jp_3471_:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3474_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3475_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3474_, v___y_3472_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v_pos_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3494_; 
v_pos_3476_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3494_ == 0)
{
lean_object* v_unused_3495_; 
v_unused_3495_ = lean_ctor_get(v___x_3475_, 1);
lean_dec(v_unused_3495_);
v___x_3478_ = v___x_3475_;
v_isShared_3479_ = v_isSharedCheck_3494_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_pos_3476_);
lean_dec(v___x_3475_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3494_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
uint8_t v___x_3480_; 
v___x_3480_ = lean_nat_dec_lt(v___x_3470_, v___x_3461_);
if (v___x_3480_ == 0)
{
lean_object* v___x_3481_; uint8_t v___x_3482_; 
lean_inc_ref(v___y_3473_);
v___x_3481_ = l_String_toListImpl(v___y_3473_);
v___x_3482_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v___x_3481_);
lean_dec(v___x_3481_);
if (v___x_3482_ == 0)
{
lean_del_object(v___x_3478_);
lean_dec_ref(v___y_3473_);
lean_dec(v___x_3470_);
v___y_3412_ = v_pos_3476_;
goto v___jp_3411_;
}
else
{
lean_object* v___x_3483_; uint16_t v___x_3484_; lean_object* v___x_3485_; 
v___x_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3483_, 0, v___y_3473_);
v___x_3484_ = lean_uint16_of_nat(v___x_3470_);
lean_dec(v___x_3470_);
v___x_3485_ = l_Std_Http_Status_ofCode(v___x_3483_, v___x_3484_);
if (lean_obj_tag(v___x_3485_) == 1)
{
lean_object* v_val_3486_; lean_object* v___x_3488_; 
v_val_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_val_3486_);
lean_dec_ref_known(v___x_3485_, 1);
if (v_isShared_3479_ == 0)
{
lean_ctor_set(v___x_3478_, 1, v_val_3486_);
v___x_3488_ = v___x_3478_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_pos_3476_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v_val_3486_);
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
lean_dec(v___x_3485_);
lean_del_object(v___x_3478_);
v___y_3412_ = v_pos_3476_;
goto v___jp_3411_;
}
}
}
else
{
lean_object* v___x_3490_; lean_object* v___x_3492_; 
lean_dec_ref(v___y_3473_);
lean_dec(v___x_3470_);
v___x_3490_ = lean_box(52);
if (v_isShared_3479_ == 0)
{
lean_ctor_set(v___x_3478_, 1, v___x_3490_);
v___x_3492_ = v___x_3478_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_pos_3476_);
lean_ctor_set(v_reuseFailAlloc_3493_, 1, v___x_3490_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
else
{
lean_object* v_pos_3496_; lean_object* v_err_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
lean_dec_ref(v___y_3473_);
lean_dec(v___x_3470_);
v_pos_3496_ = lean_ctor_get(v___x_3475_, 0);
v_err_3497_ = lean_ctor_get(v___x_3475_, 1);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3475_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_err_3497_);
lean_inc(v_pos_3496_);
lean_dec(v___x_3475_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_pos_3496_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v_err_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
v___jp_3505_:
{
uint8_t v___x_3509_; 
v___x_3509_ = lean_nat_dec_eq(v___x_3456_, v_idx_3507_);
lean_dec(v_idx_3507_);
lean_dec(v___x_3456_);
if (v___x_3509_ == 0)
{
lean_object* v___x_3510_; 
lean_dec(v___x_3470_);
lean_inc(v_err_3508_);
v___x_3510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3510_, 0, v_pos_3506_);
lean_ctor_set(v___x_3510_, 1, v_err_3508_);
return v___x_3510_;
}
else
{
lean_object* v___x_3511_; 
v___x_3511_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2));
v___y_3472_ = v_pos_3506_;
v___y_3473_ = v___x_3511_;
goto v___jp_3471_;
}
}
}
}
}
v___jp_3444_:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3445_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3446_, 0, v_it_x27_3443_);
lean_ctor_set(v___x_3446_, 1, v___x_3445_);
return v___x_3446_;
}
}
}
}
v___jp_3433_:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3434_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3435_, 0, v_it_x27_3432_);
lean_ctor_set(v___x_3435_, 1, v___x_3434_);
return v___x_3435_;
}
}
}
}
}
}
v___jp_3408_:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3410_, 0, v_a_3407_);
lean_ctor_set(v___x_3410_, 1, v___x_3409_);
return v___x_3410_;
}
v___jp_3411_:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__1));
v___x_3414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3414_, 0, v___y_3412_);
lean_ctor_set(v___x_3414_, 1, v___x_3413_);
return v___x_3414_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___boxed(lean_object* v_limits_3530_, lean_object* v_a_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_3530_, v_a_3531_);
lean_dec_ref(v_limits_3530_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine(lean_object* v_limits_3533_, lean_object* v_a_3534_){
_start:
{
lean_object* v___x_3535_; 
v___x_3535_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_3534_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_pos_3536_; lean_object* v_res_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3611_; 
v_pos_3536_ = lean_ctor_get(v___x_3535_, 0);
v_res_3537_ = lean_ctor_get(v___x_3535_, 1);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3539_ = v___x_3535_;
v_isShared_3540_ = v_isSharedCheck_3611_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_res_3537_);
lean_inc(v_pos_3536_);
lean_dec(v___x_3535_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3611_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v_array_3541_; lean_object* v_idx_3542_; lean_object* v___x_3543_; uint8_t v___x_3544_; 
v_array_3541_ = lean_ctor_get(v_pos_3536_, 0);
v_idx_3542_ = lean_ctor_get(v_pos_3536_, 1);
v___x_3543_ = lean_byte_array_size(v_array_3541_);
v___x_3544_ = lean_nat_dec_lt(v_idx_3542_, v___x_3543_);
if (v___x_3544_ == 0)
{
lean_object* v___x_3545_; lean_object* v___x_3547_; 
lean_dec(v_res_3537_);
v___x_3545_ = lean_box(0);
if (v_isShared_3540_ == 0)
{
lean_ctor_set_tag(v___x_3539_, 1);
lean_ctor_set(v___x_3539_, 1, v___x_3545_);
v___x_3547_ = v___x_3539_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_pos_3536_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v___x_3545_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
else
{
uint8_t v___x_3549_; uint8_t v_got_3550_; uint8_t v___x_3551_; 
v___x_3549_ = 32;
v_got_3550_ = lean_byte_array_fget(v_array_3541_, v_idx_3542_);
v___x_3551_ = lean_uint8_dec_eq(v_got_3550_, v___x_3549_);
if (v___x_3551_ == 0)
{
lean_object* v___x_3552_; lean_object* v___x_3554_; 
lean_dec(v_res_3537_);
v___x_3552_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_3540_ == 0)
{
lean_ctor_set_tag(v___x_3539_, 1);
lean_ctor_set(v___x_3539_, 1, v___x_3552_);
v___x_3554_ = v___x_3539_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_pos_3536_);
lean_ctor_set(v_reuseFailAlloc_3555_, 1, v___x_3552_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
else
{
lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3608_; 
lean_inc(v_idx_3542_);
lean_inc_ref(v_array_3541_);
v_isSharedCheck_3608_ = !lean_is_exclusive(v_pos_3536_);
if (v_isSharedCheck_3608_ == 0)
{
lean_object* v_unused_3609_; lean_object* v_unused_3610_; 
v_unused_3609_ = lean_ctor_get(v_pos_3536_, 1);
lean_dec(v_unused_3609_);
v_unused_3610_ = lean_ctor_get(v_pos_3536_, 0);
lean_dec(v_unused_3610_);
v___x_3557_ = v_pos_3536_;
v_isShared_3558_ = v_isSharedCheck_3608_;
goto v_resetjp_3556_;
}
else
{
lean_dec(v_pos_3536_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3608_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v_fst_3559_; lean_object* v_snd_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3607_; 
v_fst_3559_ = lean_ctor_get(v_res_3537_, 0);
v_snd_3560_ = lean_ctor_get(v_res_3537_, 1);
v_isSharedCheck_3607_ = !lean_is_exclusive(v_res_3537_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3562_ = v_res_3537_;
v_isShared_3563_ = v_isSharedCheck_3607_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_snd_3560_);
lean_inc(v_fst_3559_);
lean_dec(v_res_3537_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3607_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3567_; 
v___x_3564_ = lean_unsigned_to_nat(1u);
v___x_3565_ = lean_nat_add(v_idx_3542_, v___x_3564_);
lean_dec(v_idx_3542_);
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 1, v___x_3565_);
v___x_3567_ = v___x_3557_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_array_3541_);
lean_ctor_set(v_reuseFailAlloc_3606_, 1, v___x_3565_);
v___x_3567_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
lean_object* v___x_3568_; 
v___x_3568_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_3533_, v___x_3567_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_pos_3569_; lean_object* v_res_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3596_; 
v_pos_3569_ = lean_ctor_get(v___x_3568_, 0);
v_res_3570_ = lean_ctor_get(v___x_3568_, 1);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3572_ = v___x_3568_;
v_isShared_3573_ = v_isSharedCheck_3596_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_res_3570_);
lean_inc(v_pos_3569_);
lean_dec(v___x_3568_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3596_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
uint8_t v___x_3579_; 
v___x_3579_ = lean_nat_dec_eq(v_fst_3559_, v___x_3564_);
lean_dec(v_fst_3559_);
if (v___x_3579_ == 0)
{
lean_del_object(v___x_3562_);
goto v___jp_3580_;
}
else
{
uint8_t v___x_3589_; 
v___x_3589_ = lean_nat_dec_le(v___x_3564_, v_snd_3560_);
if (v___x_3589_ == 0)
{
lean_del_object(v___x_3562_);
goto v___jp_3580_;
}
else
{
uint8_t v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3594_; 
lean_del_object(v___x_3572_);
lean_dec(v_snd_3560_);
lean_del_object(v___x_3539_);
v___x_3590_ = 1;
v___x_3591_ = l_Std_Http_Headers_empty;
v___x_3592_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3592_, 0, v_res_3570_);
lean_ctor_set(v___x_3592_, 1, v___x_3591_);
lean_ctor_set_uint8(v___x_3592_, sizeof(void*)*2, v___x_3590_);
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 1, v___x_3592_);
lean_ctor_set(v___x_3562_, 0, v_pos_3569_);
v___x_3594_ = v___x_3562_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_pos_3569_);
lean_ctor_set(v_reuseFailAlloc_3595_, 1, v___x_3592_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
v___jp_3574_:
{
lean_object* v___x_3575_; lean_object* v___x_3577_; 
v___x_3575_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
if (v_isShared_3573_ == 0)
{
lean_ctor_set_tag(v___x_3572_, 1);
lean_ctor_set(v___x_3572_, 1, v___x_3575_);
v___x_3577_ = v___x_3572_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_pos_3569_);
lean_ctor_set(v_reuseFailAlloc_3578_, 1, v___x_3575_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
v___jp_3580_:
{
if (v___x_3579_ == 0)
{
lean_dec(v_res_3570_);
lean_dec(v_snd_3560_);
lean_del_object(v___x_3539_);
goto v___jp_3574_;
}
else
{
lean_object* v___x_3581_; uint8_t v___x_3582_; 
v___x_3581_ = lean_unsigned_to_nat(0u);
v___x_3582_ = lean_nat_dec_eq(v_snd_3560_, v___x_3581_);
lean_dec(v_snd_3560_);
if (v___x_3582_ == 0)
{
lean_dec(v_res_3570_);
lean_del_object(v___x_3539_);
goto v___jp_3574_;
}
else
{
uint8_t v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3587_; 
lean_del_object(v___x_3572_);
v___x_3583_ = 0;
v___x_3584_ = l_Std_Http_Headers_empty;
v___x_3585_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3585_, 0, v_res_3570_);
lean_ctor_set(v___x_3585_, 1, v___x_3584_);
lean_ctor_set_uint8(v___x_3585_, sizeof(void*)*2, v___x_3583_);
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 1, v___x_3585_);
lean_ctor_set(v___x_3539_, 0, v_pos_3569_);
v___x_3587_ = v___x_3539_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_pos_3569_);
lean_ctor_set(v_reuseFailAlloc_3588_, 1, v___x_3585_);
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
}
else
{
lean_object* v_pos_3597_; lean_object* v_err_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3605_; 
lean_del_object(v___x_3562_);
lean_dec(v_snd_3560_);
lean_dec(v_fst_3559_);
lean_del_object(v___x_3539_);
v_pos_3597_ = lean_ctor_get(v___x_3568_, 0);
v_err_3598_ = lean_ctor_get(v___x_3568_, 1);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3600_ = v___x_3568_;
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_err_3598_);
lean_inc(v_pos_3597_);
lean_dec(v___x_3568_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3603_; 
if (v_isShared_3601_ == 0)
{
v___x_3603_ = v___x_3600_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_pos_3597_);
lean_ctor_set(v_reuseFailAlloc_3604_, 1, v_err_3598_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
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
lean_object* v_pos_3612_; lean_object* v_err_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3620_; 
v_pos_3612_ = lean_ctor_get(v___x_3535_, 0);
v_err_3613_ = lean_ctor_get(v___x_3535_, 1);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3615_ = v___x_3535_;
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_err_3613_);
lean_inc(v_pos_3612_);
lean_dec(v___x_3535_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
if (v_isShared_3616_ == 0)
{
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_pos_3612_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v_err_3613_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine___boxed(lean_object* v_limits_3621_, lean_object* v_a_3622_){
_start:
{
lean_object* v_res_3623_; 
v_res_3623_ = l_Std_Http_Protocol_H1_parseStatusLine(v_limits_3621_, v_a_3622_);
lean_dec_ref(v_limits_3621_);
return v_res_3623_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion(lean_object* v_limits_3624_, lean_object* v_a_3625_){
_start:
{
lean_object* v___x_3626_; 
v___x_3626_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_3625_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v_pos_3627_; lean_object* v_res_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3691_; 
v_pos_3627_ = lean_ctor_get(v___x_3626_, 0);
v_res_3628_ = lean_ctor_get(v___x_3626_, 1);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3630_ = v___x_3626_;
v_isShared_3631_ = v_isSharedCheck_3691_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_res_3628_);
lean_inc(v_pos_3627_);
lean_dec(v___x_3626_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3691_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v_array_3632_; lean_object* v_idx_3633_; lean_object* v___x_3634_; uint8_t v___x_3635_; 
v_array_3632_ = lean_ctor_get(v_pos_3627_, 0);
v_idx_3633_ = lean_ctor_get(v_pos_3627_, 1);
v___x_3634_ = lean_byte_array_size(v_array_3632_);
v___x_3635_ = lean_nat_dec_lt(v_idx_3633_, v___x_3634_);
if (v___x_3635_ == 0)
{
lean_object* v___x_3636_; lean_object* v___x_3638_; 
lean_dec(v_res_3628_);
v___x_3636_ = lean_box(0);
if (v_isShared_3631_ == 0)
{
lean_ctor_set_tag(v___x_3630_, 1);
lean_ctor_set(v___x_3630_, 1, v___x_3636_);
v___x_3638_ = v___x_3630_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_pos_3627_);
lean_ctor_set(v_reuseFailAlloc_3639_, 1, v___x_3636_);
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
uint8_t v___x_3640_; uint8_t v_got_3641_; uint8_t v___x_3642_; 
v___x_3640_ = 32;
v_got_3641_ = lean_byte_array_fget(v_array_3632_, v_idx_3633_);
v___x_3642_ = lean_uint8_dec_eq(v_got_3641_, v___x_3640_);
if (v___x_3642_ == 0)
{
lean_object* v___x_3643_; lean_object* v___x_3645_; 
lean_dec(v_res_3628_);
v___x_3643_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_3631_ == 0)
{
lean_ctor_set_tag(v___x_3630_, 1);
lean_ctor_set(v___x_3630_, 1, v___x_3643_);
v___x_3645_ = v___x_3630_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_pos_3627_);
lean_ctor_set(v_reuseFailAlloc_3646_, 1, v___x_3643_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
else
{
lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3688_; 
lean_inc(v_idx_3633_);
lean_inc_ref(v_array_3632_);
lean_del_object(v___x_3630_);
v_isSharedCheck_3688_ = !lean_is_exclusive(v_pos_3627_);
if (v_isSharedCheck_3688_ == 0)
{
lean_object* v_unused_3689_; lean_object* v_unused_3690_; 
v_unused_3689_ = lean_ctor_get(v_pos_3627_, 1);
lean_dec(v_unused_3689_);
v_unused_3690_ = lean_ctor_get(v_pos_3627_, 0);
lean_dec(v_unused_3690_);
v___x_3648_ = v_pos_3627_;
v_isShared_3649_ = v_isSharedCheck_3688_;
goto v_resetjp_3647_;
}
else
{
lean_dec(v_pos_3627_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3688_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v_fst_3650_; lean_object* v_snd_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3687_; 
v_fst_3650_ = lean_ctor_get(v_res_3628_, 0);
v_snd_3651_ = lean_ctor_get(v_res_3628_, 1);
v_isSharedCheck_3687_ = !lean_is_exclusive(v_res_3628_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3653_ = v_res_3628_;
v_isShared_3654_ = v_isSharedCheck_3687_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_snd_3651_);
lean_inc(v_fst_3650_);
lean_dec(v_res_3628_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3687_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3658_; 
v___x_3655_ = lean_unsigned_to_nat(1u);
v___x_3656_ = lean_nat_add(v_idx_3633_, v___x_3655_);
lean_dec(v_idx_3633_);
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 1, v___x_3656_);
v___x_3658_ = v___x_3648_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_array_3632_);
lean_ctor_set(v_reuseFailAlloc_3686_, 1, v___x_3656_);
v___x_3658_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
lean_object* v___x_3659_; 
v___x_3659_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_3624_, v___x_3658_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v_pos_3660_; lean_object* v_res_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3676_; 
v_pos_3660_ = lean_ctor_get(v___x_3659_, 0);
v_res_3661_ = lean_ctor_get(v___x_3659_, 1);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3663_ = v___x_3659_;
v_isShared_3664_ = v_isSharedCheck_3676_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_res_3661_);
lean_inc(v_pos_3660_);
lean_dec(v___x_3659_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3676_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___y_3666_; uint8_t v___x_3674_; 
v___x_3674_ = lean_nat_dec_eq(v_fst_3650_, v___x_3655_);
if (v___x_3674_ == 0)
{
v___y_3666_ = v_snd_3651_;
goto v___jp_3665_;
}
else
{
uint8_t v___x_3675_; 
v___x_3675_ = lean_nat_dec_le(v_snd_3651_, v___x_3655_);
if (v___x_3675_ == 0)
{
lean_dec(v_snd_3651_);
v___y_3666_ = v___x_3655_;
goto v___jp_3665_;
}
else
{
v___y_3666_ = v_snd_3651_;
goto v___jp_3665_;
}
}
v___jp_3665_:
{
lean_object* v___x_3667_; lean_object* v___x_3669_; 
v___x_3667_ = l_Std_Http_Version_ofNumber_x3f(v_fst_3650_, v___y_3666_);
lean_dec(v___y_3666_);
lean_dec(v_fst_3650_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 1, v___x_3667_);
lean_ctor_set(v___x_3653_, 0, v_res_3661_);
v___x_3669_ = v___x_3653_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_res_3661_);
lean_ctor_set(v_reuseFailAlloc_3673_, 1, v___x_3667_);
v___x_3669_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
lean_object* v___x_3671_; 
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 1, v___x_3669_);
v___x_3671_ = v___x_3663_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_pos_3660_);
lean_ctor_set(v_reuseFailAlloc_3672_, 1, v___x_3669_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
}
else
{
lean_object* v_pos_3677_; lean_object* v_err_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
lean_del_object(v___x_3653_);
lean_dec(v_snd_3651_);
lean_dec(v_fst_3650_);
v_pos_3677_ = lean_ctor_get(v___x_3659_, 0);
v_err_3678_ = lean_ctor_get(v___x_3659_, 1);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3659_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_err_3678_);
lean_inc(v_pos_3677_);
lean_dec(v___x_3659_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_pos_3677_);
lean_ctor_set(v_reuseFailAlloc_3684_, 1, v_err_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
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
lean_object* v_pos_3692_; lean_object* v_err_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3700_; 
v_pos_3692_ = lean_ctor_get(v___x_3626_, 0);
v_err_3693_ = lean_ctor_get(v___x_3626_, 1);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3695_ = v___x_3626_;
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_err_3693_);
lean_inc(v_pos_3692_);
lean_dec(v___x_3626_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3698_; 
if (v_isShared_3696_ == 0)
{
v___x_3698_ = v___x_3695_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_pos_3692_);
lean_ctor_set(v_reuseFailAlloc_3699_, 1, v_err_3693_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion___boxed(lean_object* v_limits_3701_, lean_object* v_a_3702_){
_start:
{
lean_object* v_res_3703_; 
v_res_3703_ = l_Std_Http_Protocol_H1_parseStatusLineRawVersion(v_limits_3701_, v_a_3702_);
lean_dec_ref(v_limits_3701_);
return v_res_3703_;
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
