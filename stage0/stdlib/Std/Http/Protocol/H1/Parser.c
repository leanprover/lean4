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
uint32_t lean_uint8_to_uint32(uint8_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_String_toListImpl(lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
lean_object* l_Std_Http_Status_ofCode(lean_object*, uint16_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* l_ByteSlice_size(lean_object*);
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
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__0_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "uri too long"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__1_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__1_value)}};
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
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '58'"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4_value;
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
uint8_t v_x_990__boxed_636_; uint8_t v_res_637_; lean_object* v_r_638_; 
v_x_990__boxed_636_ = lean_unbox(v_x_635_);
v_res_637_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex___lam__0(v_x_990__boxed_636_);
v_r_638_ = lean_box(v_res_637_);
return v_r_638_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(lean_object* v_a_640_){
_start:
{
lean_object* v___f_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v_snd_644_; lean_object* v_snd_645_; uint8_t v___x_646_; 
v___f_641_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex___closed__0));
v___x_642_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_640_);
v___x_643_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhile(v___f_641_, v___x_642_, v_a_640_);
v_snd_644_ = lean_ctor_get(v___x_643_, 1);
lean_inc(v_snd_644_);
v_snd_645_ = lean_ctor_get(v_snd_644_, 1);
v___x_646_ = lean_unbox(v_snd_645_);
if (v___x_646_ == 0)
{
lean_object* v_fst_647_; lean_object* v_fst_648_; lean_object* v_array_649_; lean_object* v_idx_650_; lean_object* v_lower_652_; lean_object* v_upper_653_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___y_676_; uint8_t v___x_678_; 
v_fst_647_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_fst_647_);
lean_dec_ref(v___x_643_);
v_fst_648_ = lean_ctor_get(v_snd_644_, 0);
lean_inc(v_fst_648_);
lean_dec(v_snd_644_);
v_array_649_ = lean_ctor_get(v_a_640_, 0);
lean_inc_ref(v_array_649_);
v_idx_650_ = lean_ctor_get(v_a_640_, 1);
lean_inc(v_idx_650_);
lean_dec_ref(v_a_640_);
v___x_673_ = lean_nat_add(v_idx_650_, v_fst_647_);
lean_dec(v_fst_647_);
v___x_674_ = lean_byte_array_size(v_array_649_);
v___x_678_ = lean_nat_dec_le(v_idx_650_, v___x_642_);
if (v___x_678_ == 0)
{
v___y_676_ = v_idx_650_;
goto v___jp_675_;
}
else
{
lean_dec(v_idx_650_);
v___y_676_ = v___x_642_;
goto v___jp_675_;
}
v___jp_651_:
{
lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_654_ = l_ByteArray_toByteSlice(v_array_649_, v_lower_652_, v_upper_653_);
v___x_655_ = l_ByteSlice_size(v___x_654_);
lean_dec_ref(v___x_654_);
v___x_656_ = lean_nat_dec_lt(v___x_642_, v___x_655_);
lean_dec(v___x_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; 
v___x_657_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(v___x_642_, v___x_642_, v_fst_648_);
return v___x_657_;
}
else
{
lean_object* v___x_658_; 
lean_inc(v_fst_648_);
v___x_658_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(v___x_642_, v___x_642_, v_fst_648_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_dec(v_fst_648_);
return v___x_658_;
}
else
{
lean_object* v_err_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_671_; 
v_err_659_ = lean_ctor_get(v___x_658_, 1);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; 
v_unused_672_ = lean_ctor_get(v___x_658_, 0);
lean_dec(v_unused_672_);
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_671_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_err_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_671_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v_idx_663_; uint8_t v___x_664_; 
v_idx_663_ = lean_ctor_get(v_fst_648_, 1);
v___x_664_ = lean_nat_dec_eq(v_idx_663_, v_idx_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_666_; 
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v_fst_648_);
v___x_666_ = v___x_661_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_fst_648_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_err_659_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
else
{
lean_object* v___x_669_; 
lean_dec(v_err_659_);
if (v_isShared_662_ == 0)
{
lean_ctor_set_tag(v___x_661_, 0);
lean_ctor_set(v___x_661_, 1, v___x_642_);
lean_ctor_set(v___x_661_, 0, v_fst_648_);
v___x_669_ = v___x_661_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_fst_648_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v___x_642_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
}
}
v___jp_675_:
{
uint8_t v___x_677_; 
v___x_677_ = lean_nat_dec_le(v___x_673_, v___x_674_);
if (v___x_677_ == 0)
{
lean_dec(v___x_673_);
v_lower_652_ = v___y_676_;
v_upper_653_ = v___x_674_;
goto v___jp_651_;
}
else
{
v_lower_652_ = v___y_676_;
v_upper_653_ = v___x_673_;
goto v___jp_651_;
}
}
}
else
{
lean_object* v_fst_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_687_; 
lean_dec_ref(v___x_643_);
lean_dec_ref(v_a_640_);
v_fst_679_ = lean_ctor_get(v_snd_644_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v_snd_644_);
if (v_isSharedCheck_687_ == 0)
{
lean_object* v_unused_688_; 
v_unused_688_ = lean_ctor_get(v_snd_644_, 1);
lean_dec(v_unused_688_);
v___x_681_ = v_snd_644_;
v_isShared_682_ = v_isSharedCheck_687_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_fst_679_);
lean_dec(v_snd_644_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_687_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_683_ = lean_box(0);
if (v_isShared_682_ == 0)
{
lean_ctor_set_tag(v___x_681_, 1);
lean_ctor_set(v___x_681_, 1, v___x_683_);
v___x_685_ = v___x_681_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_fst_679_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_683_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__0));
v___x_691_ = lean_string_to_utf8(v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(lean_object* v_a_698_){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1);
v___x_700_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_699_, v_a_698_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_pos_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_762_; 
v_pos_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; 
v_unused_763_ = lean_ctor_get(v___x_700_, 1);
lean_dec(v_unused_763_);
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_762_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_pos_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_762_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v_array_710_; lean_object* v_idx_711_; lean_object* v___x_712_; uint8_t v___x_713_; 
v_array_710_ = lean_ctor_get(v_pos_701_, 0);
v_idx_711_ = lean_ctor_get(v_pos_701_, 1);
v___x_712_ = lean_byte_array_size(v_array_710_);
v___x_713_ = lean_nat_dec_lt(v_idx_711_, v___x_712_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; 
lean_del_object(v___x_703_);
v___x_714_ = lean_box(0);
v___x_715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_715_, 0, v_pos_701_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
return v___x_715_;
}
else
{
uint8_t v_c_716_; uint8_t v___x_717_; uint8_t v___x_718_; 
v_c_716_ = lean_byte_array_fget(v_array_710_, v_idx_711_);
v___x_717_ = 48;
v___x_718_ = lean_uint8_dec_le(v___x_717_, v_c_716_);
if (v___x_718_ == 0)
{
goto v___jp_705_;
}
else
{
uint8_t v___x_719_; uint8_t v___x_720_; 
v___x_719_ = 57;
v___x_720_ = lean_uint8_dec_le(v_c_716_, v___x_719_);
if (v___x_720_ == 0)
{
goto v___jp_705_;
}
else
{
lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_759_; 
lean_inc(v_idx_711_);
lean_inc_ref(v_array_710_);
lean_del_object(v___x_703_);
v_isSharedCheck_759_ = !lean_is_exclusive(v_pos_701_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; lean_object* v_unused_761_; 
v_unused_760_ = lean_ctor_get(v_pos_701_, 1);
lean_dec(v_unused_760_);
v_unused_761_ = lean_ctor_get(v_pos_701_, 0);
lean_dec(v_unused_761_);
v___x_722_ = v_pos_701_;
v_isShared_723_ = v_isSharedCheck_759_;
goto v_resetjp_721_;
}
else
{
lean_dec(v_pos_701_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_759_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v_it_x27_727_; 
v___x_724_ = lean_unsigned_to_nat(1u);
v___x_725_ = lean_nat_add(v_idx_711_, v___x_724_);
lean_dec(v_idx_711_);
lean_inc(v___x_725_);
lean_inc_ref(v_array_710_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 1, v___x_725_);
v_it_x27_727_ = v___x_722_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_array_710_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v___x_725_);
v_it_x27_727_ = v_reuseFailAlloc_758_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
uint8_t v___x_728_; 
v___x_728_ = lean_nat_dec_lt(v___x_725_, v___x_712_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; 
lean_dec(v___x_725_);
lean_dec_ref(v_array_710_);
v___x_729_ = lean_box(0);
v___x_730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_730_, 0, v_it_x27_727_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
return v___x_730_;
}
else
{
uint8_t v___x_731_; uint8_t v_got_732_; uint8_t v___x_733_; 
v___x_731_ = 46;
v_got_732_ = lean_byte_array_fget(v_array_710_, v___x_725_);
v___x_733_ = lean_uint8_dec_eq(v_got_732_, v___x_731_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; 
lean_dec(v___x_725_);
lean_dec_ref(v_array_710_);
v___x_734_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5));
v___x_735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_735_, 0, v_it_x27_727_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
return v___x_735_;
}
else
{
lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_741_; 
lean_dec_ref(v_it_x27_727_);
v___x_736_ = lean_nat_add(v___x_725_, v___x_724_);
lean_dec(v___x_725_);
lean_inc(v___x_736_);
lean_inc_ref(v_array_710_);
v___x_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_737_, 0, v_array_710_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_741_ = lean_nat_dec_lt(v___x_736_, v___x_712_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; lean_object* v___x_743_; 
lean_dec(v___x_736_);
lean_dec_ref(v_array_710_);
v___x_742_ = lean_box(0);
v___x_743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_737_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
return v___x_743_;
}
else
{
uint8_t v_c_744_; uint8_t v___x_745_; 
v_c_744_ = lean_byte_array_fget(v_array_710_, v___x_736_);
v___x_745_ = lean_uint8_dec_le(v___x_717_, v_c_744_);
if (v___x_745_ == 0)
{
lean_dec(v___x_736_);
lean_dec_ref(v_array_710_);
goto v___jp_738_;
}
else
{
uint8_t v___x_746_; 
v___x_746_ = lean_uint8_dec_le(v_c_744_, v___x_719_);
if (v___x_746_ == 0)
{
lean_dec(v___x_736_);
lean_dec_ref(v_array_710_);
goto v___jp_738_;
}
else
{
lean_object* v___x_747_; uint32_t v___x_748_; lean_object* v___x_749_; lean_object* v_it_x27_750_; uint32_t v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
lean_dec_ref_known(v___x_737_, 2);
v___x_747_ = lean_unsigned_to_nat(48u);
v___x_748_ = lean_uint8_to_uint32(v_c_716_);
v___x_749_ = lean_nat_add(v___x_736_, v___x_724_);
lean_dec(v___x_736_);
v_it_x27_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_750_, 0, v_array_710_);
lean_ctor_set(v_it_x27_750_, 1, v___x_749_);
v___x_751_ = lean_uint8_to_uint32(v_c_744_);
v___x_752_ = lean_uint32_to_nat(v___x_748_);
v___x_753_ = lean_nat_sub(v___x_752_, v___x_747_);
lean_dec(v___x_752_);
v___x_754_ = lean_uint32_to_nat(v___x_751_);
v___x_755_ = lean_nat_sub(v___x_754_, v___x_747_);
lean_dec(v___x_754_);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_753_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v_it_x27_750_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
return v___x_757_;
}
}
}
v___jp_738_:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_737_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
return v___x_740_;
}
}
}
}
}
}
}
}
v___jp_705_:
{
lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_706_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
if (v_isShared_704_ == 0)
{
lean_ctor_set_tag(v___x_703_, 1);
lean_ctor_set(v___x_703_, 1, v___x_706_);
v___x_708_ = v___x_703_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_pos_701_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
else
{
lean_object* v_pos_764_; lean_object* v_err_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
v_pos_764_ = lean_ctor_get(v___x_700_, 0);
v_err_765_ = lean_ctor_get(v___x_700_, 1);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_700_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_err_765_);
lean_inc(v_pos_764_);
lean_dec(v___x_700_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_pos_764_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_err_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersion(lean_object* v_a_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_773_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_res_775_; lean_object* v_pos_776_; lean_object* v_fst_777_; lean_object* v_snd_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v_res_775_ = lean_ctor_get(v___x_774_, 1);
lean_inc(v_res_775_);
v_pos_776_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_pos_776_);
lean_dec_ref_known(v___x_774_, 2);
v_fst_777_ = lean_ctor_get(v_res_775_, 0);
lean_inc(v_fst_777_);
v_snd_778_ = lean_ctor_get(v_res_775_, 1);
lean_inc(v_snd_778_);
lean_dec(v_res_775_);
v___x_779_ = l_Std_Http_Version_ofNumber_x3f(v_fst_777_, v_snd_778_);
lean_dec(v_snd_778_);
lean_dec(v_fst_777_);
v___x_780_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_779_, v_pos_776_);
lean_dec(v___x_779_);
return v___x_780_;
}
else
{
lean_object* v_pos_781_; lean_object* v_err_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
v_pos_781_ = lean_ctor_get(v___x_774_, 0);
v_err_782_ = lean_ctor_get(v___x_774_, 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_774_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_err_782_);
lean_inc(v_pos_781_);
lean_dec(v___x_774_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_pos_781_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_err_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0(size_t v_sz_830_, size_t v_i_831_, lean_object* v_bs_832_){
_start:
{
uint8_t v___x_833_; 
v___x_833_ = lean_usize_dec_lt(v_i_831_, v_sz_830_);
if (v___x_833_ == 0)
{
return v_bs_832_;
}
else
{
lean_object* v_v_834_; lean_object* v___x_835_; lean_object* v_bs_x27_836_; lean_object* v___y_838_; uint8_t v___x_847_; 
v_v_834_ = lean_array_uget(v_bs_832_, v_i_831_);
v___x_835_ = lean_unsigned_to_nat(0u);
v_bs_x27_836_ = lean_array_uset(v_bs_832_, v_i_831_, v___x_835_);
v___x_847_ = lean_unbox(v_v_834_);
switch(v___x_847_)
{
case 0:
{
lean_object* v___x_848_; 
v___x_848_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__0));
v___y_838_ = v___x_848_;
goto v___jp_837_;
}
case 1:
{
lean_object* v___x_849_; 
v___x_849_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__1));
v___y_838_ = v___x_849_;
goto v___jp_837_;
}
case 2:
{
lean_object* v___x_850_; 
v___x_850_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__2));
v___y_838_ = v___x_850_;
goto v___jp_837_;
}
case 3:
{
lean_object* v___x_851_; 
v___x_851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__3));
v___y_838_ = v___x_851_;
goto v___jp_837_;
}
case 4:
{
lean_object* v___x_852_; 
v___x_852_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__4));
v___y_838_ = v___x_852_;
goto v___jp_837_;
}
case 5:
{
lean_object* v___x_853_; 
v___x_853_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__5));
v___y_838_ = v___x_853_;
goto v___jp_837_;
}
case 6:
{
lean_object* v___x_854_; 
v___x_854_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__6));
v___y_838_ = v___x_854_;
goto v___jp_837_;
}
case 7:
{
lean_object* v___x_855_; 
v___x_855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__7));
v___y_838_ = v___x_855_;
goto v___jp_837_;
}
case 8:
{
lean_object* v___x_856_; 
v___x_856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__8));
v___y_838_ = v___x_856_;
goto v___jp_837_;
}
case 9:
{
lean_object* v___x_857_; 
v___x_857_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__9));
v___y_838_ = v___x_857_;
goto v___jp_837_;
}
case 10:
{
lean_object* v___x_858_; 
v___x_858_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__10));
v___y_838_ = v___x_858_;
goto v___jp_837_;
}
case 11:
{
lean_object* v___x_859_; 
v___x_859_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__11));
v___y_838_ = v___x_859_;
goto v___jp_837_;
}
case 12:
{
lean_object* v___x_860_; 
v___x_860_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__12));
v___y_838_ = v___x_860_;
goto v___jp_837_;
}
case 13:
{
lean_object* v___x_861_; 
v___x_861_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__13));
v___y_838_ = v___x_861_;
goto v___jp_837_;
}
case 14:
{
lean_object* v___x_862_; 
v___x_862_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__14));
v___y_838_ = v___x_862_;
goto v___jp_837_;
}
case 15:
{
lean_object* v___x_863_; 
v___x_863_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__15));
v___y_838_ = v___x_863_;
goto v___jp_837_;
}
case 16:
{
lean_object* v___x_864_; 
v___x_864_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__16));
v___y_838_ = v___x_864_;
goto v___jp_837_;
}
case 17:
{
lean_object* v___x_865_; 
v___x_865_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__17));
v___y_838_ = v___x_865_;
goto v___jp_837_;
}
case 18:
{
lean_object* v___x_866_; 
v___x_866_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__18));
v___y_838_ = v___x_866_;
goto v___jp_837_;
}
case 19:
{
lean_object* v___x_867_; 
v___x_867_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__19));
v___y_838_ = v___x_867_;
goto v___jp_837_;
}
case 20:
{
lean_object* v___x_868_; 
v___x_868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__20));
v___y_838_ = v___x_868_;
goto v___jp_837_;
}
case 21:
{
lean_object* v___x_869_; 
v___x_869_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__21));
v___y_838_ = v___x_869_;
goto v___jp_837_;
}
case 22:
{
lean_object* v___x_870_; 
v___x_870_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__22));
v___y_838_ = v___x_870_;
goto v___jp_837_;
}
case 23:
{
lean_object* v___x_871_; 
v___x_871_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__23));
v___y_838_ = v___x_871_;
goto v___jp_837_;
}
case 24:
{
lean_object* v___x_872_; 
v___x_872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__24));
v___y_838_ = v___x_872_;
goto v___jp_837_;
}
case 25:
{
lean_object* v___x_873_; 
v___x_873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__25));
v___y_838_ = v___x_873_;
goto v___jp_837_;
}
case 26:
{
lean_object* v___x_874_; 
v___x_874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__26));
v___y_838_ = v___x_874_;
goto v___jp_837_;
}
case 27:
{
lean_object* v___x_875_; 
v___x_875_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__27));
v___y_838_ = v___x_875_;
goto v___jp_837_;
}
case 28:
{
lean_object* v___x_876_; 
v___x_876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__28));
v___y_838_ = v___x_876_;
goto v___jp_837_;
}
case 29:
{
lean_object* v___x_877_; 
v___x_877_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__29));
v___y_838_ = v___x_877_;
goto v___jp_837_;
}
case 30:
{
lean_object* v___x_878_; 
v___x_878_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__30));
v___y_838_ = v___x_878_;
goto v___jp_837_;
}
case 31:
{
lean_object* v___x_879_; 
v___x_879_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__31));
v___y_838_ = v___x_879_;
goto v___jp_837_;
}
case 32:
{
lean_object* v___x_880_; 
v___x_880_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__32));
v___y_838_ = v___x_880_;
goto v___jp_837_;
}
case 33:
{
lean_object* v___x_881_; 
v___x_881_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__33));
v___y_838_ = v___x_881_;
goto v___jp_837_;
}
case 34:
{
lean_object* v___x_882_; 
v___x_882_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__34));
v___y_838_ = v___x_882_;
goto v___jp_837_;
}
case 35:
{
lean_object* v___x_883_; 
v___x_883_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__35));
v___y_838_ = v___x_883_;
goto v___jp_837_;
}
case 36:
{
lean_object* v___x_884_; 
v___x_884_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__36));
v___y_838_ = v___x_884_;
goto v___jp_837_;
}
case 37:
{
lean_object* v___x_885_; 
v___x_885_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__37));
v___y_838_ = v___x_885_;
goto v___jp_837_;
}
case 38:
{
lean_object* v___x_886_; 
v___x_886_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__38));
v___y_838_ = v___x_886_;
goto v___jp_837_;
}
default: 
{
lean_object* v___x_887_; 
v___x_887_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___closed__39));
v___y_838_ = v___x_887_;
goto v___jp_837_;
}
}
v___jp_837_:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; size_t v___x_843_; size_t v___x_844_; lean_object* v___x_845_; 
lean_inc_ref(v___y_838_);
v___x_839_ = lean_string_to_utf8(v___y_838_);
v___x_840_ = lean_byte_array_size(v___x_839_);
v___x_841_ = l_ByteArray_toByteSlice(v___x_839_, v___x_835_, v___x_840_);
v___x_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
lean_ctor_set(v___x_842_, 1, v_v_834_);
v___x_843_ = ((size_t)1ULL);
v___x_844_ = lean_usize_add(v_i_831_, v___x_843_);
v___x_845_ = lean_array_uset(v_bs_x27_836_, v_i_831_, v___x_842_);
v_i_831_ = v___x_844_;
v_bs_832_ = v___x_845_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0___boxed(lean_object* v_sz_888_, lean_object* v_i_889_, lean_object* v_bs_890_){
_start:
{
size_t v_sz_boxed_891_; size_t v_i_boxed_892_; lean_object* v_res_893_; 
v_sz_boxed_891_ = lean_unbox_usize(v_sz_888_);
lean_dec(v_sz_888_);
v_i_boxed_892_ = lean_unbox_usize(v_i_889_);
lean_dec(v_i_889_);
v_res_893_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0(v_sz_boxed_891_, v_i_boxed_892_, v_bs_890_);
return v_res_893_;
}
}
static size_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods___closed__0(void){
_start:
{
lean_object* v___x_894_; size_t v_sz_895_; 
v___x_894_ = l_Std_Http_Method_all;
v_sz_895_ = lean_array_size(v___x_894_);
return v_sz_895_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods___closed__1(void){
_start:
{
lean_object* v___x_896_; size_t v___x_897_; size_t v_sz_898_; lean_object* v___x_899_; 
v___x_896_ = l_Std_Http_Method_all;
v___x_897_ = ((size_t)0ULL);
v_sz_898_ = lean_usize_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods___closed__0, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods___closed__0);
v___x_899_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods_spec__0(v_sz_898_, v___x_897_, v___x_896_);
return v___x_899_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods(void){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods___closed__1);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0(lean_object* v___x_904_, lean_object* v_as_905_, size_t v_sz_906_, size_t v_i_907_, lean_object* v_b_908_){
_start:
{
lean_object* v_a_910_; uint8_t v___x_914_; 
v___x_914_ = lean_usize_dec_lt(v_i_907_, v_sz_906_);
if (v___x_914_ == 0)
{
lean_inc_ref(v_b_908_);
return v_b_908_;
}
else
{
lean_object* v_a_915_; lean_object* v_fst_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
v_a_915_ = lean_array_uget_borrowed(v_as_905_, v_i_907_);
v_fst_916_ = lean_ctor_get(v_a_915_, 0);
v___x_917_ = lean_box(0);
v___x_918_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___closed__0));
v___x_919_ = l_ByteSlice_size(v_fst_916_);
v___x_920_ = l_ByteSlice_size(v___x_904_);
v___x_921_ = lean_nat_dec_eq(v___x_919_, v___x_920_);
lean_dec(v___x_920_);
lean_dec(v___x_919_);
if (v___x_921_ == 0)
{
v_a_910_ = v___x_918_;
goto v___jp_909_;
}
else
{
uint8_t v___x_922_; 
v___x_922_ = lean_byteslice_beq(v_fst_916_, v___x_904_);
if (v___x_922_ == 0)
{
v_a_910_ = v___x_918_;
goto v___jp_909_;
}
else
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
lean_inc(v_a_915_);
v___x_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_923_, 0, v_a_915_);
v___x_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set(v___x_925_, 1, v___x_917_);
return v___x_925_;
}
}
}
v___jp_909_:
{
size_t v___x_911_; size_t v___x_912_; 
v___x_911_ = ((size_t)1ULL);
v___x_912_ = lean_usize_add(v_i_907_, v___x_911_);
v_i_907_ = v___x_912_;
v_b_908_ = v_a_910_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___boxed(lean_object* v___x_926_, lean_object* v_as_927_, lean_object* v_sz_928_, lean_object* v_i_929_, lean_object* v_b_930_){
_start:
{
size_t v_sz_boxed_931_; size_t v_i_boxed_932_; lean_object* v_res_933_; 
v_sz_boxed_931_ = lean_unbox_usize(v_sz_928_);
lean_dec(v_sz_928_);
v_i_boxed_932_ = lean_unbox_usize(v_i_929_);
lean_dec(v_i_929_);
v_res_933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0(v___x_926_, v_as_927_, v_sz_boxed_931_, v_i_boxed_932_, v_b_930_);
lean_dec_ref(v_b_930_);
lean_dec_ref(v_as_927_);
lean_dec_ref(v___x_926_);
return v_res_933_;
}
}
static size_t _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4(void){
_start:
{
lean_object* v___x_940_; size_t v_sz_941_; 
v___x_940_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods;
v_sz_941_ = lean_array_size(v___x_940_);
return v_sz_941_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(lean_object* v_a_942_){
_start:
{
lean_object* v___f_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v_snd_947_; lean_object* v_fst_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_1060_; 
v___f_943_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_944_ = lean_unsigned_to_nat(64u);
v___x_945_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_942_);
v___x_946_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_943_, v___x_944_, v___x_945_, v_a_942_);
v_snd_947_ = lean_ctor_get(v___x_946_, 1);
v_fst_948_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_950_ = v___x_946_;
v_isShared_951_ = v_isSharedCheck_1060_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_snd_947_);
lean_inc(v_fst_948_);
lean_dec(v___x_946_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_1060_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v_fst_952_; lean_object* v_snd_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_1059_; 
v_fst_952_ = lean_ctor_get(v_snd_947_, 0);
v_snd_953_ = lean_ctor_get(v_snd_947_, 1);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_snd_947_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_955_ = v_snd_947_;
v_isShared_956_ = v_isSharedCheck_1059_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_snd_953_);
lean_inc(v_fst_952_);
lean_dec(v_snd_947_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_1059_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
uint32_t v___y_968_; uint32_t v___y_974_; uint8_t v___x_1024_; 
v___x_1024_ = lean_unbox(v_snd_953_);
lean_dec(v_snd_953_);
if (v___x_1024_ == 0)
{
uint8_t v___x_1025_; 
v___x_1025_ = lean_nat_dec_eq(v_fst_948_, v___x_945_);
if (v___x_1025_ == 0)
{
lean_object* v_array_1026_; lean_object* v_idx_1027_; lean_object* v_lower_1029_; lean_object* v_upper_1030_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___y_1052_; uint8_t v___x_1054_; 
v_array_1026_ = lean_ctor_get(v_a_942_, 0);
lean_inc_ref(v_array_1026_);
v_idx_1027_ = lean_ctor_get(v_a_942_, 1);
lean_inc(v_idx_1027_);
lean_dec_ref(v_a_942_);
v___x_1049_ = lean_nat_add(v_idx_1027_, v_fst_948_);
lean_dec(v_fst_948_);
v___x_1050_ = lean_byte_array_size(v_array_1026_);
v___x_1054_ = lean_nat_dec_le(v_idx_1027_, v___x_945_);
if (v___x_1054_ == 0)
{
v___y_1052_ = v_idx_1027_;
goto v___jp_1051_;
}
else
{
lean_dec(v_idx_1027_);
v___y_1052_ = v___x_945_;
goto v___jp_1051_;
}
v___jp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; size_t v_sz_1034_; size_t v___x_1035_; lean_object* v___x_1036_; lean_object* v_fst_1037_; 
v___x_1031_ = l_ByteArray_toByteSlice(v_array_1026_, v_lower_1029_, v_upper_1030_);
v___x_1032_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_knownMethods;
v___x_1033_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___closed__0));
v_sz_1034_ = lean_usize_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4);
v___x_1035_ = ((size_t)0ULL);
v___x_1036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0(v___x_1031_, v___x_1032_, v_sz_1034_, v___x_1035_, v___x_1033_);
lean_dec_ref(v___x_1031_);
v_fst_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_fst_1037_);
lean_dec_ref(v___x_1036_);
if (lean_obj_tag(v_fst_1037_) == 0)
{
goto v___jp_979_;
}
else
{
lean_object* v_val_1038_; 
v_val_1038_ = lean_ctor_get(v_fst_1037_, 0);
lean_inc(v_val_1038_);
lean_dec_ref_known(v_fst_1037_, 1);
if (lean_obj_tag(v_val_1038_) == 0)
{
goto v___jp_979_;
}
else
{
lean_object* v_val_1039_; lean_object* v_snd_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_del_object(v___x_955_);
lean_del_object(v___x_950_);
v_val_1039_ = lean_ctor_get(v_val_1038_, 0);
lean_inc(v_val_1039_);
lean_dec_ref_known(v_val_1038_, 1);
v_snd_1040_ = lean_ctor_get(v_val_1039_, 1);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_val_1039_);
if (v_isSharedCheck_1047_ == 0)
{
lean_object* v_unused_1048_; 
v_unused_1048_ = lean_ctor_get(v_val_1039_, 0);
lean_dec(v_unused_1048_);
v___x_1042_ = v_val_1039_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_snd_1040_);
lean_dec(v_val_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v_fst_952_);
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_fst_952_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_snd_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
}
v___jp_1051_:
{
uint8_t v___x_1053_; 
v___x_1053_ = lean_nat_dec_le(v___x_1049_, v___x_1050_);
if (v___x_1053_ == 0)
{
lean_dec(v___x_1049_);
v_lower_1029_ = v___y_1052_;
v_upper_1030_ = v___x_1050_;
goto v___jp_1028_;
}
else
{
v_lower_1029_ = v___y_1052_;
v_upper_1030_ = v___x_1049_;
goto v___jp_1028_;
}
}
}
else
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
lean_del_object(v___x_955_);
lean_dec(v_fst_952_);
lean_del_object(v___x_950_);
lean_dec(v_fst_948_);
v___x_1055_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
v___x_1056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1056_, 0, v_a_942_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
return v___x_1056_;
}
}
else
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
lean_del_object(v___x_955_);
lean_del_object(v___x_950_);
lean_dec(v_fst_948_);
lean_dec_ref(v_a_942_);
v___x_1057_ = lean_box(0);
v___x_1058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1058_, 0, v_fst_952_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
return v___x_1058_;
}
v___jp_957_:
{
lean_object* v___x_958_; lean_object* v___x_960_; 
v___x_958_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__1));
if (v_isShared_956_ == 0)
{
lean_ctor_set_tag(v___x_955_, 1);
lean_ctor_set(v___x_955_, 1, v___x_958_);
v___x_960_ = v___x_955_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_fst_952_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v___x_958_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
v___jp_962_:
{
lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_963_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3));
if (v_isShared_951_ == 0)
{
lean_ctor_set_tag(v___x_950_, 1);
lean_ctor_set(v___x_950_, 1, v___x_963_);
lean_ctor_set(v___x_950_, 0, v_fst_952_);
v___x_965_ = v___x_950_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_fst_952_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
v___jp_967_:
{
uint32_t v___x_969_; uint8_t v___x_970_; 
v___x_969_ = 97;
v___x_970_ = lean_uint32_dec_le(v___x_969_, v___y_968_);
if (v___x_970_ == 0)
{
lean_del_object(v___x_950_);
goto v___jp_957_;
}
else
{
uint32_t v___x_971_; uint8_t v___x_972_; 
v___x_971_ = 122;
v___x_972_ = lean_uint32_dec_le(v___y_968_, v___x_971_);
if (v___x_972_ == 0)
{
lean_del_object(v___x_950_);
goto v___jp_957_;
}
else
{
lean_del_object(v___x_955_);
goto v___jp_962_;
}
}
}
v___jp_973_:
{
uint32_t v___x_975_; uint8_t v___x_976_; 
v___x_975_ = 65;
v___x_976_ = lean_uint32_dec_le(v___x_975_, v___y_974_);
if (v___x_976_ == 0)
{
v___y_968_ = v___y_974_;
goto v___jp_967_;
}
else
{
uint32_t v___x_977_; uint8_t v___x_978_; 
v___x_977_ = 90;
v___x_978_ = lean_uint32_dec_le(v___y_974_, v___x_977_);
if (v___x_978_ == 0)
{
v___y_968_ = v___y_974_;
goto v___jp_967_;
}
else
{
lean_del_object(v___x_955_);
goto v___jp_962_;
}
}
}
v___jp_979_:
{
lean_object* v_array_980_; lean_object* v_idx_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v_array_980_ = lean_ctor_get(v_fst_952_, 0);
v_idx_981_ = lean_ctor_get(v_fst_952_, 1);
v___x_982_ = lean_byte_array_size(v_array_980_);
v___x_983_ = lean_nat_dec_lt(v_idx_981_, v___x_982_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; lean_object* v___x_985_; 
lean_del_object(v___x_955_);
lean_del_object(v___x_950_);
v___x_984_ = lean_box(0);
v___x_985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_985_, 0, v_fst_952_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
return v___x_985_;
}
else
{
uint8_t v___x_986_; uint8_t v___x_987_; uint8_t v___x_988_; 
v___x_986_ = lean_byte_array_fget(v_array_980_, v_idx_981_);
v___x_987_ = 32;
v___x_988_ = lean_uint8_dec_eq(v___x_986_, v___x_987_);
if (v___x_988_ == 0)
{
uint32_t v___x_989_; uint32_t v___x_990_; uint8_t v___x_991_; 
v___x_989_ = lean_uint8_to_uint32(v___x_986_);
v___x_990_ = 33;
v___x_991_ = lean_uint32_dec_eq(v___x_989_, v___x_990_);
if (v___x_991_ == 0)
{
uint32_t v___x_992_; uint8_t v___x_993_; 
v___x_992_ = 35;
v___x_993_ = lean_uint32_dec_eq(v___x_989_, v___x_992_);
if (v___x_993_ == 0)
{
uint32_t v___x_994_; uint8_t v___x_995_; 
v___x_994_ = 36;
v___x_995_ = lean_uint32_dec_eq(v___x_989_, v___x_994_);
if (v___x_995_ == 0)
{
uint32_t v___x_996_; uint8_t v___x_997_; 
v___x_996_ = 37;
v___x_997_ = lean_uint32_dec_eq(v___x_989_, v___x_996_);
if (v___x_997_ == 0)
{
uint32_t v___x_998_; uint8_t v___x_999_; 
v___x_998_ = 38;
v___x_999_ = lean_uint32_dec_eq(v___x_989_, v___x_998_);
if (v___x_999_ == 0)
{
uint32_t v___x_1000_; uint8_t v___x_1001_; 
v___x_1000_ = 39;
v___x_1001_ = lean_uint32_dec_eq(v___x_989_, v___x_1000_);
if (v___x_1001_ == 0)
{
uint32_t v___x_1002_; uint8_t v___x_1003_; 
v___x_1002_ = 42;
v___x_1003_ = lean_uint32_dec_eq(v___x_989_, v___x_1002_);
if (v___x_1003_ == 0)
{
uint32_t v___x_1004_; uint8_t v___x_1005_; 
v___x_1004_ = 43;
v___x_1005_ = lean_uint32_dec_eq(v___x_989_, v___x_1004_);
if (v___x_1005_ == 0)
{
uint32_t v___x_1006_; uint8_t v___x_1007_; 
v___x_1006_ = 45;
v___x_1007_ = lean_uint32_dec_eq(v___x_989_, v___x_1006_);
if (v___x_1007_ == 0)
{
uint32_t v___x_1008_; uint8_t v___x_1009_; 
v___x_1008_ = 46;
v___x_1009_ = lean_uint32_dec_eq(v___x_989_, v___x_1008_);
if (v___x_1009_ == 0)
{
uint32_t v___x_1010_; uint8_t v___x_1011_; 
v___x_1010_ = 94;
v___x_1011_ = lean_uint32_dec_eq(v___x_989_, v___x_1010_);
if (v___x_1011_ == 0)
{
uint32_t v___x_1012_; uint8_t v___x_1013_; 
v___x_1012_ = 95;
v___x_1013_ = lean_uint32_dec_eq(v___x_989_, v___x_1012_);
if (v___x_1013_ == 0)
{
uint32_t v___x_1014_; uint8_t v___x_1015_; 
v___x_1014_ = 96;
v___x_1015_ = lean_uint32_dec_eq(v___x_989_, v___x_1014_);
if (v___x_1015_ == 0)
{
uint32_t v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = 124;
v___x_1017_ = lean_uint32_dec_eq(v___x_989_, v___x_1016_);
if (v___x_1017_ == 0)
{
uint32_t v___x_1018_; uint8_t v___x_1019_; 
v___x_1018_ = 126;
v___x_1019_ = lean_uint32_dec_eq(v___x_989_, v___x_1018_);
if (v___x_1019_ == 0)
{
uint32_t v___x_1020_; uint8_t v___x_1021_; 
v___x_1020_ = 48;
v___x_1021_ = lean_uint32_dec_le(v___x_1020_, v___x_989_);
if (v___x_1021_ == 0)
{
v___y_974_ = v___x_989_;
goto v___jp_973_;
}
else
{
uint32_t v___x_1022_; uint8_t v___x_1023_; 
v___x_1022_ = 57;
v___x_1023_ = lean_uint32_dec_le(v___x_989_, v___x_1022_);
if (v___x_1023_ == 0)
{
v___y_974_ = v___x_989_;
goto v___jp_973_;
}
else
{
lean_del_object(v___x_955_);
goto v___jp_962_;
}
}
}
else
{
lean_del_object(v___x_955_);
goto v___jp_962_;
}
}
else
{
lean_del_object(v___x_955_);
goto v___jp_962_;
}
}
else
{
lean_del_object(v___x_955_);
goto v___jp_962_;
}
}
else
{
lean_del_object(v___x_955_);
goto v___jp_962_;
}
}
else
{
lean_del_object(v___x_955_);
goto v___jp_962_;
}
}
else
{
lean_del_object(v___x_955_);
goto v___jp_962_;
}
}
else
{
lean_del_object(v___x_955_);
goto v___jp_962_;
}
}
else
{
lean_del_object(v___x_955_);
goto v___jp_962_;
}
}
else
{
lean_del_object(v___x_955_);
goto v___jp_962_;
}
}
else
{
lean_del_object(v___x_955_);
goto v___jp_962_;
}
}
else
{
lean_del_object(v___x_955_);
goto v___jp_962_;
}
}
else
{
lean_del_object(v___x_955_);
goto v___jp_962_;
}
}
else
{
lean_del_object(v___x_955_);
goto v___jp_962_;
}
}
else
{
lean_del_object(v___x_955_);
goto v___jp_962_;
}
}
else
{
lean_del_object(v___x_955_);
goto v___jp_962_;
}
}
else
{
lean_del_object(v___x_955_);
goto v___jp_962_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(uint8_t v_b_1061_){
_start:
{
uint8_t v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = 32;
v___x_1063_ = lean_uint8_dec_eq(v_b_1061_, v___x_1062_);
if (v___x_1063_ == 0)
{
uint8_t v___x_1064_; 
v___x_1064_ = 1;
return v___x_1064_;
}
else
{
uint8_t v___x_1065_; 
v___x_1065_ = 0;
return v___x_1065_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0___boxed(lean_object* v_b_1066_){
_start:
{
uint8_t v_b_boxed_1067_; uint8_t v_res_1068_; lean_object* v_r_1069_; 
v_b_boxed_1067_ = lean_unbox(v_b_1066_);
v_res_1068_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(v_b_boxed_1067_);
v_r_1069_ = lean_box(v_res_1068_);
return v_r_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(lean_object* v_limits_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v_maxUriLength_1081_; lean_object* v___f_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v_snd_1085_; lean_object* v_snd_1086_; uint8_t v___x_1087_; 
v_maxUriLength_1081_ = lean_ctor_get(v_limits_1074_, 4);
v___f_1082_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__0));
v___x_1083_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1075_);
v___x_1084_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1082_, v_maxUriLength_1081_, v___x_1083_, v_a_1075_);
v_snd_1085_ = lean_ctor_get(v___x_1084_, 1);
lean_inc(v_snd_1085_);
v_snd_1086_ = lean_ctor_get(v_snd_1085_, 1);
v___x_1087_ = lean_unbox(v_snd_1086_);
if (v___x_1087_ == 0)
{
lean_object* v_fst_1088_; lean_object* v_fst_1089_; lean_object* v_array_1090_; lean_object* v_idx_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1118_; 
v_fst_1088_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_fst_1088_);
lean_dec_ref(v___x_1084_);
v_fst_1089_ = lean_ctor_get(v_snd_1085_, 0);
lean_inc(v_fst_1089_);
lean_dec(v_snd_1085_);
v_array_1090_ = lean_ctor_get(v_a_1075_, 0);
v_idx_1091_ = lean_ctor_get(v_a_1075_, 1);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_a_1075_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1093_ = v_a_1075_;
v_isShared_1094_ = v_isSharedCheck_1118_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_idx_1091_);
lean_inc(v_array_1090_);
lean_dec(v_a_1075_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1118_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v_lower_1096_; lean_object* v_upper_1097_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___y_1115_; uint8_t v___x_1117_; 
v___x_1112_ = lean_nat_add(v_idx_1091_, v_fst_1088_);
lean_dec(v_fst_1088_);
v___x_1113_ = lean_byte_array_size(v_array_1090_);
v___x_1117_ = lean_nat_dec_le(v_idx_1091_, v___x_1083_);
if (v___x_1117_ == 0)
{
v___y_1115_ = v_idx_1091_;
goto v___jp_1114_;
}
else
{
lean_dec(v_idx_1091_);
v___y_1115_ = v___x_1083_;
goto v___jp_1114_;
}
v___jp_1095_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1098_ = l_ByteArray_toByteSlice(v_array_1090_, v_lower_1096_, v_upper_1097_);
v___x_1099_ = l_ByteSlice_size(v___x_1098_);
v___x_1100_ = lean_nat_dec_eq(v___x_1099_, v_maxUriLength_1081_);
lean_dec(v___x_1099_);
if (v___x_1100_ == 0)
{
lean_del_object(v___x_1093_);
v___y_1077_ = v___x_1098_;
v___y_1078_ = v_fst_1089_;
goto v___jp_1076_;
}
else
{
lean_object* v_array_1101_; lean_object* v_idx_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v_array_1101_ = lean_ctor_get(v_fst_1089_, 0);
v_idx_1102_ = lean_ctor_get(v_fst_1089_, 1);
v___x_1103_ = lean_byte_array_size(v_array_1101_);
v___x_1104_ = lean_nat_dec_lt(v_idx_1102_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_del_object(v___x_1093_);
v___y_1077_ = v___x_1098_;
v___y_1078_ = v_fst_1089_;
goto v___jp_1076_;
}
else
{
uint8_t v___x_1105_; uint8_t v___x_1106_; uint8_t v___x_1107_; 
v___x_1105_ = lean_byte_array_fget(v_array_1101_, v_idx_1102_);
v___x_1106_ = 32;
v___x_1107_ = lean_uint8_dec_eq(v___x_1105_, v___x_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1110_; 
lean_dec_ref(v___x_1098_);
v___x_1108_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__2));
if (v_isShared_1094_ == 0)
{
lean_ctor_set_tag(v___x_1093_, 1);
lean_ctor_set(v___x_1093_, 1, v___x_1108_);
lean_ctor_set(v___x_1093_, 0, v_fst_1089_);
v___x_1110_ = v___x_1093_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_fst_1089_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
else
{
lean_del_object(v___x_1093_);
v___y_1077_ = v___x_1098_;
v___y_1078_ = v_fst_1089_;
goto v___jp_1076_;
}
}
}
}
v___jp_1114_:
{
uint8_t v___x_1116_; 
v___x_1116_ = lean_nat_dec_le(v___x_1112_, v___x_1113_);
if (v___x_1116_ == 0)
{
lean_dec(v___x_1112_);
v_lower_1096_ = v___y_1115_;
v_upper_1097_ = v___x_1113_;
goto v___jp_1095_;
}
else
{
v_lower_1096_ = v___y_1115_;
v_upper_1097_ = v___x_1112_;
goto v___jp_1095_;
}
}
}
}
else
{
lean_object* v_fst_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1127_; 
lean_dec_ref(v___x_1084_);
lean_dec_ref(v_a_1075_);
v_fst_1119_ = lean_ctor_get(v_snd_1085_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_snd_1085_);
if (v_isSharedCheck_1127_ == 0)
{
lean_object* v_unused_1128_; 
v_unused_1128_ = lean_ctor_get(v_snd_1085_, 1);
lean_dec(v_unused_1128_);
v___x_1121_ = v_snd_1085_;
v_isShared_1122_ = v_isSharedCheck_1127_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_fst_1119_);
lean_dec(v_snd_1085_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1127_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1125_; 
v___x_1123_ = lean_box(0);
if (v_isShared_1122_ == 0)
{
lean_ctor_set_tag(v___x_1121_, 1);
lean_ctor_set(v___x_1121_, 1, v___x_1123_);
v___x_1125_ = v___x_1121_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_fst_1119_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
v___jp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = l_ByteSlice_toByteArray(v___y_1077_);
v___x_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___y_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
return v___x_1080_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___boxed(lean_object* v_limits_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_1129_, v_a_1130_);
lean_dec_ref(v_limits_1129_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_requestTargetConfig(lean_object* v_limits_1132_){
_start:
{
lean_object* v_maxUriLength_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v_maxUriLength_1133_ = lean_ctor_get(v_limits_1132_, 4);
v___x_1134_ = lean_unsigned_to_nat(253u);
lean_inc_n(v_maxUriLength_1133_, 8);
v___x_1135_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1135_, 0, v_maxUriLength_1133_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
lean_ctor_set(v___x_1135_, 2, v_maxUriLength_1133_);
lean_ctor_set(v___x_1135_, 3, v_maxUriLength_1133_);
lean_ctor_set(v___x_1135_, 4, v_maxUriLength_1133_);
lean_ctor_set(v___x_1135_, 5, v_maxUriLength_1133_);
lean_ctor_set(v___x_1135_, 6, v_maxUriLength_1133_);
lean_ctor_set(v___x_1135_, 7, v_maxUriLength_1133_);
lean_ctor_set(v___x_1135_, 8, v_maxUriLength_1133_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_requestTargetConfig___boxed(lean_object* v_limits_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_requestTargetConfig(v_limits_1136_);
lean_dec_ref(v_limits_1136_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0(lean_object* v___x_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_1141_, v___y_1142_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_pos_1144_; lean_object* v_array_1145_; lean_object* v_idx_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v_pos_1144_ = lean_ctor_get(v___x_1143_, 0);
v_array_1145_ = lean_ctor_get(v_pos_1144_, 0);
v_idx_1146_ = lean_ctor_get(v_pos_1144_, 1);
v___x_1147_ = lean_byte_array_size(v_array_1145_);
v___x_1148_ = lean_nat_dec_lt(v_idx_1146_, v___x_1147_);
if (v___x_1148_ == 0)
{
return v___x_1143_;
}
else
{
lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1156_; 
lean_inc(v_pos_1144_);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1156_ == 0)
{
lean_object* v_unused_1157_; lean_object* v_unused_1158_; 
v_unused_1157_ = lean_ctor_get(v___x_1143_, 1);
lean_dec(v_unused_1157_);
v_unused_1158_ = lean_ctor_get(v___x_1143_, 0);
lean_dec(v_unused_1158_);
v___x_1150_ = v___x_1143_;
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
else
{
lean_dec(v___x_1143_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1152_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__1));
if (v_isShared_1151_ == 0)
{
lean_ctor_set_tag(v___x_1150_, 1);
lean_ctor_set(v___x_1150_, 1, v___x_1152_);
v___x_1154_ = v___x_1150_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_pos_1144_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
else
{
return v___x_1143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(lean_object* v_limits_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_1159_, v_a_1160_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_pos_1162_; lean_object* v_res_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1241_; 
v_pos_1162_ = lean_ctor_get(v___x_1161_, 0);
v_res_1163_ = lean_ctor_get(v___x_1161_, 1);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1165_ = v___x_1161_;
v_isShared_1166_ = v_isSharedCheck_1241_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_res_1163_);
lean_inc(v_pos_1162_);
lean_dec(v___x_1161_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1241_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v_array_1167_; lean_object* v_idx_1168_; lean_object* v___x_1169_; uint8_t v___x_1170_; 
v_array_1167_ = lean_ctor_get(v_pos_1162_, 0);
v_idx_1168_ = lean_ctor_get(v_pos_1162_, 1);
v___x_1169_ = lean_byte_array_size(v_array_1167_);
v___x_1170_ = lean_nat_dec_lt(v_idx_1168_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1173_; 
lean_dec(v_res_1163_);
v___x_1171_ = lean_box(0);
if (v_isShared_1166_ == 0)
{
lean_ctor_set_tag(v___x_1165_, 1);
lean_ctor_set(v___x_1165_, 1, v___x_1171_);
v___x_1173_ = v___x_1165_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_pos_1162_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
else
{
uint8_t v___x_1175_; uint8_t v_got_1176_; uint8_t v___x_1177_; 
v___x_1175_ = 32;
v_got_1176_ = lean_byte_array_fget(v_array_1167_, v_idx_1168_);
v___x_1177_ = lean_uint8_dec_eq(v_got_1176_, v___x_1175_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
lean_dec(v_res_1163_);
v___x_1178_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_1166_ == 0)
{
lean_ctor_set_tag(v___x_1165_, 1);
lean_ctor_set(v___x_1165_, 1, v___x_1178_);
v___x_1180_ = v___x_1165_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_pos_1162_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
else
{
lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1238_; 
lean_inc(v_idx_1168_);
lean_inc_ref(v_array_1167_);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_pos_1162_);
if (v_isSharedCheck_1238_ == 0)
{
lean_object* v_unused_1239_; lean_object* v_unused_1240_; 
v_unused_1239_ = lean_ctor_get(v_pos_1162_, 1);
lean_dec(v_unused_1239_);
v_unused_1240_ = lean_ctor_get(v_pos_1162_, 0);
lean_dec(v_unused_1240_);
v___x_1183_ = v_pos_1162_;
v_isShared_1184_ = v_isSharedCheck_1238_;
goto v_resetjp_1182_;
}
else
{
lean_dec(v_pos_1162_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1238_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1185_ = lean_unsigned_to_nat(1u);
v___x_1186_ = lean_nat_add(v_idx_1168_, v___x_1185_);
lean_dec(v_idx_1168_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 1, v___x_1186_);
v___x_1188_ = v___x_1183_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_array_1167_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v___x_1186_);
v___x_1188_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1189_; lean_object* v___f_1190_; lean_object* v___x_1191_; 
v___x_1189_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_requestTargetConfig(v_limits_1159_);
v___f_1190_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0), 2, 1);
lean_closure_set(v___f_1190_, 0, v___x_1189_);
v___x_1191_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1190_, v_res_1163_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1202_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1202_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1202_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
lean_ctor_set_tag(v___x_1194_, 1);
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1199_; 
if (v_isShared_1166_ == 0)
{
lean_ctor_set_tag(v___x_1165_, 1);
lean_ctor_set(v___x_1165_, 1, v___x_1197_);
lean_ctor_set(v___x_1165_, 0, v___x_1188_);
v___x_1199_ = v___x_1165_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1204_; 
lean_del_object(v___x_1165_);
v_a_1203_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_a_1203_);
lean_dec_ref_known(v___x_1191_, 1);
v___x_1204_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v___x_1188_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_pos_1205_; lean_object* v_res_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v_pos_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_pos_1205_);
v_res_1206_ = lean_ctor_get(v___x_1204_, 1);
lean_inc(v_res_1206_);
lean_dec_ref_known(v___x_1204_, 2);
v___x_1207_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_1208_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_1207_, v_pos_1205_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_pos_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1217_; 
v_pos_1209_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; 
v_unused_1218_ = lean_ctor_get(v___x_1208_, 1);
lean_dec(v_unused_1218_);
v___x_1211_ = v___x_1208_;
v_isShared_1212_ = v_isSharedCheck_1217_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_pos_1209_);
lean_dec(v___x_1208_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1217_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1213_; lean_object* v___x_1215_; 
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v_a_1203_);
lean_ctor_set(v___x_1213_, 1, v_res_1206_);
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 1, v___x_1213_);
v___x_1215_ = v___x_1211_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_pos_1209_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
else
{
lean_object* v_pos_1219_; lean_object* v_err_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec(v_res_1206_);
lean_dec(v_a_1203_);
v_pos_1219_ = lean_ctor_get(v___x_1208_, 0);
v_err_1220_ = lean_ctor_get(v___x_1208_, 1);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1208_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_err_1220_);
lean_inc(v_pos_1219_);
lean_dec(v___x_1208_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_pos_1219_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_err_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
else
{
lean_object* v_pos_1228_; lean_object* v_err_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec(v_a_1203_);
v_pos_1228_ = lean_ctor_get(v___x_1204_, 0);
v_err_1229_ = lean_ctor_get(v___x_1204_, 1);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1204_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_err_1229_);
lean_inc(v_pos_1228_);
lean_dec(v___x_1204_);
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
}
}
}
}
else
{
lean_object* v_pos_1242_; lean_object* v_err_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
v_pos_1242_ = lean_ctor_get(v___x_1161_, 0);
v_err_1243_ = lean_ctor_get(v___x_1161_, 1);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1161_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_err_1243_);
lean_inc(v_pos_1242_);
lean_dec(v___x_1161_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_pos_1242_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_err_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___boxed(lean_object* v_limits_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_1251_, v_a_1252_);
lean_dec_ref(v_limits_1251_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine(lean_object* v_limits_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_pos_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1350_; 
v_pos_1260_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1350_ == 0)
{
lean_object* v_unused_1351_; 
v_unused_1351_ = lean_ctor_get(v___x_1259_, 1);
lean_dec(v_unused_1351_);
v___x_1262_ = v___x_1259_;
v_isShared_1263_ = v_isSharedCheck_1350_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_pos_1260_);
lean_dec(v___x_1259_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1350_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; 
v___x_1264_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(v_pos_1260_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_pos_1265_; lean_object* v_res_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1340_; 
v_pos_1265_ = lean_ctor_get(v___x_1264_, 0);
v_res_1266_ = lean_ctor_get(v___x_1264_, 1);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1268_ = v___x_1264_;
v_isShared_1269_ = v_isSharedCheck_1340_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_res_1266_);
lean_inc(v_pos_1265_);
lean_dec(v___x_1264_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1340_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v_array_1270_; lean_object* v_idx_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
v_array_1270_ = lean_ctor_get(v_pos_1265_, 0);
v_idx_1271_ = lean_ctor_get(v_pos_1265_, 1);
v___x_1272_ = lean_byte_array_size(v_array_1270_);
v___x_1273_ = lean_nat_dec_lt(v_idx_1271_, v___x_1272_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; lean_object* v___x_1276_; 
lean_dec(v_res_1266_);
lean_del_object(v___x_1262_);
v___x_1274_ = lean_box(0);
if (v_isShared_1269_ == 0)
{
lean_ctor_set_tag(v___x_1268_, 1);
lean_ctor_set(v___x_1268_, 1, v___x_1274_);
v___x_1276_ = v___x_1268_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_pos_1265_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
else
{
uint8_t v___x_1278_; uint8_t v_got_1279_; uint8_t v___x_1280_; 
v___x_1278_ = 32;
v_got_1279_ = lean_byte_array_fget(v_array_1270_, v_idx_1271_);
v___x_1280_ = lean_uint8_dec_eq(v_got_1279_, v___x_1278_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; lean_object* v___x_1283_; 
lean_dec(v_res_1266_);
lean_del_object(v___x_1262_);
v___x_1281_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_1269_ == 0)
{
lean_ctor_set_tag(v___x_1268_, 1);
lean_ctor_set(v___x_1268_, 1, v___x_1281_);
v___x_1283_ = v___x_1268_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_pos_1265_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
else
{
lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1337_; 
lean_inc(v_idx_1271_);
lean_inc_ref(v_array_1270_);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_pos_1265_);
if (v_isSharedCheck_1337_ == 0)
{
lean_object* v_unused_1338_; lean_object* v_unused_1339_; 
v_unused_1338_ = lean_ctor_get(v_pos_1265_, 1);
lean_dec(v_unused_1338_);
v_unused_1339_ = lean_ctor_get(v_pos_1265_, 0);
lean_dec(v_unused_1339_);
v___x_1286_ = v_pos_1265_;
v_isShared_1287_ = v_isSharedCheck_1337_;
goto v_resetjp_1285_;
}
else
{
lean_dec(v_pos_1265_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1337_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1288_ = lean_unsigned_to_nat(1u);
v___x_1289_ = lean_nat_add(v_idx_1271_, v___x_1288_);
lean_dec(v_idx_1271_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 1, v___x_1289_);
v___x_1291_ = v___x_1286_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_array_1270_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
lean_object* v___x_1292_; 
v___x_1292_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_1257_, v___x_1291_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_pos_1293_; lean_object* v_res_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1326_; 
v_pos_1293_ = lean_ctor_get(v___x_1292_, 0);
v_res_1294_ = lean_ctor_get(v___x_1292_, 1);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1296_ = v___x_1292_;
v_isShared_1297_ = v_isSharedCheck_1326_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_res_1294_);
lean_inc(v_pos_1293_);
lean_dec(v___x_1292_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1326_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v_snd_1303_; lean_object* v_fst_1304_; lean_object* v_fst_1305_; lean_object* v_snd_1306_; uint8_t v___x_1307_; 
v_snd_1303_ = lean_ctor_get(v_res_1294_, 1);
lean_inc(v_snd_1303_);
v_fst_1304_ = lean_ctor_get(v_res_1294_, 0);
lean_inc(v_fst_1304_);
lean_dec(v_res_1294_);
v_fst_1305_ = lean_ctor_get(v_snd_1303_, 0);
lean_inc(v_fst_1305_);
v_snd_1306_ = lean_ctor_get(v_snd_1303_, 1);
lean_inc(v_snd_1306_);
lean_dec(v_snd_1303_);
v___x_1307_ = lean_nat_dec_eq(v_fst_1305_, v___x_1288_);
lean_dec(v_fst_1305_);
if (v___x_1307_ == 0)
{
lean_del_object(v___x_1262_);
goto v___jp_1308_;
}
else
{
uint8_t v___x_1318_; 
v___x_1318_ = lean_nat_dec_le(v___x_1288_, v_snd_1306_);
if (v___x_1318_ == 0)
{
lean_del_object(v___x_1262_);
goto v___jp_1308_;
}
else
{
uint8_t v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; lean_object* v___x_1324_; 
lean_dec(v_snd_1306_);
lean_del_object(v___x_1296_);
lean_del_object(v___x_1268_);
v___x_1319_ = 1;
v___x_1320_ = l_Std_Http_Headers_empty;
v___x_1321_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1321_, 0, v_fst_1304_);
lean_ctor_set(v___x_1321_, 1, v___x_1320_);
v___x_1322_ = lean_unbox(v_res_1266_);
lean_dec(v_res_1266_);
lean_ctor_set_uint8(v___x_1321_, sizeof(void*)*2, v___x_1322_);
lean_ctor_set_uint8(v___x_1321_, sizeof(void*)*2 + 1, v___x_1319_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 1, v___x_1321_);
lean_ctor_set(v___x_1262_, 0, v_pos_1293_);
v___x_1324_ = v___x_1262_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_pos_1293_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v___x_1321_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
v___jp_1298_:
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1299_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
if (v_isShared_1297_ == 0)
{
lean_ctor_set_tag(v___x_1296_, 1);
lean_ctor_set(v___x_1296_, 1, v___x_1299_);
v___x_1301_ = v___x_1296_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_pos_1293_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
v___jp_1308_:
{
if (v___x_1307_ == 0)
{
lean_dec(v_snd_1306_);
lean_dec(v_fst_1304_);
lean_del_object(v___x_1268_);
lean_dec(v_res_1266_);
goto v___jp_1298_;
}
else
{
lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1309_ = lean_unsigned_to_nat(0u);
v___x_1310_ = lean_nat_dec_eq(v_snd_1306_, v___x_1309_);
lean_dec(v_snd_1306_);
if (v___x_1310_ == 0)
{
lean_dec(v_fst_1304_);
lean_del_object(v___x_1268_);
lean_dec(v_res_1266_);
goto v___jp_1298_;
}
else
{
uint8_t v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; lean_object* v___x_1316_; 
lean_del_object(v___x_1296_);
v___x_1311_ = 0;
v___x_1312_ = l_Std_Http_Headers_empty;
v___x_1313_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1313_, 0, v_fst_1304_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = lean_unbox(v_res_1266_);
lean_dec(v_res_1266_);
lean_ctor_set_uint8(v___x_1313_, sizeof(void*)*2, v___x_1314_);
lean_ctor_set_uint8(v___x_1313_, sizeof(void*)*2 + 1, v___x_1311_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 1, v___x_1313_);
lean_ctor_set(v___x_1268_, 0, v_pos_1293_);
v___x_1316_ = v___x_1268_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_pos_1293_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v___x_1313_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1327_; lean_object* v_err_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_del_object(v___x_1268_);
lean_dec(v_res_1266_);
lean_del_object(v___x_1262_);
v_pos_1327_ = lean_ctor_get(v___x_1292_, 0);
v_err_1328_ = lean_ctor_get(v___x_1292_, 1);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1292_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_err_1328_);
lean_inc(v_pos_1327_);
lean_dec(v___x_1292_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_pos_1327_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_err_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
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
lean_object* v_pos_1341_; lean_object* v_err_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_del_object(v___x_1262_);
v_pos_1341_ = lean_ctor_get(v___x_1264_, 0);
v_err_1342_ = lean_ctor_get(v___x_1264_, 1);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1264_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_err_1342_);
lean_inc(v_pos_1341_);
lean_dec(v___x_1264_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_pos_1341_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_err_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
}
else
{
lean_object* v_pos_1352_; lean_object* v_err_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
v_pos_1352_ = lean_ctor_get(v___x_1259_, 0);
v_err_1353_ = lean_ctor_get(v___x_1259_, 1);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1259_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_err_1353_);
lean_inc(v_pos_1352_);
lean_dec(v___x_1259_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_pos_1352_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_err_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine___boxed(lean_object* v_limits_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Std_Http_Protocol_H1_parseRequestLine(v_limits_1361_, v_a_1362_);
lean_dec_ref(v_limits_1361_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion(lean_object* v_limits_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_1364_, v_a_1365_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_pos_1367_; lean_object* v___x_1368_; 
v_pos_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_pos_1367_);
lean_dec_ref_known(v___x_1366_, 2);
v___x_1368_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(v_pos_1367_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_pos_1369_; lean_object* v_res_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1444_; 
v_pos_1369_ = lean_ctor_get(v___x_1368_, 0);
v_res_1370_ = lean_ctor_get(v___x_1368_, 1);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1372_ = v___x_1368_;
v_isShared_1373_ = v_isSharedCheck_1444_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_res_1370_);
lean_inc(v_pos_1369_);
lean_dec(v___x_1368_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1444_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v_array_1374_; lean_object* v_idx_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
v_array_1374_ = lean_ctor_get(v_pos_1369_, 0);
v_idx_1375_ = lean_ctor_get(v_pos_1369_, 1);
v___x_1376_ = lean_byte_array_size(v_array_1374_);
v___x_1377_ = lean_nat_dec_lt(v_idx_1375_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1380_; 
lean_dec(v_res_1370_);
v___x_1378_ = lean_box(0);
if (v_isShared_1373_ == 0)
{
lean_ctor_set_tag(v___x_1372_, 1);
lean_ctor_set(v___x_1372_, 1, v___x_1378_);
v___x_1380_ = v___x_1372_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_pos_1369_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
else
{
uint8_t v___x_1382_; uint8_t v_got_1383_; uint8_t v___x_1384_; 
v___x_1382_ = 32;
v_got_1383_ = lean_byte_array_fget(v_array_1374_, v_idx_1375_);
v___x_1384_ = lean_uint8_dec_eq(v_got_1383_, v___x_1382_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; lean_object* v___x_1387_; 
lean_dec(v_res_1370_);
v___x_1385_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_1373_ == 0)
{
lean_ctor_set_tag(v___x_1372_, 1);
lean_ctor_set(v___x_1372_, 1, v___x_1385_);
v___x_1387_ = v___x_1372_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_pos_1369_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
else
{
lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1441_; 
lean_inc(v_idx_1375_);
lean_inc_ref(v_array_1374_);
lean_del_object(v___x_1372_);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_pos_1369_);
if (v_isSharedCheck_1441_ == 0)
{
lean_object* v_unused_1442_; lean_object* v_unused_1443_; 
v_unused_1442_ = lean_ctor_get(v_pos_1369_, 1);
lean_dec(v_unused_1442_);
v_unused_1443_ = lean_ctor_get(v_pos_1369_, 0);
lean_dec(v_unused_1443_);
v___x_1390_ = v_pos_1369_;
v_isShared_1391_ = v_isSharedCheck_1441_;
goto v_resetjp_1389_;
}
else
{
lean_dec(v_pos_1369_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1441_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1392_ = lean_unsigned_to_nat(1u);
v___x_1393_ = lean_nat_add(v_idx_1375_, v___x_1392_);
lean_dec(v_idx_1375_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 1, v___x_1393_);
v___x_1395_ = v___x_1390_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_array_1374_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1396_; 
v___x_1396_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_1364_, v___x_1395_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_res_1397_; lean_object* v_snd_1398_; lean_object* v_pos_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1429_; 
v_res_1397_ = lean_ctor_get(v___x_1396_, 1);
lean_inc(v_res_1397_);
v_snd_1398_ = lean_ctor_get(v_res_1397_, 1);
lean_inc(v_snd_1398_);
v_pos_1399_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; 
v_unused_1430_ = lean_ctor_get(v___x_1396_, 1);
lean_dec(v_unused_1430_);
v___x_1401_ = v___x_1396_;
v_isShared_1402_ = v_isSharedCheck_1429_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_pos_1399_);
lean_dec(v___x_1396_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1429_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v_fst_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1427_; 
v_fst_1403_ = lean_ctor_get(v_res_1397_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_res_1397_);
if (v_isSharedCheck_1427_ == 0)
{
lean_object* v_unused_1428_; 
v_unused_1428_ = lean_ctor_get(v_res_1397_, 1);
lean_dec(v_unused_1428_);
v___x_1405_ = v_res_1397_;
v_isShared_1406_ = v_isSharedCheck_1427_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_fst_1403_);
lean_dec(v_res_1397_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1427_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v_fst_1407_; lean_object* v_snd_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1426_; 
v_fst_1407_ = lean_ctor_get(v_snd_1398_, 0);
v_snd_1408_ = lean_ctor_get(v_snd_1398_, 1);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_snd_1398_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1410_ = v_snd_1398_;
v_isShared_1411_ = v_isSharedCheck_1426_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_snd_1408_);
lean_inc(v_fst_1407_);
lean_dec(v_snd_1398_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1426_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___y_1413_; uint8_t v___x_1424_; 
v___x_1424_ = lean_nat_dec_eq(v_fst_1407_, v___x_1392_);
if (v___x_1424_ == 0)
{
v___y_1413_ = v_snd_1408_;
goto v___jp_1412_;
}
else
{
uint8_t v___x_1425_; 
v___x_1425_ = lean_nat_dec_le(v_snd_1408_, v___x_1392_);
if (v___x_1425_ == 0)
{
lean_dec(v_snd_1408_);
v___y_1413_ = v___x_1392_;
goto v___jp_1412_;
}
else
{
v___y_1413_ = v_snd_1408_;
goto v___jp_1412_;
}
}
v___jp_1412_:
{
lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1414_ = l_Std_Http_Version_ofNumber_x3f(v_fst_1407_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec(v_fst_1407_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 1, v___x_1414_);
lean_ctor_set(v___x_1410_, 0, v_fst_1403_);
v___x_1416_ = v___x_1410_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_fst_1403_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1418_; 
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 1, v___x_1416_);
lean_ctor_set(v___x_1405_, 0, v_res_1370_);
v___x_1418_ = v___x_1405_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_res_1370_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1420_; 
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 1, v___x_1418_);
v___x_1420_ = v___x_1401_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_pos_1399_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v___x_1418_);
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
}
}
}
}
else
{
lean_object* v_pos_1431_; lean_object* v_err_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
lean_dec(v_res_1370_);
v_pos_1431_ = lean_ctor_get(v___x_1396_, 0);
v_err_1432_ = lean_ctor_get(v___x_1396_, 1);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1396_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_err_1432_);
lean_inc(v_pos_1431_);
lean_dec(v___x_1396_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_pos_1431_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_err_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
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
lean_object* v_pos_1445_; lean_object* v_err_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
v_pos_1445_ = lean_ctor_get(v___x_1368_, 0);
v_err_1446_ = lean_ctor_get(v___x_1368_, 1);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1368_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_err_1446_);
lean_inc(v_pos_1445_);
lean_dec(v___x_1368_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_pos_1445_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_err_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
else
{
lean_object* v_pos_1454_; lean_object* v_err_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
v_pos_1454_ = lean_ctor_get(v___x_1366_, 0);
v_err_1455_ = lean_ctor_get(v___x_1366_, 1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1366_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_err_1455_);
lean_inc(v_pos_1454_);
lean_dec(v___x_1366_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_pos_1454_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_err_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion___boxed(lean_object* v_limits_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Std_Http_Protocol_H1_parseRequestLineRawVersion(v_limits_1463_, v_a_1464_);
lean_dec_ref(v_limits_1463_);
return v_res_1465_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(uint8_t v___y_1466_){
_start:
{
uint32_t v___x_1467_; uint32_t v___x_1475_; uint8_t v___x_1476_; 
v___x_1467_ = lean_uint8_to_uint32(v___y_1466_);
v___x_1475_ = 33;
v___x_1476_ = lean_uint32_dec_le(v___x_1475_, v___x_1467_);
if (v___x_1476_ == 0)
{
goto v___jp_1468_;
}
else
{
uint32_t v___x_1477_; uint8_t v___x_1478_; 
v___x_1477_ = 126;
v___x_1478_ = lean_uint32_dec_le(v___x_1467_, v___x_1477_);
if (v___x_1478_ == 0)
{
goto v___jp_1468_;
}
else
{
return v___x_1478_;
}
}
v___jp_1468_:
{
uint32_t v___x_1469_; uint8_t v___x_1470_; 
v___x_1469_ = 128;
v___x_1470_ = lean_uint32_dec_le(v___x_1469_, v___x_1467_);
if (v___x_1470_ == 0)
{
uint32_t v___x_1471_; uint8_t v___x_1472_; 
v___x_1471_ = 32;
v___x_1472_ = lean_uint32_dec_eq(v___x_1467_, v___x_1471_);
if (v___x_1472_ == 0)
{
uint32_t v___x_1473_; uint8_t v___x_1474_; 
v___x_1473_ = 9;
v___x_1474_ = lean_uint32_dec_eq(v___x_1467_, v___x_1473_);
return v___x_1474_;
}
else
{
return v___x_1472_;
}
}
else
{
return v___x_1470_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed(lean_object* v___y_1479_){
_start:
{
uint8_t v___y_3635__boxed_1480_; uint8_t v_res_1481_; lean_object* v_r_1482_; 
v___y_3635__boxed_1480_ = lean_unbox(v___y_1479_);
v_res_1481_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(v___y_3635__boxed_1480_);
v_r_1482_ = lean_box(v_res_1481_);
return v_r_1482_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0(uint8_t v___y_1483_){
_start:
{
uint32_t v___x_1484_; uint32_t v___x_1485_; uint8_t v___x_1486_; 
v___x_1484_ = lean_uint8_to_uint32(v___y_1483_);
v___x_1485_ = 32;
v___x_1486_ = lean_uint32_dec_eq(v___x_1484_, v___x_1485_);
if (v___x_1486_ == 0)
{
uint32_t v___x_1487_; uint8_t v___x_1488_; 
v___x_1487_ = 9;
v___x_1488_ = lean_uint32_dec_eq(v___x_1484_, v___x_1487_);
return v___x_1488_;
}
else
{
return v___x_1486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0___boxed(lean_object* v___y_1489_){
_start:
{
uint8_t v___y_3662__boxed_1490_; uint8_t v_res_1491_; lean_object* v_r_1492_; 
v___y_3662__boxed_1490_ = lean_unbox(v___y_1489_);
v_res_1491_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0(v___y_3662__boxed_1490_);
v_r_1492_ = lean_box(v_res_1491_);
return v_r_1492_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(lean_object* v_s_1493_, lean_object* v_pos_1494_){
_start:
{
lean_object* v_str_1495_; lean_object* v_startInclusive_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; uint8_t v_decide_1500_; 
v_str_1495_ = lean_ctor_get(v_s_1493_, 0);
v_startInclusive_1496_ = lean_ctor_get(v_s_1493_, 1);
v___x_1497_ = lean_nat_add(v_startInclusive_1496_, v_pos_1494_);
v___x_1498_ = lean_nat_sub(v___x_1497_, v_startInclusive_1496_);
v___x_1499_ = lean_unsigned_to_nat(0u);
v_decide_1500_ = lean_nat_dec_eq(v___x_1498_, v___x_1499_);
if (v_decide_1500_ == 0)
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1509_; uint32_t v___x_1510_; uint32_t v___x_1511_; uint8_t v___x_1512_; 
lean_inc(v_startInclusive_1496_);
lean_inc_ref(v_str_1495_);
v___x_1501_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1501_, 0, v_str_1495_);
lean_ctor_set(v___x_1501_, 1, v_startInclusive_1496_);
lean_ctor_set(v___x_1501_, 2, v___x_1497_);
v___x_1502_ = lean_unsigned_to_nat(1u);
v___x_1503_ = lean_nat_sub(v___x_1498_, v___x_1502_);
lean_dec(v___x_1498_);
v___x_1504_ = l_String_Slice_posLE(v___x_1501_, v___x_1503_);
lean_dec_ref_known(v___x_1501_, 3);
v___x_1509_ = lean_nat_add(v_startInclusive_1496_, v___x_1504_);
v___x_1510_ = lean_string_utf8_get_fast(v_str_1495_, v___x_1509_);
lean_dec(v___x_1509_);
v___x_1511_ = 32;
v___x_1512_ = lean_uint32_dec_eq(v___x_1510_, v___x_1511_);
if (v___x_1512_ == 0)
{
uint32_t v___x_1513_; uint8_t v___x_1514_; 
v___x_1513_ = 9;
v___x_1514_ = lean_uint32_dec_eq(v___x_1510_, v___x_1513_);
if (v___x_1514_ == 0)
{
uint32_t v___x_1515_; uint8_t v___x_1516_; 
v___x_1515_ = 13;
v___x_1516_ = lean_uint32_dec_eq(v___x_1510_, v___x_1515_);
if (v___x_1516_ == 0)
{
uint32_t v___x_1517_; uint8_t v___x_1518_; 
v___x_1517_ = 10;
v___x_1518_ = lean_uint32_dec_eq(v___x_1510_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_dec(v___x_1504_);
return v_pos_1494_;
}
else
{
goto v___jp_1505_;
}
}
else
{
goto v___jp_1505_;
}
}
else
{
goto v___jp_1505_;
}
}
else
{
goto v___jp_1505_;
}
v___jp_1505_:
{
lean_object* v___x_1506_; uint8_t v___x_1507_; 
v___x_1506_ = lean_nat_add(v___x_1504_, v___x_1502_);
v___x_1507_ = lean_nat_dec_le(v___x_1506_, v_pos_1494_);
lean_dec(v___x_1506_);
if (v___x_1507_ == 0)
{
lean_dec(v___x_1504_);
return v_pos_1494_;
}
else
{
lean_dec(v_pos_1494_);
v_pos_1494_ = v___x_1504_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1498_);
lean_dec(v___x_1497_);
return v_pos_1494_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0___boxed(lean_object* v_s_1519_, lean_object* v_pos_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(v_s_1519_, v_pos_1520_);
lean_dec_ref(v_s_1519_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(lean_object* v_limits_1528_, lean_object* v_a_1529_){
_start:
{
lean_object* v_pos_1531_; lean_object* v_pos_1535_; lean_object* v_maxHeaderNameLength_1538_; lean_object* v_maxHeaderValueLength_1539_; lean_object* v_maxSpaceSequence_1540_; lean_object* v___f_1541_; lean_object* v___x_1542_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1578_; lean_object* v_pos_1579_; lean_object* v_res_1580_; lean_object* v___x_1586_; lean_object* v_snd_1587_; lean_object* v_snd_1588_; uint8_t v___x_1589_; 
v_maxHeaderNameLength_1538_ = lean_ctor_get(v_limits_1528_, 6);
v_maxHeaderValueLength_1539_ = lean_ctor_get(v_limits_1528_, 7);
v_maxSpaceSequence_1540_ = lean_ctor_get(v_limits_1528_, 8);
v___f_1541_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_1542_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1529_);
v___x_1586_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1541_, v_maxHeaderNameLength_1538_, v___x_1542_, v_a_1529_);
v_snd_1587_ = lean_ctor_get(v___x_1586_, 1);
lean_inc(v_snd_1587_);
v_snd_1588_ = lean_ctor_get(v_snd_1587_, 1);
v___x_1589_ = lean_unbox(v_snd_1588_);
if (v___x_1589_ == 0)
{
lean_object* v_fst_1590_; lean_object* v_fst_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1749_; 
v_fst_1590_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_fst_1590_);
lean_dec_ref(v___x_1586_);
v_fst_1591_ = lean_ctor_get(v_snd_1587_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v_snd_1587_);
if (v_isSharedCheck_1749_ == 0)
{
lean_object* v_unused_1750_; 
v_unused_1750_ = lean_ctor_get(v_snd_1587_, 1);
lean_dec(v_unused_1750_);
v___x_1593_ = v_snd_1587_;
v_isShared_1594_ = v_isSharedCheck_1749_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_fst_1591_);
lean_dec(v_snd_1587_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1749_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
uint8_t v___x_1595_; 
v___x_1595_ = lean_nat_dec_eq(v_fst_1590_, v___x_1542_);
if (v___x_1595_ == 0)
{
lean_object* v_array_1596_; lean_object* v_idx_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1744_; 
v_array_1596_ = lean_ctor_get(v_a_1529_, 0);
v_idx_1597_ = lean_ctor_get(v_a_1529_, 1);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_a_1529_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1599_ = v_a_1529_;
v_isShared_1600_ = v_isSharedCheck_1744_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_idx_1597_);
lean_inc(v_array_1596_);
lean_dec(v_a_1529_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1744_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___f_1601_; lean_object* v___f_1602_; lean_object* v___y_1604_; lean_object* v_pos_1605_; lean_object* v_res_1606_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v_lower_1636_; lean_object* v_upper_1637_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1649_; lean_object* v_pos_1650_; lean_object* v___y_1677_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___y_1735_; uint8_t v___x_1743_; 
v___f_1601_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1));
v___f_1602_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2));
v___x_1732_ = lean_nat_add(v_idx_1597_, v_fst_1590_);
lean_dec(v_fst_1590_);
v___x_1733_ = lean_byte_array_size(v_array_1596_);
v___x_1743_ = lean_nat_dec_le(v_idx_1597_, v___x_1542_);
if (v___x_1743_ == 0)
{
v___y_1735_ = v_idx_1597_;
goto v___jp_1734_;
}
else
{
lean_dec(v_idx_1597_);
v___y_1735_ = v___x_1542_;
goto v___jp_1734_;
}
v___jp_1603_:
{
lean_object* v___x_1607_; lean_object* v_snd_1608_; lean_object* v_snd_1609_; uint8_t v___x_1610_; 
v___x_1607_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1602_, v_maxSpaceSequence_1540_, v___x_1542_, v_pos_1605_);
v_snd_1608_ = lean_ctor_get(v___x_1607_, 1);
lean_inc(v_snd_1608_);
lean_dec_ref(v___x_1607_);
v_snd_1609_ = lean_ctor_get(v_snd_1608_, 1);
v___x_1610_ = lean_unbox(v_snd_1609_);
if (v___x_1610_ == 0)
{
lean_object* v_fst_1611_; lean_object* v_array_1612_; lean_object* v_idx_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v_fst_1611_ = lean_ctor_get(v_snd_1608_, 0);
lean_inc(v_fst_1611_);
lean_dec(v_snd_1608_);
v_array_1612_ = lean_ctor_get(v_fst_1611_, 0);
v_idx_1613_ = lean_ctor_get(v_fst_1611_, 1);
v___x_1614_ = lean_byte_array_size(v_array_1612_);
v___x_1615_ = lean_nat_dec_lt(v_idx_1613_, v___x_1614_);
if (v___x_1615_ == 0)
{
v___y_1578_ = v___y_1604_;
v_pos_1579_ = v_fst_1611_;
v_res_1580_ = v_res_1606_;
goto v___jp_1577_;
}
else
{
uint8_t v___x_1616_; uint32_t v___x_1617_; uint32_t v___x_1618_; uint8_t v___x_1619_; 
v___x_1616_ = lean_byte_array_fget(v_array_1612_, v_idx_1613_);
v___x_1617_ = lean_uint8_to_uint32(v___x_1616_);
v___x_1618_ = 32;
v___x_1619_ = lean_uint32_dec_eq(v___x_1617_, v___x_1618_);
if (v___x_1619_ == 0)
{
uint32_t v___x_1620_; uint8_t v___x_1621_; 
v___x_1620_ = 9;
v___x_1621_ = lean_uint32_dec_eq(v___x_1617_, v___x_1620_);
if (v___x_1621_ == 0)
{
v___y_1578_ = v___y_1604_;
v_pos_1579_ = v_fst_1611_;
v_res_1580_ = v_res_1606_;
goto v___jp_1577_;
}
else
{
lean_dec(v_res_1606_);
lean_dec_ref(v___y_1604_);
v_pos_1531_ = v_fst_1611_;
goto v___jp_1530_;
}
}
else
{
lean_dec(v_res_1606_);
lean_dec_ref(v___y_1604_);
v_pos_1531_ = v_fst_1611_;
goto v___jp_1530_;
}
}
}
else
{
lean_object* v_fst_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1630_; 
lean_dec(v_res_1606_);
lean_dec_ref(v___y_1604_);
v_fst_1622_ = lean_ctor_get(v_snd_1608_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v_snd_1608_);
if (v_isSharedCheck_1630_ == 0)
{
lean_object* v_unused_1631_; 
v_unused_1631_ = lean_ctor_get(v_snd_1608_, 1);
lean_dec(v_unused_1631_);
v___x_1624_ = v_snd_1608_;
v_isShared_1625_ = v_isSharedCheck_1630_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_fst_1622_);
lean_dec(v_snd_1608_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1630_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1626_; lean_object* v___x_1628_; 
v___x_1626_ = lean_box(0);
if (v_isShared_1625_ == 0)
{
lean_ctor_set_tag(v___x_1624_, 1);
lean_ctor_set(v___x_1624_, 1, v___x_1626_);
v___x_1628_ = v___x_1624_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_fst_1622_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v___x_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
v___jp_1632_:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = l_ByteArray_toByteSlice(v___y_1635_, v_lower_1636_, v_upper_1637_);
v___x_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
v___y_1604_ = v___y_1634_;
v_pos_1605_ = v___y_1633_;
v_res_1606_ = v___x_1639_;
goto v___jp_1603_;
}
v___jp_1640_:
{
uint8_t v___x_1647_; 
v___x_1647_ = lean_nat_dec_le(v___y_1644_, v___y_1643_);
if (v___x_1647_ == 0)
{
lean_dec(v___y_1644_);
v___y_1633_ = v___y_1641_;
v___y_1634_ = v___y_1642_;
v___y_1635_ = v___y_1645_;
v_lower_1636_ = v___y_1646_;
v_upper_1637_ = v___y_1643_;
goto v___jp_1632_;
}
else
{
lean_dec(v___y_1643_);
v___y_1633_ = v___y_1641_;
v___y_1634_ = v___y_1642_;
v___y_1635_ = v___y_1645_;
v_lower_1636_ = v___y_1646_;
v_upper_1637_ = v___y_1644_;
goto v___jp_1632_;
}
}
v___jp_1648_:
{
lean_object* v___x_1651_; lean_object* v_snd_1652_; lean_object* v_snd_1653_; uint8_t v___x_1654_; 
lean_inc_ref(v_pos_1650_);
v___x_1651_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1601_, v_maxHeaderValueLength_1539_, v___x_1542_, v_pos_1650_);
v_snd_1652_ = lean_ctor_get(v___x_1651_, 1);
lean_inc(v_snd_1652_);
v_snd_1653_ = lean_ctor_get(v_snd_1652_, 1);
v___x_1654_ = lean_unbox(v_snd_1653_);
if (v___x_1654_ == 0)
{
lean_object* v_fst_1655_; lean_object* v_fst_1656_; lean_object* v_array_1657_; lean_object* v_idx_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; 
v_fst_1655_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_fst_1655_);
lean_dec_ref(v___x_1651_);
v_fst_1656_ = lean_ctor_get(v_snd_1652_, 0);
lean_inc(v_fst_1656_);
lean_dec(v_snd_1652_);
v_array_1657_ = lean_ctor_get(v_pos_1650_, 0);
lean_inc_ref(v_array_1657_);
v_idx_1658_ = lean_ctor_get(v_pos_1650_, 1);
lean_inc(v_idx_1658_);
lean_dec_ref(v_pos_1650_);
v___x_1659_ = lean_nat_add(v_idx_1658_, v_fst_1655_);
lean_dec(v_fst_1655_);
v___x_1660_ = lean_byte_array_size(v_array_1657_);
v___x_1661_ = lean_nat_dec_le(v_idx_1658_, v___x_1542_);
if (v___x_1661_ == 0)
{
v___y_1641_ = v_fst_1656_;
v___y_1642_ = v___y_1649_;
v___y_1643_ = v___x_1660_;
v___y_1644_ = v___x_1659_;
v___y_1645_ = v_array_1657_;
v___y_1646_ = v_idx_1658_;
goto v___jp_1640_;
}
else
{
lean_dec(v_idx_1658_);
v___y_1641_ = v_fst_1656_;
v___y_1642_ = v___y_1649_;
v___y_1643_ = v___x_1660_;
v___y_1644_ = v___x_1659_;
v___y_1645_ = v_array_1657_;
v___y_1646_ = v___x_1542_;
goto v___jp_1640_;
}
}
else
{
lean_object* v_fst_1662_; lean_object* v_idx_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1674_; 
lean_dec_ref(v___x_1651_);
v_fst_1662_ = lean_ctor_get(v_snd_1652_, 0);
lean_inc(v_fst_1662_);
lean_dec(v_snd_1652_);
v_idx_1663_ = lean_ctor_get(v_pos_1650_, 1);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_pos_1650_);
if (v_isSharedCheck_1674_ == 0)
{
lean_object* v_unused_1675_; 
v_unused_1675_ = lean_ctor_get(v_pos_1650_, 0);
lean_dec(v_unused_1675_);
v___x_1665_ = v_pos_1650_;
v_isShared_1666_ = v_isSharedCheck_1674_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_idx_1663_);
lean_dec(v_pos_1650_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1674_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v_idx_1667_; uint8_t v___x_1668_; 
v_idx_1667_ = lean_ctor_get(v_fst_1662_, 1);
v___x_1668_ = lean_nat_dec_eq(v_idx_1663_, v_idx_1667_);
lean_dec(v_idx_1663_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; lean_object* v___x_1671_; 
lean_dec_ref(v___y_1649_);
v___x_1669_ = lean_box(0);
if (v_isShared_1666_ == 0)
{
lean_ctor_set_tag(v___x_1665_, 1);
lean_ctor_set(v___x_1665_, 1, v___x_1669_);
lean_ctor_set(v___x_1665_, 0, v_fst_1662_);
v___x_1671_ = v___x_1665_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_fst_1662_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
else
{
lean_object* v___x_1673_; 
lean_del_object(v___x_1665_);
v___x_1673_ = lean_box(0);
v___y_1604_ = v___y_1649_;
v_pos_1605_ = v_fst_1662_;
v_res_1606_ = v___x_1673_;
goto v___jp_1603_;
}
}
}
}
v___jp_1676_:
{
lean_object* v_array_1678_; lean_object* v_idx_1679_; lean_object* v___x_1680_; uint8_t v___x_1681_; 
v_array_1678_ = lean_ctor_get(v_fst_1591_, 0);
v_idx_1679_ = lean_ctor_get(v_fst_1591_, 1);
v___x_1680_ = lean_byte_array_size(v_array_1678_);
v___x_1681_ = lean_nat_dec_lt(v_idx_1679_, v___x_1680_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; lean_object* v___x_1684_; 
lean_dec_ref(v___y_1677_);
lean_dec_ref(v_array_1596_);
v___x_1682_ = lean_box(0);
if (v_isShared_1600_ == 0)
{
lean_ctor_set_tag(v___x_1599_, 1);
lean_ctor_set(v___x_1599_, 1, v___x_1682_);
lean_ctor_set(v___x_1599_, 0, v_fst_1591_);
v___x_1684_ = v___x_1599_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_fst_1591_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v___x_1682_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
else
{
uint8_t v___x_1686_; uint8_t v_got_1687_; uint8_t v___x_1688_; 
v___x_1686_ = 58;
v_got_1687_ = lean_byte_array_fget(v_array_1678_, v_idx_1679_);
v___x_1688_ = lean_uint8_dec_eq(v_got_1687_, v___x_1686_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1691_; 
lean_dec_ref(v___y_1677_);
lean_dec_ref(v_array_1596_);
v___x_1689_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4));
if (v_isShared_1600_ == 0)
{
lean_ctor_set_tag(v___x_1599_, 1);
lean_ctor_set(v___x_1599_, 1, v___x_1689_);
lean_ctor_set(v___x_1599_, 0, v_fst_1591_);
v___x_1691_ = v___x_1599_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_fst_1591_);
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
lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1729_; 
lean_inc(v_idx_1679_);
lean_inc_ref(v_array_1678_);
lean_del_object(v___x_1599_);
v_isSharedCheck_1729_ = !lean_is_exclusive(v_fst_1591_);
if (v_isSharedCheck_1729_ == 0)
{
lean_object* v_unused_1730_; lean_object* v_unused_1731_; 
v_unused_1730_ = lean_ctor_get(v_fst_1591_, 1);
lean_dec(v_unused_1730_);
v_unused_1731_ = lean_ctor_get(v_fst_1591_, 0);
lean_dec(v_unused_1731_);
v___x_1694_ = v_fst_1591_;
v_isShared_1695_ = v_isSharedCheck_1729_;
goto v_resetjp_1693_;
}
else
{
lean_dec(v_fst_1591_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1729_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1699_; 
v___x_1696_ = lean_unsigned_to_nat(1u);
v___x_1697_ = lean_nat_add(v_idx_1679_, v___x_1696_);
lean_dec(v_idx_1679_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 1, v___x_1697_);
v___x_1699_ = v___x_1694_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_array_1678_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
lean_object* v___x_1700_; lean_object* v_snd_1701_; lean_object* v_snd_1702_; uint8_t v___x_1703_; 
v___x_1700_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1602_, v_maxSpaceSequence_1540_, v___x_1542_, v___x_1699_);
v_snd_1701_ = lean_ctor_get(v___x_1700_, 1);
lean_inc(v_snd_1701_);
lean_dec_ref(v___x_1700_);
v_snd_1702_ = lean_ctor_get(v_snd_1701_, 1);
v___x_1703_ = lean_unbox(v_snd_1702_);
if (v___x_1703_ == 0)
{
lean_object* v_fst_1704_; lean_object* v_array_1705_; lean_object* v_idx_1706_; lean_object* v_lower_1707_; lean_object* v_upper_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; 
v_fst_1704_ = lean_ctor_get(v_snd_1701_, 0);
lean_inc(v_fst_1704_);
lean_dec(v_snd_1701_);
v_array_1705_ = lean_ctor_get(v_fst_1704_, 0);
v_idx_1706_ = lean_ctor_get(v_fst_1704_, 1);
v_lower_1707_ = lean_ctor_get(v___y_1677_, 0);
lean_inc(v_lower_1707_);
v_upper_1708_ = lean_ctor_get(v___y_1677_, 1);
lean_inc(v_upper_1708_);
lean_dec_ref(v___y_1677_);
v___x_1709_ = l_ByteArray_toByteSlice(v_array_1596_, v_lower_1707_, v_upper_1708_);
v___x_1710_ = lean_byte_array_size(v_array_1705_);
v___x_1711_ = lean_nat_dec_lt(v_idx_1706_, v___x_1710_);
if (v___x_1711_ == 0)
{
v___y_1649_ = v___x_1709_;
v_pos_1650_ = v_fst_1704_;
goto v___jp_1648_;
}
else
{
uint8_t v___x_1712_; uint32_t v___x_1713_; uint32_t v___x_1714_; uint8_t v___x_1715_; 
v___x_1712_ = lean_byte_array_fget(v_array_1705_, v_idx_1706_);
v___x_1713_ = lean_uint8_to_uint32(v___x_1712_);
v___x_1714_ = 32;
v___x_1715_ = lean_uint32_dec_eq(v___x_1713_, v___x_1714_);
if (v___x_1715_ == 0)
{
uint32_t v___x_1716_; uint8_t v___x_1717_; 
v___x_1716_ = 9;
v___x_1717_ = lean_uint32_dec_eq(v___x_1713_, v___x_1716_);
if (v___x_1717_ == 0)
{
v___y_1649_ = v___x_1709_;
v_pos_1650_ = v_fst_1704_;
goto v___jp_1648_;
}
else
{
lean_dec_ref(v___x_1709_);
v_pos_1535_ = v_fst_1704_;
goto v___jp_1534_;
}
}
else
{
lean_dec_ref(v___x_1709_);
v_pos_1535_ = v_fst_1704_;
goto v___jp_1534_;
}
}
}
else
{
lean_object* v_fst_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1726_; 
lean_dec_ref(v___y_1677_);
lean_dec_ref(v_array_1596_);
v_fst_1718_ = lean_ctor_get(v_snd_1701_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_snd_1701_);
if (v_isSharedCheck_1726_ == 0)
{
lean_object* v_unused_1727_; 
v_unused_1727_ = lean_ctor_get(v_snd_1701_, 1);
lean_dec(v_unused_1727_);
v___x_1720_ = v_snd_1701_;
v_isShared_1721_ = v_isSharedCheck_1726_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_fst_1718_);
lean_dec(v_snd_1701_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1726_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1722_ = lean_box(0);
if (v_isShared_1721_ == 0)
{
lean_ctor_set_tag(v___x_1720_, 1);
lean_ctor_set(v___x_1720_, 1, v___x_1722_);
v___x_1724_ = v___x_1720_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_fst_1718_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
}
}
}
}
v___jp_1734_:
{
uint8_t v___x_1736_; 
v___x_1736_ = lean_nat_dec_le(v___x_1732_, v___x_1733_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1738_; 
lean_dec(v___x_1732_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 1, v___x_1733_);
lean_ctor_set(v___x_1593_, 0, v___y_1735_);
v___x_1738_ = v___x_1593_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___y_1735_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v___x_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
v___y_1677_ = v___x_1738_;
goto v___jp_1676_;
}
}
else
{
lean_object* v___x_1741_; 
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 1, v___x_1732_);
lean_ctor_set(v___x_1593_, 0, v___y_1735_);
v___x_1741_ = v___x_1593_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___y_1735_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v___x_1732_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
v___y_1677_ = v___x_1741_;
goto v___jp_1676_;
}
}
}
}
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1747_; 
lean_dec(v_fst_1591_);
lean_dec(v_fst_1590_);
v___x_1745_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_1594_ == 0)
{
lean_ctor_set_tag(v___x_1593_, 1);
lean_ctor_set(v___x_1593_, 1, v___x_1745_);
lean_ctor_set(v___x_1593_, 0, v_a_1529_);
v___x_1747_ = v___x_1593_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1529_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
else
{
lean_object* v_fst_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1759_; 
lean_dec_ref(v___x_1586_);
lean_dec_ref(v_a_1529_);
v_fst_1751_ = lean_ctor_get(v_snd_1587_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_snd_1587_);
if (v_isSharedCheck_1759_ == 0)
{
lean_object* v_unused_1760_; 
v_unused_1760_ = lean_ctor_get(v_snd_1587_, 1);
lean_dec(v_unused_1760_);
v___x_1753_ = v_snd_1587_;
v_isShared_1754_ = v_isSharedCheck_1759_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_fst_1751_);
lean_dec(v_snd_1587_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1759_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1755_ = lean_box(0);
if (v_isShared_1754_ == 0)
{
lean_ctor_set_tag(v___x_1753_, 1);
lean_ctor_set(v___x_1753_, 1, v___x_1755_);
v___x_1757_ = v___x_1753_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_fst_1751_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
v___jp_1530_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_1533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1533_, 0, v_pos_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
return v___x_1533_;
}
v___jp_1534_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_1537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1537_, 0, v_pos_1535_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
return v___x_1537_;
}
v___jp_1543_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1547_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0));
v___x_1548_ = l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go(v___y_1546_, v___x_1542_, v___x_1547_);
lean_dec_ref(v___y_1546_);
v___x_1549_ = lean_string_utf8_byte_size(v___x_1548_);
lean_inc_ref(v___x_1548_);
v___x_1550_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1548_);
lean_ctor_set(v___x_1550_, 1, v___x_1542_);
lean_ctor_set(v___x_1550_, 2, v___x_1549_);
v___x_1551_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(v___x_1550_, v___x_1549_);
lean_dec_ref_known(v___x_1550_, 3);
v___x_1552_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1548_);
lean_ctor_set(v___x_1552_, 1, v___x_1542_);
lean_ctor_set(v___x_1552_, 2, v___x_1551_);
v___x_1553_ = l_String_Slice_toString(v___x_1552_);
lean_dec_ref_known(v___x_1552_, 3);
v___x_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___y_1545_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___y_1544_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
return v___x_1555_;
}
v___jp_1556_:
{
lean_object* v___x_1560_; 
v___x_1560_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___y_1559_, v___y_1558_);
lean_dec(v___y_1559_);
if (lean_obj_tag(v___x_1560_) == 0)
{
if (lean_obj_tag(v___y_1557_) == 0)
{
lean_object* v_pos_1561_; lean_object* v_res_1562_; lean_object* v___x_1563_; 
v_pos_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_pos_1561_);
v_res_1562_ = lean_ctor_get(v___x_1560_, 1);
lean_inc(v_res_1562_);
lean_dec_ref_known(v___x_1560_, 2);
v___x_1563_ = l_ByteArray_empty;
v___y_1544_ = v_pos_1561_;
v___y_1545_ = v_res_1562_;
v___y_1546_ = v___x_1563_;
goto v___jp_1543_;
}
else
{
lean_object* v_pos_1564_; lean_object* v_res_1565_; lean_object* v_val_1566_; lean_object* v___x_1567_; 
v_pos_1564_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_pos_1564_);
v_res_1565_ = lean_ctor_get(v___x_1560_, 1);
lean_inc(v_res_1565_);
lean_dec_ref_known(v___x_1560_, 2);
v_val_1566_ = lean_ctor_get(v___y_1557_, 0);
lean_inc(v_val_1566_);
lean_dec_ref_known(v___y_1557_, 1);
v___x_1567_ = l_ByteSlice_toByteArray(v_val_1566_);
v___y_1544_ = v_pos_1564_;
v___y_1545_ = v_res_1565_;
v___y_1546_ = v___x_1567_;
goto v___jp_1543_;
}
}
else
{
lean_object* v_pos_1568_; lean_object* v_err_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_dec(v___y_1557_);
v_pos_1568_ = lean_ctor_get(v___x_1560_, 0);
v_err_1569_ = lean_ctor_get(v___x_1560_, 1);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1560_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_err_1569_);
lean_inc(v_pos_1568_);
lean_dec(v___x_1560_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_pos_1568_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_err_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
v___jp_1577_:
{
lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1581_ = l_ByteSlice_toByteArray(v___y_1578_);
v___x_1582_ = lean_string_validate_utf8(v___x_1581_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; 
lean_dec_ref(v___x_1581_);
v___x_1583_ = lean_box(0);
v___y_1557_ = v_res_1580_;
v___y_1558_ = v_pos_1579_;
v___y_1559_ = v___x_1583_;
goto v___jp_1556_;
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = lean_string_from_utf8_unchecked(v___x_1581_);
v___x_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
v___y_1557_ = v_res_1580_;
v___y_1558_ = v_pos_1579_;
v___y_1559_ = v___x_1585_;
goto v___jp_1556_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___boxed(lean_object* v_limits_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_1761_, v_a_1762_);
lean_dec_ref(v_limits_1761_);
return v_res_1763_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(lean_object* v_x_1764_, lean_object* v_x_1765_){
_start:
{
if (lean_obj_tag(v_x_1764_) == 0)
{
if (lean_obj_tag(v_x_1765_) == 0)
{
uint8_t v___x_1766_; 
v___x_1766_ = 1;
return v___x_1766_;
}
else
{
uint8_t v___x_1767_; 
v___x_1767_ = 0;
return v___x_1767_;
}
}
else
{
if (lean_obj_tag(v_x_1765_) == 0)
{
uint8_t v___x_1768_; 
v___x_1768_ = 0;
return v___x_1768_;
}
else
{
lean_object* v_val_1769_; lean_object* v_val_1770_; uint8_t v___x_1771_; uint8_t v___x_1772_; uint8_t v___x_1773_; 
v_val_1769_ = lean_ctor_get(v_x_1764_, 0);
v_val_1770_ = lean_ctor_get(v_x_1765_, 0);
v___x_1771_ = lean_unbox(v_val_1769_);
v___x_1772_ = lean_unbox(v_val_1770_);
v___x_1773_ = lean_uint8_dec_eq(v___x_1771_, v___x_1772_);
return v___x_1773_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0___boxed(lean_object* v_x_1774_, lean_object* v_x_1775_){
_start:
{
uint8_t v_res_1776_; lean_object* v_r_1777_; 
v_res_1776_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_x_1774_, v_x_1775_);
lean_dec(v_x_1775_);
lean_dec(v_x_1774_);
v_r_1777_ = lean_box(v_res_1776_);
return v_r_1777_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader(lean_object* v_limits_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v___y_1787_; lean_object* v_pos_1810_; lean_object* v_res_1811_; lean_object* v_array_1849_; lean_object* v_idx_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; 
v_array_1849_ = lean_ctor_get(v_a_1785_, 0);
v_idx_1850_ = lean_ctor_get(v_a_1785_, 1);
v___x_1851_ = lean_byte_array_size(v_array_1849_);
v___x_1852_ = lean_nat_dec_lt(v_idx_1850_, v___x_1851_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; 
v___x_1853_ = lean_box(0);
v_pos_1810_ = v_a_1785_;
v_res_1811_ = v___x_1853_;
goto v___jp_1809_;
}
else
{
uint8_t v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1854_ = lean_byte_array_fget(v_array_1849_, v_idx_1850_);
v___x_1855_ = lean_box(v___x_1854_);
v___x_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
v_pos_1810_ = v_a_1785_;
v_res_1811_ = v___x_1856_;
goto v___jp_1809_;
}
v___jp_1786_:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_1789_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_1788_, v___y_1787_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_pos_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1798_; 
v_pos_1790_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1798_ == 0)
{
lean_object* v_unused_1799_; 
v_unused_1799_ = lean_ctor_get(v___x_1789_, 1);
lean_dec(v_unused_1799_);
v___x_1792_ = v___x_1789_;
v_isShared_1793_ = v_isSharedCheck_1798_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_pos_1790_);
lean_dec(v___x_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1798_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1794_; lean_object* v___x_1796_; 
v___x_1794_ = lean_box(0);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 1, v___x_1794_);
v___x_1796_ = v___x_1792_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_pos_1790_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v___x_1794_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
else
{
lean_object* v_pos_1800_; lean_object* v_err_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
v_pos_1800_ = lean_ctor_get(v___x_1789_, 0);
v_err_1801_ = lean_ctor_get(v___x_1789_, 1);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1789_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_err_1801_);
lean_inc(v_pos_1800_);
lean_dec(v___x_1789_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_pos_1800_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_err_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
v___jp_1809_:
{
lean_object* v___x_1812_; uint8_t v___x_1813_; 
v___x_1812_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseSingleHeader___closed__0));
v___x_1813_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_1811_, v___x_1812_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1814_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseSingleHeader___closed__1));
v___x_1815_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_1811_, v___x_1814_);
lean_dec(v_res_1811_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; 
v___x_1816_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_1784_, v_pos_1810_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_pos_1817_; lean_object* v_res_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v_pos_1817_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_pos_1817_);
v_res_1818_ = lean_ctor_get(v___x_1816_, 1);
lean_inc(v_res_1818_);
lean_dec_ref_known(v___x_1816_, 2);
v___x_1819_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_1820_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_1819_, v_pos_1817_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_pos_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1829_; 
v_pos_1821_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1829_ == 0)
{
lean_object* v_unused_1830_; 
v_unused_1830_ = lean_ctor_get(v___x_1820_, 1);
lean_dec(v_unused_1830_);
v___x_1823_ = v___x_1820_;
v_isShared_1824_ = v_isSharedCheck_1829_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_pos_1821_);
lean_dec(v___x_1820_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1829_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1825_; lean_object* v___x_1827_; 
v___x_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1825_, 0, v_res_1818_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 1, v___x_1825_);
v___x_1827_ = v___x_1823_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_pos_1821_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
else
{
lean_object* v_pos_1831_; lean_object* v_err_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_dec(v_res_1818_);
v_pos_1831_ = lean_ctor_get(v___x_1820_, 0);
v_err_1832_ = lean_ctor_get(v___x_1820_, 1);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1820_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_err_1832_);
lean_inc(v_pos_1831_);
lean_dec(v___x_1820_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_pos_1831_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_err_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
else
{
lean_object* v_pos_1840_; lean_object* v_err_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
v_pos_1840_ = lean_ctor_get(v___x_1816_, 0);
v_err_1841_ = lean_ctor_get(v___x_1816_, 1);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1816_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_err_1841_);
lean_inc(v_pos_1840_);
lean_dec(v___x_1816_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_pos_1840_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_err_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
else
{
v___y_1787_ = v_pos_1810_;
goto v___jp_1786_;
}
}
else
{
lean_dec(v_res_1811_);
v___y_1787_ = v_pos_1810_;
goto v___jp_1786_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader___boxed(lean_object* v_limits_1857_, lean_object* v_a_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_1857_, v_a_1858_);
lean_dec_ref(v_limits_1857_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair(lean_object* v_a_1864_){
_start:
{
lean_object* v_array_1865_; lean_object* v_idx_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; 
v_array_1865_ = lean_ctor_get(v_a_1864_, 0);
v_idx_1866_ = lean_ctor_get(v_a_1864_, 1);
v___x_1867_ = lean_byte_array_size(v_array_1865_);
v___x_1868_ = lean_nat_dec_lt(v_idx_1866_, v___x_1867_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = lean_box(0);
v___x_1870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1870_, 0, v_a_1864_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
return v___x_1870_;
}
else
{
uint8_t v___x_1871_; uint8_t v_got_1872_; uint8_t v___x_1873_; 
v___x_1871_ = 92;
v_got_1872_ = lean_byte_array_fget(v_array_1865_, v_idx_1866_);
v___x_1873_ = lean_uint8_dec_eq(v_got_1872_, v___x_1871_);
if (v___x_1873_ == 0)
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1));
v___x_1875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1875_, 0, v_a_1864_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
return v___x_1875_;
}
else
{
lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1909_; 
lean_inc(v_idx_1866_);
lean_inc_ref(v_array_1865_);
v_isSharedCheck_1909_ = !lean_is_exclusive(v_a_1864_);
if (v_isSharedCheck_1909_ == 0)
{
lean_object* v_unused_1910_; lean_object* v_unused_1911_; 
v_unused_1910_ = lean_ctor_get(v_a_1864_, 1);
lean_dec(v_unused_1910_);
v_unused_1911_ = lean_ctor_get(v_a_1864_, 0);
lean_dec(v_unused_1911_);
v___x_1877_ = v_a_1864_;
v_isShared_1878_ = v_isSharedCheck_1909_;
goto v_resetjp_1876_;
}
else
{
lean_dec(v_a_1864_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1909_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; uint8_t v___x_1881_; 
v___x_1879_ = lean_unsigned_to_nat(1u);
v___x_1880_ = lean_nat_add(v_idx_1866_, v___x_1879_);
lean_dec(v_idx_1866_);
v___x_1881_ = lean_nat_dec_lt(v___x_1880_, v___x_1867_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1883_; 
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 1, v___x_1880_);
v___x_1883_ = v___x_1877_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_array_1865_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v___x_1880_);
v___x_1883_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = lean_box(0);
v___x_1885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1883_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
return v___x_1885_;
}
}
else
{
uint8_t v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1887_ = lean_byte_array_fget(v_array_1865_, v___x_1880_);
v___x_1888_ = lean_nat_add(v___x_1880_, v___x_1879_);
lean_dec(v___x_1880_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 1, v___x_1888_);
v___x_1890_ = v___x_1877_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_array_1865_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; uint32_t v___x_1893_; uint32_t v___x_1900_; uint8_t v___x_1901_; 
v___x_1891_ = lean_box(v___x_1887_);
lean_inc_ref(v___x_1890_);
v___x_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1890_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = lean_uint8_to_uint32(v___x_1887_);
v___x_1900_ = 9;
v___x_1901_ = lean_uint32_dec_eq(v___x_1893_, v___x_1900_);
if (v___x_1901_ == 0)
{
uint32_t v___x_1902_; uint8_t v___x_1903_; 
v___x_1902_ = 32;
v___x_1903_ = lean_uint32_dec_eq(v___x_1893_, v___x_1902_);
if (v___x_1903_ == 0)
{
uint32_t v___x_1904_; uint8_t v___x_1905_; 
v___x_1904_ = 33;
v___x_1905_ = lean_uint32_dec_le(v___x_1904_, v___x_1893_);
if (v___x_1905_ == 0)
{
lean_dec_ref_known(v___x_1892_, 2);
goto v___jp_1894_;
}
else
{
uint32_t v___x_1906_; uint8_t v___x_1907_; 
v___x_1906_ = 126;
v___x_1907_ = lean_uint32_dec_le(v___x_1893_, v___x_1906_);
if (v___x_1907_ == 0)
{
lean_dec_ref_known(v___x_1892_, 2);
goto v___jp_1894_;
}
else
{
lean_dec_ref(v___x_1890_);
return v___x_1892_;
}
}
}
else
{
lean_dec_ref(v___x_1890_);
return v___x_1892_;
}
}
else
{
lean_dec_ref(v___x_1890_);
return v___x_1892_;
}
v___jp_1894_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1895_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2));
v___x_1896_ = l_Char_quote(v___x_1893_);
v___x_1897_ = lean_string_append(v___x_1895_, v___x_1896_);
lean_dec_ref(v___x_1896_);
v___x_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
v___x_1899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1890_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
return v___x_1899_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(lean_object* v_maxLength_1916_, lean_object* v_buf_1917_, lean_object* v_length_1918_, lean_object* v_a_1919_){
_start:
{
lean_object* v_array_1920_; lean_object* v_idx_1921_; lean_object* v___x_1922_; uint8_t v___x_1923_; 
v_array_1920_ = lean_ctor_get(v_a_1919_, 0);
v_idx_1921_ = lean_ctor_get(v_a_1919_, 1);
v___x_1922_ = lean_byte_array_size(v_array_1920_);
v___x_1923_ = lean_nat_dec_lt(v_idx_1921_, v___x_1922_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
lean_dec(v_length_1918_);
lean_dec_ref(v_buf_1917_);
v___x_1924_ = lean_box(0);
v___x_1925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1925_, 0, v_a_1919_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
return v___x_1925_;
}
else
{
lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_2002_; 
lean_inc(v_idx_1921_);
lean_inc_ref(v_array_1920_);
v_isSharedCheck_2002_ = !lean_is_exclusive(v_a_1919_);
if (v_isSharedCheck_2002_ == 0)
{
lean_object* v_unused_2003_; lean_object* v_unused_2004_; 
v_unused_2003_ = lean_ctor_get(v_a_1919_, 1);
lean_dec(v_unused_2003_);
v_unused_2004_ = lean_ctor_get(v_a_1919_, 0);
lean_dec(v_unused_2004_);
v___x_1927_ = v_a_1919_;
v_isShared_1928_ = v_isSharedCheck_2002_;
goto v_resetjp_1926_;
}
else
{
lean_dec(v_a_1919_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_2002_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
uint8_t v_c_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v_it_x27_1933_; 
v_c_1929_ = lean_byte_array_fget(v_array_1920_, v_idx_1921_);
v___x_1930_ = lean_unsigned_to_nat(1u);
v___x_1931_ = lean_nat_add(v_idx_1921_, v___x_1930_);
lean_dec(v_idx_1921_);
lean_inc(v___x_1931_);
lean_inc_ref(v_array_1920_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 1, v___x_1931_);
v_it_x27_1933_ = v___x_1927_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_array_1920_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v___x_1931_);
v_it_x27_1933_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
uint8_t v___x_1950_; uint8_t v___x_1951_; 
v___x_1950_ = 34;
v___x_1951_ = lean_uint8_dec_eq(v_c_1929_, v___x_1950_);
if (v___x_1951_ == 0)
{
uint8_t v___x_1952_; uint8_t v___x_1953_; 
v___x_1952_ = 92;
v___x_1953_ = lean_uint8_dec_eq(v_c_1929_, v___x_1952_);
if (v___x_1953_ == 0)
{
uint32_t v___x_1954_; uint32_t v___x_1960_; uint8_t v___x_1961_; 
lean_dec(v___x_1931_);
lean_dec_ref(v_array_1920_);
v___x_1954_ = lean_uint8_to_uint32(v_c_1929_);
v___x_1960_ = 9;
v___x_1961_ = lean_uint32_dec_eq(v___x_1954_, v___x_1960_);
if (v___x_1961_ == 0)
{
uint32_t v___x_1962_; uint8_t v___x_1963_; 
v___x_1962_ = 32;
v___x_1963_ = lean_uint32_dec_eq(v___x_1954_, v___x_1962_);
if (v___x_1963_ == 0)
{
uint32_t v___x_1964_; uint8_t v___x_1965_; 
v___x_1964_ = 33;
v___x_1965_ = lean_uint32_dec_eq(v___x_1954_, v___x_1964_);
if (v___x_1965_ == 0)
{
uint32_t v___x_1966_; uint8_t v___x_1967_; 
v___x_1966_ = 35;
v___x_1967_ = lean_uint32_dec_le(v___x_1966_, v___x_1954_);
if (v___x_1967_ == 0)
{
goto v___jp_1955_;
}
else
{
uint32_t v___x_1968_; uint8_t v___x_1969_; 
v___x_1968_ = 91;
v___x_1969_ = lean_uint32_dec_le(v___x_1954_, v___x_1968_);
if (v___x_1969_ == 0)
{
goto v___jp_1955_;
}
else
{
goto v___jp_1934_;
}
}
}
else
{
goto v___jp_1934_;
}
}
else
{
goto v___jp_1934_;
}
}
else
{
goto v___jp_1934_;
}
v___jp_1955_:
{
uint32_t v___x_1956_; uint8_t v___x_1957_; 
v___x_1956_ = 93;
v___x_1957_ = lean_uint32_dec_le(v___x_1956_, v___x_1954_);
if (v___x_1957_ == 0)
{
goto v___jp_1941_;
}
else
{
uint32_t v___x_1958_; uint8_t v___x_1959_; 
v___x_1958_ = 126;
v___x_1959_ = lean_uint32_dec_le(v___x_1954_, v___x_1958_);
if (v___x_1959_ == 0)
{
goto v___jp_1941_;
}
else
{
goto v___jp_1934_;
}
}
}
}
else
{
uint8_t v___x_1970_; 
v___x_1970_ = lean_nat_dec_lt(v___x_1931_, v___x_1922_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
lean_dec(v___x_1931_);
lean_dec_ref(v_array_1920_);
lean_dec(v_length_1918_);
lean_dec_ref(v_buf_1917_);
v___x_1971_ = lean_box(0);
v___x_1972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1972_, 0, v_it_x27_1933_);
lean_ctor_set(v___x_1972_, 1, v___x_1971_);
return v___x_1972_;
}
else
{
uint8_t v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; uint32_t v___x_1983_; uint32_t v___x_1992_; uint8_t v___x_1993_; 
lean_dec_ref(v_it_x27_1933_);
v___x_1973_ = lean_byte_array_fget(v_array_1920_, v___x_1931_);
v___x_1974_ = lean_nat_add(v___x_1931_, v___x_1930_);
lean_dec(v___x_1931_);
v___x_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1975_, 0, v_array_1920_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1983_ = lean_uint8_to_uint32(v___x_1973_);
v___x_1992_ = 9;
v___x_1993_ = lean_uint32_dec_eq(v___x_1983_, v___x_1992_);
if (v___x_1993_ == 0)
{
uint32_t v___x_1994_; uint8_t v___x_1995_; 
v___x_1994_ = 32;
v___x_1995_ = lean_uint32_dec_eq(v___x_1983_, v___x_1994_);
if (v___x_1995_ == 0)
{
uint32_t v___x_1996_; uint8_t v___x_1997_; 
v___x_1996_ = 33;
v___x_1997_ = lean_uint32_dec_le(v___x_1996_, v___x_1983_);
if (v___x_1997_ == 0)
{
goto v___jp_1984_;
}
else
{
uint32_t v___x_1998_; uint8_t v___x_1999_; 
v___x_1998_ = 126;
v___x_1999_ = lean_uint32_dec_le(v___x_1983_, v___x_1998_);
if (v___x_1999_ == 0)
{
goto v___jp_1984_;
}
else
{
goto v___jp_1976_;
}
}
}
else
{
goto v___jp_1976_;
}
}
else
{
goto v___jp_1976_;
}
v___jp_1976_:
{
lean_object* v___x_1977_; uint8_t v___x_1978_; 
v___x_1977_ = lean_nat_add(v_length_1918_, v___x_1930_);
lean_dec(v_length_1918_);
v___x_1978_ = lean_nat_dec_lt(v_maxLength_1916_, v___x_1977_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; 
v___x_1979_ = lean_byte_array_push(v_buf_1917_, v___x_1973_);
v_buf_1917_ = v___x_1979_;
v_length_1918_ = v___x_1977_;
v_a_1919_ = v___x_1975_;
goto _start;
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
lean_dec(v___x_1977_);
lean_dec_ref(v_buf_1917_);
v___x_1981_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_1982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1975_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
return v___x_1982_;
}
}
v___jp_1984_:
{
uint8_t v___x_1985_; uint8_t v___x_1986_; 
v___x_1985_ = 128;
v___x_1986_ = lean_uint8_dec_le(v___x_1985_, v___x_1973_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
lean_dec(v_length_1918_);
lean_dec_ref(v_buf_1917_);
v___x_1987_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2));
v___x_1988_ = l_Char_quote(v___x_1983_);
v___x_1989_ = lean_string_append(v___x_1987_, v___x_1988_);
lean_dec_ref(v___x_1988_);
v___x_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
v___x_1991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1975_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
return v___x_1991_;
}
else
{
goto v___jp_1976_;
}
}
}
}
}
else
{
lean_object* v___x_2000_; 
lean_dec(v___x_1931_);
lean_dec_ref(v_array_1920_);
lean_dec(v_length_1918_);
v___x_2000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2000_, 0, v_it_x27_1933_);
lean_ctor_set(v___x_2000_, 1, v_buf_1917_);
return v___x_2000_;
}
v___jp_1934_:
{
lean_object* v___x_1935_; uint8_t v___x_1936_; 
v___x_1935_ = lean_nat_add(v_length_1918_, v___x_1930_);
lean_dec(v_length_1918_);
v___x_1936_ = lean_nat_dec_lt(v_maxLength_1916_, v___x_1935_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; 
v___x_1937_ = lean_byte_array_push(v_buf_1917_, v_c_1929_);
v_buf_1917_ = v___x_1937_;
v_length_1918_ = v___x_1935_;
v_a_1919_ = v_it_x27_1933_;
goto _start;
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
lean_dec(v___x_1935_);
lean_dec_ref(v_buf_1917_);
v___x_1939_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_1940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1940_, 0, v_it_x27_1933_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
return v___x_1940_;
}
}
v___jp_1941_:
{
uint8_t v___x_1942_; uint8_t v___x_1943_; 
v___x_1942_ = 128;
v___x_1943_ = lean_uint8_dec_le(v___x_1942_, v_c_1929_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; uint32_t v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
lean_dec(v_length_1918_);
lean_dec_ref(v_buf_1917_);
v___x_1944_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2));
v___x_1945_ = lean_uint8_to_uint32(v_c_1929_);
v___x_1946_ = l_Char_quote(v___x_1945_);
v___x_1947_ = lean_string_append(v___x_1944_, v___x_1946_);
lean_dec_ref(v___x_1946_);
v___x_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
v___x_1949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1949_, 0, v_it_x27_1933_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
return v___x_1949_;
}
else
{
goto v___jp_1934_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___boxed(lean_object* v_maxLength_2005_, lean_object* v_buf_2006_, lean_object* v_length_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_2005_, v_buf_2006_, v_length_2007_, v_a_2008_);
lean_dec(v_maxLength_2005_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(lean_object* v_maxLength_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v_array_2015_; lean_object* v_idx_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; 
v_array_2015_ = lean_ctor_get(v_a_2014_, 0);
v_idx_2016_ = lean_ctor_get(v_a_2014_, 1);
v___x_2017_ = lean_byte_array_size(v_array_2015_);
v___x_2018_ = lean_nat_dec_lt(v_idx_2016_, v___x_2017_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = lean_box(0);
v___x_2020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2020_, 0, v_a_2014_);
lean_ctor_set(v___x_2020_, 1, v___x_2019_);
return v___x_2020_;
}
else
{
uint8_t v___x_2021_; uint8_t v_got_2022_; uint8_t v___x_2023_; 
v___x_2021_ = 34;
v_got_2022_ = lean_byte_array_fget(v_array_2015_, v_idx_2016_);
v___x_2023_ = lean_uint8_dec_eq(v_got_2022_, v___x_2021_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1));
v___x_2025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2025_, 0, v_a_2014_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
return v___x_2025_;
}
else
{
lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2037_; 
lean_inc(v_idx_2016_);
lean_inc_ref(v_array_2015_);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_a_2014_);
if (v_isSharedCheck_2037_ == 0)
{
lean_object* v_unused_2038_; lean_object* v_unused_2039_; 
v_unused_2038_ = lean_ctor_get(v_a_2014_, 1);
lean_dec(v_unused_2038_);
v_unused_2039_ = lean_ctor_get(v_a_2014_, 0);
lean_dec(v_unused_2039_);
v___x_2027_ = v_a_2014_;
v_isShared_2028_ = v_isSharedCheck_2037_;
goto v_resetjp_2026_;
}
else
{
lean_dec(v_a_2014_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2037_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2032_; 
v___x_2029_ = lean_unsigned_to_nat(1u);
v___x_2030_ = lean_nat_add(v_idx_2016_, v___x_2029_);
lean_dec(v_idx_2016_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 1, v___x_2030_);
v___x_2032_ = v___x_2027_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_array_2015_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2033_ = l_ByteArray_empty;
v___x_2034_ = lean_unsigned_to_nat(0u);
v___x_2035_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_2013_, v___x_2033_, v___x_2034_, v___x_2032_);
return v___x_2035_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___boxed(lean_object* v_maxLength_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxLength_2040_, v_a_2041_);
lean_dec(v_maxLength_2040_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(lean_object* v___f_2043_, lean_object* v_maxSpaceSequence_2044_, lean_object* v_x_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v_pos_2048_; lean_object* v_pos_2052_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v_snd_2057_; lean_object* v_snd_2058_; uint8_t v___x_2059_; 
v___x_2055_ = lean_unsigned_to_nat(0u);
v___x_2056_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2043_, v_maxSpaceSequence_2044_, v___x_2055_, v___y_2046_);
v_snd_2057_ = lean_ctor_get(v___x_2056_, 1);
lean_inc(v_snd_2057_);
lean_dec_ref(v___x_2056_);
v_snd_2058_ = lean_ctor_get(v_snd_2057_, 1);
v___x_2059_ = lean_unbox(v_snd_2058_);
if (v___x_2059_ == 0)
{
lean_object* v_fst_2060_; lean_object* v_array_2061_; lean_object* v_idx_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v_fst_2060_ = lean_ctor_get(v_snd_2057_, 0);
lean_inc(v_fst_2060_);
lean_dec(v_snd_2057_);
v_array_2061_ = lean_ctor_get(v_fst_2060_, 0);
v_idx_2062_ = lean_ctor_get(v_fst_2060_, 1);
v___x_2063_ = lean_byte_array_size(v_array_2061_);
v___x_2064_ = lean_nat_dec_lt(v_idx_2062_, v___x_2063_);
if (v___x_2064_ == 0)
{
v_pos_2048_ = v_fst_2060_;
goto v___jp_2047_;
}
else
{
uint8_t v___x_2065_; uint32_t v___x_2066_; uint32_t v___x_2067_; uint8_t v___x_2068_; 
v___x_2065_ = lean_byte_array_fget(v_array_2061_, v_idx_2062_);
v___x_2066_ = lean_uint8_to_uint32(v___x_2065_);
v___x_2067_ = 32;
v___x_2068_ = lean_uint32_dec_eq(v___x_2066_, v___x_2067_);
if (v___x_2068_ == 0)
{
uint32_t v___x_2069_; uint8_t v___x_2070_; 
v___x_2069_ = 9;
v___x_2070_ = lean_uint32_dec_eq(v___x_2066_, v___x_2069_);
if (v___x_2070_ == 0)
{
v_pos_2048_ = v_fst_2060_;
goto v___jp_2047_;
}
else
{
v_pos_2052_ = v_fst_2060_;
goto v___jp_2051_;
}
}
else
{
v_pos_2052_ = v_fst_2060_;
goto v___jp_2051_;
}
}
}
else
{
lean_object* v_fst_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2079_; 
v_fst_2071_ = lean_ctor_get(v_snd_2057_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_snd_2057_);
if (v_isSharedCheck_2079_ == 0)
{
lean_object* v_unused_2080_; 
v_unused_2080_ = lean_ctor_get(v_snd_2057_, 1);
lean_dec(v_unused_2080_);
v___x_2073_ = v_snd_2057_;
v_isShared_2074_ = v_isSharedCheck_2079_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_fst_2071_);
lean_dec(v_snd_2057_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2079_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2075_ = lean_box(0);
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
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_fst_2071_);
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
v___jp_2047_:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = lean_box(0);
v___x_2050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2050_, 0, v_pos_2048_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
return v___x_2050_;
}
v___jp_2051_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2054_, 0, v_pos_2052_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
return v___x_2054_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2___boxed(lean_object* v___f_2081_, lean_object* v_maxSpaceSequence_2082_, lean_object* v_x_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_2081_, v_maxSpaceSequence_2082_, v_x_2083_, v___y_2084_);
lean_dec(v_maxSpaceSequence_2082_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(lean_object* v_limits_2098_, lean_object* v_a_2099_){
_start:
{
lean_object* v_pos_2101_; lean_object* v_pos_2105_; lean_object* v___y_2109_; lean_object* v_pos_2110_; lean_object* v___y_2116_; lean_object* v___y_2120_; lean_object* v_pos_2121_; lean_object* v_res_2122_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v_lower_2153_; lean_object* v_upper_2154_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v_pos_2170_; lean_object* v_maxSpaceSequence_2173_; lean_object* v_maxChunkExtNameLength_2174_; lean_object* v_maxChunkExtValueLength_2175_; lean_object* v___f_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v_snd_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2471_; 
v_maxSpaceSequence_2173_ = lean_ctor_get(v_limits_2098_, 8);
v_maxChunkExtNameLength_2174_ = lean_ctor_get(v_limits_2098_, 11);
v_maxChunkExtValueLength_2175_ = lean_ctor_get(v_limits_2098_, 12);
v___f_2176_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2));
v___x_2177_ = lean_unsigned_to_nat(0u);
v___x_2178_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2176_, v_maxSpaceSequence_2173_, v___x_2177_, v_a_2099_);
v_snd_2179_ = lean_ctor_get(v___x_2178_, 1);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2471_ == 0)
{
lean_object* v_unused_2472_; 
v_unused_2472_ = lean_ctor_get(v___x_2178_, 0);
lean_dec(v_unused_2472_);
v___x_2181_ = v___x_2178_;
v_isShared_2182_ = v_isSharedCheck_2471_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_snd_2179_);
lean_dec(v___x_2178_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2471_;
goto v_resetjp_2180_;
}
v___jp_2100_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2103_, 0, v_pos_2101_);
lean_ctor_set(v___x_2103_, 1, v___x_2102_);
return v___x_2103_;
}
v___jp_2104_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2107_, 0, v_pos_2105_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
return v___x_2107_;
}
v___jp_2108_:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2111_ = lean_box(0);
v___x_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___y_2109_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v_pos_2110_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
return v___x_2114_;
}
v___jp_2115_:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = lean_box(0);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___y_2116_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
return v___x_2118_;
}
v___jp_2119_:
{
lean_object* v___x_2123_; 
v___x_2123_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_2122_, v_pos_2121_);
lean_dec(v_res_2122_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_pos_2124_; lean_object* v_res_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2139_; 
v_pos_2124_ = lean_ctor_get(v___x_2123_, 0);
v_res_2125_ = lean_ctor_get(v___x_2123_, 1);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2127_ = v___x_2123_;
v_isShared_2128_ = v_isSharedCheck_2139_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_res_2125_);
lean_inc(v_pos_2124_);
lean_dec(v___x_2123_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2139_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Std_Http_Chunk_ExtensionValue_ofString_x3f(v_res_2125_);
if (lean_obj_tag(v___x_2129_) == 1)
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2133_; 
v___x_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___y_2120_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 1, v___x_2131_);
v___x_2133_ = v___x_2127_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_pos_2124_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
else
{
lean_object* v___x_2135_; lean_object* v___x_2137_; 
lean_dec(v___x_2129_);
lean_dec_ref(v___y_2120_);
v___x_2135_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1));
if (v_isShared_2128_ == 0)
{
lean_ctor_set_tag(v___x_2127_, 1);
lean_ctor_set(v___x_2127_, 1, v___x_2135_);
v___x_2137_ = v___x_2127_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_pos_2124_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v___x_2135_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
else
{
lean_object* v_pos_2140_; lean_object* v_err_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec_ref(v___y_2120_);
v_pos_2140_ = lean_ctor_get(v___x_2123_, 0);
v_err_2141_ = lean_ctor_get(v___x_2123_, 1);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2123_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_err_2141_);
lean_inc(v_pos_2140_);
lean_dec(v___x_2123_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_pos_2140_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v_err_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
v___jp_2149_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; uint8_t v___x_2157_; 
v___x_2155_ = l_ByteArray_toByteSlice(v___y_2151_, v_lower_2153_, v_upper_2154_);
v___x_2156_ = l_ByteSlice_toByteArray(v___x_2155_);
v___x_2157_ = lean_string_validate_utf8(v___x_2156_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; 
lean_dec_ref(v___x_2156_);
v___x_2158_ = lean_box(0);
v___y_2120_ = v___y_2152_;
v_pos_2121_ = v___y_2150_;
v_res_2122_ = v___x_2158_;
goto v___jp_2119_;
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = lean_string_from_utf8_unchecked(v___x_2156_);
v___x_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
v___y_2120_ = v___y_2152_;
v_pos_2121_ = v___y_2150_;
v_res_2122_ = v___x_2160_;
goto v___jp_2119_;
}
}
v___jp_2161_:
{
uint8_t v___x_2168_; 
v___x_2168_ = lean_nat_dec_le(v___y_2163_, v___y_2162_);
if (v___x_2168_ == 0)
{
lean_dec(v___y_2163_);
v___y_2150_ = v___y_2164_;
v___y_2151_ = v___y_2165_;
v___y_2152_ = v___y_2166_;
v_lower_2153_ = v___y_2167_;
v_upper_2154_ = v___y_2162_;
goto v___jp_2149_;
}
else
{
lean_dec(v___y_2162_);
v___y_2150_ = v___y_2164_;
v___y_2151_ = v___y_2165_;
v___y_2152_ = v___y_2166_;
v_lower_2153_ = v___y_2167_;
v_upper_2154_ = v___y_2163_;
goto v___jp_2149_;
}
}
v___jp_2169_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2172_, 0, v_pos_2170_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
return v___x_2172_;
}
v_resetjp_2180_:
{
lean_object* v_snd_2183_; uint8_t v___x_2184_; 
v_snd_2183_ = lean_ctor_get(v_snd_2179_, 1);
v___x_2184_ = lean_unbox(v_snd_2183_);
if (v___x_2184_ == 0)
{
lean_object* v_fst_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2464_; 
v_fst_2185_ = lean_ctor_get(v_snd_2179_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v_snd_2179_);
if (v_isSharedCheck_2464_ == 0)
{
lean_object* v_unused_2465_; 
v_unused_2465_ = lean_ctor_get(v_snd_2179_, 1);
lean_dec(v_unused_2465_);
v___x_2187_ = v_snd_2179_;
v_isShared_2188_ = v_isSharedCheck_2464_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_fst_2185_);
lean_dec(v_snd_2179_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2464_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v_array_2189_; lean_object* v_idx_2190_; lean_object* v___f_2191_; lean_object* v___y_2193_; lean_object* v_pos_2194_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v_pos_2229_; lean_object* v_array_2230_; lean_object* v_idx_2231_; lean_object* v_pos_2302_; lean_object* v_res_2303_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v_lower_2369_; lean_object* v_upper_2370_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v_pos_2385_; lean_object* v_pos_2418_; lean_object* v___x_2456_; uint8_t v___x_2457_; 
v_array_2189_ = lean_ctor_get(v_fst_2185_, 0);
v_idx_2190_ = lean_ctor_get(v_fst_2185_, 1);
v___f_2191_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_2456_ = lean_byte_array_size(v_array_2189_);
v___x_2457_ = lean_nat_dec_lt(v_idx_2190_, v___x_2456_);
if (v___x_2457_ == 0)
{
lean_inc(v_idx_2190_);
lean_inc_ref(v_array_2189_);
v_pos_2418_ = v_fst_2185_;
goto v___jp_2417_;
}
else
{
uint8_t v___x_2458_; uint32_t v___x_2459_; uint32_t v___x_2460_; uint8_t v___x_2461_; 
v___x_2458_ = lean_byte_array_fget(v_array_2189_, v_idx_2190_);
v___x_2459_ = lean_uint8_to_uint32(v___x_2458_);
v___x_2460_ = 32;
v___x_2461_ = lean_uint32_dec_eq(v___x_2459_, v___x_2460_);
if (v___x_2461_ == 0)
{
uint32_t v___x_2462_; uint8_t v___x_2463_; 
v___x_2462_ = 9;
v___x_2463_ = lean_uint32_dec_eq(v___x_2459_, v___x_2462_);
if (v___x_2463_ == 0)
{
lean_inc(v_idx_2190_);
lean_inc_ref(v_array_2189_);
v_pos_2418_ = v_fst_2185_;
goto v___jp_2417_;
}
else
{
lean_del_object(v___x_2187_);
lean_del_object(v___x_2181_);
v_pos_2101_ = v_fst_2185_;
goto v___jp_2100_;
}
}
else
{
lean_del_object(v___x_2187_);
lean_del_object(v___x_2181_);
v_pos_2101_ = v_fst_2185_;
goto v___jp_2100_;
}
}
v___jp_2192_:
{
lean_object* v___x_2195_; lean_object* v_snd_2196_; lean_object* v_snd_2197_; uint8_t v___x_2198_; 
lean_inc_ref(v_pos_2194_);
v___x_2195_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2191_, v_maxChunkExtValueLength_2175_, v___x_2177_, v_pos_2194_);
v_snd_2196_ = lean_ctor_get(v___x_2195_, 1);
lean_inc(v_snd_2196_);
v_snd_2197_ = lean_ctor_get(v_snd_2196_, 1);
v___x_2198_ = lean_unbox(v_snd_2197_);
if (v___x_2198_ == 0)
{
lean_object* v_fst_2199_; lean_object* v_fst_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2214_; 
v_fst_2199_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_fst_2199_);
lean_dec_ref(v___x_2195_);
v_fst_2200_ = lean_ctor_get(v_snd_2196_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_snd_2196_);
if (v_isSharedCheck_2214_ == 0)
{
lean_object* v_unused_2215_; 
v_unused_2215_ = lean_ctor_get(v_snd_2196_, 1);
lean_dec(v_unused_2215_);
v___x_2202_ = v_snd_2196_;
v_isShared_2203_ = v_isSharedCheck_2214_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_fst_2200_);
lean_dec(v_snd_2196_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2214_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
uint8_t v___x_2204_; 
v___x_2204_ = lean_nat_dec_eq(v_fst_2199_, v___x_2177_);
if (v___x_2204_ == 0)
{
lean_object* v_array_2205_; lean_object* v_idx_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; uint8_t v___x_2209_; 
lean_del_object(v___x_2202_);
v_array_2205_ = lean_ctor_get(v_pos_2194_, 0);
lean_inc_ref(v_array_2205_);
v_idx_2206_ = lean_ctor_get(v_pos_2194_, 1);
lean_inc(v_idx_2206_);
lean_dec_ref(v_pos_2194_);
v___x_2207_ = lean_nat_add(v_idx_2206_, v_fst_2199_);
lean_dec(v_fst_2199_);
v___x_2208_ = lean_byte_array_size(v_array_2205_);
v___x_2209_ = lean_nat_dec_le(v_idx_2206_, v___x_2177_);
if (v___x_2209_ == 0)
{
v___y_2162_ = v___x_2208_;
v___y_2163_ = v___x_2207_;
v___y_2164_ = v_fst_2200_;
v___y_2165_ = v_array_2205_;
v___y_2166_ = v___y_2193_;
v___y_2167_ = v_idx_2206_;
goto v___jp_2161_;
}
else
{
lean_dec(v_idx_2206_);
v___y_2162_ = v___x_2208_;
v___y_2163_ = v___x_2207_;
v___y_2164_ = v_fst_2200_;
v___y_2165_ = v_array_2205_;
v___y_2166_ = v___y_2193_;
v___y_2167_ = v___x_2177_;
goto v___jp_2161_;
}
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2212_; 
lean_dec(v_fst_2200_);
lean_dec(v_fst_2199_);
lean_dec_ref(v___y_2193_);
v___x_2210_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_2203_ == 0)
{
lean_ctor_set_tag(v___x_2202_, 1);
lean_ctor_set(v___x_2202_, 1, v___x_2210_);
lean_ctor_set(v___x_2202_, 0, v_pos_2194_);
v___x_2212_ = v___x_2202_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_pos_2194_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
else
{
lean_object* v_fst_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2224_; 
lean_dec_ref(v___x_2195_);
lean_dec_ref(v_pos_2194_);
lean_dec_ref(v___y_2193_);
v_fst_2216_ = lean_ctor_get(v_snd_2196_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_snd_2196_);
if (v_isSharedCheck_2224_ == 0)
{
lean_object* v_unused_2225_; 
v_unused_2225_ = lean_ctor_get(v_snd_2196_, 1);
lean_dec(v_unused_2225_);
v___x_2218_ = v_snd_2196_;
v_isShared_2219_ = v_isSharedCheck_2224_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_fst_2216_);
lean_dec(v_snd_2196_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2224_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; lean_object* v___x_2222_; 
v___x_2220_ = lean_box(0);
if (v_isShared_2219_ == 0)
{
lean_ctor_set_tag(v___x_2218_, 1);
lean_ctor_set(v___x_2218_, 1, v___x_2220_);
v___x_2222_ = v___x_2218_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_fst_2216_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v___x_2220_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
v___jp_2226_:
{
lean_object* v___x_2232_; uint8_t v___x_2233_; 
v___x_2232_ = lean_byte_array_size(v_array_2230_);
v___x_2233_ = lean_nat_dec_lt(v_idx_2231_, v___x_2232_);
if (v___x_2233_ == 0)
{
lean_object* v___x_2234_; lean_object* v___x_2236_; 
lean_dec(v_idx_2231_);
lean_dec_ref(v_array_2230_);
lean_dec_ref(v___y_2228_);
lean_del_object(v___x_2187_);
v___x_2234_ = lean_box(0);
if (v_isShared_2182_ == 0)
{
lean_ctor_set_tag(v___x_2181_, 1);
lean_ctor_set(v___x_2181_, 1, v___x_2234_);
lean_ctor_set(v___x_2181_, 0, v_pos_2229_);
v___x_2236_ = v___x_2181_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_pos_2229_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
else
{
uint8_t v___x_2238_; uint8_t v_got_2239_; uint8_t v___x_2240_; 
v___x_2238_ = 61;
v_got_2239_ = lean_byte_array_fget(v_array_2230_, v_idx_2231_);
v___x_2240_ = lean_uint8_dec_eq(v_got_2239_, v___x_2238_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; lean_object* v___x_2243_; 
lean_dec(v_idx_2231_);
lean_dec_ref(v_array_2230_);
lean_dec_ref(v___y_2228_);
lean_del_object(v___x_2187_);
v___x_2241_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3));
if (v_isShared_2182_ == 0)
{
lean_ctor_set_tag(v___x_2181_, 1);
lean_ctor_set(v___x_2181_, 1, v___x_2241_);
lean_ctor_set(v___x_2181_, 0, v_pos_2229_);
v___x_2243_ = v___x_2181_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_pos_2229_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v___x_2241_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
else
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2248_; 
lean_dec_ref(v_pos_2229_);
v___x_2245_ = lean_unsigned_to_nat(1u);
v___x_2246_ = lean_nat_add(v_idx_2231_, v___x_2245_);
lean_dec(v_idx_2231_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 1, v___x_2246_);
lean_ctor_set(v___x_2181_, 0, v_array_2230_);
v___x_2248_ = v___x_2181_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_array_2230_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
lean_object* v___x_2249_; 
v___x_2249_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_2176_, v_maxSpaceSequence_2173_, v___y_2227_, v___x_2248_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_pos_2250_; lean_object* v_array_2251_; lean_object* v_idx_2252_; lean_object* v___x_2253_; uint8_t v___x_2254_; 
v_pos_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_pos_2250_);
lean_dec_ref_known(v___x_2249_, 2);
v_array_2251_ = lean_ctor_get(v_pos_2250_, 0);
v_idx_2252_ = lean_ctor_get(v_pos_2250_, 1);
v___x_2253_ = lean_byte_array_size(v_array_2251_);
v___x_2254_ = lean_nat_dec_lt(v_idx_2252_, v___x_2253_);
if (v___x_2254_ == 0)
{
lean_del_object(v___x_2187_);
v___y_2193_ = v___y_2228_;
v_pos_2194_ = v_pos_2250_;
goto v___jp_2192_;
}
else
{
uint8_t v___x_2255_; uint8_t v___x_2256_; uint8_t v___x_2257_; 
v___x_2255_ = lean_byte_array_fget(v_array_2251_, v_idx_2252_);
v___x_2256_ = 34;
v___x_2257_ = lean_uint8_dec_eq(v___x_2255_, v___x_2256_);
if (v___x_2257_ == 0)
{
lean_del_object(v___x_2187_);
v___y_2193_ = v___y_2228_;
v_pos_2194_ = v_pos_2250_;
goto v___jp_2192_;
}
else
{
lean_object* v___x_2258_; 
v___x_2258_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxChunkExtValueLength_2175_, v_pos_2250_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_pos_2259_; lean_object* v_res_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2281_; 
v_pos_2259_ = lean_ctor_get(v___x_2258_, 0);
v_res_2260_ = lean_ctor_get(v___x_2258_, 1);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2262_ = v___x_2258_;
v_isShared_2263_ = v_isSharedCheck_2281_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_res_2260_);
lean_inc(v_pos_2259_);
lean_dec(v___x_2258_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2281_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
uint8_t v___x_2264_; 
v___x_2264_ = lean_string_validate_utf8(v_res_2260_);
if (v___x_2264_ == 0)
{
lean_del_object(v___x_2262_);
lean_dec(v_res_2260_);
lean_dec_ref(v___y_2228_);
lean_del_object(v___x_2187_);
v___y_2116_ = v_pos_2259_;
goto v___jp_2115_;
}
else
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = lean_string_from_utf8_unchecked(v_res_2260_);
v___x_2266_ = l_Std_Http_Chunk_ExtensionValue_ofString_x3f(v___x_2265_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_del_object(v___x_2262_);
lean_dec_ref(v___y_2228_);
lean_del_object(v___x_2187_);
v___y_2116_ = v_pos_2259_;
goto v___jp_2115_;
}
else
{
lean_object* v___x_2268_; 
lean_inc_ref(v___x_2266_);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 1, v___x_2266_);
lean_ctor_set(v___x_2187_, 0, v___y_2228_);
v___x_2268_ = v___x_2187_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___y_2228_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v___x_2266_);
v___x_2268_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2278_; 
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2278_ == 0)
{
lean_object* v_unused_2279_; 
v_unused_2279_ = lean_ctor_get(v___x_2266_, 0);
lean_dec(v_unused_2279_);
v___x_2270_ = v___x_2266_;
v_isShared_2271_ = v_isSharedCheck_2278_;
goto v_resetjp_2269_;
}
else
{
lean_dec(v___x_2266_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2278_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 0, v___x_2268_);
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2268_);
v___x_2273_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
lean_object* v___x_2275_; 
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 1, v___x_2273_);
v___x_2275_ = v___x_2262_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_pos_2259_);
lean_ctor_set(v_reuseFailAlloc_2276_, 1, v___x_2273_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
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
lean_object* v_pos_2282_; lean_object* v_err_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec_ref(v___y_2228_);
lean_del_object(v___x_2187_);
v_pos_2282_ = lean_ctor_get(v___x_2258_, 0);
v_err_2283_ = lean_ctor_get(v___x_2258_, 1);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2258_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_err_2283_);
lean_inc(v_pos_2282_);
lean_dec(v___x_2258_);
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
}
else
{
lean_object* v_pos_2291_; lean_object* v_err_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec_ref(v___y_2228_);
lean_del_object(v___x_2187_);
v_pos_2291_ = lean_ctor_get(v___x_2249_, 0);
v_err_2292_ = lean_ctor_get(v___x_2249_, 1);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2249_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_err_2292_);
lean_inc(v_pos_2291_);
lean_dec(v___x_2249_);
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
}
}
}
}
v___jp_2301_:
{
lean_object* v___x_2304_; 
v___x_2304_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_2303_, v_pos_2302_);
lean_dec(v_res_2303_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_pos_2305_; lean_object* v_res_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v_pos_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_pos_2305_);
v_res_2306_ = lean_ctor_get(v___x_2304_, 1);
lean_inc(v_res_2306_);
lean_dec_ref_known(v___x_2304_, 2);
v___x_2307_ = lean_box(0);
v___x_2308_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_2176_, v_maxSpaceSequence_2173_, v___x_2307_, v_pos_2305_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_pos_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2346_; 
v_pos_2309_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2346_ == 0)
{
lean_object* v_unused_2347_; 
v_unused_2347_ = lean_ctor_get(v___x_2308_, 1);
lean_dec(v_unused_2347_);
v___x_2311_ = v___x_2308_;
v_isShared_2312_ = v_isSharedCheck_2346_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_pos_2309_);
lean_dec(v___x_2308_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2346_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Std_Http_Chunk_ExtensionName_ofString_x3f(v_res_2306_);
if (lean_obj_tag(v___x_2313_) == 1)
{
lean_object* v_val_2314_; lean_object* v_array_2315_; lean_object* v_idx_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; 
v_val_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_val_2314_);
lean_dec_ref_known(v___x_2313_, 1);
v_array_2315_ = lean_ctor_get(v_pos_2309_, 0);
v_idx_2316_ = lean_ctor_get(v_pos_2309_, 1);
v___x_2317_ = lean_byte_array_size(v_array_2315_);
v___x_2318_ = lean_nat_dec_lt(v_idx_2316_, v___x_2317_);
if (v___x_2318_ == 0)
{
lean_del_object(v___x_2311_);
lean_del_object(v___x_2187_);
lean_del_object(v___x_2181_);
v___y_2109_ = v_val_2314_;
v_pos_2110_ = v_pos_2309_;
goto v___jp_2108_;
}
else
{
uint8_t v___x_2319_; uint8_t v___x_2320_; uint8_t v___x_2321_; 
v___x_2319_ = lean_byte_array_fget(v_array_2315_, v_idx_2316_);
v___x_2320_ = 61;
v___x_2321_ = lean_uint8_dec_eq(v___x_2319_, v___x_2320_);
if (v___x_2321_ == 0)
{
lean_del_object(v___x_2311_);
lean_del_object(v___x_2187_);
lean_del_object(v___x_2181_);
v___y_2109_ = v_val_2314_;
v_pos_2110_ = v_pos_2309_;
goto v___jp_2108_;
}
else
{
lean_object* v___x_2322_; lean_object* v_snd_2323_; lean_object* v_snd_2324_; uint8_t v___x_2325_; 
v___x_2322_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2176_, v_maxSpaceSequence_2173_, v___x_2177_, v_pos_2309_);
v_snd_2323_ = lean_ctor_get(v___x_2322_, 1);
lean_inc(v_snd_2323_);
lean_dec_ref(v___x_2322_);
v_snd_2324_ = lean_ctor_get(v_snd_2323_, 1);
v___x_2325_ = lean_unbox(v_snd_2324_);
if (v___x_2325_ == 0)
{
lean_object* v_fst_2326_; lean_object* v_array_2327_; lean_object* v_idx_2328_; lean_object* v___x_2329_; uint8_t v___x_2330_; 
lean_del_object(v___x_2311_);
v_fst_2326_ = lean_ctor_get(v_snd_2323_, 0);
lean_inc(v_fst_2326_);
lean_dec(v_snd_2323_);
v_array_2327_ = lean_ctor_get(v_fst_2326_, 0);
v_idx_2328_ = lean_ctor_get(v_fst_2326_, 1);
v___x_2329_ = lean_byte_array_size(v_array_2327_);
v___x_2330_ = lean_nat_dec_lt(v_idx_2328_, v___x_2329_);
if (v___x_2330_ == 0)
{
lean_inc(v_idx_2328_);
lean_inc_ref(v_array_2327_);
v___y_2227_ = v___x_2307_;
v___y_2228_ = v_val_2314_;
v_pos_2229_ = v_fst_2326_;
v_array_2230_ = v_array_2327_;
v_idx_2231_ = v_idx_2328_;
goto v___jp_2226_;
}
else
{
uint8_t v___x_2331_; uint32_t v___x_2332_; uint32_t v___x_2333_; uint8_t v___x_2334_; 
v___x_2331_ = lean_byte_array_fget(v_array_2327_, v_idx_2328_);
v___x_2332_ = lean_uint8_to_uint32(v___x_2331_);
v___x_2333_ = 32;
v___x_2334_ = lean_uint32_dec_eq(v___x_2332_, v___x_2333_);
if (v___x_2334_ == 0)
{
uint32_t v___x_2335_; uint8_t v___x_2336_; 
v___x_2335_ = 9;
v___x_2336_ = lean_uint32_dec_eq(v___x_2332_, v___x_2335_);
if (v___x_2336_ == 0)
{
lean_inc(v_idx_2328_);
lean_inc_ref(v_array_2327_);
v___y_2227_ = v___x_2307_;
v___y_2228_ = v_val_2314_;
v_pos_2229_ = v_fst_2326_;
v_array_2230_ = v_array_2327_;
v_idx_2231_ = v_idx_2328_;
goto v___jp_2226_;
}
else
{
lean_dec(v_val_2314_);
lean_del_object(v___x_2187_);
lean_del_object(v___x_2181_);
v_pos_2170_ = v_fst_2326_;
goto v___jp_2169_;
}
}
else
{
lean_dec(v_val_2314_);
lean_del_object(v___x_2187_);
lean_del_object(v___x_2181_);
v_pos_2170_ = v_fst_2326_;
goto v___jp_2169_;
}
}
}
else
{
lean_object* v_fst_2337_; lean_object* v___x_2338_; lean_object* v___x_2340_; 
lean_dec(v_val_2314_);
lean_del_object(v___x_2187_);
lean_del_object(v___x_2181_);
v_fst_2337_ = lean_ctor_get(v_snd_2323_, 0);
lean_inc(v_fst_2337_);
lean_dec(v_snd_2323_);
v___x_2338_ = lean_box(0);
if (v_isShared_2312_ == 0)
{
lean_ctor_set_tag(v___x_2311_, 1);
lean_ctor_set(v___x_2311_, 1, v___x_2338_);
lean_ctor_set(v___x_2311_, 0, v_fst_2337_);
v___x_2340_ = v___x_2311_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_fst_2337_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
else
{
lean_object* v___x_2342_; lean_object* v___x_2344_; 
lean_dec(v___x_2313_);
lean_del_object(v___x_2187_);
lean_del_object(v___x_2181_);
v___x_2342_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5));
if (v_isShared_2312_ == 0)
{
lean_ctor_set_tag(v___x_2311_, 1);
lean_ctor_set(v___x_2311_, 1, v___x_2342_);
v___x_2344_ = v___x_2311_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_pos_2309_);
lean_ctor_set(v_reuseFailAlloc_2345_, 1, v___x_2342_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
else
{
lean_object* v_pos_2348_; lean_object* v_err_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec(v_res_2306_);
lean_del_object(v___x_2187_);
lean_del_object(v___x_2181_);
v_pos_2348_ = lean_ctor_get(v___x_2308_, 0);
v_err_2349_ = lean_ctor_get(v___x_2308_, 1);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2308_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_err_2349_);
lean_inc(v_pos_2348_);
lean_dec(v___x_2308_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_pos_2348_);
lean_ctor_set(v_reuseFailAlloc_2355_, 1, v_err_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
else
{
lean_object* v_pos_2357_; lean_object* v_err_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_del_object(v___x_2187_);
lean_del_object(v___x_2181_);
v_pos_2357_ = lean_ctor_get(v___x_2304_, 0);
v_err_2358_ = lean_ctor_get(v___x_2304_, 1);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2304_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_err_2358_);
lean_inc(v_pos_2357_);
lean_dec(v___x_2304_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_pos_2357_);
lean_ctor_set(v_reuseFailAlloc_2364_, 1, v_err_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
v___jp_2366_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; uint8_t v___x_2373_; 
v___x_2371_ = l_ByteArray_toByteSlice(v___y_2368_, v_lower_2369_, v_upper_2370_);
v___x_2372_ = l_ByteSlice_toByteArray(v___x_2371_);
v___x_2373_ = lean_string_validate_utf8(v___x_2372_);
if (v___x_2373_ == 0)
{
lean_object* v___x_2374_; 
lean_dec_ref(v___x_2372_);
v___x_2374_ = lean_box(0);
v_pos_2302_ = v___y_2367_;
v_res_2303_ = v___x_2374_;
goto v___jp_2301_;
}
else
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = lean_string_from_utf8_unchecked(v___x_2372_);
v___x_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
v_pos_2302_ = v___y_2367_;
v_res_2303_ = v___x_2376_;
goto v___jp_2301_;
}
}
v___jp_2377_:
{
uint8_t v___x_2383_; 
v___x_2383_ = lean_nat_dec_le(v___y_2378_, v___y_2381_);
if (v___x_2383_ == 0)
{
lean_dec(v___y_2378_);
v___y_2367_ = v___y_2379_;
v___y_2368_ = v___y_2380_;
v_lower_2369_ = v___y_2382_;
v_upper_2370_ = v___y_2381_;
goto v___jp_2366_;
}
else
{
lean_dec(v___y_2381_);
v___y_2367_ = v___y_2379_;
v___y_2368_ = v___y_2380_;
v_lower_2369_ = v___y_2382_;
v_upper_2370_ = v___y_2378_;
goto v___jp_2366_;
}
}
v___jp_2384_:
{
lean_object* v___x_2386_; lean_object* v_snd_2387_; lean_object* v_snd_2388_; uint8_t v___x_2389_; 
lean_inc_ref(v_pos_2385_);
v___x_2386_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2191_, v_maxChunkExtNameLength_2174_, v___x_2177_, v_pos_2385_);
v_snd_2387_ = lean_ctor_get(v___x_2386_, 1);
lean_inc(v_snd_2387_);
v_snd_2388_ = lean_ctor_get(v_snd_2387_, 1);
v___x_2389_ = lean_unbox(v_snd_2388_);
if (v___x_2389_ == 0)
{
lean_object* v_fst_2390_; lean_object* v_fst_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2405_; 
v_fst_2390_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_fst_2390_);
lean_dec_ref(v___x_2386_);
v_fst_2391_ = lean_ctor_get(v_snd_2387_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v_snd_2387_);
if (v_isSharedCheck_2405_ == 0)
{
lean_object* v_unused_2406_; 
v_unused_2406_ = lean_ctor_get(v_snd_2387_, 1);
lean_dec(v_unused_2406_);
v___x_2393_ = v_snd_2387_;
v_isShared_2394_ = v_isSharedCheck_2405_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_fst_2391_);
lean_dec(v_snd_2387_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2405_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
uint8_t v___x_2395_; 
v___x_2395_ = lean_nat_dec_eq(v_fst_2390_, v___x_2177_);
if (v___x_2395_ == 0)
{
lean_object* v_array_2396_; lean_object* v_idx_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; 
lean_del_object(v___x_2393_);
v_array_2396_ = lean_ctor_get(v_pos_2385_, 0);
lean_inc_ref(v_array_2396_);
v_idx_2397_ = lean_ctor_get(v_pos_2385_, 1);
lean_inc(v_idx_2397_);
lean_dec_ref(v_pos_2385_);
v___x_2398_ = lean_nat_add(v_idx_2397_, v_fst_2390_);
lean_dec(v_fst_2390_);
v___x_2399_ = lean_byte_array_size(v_array_2396_);
v___x_2400_ = lean_nat_dec_le(v_idx_2397_, v___x_2177_);
if (v___x_2400_ == 0)
{
v___y_2378_ = v___x_2398_;
v___y_2379_ = v_fst_2391_;
v___y_2380_ = v_array_2396_;
v___y_2381_ = v___x_2399_;
v___y_2382_ = v_idx_2397_;
goto v___jp_2377_;
}
else
{
lean_dec(v_idx_2397_);
v___y_2378_ = v___x_2398_;
v___y_2379_ = v_fst_2391_;
v___y_2380_ = v_array_2396_;
v___y_2381_ = v___x_2399_;
v___y_2382_ = v___x_2177_;
goto v___jp_2377_;
}
}
else
{
lean_object* v___x_2401_; lean_object* v___x_2403_; 
lean_dec(v_fst_2391_);
lean_dec(v_fst_2390_);
lean_del_object(v___x_2187_);
lean_del_object(v___x_2181_);
v___x_2401_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_2394_ == 0)
{
lean_ctor_set_tag(v___x_2393_, 1);
lean_ctor_set(v___x_2393_, 1, v___x_2401_);
lean_ctor_set(v___x_2393_, 0, v_pos_2385_);
v___x_2403_ = v___x_2393_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_pos_2385_);
lean_ctor_set(v_reuseFailAlloc_2404_, 1, v___x_2401_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
else
{
lean_object* v_fst_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2415_; 
lean_dec_ref(v___x_2386_);
lean_dec_ref(v_pos_2385_);
lean_del_object(v___x_2187_);
lean_del_object(v___x_2181_);
v_fst_2407_ = lean_ctor_get(v_snd_2387_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v_snd_2387_);
if (v_isSharedCheck_2415_ == 0)
{
lean_object* v_unused_2416_; 
v_unused_2416_ = lean_ctor_get(v_snd_2387_, 1);
lean_dec(v_unused_2416_);
v___x_2409_ = v_snd_2387_;
v_isShared_2410_ = v_isSharedCheck_2415_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_fst_2407_);
lean_dec(v_snd_2387_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2415_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2411_; lean_object* v___x_2413_; 
v___x_2411_ = lean_box(0);
if (v_isShared_2410_ == 0)
{
lean_ctor_set_tag(v___x_2409_, 1);
lean_ctor_set(v___x_2409_, 1, v___x_2411_);
v___x_2413_ = v___x_2409_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_fst_2407_);
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
}
v___jp_2417_:
{
lean_object* v___x_2419_; uint8_t v___x_2420_; 
v___x_2419_ = lean_byte_array_size(v_array_2189_);
v___x_2420_ = lean_nat_dec_lt(v_idx_2190_, v___x_2419_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
lean_dec(v_idx_2190_);
lean_dec_ref(v_array_2189_);
lean_del_object(v___x_2187_);
lean_del_object(v___x_2181_);
v___x_2421_ = lean_box(0);
v___x_2422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2422_, 0, v_pos_2418_);
lean_ctor_set(v___x_2422_, 1, v___x_2421_);
return v___x_2422_;
}
else
{
uint8_t v___x_2423_; uint8_t v_got_2424_; uint8_t v___x_2425_; 
v___x_2423_ = 59;
v_got_2424_ = lean_byte_array_fget(v_array_2189_, v_idx_2190_);
v___x_2425_ = lean_uint8_dec_eq(v_got_2424_, v___x_2423_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
lean_dec(v_idx_2190_);
lean_dec_ref(v_array_2189_);
lean_del_object(v___x_2187_);
lean_del_object(v___x_2181_);
v___x_2426_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7));
v___x_2427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2427_, 0, v_pos_2418_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
return v___x_2427_;
}
else
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v_snd_2432_; lean_object* v_snd_2433_; uint8_t v___x_2434_; 
lean_dec_ref(v_pos_2418_);
v___x_2428_ = lean_unsigned_to_nat(1u);
v___x_2429_ = lean_nat_add(v_idx_2190_, v___x_2428_);
lean_dec(v_idx_2190_);
v___x_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2430_, 0, v_array_2189_);
lean_ctor_set(v___x_2430_, 1, v___x_2429_);
v___x_2431_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2176_, v_maxSpaceSequence_2173_, v___x_2177_, v___x_2430_);
v_snd_2432_ = lean_ctor_get(v___x_2431_, 1);
lean_inc(v_snd_2432_);
lean_dec_ref(v___x_2431_);
v_snd_2433_ = lean_ctor_get(v_snd_2432_, 1);
v___x_2434_ = lean_unbox(v_snd_2433_);
if (v___x_2434_ == 0)
{
lean_object* v_fst_2435_; lean_object* v_array_2436_; lean_object* v_idx_2437_; lean_object* v___x_2438_; uint8_t v___x_2439_; 
v_fst_2435_ = lean_ctor_get(v_snd_2432_, 0);
lean_inc(v_fst_2435_);
lean_dec(v_snd_2432_);
v_array_2436_ = lean_ctor_get(v_fst_2435_, 0);
v_idx_2437_ = lean_ctor_get(v_fst_2435_, 1);
v___x_2438_ = lean_byte_array_size(v_array_2436_);
v___x_2439_ = lean_nat_dec_lt(v_idx_2437_, v___x_2438_);
if (v___x_2439_ == 0)
{
v_pos_2385_ = v_fst_2435_;
goto v___jp_2384_;
}
else
{
uint8_t v___x_2440_; uint32_t v___x_2441_; uint32_t v___x_2442_; uint8_t v___x_2443_; 
v___x_2440_ = lean_byte_array_fget(v_array_2436_, v_idx_2437_);
v___x_2441_ = lean_uint8_to_uint32(v___x_2440_);
v___x_2442_ = 32;
v___x_2443_ = lean_uint32_dec_eq(v___x_2441_, v___x_2442_);
if (v___x_2443_ == 0)
{
uint32_t v___x_2444_; uint8_t v___x_2445_; 
v___x_2444_ = 9;
v___x_2445_ = lean_uint32_dec_eq(v___x_2441_, v___x_2444_);
if (v___x_2445_ == 0)
{
v_pos_2385_ = v_fst_2435_;
goto v___jp_2384_;
}
else
{
lean_del_object(v___x_2187_);
lean_del_object(v___x_2181_);
v_pos_2105_ = v_fst_2435_;
goto v___jp_2104_;
}
}
else
{
lean_del_object(v___x_2187_);
lean_del_object(v___x_2181_);
v_pos_2105_ = v_fst_2435_;
goto v___jp_2104_;
}
}
}
else
{
lean_object* v_fst_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2454_; 
lean_del_object(v___x_2187_);
lean_del_object(v___x_2181_);
v_fst_2446_ = lean_ctor_get(v_snd_2432_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v_snd_2432_);
if (v_isSharedCheck_2454_ == 0)
{
lean_object* v_unused_2455_; 
v_unused_2455_ = lean_ctor_get(v_snd_2432_, 1);
lean_dec(v_unused_2455_);
v___x_2448_ = v_snd_2432_;
v_isShared_2449_ = v_isSharedCheck_2454_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_fst_2446_);
lean_dec(v_snd_2432_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2454_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2450_; lean_object* v___x_2452_; 
v___x_2450_ = lean_box(0);
if (v_isShared_2449_ == 0)
{
lean_ctor_set_tag(v___x_2448_, 1);
lean_ctor_set(v___x_2448_, 1, v___x_2450_);
v___x_2452_ = v___x_2448_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_fst_2446_);
lean_ctor_set(v_reuseFailAlloc_2453_, 1, v___x_2450_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
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
lean_object* v_fst_2466_; lean_object* v___x_2467_; lean_object* v___x_2469_; 
v_fst_2466_ = lean_ctor_get(v_snd_2179_, 0);
lean_inc(v_fst_2466_);
lean_dec(v_snd_2179_);
v___x_2467_ = lean_box(0);
if (v_isShared_2182_ == 0)
{
lean_ctor_set_tag(v___x_2181_, 1);
lean_ctor_set(v___x_2181_, 1, v___x_2467_);
lean_ctor_set(v___x_2181_, 0, v_fst_2466_);
v___x_2469_ = v___x_2181_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_fst_2466_);
lean_ctor_set(v_reuseFailAlloc_2470_, 1, v___x_2467_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___boxed(lean_object* v_limits_2473_, lean_object* v_a_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_2473_, v_a_2474_);
lean_dec_ref(v_limits_2473_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0(lean_object* v_limits_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_2476_, v___y_2477_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_pos_2479_; lean_object* v_res_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2488_; 
v_pos_2479_ = lean_ctor_get(v___x_2478_, 0);
v_res_2480_ = lean_ctor_get(v___x_2478_, 1);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2482_ = v___x_2478_;
v_isShared_2483_ = v_isSharedCheck_2488_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_res_2480_);
lean_inc(v_pos_2479_);
lean_dec(v___x_2478_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2488_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2484_; lean_object* v___x_2486_; 
v___x_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2484_, 0, v_res_2480_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 1, v___x_2484_);
v___x_2486_ = v___x_2482_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_pos_2479_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v___x_2484_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
else
{
lean_object* v_pos_2489_; lean_object* v_err_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
v_pos_2489_ = lean_ctor_get(v___x_2478_, 0);
v_err_2490_ = lean_ctor_get(v___x_2478_, 1);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2492_ = v___x_2478_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_err_2490_);
lean_inc(v_pos_2489_);
lean_dec(v___x_2478_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_pos_2489_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v_err_2490_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed(lean_object* v_limits_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Std_Http_Protocol_H1_parseChunkSize___lam__0(v_limits_2498_, v___y_2499_);
lean_dec_ref(v_limits_2498_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0_spec__0(lean_object* v_as_2501_, size_t v_i_2502_, size_t v_stop_2503_, lean_object* v_b_2504_){
_start:
{
lean_object* v___y_2506_; uint8_t v___x_2510_; 
v___x_2510_ = lean_usize_dec_eq(v_i_2502_, v_stop_2503_);
if (v___x_2510_ == 0)
{
lean_object* v___x_2511_; 
v___x_2511_ = lean_array_uget_borrowed(v_as_2501_, v_i_2502_);
if (lean_obj_tag(v___x_2511_) == 0)
{
v___y_2506_ = v_b_2504_;
goto v___jp_2505_;
}
else
{
lean_object* v_val_2512_; lean_object* v___x_2513_; 
v_val_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_val_2512_);
v___x_2513_ = lean_array_push(v_b_2504_, v_val_2512_);
v___y_2506_ = v___x_2513_;
goto v___jp_2505_;
}
}
else
{
return v_b_2504_;
}
v___jp_2505_:
{
size_t v___x_2507_; size_t v___x_2508_; 
v___x_2507_ = ((size_t)1ULL);
v___x_2508_ = lean_usize_add(v_i_2502_, v___x_2507_);
v_i_2502_ = v___x_2508_;
v_b_2504_ = v___y_2506_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0_spec__0___boxed(lean_object* v_as_2514_, lean_object* v_i_2515_, lean_object* v_stop_2516_, lean_object* v_b_2517_){
_start:
{
size_t v_i_boxed_2518_; size_t v_stop_boxed_2519_; lean_object* v_res_2520_; 
v_i_boxed_2518_ = lean_unbox_usize(v_i_2515_);
lean_dec(v_i_2515_);
v_stop_boxed_2519_ = lean_unbox_usize(v_stop_2516_);
lean_dec(v_stop_2516_);
v_res_2520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0_spec__0(v_as_2514_, v_i_boxed_2518_, v_stop_boxed_2519_, v_b_2517_);
lean_dec_ref(v_as_2514_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0(lean_object* v_as_2523_, lean_object* v_start_2524_, lean_object* v_stop_2525_){
_start:
{
lean_object* v___x_2526_; uint8_t v___x_2527_; 
v___x_2526_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0___closed__0));
v___x_2527_ = lean_nat_dec_lt(v_start_2524_, v_stop_2525_);
if (v___x_2527_ == 0)
{
return v___x_2526_;
}
else
{
lean_object* v___x_2528_; uint8_t v___x_2529_; 
v___x_2528_ = lean_array_get_size(v_as_2523_);
v___x_2529_ = lean_nat_dec_le(v_stop_2525_, v___x_2528_);
if (v___x_2529_ == 0)
{
uint8_t v___x_2530_; 
v___x_2530_ = lean_nat_dec_lt(v_start_2524_, v___x_2528_);
if (v___x_2530_ == 0)
{
return v___x_2526_;
}
else
{
size_t v___x_2531_; size_t v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = lean_usize_of_nat(v_start_2524_);
v___x_2532_ = lean_usize_of_nat(v___x_2528_);
v___x_2533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0_spec__0(v_as_2523_, v___x_2531_, v___x_2532_, v___x_2526_);
return v___x_2533_;
}
}
else
{
size_t v___x_2534_; size_t v___x_2535_; lean_object* v___x_2536_; 
v___x_2534_ = lean_usize_of_nat(v_start_2524_);
v___x_2535_ = lean_usize_of_nat(v_stop_2525_);
v___x_2536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0_spec__0(v_as_2523_, v___x_2534_, v___x_2535_, v___x_2526_);
return v___x_2536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0___boxed(lean_object* v_as_2537_, lean_object* v_start_2538_, lean_object* v_stop_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0(v_as_2537_, v_start_2538_, v_stop_2539_);
lean_dec(v_stop_2539_);
lean_dec(v_start_2538_);
lean_dec_ref(v_as_2537_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize(lean_object* v_limits_2541_, lean_object* v_a_2542_){
_start:
{
lean_object* v___x_2543_; 
v___x_2543_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(v_a_2542_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_pos_2544_; lean_object* v_res_2545_; lean_object* v_maxChunkExtensions_2546_; lean_object* v___f_2547_; lean_object* v___x_2548_; 
v_pos_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_pos_2544_);
v_res_2545_ = lean_ctor_get(v___x_2543_, 1);
lean_inc(v_res_2545_);
lean_dec_ref_known(v___x_2543_, 2);
v_maxChunkExtensions_2546_ = lean_ctor_get(v_limits_2541_, 10);
lean_inc(v_maxChunkExtensions_2546_);
v___f_2547_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2547_, 0, v_limits_2541_);
v___x_2548_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___f_2547_, v_maxChunkExtensions_2546_, v_pos_2544_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_pos_2549_; lean_object* v_res_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v_pos_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_pos_2549_);
v_res_2550_ = lean_ctor_get(v___x_2548_, 1);
lean_inc(v_res_2550_);
lean_dec_ref_known(v___x_2548_, 2);
v___x_2551_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2552_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2551_, v_pos_2549_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_pos_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2564_; 
v_pos_2553_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2564_ == 0)
{
lean_object* v_unused_2565_; 
v_unused_2565_ = lean_ctor_get(v___x_2552_, 1);
lean_dec(v_unused_2565_);
v___x_2555_ = v___x_2552_;
v_isShared_2556_ = v_isSharedCheck_2564_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_pos_2553_);
lean_dec(v___x_2552_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2564_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2562_; 
v___x_2557_ = lean_unsigned_to_nat(0u);
v___x_2558_ = lean_array_get_size(v_res_2550_);
v___x_2559_ = l_Array_filterMapM___at___00Std_Http_Protocol_H1_parseChunkSize_spec__0(v_res_2550_, v___x_2557_, v___x_2558_);
lean_dec(v_res_2550_);
v___x_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2560_, 0, v_res_2545_);
lean_ctor_set(v___x_2560_, 1, v___x_2559_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 1, v___x_2560_);
v___x_2562_ = v___x_2555_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_pos_2553_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v___x_2560_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
else
{
lean_object* v_pos_2566_; lean_object* v_err_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
lean_dec(v_res_2550_);
lean_dec(v_res_2545_);
v_pos_2566_ = lean_ctor_get(v___x_2552_, 0);
v_err_2567_ = lean_ctor_get(v___x_2552_, 1);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2552_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_err_2567_);
lean_inc(v_pos_2566_);
lean_dec(v___x_2552_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_pos_2566_);
lean_ctor_set(v_reuseFailAlloc_2573_, 1, v_err_2567_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
else
{
lean_object* v_pos_2575_; lean_object* v_err_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
lean_dec(v_res_2545_);
v_pos_2575_ = lean_ctor_get(v___x_2548_, 0);
v_err_2576_ = lean_ctor_get(v___x_2548_, 1);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v___x_2548_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_err_2576_);
lean_inc(v_pos_2575_);
lean_dec(v___x_2548_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_pos_2575_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v_err_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
else
{
lean_object* v_pos_2584_; lean_object* v_err_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_dec_ref(v_limits_2541_);
v_pos_2584_ = lean_ctor_get(v___x_2543_, 0);
v_err_2585_ = lean_ctor_get(v___x_2543_, 1);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2543_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_err_2585_);
lean_inc(v_pos_2584_);
lean_dec(v___x_2543_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_pos_2584_);
lean_ctor_set(v_reuseFailAlloc_2591_, 1, v_err_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl(lean_object* v_x_2593_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = lean_obj_tag_nat(v_x_2593_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl___boxed(lean_object* v_x_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl(v_x_2595_);
lean_dec_ref(v_x_2595_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(lean_object* v_t_2597_, lean_object* v_k_2598_){
_start:
{
if (lean_obj_tag(v_t_2597_) == 0)
{
lean_object* v_data_2599_; lean_object* v___x_2600_; 
v_data_2599_ = lean_ctor_get(v_t_2597_, 0);
lean_inc_ref(v_data_2599_);
lean_dec_ref_known(v_t_2597_, 1);
v___x_2600_ = lean_apply_1(v_k_2598_, v_data_2599_);
return v___x_2600_;
}
else
{
lean_object* v_data_2601_; lean_object* v_remaining_2602_; lean_object* v___x_2603_; 
v_data_2601_ = lean_ctor_get(v_t_2597_, 0);
lean_inc_ref(v_data_2601_);
v_remaining_2602_ = lean_ctor_get(v_t_2597_, 1);
lean_inc(v_remaining_2602_);
lean_dec_ref_known(v_t_2597_, 2);
v___x_2603_ = lean_apply_2(v_k_2598_, v_data_2601_, v_remaining_2602_);
return v___x_2603_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim(lean_object* v_motive_2604_, lean_object* v_ctorIdx_2605_, lean_object* v_t_2606_, lean_object* v_h_2607_, lean_object* v_k_2608_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_2606_, v_k_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___boxed(lean_object* v_motive_2610_, lean_object* v_ctorIdx_2611_, lean_object* v_t_2612_, lean_object* v_h_2613_, lean_object* v_k_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim(v_motive_2610_, v_ctorIdx_2611_, v_t_2612_, v_h_2613_, v_k_2614_);
lean_dec(v_ctorIdx_2611_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim___redArg(lean_object* v_t_2616_, lean_object* v_complete_2617_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_2616_, v_complete_2617_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim(lean_object* v_motive_2619_, lean_object* v_t_2620_, lean_object* v_h_2621_, lean_object* v_complete_2622_){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_2620_, v_complete_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim___redArg(lean_object* v_t_2624_, lean_object* v_incomplete_2625_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_2624_, v_incomplete_2625_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim(lean_object* v_motive_2627_, lean_object* v_t_2628_, lean_object* v_h_2629_, lean_object* v_incomplete_2630_){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_2628_, v_incomplete_2630_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkPartial(lean_object* v_limits_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Std_Http_Protocol_H1_parseChunkSize(v_limits_2632_, v_a_2633_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_res_2635_; lean_object* v_pos_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2676_; 
v_res_2635_ = lean_ctor_get(v___x_2634_, 1);
v_pos_2636_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2638_ = v___x_2634_;
v_isShared_2639_ = v_isSharedCheck_2676_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_res_2635_);
lean_inc(v_pos_2636_);
lean_dec(v___x_2634_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2676_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v_fst_2640_; lean_object* v_snd_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2675_; 
v_fst_2640_ = lean_ctor_get(v_res_2635_, 0);
v_snd_2641_ = lean_ctor_get(v_res_2635_, 1);
v_isSharedCheck_2675_ = !lean_is_exclusive(v_res_2635_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2643_ = v_res_2635_;
v_isShared_2644_ = v_isSharedCheck_2675_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_snd_2641_);
lean_inc(v_fst_2640_);
lean_dec(v_res_2635_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2675_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2645_; uint8_t v___x_2646_; 
v___x_2645_ = lean_unsigned_to_nat(0u);
v___x_2646_ = lean_nat_dec_eq(v_fst_2640_, v___x_2645_);
if (v___x_2646_ == 0)
{
lean_object* v___x_2647_; 
lean_del_object(v___x_2638_);
v___x_2647_ = l_Std_Internal_Parsec_ByteArray_take(v_fst_2640_, v_pos_2636_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_pos_2648_; lean_object* v_res_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2661_; 
v_pos_2648_ = lean_ctor_get(v___x_2647_, 0);
v_res_2649_ = lean_ctor_get(v___x_2647_, 1);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2651_ = v___x_2647_;
v_isShared_2652_ = v_isSharedCheck_2661_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_res_2649_);
lean_inc(v_pos_2648_);
lean_dec(v___x_2647_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2661_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 1, v_res_2649_);
lean_ctor_set(v___x_2643_, 0, v_snd_2641_);
v___x_2654_ = v___x_2643_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_snd_2641_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v_res_2649_);
v___x_2654_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2658_; 
v___x_2655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2655_, 0, v_fst_2640_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
v___x_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2655_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 1, v___x_2656_);
v___x_2658_ = v___x_2651_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_pos_2648_);
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
else
{
lean_object* v_pos_2662_; lean_object* v_err_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
lean_del_object(v___x_2643_);
lean_dec(v_snd_2641_);
lean_dec(v_fst_2640_);
v_pos_2662_ = lean_ctor_get(v___x_2647_, 0);
v_err_2663_ = lean_ctor_get(v___x_2647_, 1);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2665_ = v___x_2647_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_err_2663_);
lean_inc(v_pos_2662_);
lean_dec(v___x_2647_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_pos_2662_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v_err_2663_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
else
{
lean_object* v___x_2671_; lean_object* v___x_2673_; 
lean_del_object(v___x_2643_);
lean_dec(v_snd_2641_);
lean_dec(v_fst_2640_);
v___x_2671_ = lean_box(0);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 1, v___x_2671_);
v___x_2673_ = v___x_2638_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_pos_2636_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
}
else
{
lean_object* v_pos_2677_; lean_object* v_err_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
v_pos_2677_ = lean_ctor_get(v___x_2634_, 0);
v_err_2678_ = lean_ctor_get(v___x_2634_, 1);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2634_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_err_2678_);
lean_inc(v_pos_2677_);
lean_dec(v___x_2634_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_pos_2677_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_err_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData(lean_object* v_size_2686_, lean_object* v_it_2687_){
_start:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; uint8_t v___x_2690_; 
v___x_2688_ = l_ByteArray_Iterator_remainingBytes(v_it_2687_);
v___x_2689_ = lean_unsigned_to_nat(0u);
v___x_2690_ = lean_nat_dec_eq(v___x_2688_, v___x_2689_);
if (v___x_2690_ == 0)
{
uint8_t v___x_2691_; 
v___x_2691_ = lean_nat_dec_lt(v___x_2688_, v_size_2686_);
if (v___x_2691_ == 0)
{
lean_object* v_array_2692_; lean_object* v_idx_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2712_; 
lean_dec(v___x_2688_);
v_array_2692_ = lean_ctor_get(v_it_2687_, 0);
v_idx_2693_ = lean_ctor_get(v_it_2687_, 1);
v_isSharedCheck_2712_ = !lean_is_exclusive(v_it_2687_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2695_ = v_it_2687_;
v_isShared_2696_ = v_isSharedCheck_2712_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_idx_2693_);
lean_inc(v_array_2692_);
lean_dec(v_it_2687_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2712_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2697_; lean_object* v___x_2699_; 
v___x_2697_ = lean_nat_add(v_idx_2693_, v_size_2686_);
lean_inc(v___x_2697_);
lean_inc_ref(v_array_2692_);
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 1, v___x_2697_);
v___x_2699_ = v___x_2695_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_array_2692_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
lean_object* v_lower_2701_; lean_object* v_upper_2702_; lean_object* v___x_2706_; lean_object* v___y_2708_; uint8_t v___x_2710_; 
v___x_2706_ = lean_byte_array_size(v_array_2692_);
v___x_2710_ = lean_nat_dec_le(v_idx_2693_, v___x_2689_);
if (v___x_2710_ == 0)
{
v___y_2708_ = v_idx_2693_;
goto v___jp_2707_;
}
else
{
lean_dec(v_idx_2693_);
v___y_2708_ = v___x_2689_;
goto v___jp_2707_;
}
v___jp_2700_:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2703_ = l_ByteArray_toByteSlice(v_array_2692_, v_lower_2701_, v_upper_2702_);
v___x_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
v___x_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2699_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
return v___x_2705_;
}
v___jp_2707_:
{
uint8_t v___x_2709_; 
v___x_2709_ = lean_nat_dec_le(v___x_2697_, v___x_2706_);
if (v___x_2709_ == 0)
{
lean_dec(v___x_2697_);
v_lower_2701_ = v___y_2708_;
v_upper_2702_ = v___x_2706_;
goto v___jp_2700_;
}
else
{
v_lower_2701_ = v___y_2708_;
v_upper_2702_ = v___x_2697_;
goto v___jp_2700_;
}
}
}
}
}
else
{
lean_object* v_array_2713_; lean_object* v_idx_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2734_; 
v_array_2713_ = lean_ctor_get(v_it_2687_, 0);
v_idx_2714_ = lean_ctor_get(v_it_2687_, 1);
v_isSharedCheck_2734_ = !lean_is_exclusive(v_it_2687_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2716_ = v_it_2687_;
v_isShared_2717_ = v_isSharedCheck_2734_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_idx_2714_);
lean_inc(v_array_2713_);
lean_dec(v_it_2687_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2734_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2718_; lean_object* v___x_2720_; 
v___x_2718_ = lean_nat_add(v_idx_2714_, v___x_2688_);
lean_inc(v___x_2718_);
lean_inc_ref(v_array_2713_);
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 1, v___x_2718_);
v___x_2720_ = v___x_2716_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_array_2713_);
lean_ctor_set(v_reuseFailAlloc_2733_, 1, v___x_2718_);
v___x_2720_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
lean_object* v_lower_2722_; lean_object* v_upper_2723_; lean_object* v___x_2728_; lean_object* v___y_2730_; uint8_t v___x_2732_; 
v___x_2728_ = lean_byte_array_size(v_array_2713_);
v___x_2732_ = lean_nat_dec_le(v_idx_2714_, v___x_2689_);
if (v___x_2732_ == 0)
{
v___y_2730_ = v_idx_2714_;
goto v___jp_2729_;
}
else
{
lean_dec(v_idx_2714_);
v___y_2730_ = v___x_2689_;
goto v___jp_2729_;
}
v___jp_2721_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2724_ = l_ByteArray_toByteSlice(v_array_2713_, v_lower_2722_, v_upper_2723_);
v___x_2725_ = lean_nat_sub(v_size_2686_, v___x_2688_);
lean_dec(v___x_2688_);
v___x_2726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2724_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2720_);
lean_ctor_set(v___x_2727_, 1, v___x_2726_);
return v___x_2727_;
}
v___jp_2729_:
{
uint8_t v___x_2731_; 
v___x_2731_ = lean_nat_dec_le(v___x_2718_, v___x_2728_);
if (v___x_2731_ == 0)
{
lean_dec(v___x_2718_);
v_lower_2722_ = v___y_2730_;
v_upper_2723_ = v___x_2728_;
goto v___jp_2721_;
}
else
{
v_lower_2722_ = v___y_2730_;
v_upper_2723_ = v___x_2718_;
goto v___jp_2721_;
}
}
}
}
}
}
else
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
lean_dec(v___x_2688_);
v___x_2735_ = lean_box(0);
v___x_2736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2736_, 0, v_it_2687_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
return v___x_2736_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData___boxed(lean_object* v_size_2737_, lean_object* v_it_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_2737_, v_it_2738_);
lean_dec(v_size_2737_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData(lean_object* v_size_2740_, lean_object* v_a_2741_){
_start:
{
lean_object* v___x_2742_; 
v___x_2742_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_res_2743_; 
v_res_2743_ = lean_ctor_get(v___x_2742_, 1);
if (lean_obj_tag(v_res_2743_) == 0)
{
lean_object* v_pos_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
lean_inc_ref(v_res_2743_);
v_pos_2744_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_pos_2744_);
lean_dec_ref_known(v___x_2742_, 2);
v___x_2745_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2746_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2745_, v_pos_2744_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_pos_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
v_pos_2747_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2754_ == 0)
{
lean_object* v_unused_2755_; 
v_unused_2755_ = lean_ctor_get(v___x_2746_, 1);
lean_dec(v_unused_2755_);
v___x_2749_ = v___x_2746_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_pos_2747_);
lean_dec(v___x_2746_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 1, v_res_2743_);
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_pos_2747_);
lean_ctor_set(v_reuseFailAlloc_2753_, 1, v_res_2743_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
else
{
lean_object* v_pos_2756_; lean_object* v_err_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
lean_dec_ref_known(v_res_2743_, 1);
v_pos_2756_ = lean_ctor_get(v___x_2746_, 0);
v_err_2757_ = lean_ctor_get(v___x_2746_, 1);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2746_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_err_2757_);
lean_inc(v_pos_2756_);
lean_dec(v___x_2746_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_pos_2756_);
lean_ctor_set(v_reuseFailAlloc_2763_, 1, v_err_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
else
{
return v___x_2742_;
}
}
else
{
return v___x_2742_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData___boxed(lean_object* v_size_2765_, lean_object* v_a_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l_Std_Http_Protocol_H1_parseChunkSizedData(v_size_2765_, v_a_2766_);
lean_dec(v_size_2765_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField_spec__0(lean_object* v_s_2768_, lean_object* v_p_2769_){
_start:
{
lean_object* v___y_2771_; lean_object* v___y_2772_; uint32_t v___y_2776_; lean_object* v___x_2788_; uint8_t v_decide_2789_; 
v___x_2788_ = lean_string_utf8_byte_size(v_s_2768_);
v_decide_2789_ = lean_nat_dec_eq(v_p_2769_, v___x_2788_);
if (v_decide_2789_ == 0)
{
uint32_t v___x_2790_; uint32_t v___x_2791_; uint8_t v___x_2792_; 
v___x_2790_ = lean_string_utf8_get_fast(v_s_2768_, v_p_2769_);
v___x_2791_ = 65;
v___x_2792_ = lean_uint32_dec_le(v___x_2791_, v___x_2790_);
if (v___x_2792_ == 0)
{
v___y_2776_ = v___x_2790_;
goto v___jp_2775_;
}
else
{
uint32_t v___x_2793_; uint8_t v___x_2794_; 
v___x_2793_ = 90;
v___x_2794_ = lean_uint32_dec_le(v___x_2790_, v___x_2793_);
if (v___x_2794_ == 0)
{
v___y_2776_ = v___x_2790_;
goto v___jp_2775_;
}
else
{
uint32_t v___x_2795_; uint32_t v___x_2796_; 
v___x_2795_ = 32;
v___x_2796_ = lean_uint32_add(v___x_2790_, v___x_2795_);
v___y_2776_ = v___x_2796_;
goto v___jp_2775_;
}
}
}
else
{
lean_dec(v_p_2769_);
return v_s_2768_;
}
v___jp_2770_:
{
lean_object* v___x_2773_; 
v___x_2773_ = lean_nat_add(v_p_2769_, v___y_2772_);
lean_dec(v_p_2769_);
v_s_2768_ = v___y_2771_;
v_p_2769_ = v___x_2773_;
goto _start;
}
v___jp_2775_:
{
lean_object* v___x_2777_; uint32_t v___x_2778_; uint8_t v___x_2779_; 
lean_inc(v_p_2769_);
v___x_2777_ = lean_string_utf8_set(v_s_2768_, v_p_2769_, v___y_2776_);
v___x_2778_ = 127;
v___x_2779_ = lean_uint32_dec_le(v___y_2776_, v___x_2778_);
if (v___x_2779_ == 0)
{
uint32_t v___x_2780_; uint8_t v___x_2781_; 
v___x_2780_ = 2047;
v___x_2781_ = lean_uint32_dec_le(v___y_2776_, v___x_2780_);
if (v___x_2781_ == 0)
{
uint32_t v___x_2782_; uint8_t v___x_2783_; 
v___x_2782_ = 65535;
v___x_2783_ = lean_uint32_dec_le(v___y_2776_, v___x_2782_);
if (v___x_2783_ == 0)
{
lean_object* v___x_2784_; 
v___x_2784_ = lean_unsigned_to_nat(4u);
v___y_2771_ = v___x_2777_;
v___y_2772_ = v___x_2784_;
goto v___jp_2770_;
}
else
{
lean_object* v___x_2785_; 
v___x_2785_ = lean_unsigned_to_nat(3u);
v___y_2771_ = v___x_2777_;
v___y_2772_ = v___x_2785_;
goto v___jp_2770_;
}
}
else
{
lean_object* v___x_2786_; 
v___x_2786_ = lean_unsigned_to_nat(2u);
v___y_2771_ = v___x_2777_;
v___y_2772_ = v___x_2786_;
goto v___jp_2770_;
}
}
else
{
lean_object* v___x_2787_; 
v___x_2787_ = lean_unsigned_to_nat(1u);
v___y_2771_ = v___x_2777_;
v___y_2772_ = v___x_2787_;
goto v___jp_2770_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField(lean_object* v_name_2804_){
_start:
{
lean_object* v___x_2805_; lean_object* v_n_2806_; lean_object* v___x_2807_; uint8_t v___x_2808_; 
v___x_2805_ = lean_unsigned_to_nat(0u);
v_n_2806_ = l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField_spec__0(v_name_2804_, v___x_2805_);
v___x_2807_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__0));
v___x_2808_ = lean_string_dec_eq(v_n_2806_, v___x_2807_);
if (v___x_2808_ == 0)
{
lean_object* v___x_2809_; uint8_t v___x_2810_; 
v___x_2809_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__1));
v___x_2810_ = lean_string_dec_eq(v_n_2806_, v___x_2809_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; uint8_t v___x_2812_; 
v___x_2811_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__2));
v___x_2812_ = lean_string_dec_eq(v_n_2806_, v___x_2811_);
if (v___x_2812_ == 0)
{
lean_object* v___x_2813_; uint8_t v___x_2814_; 
v___x_2813_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__3));
v___x_2814_ = lean_string_dec_eq(v_n_2806_, v___x_2813_);
if (v___x_2814_ == 0)
{
lean_object* v___x_2815_; uint8_t v___x_2816_; 
v___x_2815_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__4));
v___x_2816_ = lean_string_dec_eq(v_n_2806_, v___x_2815_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2817_; uint8_t v___x_2818_; 
v___x_2817_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__5));
v___x_2818_ = lean_string_dec_eq(v_n_2806_, v___x_2817_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2819_; uint8_t v___x_2820_; 
v___x_2819_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__6));
v___x_2820_ = lean_string_dec_eq(v_n_2806_, v___x_2819_);
lean_dec_ref(v_n_2806_);
return v___x_2820_;
}
else
{
lean_dec_ref(v_n_2806_);
return v___x_2818_;
}
}
else
{
lean_dec_ref(v_n_2806_);
return v___x_2816_;
}
}
else
{
lean_dec_ref(v_n_2806_);
return v___x_2814_;
}
}
else
{
lean_dec_ref(v_n_2806_);
return v___x_2812_;
}
}
else
{
lean_dec_ref(v_n_2806_);
return v___x_2810_;
}
}
else
{
lean_dec_ref(v_n_2806_);
return v___x_2808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___boxed(lean_object* v_name_2821_){
_start:
{
uint8_t v_res_2822_; lean_object* v_r_2823_; 
v_res_2822_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField(v_name_2821_);
v_r_2823_ = lean_box(v_res_2822_);
return v_r_2823_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(lean_object* v_name_2829_){
_start:
{
lean_object* v___x_2830_; lean_object* v_n_2831_; uint8_t v___x_2832_; 
v___x_2830_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_name_2829_);
v_n_2831_ = l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField_spec__0(v_name_2829_, v___x_2830_);
v___x_2832_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField(v_name_2829_);
if (v___x_2832_ == 0)
{
lean_object* v___x_2833_; uint8_t v___x_2834_; 
v___x_2833_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0));
v___x_2834_ = lean_string_dec_eq(v_n_2831_, v___x_2833_);
if (v___x_2834_ == 0)
{
lean_object* v___x_2835_; uint8_t v___x_2836_; 
v___x_2835_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1));
v___x_2836_ = lean_string_dec_eq(v_n_2831_, v___x_2835_);
if (v___x_2836_ == 0)
{
lean_object* v___x_2837_; uint8_t v___x_2838_; 
v___x_2837_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2));
v___x_2838_ = lean_string_dec_eq(v_n_2831_, v___x_2837_);
if (v___x_2838_ == 0)
{
lean_object* v___x_2839_; uint8_t v___x_2840_; 
v___x_2839_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3));
v___x_2840_ = lean_string_dec_eq(v_n_2831_, v___x_2839_);
if (v___x_2840_ == 0)
{
lean_object* v___x_2841_; uint8_t v___x_2842_; 
v___x_2841_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4));
v___x_2842_ = lean_string_dec_eq(v_n_2831_, v___x_2841_);
lean_dec_ref(v_n_2831_);
return v___x_2842_;
}
else
{
lean_dec_ref(v_n_2831_);
return v___x_2840_;
}
}
else
{
lean_dec_ref(v_n_2831_);
return v___x_2838_;
}
}
else
{
lean_dec_ref(v_n_2831_);
return v___x_2836_;
}
}
else
{
lean_dec_ref(v_n_2831_);
return v___x_2834_;
}
}
else
{
lean_dec_ref(v_n_2831_);
return v___x_2832_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___boxed(lean_object* v_name_2843_){
_start:
{
uint8_t v_res_2844_; lean_object* v_r_2845_; 
v_res_2844_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_name_2843_);
v_r_2845_ = lean_box(v_res_2844_);
return v_r_2845_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailerHeader(lean_object* v_limits_2847_, uint8_t v_strict_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_2847_, v_a_2849_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_res_2851_; 
v_res_2851_ = lean_ctor_get(v___x_2850_, 1);
lean_inc(v_res_2851_);
if (lean_obj_tag(v_res_2851_) == 1)
{
lean_object* v_val_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2874_; 
v_val_2852_ = lean_ctor_get(v_res_2851_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v_res_2851_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2854_ = v_res_2851_;
v_isShared_2855_ = v_isSharedCheck_2874_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_val_2852_);
lean_dec(v_res_2851_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2874_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v_pos_2856_; lean_object* v_fst_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2872_; 
v_pos_2856_ = lean_ctor_get(v___x_2850_, 0);
v_fst_2857_ = lean_ctor_get(v_val_2852_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v_val_2852_);
if (v_isSharedCheck_2872_ == 0)
{
lean_object* v_unused_2873_; 
v_unused_2873_ = lean_ctor_get(v_val_2852_, 1);
lean_dec(v_unused_2873_);
v___x_2859_ = v_val_2852_;
v_isShared_2860_ = v_isSharedCheck_2872_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_fst_2857_);
lean_dec(v_val_2852_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2872_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
uint8_t v___x_2870_; 
lean_inc(v_fst_2857_);
v___x_2870_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField(v_fst_2857_);
if (v___x_2870_ == 0)
{
if (v_strict_2848_ == 0)
{
lean_del_object(v___x_2859_);
lean_dec(v_fst_2857_);
lean_del_object(v___x_2854_);
return v___x_2850_;
}
else
{
uint8_t v___x_2871_; 
lean_inc(v_fst_2857_);
v___x_2871_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_fst_2857_);
if (v___x_2871_ == 0)
{
lean_del_object(v___x_2859_);
lean_dec(v_fst_2857_);
lean_del_object(v___x_2854_);
return v___x_2850_;
}
else
{
lean_inc(v_pos_2856_);
lean_dec_ref_known(v___x_2850_, 2);
goto v___jp_2861_;
}
}
}
else
{
lean_inc(v_pos_2856_);
lean_dec_ref_known(v___x_2850_, 2);
goto v___jp_2861_;
}
v___jp_2861_:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2865_; 
v___x_2862_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseTrailerHeader___closed__0));
v___x_2863_ = lean_string_append(v___x_2862_, v_fst_2857_);
lean_dec(v_fst_2857_);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 0, v___x_2863_);
v___x_2865_ = v___x_2854_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___x_2863_);
v___x_2865_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
lean_object* v___x_2867_; 
if (v_isShared_2860_ == 0)
{
lean_ctor_set_tag(v___x_2859_, 1);
lean_ctor_set(v___x_2859_, 1, v___x_2865_);
lean_ctor_set(v___x_2859_, 0, v_pos_2856_);
v___x_2867_ = v___x_2859_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_pos_2856_);
lean_ctor_set(v_reuseFailAlloc_2868_, 1, v___x_2865_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
}
}
else
{
lean_dec(v_res_2851_);
return v___x_2850_;
}
}
else
{
return v___x_2850_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailerHeader___boxed(lean_object* v_limits_2875_, lean_object* v_strict_2876_, lean_object* v_a_2877_){
_start:
{
uint8_t v_strict_boxed_2878_; lean_object* v_res_2879_; 
v_strict_boxed_2878_ = lean_unbox(v_strict_2876_);
v_res_2879_ = l_Std_Http_Protocol_H1_parseTrailerHeader(v_limits_2875_, v_strict_boxed_2878_, v_a_2877_);
lean_dec_ref(v_limits_2875_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailers(lean_object* v_limits_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v_maxTrailerHeaders_2882_; uint8_t v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v_maxTrailerHeaders_2882_ = lean_ctor_get(v_limits_2880_, 17);
lean_inc(v_maxTrailerHeaders_2882_);
v___x_2883_ = 1;
v___x_2884_ = lean_box(v___x_2883_);
v___x_2885_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_parseTrailerHeader___boxed), 3, 2);
lean_closure_set(v___x_2885_, 0, v_limits_2880_);
lean_closure_set(v___x_2885_, 1, v___x_2884_);
v___x_2886_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___x_2885_, v_maxTrailerHeaders_2882_, v_a_2881_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v_pos_2887_; lean_object* v_res_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v_pos_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_pos_2887_);
v_res_2888_ = lean_ctor_get(v___x_2886_, 1);
lean_inc(v_res_2888_);
lean_dec_ref_known(v___x_2886_, 2);
v___x_2889_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2890_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2889_, v_pos_2887_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_pos_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
v_pos_2891_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2898_ == 0)
{
lean_object* v_unused_2899_; 
v_unused_2899_ = lean_ctor_get(v___x_2890_, 1);
lean_dec(v_unused_2899_);
v___x_2893_ = v___x_2890_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_pos_2891_);
lean_dec(v___x_2890_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 1, v_res_2888_);
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_pos_2891_);
lean_ctor_set(v_reuseFailAlloc_2897_, 1, v_res_2888_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
else
{
lean_object* v_pos_2900_; lean_object* v_err_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_dec(v_res_2888_);
v_pos_2900_ = lean_ctor_get(v___x_2890_, 0);
v_err_2901_ = lean_ctor_get(v___x_2890_, 1);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2890_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_err_2901_);
lean_inc(v_pos_2900_);
lean_dec(v___x_2890_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_pos_2900_);
lean_ctor_set(v_reuseFailAlloc_2907_, 1, v_err_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
else
{
return v___x_2886_;
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(uint8_t v_c_2909_){
_start:
{
uint32_t v___x_2910_; uint32_t v___x_2918_; uint8_t v___x_2919_; 
v___x_2910_ = lean_uint8_to_uint32(v_c_2909_);
v___x_2918_ = 33;
v___x_2919_ = lean_uint32_dec_le(v___x_2918_, v___x_2910_);
if (v___x_2919_ == 0)
{
goto v___jp_2911_;
}
else
{
uint32_t v___x_2920_; uint8_t v___x_2921_; 
v___x_2920_ = 126;
v___x_2921_ = lean_uint32_dec_le(v___x_2910_, v___x_2920_);
if (v___x_2921_ == 0)
{
goto v___jp_2911_;
}
else
{
return v___x_2921_;
}
}
v___jp_2911_:
{
uint32_t v___x_2912_; uint8_t v___x_2913_; 
v___x_2912_ = 128;
v___x_2913_ = lean_uint32_dec_le(v___x_2912_, v___x_2910_);
if (v___x_2913_ == 0)
{
uint32_t v___x_2914_; uint8_t v___x_2915_; 
v___x_2914_ = 32;
v___x_2915_ = lean_uint32_dec_eq(v___x_2910_, v___x_2914_);
if (v___x_2915_ == 0)
{
uint32_t v___x_2916_; uint8_t v___x_2917_; 
v___x_2916_ = 9;
v___x_2917_ = lean_uint32_dec_eq(v___x_2910_, v___x_2916_);
return v___x_2917_;
}
else
{
return v___x_2915_;
}
}
else
{
return v___x_2913_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte___boxed(lean_object* v_c_2922_){
_start:
{
uint8_t v_c_boxed_2923_; uint8_t v_res_2924_; lean_object* v_r_2925_; 
v_c_boxed_2923_ = lean_unbox(v_c_2922_);
v_res_2924_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(v_c_boxed_2923_);
v_r_2925_ = lean_box(v_res_2924_);
return v_r_2925_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(lean_object* v_limits_2926_, lean_object* v_a_2927_){
_start:
{
lean_object* v_maxReasonPhraseLength_2928_; lean_object* v___f_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v_snd_2932_; lean_object* v_snd_2933_; uint8_t v___x_2934_; 
v_maxReasonPhraseLength_2928_ = lean_ctor_get(v_limits_2926_, 16);
v___f_2929_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1));
v___x_2930_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2927_);
v___x_2931_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2929_, v_maxReasonPhraseLength_2928_, v___x_2930_, v_a_2927_);
v_snd_2932_ = lean_ctor_get(v___x_2931_, 1);
lean_inc(v_snd_2932_);
v_snd_2933_ = lean_ctor_get(v_snd_2932_, 1);
v___x_2934_ = lean_unbox(v_snd_2933_);
if (v___x_2934_ == 0)
{
lean_object* v_fst_2935_; lean_object* v_fst_2936_; lean_object* v_array_2937_; lean_object* v_idx_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2958_; 
v_fst_2935_ = lean_ctor_get(v___x_2931_, 0);
lean_inc(v_fst_2935_);
lean_dec_ref(v___x_2931_);
v_fst_2936_ = lean_ctor_get(v_snd_2932_, 0);
lean_inc(v_fst_2936_);
lean_dec(v_snd_2932_);
v_array_2937_ = lean_ctor_get(v_a_2927_, 0);
v_idx_2938_ = lean_ctor_get(v_a_2927_, 1);
v_isSharedCheck_2958_ = !lean_is_exclusive(v_a_2927_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2940_ = v_a_2927_;
v_isShared_2941_ = v_isSharedCheck_2958_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_idx_2938_);
lean_inc(v_array_2937_);
lean_dec(v_a_2927_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2958_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v_lower_2943_; lean_object* v_upper_2944_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___y_2955_; uint8_t v___x_2957_; 
v___x_2952_ = lean_nat_add(v_idx_2938_, v_fst_2935_);
lean_dec(v_fst_2935_);
v___x_2953_ = lean_byte_array_size(v_array_2937_);
v___x_2957_ = lean_nat_dec_le(v_idx_2938_, v___x_2930_);
if (v___x_2957_ == 0)
{
v___y_2955_ = v_idx_2938_;
goto v___jp_2954_;
}
else
{
lean_dec(v_idx_2938_);
v___y_2955_ = v___x_2930_;
goto v___jp_2954_;
}
v___jp_2942_:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2950_; 
v___x_2945_ = l_ByteArray_toByteSlice(v_array_2937_, v_lower_2943_, v_upper_2944_);
v___x_2946_ = l_ByteSlice_toByteArray(v___x_2945_);
v___x_2947_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0));
v___x_2948_ = l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go(v___x_2946_, v___x_2930_, v___x_2947_);
lean_dec_ref(v___x_2946_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 1, v___x_2948_);
lean_ctor_set(v___x_2940_, 0, v_fst_2936_);
v___x_2950_ = v___x_2940_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_fst_2936_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v___x_2948_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
v___jp_2954_:
{
uint8_t v___x_2956_; 
v___x_2956_ = lean_nat_dec_le(v___x_2952_, v___x_2953_);
if (v___x_2956_ == 0)
{
lean_dec(v___x_2952_);
v_lower_2943_ = v___y_2955_;
v_upper_2944_ = v___x_2953_;
goto v___jp_2942_;
}
else
{
v_lower_2943_ = v___y_2955_;
v_upper_2944_ = v___x_2952_;
goto v___jp_2942_;
}
}
}
}
else
{
lean_object* v_fst_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2967_; 
lean_dec_ref(v___x_2931_);
lean_dec_ref(v_a_2927_);
v_fst_2959_ = lean_ctor_get(v_snd_2932_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v_snd_2932_);
if (v_isSharedCheck_2967_ == 0)
{
lean_object* v_unused_2968_; 
v_unused_2968_ = lean_ctor_get(v_snd_2932_, 1);
lean_dec(v_unused_2968_);
v___x_2961_ = v_snd_2932_;
v_isShared_2962_ = v_isSharedCheck_2967_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_fst_2959_);
lean_dec(v_snd_2932_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2967_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2963_; lean_object* v___x_2965_; 
v___x_2963_ = lean_box(0);
if (v_isShared_2962_ == 0)
{
lean_ctor_set_tag(v___x_2961_, 1);
lean_ctor_set(v___x_2961_, 1, v___x_2963_);
v___x_2965_ = v___x_2961_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_fst_2959_);
lean_ctor_set(v_reuseFailAlloc_2966_, 1, v___x_2963_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___boxed(lean_object* v_limits_2969_, lean_object* v_a_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_2969_, v_a_2970_);
lean_dec_ref(v_limits_2969_);
return v_res_2971_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(lean_object* v_x_2972_){
_start:
{
if (lean_obj_tag(v_x_2972_) == 0)
{
uint8_t v___x_2973_; 
v___x_2973_ = 1;
return v___x_2973_;
}
else
{
lean_object* v_head_2974_; lean_object* v_tail_2975_; uint32_t v___x_2981_; uint32_t v___x_2982_; uint8_t v___x_2983_; 
v_head_2974_ = lean_ctor_get(v_x_2972_, 0);
v_tail_2975_ = lean_ctor_get(v_x_2972_, 1);
v___x_2981_ = 9;
v___x_2982_ = lean_unbox_uint32(v_head_2974_);
v___x_2983_ = lean_uint32_dec_eq(v___x_2982_, v___x_2981_);
if (v___x_2983_ == 0)
{
uint32_t v___x_2984_; uint32_t v___x_2985_; uint8_t v___x_2986_; 
v___x_2984_ = 32;
v___x_2985_ = lean_unbox_uint32(v_head_2974_);
v___x_2986_ = lean_uint32_dec_eq(v___x_2985_, v___x_2984_);
if (v___x_2986_ == 0)
{
uint32_t v___x_2987_; uint32_t v___x_2988_; uint8_t v___x_2989_; 
v___x_2987_ = 33;
v___x_2988_ = lean_unbox_uint32(v_head_2974_);
v___x_2989_ = lean_uint32_dec_le(v___x_2987_, v___x_2988_);
if (v___x_2989_ == 0)
{
goto v___jp_2976_;
}
else
{
uint32_t v___x_2990_; uint32_t v___x_2991_; uint8_t v___x_2992_; 
v___x_2990_ = 126;
v___x_2991_ = lean_unbox_uint32(v_head_2974_);
v___x_2992_ = lean_uint32_dec_le(v___x_2991_, v___x_2990_);
if (v___x_2992_ == 0)
{
goto v___jp_2976_;
}
else
{
v_x_2972_ = v_tail_2975_;
goto _start;
}
}
}
else
{
v_x_2972_ = v_tail_2975_;
goto _start;
}
}
else
{
v_x_2972_ = v_tail_2975_;
goto _start;
}
v___jp_2976_:
{
uint32_t v___x_2977_; uint32_t v___x_2978_; uint8_t v___x_2979_; 
v___x_2977_ = 128;
v___x_2978_ = lean_unbox_uint32(v_head_2974_);
v___x_2979_ = lean_uint32_dec_le(v___x_2977_, v___x_2978_);
if (v___x_2979_ == 0)
{
return v___x_2979_;
}
else
{
v_x_2972_ = v_tail_2975_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0___boxed(lean_object* v_x_2996_){
_start:
{
uint8_t v_res_2997_; lean_object* v_r_2998_; 
v_res_2997_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v_x_2996_);
lean_dec(v_x_2996_);
v_r_2998_ = lean_box(v_res_2997_);
return v_r_2998_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(lean_object* v_limits_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v___y_3008_; lean_object* v_array_3011_; lean_object* v_idx_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; 
v_array_3011_ = lean_ctor_get(v_a_3003_, 0);
v_idx_3012_ = lean_ctor_get(v_a_3003_, 1);
v___x_3013_ = lean_byte_array_size(v_array_3011_);
v___x_3014_ = lean_nat_dec_lt(v_idx_3012_, v___x_3013_);
if (v___x_3014_ == 0)
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = lean_box(0);
v___x_3016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3016_, 0, v_a_3003_);
lean_ctor_set(v___x_3016_, 1, v___x_3015_);
return v___x_3016_;
}
else
{
uint8_t v_c_3017_; uint8_t v___x_3018_; uint8_t v___x_3019_; 
v_c_3017_ = lean_byte_array_fget(v_array_3011_, v_idx_3012_);
v___x_3018_ = 48;
v___x_3019_ = lean_uint8_dec_le(v___x_3018_, v_c_3017_);
if (v___x_3019_ == 0)
{
goto v___jp_3004_;
}
else
{
uint8_t v___x_3020_; uint8_t v___x_3021_; 
v___x_3020_ = 57;
v___x_3021_ = lean_uint8_dec_le(v_c_3017_, v___x_3020_);
if (v___x_3021_ == 0)
{
goto v___jp_3004_;
}
else
{
lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3118_; 
lean_inc(v_idx_3012_);
lean_inc_ref(v_array_3011_);
v_isSharedCheck_3118_ = !lean_is_exclusive(v_a_3003_);
if (v_isSharedCheck_3118_ == 0)
{
lean_object* v_unused_3119_; lean_object* v_unused_3120_; 
v_unused_3119_ = lean_ctor_get(v_a_3003_, 1);
lean_dec(v_unused_3119_);
v_unused_3120_ = lean_ctor_get(v_a_3003_, 0);
lean_dec(v_unused_3120_);
v___x_3023_ = v_a_3003_;
v_isShared_3024_ = v_isSharedCheck_3118_;
goto v_resetjp_3022_;
}
else
{
lean_dec(v_a_3003_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3118_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v_it_x27_3028_; 
v___x_3025_ = lean_unsigned_to_nat(1u);
v___x_3026_ = lean_nat_add(v_idx_3012_, v___x_3025_);
lean_dec(v_idx_3012_);
lean_inc(v___x_3026_);
lean_inc_ref(v_array_3011_);
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 1, v___x_3026_);
v_it_x27_3028_ = v___x_3023_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_array_3011_);
lean_ctor_set(v_reuseFailAlloc_3117_, 1, v___x_3026_);
v_it_x27_3028_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
uint8_t v___x_3032_; 
v___x_3032_ = lean_nat_dec_lt(v___x_3026_, v___x_3013_);
if (v___x_3032_ == 0)
{
lean_object* v___x_3033_; lean_object* v___x_3034_; 
lean_dec(v___x_3026_);
lean_dec_ref(v_array_3011_);
v___x_3033_ = lean_box(0);
v___x_3034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3034_, 0, v_it_x27_3028_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
return v___x_3034_;
}
else
{
uint8_t v_c_3035_; uint8_t v___x_3036_; 
v_c_3035_ = lean_byte_array_fget(v_array_3011_, v___x_3026_);
v___x_3036_ = lean_uint8_dec_le(v___x_3018_, v_c_3035_);
if (v___x_3036_ == 0)
{
lean_dec(v___x_3026_);
lean_dec_ref(v_array_3011_);
goto v___jp_3029_;
}
else
{
uint8_t v___x_3037_; 
v___x_3037_ = lean_uint8_dec_le(v_c_3035_, v___x_3020_);
if (v___x_3037_ == 0)
{
lean_dec(v___x_3026_);
lean_dec_ref(v_array_3011_);
goto v___jp_3029_;
}
else
{
lean_object* v___x_3038_; lean_object* v_it_x27_3039_; uint8_t v___x_3043_; 
lean_dec_ref(v_it_x27_3028_);
v___x_3038_ = lean_nat_add(v___x_3026_, v___x_3025_);
lean_dec(v___x_3026_);
lean_inc(v___x_3038_);
lean_inc_ref(v_array_3011_);
v_it_x27_3039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3039_, 0, v_array_3011_);
lean_ctor_set(v_it_x27_3039_, 1, v___x_3038_);
v___x_3043_ = lean_nat_dec_lt(v___x_3038_, v___x_3013_);
if (v___x_3043_ == 0)
{
lean_object* v___x_3044_; lean_object* v___x_3045_; 
lean_dec(v___x_3038_);
lean_dec_ref(v_array_3011_);
v___x_3044_ = lean_box(0);
v___x_3045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3045_, 0, v_it_x27_3039_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
return v___x_3045_;
}
else
{
uint8_t v_c_3046_; uint8_t v___x_3047_; 
v_c_3046_ = lean_byte_array_fget(v_array_3011_, v___x_3038_);
v___x_3047_ = lean_uint8_dec_le(v___x_3018_, v_c_3046_);
if (v___x_3047_ == 0)
{
lean_dec(v___x_3038_);
lean_dec_ref(v_array_3011_);
goto v___jp_3040_;
}
else
{
uint8_t v___x_3048_; 
v___x_3048_ = lean_uint8_dec_le(v_c_3046_, v___x_3020_);
if (v___x_3048_ == 0)
{
lean_dec(v___x_3038_);
lean_dec_ref(v_array_3011_);
goto v___jp_3040_;
}
else
{
lean_object* v___x_3049_; uint32_t v___x_3050_; uint32_t v___x_3051_; lean_object* v___x_3052_; lean_object* v_it_x27_3053_; uint32_t v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v_pos_3097_; lean_object* v_idx_3098_; lean_object* v_err_3099_; uint8_t v___x_3103_; 
lean_dec_ref_known(v_it_x27_3039_, 2);
v___x_3049_ = lean_unsigned_to_nat(48u);
v___x_3050_ = lean_uint8_to_uint32(v_c_3017_);
v___x_3051_ = lean_uint8_to_uint32(v_c_3035_);
v___x_3052_ = lean_nat_add(v___x_3038_, v___x_3025_);
lean_dec(v___x_3038_);
lean_inc(v___x_3052_);
lean_inc_ref(v_array_3011_);
v_it_x27_3053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3053_, 0, v_array_3011_);
lean_ctor_set(v_it_x27_3053_, 1, v___x_3052_);
v___x_3054_ = lean_uint8_to_uint32(v_c_3046_);
v___x_3055_ = lean_uint32_to_nat(v___x_3050_);
v___x_3056_ = lean_nat_sub(v___x_3055_, v___x_3049_);
lean_dec(v___x_3055_);
v___x_3057_ = lean_unsigned_to_nat(100u);
v___x_3058_ = lean_nat_mul(v___x_3056_, v___x_3057_);
lean_dec(v___x_3056_);
v___x_3059_ = lean_uint32_to_nat(v___x_3051_);
v___x_3060_ = lean_nat_sub(v___x_3059_, v___x_3049_);
lean_dec(v___x_3059_);
v___x_3061_ = lean_unsigned_to_nat(10u);
v___x_3062_ = lean_nat_mul(v___x_3060_, v___x_3061_);
lean_dec(v___x_3060_);
v___x_3063_ = lean_nat_add(v___x_3058_, v___x_3062_);
lean_dec(v___x_3062_);
lean_dec(v___x_3058_);
v___x_3064_ = lean_uint32_to_nat(v___x_3054_);
v___x_3065_ = lean_nat_sub(v___x_3064_, v___x_3049_);
lean_dec(v___x_3064_);
v___x_3066_ = lean_nat_add(v___x_3063_, v___x_3065_);
lean_dec(v___x_3065_);
lean_dec(v___x_3063_);
v___x_3103_ = lean_nat_dec_lt(v___x_3052_, v___x_3013_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3104_; 
lean_dec_ref(v_array_3011_);
v___x_3104_ = lean_box(0);
lean_inc(v___x_3052_);
v_pos_3097_ = v_it_x27_3053_;
v_idx_3098_ = v___x_3052_;
v_err_3099_ = v___x_3104_;
goto v___jp_3096_;
}
else
{
uint8_t v___x_3105_; uint8_t v_got_3106_; uint8_t v___x_3107_; 
v___x_3105_ = 32;
v_got_3106_ = lean_byte_array_fget(v_array_3011_, v___x_3052_);
v___x_3107_ = lean_uint8_dec_eq(v_got_3106_, v___x_3105_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; 
lean_dec_ref(v_array_3011_);
v___x_3108_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
lean_inc(v___x_3052_);
v_pos_3097_ = v_it_x27_3053_;
v_idx_3098_ = v___x_3052_;
v_err_3099_ = v___x_3108_;
goto v___jp_3096_;
}
else
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
lean_dec_ref_known(v_it_x27_3053_, 2);
v___x_3109_ = lean_nat_add(v___x_3052_, v___x_3025_);
v___x_3110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3110_, 0, v_array_3011_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
v___x_3111_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_3002_, v___x_3110_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_pos_3112_; lean_object* v_res_3113_; 
lean_dec(v___x_3052_);
v_pos_3112_ = lean_ctor_get(v___x_3111_, 0);
lean_inc(v_pos_3112_);
v_res_3113_ = lean_ctor_get(v___x_3111_, 1);
lean_inc(v_res_3113_);
lean_dec_ref_known(v___x_3111_, 2);
v___y_3068_ = v_pos_3112_;
v___y_3069_ = v_res_3113_;
goto v___jp_3067_;
}
else
{
lean_object* v_pos_3114_; lean_object* v___x_3115_; lean_object* v_idx_3116_; 
v_pos_3114_ = lean_ctor_get(v___x_3111_, 0);
lean_inc(v_pos_3114_);
lean_dec_ref_known(v___x_3111_, 2);
v___x_3115_ = lean_box(0);
v_idx_3116_ = lean_ctor_get(v_pos_3114_, 1);
lean_inc(v_idx_3116_);
v_pos_3097_ = v_pos_3114_;
v_idx_3098_ = v_idx_3116_;
v_err_3099_ = v___x_3115_;
goto v___jp_3096_;
}
}
}
v___jp_3067_:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3070_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3071_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3070_, v___y_3068_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_pos_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3085_; 
v_pos_3072_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3085_ == 0)
{
lean_object* v_unused_3086_; 
v_unused_3086_ = lean_ctor_get(v___x_3071_, 1);
lean_dec(v_unused_3086_);
v___x_3074_ = v___x_3071_;
v_isShared_3075_ = v_isSharedCheck_3085_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_pos_3072_);
lean_dec(v___x_3071_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3085_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3076_; uint8_t v___x_3077_; 
lean_inc_ref(v___y_3069_);
v___x_3076_ = l_String_toListImpl(v___y_3069_);
v___x_3077_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v___x_3076_);
lean_dec(v___x_3076_);
if (v___x_3077_ == 0)
{
lean_del_object(v___x_3074_);
lean_dec_ref(v___y_3069_);
lean_dec(v___x_3066_);
v___y_3008_ = v_pos_3072_;
goto v___jp_3007_;
}
else
{
lean_object* v___x_3078_; uint16_t v___x_3079_; lean_object* v___x_3080_; 
v___x_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3078_, 0, v___y_3069_);
v___x_3079_ = lean_uint16_of_nat(v___x_3066_);
lean_dec(v___x_3066_);
v___x_3080_ = l_Std_Http_Status_ofCode(v___x_3078_, v___x_3079_);
if (lean_obj_tag(v___x_3080_) == 1)
{
lean_object* v_val_3081_; lean_object* v___x_3083_; 
v_val_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_val_3081_);
lean_dec_ref_known(v___x_3080_, 1);
if (v_isShared_3075_ == 0)
{
lean_ctor_set(v___x_3074_, 1, v_val_3081_);
v___x_3083_ = v___x_3074_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_pos_3072_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v_val_3081_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
else
{
lean_dec(v___x_3080_);
lean_del_object(v___x_3074_);
v___y_3008_ = v_pos_3072_;
goto v___jp_3007_;
}
}
}
}
else
{
lean_object* v_pos_3087_; lean_object* v_err_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
lean_dec_ref(v___y_3069_);
lean_dec(v___x_3066_);
v_pos_3087_ = lean_ctor_get(v___x_3071_, 0);
v_err_3088_ = lean_ctor_get(v___x_3071_, 1);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_3071_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_err_3088_);
lean_inc(v_pos_3087_);
lean_dec(v___x_3071_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_pos_3087_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v_err_3088_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
v___jp_3096_:
{
uint8_t v___x_3100_; 
v___x_3100_ = lean_nat_dec_eq(v___x_3052_, v_idx_3098_);
lean_dec(v_idx_3098_);
lean_dec(v___x_3052_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; 
lean_dec(v___x_3066_);
lean_inc(v_err_3099_);
v___x_3101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3101_, 0, v_pos_3097_);
lean_ctor_set(v___x_3101_, 1, v_err_3099_);
return v___x_3101_;
}
else
{
lean_object* v___x_3102_; 
v___x_3102_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0));
v___y_3068_ = v_pos_3097_;
v___y_3069_ = v___x_3102_;
goto v___jp_3067_;
}
}
}
}
}
v___jp_3040_:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3041_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3042_, 0, v_it_x27_3039_);
lean_ctor_set(v___x_3042_, 1, v___x_3041_);
return v___x_3042_;
}
}
}
}
v___jp_3029_:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3030_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3031_, 0, v_it_x27_3028_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
return v___x_3031_;
}
}
}
}
}
}
v___jp_3004_:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3005_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3006_, 0, v_a_3003_);
lean_ctor_set(v___x_3006_, 1, v___x_3005_);
return v___x_3006_;
}
v___jp_3007_:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3009_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__1));
v___x_3010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3010_, 0, v___y_3008_);
lean_ctor_set(v___x_3010_, 1, v___x_3009_);
return v___x_3010_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___boxed(lean_object* v_limits_3121_, lean_object* v_a_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_3121_, v_a_3122_);
lean_dec_ref(v_limits_3121_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine(lean_object* v_limits_3124_, lean_object* v_a_3125_){
_start:
{
lean_object* v___x_3126_; 
v___x_3126_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_3125_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_pos_3127_; lean_object* v_res_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3202_; 
v_pos_3127_ = lean_ctor_get(v___x_3126_, 0);
v_res_3128_ = lean_ctor_get(v___x_3126_, 1);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3130_ = v___x_3126_;
v_isShared_3131_ = v_isSharedCheck_3202_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_res_3128_);
lean_inc(v_pos_3127_);
lean_dec(v___x_3126_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3202_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v_array_3132_; lean_object* v_idx_3133_; lean_object* v___x_3134_; uint8_t v___x_3135_; 
v_array_3132_ = lean_ctor_get(v_pos_3127_, 0);
v_idx_3133_ = lean_ctor_get(v_pos_3127_, 1);
v___x_3134_ = lean_byte_array_size(v_array_3132_);
v___x_3135_ = lean_nat_dec_lt(v_idx_3133_, v___x_3134_);
if (v___x_3135_ == 0)
{
lean_object* v___x_3136_; lean_object* v___x_3138_; 
lean_dec(v_res_3128_);
v___x_3136_ = lean_box(0);
if (v_isShared_3131_ == 0)
{
lean_ctor_set_tag(v___x_3130_, 1);
lean_ctor_set(v___x_3130_, 1, v___x_3136_);
v___x_3138_ = v___x_3130_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_pos_3127_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v___x_3136_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
else
{
uint8_t v___x_3140_; uint8_t v_got_3141_; uint8_t v___x_3142_; 
v___x_3140_ = 32;
v_got_3141_ = lean_byte_array_fget(v_array_3132_, v_idx_3133_);
v___x_3142_ = lean_uint8_dec_eq(v_got_3141_, v___x_3140_);
if (v___x_3142_ == 0)
{
lean_object* v___x_3143_; lean_object* v___x_3145_; 
lean_dec(v_res_3128_);
v___x_3143_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_3131_ == 0)
{
lean_ctor_set_tag(v___x_3130_, 1);
lean_ctor_set(v___x_3130_, 1, v___x_3143_);
v___x_3145_ = v___x_3130_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_pos_3127_);
lean_ctor_set(v_reuseFailAlloc_3146_, 1, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
else
{
lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3199_; 
lean_inc(v_idx_3133_);
lean_inc_ref(v_array_3132_);
v_isSharedCheck_3199_ = !lean_is_exclusive(v_pos_3127_);
if (v_isSharedCheck_3199_ == 0)
{
lean_object* v_unused_3200_; lean_object* v_unused_3201_; 
v_unused_3200_ = lean_ctor_get(v_pos_3127_, 1);
lean_dec(v_unused_3200_);
v_unused_3201_ = lean_ctor_get(v_pos_3127_, 0);
lean_dec(v_unused_3201_);
v___x_3148_ = v_pos_3127_;
v_isShared_3149_ = v_isSharedCheck_3199_;
goto v_resetjp_3147_;
}
else
{
lean_dec(v_pos_3127_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3199_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v_fst_3150_; lean_object* v_snd_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3198_; 
v_fst_3150_ = lean_ctor_get(v_res_3128_, 0);
v_snd_3151_ = lean_ctor_get(v_res_3128_, 1);
v_isSharedCheck_3198_ = !lean_is_exclusive(v_res_3128_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3153_ = v_res_3128_;
v_isShared_3154_ = v_isSharedCheck_3198_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_snd_3151_);
lean_inc(v_fst_3150_);
lean_dec(v_res_3128_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3198_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3158_; 
v___x_3155_ = lean_unsigned_to_nat(1u);
v___x_3156_ = lean_nat_add(v_idx_3133_, v___x_3155_);
lean_dec(v_idx_3133_);
if (v_isShared_3149_ == 0)
{
lean_ctor_set(v___x_3148_, 1, v___x_3156_);
v___x_3158_ = v___x_3148_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_array_3132_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v___x_3156_);
v___x_3158_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
lean_object* v___x_3159_; 
v___x_3159_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_3124_, v___x_3158_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_pos_3160_; lean_object* v_res_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3187_; 
v_pos_3160_ = lean_ctor_get(v___x_3159_, 0);
v_res_3161_ = lean_ctor_get(v___x_3159_, 1);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3163_ = v___x_3159_;
v_isShared_3164_ = v_isSharedCheck_3187_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_res_3161_);
lean_inc(v_pos_3160_);
lean_dec(v___x_3159_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3187_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
uint8_t v___x_3170_; 
v___x_3170_ = lean_nat_dec_eq(v_fst_3150_, v___x_3155_);
lean_dec(v_fst_3150_);
if (v___x_3170_ == 0)
{
lean_del_object(v___x_3153_);
goto v___jp_3171_;
}
else
{
uint8_t v___x_3180_; 
v___x_3180_ = lean_nat_dec_le(v___x_3155_, v_snd_3151_);
if (v___x_3180_ == 0)
{
lean_del_object(v___x_3153_);
goto v___jp_3171_;
}
else
{
uint8_t v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3185_; 
lean_del_object(v___x_3163_);
lean_dec(v_snd_3151_);
lean_del_object(v___x_3130_);
v___x_3181_ = 1;
v___x_3182_ = l_Std_Http_Headers_empty;
v___x_3183_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3183_, 0, v_res_3161_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
lean_ctor_set_uint8(v___x_3183_, sizeof(void*)*2, v___x_3181_);
if (v_isShared_3154_ == 0)
{
lean_ctor_set(v___x_3153_, 1, v___x_3183_);
lean_ctor_set(v___x_3153_, 0, v_pos_3160_);
v___x_3185_ = v___x_3153_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_pos_3160_);
lean_ctor_set(v_reuseFailAlloc_3186_, 1, v___x_3183_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
v___jp_3165_:
{
lean_object* v___x_3166_; lean_object* v___x_3168_; 
v___x_3166_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
if (v_isShared_3164_ == 0)
{
lean_ctor_set_tag(v___x_3163_, 1);
lean_ctor_set(v___x_3163_, 1, v___x_3166_);
v___x_3168_ = v___x_3163_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_pos_3160_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
v___jp_3171_:
{
if (v___x_3170_ == 0)
{
lean_dec(v_res_3161_);
lean_dec(v_snd_3151_);
lean_del_object(v___x_3130_);
goto v___jp_3165_;
}
else
{
lean_object* v___x_3172_; uint8_t v___x_3173_; 
v___x_3172_ = lean_unsigned_to_nat(0u);
v___x_3173_ = lean_nat_dec_eq(v_snd_3151_, v___x_3172_);
lean_dec(v_snd_3151_);
if (v___x_3173_ == 0)
{
lean_dec(v_res_3161_);
lean_del_object(v___x_3130_);
goto v___jp_3165_;
}
else
{
uint8_t v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3178_; 
lean_del_object(v___x_3163_);
v___x_3174_ = 0;
v___x_3175_ = l_Std_Http_Headers_empty;
v___x_3176_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3176_, 0, v_res_3161_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
lean_ctor_set_uint8(v___x_3176_, sizeof(void*)*2, v___x_3174_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 1, v___x_3176_);
lean_ctor_set(v___x_3130_, 0, v_pos_3160_);
v___x_3178_ = v___x_3130_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_pos_3160_);
lean_ctor_set(v_reuseFailAlloc_3179_, 1, v___x_3176_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
}
}
else
{
lean_object* v_pos_3188_; lean_object* v_err_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_fst_3150_);
lean_del_object(v___x_3130_);
v_pos_3188_ = lean_ctor_get(v___x_3159_, 0);
v_err_3189_ = lean_ctor_get(v___x_3159_, 1);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3159_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_err_3189_);
lean_inc(v_pos_3188_);
lean_dec(v___x_3159_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_pos_3188_);
lean_ctor_set(v_reuseFailAlloc_3195_, 1, v_err_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
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
lean_object* v_pos_3203_; lean_object* v_err_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3211_; 
v_pos_3203_ = lean_ctor_get(v___x_3126_, 0);
v_err_3204_ = lean_ctor_get(v___x_3126_, 1);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___x_3126_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_err_3204_);
lean_inc(v_pos_3203_);
lean_dec(v___x_3126_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3209_; 
if (v_isShared_3207_ == 0)
{
v___x_3209_ = v___x_3206_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_pos_3203_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v_err_3204_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine___boxed(lean_object* v_limits_3212_, lean_object* v_a_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l_Std_Http_Protocol_H1_parseStatusLine(v_limits_3212_, v_a_3213_);
lean_dec_ref(v_limits_3212_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion(lean_object* v_limits_3215_, lean_object* v_a_3216_){
_start:
{
lean_object* v___x_3217_; 
v___x_3217_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_3216_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_pos_3218_; lean_object* v_res_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3282_; 
v_pos_3218_ = lean_ctor_get(v___x_3217_, 0);
v_res_3219_ = lean_ctor_get(v___x_3217_, 1);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3221_ = v___x_3217_;
v_isShared_3222_ = v_isSharedCheck_3282_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_res_3219_);
lean_inc(v_pos_3218_);
lean_dec(v___x_3217_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3282_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v_array_3223_; lean_object* v_idx_3224_; lean_object* v___x_3225_; uint8_t v___x_3226_; 
v_array_3223_ = lean_ctor_get(v_pos_3218_, 0);
v_idx_3224_ = lean_ctor_get(v_pos_3218_, 1);
v___x_3225_ = lean_byte_array_size(v_array_3223_);
v___x_3226_ = lean_nat_dec_lt(v_idx_3224_, v___x_3225_);
if (v___x_3226_ == 0)
{
lean_object* v___x_3227_; lean_object* v___x_3229_; 
lean_dec(v_res_3219_);
v___x_3227_ = lean_box(0);
if (v_isShared_3222_ == 0)
{
lean_ctor_set_tag(v___x_3221_, 1);
lean_ctor_set(v___x_3221_, 1, v___x_3227_);
v___x_3229_ = v___x_3221_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_pos_3218_);
lean_ctor_set(v_reuseFailAlloc_3230_, 1, v___x_3227_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
else
{
uint8_t v___x_3231_; uint8_t v_got_3232_; uint8_t v___x_3233_; 
v___x_3231_ = 32;
v_got_3232_ = lean_byte_array_fget(v_array_3223_, v_idx_3224_);
v___x_3233_ = lean_uint8_dec_eq(v_got_3232_, v___x_3231_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3234_; lean_object* v___x_3236_; 
lean_dec(v_res_3219_);
v___x_3234_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_3222_ == 0)
{
lean_ctor_set_tag(v___x_3221_, 1);
lean_ctor_set(v___x_3221_, 1, v___x_3234_);
v___x_3236_ = v___x_3221_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_pos_3218_);
lean_ctor_set(v_reuseFailAlloc_3237_, 1, v___x_3234_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
else
{
lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3279_; 
lean_inc(v_idx_3224_);
lean_inc_ref(v_array_3223_);
lean_del_object(v___x_3221_);
v_isSharedCheck_3279_ = !lean_is_exclusive(v_pos_3218_);
if (v_isSharedCheck_3279_ == 0)
{
lean_object* v_unused_3280_; lean_object* v_unused_3281_; 
v_unused_3280_ = lean_ctor_get(v_pos_3218_, 1);
lean_dec(v_unused_3280_);
v_unused_3281_ = lean_ctor_get(v_pos_3218_, 0);
lean_dec(v_unused_3281_);
v___x_3239_ = v_pos_3218_;
v_isShared_3240_ = v_isSharedCheck_3279_;
goto v_resetjp_3238_;
}
else
{
lean_dec(v_pos_3218_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3279_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v_fst_3241_; lean_object* v_snd_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3278_; 
v_fst_3241_ = lean_ctor_get(v_res_3219_, 0);
v_snd_3242_ = lean_ctor_get(v_res_3219_, 1);
v_isSharedCheck_3278_ = !lean_is_exclusive(v_res_3219_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3244_ = v_res_3219_;
v_isShared_3245_ = v_isSharedCheck_3278_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_snd_3242_);
lean_inc(v_fst_3241_);
lean_dec(v_res_3219_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3278_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3249_; 
v___x_3246_ = lean_unsigned_to_nat(1u);
v___x_3247_ = lean_nat_add(v_idx_3224_, v___x_3246_);
lean_dec(v_idx_3224_);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 1, v___x_3247_);
v___x_3249_ = v___x_3239_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_array_3223_);
lean_ctor_set(v_reuseFailAlloc_3277_, 1, v___x_3247_);
v___x_3249_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
lean_object* v___x_3250_; 
v___x_3250_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_3215_, v___x_3249_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_pos_3251_; lean_object* v_res_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3267_; 
v_pos_3251_ = lean_ctor_get(v___x_3250_, 0);
v_res_3252_ = lean_ctor_get(v___x_3250_, 1);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3254_ = v___x_3250_;
v_isShared_3255_ = v_isSharedCheck_3267_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_res_3252_);
lean_inc(v_pos_3251_);
lean_dec(v___x_3250_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3267_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___y_3257_; uint8_t v___x_3265_; 
v___x_3265_ = lean_nat_dec_eq(v_fst_3241_, v___x_3246_);
if (v___x_3265_ == 0)
{
v___y_3257_ = v_snd_3242_;
goto v___jp_3256_;
}
else
{
uint8_t v___x_3266_; 
v___x_3266_ = lean_nat_dec_le(v_snd_3242_, v___x_3246_);
if (v___x_3266_ == 0)
{
lean_dec(v_snd_3242_);
v___y_3257_ = v___x_3246_;
goto v___jp_3256_;
}
else
{
v___y_3257_ = v_snd_3242_;
goto v___jp_3256_;
}
}
v___jp_3256_:
{
lean_object* v___x_3258_; lean_object* v___x_3260_; 
v___x_3258_ = l_Std_Http_Version_ofNumber_x3f(v_fst_3241_, v___y_3257_);
lean_dec(v___y_3257_);
lean_dec(v_fst_3241_);
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 1, v___x_3258_);
lean_ctor_set(v___x_3244_, 0, v_res_3252_);
v___x_3260_ = v___x_3244_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_res_3252_);
lean_ctor_set(v_reuseFailAlloc_3264_, 1, v___x_3258_);
v___x_3260_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
lean_object* v___x_3262_; 
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 1, v___x_3260_);
v___x_3262_ = v___x_3254_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_pos_3251_);
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
}
else
{
lean_object* v_pos_3268_; lean_object* v_err_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3276_; 
lean_del_object(v___x_3244_);
lean_dec(v_snd_3242_);
lean_dec(v_fst_3241_);
v_pos_3268_ = lean_ctor_get(v___x_3250_, 0);
v_err_3269_ = lean_ctor_get(v___x_3250_, 1);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3271_ = v___x_3250_;
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_err_3269_);
lean_inc(v_pos_3268_);
lean_dec(v___x_3250_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3274_; 
if (v_isShared_3272_ == 0)
{
v___x_3274_ = v___x_3271_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_pos_3268_);
lean_ctor_set(v_reuseFailAlloc_3275_, 1, v_err_3269_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
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
lean_object* v_pos_3283_; lean_object* v_err_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
v_pos_3283_ = lean_ctor_get(v___x_3217_, 0);
v_err_3284_ = lean_ctor_get(v___x_3217_, 1);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3217_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_err_3284_);
lean_inc(v_pos_3283_);
lean_dec(v___x_3217_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_pos_3283_);
lean_ctor_set(v_reuseFailAlloc_3290_, 1, v_err_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion___boxed(lean_object* v_limits_3292_, lean_object* v_a_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l_Std_Http_Protocol_H1_parseStatusLineRawVersion(v_limits_3292_, v_a_3293_);
lean_dec_ref(v_limits_3292_);
return v_res_3294_;
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
