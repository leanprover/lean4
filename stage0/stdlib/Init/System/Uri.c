// Lean compiler output
// Module: Init.System.Uri
// Imports: public import Init.System.FilePath import Init.Data.String.TakeDrop import Init.Data.String.Modify import Init.Data.String.Search import Init.Omega import Init.System.Platform import Init.While import Init.Data.String.Length import Init.Data.Iterators.Combinators.Take
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_String_Slice_positions(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
extern lean_object* l_ByteArray_empty;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
uint8_t lean_uint8_add(uint8_t, uint8_t);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint8_t lean_uint8_shift_left(uint8_t, uint8_t);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
extern uint8_t l_System_Platform_isWindows;
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_byte_array_uget(lean_object*, size_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_uint8_shift_right(uint8_t, uint8_t);
uint8_t lean_uint8_mod(uint8_t, uint8_t);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l_hexDigitRepr(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
lean_object* l_System_FilePath_normalize(lean_object*);
LEAN_EXPORT uint8_t l_System_Uri_UriEscape_zero;
LEAN_EXPORT uint8_t l_System_Uri_UriEscape_nine;
LEAN_EXPORT uint8_t l_System_Uri_UriEscape_lettera;
LEAN_EXPORT uint8_t l_System_Uri_UriEscape_letterf;
LEAN_EXPORT uint8_t l_System_Uri_UriEscape_letterA;
LEAN_EXPORT uint8_t l_System_Uri_UriEscape_letterF;
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f___boxed(lean_object*);
static const lean_string_object l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0 = (const lean_object*)&l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_System_Uri_UriEscape_decodeUri___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Uri_UriEscape_decodeUri___closed__0;
static const lean_string_object l_System_Uri_UriEscape_decodeUri___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Init.Data.String.Basic"};
static const lean_object* l_System_Uri_UriEscape_decodeUri___closed__1 = (const lean_object*)&l_System_Uri_UriEscape_decodeUri___closed__1_value;
static const lean_string_object l_System_Uri_UriEscape_decodeUri___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "String.fromUTF8!"};
static const lean_object* l_System_Uri_UriEscape_decodeUri___closed__2 = (const lean_object*)&l_System_Uri_UriEscape_decodeUri___closed__2_value;
static const lean_string_object l_System_Uri_UriEscape_decodeUri___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid UTF-8 string"};
static const lean_object* l_System_Uri_UriEscape_decodeUri___closed__3 = (const lean_object*)&l_System_Uri_UriEscape_decodeUri___closed__3_value;
static lean_once_cell_t l_System_Uri_UriEscape_decodeUri___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Uri_UriEscape_decodeUri___closed__4;
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_decodeUri(lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_decodeUri___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0___boxed__const__1;
static lean_once_cell_t l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0;
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1___boxed__const__1;
static lean_once_cell_t l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1;
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2___boxed__const__1;
static lean_once_cell_t l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2;
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3___boxed__const__1;
static lean_once_cell_t l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3;
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4___boxed__const__1;
static lean_once_cell_t l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4;
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5___boxed__const__1;
static lean_once_cell_t l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5;
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6___boxed__const__1;
static lean_once_cell_t l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6;
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7___boxed__const__1;
static lean_once_cell_t l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7;
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8___boxed__const__1;
static lean_once_cell_t l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8;
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9___boxed__const__1;
static lean_once_cell_t l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9;
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10___boxed__const__1;
static lean_once_cell_t l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10;
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11___boxed__const__1;
static lean_once_cell_t l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11;
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12___boxed__const__1;
static lean_once_cell_t l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12;
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13___boxed__const__1;
static lean_once_cell_t l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13;
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14___boxed__const__1;
static lean_once_cell_t l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14;
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15___boxed__const__1;
static lean_once_cell_t l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15;
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16___boxed__const__1;
static lean_once_cell_t l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16;
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17___boxed__const__1;
static lean_once_cell_t l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17;
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18___boxed__const__1;
static lean_once_cell_t l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18;
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars;
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex___boxed(lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "%"};
static const lean_object* l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___closed__0 = (const lean_object*)&l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_uriEscapeAsciiChar(uint32_t);
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_uriEscapeAsciiChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_escapeUri(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_unescapeUri(lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_unescapeUri___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__0 = (const lean_object*)&l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_Uri_pathToUri_spec__0(lean_object*, lean_object*);
static const lean_string_object l_System_Uri_pathToUri___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "file:///"};
static const lean_object* l_System_Uri_pathToUri___closed__0 = (const lean_object*)&l_System_Uri_pathToUri___closed__0_value;
static const lean_string_object l_System_Uri_pathToUri___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_System_Uri_pathToUri___closed__1 = (const lean_object*)&l_System_Uri_pathToUri___closed__1_value;
static lean_once_cell_t l_System_Uri_pathToUri___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Uri_pathToUri___closed__2;
static const lean_string_object l_System_Uri_pathToUri___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "file://"};
static const lean_object* l_System_Uri_pathToUri___closed__3 = (const lean_object*)&l_System_Uri_pathToUri___closed__3_value;
LEAN_EXPORT lean_object* l_System_Uri_pathToUri(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_Uri_fileUriToPath_x3f_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_fileUriToPath_x3f(lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_fileUriToPath_x3f___boxed(lean_object*);
static uint8_t _init_l_System_Uri_UriEscape_zero(void){
_start:
{
uint8_t v___x_1_; 
v___x_1_ = 48;
return v___x_1_;
}
}
static uint8_t _init_l_System_Uri_UriEscape_nine(void){
_start:
{
uint8_t v___x_2_; 
v___x_2_ = 57;
return v___x_2_;
}
}
static uint8_t _init_l_System_Uri_UriEscape_lettera(void){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = 97;
return v___x_3_;
}
}
static uint8_t _init_l_System_Uri_UriEscape_letterf(void){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = 102;
return v___x_4_;
}
}
static uint8_t _init_l_System_Uri_UriEscape_letterA(void){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = 65;
return v___x_5_;
}
}
static uint8_t _init_l_System_Uri_UriEscape_letterF(void){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = 70;
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(uint8_t v_c_7_){
_start:
{
uint8_t v___y_9_; uint8_t v___y_10_; uint8_t v___y_18_; uint8_t v___y_19_; uint8_t v___x_29_; uint8_t v___y_31_; uint8_t v___x_39_; 
v___x_29_ = 48;
v___x_39_ = lean_uint8_dec_le(v___x_29_, v_c_7_);
if (v___x_39_ == 0)
{
v___y_31_ = v___x_39_;
goto v___jp_30_;
}
else
{
uint8_t v___x_40_; uint8_t v___x_41_; 
v___x_40_ = 57;
v___x_41_ = lean_uint8_dec_le(v_c_7_, v___x_40_);
v___y_31_ = v___x_41_;
goto v___jp_30_;
}
v___jp_8_:
{
if (v___y_10_ == 0)
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
else
{
uint8_t v___x_12_; uint8_t v___x_13_; uint8_t v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_12_ = lean_uint8_sub(v_c_7_, v___y_9_);
v___x_13_ = 10;
v___x_14_ = lean_uint8_add(v___x_12_, v___x_13_);
v___x_15_ = lean_box(v___x_14_);
v___x_16_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
v___jp_17_:
{
if (v___y_19_ == 0)
{
uint8_t v___x_20_; uint8_t v___x_21_; 
v___x_20_ = 65;
v___x_21_ = lean_uint8_dec_le(v___x_20_, v_c_7_);
if (v___x_21_ == 0)
{
v___y_9_ = v___x_20_;
v___y_10_ = v___x_21_;
goto v___jp_8_;
}
else
{
uint8_t v___x_22_; uint8_t v___x_23_; 
v___x_22_ = 70;
v___x_23_ = lean_uint8_dec_le(v_c_7_, v___x_22_);
v___y_9_ = v___x_20_;
v___y_10_ = v___x_23_;
goto v___jp_8_;
}
}
else
{
uint8_t v___x_24_; uint8_t v___x_25_; uint8_t v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_24_ = lean_uint8_sub(v_c_7_, v___y_18_);
v___x_25_ = 10;
v___x_26_ = lean_uint8_add(v___x_24_, v___x_25_);
v___x_27_ = lean_box(v___x_26_);
v___x_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
return v___x_28_;
}
}
v___jp_30_:
{
if (v___y_31_ == 0)
{
uint8_t v___x_32_; uint8_t v___x_33_; 
v___x_32_ = 97;
v___x_33_ = lean_uint8_dec_le(v___x_32_, v_c_7_);
if (v___x_33_ == 0)
{
v___y_18_ = v___x_32_;
v___y_19_ = v___x_33_;
goto v___jp_17_;
}
else
{
uint8_t v___x_34_; uint8_t v___x_35_; 
v___x_34_ = 102;
v___x_35_ = lean_uint8_dec_le(v_c_7_, v___x_34_);
v___y_18_ = v___x_32_;
v___y_19_ = v___x_35_;
goto v___jp_17_;
}
}
else
{
uint8_t v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = lean_uint8_sub(v_c_7_, v___x_29_);
v___x_37_ = lean_box(v___x_36_);
v___x_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
return v___x_38_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f___boxed(lean_object* v_c_42_){
_start:
{
uint8_t v_c_boxed_43_; lean_object* v_res_44_; 
v_c_boxed_43_ = lean_unbox(v_c_42_);
v_res_44_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(v_c_boxed_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1(lean_object* v_msg_46_){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = ((lean_object*)(l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0));
v___x_48_ = lean_panic_fn_borrowed(v___x_47_, v_msg_46_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___redArg(lean_object* v_len_49_, lean_object* v_rawBytes_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_fst_52_; lean_object* v_snd_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_118_; 
v_fst_52_ = lean_ctor_get(v_a_51_, 0);
v_snd_53_ = lean_ctor_get(v_a_51_, 1);
v_isSharedCheck_118_ = !lean_is_exclusive(v_a_51_);
if (v_isSharedCheck_118_ == 0)
{
v___x_55_ = v_a_51_;
v_isShared_56_ = v_isSharedCheck_118_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_snd_53_);
lean_inc(v_fst_52_);
lean_dec(v_a_51_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_118_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
uint8_t v___x_57_; 
v___x_57_ = lean_nat_dec_lt(v_snd_53_, v_len_49_);
if (v___x_57_ == 0)
{
lean_object* v___x_59_; 
if (v_isShared_56_ == 0)
{
v___x_59_ = v___x_55_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_fst_52_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v_snd_53_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
else
{
uint8_t v_percent_61_; uint8_t v___x_62_; uint8_t v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; uint8_t v___y_67_; 
v_percent_61_ = 37;
v___x_62_ = lean_byte_array_fget(v_rawBytes_50_, v_snd_53_);
v___x_63_ = lean_uint8_dec_eq(v___x_62_, v_percent_61_);
v___x_64_ = lean_unsigned_to_nat(1u);
v___x_65_ = lean_nat_add(v_snd_53_, v___x_64_);
if (v___x_63_ == 0)
{
v___y_67_ = v___x_63_;
goto v___jp_66_;
}
else
{
uint8_t v___x_117_; 
v___x_117_ = lean_nat_dec_lt(v___x_65_, v_len_49_);
v___y_67_ = v___x_117_;
goto v___jp_66_;
}
v___jp_66_:
{
if (v___y_67_ == 0)
{
lean_object* v___x_68_; lean_object* v___x_70_; 
lean_dec(v_snd_53_);
v___x_68_ = lean_byte_array_push(v_fst_52_, v___x_62_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v___x_65_);
lean_ctor_set(v___x_55_, 0, v___x_68_);
v___x_70_ = v___x_55_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_68_);
lean_ctor_set(v_reuseFailAlloc_72_, 1, v___x_65_);
v___x_70_ = v_reuseFailAlloc_72_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
v_a_51_ = v___x_70_;
goto _start;
}
}
else
{
uint8_t v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_byte_array_fget(v_rawBytes_50_, v___x_65_);
lean_dec(v___x_65_);
v___x_74_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(v___x_73_);
if (lean_obj_tag(v___x_74_) == 1)
{
lean_object* v_val_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v_val_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_val_75_);
lean_dec_ref_known(v___x_74_, 1);
v___x_76_ = lean_unsigned_to_nat(2u);
v___x_77_ = lean_nat_add(v_snd_53_, v___x_76_);
v___x_78_ = lean_nat_dec_lt(v___x_77_, v_len_49_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_82_; 
lean_dec(v_val_75_);
lean_dec(v_snd_53_);
v___x_79_ = lean_byte_array_push(v_fst_52_, v___x_62_);
v___x_80_ = lean_byte_array_push(v___x_79_, v___x_73_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v___x_77_);
lean_ctor_set(v___x_55_, 0, v___x_80_);
v___x_82_ = v___x_55_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_80_);
lean_ctor_set(v_reuseFailAlloc_84_, 1, v___x_77_);
v___x_82_ = v_reuseFailAlloc_84_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
v_a_51_ = v___x_82_;
goto _start;
}
}
else
{
uint8_t v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_byte_array_fget(v_rawBytes_50_, v___x_77_);
lean_dec(v___x_77_);
v___x_86_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(v___x_85_);
if (lean_obj_tag(v___x_86_) == 1)
{
lean_object* v_val_87_; uint8_t v___x_88_; uint8_t v___x_89_; uint8_t v___x_90_; uint8_t v___x_91_; uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_97_; 
v_val_87_ = lean_ctor_get(v___x_86_, 0);
lean_inc(v_val_87_);
lean_dec_ref_known(v___x_86_, 1);
v___x_88_ = 4;
v___x_89_ = lean_unbox(v_val_75_);
lean_dec(v_val_75_);
v___x_90_ = lean_uint8_shift_left(v___x_89_, v___x_88_);
v___x_91_ = lean_unbox(v_val_87_);
lean_dec(v_val_87_);
v___x_92_ = lean_uint8_add(v___x_90_, v___x_91_);
v___x_93_ = lean_byte_array_push(v_fst_52_, v___x_92_);
v___x_94_ = lean_unsigned_to_nat(3u);
v___x_95_ = lean_nat_add(v_snd_53_, v___x_94_);
lean_dec(v_snd_53_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v___x_95_);
lean_ctor_set(v___x_55_, 0, v___x_93_);
v___x_97_ = v___x_55_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_93_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v___x_95_);
v___x_97_ = v_reuseFailAlloc_99_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
v_a_51_ = v___x_97_;
goto _start;
}
}
else
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
lean_dec(v___x_86_);
lean_dec(v_val_75_);
v___x_100_ = lean_byte_array_push(v_fst_52_, v___x_62_);
v___x_101_ = lean_byte_array_push(v___x_100_, v___x_73_);
v___x_102_ = lean_byte_array_push(v___x_101_, v___x_85_);
v___x_103_ = lean_unsigned_to_nat(3u);
v___x_104_ = lean_nat_add(v_snd_53_, v___x_103_);
lean_dec(v_snd_53_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v___x_104_);
lean_ctor_set(v___x_55_, 0, v___x_102_);
v___x_106_ = v___x_55_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_102_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v___x_104_);
v___x_106_ = v_reuseFailAlloc_108_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
v_a_51_ = v___x_106_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_114_; 
lean_dec(v___x_74_);
v___x_109_ = lean_byte_array_push(v_fst_52_, v___x_62_);
v___x_110_ = lean_byte_array_push(v___x_109_, v___x_73_);
v___x_111_ = lean_unsigned_to_nat(2u);
v___x_112_ = lean_nat_add(v_snd_53_, v___x_111_);
lean_dec(v_snd_53_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v___x_112_);
lean_ctor_set(v___x_55_, 0, v___x_110_);
v___x_114_ = v___x_55_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_110_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v___x_112_);
v___x_114_ = v_reuseFailAlloc_116_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
v_a_51_ = v___x_114_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___redArg___boxed(lean_object* v_len_119_, lean_object* v_rawBytes_120_, lean_object* v_a_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___redArg(v_len_119_, v_rawBytes_120_, v_a_121_);
lean_dec_ref(v_rawBytes_120_);
lean_dec(v_len_119_);
return v_res_122_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_decodeUri___closed__0(void){
_start:
{
lean_object* v_i_123_; lean_object* v_decoded_124_; lean_object* v___x_125_; 
v_i_123_ = lean_unsigned_to_nat(0u);
v_decoded_124_ = l_ByteArray_empty;
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v_decoded_124_);
lean_ctor_set(v___x_125_, 1, v_i_123_);
return v___x_125_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_decodeUri___closed__4(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_129_ = ((lean_object*)(l_System_Uri_UriEscape_decodeUri___closed__3));
v___x_130_ = lean_unsigned_to_nat(46u);
v___x_131_ = lean_unsigned_to_nat(193u);
v___x_132_ = ((lean_object*)(l_System_Uri_UriEscape_decodeUri___closed__2));
v___x_133_ = ((lean_object*)(l_System_Uri_UriEscape_decodeUri___closed__1));
v___x_134_ = l_mkPanicMessageWithDecl(v___x_133_, v___x_132_, v___x_131_, v___x_130_, v___x_129_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_decodeUri(lean_object* v_uri_135_){
_start:
{
lean_object* v_rawBytes_136_; lean_object* v_len_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v_fst_140_; uint8_t v___x_141_; 
v_rawBytes_136_ = lean_string_to_utf8(v_uri_135_);
v_len_137_ = lean_byte_array_size(v_rawBytes_136_);
v___x_138_ = lean_obj_once(&l_System_Uri_UriEscape_decodeUri___closed__0, &l_System_Uri_UriEscape_decodeUri___closed__0_once, _init_l_System_Uri_UriEscape_decodeUri___closed__0);
v___x_139_ = l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___redArg(v_len_137_, v_rawBytes_136_, v___x_138_);
lean_dec_ref(v_rawBytes_136_);
v_fst_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_fst_140_);
lean_dec_ref(v___x_139_);
v___x_141_ = lean_string_validate_utf8(v_fst_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec(v_fst_140_);
v___x_142_ = lean_obj_once(&l_System_Uri_UriEscape_decodeUri___closed__4, &l_System_Uri_UriEscape_decodeUri___closed__4_once, _init_l_System_Uri_UriEscape_decodeUri___closed__4);
v___x_143_ = l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1(v___x_142_);
return v___x_143_;
}
else
{
lean_object* v___x_144_; 
v___x_144_ = lean_string_from_utf8_unchecked(v_fst_140_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_decodeUri___boxed(lean_object* v_uri_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_System_Uri_UriEscape_decodeUri(v_uri_145_);
lean_dec_ref(v_uri_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0(lean_object* v_len_147_, lean_object* v_rawBytes_148_, lean_object* v_inst_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___redArg(v_len_147_, v_rawBytes_148_, v_a_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___boxed(lean_object* v_len_152_, lean_object* v_rawBytes_153_, lean_object* v_inst_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0(v_len_152_, v_rawBytes_153_, v_inst_154_, v_a_155_);
lean_dec_ref(v_rawBytes_153_);
lean_dec(v_len_152_);
return v_res_156_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_157_; lean_object* v___x_158_; 
v___x_157_ = 32;
v___x_158_ = lean_box_uint32(v___x_157_);
return v___x_158_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = lean_box(0);
v___x_160_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0___boxed__const__1;
v___x_161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v___x_159_);
return v___x_161_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_162_; lean_object* v___x_163_; 
v___x_162_ = 37;
v___x_163_ = lean_box_uint32(v___x_162_);
return v___x_163_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0);
v___x_165_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1___boxed__const__1;
v___x_166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_164_);
return v___x_166_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_167_; lean_object* v___x_168_; 
v___x_167_ = 42;
v___x_168_ = lean_box_uint32(v___x_167_);
return v___x_168_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1);
v___x_170_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2___boxed__const__1;
v___x_171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
return v___x_171_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_172_; lean_object* v___x_173_; 
v___x_172_ = 41;
v___x_173_ = lean_box_uint32(v___x_172_);
return v___x_173_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2);
v___x_175_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3___boxed__const__1;
v___x_176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v___x_174_);
return v___x_176_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4___boxed__const__1(void){
_start:
{
uint32_t v___x_177_; lean_object* v___x_178_; 
v___x_177_ = 40;
v___x_178_ = lean_box_uint32(v___x_177_);
return v___x_178_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3);
v___x_180_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4___boxed__const__1;
v___x_181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___x_179_);
return v___x_181_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5___boxed__const__1(void){
_start:
{
uint32_t v___x_182_; lean_object* v___x_183_; 
v___x_182_ = 39;
v___x_183_ = lean_box_uint32(v___x_182_);
return v___x_183_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4);
v___x_185_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5___boxed__const__1;
v___x_186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v___x_184_);
return v___x_186_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6___boxed__const__1(void){
_start:
{
uint32_t v___x_187_; lean_object* v___x_188_; 
v___x_187_ = 33;
v___x_188_ = lean_box_uint32(v___x_187_);
return v___x_188_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5);
v___x_190_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6___boxed__const__1;
v___x_191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v___x_189_);
return v___x_191_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7___boxed__const__1(void){
_start:
{
uint32_t v___x_192_; lean_object* v___x_193_; 
v___x_192_ = 44;
v___x_193_ = lean_box_uint32(v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6);
v___x_195_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7___boxed__const__1;
v___x_196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___x_194_);
return v___x_196_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8___boxed__const__1(void){
_start:
{
uint32_t v___x_197_; lean_object* v___x_198_; 
v___x_197_ = 36;
v___x_198_ = lean_box_uint32(v___x_197_);
return v___x_198_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7);
v___x_200_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8___boxed__const__1;
v___x_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v___x_199_);
return v___x_201_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9___boxed__const__1(void){
_start:
{
uint32_t v___x_202_; lean_object* v___x_203_; 
v___x_202_ = 43;
v___x_203_ = lean_box_uint32(v___x_202_);
return v___x_203_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8);
v___x_205_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9___boxed__const__1;
v___x_206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___x_204_);
return v___x_206_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10___boxed__const__1(void){
_start:
{
uint32_t v___x_207_; lean_object* v___x_208_; 
v___x_207_ = 61;
v___x_208_ = lean_box_uint32(v___x_207_);
return v___x_208_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9);
v___x_210_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10___boxed__const__1;
v___x_211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v___x_209_);
return v___x_211_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11___boxed__const__1(void){
_start:
{
uint32_t v___x_212_; lean_object* v___x_213_; 
v___x_212_ = 38;
v___x_213_ = lean_box_uint32(v___x_212_);
return v___x_213_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_214_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10);
v___x_215_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11___boxed__const__1;
v___x_216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v___x_214_);
return v___x_216_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12___boxed__const__1(void){
_start:
{
uint32_t v___x_217_; lean_object* v___x_218_; 
v___x_217_ = 64;
v___x_218_ = lean_box_uint32(v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11);
v___x_220_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12___boxed__const__1;
v___x_221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v___x_219_);
return v___x_221_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13___boxed__const__1(void){
_start:
{
uint32_t v___x_222_; lean_object* v___x_223_; 
v___x_222_ = 93;
v___x_223_ = lean_box_uint32(v___x_222_);
return v___x_223_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12);
v___x_225_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13___boxed__const__1;
v___x_226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___x_224_);
return v___x_226_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14___boxed__const__1(void){
_start:
{
uint32_t v___x_227_; lean_object* v___x_228_; 
v___x_227_ = 91;
v___x_228_ = lean_box_uint32(v___x_227_);
return v___x_228_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13);
v___x_230_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14___boxed__const__1;
v___x_231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v___x_229_);
return v___x_231_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15___boxed__const__1(void){
_start:
{
uint32_t v___x_232_; lean_object* v___x_233_; 
v___x_232_ = 35;
v___x_233_ = lean_box_uint32(v___x_232_);
return v___x_233_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_234_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14);
v___x_235_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15___boxed__const__1;
v___x_236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v___x_234_);
return v___x_236_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16___boxed__const__1(void){
_start:
{
uint32_t v___x_237_; lean_object* v___x_238_; 
v___x_237_ = 63;
v___x_238_ = lean_box_uint32(v___x_237_);
return v___x_238_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15);
v___x_240_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16___boxed__const__1;
v___x_241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v___x_239_);
return v___x_241_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17___boxed__const__1(void){
_start:
{
uint32_t v___x_242_; lean_object* v___x_243_; 
v___x_242_ = 58;
v___x_243_ = lean_box_uint32(v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16);
v___x_245_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17___boxed__const__1;
v___x_246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v___x_244_);
return v___x_246_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18___boxed__const__1(void){
_start:
{
uint32_t v___x_247_; lean_object* v___x_248_; 
v___x_247_ = 59;
v___x_248_ = lean_box_uint32(v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_249_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17);
v___x_250_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18___boxed__const__1;
v___x_251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___x_249_);
return v___x_251_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars(void){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex_spec__0(lean_object* v_s_253_, lean_object* v_p_254_){
_start:
{
uint32_t v___y_256_; lean_object* v___x_261_; uint8_t v_decide_262_; 
v___x_261_ = lean_string_utf8_byte_size(v_s_253_);
v_decide_262_ = lean_nat_dec_eq(v_p_254_, v___x_261_);
if (v_decide_262_ == 0)
{
uint32_t v___x_263_; uint8_t v___y_265_; uint32_t v___x_268_; uint8_t v___x_269_; 
v___x_263_ = lean_string_utf8_get_fast(v_s_253_, v_p_254_);
v___x_268_ = 97;
v___x_269_ = lean_uint32_dec_le(v___x_268_, v___x_263_);
if (v___x_269_ == 0)
{
v___y_265_ = v___x_269_;
goto v___jp_264_;
}
else
{
uint32_t v___x_270_; uint8_t v___x_271_; 
v___x_270_ = 122;
v___x_271_ = lean_uint32_dec_le(v___x_263_, v___x_270_);
v___y_265_ = v___x_271_;
goto v___jp_264_;
}
v___jp_264_:
{
if (v___y_265_ == 0)
{
v___y_256_ = v___x_263_;
goto v___jp_255_;
}
else
{
uint32_t v___x_266_; uint32_t v___x_267_; 
v___x_266_ = 4294967264;
v___x_267_ = lean_uint32_add(v___x_263_, v___x_266_);
v___y_256_ = v___x_267_;
goto v___jp_255_;
}
}
}
else
{
lean_dec(v_p_254_);
return v_s_253_;
}
v___jp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
lean_inc(v_p_254_);
v___x_257_ = lean_string_utf8_set(v_s_253_, v_p_254_, v___y_256_);
v___x_258_ = l_Char_utf8Size(v___y_256_);
v___x_259_ = lean_nat_add(v_p_254_, v___x_258_);
lean_dec(v___x_258_);
lean_dec(v_p_254_);
v_s_253_ = v___x_257_;
v_p_254_ = v___x_259_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(uint8_t v_c_272_){
_start:
{
uint8_t v___x_273_; uint8_t v___x_274_; uint8_t v_d2_275_; uint8_t v_d1_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_273_ = 16;
v___x_274_ = 4;
v_d2_275_ = lean_uint8_shift_right(v_c_272_, v___x_274_);
v_d1_276_ = lean_uint8_mod(v_c_272_, v___x_273_);
v___x_277_ = lean_uint8_to_nat(v_d2_275_);
v___x_278_ = l_hexDigitRepr(v___x_277_);
v___x_279_ = lean_uint8_to_nat(v_d1_276_);
v___x_280_ = l_hexDigitRepr(v___x_279_);
v___x_281_ = lean_string_append(v___x_278_, v___x_280_);
lean_dec_ref(v___x_280_);
v___x_282_ = lean_unsigned_to_nat(0u);
v___x_283_ = l_String_mapAux___at___00__private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex_spec__0(v___x_281_, v___x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex___boxed(lean_object* v_c_284_){
_start:
{
uint8_t v_c_boxed_285_; lean_object* v_res_286_; 
v_c_boxed_285_ = lean_unbox(v_c_284_);
v_res_286_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(v_c_boxed_285_);
return v_res_286_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1(uint32_t v_a_287_, lean_object* v_x_288_){
_start:
{
if (lean_obj_tag(v_x_288_) == 0)
{
uint8_t v___x_289_; 
v___x_289_ = 0;
return v___x_289_;
}
else
{
lean_object* v_head_290_; lean_object* v_tail_291_; uint32_t v___x_292_; uint8_t v___x_293_; 
v_head_290_ = lean_ctor_get(v_x_288_, 0);
v_tail_291_ = lean_ctor_get(v_x_288_, 1);
v___x_292_ = lean_unbox_uint32(v_head_290_);
v___x_293_ = lean_uint32_dec_eq(v_a_287_, v___x_292_);
if (v___x_293_ == 0)
{
v_x_288_ = v_tail_291_;
goto _start;
}
else
{
return v___x_293_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1___boxed(lean_object* v_a_295_, lean_object* v_x_296_){
_start:
{
uint32_t v_a_boxed_297_; uint8_t v_res_298_; lean_object* v_r_299_; 
v_a_boxed_297_ = lean_unbox_uint32(v_a_295_);
lean_dec(v_a_295_);
v_res_298_ = l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1(v_a_boxed_297_, v_x_296_);
lean_dec(v_x_296_);
v_r_299_ = lean_box(v_res_298_);
return v_r_299_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(lean_object* v_as_301_, size_t v_i_302_, size_t v_stop_303_, lean_object* v_b_304_){
_start:
{
uint8_t v___x_305_; 
v___x_305_ = lean_usize_dec_eq(v_i_302_, v_stop_303_);
if (v___x_305_ == 0)
{
uint8_t v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; size_t v___x_311_; size_t v___x_312_; 
v___x_306_ = lean_byte_array_uget(v_as_301_, v_i_302_);
v___x_307_ = ((lean_object*)(l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___closed__0));
v___x_308_ = lean_string_append(v_b_304_, v___x_307_);
v___x_309_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(v___x_306_);
v___x_310_ = lean_string_append(v___x_308_, v___x_309_);
lean_dec_ref(v___x_309_);
v___x_311_ = ((size_t)1ULL);
v___x_312_ = lean_usize_add(v_i_302_, v___x_311_);
v_i_302_ = v___x_312_;
v_b_304_ = v___x_310_;
goto _start;
}
else
{
return v_b_304_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___boxed(lean_object* v_as_314_, lean_object* v_i_315_, lean_object* v_stop_316_, lean_object* v_b_317_){
_start:
{
size_t v_i_boxed_318_; size_t v_stop_boxed_319_; lean_object* v_res_320_; 
v_i_boxed_318_ = lean_unbox_usize(v_i_315_);
lean_dec(v_i_315_);
v_stop_boxed_319_ = lean_unbox_usize(v_stop_316_);
lean_dec(v_stop_316_);
v_res_320_ = l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(v_as_314_, v_i_boxed_318_, v_stop_boxed_319_, v_b_317_);
lean_dec_ref(v_as_314_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_uriEscapeAsciiChar(uint32_t v_c_321_){
_start:
{
uint8_t v___y_323_; lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = l_System_Uri_UriEscape_rfc3986ReservedChars;
v___x_348_ = l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1(v_c_321_, v___x_347_);
if (v___x_348_ == 0)
{
uint32_t v___x_349_; uint8_t v___x_350_; 
v___x_349_ = 32;
v___x_350_ = lean_uint32_dec_lt(v_c_321_, v___x_349_);
v___y_323_ = v___x_350_;
goto v___jp_322_;
}
else
{
v___y_323_ = v___x_348_;
goto v___jp_322_;
}
v___jp_322_:
{
if (v___y_323_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_324_ = lean_uint32_to_nat(v_c_321_);
v___x_325_ = lean_unsigned_to_nat(127u);
v___x_326_ = lean_nat_dec_lt(v___x_324_, v___x_325_);
lean_dec(v___x_324_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_327_ = ((lean_object*)(l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0));
v___x_328_ = lean_string_push(v___x_327_, v_c_321_);
v___x_329_ = lean_string_to_utf8(v___x_328_);
lean_dec_ref(v___x_328_);
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = lean_byte_array_size(v___x_329_);
v___x_332_ = lean_nat_dec_lt(v___x_330_, v___x_331_);
if (v___x_332_ == 0)
{
lean_dec_ref(v___x_329_);
return v___x_327_;
}
else
{
uint8_t v___x_333_; 
v___x_333_ = lean_nat_dec_le(v___x_331_, v___x_331_);
if (v___x_333_ == 0)
{
if (v___x_332_ == 0)
{
lean_dec_ref(v___x_329_);
return v___x_327_;
}
else
{
size_t v___x_334_; size_t v___x_335_; lean_object* v___x_336_; 
v___x_334_ = ((size_t)0ULL);
v___x_335_ = lean_usize_of_nat(v___x_331_);
v___x_336_ = l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(v___x_329_, v___x_334_, v___x_335_, v___x_327_);
lean_dec_ref(v___x_329_);
return v___x_336_;
}
}
else
{
size_t v___x_337_; size_t v___x_338_; lean_object* v___x_339_; 
v___x_337_ = ((size_t)0ULL);
v___x_338_ = lean_usize_of_nat(v___x_331_);
v___x_339_ = l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(v___x_329_, v___x_337_, v___x_338_, v___x_327_);
lean_dec_ref(v___x_329_);
return v___x_339_;
}
}
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = ((lean_object*)(l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0));
v___x_341_ = lean_string_push(v___x_340_, v_c_321_);
return v___x_341_;
}
}
else
{
lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_342_ = ((lean_object*)(l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___closed__0));
v___x_343_ = lean_uint32_to_nat(v_c_321_);
v___x_344_ = lean_uint8_of_nat(v___x_343_);
lean_dec(v___x_343_);
v___x_345_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(v___x_344_);
v___x_346_ = lean_string_append(v___x_342_, v___x_345_);
lean_dec_ref(v___x_345_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_uriEscapeAsciiChar___boxed(lean_object* v_c_351_){
_start:
{
uint32_t v_c_boxed_352_; lean_object* v_res_353_; 
v_c_boxed_352_ = lean_unbox_uint32(v_c_351_);
lean_dec(v_c_351_);
v_res_353_ = l_System_Uri_UriEscape_uriEscapeAsciiChar(v_c_boxed_352_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(lean_object* v___x_354_, lean_object* v_uri_355_, lean_object* v_a_356_, lean_object* v_b_357_){
_start:
{
uint8_t v_decide_358_; 
v_decide_358_ = lean_nat_dec_eq(v_a_356_, v___x_354_);
if (v_decide_358_ == 0)
{
uint32_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_359_ = lean_string_utf8_get_fast(v_uri_355_, v_a_356_);
v___x_360_ = lean_string_utf8_next_fast(v_uri_355_, v_a_356_);
lean_dec(v_a_356_);
v___x_361_ = l_System_Uri_UriEscape_uriEscapeAsciiChar(v___x_359_);
v___x_362_ = lean_string_append(v_b_357_, v___x_361_);
lean_dec_ref(v___x_361_);
v_a_356_ = v___x_360_;
v_b_357_ = v___x_362_;
goto _start;
}
else
{
lean_dec(v_a_356_);
return v_b_357_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg___boxed(lean_object* v___x_364_, lean_object* v_uri_365_, lean_object* v_a_366_, lean_object* v_b_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(v___x_364_, v_uri_365_, v_a_366_, v_b_367_);
lean_dec_ref(v_uri_365_);
lean_dec(v___x_364_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_escapeUri(lean_object* v_uri_369_){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_370_ = ((lean_object*)(l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0));
v___x_371_ = lean_unsigned_to_nat(0u);
v___x_372_ = lean_string_utf8_byte_size(v_uri_369_);
lean_inc_ref(v_uri_369_);
v___x_373_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_373_, 0, v_uri_369_);
lean_ctor_set(v___x_373_, 1, v___x_371_);
lean_ctor_set(v___x_373_, 2, v___x_372_);
v___x_374_ = l_String_Slice_positions(v___x_373_);
lean_dec_ref_known(v___x_373_, 3);
v___x_375_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(v___x_372_, v_uri_369_, v___x_374_, v___x_370_);
lean_dec_ref(v_uri_369_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0(lean_object* v___x_376_, lean_object* v___x_377_, lean_object* v_uri_378_, lean_object* v_inst_379_, lean_object* v_R_380_, lean_object* v_a_381_, lean_object* v_b_382_, lean_object* v_c_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(v___x_377_, v_uri_378_, v_a_381_, v_b_382_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___boxed(lean_object* v___x_385_, lean_object* v___x_386_, lean_object* v_uri_387_, lean_object* v_inst_388_, lean_object* v_R_389_, lean_object* v_a_390_, lean_object* v_b_391_, lean_object* v_c_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0(v___x_385_, v___x_386_, v_uri_387_, v_inst_388_, v_R_389_, v_a_390_, v_b_391_, v_c_392_);
lean_dec_ref(v_uri_387_);
lean_dec(v___x_386_);
lean_dec_ref(v___x_385_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_unescapeUri(lean_object* v_s_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_System_Uri_UriEscape_decodeUri(v_s_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_unescapeUri___boxed(lean_object* v_s_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_System_Uri_unescapeUri(v_s_396_);
lean_dec_ref(v_s_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg(lean_object* v_uri_398_, lean_object* v___x_399_, lean_object* v_a_400_, lean_object* v_b_401_){
_start:
{
lean_object* v_countdown_402_; lean_object* v_inner_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_419_; 
v_countdown_402_ = lean_ctor_get(v_a_400_, 0);
v_inner_403_ = lean_ctor_get(v_a_400_, 1);
v_isSharedCheck_419_ = !lean_is_exclusive(v_a_400_);
if (v_isSharedCheck_419_ == 0)
{
v___x_405_ = v_a_400_;
v_isShared_406_ = v_isSharedCheck_419_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_inner_403_);
lean_inc(v_countdown_402_);
lean_dec(v_a_400_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_419_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = lean_unsigned_to_nat(1u);
v___x_408_ = lean_nat_dec_eq(v_countdown_402_, v___x_407_);
if (v___x_408_ == 0)
{
uint8_t v_decide_409_; 
v_decide_409_ = lean_nat_dec_eq(v_inner_403_, v___x_399_);
if (v_decide_409_ == 0)
{
lean_object* v___x_410_; uint32_t v___x_411_; lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_410_ = lean_string_utf8_next_fast(v_uri_398_, v_inner_403_);
v___x_411_ = lean_string_utf8_get_fast(v_uri_398_, v_inner_403_);
lean_dec(v_inner_403_);
v___x_412_ = lean_nat_sub(v_countdown_402_, v___x_407_);
lean_dec(v_countdown_402_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 1, v___x_410_);
lean_ctor_set(v___x_405_, 0, v___x_412_);
v___x_414_ = v___x_405_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v___x_410_);
v___x_414_ = v_reuseFailAlloc_418_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_box_uint32(v___x_411_);
v___x_416_ = lean_array_push(v_b_401_, v___x_415_);
v_a_400_ = v___x_414_;
v_b_401_ = v___x_416_;
goto _start;
}
}
else
{
lean_del_object(v___x_405_);
lean_dec(v_inner_403_);
lean_dec(v_countdown_402_);
return v_b_401_;
}
}
else
{
lean_del_object(v___x_405_);
lean_dec(v_inner_403_);
lean_dec(v_countdown_402_);
return v_b_401_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg___boxed(lean_object* v_uri_420_, lean_object* v___x_421_, lean_object* v_a_422_, lean_object* v_b_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg(v_uri_420_, v___x_421_, v_a_422_, v_b_423_);
lean_dec(v___x_421_);
lean_dec_ref(v_uri_420_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter(lean_object* v_uri_427_){
_start:
{
lean_object* v___x_428_; uint32_t v___y_430_; uint8_t v___y_431_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_436_ = lean_string_utf8_byte_size(v_uri_427_);
lean_inc_ref(v_uri_427_);
v___x_437_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_437_, 0, v_uri_427_);
lean_ctor_set(v___x_437_, 1, v___x_428_);
lean_ctor_set(v___x_437_, 2, v___x_436_);
v___x_438_ = l_String_Slice_positions(v___x_437_);
lean_dec_ref_known(v___x_437_, 3);
v___x_439_ = lean_unsigned_to_nat(3u);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v___x_438_);
v___x_441_ = ((lean_object*)(l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__0));
v___x_442_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg(v_uri_427_, v___x_436_, v___x_440_, v___x_441_);
v___x_443_ = lean_array_to_list(v___x_442_);
if (lean_obj_tag(v___x_443_) == 1)
{
lean_object* v_tail_444_; 
v_tail_444_ = lean_ctor_get(v___x_443_, 1);
lean_inc(v_tail_444_);
if (lean_obj_tag(v_tail_444_) == 1)
{
lean_object* v_head_445_; lean_object* v_head_446_; lean_object* v_tail_447_; uint32_t v___x_448_; uint32_t v___x_449_; uint8_t v___x_450_; 
v_head_445_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_head_445_);
lean_dec_ref_known(v___x_443_, 2);
v_head_446_ = lean_ctor_get(v_tail_444_, 0);
lean_inc(v_head_446_);
v_tail_447_ = lean_ctor_get(v_tail_444_, 1);
lean_inc(v_tail_447_);
lean_dec_ref_known(v_tail_444_, 2);
v___x_448_ = 58;
v___x_449_ = lean_unbox_uint32(v_head_446_);
lean_dec(v_head_446_);
v___x_450_ = lean_uint32_dec_eq(v___x_449_, v___x_448_);
if (v___x_450_ == 0)
{
lean_dec(v_tail_447_);
lean_dec(v_head_445_);
return v_uri_427_;
}
else
{
if (lean_obj_tag(v_tail_447_) == 0)
{
uint32_t v___x_451_; uint32_t v___x_452_; uint8_t v___x_453_; uint32_t v___x_454_; uint8_t v___y_456_; 
v___x_451_ = 65;
v___x_452_ = lean_unbox_uint32(v_head_445_);
v___x_453_ = lean_uint32_dec_le(v___x_451_, v___x_452_);
v___x_454_ = 90;
if (v___x_453_ == 0)
{
lean_dec(v_head_445_);
v___y_456_ = v___x_453_;
goto v___jp_455_;
}
else
{
uint32_t v___x_460_; uint8_t v___x_461_; 
v___x_460_ = lean_unbox_uint32(v_head_445_);
lean_dec(v_head_445_);
v___x_461_ = lean_uint32_dec_le(v___x_460_, v___x_454_);
v___y_456_ = v___x_461_;
goto v___jp_455_;
}
v___jp_455_:
{
if (v___y_456_ == 0)
{
return v_uri_427_;
}
else
{
uint32_t v___x_457_; uint8_t v___x_458_; 
v___x_457_ = lean_string_utf8_get(v_uri_427_, v___x_428_);
v___x_458_ = lean_uint32_dec_le(v___x_451_, v___x_457_);
if (v___x_458_ == 0)
{
v___y_430_ = v___x_457_;
v___y_431_ = v___x_458_;
goto v___jp_429_;
}
else
{
uint8_t v___x_459_; 
v___x_459_ = lean_uint32_dec_le(v___x_457_, v___x_454_);
v___y_430_ = v___x_457_;
v___y_431_ = v___x_459_;
goto v___jp_429_;
}
}
}
}
else
{
lean_dec(v_tail_447_);
lean_dec(v_head_445_);
return v_uri_427_;
}
}
}
else
{
lean_dec(v_tail_444_);
lean_dec_ref_known(v___x_443_, 2);
return v_uri_427_;
}
}
else
{
lean_dec(v___x_443_);
return v_uri_427_;
}
v___jp_429_:
{
if (v___y_431_ == 0)
{
lean_object* v___x_432_; 
v___x_432_ = lean_string_utf8_set(v_uri_427_, v___x_428_, v___y_430_);
return v___x_432_;
}
else
{
uint32_t v___x_433_; uint32_t v___x_434_; lean_object* v___x_435_; 
v___x_433_ = 32;
v___x_434_ = lean_uint32_add(v___y_430_, v___x_433_);
v___x_435_ = lean_string_utf8_set(v_uri_427_, v___x_428_, v___x_434_);
return v___x_435_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0(lean_object* v___x_462_, lean_object* v_uri_463_, lean_object* v___x_464_, lean_object* v_inst_465_, lean_object* v_R_466_, lean_object* v_a_467_, lean_object* v_b_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg(v_uri_463_, v___x_464_, v_a_467_, v_b_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___boxed(lean_object* v___x_470_, lean_object* v_uri_471_, lean_object* v___x_472_, lean_object* v_inst_473_, lean_object* v_R_474_, lean_object* v_a_475_, lean_object* v_b_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0(v___x_470_, v_uri_471_, v___x_472_, v_inst_473_, v_R_474_, v_a_475_, v_b_476_);
lean_dec(v___x_472_);
lean_dec_ref(v_uri_471_);
lean_dec_ref(v___x_470_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_Uri_pathToUri_spec__0(lean_object* v_s_478_, lean_object* v_p_479_){
_start:
{
uint32_t v___y_481_; lean_object* v___x_486_; uint8_t v_decide_487_; 
v___x_486_ = lean_string_utf8_byte_size(v_s_478_);
v_decide_487_ = lean_nat_dec_eq(v_p_479_, v___x_486_);
if (v_decide_487_ == 0)
{
uint32_t v___x_488_; uint32_t v___x_489_; uint8_t v___x_490_; 
v___x_488_ = lean_string_utf8_get_fast(v_s_478_, v_p_479_);
v___x_489_ = 92;
v___x_490_ = lean_uint32_dec_eq(v___x_488_, v___x_489_);
if (v___x_490_ == 0)
{
v___y_481_ = v___x_488_;
goto v___jp_480_;
}
else
{
uint32_t v___x_491_; 
v___x_491_ = 47;
v___y_481_ = v___x_491_;
goto v___jp_480_;
}
}
else
{
lean_dec(v_p_479_);
return v_s_478_;
}
v___jp_480_:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
lean_inc(v_p_479_);
v___x_482_ = lean_string_utf8_set(v_s_478_, v_p_479_, v___y_481_);
v___x_483_ = l_Char_utf8Size(v___y_481_);
v___x_484_ = lean_nat_add(v_p_479_, v___x_483_);
lean_dec(v___x_483_);
lean_dec(v_p_479_);
v_s_478_ = v___x_482_;
v_p_479_ = v___x_484_;
goto _start;
}
}
}
static lean_object* _init_l_System_Uri_pathToUri___closed__2(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l_System_Uri_pathToUri___closed__1));
v___x_495_ = lean_string_utf8_byte_size(v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_pathToUri(lean_object* v_fname_497_){
_start:
{
lean_object* v___y_499_; lean_object* v_uri_503_; lean_object* v_uri_517_; uint8_t v___x_518_; 
v_uri_517_ = l_System_FilePath_normalize(v_fname_497_);
v___x_518_ = l_System_Platform_isWindows;
if (v___x_518_ == 0)
{
v_uri_503_ = v_uri_517_;
goto v___jp_502_;
}
else
{
lean_object* v_uri_519_; lean_object* v___x_520_; lean_object* v_uri_521_; 
v_uri_519_ = l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter(v_uri_517_);
v___x_520_ = lean_unsigned_to_nat(0u);
v_uri_521_ = l_String_mapAux___at___00System_Uri_pathToUri_spec__0(v_uri_519_, v___x_520_);
v_uri_503_ = v_uri_521_;
goto v___jp_502_;
}
v___jp_498_:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = ((lean_object*)(l_System_Uri_pathToUri___closed__0));
v___x_501_ = lean_string_append(v___x_500_, v___y_499_);
lean_dec_ref(v___y_499_);
return v___x_501_;
}
v___jp_502_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v_uri_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_504_ = ((lean_object*)(l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0));
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = lean_string_utf8_byte_size(v_uri_503_);
lean_inc_ref(v_uri_503_);
v___x_507_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_507_, 0, v_uri_503_);
lean_ctor_set(v___x_507_, 1, v___x_505_);
lean_ctor_set(v___x_507_, 2, v___x_506_);
v___x_508_ = l_String_Slice_positions(v___x_507_);
lean_dec_ref_known(v___x_507_, 3);
v_uri_509_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(v___x_506_, v_uri_503_, v___x_508_, v___x_504_);
lean_dec_ref(v_uri_503_);
v___x_510_ = ((lean_object*)(l_System_Uri_pathToUri___closed__1));
v___x_511_ = lean_string_utf8_byte_size(v_uri_509_);
v___x_512_ = lean_obj_once(&l_System_Uri_pathToUri___closed__2, &l_System_Uri_pathToUri___closed__2_once, _init_l_System_Uri_pathToUri___closed__2);
v___x_513_ = lean_nat_dec_le(v___x_512_, v___x_511_);
if (v___x_513_ == 0)
{
v___y_499_ = v_uri_509_;
goto v___jp_498_;
}
else
{
uint8_t v___x_514_; 
v___x_514_ = lean_string_memcmp(v_uri_509_, v___x_510_, v___x_505_, v___x_505_, v___x_512_);
if (v___x_514_ == 0)
{
v___y_499_ = v_uri_509_;
goto v___jp_498_;
}
else
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = ((lean_object*)(l_System_Uri_pathToUri___closed__3));
v___x_516_ = lean_string_append(v___x_515_, v_uri_509_);
lean_dec_ref(v_uri_509_);
return v___x_516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg(lean_object* v_p_522_, lean_object* v_a_523_, lean_object* v_b_524_){
_start:
{
lean_object* v_countdown_525_; lean_object* v_inner_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_548_; 
v_countdown_525_ = lean_ctor_get(v_a_523_, 0);
v_inner_526_ = lean_ctor_get(v_a_523_, 1);
v_isSharedCheck_548_ = !lean_is_exclusive(v_a_523_);
if (v_isSharedCheck_548_ == 0)
{
v___x_528_ = v_a_523_;
v_isShared_529_ = v_isSharedCheck_548_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_inner_526_);
lean_inc(v_countdown_525_);
lean_dec(v_a_523_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_548_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_530_ = lean_unsigned_to_nat(1u);
v___x_531_ = lean_nat_dec_eq(v_countdown_525_, v___x_530_);
if (v___x_531_ == 0)
{
lean_object* v_str_532_; lean_object* v_startInclusive_533_; lean_object* v_endExclusive_534_; lean_object* v___x_535_; uint8_t v_decide_536_; 
v_str_532_ = lean_ctor_get(v_p_522_, 0);
v_startInclusive_533_ = lean_ctor_get(v_p_522_, 1);
v_endExclusive_534_ = lean_ctor_get(v_p_522_, 2);
v___x_535_ = lean_nat_sub(v_endExclusive_534_, v_startInclusive_533_);
v_decide_536_ = lean_nat_dec_eq(v_inner_526_, v___x_535_);
lean_dec(v___x_535_);
if (v_decide_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; uint32_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_537_ = lean_nat_add(v_startInclusive_533_, v_inner_526_);
lean_dec(v_inner_526_);
v___x_538_ = lean_string_utf8_next_fast(v_str_532_, v___x_537_);
v___x_539_ = lean_nat_sub(v___x_538_, v_startInclusive_533_);
v___x_540_ = lean_string_utf8_get_fast(v_str_532_, v___x_537_);
lean_dec(v___x_537_);
v___x_541_ = lean_nat_sub(v_countdown_525_, v___x_530_);
lean_dec(v_countdown_525_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 1, v___x_539_);
lean_ctor_set(v___x_528_, 0, v___x_541_);
v___x_543_ = v___x_528_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v___x_539_);
v___x_543_ = v_reuseFailAlloc_547_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_box_uint32(v___x_540_);
v___x_545_ = lean_array_push(v_b_524_, v___x_544_);
v_a_523_ = v___x_543_;
v_b_524_ = v___x_545_;
goto _start;
}
}
else
{
lean_del_object(v___x_528_);
lean_dec(v_inner_526_);
lean_dec(v_countdown_525_);
return v_b_524_;
}
}
else
{
lean_del_object(v___x_528_);
lean_dec(v_inner_526_);
lean_dec(v_countdown_525_);
return v_b_524_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg___boxed(lean_object* v_p_549_, lean_object* v_a_550_, lean_object* v_b_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg(v_p_549_, v_a_550_, v_b_551_);
lean_dec_ref(v_p_549_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression(lean_object* v_p_553_){
_start:
{
uint32_t v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; uint8_t v___y_563_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_587_ = l_String_Slice_positions(v_p_553_);
v___x_588_ = lean_unsigned_to_nat(4u);
v___x_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
lean_ctor_set(v___x_589_, 1, v___x_587_);
v___x_590_ = ((lean_object*)(l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__0));
v___x_591_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg(v_p_553_, v___x_589_, v___x_590_);
v___x_592_ = lean_array_to_list(v___x_591_);
if (lean_obj_tag(v___x_592_) == 1)
{
lean_object* v_head_593_; lean_object* v_tail_594_; uint32_t v___x_595_; uint32_t v___x_596_; uint8_t v___x_597_; 
v_head_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_head_593_);
v_tail_594_ = lean_ctor_get(v___x_592_, 1);
lean_inc(v_tail_594_);
lean_dec_ref_known(v___x_592_, 2);
v___x_595_ = 47;
v___x_596_ = lean_unbox_uint32(v_head_593_);
lean_dec(v_head_593_);
v___x_597_ = lean_uint32_dec_eq(v___x_596_, v___x_595_);
if (v___x_597_ == 0)
{
lean_dec(v_tail_594_);
goto v___jp_582_;
}
else
{
if (lean_obj_tag(v_tail_594_) == 1)
{
lean_object* v_head_598_; lean_object* v_tail_599_; uint8_t v___y_601_; 
v_head_598_ = lean_ctor_get(v_tail_594_, 0);
lean_inc(v_head_598_);
v_tail_599_ = lean_ctor_get(v_tail_594_, 1);
lean_inc(v_tail_599_);
lean_dec_ref_known(v_tail_594_, 2);
if (lean_obj_tag(v_tail_599_) == 1)
{
lean_object* v_head_608_; lean_object* v_tail_609_; uint32_t v___x_610_; uint32_t v___x_611_; uint8_t v___x_612_; 
v_head_608_ = lean_ctor_get(v_tail_599_, 0);
lean_inc(v_head_608_);
v_tail_609_ = lean_ctor_get(v_tail_599_, 1);
lean_inc(v_tail_609_);
lean_dec_ref_known(v_tail_599_, 2);
v___x_610_ = 58;
v___x_611_ = lean_unbox_uint32(v_head_608_);
lean_dec(v_head_608_);
v___x_612_ = lean_uint32_dec_eq(v___x_611_, v___x_610_);
if (v___x_612_ == 0)
{
lean_dec(v_tail_609_);
lean_dec(v_head_598_);
goto v___jp_582_;
}
else
{
if (lean_obj_tag(v_tail_609_) == 0)
{
uint32_t v___x_613_; uint32_t v___x_614_; uint8_t v___x_615_; 
v___x_613_ = 65;
v___x_614_ = lean_unbox_uint32(v_head_598_);
v___x_615_ = lean_uint32_dec_le(v___x_613_, v___x_614_);
if (v___x_615_ == 0)
{
v___y_601_ = v___x_615_;
goto v___jp_600_;
}
else
{
uint32_t v___x_616_; uint32_t v___x_617_; uint8_t v___x_618_; 
v___x_616_ = 90;
v___x_617_ = lean_unbox_uint32(v_head_598_);
v___x_618_ = lean_uint32_dec_le(v___x_617_, v___x_616_);
v___y_601_ = v___x_618_;
goto v___jp_600_;
}
}
else
{
lean_dec(v_tail_609_);
lean_dec(v_head_598_);
goto v___jp_582_;
}
}
}
else
{
lean_dec(v_tail_599_);
lean_dec(v_head_598_);
goto v___jp_582_;
}
v___jp_600_:
{
if (v___y_601_ == 0)
{
uint32_t v___x_602_; uint32_t v___x_603_; uint8_t v___x_604_; 
v___x_602_ = 97;
v___x_603_ = lean_unbox_uint32(v_head_598_);
v___x_604_ = lean_uint32_dec_le(v___x_602_, v___x_603_);
if (v___x_604_ == 0)
{
lean_dec(v_head_598_);
goto v___jp_554_;
}
else
{
uint32_t v___x_605_; uint32_t v___x_606_; uint8_t v___x_607_; 
v___x_605_ = 122;
v___x_606_ = lean_unbox_uint32(v_head_598_);
lean_dec(v_head_598_);
v___x_607_ = lean_uint32_dec_le(v___x_606_, v___x_605_);
if (v___x_607_ == 0)
{
goto v___jp_554_;
}
else
{
goto v___jp_568_;
}
}
}
else
{
lean_dec(v_head_598_);
goto v___jp_568_;
}
}
}
else
{
lean_dec(v_tail_594_);
goto v___jp_582_;
}
}
}
else
{
lean_dec(v___x_592_);
goto v___jp_582_;
}
v___jp_554_:
{
lean_object* v_str_555_; lean_object* v_startInclusive_556_; lean_object* v_endExclusive_557_; lean_object* v___x_558_; 
v_str_555_ = lean_ctor_get(v_p_553_, 0);
v_startInclusive_556_ = lean_ctor_get(v_p_553_, 1);
v_endExclusive_557_ = lean_ctor_get(v_p_553_, 2);
v___x_558_ = lean_string_utf8_extract_fast(v_str_555_, v_startInclusive_556_, v_endExclusive_557_);
return v___x_558_;
}
v___jp_559_:
{
if (v___y_563_ == 0)
{
lean_object* v___x_564_; 
v___x_564_ = lean_string_utf8_set(v___y_562_, v___y_561_, v___y_560_);
lean_dec(v___y_561_);
return v___x_564_;
}
else
{
uint32_t v___x_565_; uint32_t v___x_566_; lean_object* v___x_567_; 
v___x_565_ = 4294967264;
v___x_566_ = lean_uint32_add(v___y_560_, v___x_565_);
v___x_567_ = lean_string_utf8_set(v___y_562_, v___y_561_, v___x_566_);
lean_dec(v___y_561_);
return v___x_567_;
}
}
v___jp_568_:
{
lean_object* v_str_569_; lean_object* v_startInclusive_570_; lean_object* v_endExclusive_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; uint32_t v___x_577_; uint32_t v___x_578_; uint8_t v___x_579_; 
v_str_569_ = lean_ctor_get(v_p_553_, 0);
v_startInclusive_570_ = lean_ctor_get(v_p_553_, 1);
v_endExclusive_571_ = lean_ctor_get(v_p_553_, 2);
v___x_572_ = lean_unsigned_to_nat(1u);
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = l_String_Slice_Pos_nextn(v_p_553_, v___x_573_, v___x_572_);
v___x_575_ = lean_nat_add(v_startInclusive_570_, v___x_574_);
lean_dec(v___x_574_);
v___x_576_ = lean_string_utf8_extract_fast(v_str_569_, v___x_575_, v_endExclusive_571_);
lean_dec(v___x_575_);
v___x_577_ = lean_string_utf8_get(v___x_576_, v___x_573_);
v___x_578_ = 97;
v___x_579_ = lean_uint32_dec_le(v___x_578_, v___x_577_);
if (v___x_579_ == 0)
{
v___y_560_ = v___x_577_;
v___y_561_ = v___x_573_;
v___y_562_ = v___x_576_;
v___y_563_ = v___x_579_;
goto v___jp_559_;
}
else
{
uint32_t v___x_580_; uint8_t v___x_581_; 
v___x_580_ = 122;
v___x_581_ = lean_uint32_dec_le(v___x_577_, v___x_580_);
v___y_560_ = v___x_577_;
v___y_561_ = v___x_573_;
v___y_562_ = v___x_576_;
v___y_563_ = v___x_581_;
goto v___jp_559_;
}
}
v___jp_582_:
{
lean_object* v_str_583_; lean_object* v_startInclusive_584_; lean_object* v_endExclusive_585_; lean_object* v___x_586_; 
v_str_583_ = lean_ctor_get(v_p_553_, 0);
v_startInclusive_584_ = lean_ctor_get(v_p_553_, 1);
v_endExclusive_585_ = lean_ctor_get(v_p_553_, 2);
v___x_586_ = lean_string_utf8_extract_fast(v_str_583_, v_startInclusive_584_, v_endExclusive_585_);
return v___x_586_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression___boxed(lean_object* v_p_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression(v_p_619_);
lean_dec_ref(v_p_619_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0(lean_object* v_p_621_, lean_object* v_inst_622_, lean_object* v_R_623_, lean_object* v_a_624_, lean_object* v_b_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg(v_p_621_, v_a_624_, v_b_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___boxed(lean_object* v_p_627_, lean_object* v_inst_628_, lean_object* v_R_629_, lean_object* v_a_630_, lean_object* v_b_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0(v_p_627_, v_inst_628_, v_R_629_, v_a_630_, v_b_631_);
lean_dec_ref(v_p_627_);
return v_res_632_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = ((lean_object*)(l_System_Uri_pathToUri___closed__3));
v___x_634_ = lean_string_utf8_byte_size(v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg(lean_object* v_s_635_){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_636_ = ((lean_object*)(l_System_Uri_pathToUri___closed__3));
v___x_637_ = lean_string_utf8_byte_size(v_s_635_);
v___x_638_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg___closed__0, &l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg___closed__0_once, _init_l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg___closed__0);
v___x_639_ = lean_nat_dec_le(v___x_638_, v___x_637_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
lean_dec_ref(v_s_635_);
v___x_640_ = lean_box(0);
return v___x_640_;
}
else
{
lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_641_ = lean_unsigned_to_nat(0u);
v___x_642_ = lean_string_memcmp(v_s_635_, v___x_636_, v___x_641_, v___x_641_, v___x_638_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
lean_dec_ref(v_s_635_);
v___x_643_ = lean_box(0);
return v___x_643_;
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
lean_inc_ref(v_s_635_);
v___x_644_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_644_, 0, v_s_635_);
lean_ctor_set(v___x_644_, 1, v___x_641_);
lean_ctor_set(v___x_644_, 2, v___x_637_);
v___x_645_ = l_String_Slice_pos_x21(v___x_644_, v___x_638_);
lean_dec_ref_known(v___x_644_, 3);
v___x_646_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_646_, 0, v_s_635_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
lean_ctor_set(v___x_646_, 2, v___x_637_);
v___x_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
return v___x_647_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0(lean_object* v_s_648_, lean_object* v_pat_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg(v_s_648_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___boxed(lean_object* v_s_651_, lean_object* v_pat_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0(v_s_651_, v_pat_652_);
lean_dec_ref(v_pat_652_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1(lean_object* v_s_654_, lean_object* v_pos_655_){
_start:
{
lean_object* v_str_656_; lean_object* v_startInclusive_657_; lean_object* v_endExclusive_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v_decide_662_; 
v_str_656_ = lean_ctor_get(v_s_654_, 0);
v_startInclusive_657_ = lean_ctor_get(v_s_654_, 1);
v_endExclusive_658_ = lean_ctor_get(v_s_654_, 2);
v___x_659_ = lean_nat_add(v_startInclusive_657_, v_pos_655_);
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = lean_nat_sub(v_endExclusive_658_, v___x_659_);
v_decide_662_ = lean_nat_dec_eq(v___x_660_, v___x_661_);
lean_dec(v___x_661_);
if (v_decide_662_ == 0)
{
uint32_t v___x_663_; uint32_t v___x_664_; uint8_t v___x_665_; 
v___x_663_ = lean_string_utf8_get_fast(v_str_656_, v___x_659_);
v___x_664_ = 47;
v___x_665_ = lean_uint32_dec_eq(v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_666_ = lean_string_utf8_next_fast(v_str_656_, v___x_659_);
v___x_667_ = lean_nat_sub(v___x_666_, v___x_659_);
lean_dec(v___x_659_);
v___x_668_ = lean_nat_add(v_pos_655_, v___x_667_);
lean_dec(v___x_667_);
v___x_669_ = lean_unsigned_to_nat(1u);
v___x_670_ = lean_nat_add(v_pos_655_, v___x_669_);
v___x_671_ = lean_nat_dec_le(v___x_670_, v___x_668_);
lean_dec(v___x_670_);
if (v___x_671_ == 0)
{
lean_dec(v___x_668_);
return v_pos_655_;
}
else
{
lean_dec(v_pos_655_);
v_pos_655_ = v___x_668_;
goto _start;
}
}
else
{
lean_dec(v___x_659_);
return v_pos_655_;
}
}
else
{
lean_dec(v___x_659_);
return v_pos_655_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1___boxed(lean_object* v_s_673_, lean_object* v_pos_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1(v_s_673_, v_pos_674_);
lean_dec_ref(v_s_673_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_Uri_fileUriToPath_x3f_spec__2(lean_object* v_s_676_, lean_object* v_p_677_){
_start:
{
uint32_t v___y_679_; lean_object* v___x_684_; uint8_t v_decide_685_; 
v___x_684_ = lean_string_utf8_byte_size(v_s_676_);
v_decide_685_ = lean_nat_dec_eq(v_p_677_, v___x_684_);
if (v_decide_685_ == 0)
{
uint32_t v___x_686_; uint32_t v___x_687_; uint8_t v___x_688_; 
v___x_686_ = lean_string_utf8_get_fast(v_s_676_, v_p_677_);
v___x_687_ = 47;
v___x_688_ = lean_uint32_dec_eq(v___x_686_, v___x_687_);
if (v___x_688_ == 0)
{
v___y_679_ = v___x_686_;
goto v___jp_678_;
}
else
{
uint32_t v___x_689_; 
v___x_689_ = 92;
v___y_679_ = v___x_689_;
goto v___jp_678_;
}
}
else
{
lean_dec(v_p_677_);
return v_s_676_;
}
v___jp_678_:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
lean_inc(v_p_677_);
v___x_680_ = lean_string_utf8_set(v_s_676_, v_p_677_, v___y_679_);
v___x_681_ = l_Char_utf8Size(v___y_679_);
v___x_682_ = lean_nat_add(v_p_677_, v___x_681_);
lean_dec(v___x_681_);
lean_dec(v_p_677_);
v_s_676_ = v___x_680_;
v_p_677_ = v___x_682_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_fileUriToPath_x3f(lean_object* v_uri_690_){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = l_System_Uri_UriEscape_decodeUri(v_uri_690_);
v___x_692_ = l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg(v___x_691_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v___x_693_; 
v___x_693_ = lean_box(0);
return v___x_693_;
}
else
{
lean_object* v_val_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_724_; 
v_val_694_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_724_ == 0)
{
v___x_696_ = v___x_692_;
v_isShared_697_ = v_isSharedCheck_724_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_val_694_);
lean_dec(v___x_692_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_724_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v_str_698_; lean_object* v_startInclusive_699_; lean_object* v_endExclusive_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_720_; 
v_str_698_ = lean_ctor_get(v_val_694_, 0);
lean_inc_ref(v_str_698_);
v_startInclusive_699_ = lean_ctor_get(v_val_694_, 1);
lean_inc(v_startInclusive_699_);
v_endExclusive_700_ = lean_ctor_get(v_val_694_, 2);
lean_inc(v_endExclusive_700_);
v___x_701_ = lean_unsigned_to_nat(0u);
v___x_702_ = l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1(v_val_694_, v___x_701_);
v_isSharedCheck_720_ = !lean_is_exclusive(v_val_694_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; lean_object* v_unused_722_; lean_object* v_unused_723_; 
v_unused_721_ = lean_ctor_get(v_val_694_, 2);
lean_dec(v_unused_721_);
v_unused_722_ = lean_ctor_get(v_val_694_, 1);
lean_dec(v_unused_722_);
v_unused_723_ = lean_ctor_get(v_val_694_, 0);
lean_dec(v_unused_723_);
v___x_704_ = v_val_694_;
v_isShared_705_ = v_isSharedCheck_720_;
goto v_resetjp_703_;
}
else
{
lean_dec(v_val_694_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_720_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_706_ = lean_nat_add(v_startInclusive_699_, v___x_702_);
lean_dec(v___x_702_);
lean_dec(v_startInclusive_699_);
v___x_707_ = l_System_Platform_isWindows;
if (v___x_707_ == 0)
{
lean_object* v___x_708_; lean_object* v___x_710_; 
lean_del_object(v___x_704_);
v___x_708_ = lean_string_utf8_extract_fast(v_str_698_, v___x_706_, v_endExclusive_700_);
lean_dec(v_endExclusive_700_);
lean_dec(v___x_706_);
lean_dec_ref(v_str_698_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_708_);
v___x_710_ = v___x_696_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
else
{
lean_object* v_p_713_; 
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 1, v___x_706_);
v_p_713_ = v___x_704_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_str_698_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_endExclusive_700_);
v_p_713_ = v_reuseFailAlloc_719_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_714_ = l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression(v_p_713_);
lean_dec_ref(v_p_713_);
v___x_715_ = l_String_mapAux___at___00System_Uri_fileUriToPath_x3f_spec__2(v___x_714_, v___x_701_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_715_);
v___x_717_ = v___x_696_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_fileUriToPath_x3f___boxed(lean_object* v_uri_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_System_Uri_fileUriToPath_x3f(v_uri_725_);
lean_dec_ref(v_uri_725_);
return v_res_726_;
}
}
lean_object* runtime_initialize_Init_System_FilePath(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Take(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_System_Uri(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_System_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_System_Uri_UriEscape_zero = _init_l_System_Uri_UriEscape_zero();
l_System_Uri_UriEscape_nine = _init_l_System_Uri_UriEscape_nine();
l_System_Uri_UriEscape_lettera = _init_l_System_Uri_UriEscape_lettera();
l_System_Uri_UriEscape_letterf = _init_l_System_Uri_UriEscape_letterf();
l_System_Uri_UriEscape_letterA = _init_l_System_Uri_UriEscape_letterA();
l_System_Uri_UriEscape_letterF = _init_l_System_Uri_UriEscape_letterF();
l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0___boxed__const__1 = _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0___boxed__const__1();
lean_mark_persistent(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0___boxed__const__1);
l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1___boxed__const__1 = _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1___boxed__const__1();
lean_mark_persistent(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1___boxed__const__1);
l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2___boxed__const__1 = _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2___boxed__const__1();
lean_mark_persistent(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2___boxed__const__1);
l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3___boxed__const__1 = _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3___boxed__const__1();
lean_mark_persistent(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3___boxed__const__1);
l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4___boxed__const__1 = _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4___boxed__const__1();
lean_mark_persistent(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4___boxed__const__1);
l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5___boxed__const__1 = _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5___boxed__const__1();
lean_mark_persistent(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5___boxed__const__1);
l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6___boxed__const__1 = _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6___boxed__const__1();
lean_mark_persistent(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6___boxed__const__1);
l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7___boxed__const__1 = _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7___boxed__const__1();
lean_mark_persistent(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7___boxed__const__1);
l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8___boxed__const__1 = _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8___boxed__const__1();
lean_mark_persistent(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8___boxed__const__1);
l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9___boxed__const__1 = _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9___boxed__const__1();
lean_mark_persistent(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9___boxed__const__1);
l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10___boxed__const__1 = _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10___boxed__const__1();
lean_mark_persistent(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10___boxed__const__1);
l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11___boxed__const__1 = _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11___boxed__const__1();
lean_mark_persistent(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11___boxed__const__1);
l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12___boxed__const__1 = _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12___boxed__const__1();
lean_mark_persistent(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12___boxed__const__1);
l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13___boxed__const__1 = _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13___boxed__const__1();
lean_mark_persistent(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13___boxed__const__1);
l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14___boxed__const__1 = _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14___boxed__const__1();
lean_mark_persistent(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14___boxed__const__1);
l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15___boxed__const__1 = _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15___boxed__const__1();
lean_mark_persistent(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15___boxed__const__1);
l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16___boxed__const__1 = _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16___boxed__const__1();
lean_mark_persistent(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16___boxed__const__1);
l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17___boxed__const__1 = _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17___boxed__const__1();
lean_mark_persistent(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17___boxed__const__1);
l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18___boxed__const__1 = _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18___boxed__const__1();
lean_mark_persistent(l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18___boxed__const__1);
l_System_Uri_UriEscape_rfc3986ReservedChars = _init_l_System_Uri_UriEscape_rfc3986ReservedChars();
lean_mark_persistent(l_System_Uri_UriEscape_rfc3986ReservedChars);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_System_Uri(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_FilePath(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_String_Length(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Combinators_Take(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_System_Uri(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Uri(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_System_Uri(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_System_Uri(builtin);
}
#ifdef __cplusplus
}
#endif
