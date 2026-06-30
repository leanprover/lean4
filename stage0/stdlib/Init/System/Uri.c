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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* l_String_Slice_positions(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
extern lean_object* l_ByteArray_empty;
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
uint8_t lean_uint8_add(uint8_t, uint8_t);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_unescapeUri(lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_unescapeUri___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__0 = (const lean_object*)&l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_30_; uint8_t v___x_31_; 
v___x_30_ = 48;
v___x_31_ = lean_uint8_dec_le(v___x_30_, v_c_7_);
if (v___x_31_ == 0)
{
goto v___jp_20_;
}
else
{
uint8_t v___x_32_; uint8_t v___x_33_; 
v___x_32_ = 57;
v___x_33_ = lean_uint8_dec_le(v_c_7_, v___x_32_);
if (v___x_33_ == 0)
{
goto v___jp_20_;
}
else
{
uint8_t v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_uint8_sub(v_c_7_, v___x_30_);
v___x_35_ = lean_box(v___x_34_);
v___x_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
return v___x_36_;
}
}
v___jp_8_:
{
uint8_t v___x_9_; uint8_t v___x_10_; 
v___x_9_ = 65;
v___x_10_ = lean_uint8_dec_le(v___x_9_, v_c_7_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
else
{
uint8_t v___x_12_; uint8_t v___x_13_; 
v___x_12_ = 70;
v___x_13_ = lean_uint8_dec_le(v_c_7_, v___x_12_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; 
v___x_14_ = lean_box(0);
return v___x_14_;
}
else
{
uint8_t v___x_15_; uint8_t v___x_16_; uint8_t v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_15_ = lean_uint8_sub(v_c_7_, v___x_9_);
v___x_16_ = 10;
v___x_17_ = lean_uint8_add(v___x_15_, v___x_16_);
v___x_18_ = lean_box(v___x_17_);
v___x_19_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
return v___x_19_;
}
}
}
v___jp_20_:
{
uint8_t v___x_21_; uint8_t v___x_22_; 
v___x_21_ = 97;
v___x_22_ = lean_uint8_dec_le(v___x_21_, v_c_7_);
if (v___x_22_ == 0)
{
goto v___jp_8_;
}
else
{
uint8_t v___x_23_; uint8_t v___x_24_; 
v___x_23_ = 102;
v___x_24_ = lean_uint8_dec_le(v_c_7_, v___x_23_);
if (v___x_24_ == 0)
{
goto v___jp_8_;
}
else
{
uint8_t v___x_25_; uint8_t v___x_26_; uint8_t v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_25_ = lean_uint8_sub(v_c_7_, v___x_21_);
v___x_26_ = 10;
v___x_27_ = lean_uint8_add(v___x_25_, v___x_26_);
v___x_28_ = lean_box(v___x_27_);
v___x_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f___boxed(lean_object* v_c_37_){
_start:
{
uint8_t v_c_boxed_38_; lean_object* v_res_39_; 
v_c_boxed_38_ = lean_unbox(v_c_37_);
v_res_39_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(v_c_boxed_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1(lean_object* v_msg_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = ((lean_object*)(l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0));
v___x_43_ = lean_panic_fn_borrowed(v___x_42_, v_msg_41_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___redArg(lean_object* v_len_44_, lean_object* v_rawBytes_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_fst_47_; lean_object* v_snd_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_106_; 
v_fst_47_ = lean_ctor_get(v_a_46_, 0);
v_snd_48_ = lean_ctor_get(v_a_46_, 1);
v_isSharedCheck_106_ = !lean_is_exclusive(v_a_46_);
if (v_isSharedCheck_106_ == 0)
{
v___x_50_ = v_a_46_;
v_isShared_51_ = v_isSharedCheck_106_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_snd_48_);
lean_inc(v_fst_47_);
lean_dec(v_a_46_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_106_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
uint8_t v___x_52_; 
v___x_52_ = lean_nat_dec_lt(v_snd_48_, v_len_44_);
if (v___x_52_ == 0)
{
lean_object* v___x_54_; 
if (v_isShared_51_ == 0)
{
v___x_54_ = v___x_50_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_fst_47_);
lean_ctor_set(v_reuseFailAlloc_55_, 1, v_snd_48_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
else
{
uint8_t v_percent_56_; uint8_t v___x_57_; uint8_t v___x_66_; 
v_percent_56_ = 37;
v___x_57_ = lean_byte_array_fget(v_rawBytes_45_, v_snd_48_);
v___x_66_ = lean_uint8_dec_eq(v___x_57_, v_percent_56_);
if (v___x_66_ == 0)
{
goto v___jp_58_;
}
else
{
lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_67_ = lean_unsigned_to_nat(1u);
v___x_68_ = lean_nat_add(v_snd_48_, v___x_67_);
v___x_69_ = lean_nat_dec_lt(v___x_68_, v_len_44_);
if (v___x_69_ == 0)
{
lean_dec(v___x_68_);
goto v___jp_58_;
}
else
{
uint8_t v___x_70_; lean_object* v___x_71_; 
lean_del_object(v___x_50_);
v___x_70_ = lean_byte_array_fget(v_rawBytes_45_, v___x_68_);
lean_dec(v___x_68_);
v___x_71_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(v___x_70_);
if (lean_obj_tag(v___x_71_) == 1)
{
lean_object* v_val_72_; lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; 
v_val_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc(v_val_72_);
lean_dec_ref_known(v___x_71_, 1);
v___x_73_ = lean_unsigned_to_nat(2u);
v___x_74_ = lean_nat_add(v_snd_48_, v___x_73_);
v___x_75_ = lean_nat_dec_lt(v___x_74_, v_len_44_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
lean_dec(v_val_72_);
lean_dec(v_snd_48_);
v___x_76_ = lean_byte_array_push(v_fst_47_, v___x_57_);
v___x_77_ = lean_byte_array_push(v___x_76_, v___x_70_);
v___x_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v___x_74_);
v_a_46_ = v___x_78_;
goto _start;
}
else
{
uint8_t v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_byte_array_fget(v_rawBytes_45_, v___x_74_);
lean_dec(v___x_74_);
v___x_81_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(v___x_80_);
if (lean_obj_tag(v___x_81_) == 1)
{
lean_object* v_val_82_; uint8_t v___x_83_; uint8_t v___x_84_; uint8_t v___x_85_; uint8_t v___x_86_; uint8_t v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v_val_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_val_82_);
lean_dec_ref_known(v___x_81_, 1);
v___x_83_ = 4;
v___x_84_ = lean_unbox(v_val_72_);
lean_dec(v_val_72_);
v___x_85_ = lean_uint8_shift_left(v___x_84_, v___x_83_);
v___x_86_ = lean_unbox(v_val_82_);
lean_dec(v_val_82_);
v___x_87_ = lean_uint8_add(v___x_85_, v___x_86_);
v___x_88_ = lean_byte_array_push(v_fst_47_, v___x_87_);
v___x_89_ = lean_unsigned_to_nat(3u);
v___x_90_ = lean_nat_add(v_snd_48_, v___x_89_);
lean_dec(v_snd_48_);
v___x_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_88_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v_a_46_ = v___x_91_;
goto _start;
}
else
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
lean_dec(v___x_81_);
lean_dec(v_val_72_);
v___x_93_ = lean_byte_array_push(v_fst_47_, v___x_57_);
v___x_94_ = lean_byte_array_push(v___x_93_, v___x_70_);
v___x_95_ = lean_byte_array_push(v___x_94_, v___x_80_);
v___x_96_ = lean_unsigned_to_nat(3u);
v___x_97_ = lean_nat_add(v_snd_48_, v___x_96_);
lean_dec(v_snd_48_);
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_95_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v_a_46_ = v___x_98_;
goto _start;
}
}
}
else
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
lean_dec(v___x_71_);
v___x_100_ = lean_byte_array_push(v_fst_47_, v___x_57_);
v___x_101_ = lean_byte_array_push(v___x_100_, v___x_70_);
v___x_102_ = lean_unsigned_to_nat(2u);
v___x_103_ = lean_nat_add(v_snd_48_, v___x_102_);
lean_dec(v_snd_48_);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_101_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v_a_46_ = v___x_104_;
goto _start;
}
}
}
v___jp_58_:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_63_; 
v___x_59_ = lean_byte_array_push(v_fst_47_, v___x_57_);
v___x_60_ = lean_unsigned_to_nat(1u);
v___x_61_ = lean_nat_add(v_snd_48_, v___x_60_);
lean_dec(v_snd_48_);
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 1, v___x_61_);
lean_ctor_set(v___x_50_, 0, v___x_59_);
v___x_63_ = v___x_50_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_59_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v___x_61_);
v___x_63_ = v_reuseFailAlloc_65_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
v_a_46_ = v___x_63_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___redArg___boxed(lean_object* v_len_107_, lean_object* v_rawBytes_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___redArg(v_len_107_, v_rawBytes_108_, v_a_109_);
lean_dec_ref(v_rawBytes_108_);
lean_dec(v_len_107_);
return v_res_110_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_decodeUri___closed__0(void){
_start:
{
lean_object* v_i_111_; lean_object* v_decoded_112_; lean_object* v___x_113_; 
v_i_111_ = lean_unsigned_to_nat(0u);
v_decoded_112_ = l_ByteArray_empty;
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v_decoded_112_);
lean_ctor_set(v___x_113_, 1, v_i_111_);
return v___x_113_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_decodeUri___closed__4(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_117_ = ((lean_object*)(l_System_Uri_UriEscape_decodeUri___closed__3));
v___x_118_ = lean_unsigned_to_nat(46u);
v___x_119_ = lean_unsigned_to_nat(193u);
v___x_120_ = ((lean_object*)(l_System_Uri_UriEscape_decodeUri___closed__2));
v___x_121_ = ((lean_object*)(l_System_Uri_UriEscape_decodeUri___closed__1));
v___x_122_ = l_mkPanicMessageWithDecl(v___x_121_, v___x_120_, v___x_119_, v___x_118_, v___x_117_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_decodeUri(lean_object* v_uri_123_){
_start:
{
lean_object* v_rawBytes_124_; lean_object* v_len_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v_fst_128_; uint8_t v___x_129_; 
v_rawBytes_124_ = lean_string_to_utf8(v_uri_123_);
v_len_125_ = lean_byte_array_size(v_rawBytes_124_);
v___x_126_ = lean_obj_once(&l_System_Uri_UriEscape_decodeUri___closed__0, &l_System_Uri_UriEscape_decodeUri___closed__0_once, _init_l_System_Uri_UriEscape_decodeUri___closed__0);
v___x_127_ = l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___redArg(v_len_125_, v_rawBytes_124_, v___x_126_);
lean_dec_ref(v_rawBytes_124_);
v_fst_128_ = lean_ctor_get(v___x_127_, 0);
lean_inc(v_fst_128_);
lean_dec_ref(v___x_127_);
v___x_129_ = lean_string_validate_utf8(v_fst_128_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; 
lean_dec(v_fst_128_);
v___x_130_ = lean_obj_once(&l_System_Uri_UriEscape_decodeUri___closed__4, &l_System_Uri_UriEscape_decodeUri___closed__4_once, _init_l_System_Uri_UriEscape_decodeUri___closed__4);
v___x_131_ = l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1(v___x_130_);
return v___x_131_;
}
else
{
lean_object* v___x_132_; 
v___x_132_ = lean_string_from_utf8_unchecked(v_fst_128_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_decodeUri___boxed(lean_object* v_uri_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_System_Uri_UriEscape_decodeUri(v_uri_133_);
lean_dec_ref(v_uri_133_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0(lean_object* v_len_135_, lean_object* v_rawBytes_136_, lean_object* v_inst_137_, lean_object* v_a_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___redArg(v_len_135_, v_rawBytes_136_, v_a_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___boxed(lean_object* v_len_140_, lean_object* v_rawBytes_141_, lean_object* v_inst_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0(v_len_140_, v_rawBytes_141_, v_inst_142_, v_a_143_);
lean_dec_ref(v_rawBytes_141_);
lean_dec(v_len_140_);
return v_res_144_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_145_; lean_object* v___x_146_; 
v___x_145_ = 32;
v___x_146_ = lean_box_uint32(v___x_145_);
return v___x_146_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = lean_box(0);
v___x_148_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0___boxed__const__1;
v___x_149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v___x_147_);
return v___x_149_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_150_; lean_object* v___x_151_; 
v___x_150_ = 37;
v___x_151_ = lean_box_uint32(v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0);
v___x_153_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1___boxed__const__1;
v___x_154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v___x_152_);
return v___x_154_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_155_; lean_object* v___x_156_; 
v___x_155_ = 42;
v___x_156_ = lean_box_uint32(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1);
v___x_158_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2___boxed__const__1;
v___x_159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_160_; lean_object* v___x_161_; 
v___x_160_ = 41;
v___x_161_ = lean_box_uint32(v___x_160_);
return v___x_161_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2);
v___x_163_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3___boxed__const__1;
v___x_164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_162_);
return v___x_164_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4___boxed__const__1(void){
_start:
{
uint32_t v___x_165_; lean_object* v___x_166_; 
v___x_165_ = 40;
v___x_166_ = lean_box_uint32(v___x_165_);
return v___x_166_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3);
v___x_168_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4___boxed__const__1;
v___x_169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v___x_167_);
return v___x_169_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5___boxed__const__1(void){
_start:
{
uint32_t v___x_170_; lean_object* v___x_171_; 
v___x_170_ = 39;
v___x_171_ = lean_box_uint32(v___x_170_);
return v___x_171_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4);
v___x_173_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5___boxed__const__1;
v___x_174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v___x_172_);
return v___x_174_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6___boxed__const__1(void){
_start:
{
uint32_t v___x_175_; lean_object* v___x_176_; 
v___x_175_ = 33;
v___x_176_ = lean_box_uint32(v___x_175_);
return v___x_176_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5);
v___x_178_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6___boxed__const__1;
v___x_179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v___x_177_);
return v___x_179_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7___boxed__const__1(void){
_start:
{
uint32_t v___x_180_; lean_object* v___x_181_; 
v___x_180_ = 44;
v___x_181_ = lean_box_uint32(v___x_180_);
return v___x_181_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6);
v___x_183_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7___boxed__const__1;
v___x_184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v___x_182_);
return v___x_184_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8___boxed__const__1(void){
_start:
{
uint32_t v___x_185_; lean_object* v___x_186_; 
v___x_185_ = 36;
v___x_186_ = lean_box_uint32(v___x_185_);
return v___x_186_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_187_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7);
v___x_188_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8___boxed__const__1;
v___x_189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v___x_187_);
return v___x_189_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9___boxed__const__1(void){
_start:
{
uint32_t v___x_190_; lean_object* v___x_191_; 
v___x_190_ = 43;
v___x_191_ = lean_box_uint32(v___x_190_);
return v___x_191_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8);
v___x_193_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9___boxed__const__1;
v___x_194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v___x_192_);
return v___x_194_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10___boxed__const__1(void){
_start:
{
uint32_t v___x_195_; lean_object* v___x_196_; 
v___x_195_ = 61;
v___x_196_ = lean_box_uint32(v___x_195_);
return v___x_196_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9);
v___x_198_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10___boxed__const__1;
v___x_199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_197_);
return v___x_199_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11___boxed__const__1(void){
_start:
{
uint32_t v___x_200_; lean_object* v___x_201_; 
v___x_200_ = 38;
v___x_201_ = lean_box_uint32(v___x_200_);
return v___x_201_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10);
v___x_203_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11___boxed__const__1;
v___x_204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v___x_202_);
return v___x_204_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12___boxed__const__1(void){
_start:
{
uint32_t v___x_205_; lean_object* v___x_206_; 
v___x_205_ = 64;
v___x_206_ = lean_box_uint32(v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11);
v___x_208_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12___boxed__const__1;
v___x_209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
lean_ctor_set(v___x_209_, 1, v___x_207_);
return v___x_209_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13___boxed__const__1(void){
_start:
{
uint32_t v___x_210_; lean_object* v___x_211_; 
v___x_210_ = 93;
v___x_211_ = lean_box_uint32(v___x_210_);
return v___x_211_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12);
v___x_213_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13___boxed__const__1;
v___x_214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v___x_212_);
return v___x_214_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14___boxed__const__1(void){
_start:
{
uint32_t v___x_215_; lean_object* v___x_216_; 
v___x_215_ = 91;
v___x_216_ = lean_box_uint32(v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_217_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13);
v___x_218_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14___boxed__const__1;
v___x_219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v___x_217_);
return v___x_219_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15___boxed__const__1(void){
_start:
{
uint32_t v___x_220_; lean_object* v___x_221_; 
v___x_220_ = 35;
v___x_221_ = lean_box_uint32(v___x_220_);
return v___x_221_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14);
v___x_223_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15___boxed__const__1;
v___x_224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v___x_222_);
return v___x_224_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16___boxed__const__1(void){
_start:
{
uint32_t v___x_225_; lean_object* v___x_226_; 
v___x_225_ = 63;
v___x_226_ = lean_box_uint32(v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_227_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15);
v___x_228_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16___boxed__const__1;
v___x_229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v___x_227_);
return v___x_229_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17___boxed__const__1(void){
_start:
{
uint32_t v___x_230_; lean_object* v___x_231_; 
v___x_230_ = 58;
v___x_231_ = lean_box_uint32(v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_232_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16);
v___x_233_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17___boxed__const__1;
v___x_234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set(v___x_234_, 1, v___x_232_);
return v___x_234_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18___boxed__const__1(void){
_start:
{
uint32_t v___x_235_; lean_object* v___x_236_; 
v___x_235_ = 59;
v___x_236_ = lean_box_uint32(v___x_235_);
return v___x_236_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17);
v___x_238_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18___boxed__const__1;
v___x_239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___x_237_);
return v___x_239_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars(void){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex_spec__0(lean_object* v_s_241_, lean_object* v_p_242_){
_start:
{
uint32_t v___y_244_; lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = lean_string_utf8_byte_size(v_s_241_);
v___x_250_ = lean_nat_dec_eq(v_p_242_, v___x_249_);
if (v___x_250_ == 0)
{
uint32_t v___x_251_; uint32_t v___x_252_; uint8_t v___x_253_; 
v___x_251_ = lean_string_utf8_get_fast(v_s_241_, v_p_242_);
v___x_252_ = 97;
v___x_253_ = lean_uint32_dec_le(v___x_252_, v___x_251_);
if (v___x_253_ == 0)
{
v___y_244_ = v___x_251_;
goto v___jp_243_;
}
else
{
uint32_t v___x_254_; uint8_t v___x_255_; 
v___x_254_ = 122;
v___x_255_ = lean_uint32_dec_le(v___x_251_, v___x_254_);
if (v___x_255_ == 0)
{
v___y_244_ = v___x_251_;
goto v___jp_243_;
}
else
{
uint32_t v___x_256_; uint32_t v___x_257_; 
v___x_256_ = 4294967264;
v___x_257_ = lean_uint32_add(v___x_251_, v___x_256_);
v___y_244_ = v___x_257_;
goto v___jp_243_;
}
}
}
else
{
lean_dec(v_p_242_);
return v_s_241_;
}
v___jp_243_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
lean_inc(v_p_242_);
v___x_245_ = lean_string_utf8_set(v_s_241_, v_p_242_, v___y_244_);
v___x_246_ = l_Char_utf8Size(v___y_244_);
v___x_247_ = lean_nat_add(v_p_242_, v___x_246_);
lean_dec(v___x_246_);
lean_dec(v_p_242_);
v_s_241_ = v___x_245_;
v_p_242_ = v___x_247_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(uint8_t v_c_258_){
_start:
{
uint8_t v___x_259_; uint8_t v___x_260_; uint8_t v_d2_261_; uint8_t v_d1_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_259_ = 16;
v___x_260_ = 4;
v_d2_261_ = lean_uint8_shift_right(v_c_258_, v___x_260_);
v_d1_262_ = lean_uint8_mod(v_c_258_, v___x_259_);
v___x_263_ = lean_uint8_to_nat(v_d2_261_);
v___x_264_ = l_hexDigitRepr(v___x_263_);
v___x_265_ = lean_uint8_to_nat(v_d1_262_);
v___x_266_ = l_hexDigitRepr(v___x_265_);
v___x_267_ = lean_string_append(v___x_264_, v___x_266_);
lean_dec_ref(v___x_266_);
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = l_String_mapAux___at___00__private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex_spec__0(v___x_267_, v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex___boxed(lean_object* v_c_270_){
_start:
{
uint8_t v_c_boxed_271_; lean_object* v_res_272_; 
v_c_boxed_271_ = lean_unbox(v_c_270_);
v_res_272_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(v_c_boxed_271_);
return v_res_272_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1(uint32_t v_a_273_, lean_object* v_x_274_){
_start:
{
if (lean_obj_tag(v_x_274_) == 0)
{
uint8_t v___x_275_; 
v___x_275_ = 0;
return v___x_275_;
}
else
{
lean_object* v_head_276_; lean_object* v_tail_277_; uint32_t v___x_278_; uint8_t v___x_279_; 
v_head_276_ = lean_ctor_get(v_x_274_, 0);
v_tail_277_ = lean_ctor_get(v_x_274_, 1);
v___x_278_ = lean_unbox_uint32(v_head_276_);
v___x_279_ = lean_uint32_dec_eq(v_a_273_, v___x_278_);
if (v___x_279_ == 0)
{
v_x_274_ = v_tail_277_;
goto _start;
}
else
{
return v___x_279_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1___boxed(lean_object* v_a_281_, lean_object* v_x_282_){
_start:
{
uint32_t v_a_boxed_283_; uint8_t v_res_284_; lean_object* v_r_285_; 
v_a_boxed_283_ = lean_unbox_uint32(v_a_281_);
lean_dec(v_a_281_);
v_res_284_ = l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1(v_a_boxed_283_, v_x_282_);
lean_dec(v_x_282_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(lean_object* v_as_287_, size_t v_i_288_, size_t v_stop_289_, lean_object* v_b_290_){
_start:
{
uint8_t v___x_291_; 
v___x_291_ = lean_usize_dec_eq(v_i_288_, v_stop_289_);
if (v___x_291_ == 0)
{
uint8_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; size_t v___x_297_; size_t v___x_298_; 
v___x_292_ = lean_byte_array_uget(v_as_287_, v_i_288_);
v___x_293_ = ((lean_object*)(l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___closed__0));
v___x_294_ = lean_string_append(v_b_290_, v___x_293_);
v___x_295_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(v___x_292_);
v___x_296_ = lean_string_append(v___x_294_, v___x_295_);
lean_dec_ref(v___x_295_);
v___x_297_ = ((size_t)1ULL);
v___x_298_ = lean_usize_add(v_i_288_, v___x_297_);
v_i_288_ = v___x_298_;
v_b_290_ = v___x_296_;
goto _start;
}
else
{
return v_b_290_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___boxed(lean_object* v_as_300_, lean_object* v_i_301_, lean_object* v_stop_302_, lean_object* v_b_303_){
_start:
{
size_t v_i_boxed_304_; size_t v_stop_boxed_305_; lean_object* v_res_306_; 
v_i_boxed_304_ = lean_unbox_usize(v_i_301_);
lean_dec(v_i_301_);
v_stop_boxed_305_ = lean_unbox_usize(v_stop_302_);
lean_dec(v_stop_302_);
v_res_306_ = l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(v_as_300_, v_i_boxed_304_, v_stop_boxed_305_, v_b_303_);
lean_dec_ref(v_as_300_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_uriEscapeAsciiChar(uint32_t v_c_307_){
_start:
{
uint8_t v___y_309_; lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = l_System_Uri_UriEscape_rfc3986ReservedChars;
v___x_334_ = l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1(v_c_307_, v___x_333_);
if (v___x_334_ == 0)
{
uint32_t v___x_335_; uint8_t v___x_336_; 
v___x_335_ = 32;
v___x_336_ = lean_uint32_dec_lt(v_c_307_, v___x_335_);
v___y_309_ = v___x_336_;
goto v___jp_308_;
}
else
{
v___y_309_ = v___x_334_;
goto v___jp_308_;
}
v___jp_308_:
{
if (v___y_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_310_ = lean_uint32_to_nat(v_c_307_);
v___x_311_ = lean_unsigned_to_nat(127u);
v___x_312_ = lean_nat_dec_lt(v___x_310_, v___x_311_);
lean_dec(v___x_310_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_313_ = ((lean_object*)(l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0));
v___x_314_ = lean_string_push(v___x_313_, v_c_307_);
v___x_315_ = lean_string_to_utf8(v___x_314_);
lean_dec_ref(v___x_314_);
v___x_316_ = lean_unsigned_to_nat(0u);
v___x_317_ = lean_byte_array_size(v___x_315_);
v___x_318_ = lean_nat_dec_lt(v___x_316_, v___x_317_);
if (v___x_318_ == 0)
{
lean_dec_ref(v___x_315_);
return v___x_313_;
}
else
{
uint8_t v___x_319_; 
v___x_319_ = lean_nat_dec_le(v___x_317_, v___x_317_);
if (v___x_319_ == 0)
{
if (v___x_318_ == 0)
{
lean_dec_ref(v___x_315_);
return v___x_313_;
}
else
{
size_t v___x_320_; size_t v___x_321_; lean_object* v___x_322_; 
v___x_320_ = ((size_t)0ULL);
v___x_321_ = lean_usize_of_nat(v___x_317_);
v___x_322_ = l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(v___x_315_, v___x_320_, v___x_321_, v___x_313_);
lean_dec_ref(v___x_315_);
return v___x_322_;
}
}
else
{
size_t v___x_323_; size_t v___x_324_; lean_object* v___x_325_; 
v___x_323_ = ((size_t)0ULL);
v___x_324_ = lean_usize_of_nat(v___x_317_);
v___x_325_ = l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(v___x_315_, v___x_323_, v___x_324_, v___x_313_);
lean_dec_ref(v___x_315_);
return v___x_325_;
}
}
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = ((lean_object*)(l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0));
v___x_327_ = lean_string_push(v___x_326_, v_c_307_);
return v___x_327_;
}
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_328_ = ((lean_object*)(l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___closed__0));
v___x_329_ = lean_uint32_to_nat(v_c_307_);
v___x_330_ = lean_uint8_of_nat(v___x_329_);
lean_dec(v___x_329_);
v___x_331_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(v___x_330_);
v___x_332_ = lean_string_append(v___x_328_, v___x_331_);
lean_dec_ref(v___x_331_);
return v___x_332_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_uriEscapeAsciiChar___boxed(lean_object* v_c_337_){
_start:
{
uint32_t v_c_boxed_338_; lean_object* v_res_339_; 
v_c_boxed_338_ = lean_unbox_uint32(v_c_337_);
lean_dec(v_c_337_);
v_res_339_ = l_System_Uri_UriEscape_uriEscapeAsciiChar(v_c_boxed_338_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(lean_object* v___x_340_, lean_object* v_uri_341_, lean_object* v_a_342_, lean_object* v_b_343_){
_start:
{
lean_object* v_startInclusive_344_; lean_object* v_endExclusive_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v_startInclusive_344_ = lean_ctor_get(v___x_340_, 1);
v_endExclusive_345_ = lean_ctor_get(v___x_340_, 2);
v___x_346_ = lean_nat_sub(v_endExclusive_345_, v_startInclusive_344_);
v___x_347_ = lean_nat_dec_eq(v_a_342_, v___x_346_);
lean_dec(v___x_346_);
if (v___x_347_ == 0)
{
uint32_t v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_348_ = lean_string_utf8_get_fast(v_uri_341_, v_a_342_);
v___x_349_ = lean_string_utf8_next_fast(v_uri_341_, v_a_342_);
lean_dec(v_a_342_);
v___x_350_ = l_System_Uri_UriEscape_uriEscapeAsciiChar(v___x_348_);
v___x_351_ = lean_string_append(v_b_343_, v___x_350_);
lean_dec_ref(v___x_350_);
v_a_342_ = v___x_349_;
v_b_343_ = v___x_351_;
goto _start;
}
else
{
lean_dec(v_a_342_);
return v_b_343_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg___boxed(lean_object* v___x_353_, lean_object* v_uri_354_, lean_object* v_a_355_, lean_object* v_b_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(v___x_353_, v_uri_354_, v_a_355_, v_b_356_);
lean_dec_ref(v_uri_354_);
lean_dec_ref(v___x_353_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_escapeUri(lean_object* v_uri_358_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_359_ = ((lean_object*)(l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0));
v___x_360_ = lean_unsigned_to_nat(0u);
v___x_361_ = lean_string_utf8_byte_size(v_uri_358_);
lean_inc_ref(v_uri_358_);
v___x_362_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_362_, 0, v_uri_358_);
lean_ctor_set(v___x_362_, 1, v___x_360_);
lean_ctor_set(v___x_362_, 2, v___x_361_);
v___x_363_ = l_String_Slice_positions(v___x_362_);
v___x_364_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(v___x_362_, v_uri_358_, v___x_363_, v___x_359_);
lean_dec_ref(v_uri_358_);
lean_dec_ref_known(v___x_362_, 3);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0(lean_object* v___x_365_, lean_object* v_uri_366_, lean_object* v_inst_367_, lean_object* v_R_368_, lean_object* v_a_369_, lean_object* v_b_370_, lean_object* v_c_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(v___x_365_, v_uri_366_, v_a_369_, v_b_370_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___boxed(lean_object* v___x_373_, lean_object* v_uri_374_, lean_object* v_inst_375_, lean_object* v_R_376_, lean_object* v_a_377_, lean_object* v_b_378_, lean_object* v_c_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0(v___x_373_, v_uri_374_, v_inst_375_, v_R_376_, v_a_377_, v_b_378_, v_c_379_);
lean_dec_ref(v_uri_374_);
lean_dec_ref(v___x_373_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_unescapeUri(lean_object* v_s_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_System_Uri_UriEscape_decodeUri(v_s_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_unescapeUri___boxed(lean_object* v_s_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_System_Uri_unescapeUri(v_s_383_);
lean_dec_ref(v_s_383_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg(lean_object* v___x_385_, lean_object* v_uri_386_, lean_object* v_a_387_, lean_object* v_b_388_){
_start:
{
lean_object* v_countdown_389_; lean_object* v_inner_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_409_; 
v_countdown_389_ = lean_ctor_get(v_a_387_, 0);
v_inner_390_ = lean_ctor_get(v_a_387_, 1);
v_isSharedCheck_409_ = !lean_is_exclusive(v_a_387_);
if (v_isSharedCheck_409_ == 0)
{
v___x_392_ = v_a_387_;
v_isShared_393_ = v_isSharedCheck_409_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_inner_390_);
lean_inc(v_countdown_389_);
lean_dec(v_a_387_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_409_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = lean_unsigned_to_nat(1u);
v___x_395_ = lean_nat_dec_eq(v_countdown_389_, v___x_394_);
if (v___x_395_ == 0)
{
lean_object* v_startInclusive_396_; lean_object* v_endExclusive_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v_startInclusive_396_ = lean_ctor_get(v___x_385_, 1);
v_endExclusive_397_ = lean_ctor_get(v___x_385_, 2);
v___x_398_ = lean_nat_sub(v_endExclusive_397_, v_startInclusive_396_);
v___x_399_ = lean_nat_dec_eq(v_inner_390_, v___x_398_);
lean_dec(v___x_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; uint32_t v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_400_ = lean_string_utf8_next_fast(v_uri_386_, v_inner_390_);
v___x_401_ = lean_string_utf8_get_fast(v_uri_386_, v_inner_390_);
lean_dec(v_inner_390_);
v___x_402_ = lean_nat_sub(v_countdown_389_, v___x_394_);
lean_dec(v_countdown_389_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 1, v___x_400_);
lean_ctor_set(v___x_392_, 0, v___x_402_);
v___x_404_ = v___x_392_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v___x_400_);
v___x_404_ = v_reuseFailAlloc_408_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_box_uint32(v___x_401_);
v___x_406_ = lean_array_push(v_b_388_, v___x_405_);
v_a_387_ = v___x_404_;
v_b_388_ = v___x_406_;
goto _start;
}
}
else
{
lean_del_object(v___x_392_);
lean_dec(v_inner_390_);
lean_dec(v_countdown_389_);
return v_b_388_;
}
}
else
{
lean_del_object(v___x_392_);
lean_dec(v_inner_390_);
lean_dec(v_countdown_389_);
return v_b_388_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg___boxed(lean_object* v___x_410_, lean_object* v_uri_411_, lean_object* v_a_412_, lean_object* v_b_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg(v___x_410_, v_uri_411_, v_a_412_, v_b_413_);
lean_dec_ref(v_uri_411_);
lean_dec_ref(v___x_410_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter(lean_object* v_uri_417_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = lean_string_utf8_byte_size(v_uri_417_);
lean_inc_ref(v_uri_417_);
v___x_420_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_420_, 0, v_uri_417_);
lean_ctor_set(v___x_420_, 1, v___x_418_);
lean_ctor_set(v___x_420_, 2, v___x_419_);
v___x_421_ = l_String_Slice_positions(v___x_420_);
v___x_422_ = lean_unsigned_to_nat(3u);
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___x_421_);
v___x_424_ = ((lean_object*)(l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__0));
v___x_425_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg(v___x_420_, v_uri_417_, v___x_423_, v___x_424_);
lean_dec_ref_known(v___x_420_, 3);
v___x_426_ = lean_array_to_list(v___x_425_);
if (lean_obj_tag(v___x_426_) == 1)
{
lean_object* v_tail_427_; 
v_tail_427_ = lean_ctor_get(v___x_426_, 1);
lean_inc(v_tail_427_);
if (lean_obj_tag(v_tail_427_) == 1)
{
lean_object* v_head_428_; lean_object* v_head_429_; lean_object* v_tail_430_; uint32_t v___x_431_; uint32_t v___x_432_; uint8_t v___x_433_; 
v_head_428_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_head_428_);
lean_dec_ref_known(v___x_426_, 2);
v_head_429_ = lean_ctor_get(v_tail_427_, 0);
lean_inc(v_head_429_);
v_tail_430_ = lean_ctor_get(v_tail_427_, 1);
lean_inc(v_tail_430_);
lean_dec_ref_known(v_tail_427_, 2);
v___x_431_ = 58;
v___x_432_ = lean_unbox_uint32(v_head_429_);
lean_dec(v_head_429_);
v___x_433_ = lean_uint32_dec_eq(v___x_432_, v___x_431_);
if (v___x_433_ == 0)
{
lean_dec(v_tail_430_);
lean_dec(v_head_428_);
return v_uri_417_;
}
else
{
if (lean_obj_tag(v_tail_430_) == 0)
{
uint32_t v___x_434_; uint32_t v___x_435_; uint8_t v___x_436_; 
v___x_434_ = 65;
v___x_435_ = lean_unbox_uint32(v_head_428_);
v___x_436_ = lean_uint32_dec_le(v___x_434_, v___x_435_);
if (v___x_436_ == 0)
{
lean_dec(v_head_428_);
return v_uri_417_;
}
else
{
uint32_t v___x_437_; uint32_t v___x_438_; uint8_t v___x_439_; 
v___x_437_ = 90;
v___x_438_ = lean_unbox_uint32(v_head_428_);
lean_dec(v_head_428_);
v___x_439_ = lean_uint32_dec_le(v___x_438_, v___x_437_);
if (v___x_439_ == 0)
{
return v_uri_417_;
}
else
{
uint32_t v___x_440_; uint8_t v___x_441_; 
v___x_440_ = lean_string_utf8_get(v_uri_417_, v___x_418_);
v___x_441_ = lean_uint32_dec_le(v___x_434_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; 
v___x_442_ = lean_string_utf8_set(v_uri_417_, v___x_418_, v___x_440_);
return v___x_442_;
}
else
{
uint8_t v___x_443_; 
v___x_443_ = lean_uint32_dec_le(v___x_440_, v___x_437_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; 
v___x_444_ = lean_string_utf8_set(v_uri_417_, v___x_418_, v___x_440_);
return v___x_444_;
}
else
{
uint32_t v___x_445_; uint32_t v___x_446_; lean_object* v___x_447_; 
v___x_445_ = 32;
v___x_446_ = lean_uint32_add(v___x_440_, v___x_445_);
v___x_447_ = lean_string_utf8_set(v_uri_417_, v___x_418_, v___x_446_);
return v___x_447_;
}
}
}
}
}
else
{
lean_dec(v_tail_430_);
lean_dec(v_head_428_);
return v_uri_417_;
}
}
}
else
{
lean_dec_ref_known(v___x_426_, 2);
lean_dec(v_tail_427_);
return v_uri_417_;
}
}
else
{
lean_dec(v___x_426_);
return v_uri_417_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0(lean_object* v___x_448_, lean_object* v_uri_449_, lean_object* v_inst_450_, lean_object* v_R_451_, lean_object* v_a_452_, lean_object* v_b_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg(v___x_448_, v_uri_449_, v_a_452_, v_b_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___boxed(lean_object* v___x_455_, lean_object* v_uri_456_, lean_object* v_inst_457_, lean_object* v_R_458_, lean_object* v_a_459_, lean_object* v_b_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0(v___x_455_, v_uri_456_, v_inst_457_, v_R_458_, v_a_459_, v_b_460_);
lean_dec_ref(v_uri_456_);
lean_dec_ref(v___x_455_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_Uri_pathToUri_spec__0(lean_object* v_s_462_, lean_object* v_p_463_){
_start:
{
uint32_t v___y_465_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = lean_string_utf8_byte_size(v_s_462_);
v___x_471_ = lean_nat_dec_eq(v_p_463_, v___x_470_);
if (v___x_471_ == 0)
{
uint32_t v___x_472_; uint32_t v___x_473_; uint8_t v___x_474_; 
v___x_472_ = lean_string_utf8_get_fast(v_s_462_, v_p_463_);
v___x_473_ = 92;
v___x_474_ = lean_uint32_dec_eq(v___x_472_, v___x_473_);
if (v___x_474_ == 0)
{
v___y_465_ = v___x_472_;
goto v___jp_464_;
}
else
{
uint32_t v___x_475_; 
v___x_475_ = 47;
v___y_465_ = v___x_475_;
goto v___jp_464_;
}
}
else
{
lean_dec(v_p_463_);
return v_s_462_;
}
v___jp_464_:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
lean_inc(v_p_463_);
v___x_466_ = lean_string_utf8_set(v_s_462_, v_p_463_, v___y_465_);
v___x_467_ = l_Char_utf8Size(v___y_465_);
v___x_468_ = lean_nat_add(v_p_463_, v___x_467_);
lean_dec(v___x_467_);
lean_dec(v_p_463_);
v_s_462_ = v___x_466_;
v_p_463_ = v___x_468_;
goto _start;
}
}
}
static lean_object* _init_l_System_Uri_pathToUri___closed__2(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = ((lean_object*)(l_System_Uri_pathToUri___closed__1));
v___x_479_ = lean_string_utf8_byte_size(v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_pathToUri(lean_object* v_fname_481_){
_start:
{
lean_object* v___y_483_; lean_object* v_uri_487_; lean_object* v_uri_501_; uint8_t v___x_502_; 
v_uri_501_ = l_System_FilePath_normalize(v_fname_481_);
v___x_502_ = l_System_Platform_isWindows;
if (v___x_502_ == 0)
{
v_uri_487_ = v_uri_501_;
goto v___jp_486_;
}
else
{
lean_object* v_uri_503_; lean_object* v___x_504_; lean_object* v_uri_505_; 
v_uri_503_ = l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter(v_uri_501_);
v___x_504_ = lean_unsigned_to_nat(0u);
v_uri_505_ = l_String_mapAux___at___00System_Uri_pathToUri_spec__0(v_uri_503_, v___x_504_);
v_uri_487_ = v_uri_505_;
goto v___jp_486_;
}
v___jp_482_:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = ((lean_object*)(l_System_Uri_pathToUri___closed__0));
v___x_485_ = lean_string_append(v___x_484_, v___y_483_);
lean_dec_ref(v___y_483_);
return v___x_485_;
}
v___jp_486_:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v_uri_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_488_ = ((lean_object*)(l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0));
v___x_489_ = lean_unsigned_to_nat(0u);
v___x_490_ = lean_string_utf8_byte_size(v_uri_487_);
lean_inc_ref(v_uri_487_);
v___x_491_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_491_, 0, v_uri_487_);
lean_ctor_set(v___x_491_, 1, v___x_489_);
lean_ctor_set(v___x_491_, 2, v___x_490_);
v___x_492_ = l_String_Slice_positions(v___x_491_);
v_uri_493_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(v___x_491_, v_uri_487_, v___x_492_, v___x_488_);
lean_dec_ref(v_uri_487_);
lean_dec_ref_known(v___x_491_, 3);
v___x_494_ = ((lean_object*)(l_System_Uri_pathToUri___closed__1));
v___x_495_ = lean_string_utf8_byte_size(v_uri_493_);
v___x_496_ = lean_obj_once(&l_System_Uri_pathToUri___closed__2, &l_System_Uri_pathToUri___closed__2_once, _init_l_System_Uri_pathToUri___closed__2);
v___x_497_ = lean_nat_dec_le(v___x_496_, v___x_495_);
if (v___x_497_ == 0)
{
v___y_483_ = v_uri_493_;
goto v___jp_482_;
}
else
{
uint8_t v___x_498_; 
v___x_498_ = lean_string_memcmp(v_uri_493_, v___x_494_, v___x_489_, v___x_489_, v___x_496_);
if (v___x_498_ == 0)
{
v___y_483_ = v_uri_493_;
goto v___jp_482_;
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = ((lean_object*)(l_System_Uri_pathToUri___closed__3));
v___x_500_ = lean_string_append(v___x_499_, v_uri_493_);
lean_dec_ref(v_uri_493_);
return v___x_500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg(lean_object* v_p_506_, lean_object* v_a_507_, lean_object* v_b_508_){
_start:
{
lean_object* v_countdown_509_; lean_object* v_inner_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_532_; 
v_countdown_509_ = lean_ctor_get(v_a_507_, 0);
v_inner_510_ = lean_ctor_get(v_a_507_, 1);
v_isSharedCheck_532_ = !lean_is_exclusive(v_a_507_);
if (v_isSharedCheck_532_ == 0)
{
v___x_512_ = v_a_507_;
v_isShared_513_ = v_isSharedCheck_532_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_inner_510_);
lean_inc(v_countdown_509_);
lean_dec(v_a_507_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_532_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_514_ = lean_unsigned_to_nat(1u);
v___x_515_ = lean_nat_dec_eq(v_countdown_509_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v_str_516_; lean_object* v_startInclusive_517_; lean_object* v_endExclusive_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v_str_516_ = lean_ctor_get(v_p_506_, 0);
v_startInclusive_517_ = lean_ctor_get(v_p_506_, 1);
v_endExclusive_518_ = lean_ctor_get(v_p_506_, 2);
v___x_519_ = lean_nat_sub(v_endExclusive_518_, v_startInclusive_517_);
v___x_520_ = lean_nat_dec_eq(v_inner_510_, v___x_519_);
lean_dec(v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; uint32_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_521_ = lean_nat_add(v_startInclusive_517_, v_inner_510_);
lean_dec(v_inner_510_);
v___x_522_ = lean_string_utf8_next_fast(v_str_516_, v___x_521_);
v___x_523_ = lean_nat_sub(v___x_522_, v_startInclusive_517_);
v___x_524_ = lean_string_utf8_get_fast(v_str_516_, v___x_521_);
lean_dec(v___x_521_);
v___x_525_ = lean_nat_sub(v_countdown_509_, v___x_514_);
lean_dec(v_countdown_509_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 1, v___x_523_);
lean_ctor_set(v___x_512_, 0, v___x_525_);
v___x_527_ = v___x_512_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_525_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v___x_523_);
v___x_527_ = v_reuseFailAlloc_531_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_box_uint32(v___x_524_);
v___x_529_ = lean_array_push(v_b_508_, v___x_528_);
v_a_507_ = v___x_527_;
v_b_508_ = v___x_529_;
goto _start;
}
}
else
{
lean_del_object(v___x_512_);
lean_dec(v_inner_510_);
lean_dec(v_countdown_509_);
return v_b_508_;
}
}
else
{
lean_del_object(v___x_512_);
lean_dec(v_inner_510_);
lean_dec(v_countdown_509_);
return v_b_508_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg___boxed(lean_object* v_p_533_, lean_object* v_a_534_, lean_object* v_b_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg(v_p_533_, v_a_534_, v_b_535_);
lean_dec_ref(v_p_533_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression(lean_object* v_p_537_){
_start:
{
uint8_t v___y_558_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_568_ = l_String_Slice_positions(v_p_537_);
v___x_569_ = lean_unsigned_to_nat(4u);
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
lean_ctor_set(v___x_570_, 1, v___x_568_);
v___x_571_ = ((lean_object*)(l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__0));
v___x_572_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg(v_p_537_, v___x_570_, v___x_571_);
v___x_573_ = lean_array_to_list(v___x_572_);
if (lean_obj_tag(v___x_573_) == 1)
{
lean_object* v_head_574_; lean_object* v_tail_575_; uint32_t v___x_576_; uint32_t v___x_577_; uint8_t v___x_578_; 
v_head_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_head_574_);
v_tail_575_ = lean_ctor_get(v___x_573_, 1);
lean_inc(v_tail_575_);
lean_dec_ref_known(v___x_573_, 2);
v___x_576_ = 47;
v___x_577_ = lean_unbox_uint32(v_head_574_);
lean_dec(v_head_574_);
v___x_578_ = lean_uint32_dec_eq(v___x_577_, v___x_576_);
if (v___x_578_ == 0)
{
lean_dec(v_tail_575_);
goto v___jp_563_;
}
else
{
if (lean_obj_tag(v_tail_575_) == 1)
{
lean_object* v_head_579_; lean_object* v_tail_580_; 
v_head_579_ = lean_ctor_get(v_tail_575_, 0);
lean_inc(v_head_579_);
v_tail_580_ = lean_ctor_get(v_tail_575_, 1);
lean_inc(v_tail_580_);
lean_dec_ref_known(v_tail_575_, 2);
if (lean_obj_tag(v_tail_580_) == 1)
{
lean_object* v_head_588_; lean_object* v_tail_589_; uint32_t v___x_590_; uint32_t v___x_591_; uint8_t v___x_592_; 
v_head_588_ = lean_ctor_get(v_tail_580_, 0);
lean_inc(v_head_588_);
v_tail_589_ = lean_ctor_get(v_tail_580_, 1);
lean_inc(v_tail_589_);
lean_dec_ref_known(v_tail_580_, 2);
v___x_590_ = 58;
v___x_591_ = lean_unbox_uint32(v_head_588_);
lean_dec(v_head_588_);
v___x_592_ = lean_uint32_dec_eq(v___x_591_, v___x_590_);
if (v___x_592_ == 0)
{
lean_dec(v_tail_589_);
lean_dec(v_head_579_);
goto v___jp_563_;
}
else
{
if (lean_obj_tag(v_tail_589_) == 0)
{
uint32_t v___x_593_; uint32_t v___x_594_; uint8_t v___x_595_; 
v___x_593_ = 65;
v___x_594_ = lean_unbox_uint32(v_head_579_);
v___x_595_ = lean_uint32_dec_le(v___x_593_, v___x_594_);
if (v___x_595_ == 0)
{
goto v___jp_581_;
}
else
{
uint32_t v___x_596_; uint32_t v___x_597_; uint8_t v___x_598_; 
v___x_596_ = 90;
v___x_597_ = lean_unbox_uint32(v_head_579_);
v___x_598_ = lean_uint32_dec_le(v___x_597_, v___x_596_);
if (v___x_598_ == 0)
{
goto v___jp_581_;
}
else
{
lean_dec(v_head_579_);
goto v___jp_538_;
}
}
}
else
{
lean_dec(v_tail_589_);
lean_dec(v_head_579_);
goto v___jp_563_;
}
}
}
else
{
lean_dec(v_tail_580_);
lean_dec(v_head_579_);
goto v___jp_563_;
}
v___jp_581_:
{
uint32_t v___x_582_; uint32_t v___x_583_; uint8_t v___x_584_; 
v___x_582_ = 97;
v___x_583_ = lean_unbox_uint32(v_head_579_);
v___x_584_ = lean_uint32_dec_le(v___x_582_, v___x_583_);
if (v___x_584_ == 0)
{
lean_dec(v_head_579_);
v___y_558_ = v___x_584_;
goto v___jp_557_;
}
else
{
uint32_t v___x_585_; uint32_t v___x_586_; uint8_t v___x_587_; 
v___x_585_ = 122;
v___x_586_ = lean_unbox_uint32(v_head_579_);
lean_dec(v_head_579_);
v___x_587_ = lean_uint32_dec_le(v___x_586_, v___x_585_);
v___y_558_ = v___x_587_;
goto v___jp_557_;
}
}
}
else
{
lean_dec(v_tail_575_);
goto v___jp_563_;
}
}
}
else
{
lean_dec(v___x_573_);
goto v___jp_563_;
}
v___jp_538_:
{
lean_object* v_str_539_; lean_object* v_startInclusive_540_; lean_object* v_endExclusive_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint32_t v___x_547_; uint32_t v___x_548_; uint8_t v___x_549_; 
v_str_539_ = lean_ctor_get(v_p_537_, 0);
v_startInclusive_540_ = lean_ctor_get(v_p_537_, 1);
v_endExclusive_541_ = lean_ctor_get(v_p_537_, 2);
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = l_String_Slice_Pos_nextn(v_p_537_, v___x_543_, v___x_542_);
v___x_545_ = lean_nat_add(v_startInclusive_540_, v___x_544_);
lean_dec(v___x_544_);
v___x_546_ = lean_string_utf8_extract(v_str_539_, v___x_545_, v_endExclusive_541_);
lean_dec(v___x_545_);
v___x_547_ = lean_string_utf8_get(v___x_546_, v___x_543_);
v___x_548_ = 97;
v___x_549_ = lean_uint32_dec_le(v___x_548_, v___x_547_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; 
v___x_550_ = lean_string_utf8_set(v___x_546_, v___x_543_, v___x_547_);
return v___x_550_;
}
else
{
uint32_t v___x_551_; uint8_t v___x_552_; 
v___x_551_ = 122;
v___x_552_ = lean_uint32_dec_le(v___x_547_, v___x_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; 
v___x_553_ = lean_string_utf8_set(v___x_546_, v___x_543_, v___x_547_);
return v___x_553_;
}
else
{
uint32_t v___x_554_; uint32_t v___x_555_; lean_object* v___x_556_; 
v___x_554_ = 4294967264;
v___x_555_ = lean_uint32_add(v___x_547_, v___x_554_);
v___x_556_ = lean_string_utf8_set(v___x_546_, v___x_543_, v___x_555_);
return v___x_556_;
}
}
}
v___jp_557_:
{
if (v___y_558_ == 0)
{
lean_object* v_str_559_; lean_object* v_startInclusive_560_; lean_object* v_endExclusive_561_; lean_object* v___x_562_; 
v_str_559_ = lean_ctor_get(v_p_537_, 0);
v_startInclusive_560_ = lean_ctor_get(v_p_537_, 1);
v_endExclusive_561_ = lean_ctor_get(v_p_537_, 2);
v___x_562_ = lean_string_utf8_extract(v_str_559_, v_startInclusive_560_, v_endExclusive_561_);
return v___x_562_;
}
else
{
goto v___jp_538_;
}
}
v___jp_563_:
{
lean_object* v_str_564_; lean_object* v_startInclusive_565_; lean_object* v_endExclusive_566_; lean_object* v___x_567_; 
v_str_564_ = lean_ctor_get(v_p_537_, 0);
v_startInclusive_565_ = lean_ctor_get(v_p_537_, 1);
v_endExclusive_566_ = lean_ctor_get(v_p_537_, 2);
v___x_567_ = lean_string_utf8_extract(v_str_564_, v_startInclusive_565_, v_endExclusive_566_);
return v___x_567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression___boxed(lean_object* v_p_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression(v_p_599_);
lean_dec_ref(v_p_599_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0(lean_object* v_p_601_, lean_object* v_inst_602_, lean_object* v_R_603_, lean_object* v_a_604_, lean_object* v_b_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg(v_p_601_, v_a_604_, v_b_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___boxed(lean_object* v_p_607_, lean_object* v_inst_608_, lean_object* v_R_609_, lean_object* v_a_610_, lean_object* v_b_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0(v_p_607_, v_inst_608_, v_R_609_, v_a_610_, v_b_611_);
lean_dec_ref(v_p_607_);
return v_res_612_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = ((lean_object*)(l_System_Uri_pathToUri___closed__3));
v___x_614_ = lean_string_utf8_byte_size(v___x_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg(lean_object* v_s_615_){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_616_ = ((lean_object*)(l_System_Uri_pathToUri___closed__3));
v___x_617_ = lean_string_utf8_byte_size(v_s_615_);
v___x_618_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg___closed__0, &l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg___closed__0_once, _init_l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg___closed__0);
v___x_619_ = lean_nat_dec_le(v___x_618_, v___x_617_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
lean_dec_ref(v_s_615_);
v___x_620_ = lean_box(0);
return v___x_620_;
}
else
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = lean_string_memcmp(v_s_615_, v___x_616_, v___x_621_, v___x_621_, v___x_618_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
lean_dec_ref(v_s_615_);
v___x_623_ = lean_box(0);
return v___x_623_;
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
lean_inc_ref(v_s_615_);
v___x_624_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_624_, 0, v_s_615_);
lean_ctor_set(v___x_624_, 1, v___x_621_);
lean_ctor_set(v___x_624_, 2, v___x_617_);
v___x_625_ = l_String_Slice_pos_x21(v___x_624_, v___x_618_);
lean_dec_ref_known(v___x_624_, 3);
v___x_626_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_626_, 0, v_s_615_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
lean_ctor_set(v___x_626_, 2, v___x_617_);
v___x_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0(lean_object* v_s_628_, lean_object* v_pat_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg(v_s_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___boxed(lean_object* v_s_631_, lean_object* v_pat_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0(v_s_631_, v_pat_632_);
lean_dec_ref(v_pat_632_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1(lean_object* v_s_634_, lean_object* v_pos_635_){
_start:
{
lean_object* v_str_636_; lean_object* v_startInclusive_637_; lean_object* v_endExclusive_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v_str_636_ = lean_ctor_get(v_s_634_, 0);
v_startInclusive_637_ = lean_ctor_get(v_s_634_, 1);
v_endExclusive_638_ = lean_ctor_get(v_s_634_, 2);
v___x_639_ = lean_nat_add(v_startInclusive_637_, v_pos_635_);
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = lean_nat_sub(v_endExclusive_638_, v___x_639_);
v___x_642_ = lean_nat_dec_eq(v___x_640_, v___x_641_);
lean_dec(v___x_641_);
if (v___x_642_ == 0)
{
uint32_t v___x_643_; uint32_t v___x_644_; uint8_t v___x_645_; 
v___x_643_ = lean_string_utf8_get_fast(v_str_636_, v___x_639_);
v___x_644_ = 47;
v___x_645_ = lean_uint32_dec_eq(v___x_643_, v___x_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_646_ = lean_string_utf8_next_fast(v_str_636_, v___x_639_);
v___x_647_ = lean_nat_sub(v___x_646_, v___x_639_);
lean_dec(v___x_639_);
v___x_648_ = lean_nat_add(v_pos_635_, v___x_647_);
lean_dec(v___x_647_);
v___x_649_ = lean_nat_dec_lt(v_pos_635_, v___x_648_);
if (v___x_649_ == 0)
{
lean_dec(v___x_648_);
return v_pos_635_;
}
else
{
lean_dec(v_pos_635_);
v_pos_635_ = v___x_648_;
goto _start;
}
}
else
{
lean_dec(v___x_639_);
return v_pos_635_;
}
}
else
{
lean_dec(v___x_639_);
return v_pos_635_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1___boxed(lean_object* v_s_651_, lean_object* v_pos_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1(v_s_651_, v_pos_652_);
lean_dec_ref(v_s_651_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_Uri_fileUriToPath_x3f_spec__2(lean_object* v_s_654_, lean_object* v_p_655_){
_start:
{
uint32_t v___y_657_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = lean_string_utf8_byte_size(v_s_654_);
v___x_663_ = lean_nat_dec_eq(v_p_655_, v___x_662_);
if (v___x_663_ == 0)
{
uint32_t v___x_664_; uint32_t v___x_665_; uint8_t v___x_666_; 
v___x_664_ = lean_string_utf8_get_fast(v_s_654_, v_p_655_);
v___x_665_ = 47;
v___x_666_ = lean_uint32_dec_eq(v___x_664_, v___x_665_);
if (v___x_666_ == 0)
{
v___y_657_ = v___x_664_;
goto v___jp_656_;
}
else
{
uint32_t v___x_667_; 
v___x_667_ = 92;
v___y_657_ = v___x_667_;
goto v___jp_656_;
}
}
else
{
lean_dec(v_p_655_);
return v_s_654_;
}
v___jp_656_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
lean_inc(v_p_655_);
v___x_658_ = lean_string_utf8_set(v_s_654_, v_p_655_, v___y_657_);
v___x_659_ = l_Char_utf8Size(v___y_657_);
v___x_660_ = lean_nat_add(v_p_655_, v___x_659_);
lean_dec(v___x_659_);
lean_dec(v_p_655_);
v_s_654_ = v___x_658_;
v_p_655_ = v___x_660_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_fileUriToPath_x3f(lean_object* v_uri_668_){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = l_System_Uri_UriEscape_decodeUri(v_uri_668_);
v___x_670_ = l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg(v___x_669_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v___x_671_; 
v___x_671_ = lean_box(0);
return v___x_671_;
}
else
{
lean_object* v_val_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_702_; 
v_val_672_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_702_ == 0)
{
v___x_674_ = v___x_670_;
v_isShared_675_ = v_isSharedCheck_702_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_val_672_);
lean_dec(v___x_670_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_702_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_str_676_; lean_object* v_startInclusive_677_; lean_object* v_endExclusive_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_698_; 
v_str_676_ = lean_ctor_get(v_val_672_, 0);
lean_inc_ref(v_str_676_);
v_startInclusive_677_ = lean_ctor_get(v_val_672_, 1);
lean_inc(v_startInclusive_677_);
v_endExclusive_678_ = lean_ctor_get(v_val_672_, 2);
lean_inc(v_endExclusive_678_);
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1(v_val_672_, v___x_679_);
v_isSharedCheck_698_ = !lean_is_exclusive(v_val_672_);
if (v_isSharedCheck_698_ == 0)
{
lean_object* v_unused_699_; lean_object* v_unused_700_; lean_object* v_unused_701_; 
v_unused_699_ = lean_ctor_get(v_val_672_, 2);
lean_dec(v_unused_699_);
v_unused_700_ = lean_ctor_get(v_val_672_, 1);
lean_dec(v_unused_700_);
v_unused_701_ = lean_ctor_get(v_val_672_, 0);
lean_dec(v_unused_701_);
v___x_682_ = v_val_672_;
v_isShared_683_ = v_isSharedCheck_698_;
goto v_resetjp_681_;
}
else
{
lean_dec(v_val_672_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_698_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_684_ = lean_nat_add(v_startInclusive_677_, v___x_680_);
lean_dec(v___x_680_);
lean_dec(v_startInclusive_677_);
v___x_685_ = l_System_Platform_isWindows;
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_688_; 
lean_del_object(v___x_682_);
v___x_686_ = lean_string_utf8_extract(v_str_676_, v___x_684_, v_endExclusive_678_);
lean_dec(v_endExclusive_678_);
lean_dec(v___x_684_);
lean_dec_ref(v_str_676_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_686_);
v___x_688_ = v___x_674_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_686_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
else
{
lean_object* v_p_691_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v___x_684_);
v_p_691_ = v___x_682_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_str_676_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_697_, 2, v_endExclusive_678_);
v_p_691_ = v_reuseFailAlloc_697_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_692_ = l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression(v_p_691_);
lean_dec_ref(v_p_691_);
v___x_693_ = l_String_mapAux___at___00System_Uri_fileUriToPath_x3f_spec__2(v___x_692_, v___x_679_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_693_);
v___x_695_ = v___x_674_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_693_);
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
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_fileUriToPath_x3f___boxed(lean_object* v_uri_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_System_Uri_fileUriToPath_x3f(v_uri_703_);
lean_dec_ref(v_uri_703_);
return v_res_704_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_System_Uri(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
