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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
extern lean_object* l_ByteArray_empty;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_System_Uri_escapeUri___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_unescapeUri(lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_unescapeUri___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__0 = (const lean_object*)&l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__0_value;
static const lean_array_object l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__1 = (const lean_object*)&l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_Uri_pathToUri_spec__0(lean_object*, lean_object*);
static const lean_string_object l_System_Uri_pathToUri___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "file:///"};
static const lean_object* l_System_Uri_pathToUri___closed__0 = (const lean_object*)&l_System_Uri_pathToUri___closed__0_value;
static const lean_string_object l_System_Uri_pathToUri___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_System_Uri_pathToUri___closed__1 = (const lean_object*)&l_System_Uri_pathToUri___closed__1_value;
static const lean_string_object l_System_Uri_pathToUri___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "file://"};
static const lean_object* l_System_Uri_pathToUri___closed__2 = (const lean_object*)&l_System_Uri_pathToUri___closed__2_value;
LEAN_EXPORT lean_object* l_System_Uri_pathToUri(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression___closed__0 = (const lean_object*)&l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(uint8_t v_c_7_){
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
LEAN_EXPORT void l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_7_ = stack[0].m_num;
lean_object* v_res_37_;
v_res_37_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(v_c_7_);
stack->m_obj
 = v_res_37_;
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f___boxed(lean_object* v_c_38_){
_start:
{
uint8_t v_c_boxed_39_; lean_object* v_res_40_; 
v_c_boxed_39_ = lean_unbox(v_c_38_);
v_res_40_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(v_c_boxed_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1(lean_object* v_msg_42_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = ((lean_object*)(l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0));
v___x_44_ = lean_panic_fn_borrowed(v___x_43_, v_msg_42_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___redArg(lean_object* v_len_45_, lean_object* v_rawBytes_46_, lean_object* v_a_47_){
_start:
{
lean_object* v_fst_48_; lean_object* v_snd_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_107_; 
v_fst_48_ = lean_ctor_get(v_a_47_, 0);
v_snd_49_ = lean_ctor_get(v_a_47_, 1);
v_isSharedCheck_107_ = !lean_is_exclusive(v_a_47_);
if (v_isSharedCheck_107_ == 0)
{
v___x_51_ = v_a_47_;
v_isShared_52_ = v_isSharedCheck_107_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_snd_49_);
lean_inc(v_fst_48_);
lean_dec(v_a_47_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_107_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
uint8_t v___x_53_; 
v___x_53_ = lean_nat_dec_lt(v_snd_49_, v_len_45_);
if (v___x_53_ == 0)
{
lean_object* v___x_55_; 
if (v_isShared_52_ == 0)
{
v___x_55_ = v___x_51_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_fst_48_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v_snd_49_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
else
{
uint8_t v_percent_57_; uint8_t v___x_58_; uint8_t v___x_67_; 
v_percent_57_ = 37;
v___x_58_ = lean_byte_array_fget(v_rawBytes_46_, v_snd_49_);
v___x_67_ = lean_uint8_dec_eq(v___x_58_, v_percent_57_);
if (v___x_67_ == 0)
{
goto v___jp_59_;
}
else
{
lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_68_ = lean_unsigned_to_nat(1u);
v___x_69_ = lean_nat_add(v_snd_49_, v___x_68_);
v___x_70_ = lean_nat_dec_lt(v___x_69_, v_len_45_);
if (v___x_70_ == 0)
{
lean_dec(v___x_69_);
goto v___jp_59_;
}
else
{
uint8_t v___x_71_; lean_object* v___x_72_; 
lean_del_object(v___x_51_);
v___x_71_ = lean_byte_array_fget(v_rawBytes_46_, v___x_69_);
lean_dec(v___x_69_);
v___x_72_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(v___x_71_);
if (lean_obj_tag(v___x_72_) == 1)
{
lean_object* v_val_73_; lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v_val_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_val_73_);
lean_dec_ref_known(v___x_72_, 1);
v___x_74_ = lean_unsigned_to_nat(2u);
v___x_75_ = lean_nat_add(v_snd_49_, v___x_74_);
v___x_76_ = lean_nat_dec_lt(v___x_75_, v_len_45_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
lean_dec(v_val_73_);
lean_dec(v_snd_49_);
v___x_77_ = lean_byte_array_push(v_fst_48_, v___x_58_);
v___x_78_ = lean_byte_array_push(v___x_77_, v___x_71_);
v___x_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___x_75_);
v_a_47_ = v___x_79_;
goto _start;
}
else
{
uint8_t v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_byte_array_fget(v_rawBytes_46_, v___x_75_);
lean_dec(v___x_75_);
v___x_82_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(v___x_81_);
if (lean_obj_tag(v___x_82_) == 1)
{
lean_object* v_val_83_; uint8_t v___x_84_; uint8_t v___x_85_; uint8_t v___x_86_; uint8_t v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v_val_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_val_83_);
lean_dec_ref_known(v___x_82_, 1);
v___x_84_ = 4;
v___x_85_ = lean_unbox(v_val_73_);
lean_dec(v_val_73_);
v___x_86_ = lean_uint8_shift_left(v___x_85_, v___x_84_);
v___x_87_ = lean_unbox(v_val_83_);
lean_dec(v_val_83_);
v___x_88_ = lean_uint8_add(v___x_86_, v___x_87_);
v___x_89_ = lean_byte_array_push(v_fst_48_, v___x_88_);
v___x_90_ = lean_unsigned_to_nat(3u);
v___x_91_ = lean_nat_add(v_snd_49_, v___x_90_);
lean_dec(v_snd_49_);
v___x_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_89_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
v_a_47_ = v___x_92_;
goto _start;
}
else
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
lean_dec(v___x_82_);
lean_dec(v_val_73_);
v___x_94_ = lean_byte_array_push(v_fst_48_, v___x_58_);
v___x_95_ = lean_byte_array_push(v___x_94_, v___x_71_);
v___x_96_ = lean_byte_array_push(v___x_95_, v___x_81_);
v___x_97_ = lean_unsigned_to_nat(3u);
v___x_98_ = lean_nat_add(v_snd_49_, v___x_97_);
lean_dec(v_snd_49_);
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_96_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v_a_47_ = v___x_99_;
goto _start;
}
}
}
else
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec(v___x_72_);
v___x_101_ = lean_byte_array_push(v_fst_48_, v___x_58_);
v___x_102_ = lean_byte_array_push(v___x_101_, v___x_71_);
v___x_103_ = lean_unsigned_to_nat(2u);
v___x_104_ = lean_nat_add(v_snd_49_, v___x_103_);
lean_dec(v_snd_49_);
v___x_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_102_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v_a_47_ = v___x_105_;
goto _start;
}
}
}
v___jp_59_:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_64_; 
v___x_60_ = lean_byte_array_push(v_fst_48_, v___x_58_);
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = lean_nat_add(v_snd_49_, v___x_61_);
lean_dec(v_snd_49_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 1, v___x_62_);
lean_ctor_set(v___x_51_, 0, v___x_60_);
v___x_64_ = v___x_51_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v___x_62_);
v___x_64_ = v_reuseFailAlloc_66_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
v_a_47_ = v___x_64_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___redArg___boxed(lean_object* v_len_108_, lean_object* v_rawBytes_109_, lean_object* v_a_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___redArg(v_len_108_, v_rawBytes_109_, v_a_110_);
lean_dec_ref(v_rawBytes_109_);
lean_dec(v_len_108_);
return v_res_111_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_decodeUri___closed__0(void){
_start:
{
lean_object* v_i_112_; lean_object* v_decoded_113_; lean_object* v___x_114_; 
v_i_112_ = lean_unsigned_to_nat(0u);
v_decoded_113_ = l_ByteArray_empty;
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v_decoded_113_);
lean_ctor_set(v___x_114_, 1, v_i_112_);
return v___x_114_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_decodeUri___closed__4(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_118_ = ((lean_object*)(l_System_Uri_UriEscape_decodeUri___closed__3));
v___x_119_ = lean_unsigned_to_nat(46u);
v___x_120_ = lean_unsigned_to_nat(193u);
v___x_121_ = ((lean_object*)(l_System_Uri_UriEscape_decodeUri___closed__2));
v___x_122_ = ((lean_object*)(l_System_Uri_UriEscape_decodeUri___closed__1));
v___x_123_ = l_mkPanicMessageWithDecl(v___x_122_, v___x_121_, v___x_120_, v___x_119_, v___x_118_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_decodeUri(lean_object* v_uri_124_){
_start:
{
lean_object* v_rawBytes_125_; lean_object* v_len_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v_fst_129_; uint8_t v___x_130_; 
v_rawBytes_125_ = lean_string_to_utf8(v_uri_124_);
v_len_126_ = lean_byte_array_size(v_rawBytes_125_);
v___x_127_ = lean_obj_once(&l_System_Uri_UriEscape_decodeUri___closed__0, &l_System_Uri_UriEscape_decodeUri___closed__0_once, _init_l_System_Uri_UriEscape_decodeUri___closed__0);
v___x_128_ = l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___redArg(v_len_126_, v_rawBytes_125_, v___x_127_);
lean_dec_ref(v_rawBytes_125_);
v_fst_129_ = lean_ctor_get(v___x_128_, 0);
lean_inc(v_fst_129_);
lean_dec_ref(v___x_128_);
v___x_130_ = lean_string_validate_utf8(v_fst_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; 
lean_dec(v_fst_129_);
v___x_131_ = lean_obj_once(&l_System_Uri_UriEscape_decodeUri___closed__4, &l_System_Uri_UriEscape_decodeUri___closed__4_once, _init_l_System_Uri_UriEscape_decodeUri___closed__4);
v___x_132_ = l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1(v___x_131_);
return v___x_132_;
}
else
{
lean_object* v___x_133_; 
v___x_133_ = lean_string_from_utf8_unchecked(v_fst_129_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_decodeUri___boxed(lean_object* v_uri_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_System_Uri_UriEscape_decodeUri(v_uri_134_);
lean_dec_ref(v_uri_134_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0(lean_object* v_len_136_, lean_object* v_rawBytes_137_, lean_object* v_inst_138_, lean_object* v_a_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___redArg(v_len_136_, v_rawBytes_137_, v_a_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___boxed(lean_object* v_len_141_, lean_object* v_rawBytes_142_, lean_object* v_inst_143_, lean_object* v_a_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0(v_len_141_, v_rawBytes_142_, v_inst_143_, v_a_144_);
lean_dec_ref(v_rawBytes_142_);
lean_dec(v_len_141_);
return v_res_145_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_146_; lean_object* v___x_147_; 
v___x_146_ = 32;
v___x_147_ = lean_box_uint32(v___x_146_);
return v___x_147_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_box(0);
v___x_149_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0___boxed__const__1;
v___x_150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v___x_148_);
return v___x_150_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_151_; lean_object* v___x_152_; 
v___x_151_ = 37;
v___x_152_ = lean_box_uint32(v___x_151_);
return v___x_152_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_153_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0);
v___x_154_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1___boxed__const__1;
v___x_155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v___x_153_);
return v___x_155_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_156_; lean_object* v___x_157_; 
v___x_156_ = 42;
v___x_157_ = lean_box_uint32(v___x_156_);
return v___x_157_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1);
v___x_159_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2___boxed__const__1;
v___x_160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___x_158_);
return v___x_160_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_161_; lean_object* v___x_162_; 
v___x_161_ = 41;
v___x_162_ = lean_box_uint32(v___x_161_);
return v___x_162_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2);
v___x_164_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3___boxed__const__1;
v___x_165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v___x_163_);
return v___x_165_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4___boxed__const__1(void){
_start:
{
uint32_t v___x_166_; lean_object* v___x_167_; 
v___x_166_ = 40;
v___x_167_ = lean_box_uint32(v___x_166_);
return v___x_167_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3);
v___x_169_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4___boxed__const__1;
v___x_170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
return v___x_170_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5___boxed__const__1(void){
_start:
{
uint32_t v___x_171_; lean_object* v___x_172_; 
v___x_171_ = 39;
v___x_172_ = lean_box_uint32(v___x_171_);
return v___x_172_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4);
v___x_174_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5___boxed__const__1;
v___x_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___x_173_);
return v___x_175_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6___boxed__const__1(void){
_start:
{
uint32_t v___x_176_; lean_object* v___x_177_; 
v___x_176_ = 33;
v___x_177_ = lean_box_uint32(v___x_176_);
return v___x_177_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5);
v___x_179_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6___boxed__const__1;
v___x_180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v___x_178_);
return v___x_180_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7___boxed__const__1(void){
_start:
{
uint32_t v___x_181_; lean_object* v___x_182_; 
v___x_181_ = 44;
v___x_182_ = lean_box_uint32(v___x_181_);
return v___x_182_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6);
v___x_184_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7___boxed__const__1;
v___x_185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v___x_183_);
return v___x_185_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8___boxed__const__1(void){
_start:
{
uint32_t v___x_186_; lean_object* v___x_187_; 
v___x_186_ = 36;
v___x_187_ = lean_box_uint32(v___x_186_);
return v___x_187_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_188_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7);
v___x_189_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8___boxed__const__1;
v___x_190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v___x_188_);
return v___x_190_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9___boxed__const__1(void){
_start:
{
uint32_t v___x_191_; lean_object* v___x_192_; 
v___x_191_ = 43;
v___x_192_ = lean_box_uint32(v___x_191_);
return v___x_192_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8);
v___x_194_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9___boxed__const__1;
v___x_195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_193_);
return v___x_195_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10___boxed__const__1(void){
_start:
{
uint32_t v___x_196_; lean_object* v___x_197_; 
v___x_196_ = 61;
v___x_197_ = lean_box_uint32(v___x_196_);
return v___x_197_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9);
v___x_199_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10___boxed__const__1;
v___x_200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v___x_198_);
return v___x_200_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11___boxed__const__1(void){
_start:
{
uint32_t v___x_201_; lean_object* v___x_202_; 
v___x_201_ = 38;
v___x_202_ = lean_box_uint32(v___x_201_);
return v___x_202_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_203_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10);
v___x_204_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11___boxed__const__1;
v___x_205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_203_);
return v___x_205_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12___boxed__const__1(void){
_start:
{
uint32_t v___x_206_; lean_object* v___x_207_; 
v___x_206_ = 64;
v___x_207_ = lean_box_uint32(v___x_206_);
return v___x_207_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11);
v___x_209_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12___boxed__const__1;
v___x_210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v___x_208_);
return v___x_210_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13___boxed__const__1(void){
_start:
{
uint32_t v___x_211_; lean_object* v___x_212_; 
v___x_211_ = 93;
v___x_212_ = lean_box_uint32(v___x_211_);
return v___x_212_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12);
v___x_214_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13___boxed__const__1;
v___x_215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v___x_213_);
return v___x_215_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14___boxed__const__1(void){
_start:
{
uint32_t v___x_216_; lean_object* v___x_217_; 
v___x_216_ = 91;
v___x_217_ = lean_box_uint32(v___x_216_);
return v___x_217_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13);
v___x_219_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14___boxed__const__1;
v___x_220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___x_218_);
return v___x_220_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15___boxed__const__1(void){
_start:
{
uint32_t v___x_221_; lean_object* v___x_222_; 
v___x_221_ = 35;
v___x_222_ = lean_box_uint32(v___x_221_);
return v___x_222_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_223_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14);
v___x_224_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15___boxed__const__1;
v___x_225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set(v___x_225_, 1, v___x_223_);
return v___x_225_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16___boxed__const__1(void){
_start:
{
uint32_t v___x_226_; lean_object* v___x_227_; 
v___x_226_ = 63;
v___x_227_ = lean_box_uint32(v___x_226_);
return v___x_227_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_228_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15);
v___x_229_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16___boxed__const__1;
v___x_230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v___x_228_);
return v___x_230_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17___boxed__const__1(void){
_start:
{
uint32_t v___x_231_; lean_object* v___x_232_; 
v___x_231_ = 58;
v___x_232_ = lean_box_uint32(v___x_231_);
return v___x_232_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16);
v___x_234_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17___boxed__const__1;
v___x_235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v___x_233_);
return v___x_235_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18___boxed__const__1(void){
_start:
{
uint32_t v___x_236_; lean_object* v___x_237_; 
v___x_236_ = 59;
v___x_237_ = lean_box_uint32(v___x_236_);
return v___x_237_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17);
v___x_239_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18___boxed__const__1;
v___x_240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_238_);
return v___x_240_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars(void){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex_spec__0(lean_object* v_s_242_, lean_object* v_p_243_){
_start:
{
uint32_t v___y_245_; lean_object* v___x_250_; uint8_t v_decide_251_; 
v___x_250_ = lean_string_utf8_byte_size(v_s_242_);
v_decide_251_ = lean_nat_dec_eq(v_p_243_, v___x_250_);
if (v_decide_251_ == 0)
{
uint32_t v___x_252_; uint32_t v___x_253_; uint8_t v___x_254_; 
v___x_252_ = lean_string_utf8_get_fast(v_s_242_, v_p_243_);
v___x_253_ = 97;
v___x_254_ = lean_uint32_dec_le(v___x_253_, v___x_252_);
if (v___x_254_ == 0)
{
v___y_245_ = v___x_252_;
goto v___jp_244_;
}
else
{
uint32_t v___x_255_; uint8_t v___x_256_; 
v___x_255_ = 122;
v___x_256_ = lean_uint32_dec_le(v___x_252_, v___x_255_);
if (v___x_256_ == 0)
{
v___y_245_ = v___x_252_;
goto v___jp_244_;
}
else
{
uint32_t v___x_257_; uint32_t v___x_258_; 
v___x_257_ = 4294967264;
v___x_258_ = lean_uint32_add(v___x_252_, v___x_257_);
v___y_245_ = v___x_258_;
goto v___jp_244_;
}
}
}
else
{
lean_dec(v_p_243_);
return v_s_242_;
}
v___jp_244_:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
lean_inc(v_p_243_);
v___x_246_ = lean_string_utf8_set(v_s_242_, v_p_243_, v___y_245_);
v___x_247_ = l_Char_utf8Size(v___y_245_);
v___x_248_ = lean_nat_add(v_p_243_, v___x_247_);
lean_dec(v___x_247_);
lean_dec(v_p_243_);
v_s_242_ = v___x_246_;
v_p_243_ = v___x_248_;
goto _start;
}
}
}
lean_object* l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(uint8_t v_c_259_){
_start:
{
uint8_t v___x_260_; uint8_t v___x_261_; uint8_t v_d2_262_; uint8_t v_d1_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_260_ = 16;
v___x_261_ = 4;
v_d2_262_ = lean_uint8_shift_right(v_c_259_, v___x_261_);
v_d1_263_ = lean_uint8_mod(v_c_259_, v___x_260_);
v___x_264_ = lean_uint8_to_nat(v_d2_262_);
v___x_265_ = l_hexDigitRepr(v___x_264_);
v___x_266_ = lean_uint8_to_nat(v_d1_263_);
v___x_267_ = l_hexDigitRepr(v___x_266_);
v___x_268_ = lean_string_append(v___x_265_, v___x_267_);
lean_dec_ref(v___x_267_);
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = l_String_mapAux___at___00__private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex_spec__0(v___x_268_, v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT void l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_259_ = stack[0].m_num;
lean_object* v_res_271_;
v_res_271_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(v_c_259_);
stack->m_obj
 = v_res_271_;
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex___boxed(lean_object* v_c_272_){
_start:
{
uint8_t v_c_boxed_273_; lean_object* v_res_274_; 
v_c_boxed_273_ = lean_unbox(v_c_272_);
v_res_274_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(v_c_boxed_273_);
return v_res_274_;
}
}
uint8_t l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1(uint32_t v_a_275_, lean_object* v_x_276_){
_start:
{
if (lean_obj_tag(v_x_276_) == 0)
{
uint8_t v___x_277_; 
v___x_277_ = 0;
return v___x_277_;
}
else
{
lean_object* v_head_278_; lean_object* v_tail_279_; uint32_t v___x_280_; uint8_t v___x_281_; 
v_head_278_ = lean_ctor_get(v_x_276_, 0);
v_tail_279_ = lean_ctor_get(v_x_276_, 1);
v___x_280_ = lean_unbox_uint32(v_head_278_);
v___x_281_ = lean_uint32_dec_eq(v_a_275_, v___x_280_);
if (v___x_281_ == 0)
{
v_x_276_ = v_tail_279_;
goto _start;
}
else
{
return v___x_281_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_275_ = stack[0].m_num;
lean_object* v_x_276_ = stack[1].m_obj;
uint8_t v_res_283_;
v_res_283_ = l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1(v_a_275_, v_x_276_);
stack->m_num = v_res_283_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1___boxed(lean_object* v_a_284_, lean_object* v_x_285_){
_start:
{
uint32_t v_a_boxed_286_; uint8_t v_res_287_; lean_object* v_r_288_; 
v_a_boxed_286_ = lean_unbox_uint32(v_a_284_);
lean_dec(v_a_284_);
v_res_287_ = l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1(v_a_boxed_286_, v_x_285_);
lean_dec(v_x_285_);
v_r_288_ = lean_box(v_res_287_);
return v_r_288_;
}
}
lean_object* l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(lean_object* v_as_290_, size_t v_i_291_, size_t v_stop_292_, lean_object* v_b_293_){
_start:
{
uint8_t v___x_294_; 
v___x_294_ = lean_usize_dec_eq(v_i_291_, v_stop_292_);
if (v___x_294_ == 0)
{
uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; size_t v___x_300_; size_t v___x_301_; 
v___x_295_ = lean_byte_array_uget(v_as_290_, v_i_291_);
v___x_296_ = ((lean_object*)(l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___closed__0));
v___x_297_ = lean_string_append(v_b_293_, v___x_296_);
v___x_298_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(v___x_295_);
v___x_299_ = lean_string_append(v___x_297_, v___x_298_);
lean_dec_ref(v___x_298_);
v___x_300_ = ((size_t)1ULL);
v___x_301_ = lean_usize_add(v_i_291_, v___x_300_);
v_i_291_ = v___x_301_;
v_b_293_ = v___x_299_;
goto _start;
}
else
{
return v_b_293_;
}
}
}
LEAN_EXPORT void l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_290_ = stack[0].m_obj;
size_t v_i_291_ = stack[1].m_num;
size_t v_stop_292_ = stack[2].m_num;
lean_object* v_b_293_ = stack[3].m_obj;
lean_object* v_res_303_;
v_res_303_ = l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(v_as_290_, v_i_291_, v_stop_292_, v_b_293_);
stack->m_obj
 = v_res_303_;
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___boxed(lean_object* v_as_304_, lean_object* v_i_305_, lean_object* v_stop_306_, lean_object* v_b_307_){
_start:
{
size_t v_i_boxed_308_; size_t v_stop_boxed_309_; lean_object* v_res_310_; 
v_i_boxed_308_ = lean_unbox_usize(v_i_305_);
lean_dec(v_i_305_);
v_stop_boxed_309_ = lean_unbox_usize(v_stop_306_);
lean_dec(v_stop_306_);
v_res_310_ = l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(v_as_304_, v_i_boxed_308_, v_stop_boxed_309_, v_b_307_);
lean_dec_ref(v_as_304_);
return v_res_310_;
}
}
lean_object* l_System_Uri_UriEscape_uriEscapeAsciiChar(uint32_t v_c_311_){
_start:
{
uint8_t v___y_313_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = l_System_Uri_UriEscape_rfc3986ReservedChars;
v___x_338_ = l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1(v_c_311_, v___x_337_);
if (v___x_338_ == 0)
{
uint32_t v___x_339_; uint8_t v___x_340_; 
v___x_339_ = 32;
v___x_340_ = lean_uint32_dec_lt(v_c_311_, v___x_339_);
v___y_313_ = v___x_340_;
goto v___jp_312_;
}
else
{
v___y_313_ = v___x_338_;
goto v___jp_312_;
}
v___jp_312_:
{
if (v___y_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_314_ = lean_uint32_to_nat(v_c_311_);
v___x_315_ = lean_unsigned_to_nat(127u);
v___x_316_ = lean_nat_dec_lt(v___x_314_, v___x_315_);
lean_dec(v___x_314_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_317_ = ((lean_object*)(l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0));
v___x_318_ = lean_string_push(v___x_317_, v_c_311_);
v___x_319_ = lean_string_to_utf8(v___x_318_);
lean_dec_ref(v___x_318_);
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_321_ = lean_byte_array_size(v___x_319_);
v___x_322_ = lean_nat_dec_lt(v___x_320_, v___x_321_);
if (v___x_322_ == 0)
{
lean_dec_ref(v___x_319_);
return v___x_317_;
}
else
{
uint8_t v___x_323_; 
v___x_323_ = lean_nat_dec_le(v___x_321_, v___x_321_);
if (v___x_323_ == 0)
{
if (v___x_322_ == 0)
{
lean_dec_ref(v___x_319_);
return v___x_317_;
}
else
{
size_t v___x_324_; size_t v___x_325_; lean_object* v___x_326_; 
v___x_324_ = ((size_t)0ULL);
v___x_325_ = lean_usize_of_nat(v___x_321_);
v___x_326_ = l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(v___x_319_, v___x_324_, v___x_325_, v___x_317_);
lean_dec_ref(v___x_319_);
return v___x_326_;
}
}
else
{
size_t v___x_327_; size_t v___x_328_; lean_object* v___x_329_; 
v___x_327_ = ((size_t)0ULL);
v___x_328_ = lean_usize_of_nat(v___x_321_);
v___x_329_ = l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(v___x_319_, v___x_327_, v___x_328_, v___x_317_);
lean_dec_ref(v___x_319_);
return v___x_329_;
}
}
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = ((lean_object*)(l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0));
v___x_331_ = lean_string_push(v___x_330_, v_c_311_);
return v___x_331_;
}
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_332_ = ((lean_object*)(l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___closed__0));
v___x_333_ = lean_uint32_to_nat(v_c_311_);
v___x_334_ = lean_uint8_of_nat(v___x_333_);
lean_dec(v___x_333_);
v___x_335_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(v___x_334_);
v___x_336_ = lean_string_append(v___x_332_, v___x_335_);
lean_dec_ref(v___x_335_);
return v___x_336_;
}
}
}
}
LEAN_EXPORT void l_System_Uri_UriEscape_uriEscapeAsciiChar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_311_ = stack[0].m_num;
lean_object* v_res_341_;
v_res_341_ = l_System_Uri_UriEscape_uriEscapeAsciiChar(v_c_311_);
stack->m_obj
 = v_res_341_;
}
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_uriEscapeAsciiChar___boxed(lean_object* v_c_342_){
_start:
{
uint32_t v_c_boxed_343_; lean_object* v_res_344_; 
v_c_boxed_343_ = lean_unbox_uint32(v_c_342_);
lean_dec(v_c_342_);
v_res_344_ = l_System_Uri_UriEscape_uriEscapeAsciiChar(v_c_boxed_343_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(lean_object* v___x_345_, lean_object* v_uri_346_, lean_object* v_a_347_, lean_object* v_b_348_){
_start:
{
uint8_t v_decide_349_; 
v_decide_349_ = lean_nat_dec_eq(v_a_347_, v___x_345_);
if (v_decide_349_ == 0)
{
uint32_t v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_350_ = lean_string_utf8_get_fast(v_uri_346_, v_a_347_);
v___x_351_ = lean_string_utf8_next_fast(v_uri_346_, v_a_347_);
lean_dec(v_a_347_);
v___x_352_ = l_System_Uri_UriEscape_uriEscapeAsciiChar(v___x_350_);
v___x_353_ = lean_string_append(v_b_348_, v___x_352_);
lean_dec_ref(v___x_352_);
v_a_347_ = v___x_351_;
v_b_348_ = v___x_353_;
goto _start;
}
else
{
lean_dec(v_a_347_);
return v_b_348_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg___boxed(lean_object* v___x_355_, lean_object* v_uri_356_, lean_object* v_a_357_, lean_object* v_b_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(v___x_355_, v_uri_356_, v_a_357_, v_b_358_);
lean_dec_ref(v_uri_356_);
lean_dec(v___x_355_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_escapeUri(lean_object* v_uri_360_){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_361_ = ((lean_object*)(l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0));
v___x_362_ = lean_string_utf8_byte_size(v_uri_360_);
v___x_363_ = lean_unsigned_to_nat(0u);
v___x_364_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(v___x_362_, v_uri_360_, v___x_363_, v___x_361_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_escapeUri___boxed(lean_object* v_uri_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_System_Uri_escapeUri(v_uri_365_);
lean_dec_ref(v_uri_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0(lean_object* v___x_367_, lean_object* v___x_368_, lean_object* v_uri_369_, lean_object* v_inst_370_, lean_object* v_R_371_, lean_object* v_a_372_, lean_object* v_b_373_, lean_object* v_c_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(v___x_368_, v_uri_369_, v_a_372_, v_b_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___boxed(lean_object* v___x_376_, lean_object* v___x_377_, lean_object* v_uri_378_, lean_object* v_inst_379_, lean_object* v_R_380_, lean_object* v_a_381_, lean_object* v_b_382_, lean_object* v_c_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0(v___x_376_, v___x_377_, v_uri_378_, v_inst_379_, v_R_380_, v_a_381_, v_b_382_, v_c_383_);
lean_dec_ref(v_uri_378_);
lean_dec(v___x_377_);
lean_dec_ref(v___x_376_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_unescapeUri(lean_object* v_s_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_System_Uri_UriEscape_decodeUri(v_s_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_unescapeUri___boxed(lean_object* v_s_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_System_Uri_unescapeUri(v_s_387_);
lean_dec_ref(v_s_387_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg(lean_object* v_uri_389_, lean_object* v___x_390_, lean_object* v_a_391_, lean_object* v_b_392_){
_start:
{
lean_object* v_countdown_393_; lean_object* v_inner_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_410_; 
v_countdown_393_ = lean_ctor_get(v_a_391_, 0);
v_inner_394_ = lean_ctor_get(v_a_391_, 1);
v_isSharedCheck_410_ = !lean_is_exclusive(v_a_391_);
if (v_isSharedCheck_410_ == 0)
{
v___x_396_ = v_a_391_;
v_isShared_397_ = v_isSharedCheck_410_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_inner_394_);
lean_inc(v_countdown_393_);
lean_dec(v_a_391_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_410_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_398_ = lean_unsigned_to_nat(1u);
v___x_399_ = lean_nat_dec_eq(v_countdown_393_, v___x_398_);
if (v___x_399_ == 0)
{
uint8_t v_decide_400_; 
v_decide_400_ = lean_nat_dec_eq(v_inner_394_, v___x_390_);
if (v_decide_400_ == 0)
{
lean_object* v___x_401_; uint32_t v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_401_ = lean_string_utf8_next_fast(v_uri_389_, v_inner_394_);
v___x_402_ = lean_string_utf8_get_fast(v_uri_389_, v_inner_394_);
lean_dec(v_inner_394_);
v___x_403_ = lean_nat_sub(v_countdown_393_, v___x_398_);
lean_dec(v_countdown_393_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 1, v___x_401_);
lean_ctor_set(v___x_396_, 0, v___x_403_);
v___x_405_ = v___x_396_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v___x_401_);
v___x_405_ = v_reuseFailAlloc_409_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_box_uint32(v___x_402_);
v___x_407_ = lean_array_push(v_b_392_, v___x_406_);
v_a_391_ = v___x_405_;
v_b_392_ = v___x_407_;
goto _start;
}
}
else
{
lean_del_object(v___x_396_);
lean_dec(v_inner_394_);
lean_dec(v_countdown_393_);
return v_b_392_;
}
}
else
{
lean_del_object(v___x_396_);
lean_dec(v_inner_394_);
lean_dec(v_countdown_393_);
return v_b_392_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg___boxed(lean_object* v_uri_411_, lean_object* v___x_412_, lean_object* v_a_413_, lean_object* v_b_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg(v_uri_411_, v___x_412_, v_a_413_, v_b_414_);
lean_dec(v___x_412_);
lean_dec_ref(v_uri_411_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter(lean_object* v_uri_421_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = lean_string_utf8_byte_size(v_uri_421_);
v___x_424_ = ((lean_object*)(l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__0));
v___x_425_ = ((lean_object*)(l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__1));
v___x_426_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg(v_uri_421_, v___x_423_, v___x_424_, v___x_425_);
v___x_427_ = lean_array_to_list(v___x_426_);
if (lean_obj_tag(v___x_427_) == 1)
{
lean_object* v_tail_428_; 
v_tail_428_ = lean_ctor_get(v___x_427_, 1);
lean_inc(v_tail_428_);
if (lean_obj_tag(v_tail_428_) == 1)
{
lean_object* v_head_429_; lean_object* v_head_430_; lean_object* v_tail_431_; uint32_t v___x_432_; uint32_t v___x_433_; uint8_t v___x_434_; 
v_head_429_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_head_429_);
lean_dec_ref_known(v___x_427_, 2);
v_head_430_ = lean_ctor_get(v_tail_428_, 0);
lean_inc(v_head_430_);
v_tail_431_ = lean_ctor_get(v_tail_428_, 1);
lean_inc(v_tail_431_);
lean_dec_ref_known(v_tail_428_, 2);
v___x_432_ = 58;
v___x_433_ = lean_unbox_uint32(v_head_430_);
lean_dec(v_head_430_);
v___x_434_ = lean_uint32_dec_eq(v___x_433_, v___x_432_);
if (v___x_434_ == 0)
{
lean_dec(v_tail_431_);
lean_dec(v_head_429_);
return v_uri_421_;
}
else
{
if (lean_obj_tag(v_tail_431_) == 0)
{
uint32_t v___x_435_; uint32_t v___x_436_; uint8_t v___x_437_; 
v___x_435_ = 65;
v___x_436_ = lean_unbox_uint32(v_head_429_);
v___x_437_ = lean_uint32_dec_le(v___x_435_, v___x_436_);
if (v___x_437_ == 0)
{
lean_dec(v_head_429_);
return v_uri_421_;
}
else
{
uint32_t v___x_438_; uint32_t v___x_439_; uint8_t v___x_440_; 
v___x_438_ = 90;
v___x_439_ = lean_unbox_uint32(v_head_429_);
lean_dec(v_head_429_);
v___x_440_ = lean_uint32_dec_le(v___x_439_, v___x_438_);
if (v___x_440_ == 0)
{
return v_uri_421_;
}
else
{
uint32_t v___x_441_; uint8_t v___x_442_; 
v___x_441_ = lean_string_utf8_get(v_uri_421_, v___x_422_);
v___x_442_ = lean_uint32_dec_le(v___x_435_, v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; 
v___x_443_ = lean_string_utf8_set(v_uri_421_, v___x_422_, v___x_441_);
return v___x_443_;
}
else
{
uint8_t v___x_444_; 
v___x_444_ = lean_uint32_dec_le(v___x_441_, v___x_438_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; 
v___x_445_ = lean_string_utf8_set(v_uri_421_, v___x_422_, v___x_441_);
return v___x_445_;
}
else
{
uint32_t v___x_446_; uint32_t v___x_447_; lean_object* v___x_448_; 
v___x_446_ = 32;
v___x_447_ = lean_uint32_add(v___x_441_, v___x_446_);
v___x_448_ = lean_string_utf8_set(v_uri_421_, v___x_422_, v___x_447_);
return v___x_448_;
}
}
}
}
}
else
{
lean_dec(v_tail_431_);
lean_dec(v_head_429_);
return v_uri_421_;
}
}
}
else
{
lean_dec_ref_known(v___x_427_, 2);
lean_dec(v_tail_428_);
return v_uri_421_;
}
}
else
{
lean_dec(v___x_427_);
return v_uri_421_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0(lean_object* v___x_449_, lean_object* v_uri_450_, lean_object* v___x_451_, lean_object* v_inst_452_, lean_object* v_R_453_, lean_object* v_a_454_, lean_object* v_b_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg(v_uri_450_, v___x_451_, v_a_454_, v_b_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___boxed(lean_object* v___x_457_, lean_object* v_uri_458_, lean_object* v___x_459_, lean_object* v_inst_460_, lean_object* v_R_461_, lean_object* v_a_462_, lean_object* v_b_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0(v___x_457_, v_uri_458_, v___x_459_, v_inst_460_, v_R_461_, v_a_462_, v_b_463_);
lean_dec(v___x_459_);
lean_dec_ref(v_uri_458_);
lean_dec_ref(v___x_457_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_Uri_pathToUri_spec__0(lean_object* v_s_465_, lean_object* v_p_466_){
_start:
{
uint32_t v___y_468_; lean_object* v___x_473_; uint8_t v_decide_474_; 
v___x_473_ = lean_string_utf8_byte_size(v_s_465_);
v_decide_474_ = lean_nat_dec_eq(v_p_466_, v___x_473_);
if (v_decide_474_ == 0)
{
uint32_t v___x_475_; uint32_t v___x_476_; uint8_t v___x_477_; 
v___x_475_ = lean_string_utf8_get_fast(v_s_465_, v_p_466_);
v___x_476_ = 92;
v___x_477_ = lean_uint32_dec_eq(v___x_475_, v___x_476_);
if (v___x_477_ == 0)
{
v___y_468_ = v___x_475_;
goto v___jp_467_;
}
else
{
uint32_t v___x_478_; 
v___x_478_ = 47;
v___y_468_ = v___x_478_;
goto v___jp_467_;
}
}
else
{
lean_dec(v_p_466_);
return v_s_465_;
}
v___jp_467_:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
lean_inc(v_p_466_);
v___x_469_ = lean_string_utf8_set(v_s_465_, v_p_466_, v___y_468_);
v___x_470_ = l_Char_utf8Size(v___y_468_);
v___x_471_ = lean_nat_add(v_p_466_, v___x_470_);
lean_dec(v___x_470_);
lean_dec(v_p_466_);
v_s_465_ = v___x_469_;
v_p_466_ = v___x_471_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_pathToUri(lean_object* v_fname_482_){
_start:
{
lean_object* v___y_484_; lean_object* v_uri_488_; lean_object* v_uri_500_; uint8_t v___x_501_; 
v_uri_500_ = l_System_FilePath_normalize(v_fname_482_);
v___x_501_ = l_System_Platform_isWindows;
if (v___x_501_ == 0)
{
v_uri_488_ = v_uri_500_;
goto v___jp_487_;
}
else
{
lean_object* v_uri_502_; lean_object* v___x_503_; lean_object* v_uri_504_; 
v_uri_502_ = l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter(v_uri_500_);
v___x_503_ = lean_unsigned_to_nat(0u);
v_uri_504_ = l_String_mapAux___at___00System_Uri_pathToUri_spec__0(v_uri_502_, v___x_503_);
v_uri_488_ = v_uri_504_;
goto v___jp_487_;
}
v___jp_483_:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = ((lean_object*)(l_System_Uri_pathToUri___closed__0));
v___x_486_ = lean_string_append(v___x_485_, v___y_484_);
lean_dec_ref(v___y_484_);
return v___x_486_;
}
v___jp_487_:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v_uri_492_; lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_489_ = ((lean_object*)(l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0));
v___x_490_ = lean_string_utf8_byte_size(v_uri_488_);
v___x_491_ = lean_unsigned_to_nat(0u);
v_uri_492_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(v___x_490_, v_uri_488_, v___x_491_, v___x_489_);
lean_dec_ref(v_uri_488_);
v___x_493_ = lean_string_utf8_byte_size(v_uri_492_);
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = lean_nat_dec_le(v___x_494_, v___x_493_);
if (v___x_495_ == 0)
{
v___y_484_ = v_uri_492_;
goto v___jp_483_;
}
else
{
lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_496_ = ((lean_object*)(l_System_Uri_pathToUri___closed__1));
v___x_497_ = lean_string_memcmp(v_uri_492_, v___x_496_, v___x_491_, v___x_491_, v___x_494_);
if (v___x_497_ == 0)
{
v___y_484_ = v_uri_492_;
goto v___jp_483_;
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l_System_Uri_pathToUri___closed__2));
v___x_499_ = lean_string_append(v___x_498_, v_uri_492_);
lean_dec_ref(v_uri_492_);
return v___x_499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg(lean_object* v_p_505_, lean_object* v_a_506_, lean_object* v_b_507_){
_start:
{
lean_object* v_countdown_508_; lean_object* v_inner_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_531_; 
v_countdown_508_ = lean_ctor_get(v_a_506_, 0);
v_inner_509_ = lean_ctor_get(v_a_506_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v_a_506_);
if (v_isSharedCheck_531_ == 0)
{
v___x_511_ = v_a_506_;
v_isShared_512_ = v_isSharedCheck_531_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_inner_509_);
lean_inc(v_countdown_508_);
lean_dec(v_a_506_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_531_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_513_ = lean_unsigned_to_nat(1u);
v___x_514_ = lean_nat_dec_eq(v_countdown_508_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v_str_515_; lean_object* v_startInclusive_516_; lean_object* v_endExclusive_517_; lean_object* v___x_518_; uint8_t v_decide_519_; 
v_str_515_ = lean_ctor_get(v_p_505_, 0);
v_startInclusive_516_ = lean_ctor_get(v_p_505_, 1);
v_endExclusive_517_ = lean_ctor_get(v_p_505_, 2);
v___x_518_ = lean_nat_sub(v_endExclusive_517_, v_startInclusive_516_);
v_decide_519_ = lean_nat_dec_eq(v_inner_509_, v___x_518_);
lean_dec(v___x_518_);
if (v_decide_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; uint32_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_520_ = lean_nat_add(v_startInclusive_516_, v_inner_509_);
lean_dec(v_inner_509_);
v___x_521_ = lean_string_utf8_next_fast(v_str_515_, v___x_520_);
v___x_522_ = lean_nat_sub(v___x_521_, v_startInclusive_516_);
v___x_523_ = lean_string_utf8_get_fast(v_str_515_, v___x_520_);
lean_dec(v___x_520_);
v___x_524_ = lean_nat_sub(v_countdown_508_, v___x_513_);
lean_dec(v_countdown_508_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 1, v___x_522_);
lean_ctor_set(v___x_511_, 0, v___x_524_);
v___x_526_ = v___x_511_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v___x_522_);
v___x_526_ = v_reuseFailAlloc_530_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_box_uint32(v___x_523_);
v___x_528_ = lean_array_push(v_b_507_, v___x_527_);
v_a_506_ = v___x_526_;
v_b_507_ = v___x_528_;
goto _start;
}
}
else
{
lean_del_object(v___x_511_);
lean_dec(v_inner_509_);
lean_dec(v_countdown_508_);
return v_b_507_;
}
}
else
{
lean_del_object(v___x_511_);
lean_dec(v_inner_509_);
lean_dec(v_countdown_508_);
return v_b_507_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg___boxed(lean_object* v_p_532_, lean_object* v_a_533_, lean_object* v_b_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg(v_p_532_, v_a_533_, v_b_534_);
lean_dec_ref(v_p_532_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression(lean_object* v_p_539_){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_569_ = ((lean_object*)(l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression___closed__0));
v___x_570_ = ((lean_object*)(l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__1));
v___x_571_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg(v_p_539_, v___x_569_, v___x_570_);
v___x_572_ = lean_array_to_list(v___x_571_);
if (lean_obj_tag(v___x_572_) == 1)
{
lean_object* v_head_573_; lean_object* v_tail_574_; uint32_t v___x_575_; uint32_t v___x_576_; uint8_t v___x_577_; 
v_head_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_head_573_);
v_tail_574_ = lean_ctor_get(v___x_572_, 1);
lean_inc(v_tail_574_);
lean_dec_ref_known(v___x_572_, 2);
v___x_575_ = 47;
v___x_576_ = lean_unbox_uint32(v_head_573_);
lean_dec(v_head_573_);
v___x_577_ = lean_uint32_dec_eq(v___x_576_, v___x_575_);
if (v___x_577_ == 0)
{
lean_dec(v_tail_574_);
goto v___jp_564_;
}
else
{
if (lean_obj_tag(v_tail_574_) == 1)
{
lean_object* v_head_578_; lean_object* v_tail_579_; 
v_head_578_ = lean_ctor_get(v_tail_574_, 0);
lean_inc(v_head_578_);
v_tail_579_ = lean_ctor_get(v_tail_574_, 1);
lean_inc(v_tail_579_);
lean_dec_ref_known(v_tail_574_, 2);
if (lean_obj_tag(v_tail_579_) == 1)
{
lean_object* v_head_587_; lean_object* v_tail_588_; uint32_t v___x_589_; uint32_t v___x_590_; uint8_t v___x_591_; 
v_head_587_ = lean_ctor_get(v_tail_579_, 0);
lean_inc(v_head_587_);
v_tail_588_ = lean_ctor_get(v_tail_579_, 1);
lean_inc(v_tail_588_);
lean_dec_ref_known(v_tail_579_, 2);
v___x_589_ = 58;
v___x_590_ = lean_unbox_uint32(v_head_587_);
lean_dec(v_head_587_);
v___x_591_ = lean_uint32_dec_eq(v___x_590_, v___x_589_);
if (v___x_591_ == 0)
{
lean_dec(v_tail_588_);
lean_dec(v_head_578_);
goto v___jp_564_;
}
else
{
if (lean_obj_tag(v_tail_588_) == 0)
{
uint32_t v___x_592_; uint32_t v___x_593_; uint8_t v___x_594_; 
v___x_592_ = 65;
v___x_593_ = lean_unbox_uint32(v_head_578_);
v___x_594_ = lean_uint32_dec_le(v___x_592_, v___x_593_);
if (v___x_594_ == 0)
{
goto v___jp_580_;
}
else
{
uint32_t v___x_595_; uint32_t v___x_596_; uint8_t v___x_597_; 
v___x_595_ = 90;
v___x_596_ = lean_unbox_uint32(v_head_578_);
v___x_597_ = lean_uint32_dec_le(v___x_596_, v___x_595_);
if (v___x_597_ == 0)
{
goto v___jp_580_;
}
else
{
lean_dec(v_head_578_);
goto v___jp_545_;
}
}
}
else
{
lean_dec(v_tail_588_);
lean_dec(v_head_578_);
goto v___jp_564_;
}
}
}
else
{
lean_dec(v_tail_579_);
lean_dec(v_head_578_);
goto v___jp_564_;
}
v___jp_580_:
{
uint32_t v___x_581_; uint32_t v___x_582_; uint8_t v___x_583_; 
v___x_581_ = 97;
v___x_582_ = lean_unbox_uint32(v_head_578_);
v___x_583_ = lean_uint32_dec_le(v___x_581_, v___x_582_);
if (v___x_583_ == 0)
{
lean_dec(v_head_578_);
goto v___jp_540_;
}
else
{
uint32_t v___x_584_; uint32_t v___x_585_; uint8_t v___x_586_; 
v___x_584_ = 122;
v___x_585_ = lean_unbox_uint32(v_head_578_);
lean_dec(v_head_578_);
v___x_586_ = lean_uint32_dec_le(v___x_585_, v___x_584_);
if (v___x_586_ == 0)
{
goto v___jp_540_;
}
else
{
goto v___jp_545_;
}
}
}
}
else
{
lean_dec(v_tail_574_);
goto v___jp_564_;
}
}
}
else
{
lean_dec(v___x_572_);
goto v___jp_564_;
}
v___jp_540_:
{
lean_object* v_str_541_; lean_object* v_startInclusive_542_; lean_object* v_endExclusive_543_; lean_object* v___x_544_; 
v_str_541_ = lean_ctor_get(v_p_539_, 0);
v_startInclusive_542_ = lean_ctor_get(v_p_539_, 1);
v_endExclusive_543_ = lean_ctor_get(v_p_539_, 2);
v___x_544_ = lean_string_utf8_extract_fast(v_str_541_, v_startInclusive_542_, v_endExclusive_543_);
return v___x_544_;
}
v___jp_545_:
{
lean_object* v_str_546_; lean_object* v_startInclusive_547_; lean_object* v_endExclusive_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; uint32_t v___x_554_; uint32_t v___x_555_; uint8_t v___x_556_; 
v_str_546_ = lean_ctor_get(v_p_539_, 0);
v_startInclusive_547_ = lean_ctor_get(v_p_539_, 1);
v_endExclusive_548_ = lean_ctor_get(v_p_539_, 2);
v___x_549_ = lean_unsigned_to_nat(1u);
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_551_ = l_String_Slice_Pos_nextn(v_p_539_, v___x_550_, v___x_549_);
v___x_552_ = lean_nat_add(v_startInclusive_547_, v___x_551_);
lean_dec(v___x_551_);
v___x_553_ = lean_string_utf8_extract_fast(v_str_546_, v___x_552_, v_endExclusive_548_);
lean_dec(v___x_552_);
v___x_554_ = lean_string_utf8_get(v___x_553_, v___x_550_);
v___x_555_ = 97;
v___x_556_ = lean_uint32_dec_le(v___x_555_, v___x_554_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; 
v___x_557_ = lean_string_utf8_set(v___x_553_, v___x_550_, v___x_554_);
return v___x_557_;
}
else
{
uint32_t v___x_558_; uint8_t v___x_559_; 
v___x_558_ = 122;
v___x_559_ = lean_uint32_dec_le(v___x_554_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; 
v___x_560_ = lean_string_utf8_set(v___x_553_, v___x_550_, v___x_554_);
return v___x_560_;
}
else
{
uint32_t v___x_561_; uint32_t v___x_562_; lean_object* v___x_563_; 
v___x_561_ = 4294967264;
v___x_562_ = lean_uint32_add(v___x_554_, v___x_561_);
v___x_563_ = lean_string_utf8_set(v___x_553_, v___x_550_, v___x_562_);
return v___x_563_;
}
}
}
v___jp_564_:
{
lean_object* v_str_565_; lean_object* v_startInclusive_566_; lean_object* v_endExclusive_567_; lean_object* v___x_568_; 
v_str_565_ = lean_ctor_get(v_p_539_, 0);
v_startInclusive_566_ = lean_ctor_get(v_p_539_, 1);
v_endExclusive_567_ = lean_ctor_get(v_p_539_, 2);
v___x_568_ = lean_string_utf8_extract_fast(v_str_565_, v_startInclusive_566_, v_endExclusive_567_);
return v___x_568_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression___boxed(lean_object* v_p_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression(v_p_598_);
lean_dec_ref(v_p_598_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0(lean_object* v_p_600_, lean_object* v_inst_601_, lean_object* v_R_602_, lean_object* v_a_603_, lean_object* v_b_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg(v_p_600_, v_a_603_, v_b_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___boxed(lean_object* v_p_606_, lean_object* v_inst_607_, lean_object* v_R_608_, lean_object* v_a_609_, lean_object* v_b_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0(v_p_606_, v_inst_607_, v_R_608_, v_a_609_, v_b_610_);
lean_dec_ref(v_p_606_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg(lean_object* v_s_612_){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_613_ = lean_string_utf8_byte_size(v_s_612_);
v___x_614_ = lean_unsigned_to_nat(7u);
v___x_615_ = lean_nat_dec_le(v___x_614_, v___x_613_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; 
lean_dec_ref(v_s_612_);
v___x_616_ = lean_box(0);
return v___x_616_;
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_617_ = ((lean_object*)(l_System_Uri_pathToUri___closed__2));
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = lean_string_memcmp(v_s_612_, v___x_617_, v___x_618_, v___x_618_, v___x_614_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
lean_dec_ref(v_s_612_);
v___x_620_ = lean_box(0);
return v___x_620_;
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
lean_inc_ref(v_s_612_);
v___x_621_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_621_, 0, v_s_612_);
lean_ctor_set(v___x_621_, 1, v___x_618_);
lean_ctor_set(v___x_621_, 2, v___x_613_);
v___x_622_ = l_String_Slice_pos_x21(v___x_621_, v___x_614_);
lean_dec_ref_known(v___x_621_, 3);
v___x_623_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_623_, 0, v_s_612_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
lean_ctor_set(v___x_623_, 2, v___x_613_);
v___x_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
return v___x_624_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0(lean_object* v_s_625_, lean_object* v_pat_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg(v_s_625_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___boxed(lean_object* v_s_628_, lean_object* v_pat_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0(v_s_628_, v_pat_629_);
lean_dec_ref(v_pat_629_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1(lean_object* v_s_631_, lean_object* v_pos_632_){
_start:
{
lean_object* v_str_633_; lean_object* v_startInclusive_634_; lean_object* v_endExclusive_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; uint8_t v_decide_639_; 
v_str_633_ = lean_ctor_get(v_s_631_, 0);
v_startInclusive_634_ = lean_ctor_get(v_s_631_, 1);
v_endExclusive_635_ = lean_ctor_get(v_s_631_, 2);
v___x_636_ = lean_nat_add(v_startInclusive_634_, v_pos_632_);
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = lean_nat_sub(v_endExclusive_635_, v___x_636_);
v_decide_639_ = lean_nat_dec_eq(v___x_637_, v___x_638_);
lean_dec(v___x_638_);
if (v_decide_639_ == 0)
{
uint32_t v___x_640_; uint32_t v___x_641_; uint8_t v___x_642_; 
v___x_640_ = lean_string_utf8_get_fast(v_str_633_, v___x_636_);
v___x_641_ = 47;
v___x_642_ = lean_uint32_dec_eq(v___x_640_, v___x_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_643_ = lean_string_utf8_next_fast(v_str_633_, v___x_636_);
v___x_644_ = lean_nat_sub(v___x_643_, v___x_636_);
lean_dec(v___x_636_);
v___x_645_ = lean_nat_add(v_pos_632_, v___x_644_);
lean_dec(v___x_644_);
v___x_646_ = lean_unsigned_to_nat(1u);
v___x_647_ = lean_nat_add(v_pos_632_, v___x_646_);
v___x_648_ = lean_nat_dec_le(v___x_647_, v___x_645_);
lean_dec(v___x_647_);
if (v___x_648_ == 0)
{
lean_dec(v___x_645_);
return v_pos_632_;
}
else
{
lean_dec(v_pos_632_);
v_pos_632_ = v___x_645_;
goto _start;
}
}
else
{
lean_dec(v___x_636_);
return v_pos_632_;
}
}
else
{
lean_dec(v___x_636_);
return v_pos_632_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1___boxed(lean_object* v_s_650_, lean_object* v_pos_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1(v_s_650_, v_pos_651_);
lean_dec_ref(v_s_650_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_Uri_fileUriToPath_x3f_spec__2(lean_object* v_s_653_, lean_object* v_p_654_){
_start:
{
uint32_t v___y_656_; lean_object* v___x_661_; uint8_t v_decide_662_; 
v___x_661_ = lean_string_utf8_byte_size(v_s_653_);
v_decide_662_ = lean_nat_dec_eq(v_p_654_, v___x_661_);
if (v_decide_662_ == 0)
{
uint32_t v___x_663_; uint32_t v___x_664_; uint8_t v___x_665_; 
v___x_663_ = lean_string_utf8_get_fast(v_s_653_, v_p_654_);
v___x_664_ = 47;
v___x_665_ = lean_uint32_dec_eq(v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
v___y_656_ = v___x_663_;
goto v___jp_655_;
}
else
{
uint32_t v___x_666_; 
v___x_666_ = 92;
v___y_656_ = v___x_666_;
goto v___jp_655_;
}
}
else
{
lean_dec(v_p_654_);
return v_s_653_;
}
v___jp_655_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
lean_inc(v_p_654_);
v___x_657_ = lean_string_utf8_set(v_s_653_, v_p_654_, v___y_656_);
v___x_658_ = l_Char_utf8Size(v___y_656_);
v___x_659_ = lean_nat_add(v_p_654_, v___x_658_);
lean_dec(v___x_658_);
lean_dec(v_p_654_);
v_s_653_ = v___x_657_;
v_p_654_ = v___x_659_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_fileUriToPath_x3f(lean_object* v_uri_667_){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = l_System_Uri_UriEscape_decodeUri(v_uri_667_);
v___x_669_ = l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg(v___x_668_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v___x_670_; 
v___x_670_ = lean_box(0);
return v___x_670_;
}
else
{
lean_object* v_val_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_701_; 
v_val_671_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_701_ == 0)
{
v___x_673_ = v___x_669_;
v_isShared_674_ = v_isSharedCheck_701_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_val_671_);
lean_dec(v___x_669_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_701_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v_str_675_; lean_object* v_startInclusive_676_; lean_object* v_endExclusive_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_697_; 
v_str_675_ = lean_ctor_get(v_val_671_, 0);
lean_inc_ref(v_str_675_);
v_startInclusive_676_ = lean_ctor_get(v_val_671_, 1);
lean_inc(v_startInclusive_676_);
v_endExclusive_677_ = lean_ctor_get(v_val_671_, 2);
lean_inc(v_endExclusive_677_);
v___x_678_ = lean_unsigned_to_nat(0u);
v___x_679_ = l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1(v_val_671_, v___x_678_);
v_isSharedCheck_697_ = !lean_is_exclusive(v_val_671_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; lean_object* v_unused_699_; lean_object* v_unused_700_; 
v_unused_698_ = lean_ctor_get(v_val_671_, 2);
lean_dec(v_unused_698_);
v_unused_699_ = lean_ctor_get(v_val_671_, 1);
lean_dec(v_unused_699_);
v_unused_700_ = lean_ctor_get(v_val_671_, 0);
lean_dec(v_unused_700_);
v___x_681_ = v_val_671_;
v_isShared_682_ = v_isSharedCheck_697_;
goto v_resetjp_680_;
}
else
{
lean_dec(v_val_671_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_697_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_683_ = lean_nat_add(v_startInclusive_676_, v___x_679_);
lean_dec(v___x_679_);
lean_dec(v_startInclusive_676_);
v___x_684_ = l_System_Platform_isWindows;
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_687_; 
lean_del_object(v___x_681_);
v___x_685_ = lean_string_utf8_extract_fast(v_str_675_, v___x_683_, v_endExclusive_677_);
lean_dec(v_endExclusive_677_);
lean_dec(v___x_683_);
lean_dec_ref(v_str_675_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v___x_685_);
v___x_687_ = v___x_673_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
else
{
lean_object* v_p_690_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v___x_683_);
v_p_690_ = v___x_681_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_str_675_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_696_, 2, v_endExclusive_677_);
v_p_690_ = v_reuseFailAlloc_696_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_691_ = l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression(v_p_690_);
lean_dec_ref(v_p_690_);
v___x_692_ = l_String_mapAux___at___00System_Uri_fileUriToPath_x3f_spec__2(v___x_691_, v___x_678_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v___x_692_);
v___x_694_ = v___x_673_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_fileUriToPath_x3f___boxed(lean_object* v_uri_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_System_Uri_fileUriToPath_x3f(v_uri_702_);
lean_dec_ref(v_uri_702_);
return v_res_703_;
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
