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
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_byte_array_uget(lean_object*, size_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_uint8_shift_right(uint8_t, uint8_t);
uint8_t lean_uint8_mod(uint8_t, uint8_t);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l_hexDigitRepr(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
extern uint8_t l_System_Platform_isWindows;
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t lean_uint8_of_nat(lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
size_t lean_usize_of_nat(lean_object*);
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
static const lean_string_object l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "%"};
static const lean_object* l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1___closed__0 = (const lean_object*)&l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_uriEscapeAsciiChar(uint32_t);
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_uriEscapeAsciiChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_escapeUri(lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_escapeUri___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_unescapeUri(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0(lean_object* v_len_133_, lean_object* v_rawBytes_134_, lean_object* v_inst_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___redArg(v_len_133_, v_rawBytes_134_, v_a_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0___boxed(lean_object* v_len_138_, lean_object* v_rawBytes_139_, lean_object* v_inst_140_, lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Init_While_0__repeatM_erased___at___00System_Uri_UriEscape_decodeUri_spec__0(v_len_138_, v_rawBytes_139_, v_inst_140_, v_a_141_);
lean_dec_ref(v_rawBytes_139_);
lean_dec(v_len_138_);
return v_res_142_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_143_; lean_object* v___x_144_; 
v___x_143_ = 32;
v___x_144_ = lean_box_uint32(v___x_143_);
return v___x_144_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_box(0);
v___x_146_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0___boxed__const__1;
v___x_147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v___x_145_);
return v___x_147_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_148_; lean_object* v___x_149_; 
v___x_148_ = 37;
v___x_149_ = lean_box_uint32(v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0);
v___x_151_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1___boxed__const__1;
v___x_152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v___x_150_);
return v___x_152_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_153_; lean_object* v___x_154_; 
v___x_153_ = 42;
v___x_154_ = lean_box_uint32(v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1);
v___x_156_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2___boxed__const__1;
v___x_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_155_);
return v___x_157_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_158_; lean_object* v___x_159_; 
v___x_158_ = 41;
v___x_159_ = lean_box_uint32(v___x_158_);
return v___x_159_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2);
v___x_161_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3___boxed__const__1;
v___x_162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v___x_160_);
return v___x_162_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4___boxed__const__1(void){
_start:
{
uint32_t v___x_163_; lean_object* v___x_164_; 
v___x_163_ = 40;
v___x_164_ = lean_box_uint32(v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3);
v___x_166_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4___boxed__const__1;
v___x_167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v___x_165_);
return v___x_167_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5___boxed__const__1(void){
_start:
{
uint32_t v___x_168_; lean_object* v___x_169_; 
v___x_168_ = 39;
v___x_169_ = lean_box_uint32(v___x_168_);
return v___x_169_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4);
v___x_171_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5___boxed__const__1;
v___x_172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v___x_170_);
return v___x_172_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6___boxed__const__1(void){
_start:
{
uint32_t v___x_173_; lean_object* v___x_174_; 
v___x_173_ = 33;
v___x_174_ = lean_box_uint32(v___x_173_);
return v___x_174_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5);
v___x_176_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6___boxed__const__1;
v___x_177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v___x_175_);
return v___x_177_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7___boxed__const__1(void){
_start:
{
uint32_t v___x_178_; lean_object* v___x_179_; 
v___x_178_ = 44;
v___x_179_ = lean_box_uint32(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6);
v___x_181_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7___boxed__const__1;
v___x_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___x_180_);
return v___x_182_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8___boxed__const__1(void){
_start:
{
uint32_t v___x_183_; lean_object* v___x_184_; 
v___x_183_ = 36;
v___x_184_ = lean_box_uint32(v___x_183_);
return v___x_184_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7);
v___x_186_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8___boxed__const__1;
v___x_187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v___x_185_);
return v___x_187_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9___boxed__const__1(void){
_start:
{
uint32_t v___x_188_; lean_object* v___x_189_; 
v___x_188_ = 43;
v___x_189_ = lean_box_uint32(v___x_188_);
return v___x_189_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8);
v___x_191_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9___boxed__const__1;
v___x_192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_190_);
return v___x_192_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10___boxed__const__1(void){
_start:
{
uint32_t v___x_193_; lean_object* v___x_194_; 
v___x_193_ = 61;
v___x_194_ = lean_box_uint32(v___x_193_);
return v___x_194_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9);
v___x_196_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10___boxed__const__1;
v___x_197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set(v___x_197_, 1, v___x_195_);
return v___x_197_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11___boxed__const__1(void){
_start:
{
uint32_t v___x_198_; lean_object* v___x_199_; 
v___x_198_ = 38;
v___x_199_ = lean_box_uint32(v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10);
v___x_201_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11___boxed__const__1;
v___x_202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v___x_200_);
return v___x_202_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12___boxed__const__1(void){
_start:
{
uint32_t v___x_203_; lean_object* v___x_204_; 
v___x_203_ = 64;
v___x_204_ = lean_box_uint32(v___x_203_);
return v___x_204_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11);
v___x_206_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12___boxed__const__1;
v___x_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v___x_205_);
return v___x_207_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13___boxed__const__1(void){
_start:
{
uint32_t v___x_208_; lean_object* v___x_209_; 
v___x_208_ = 93;
v___x_209_ = lean_box_uint32(v___x_208_);
return v___x_209_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12);
v___x_211_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13___boxed__const__1;
v___x_212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v___x_210_);
return v___x_212_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14___boxed__const__1(void){
_start:
{
uint32_t v___x_213_; lean_object* v___x_214_; 
v___x_213_ = 91;
v___x_214_ = lean_box_uint32(v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13);
v___x_216_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14___boxed__const__1;
v___x_217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v___x_215_);
return v___x_217_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15___boxed__const__1(void){
_start:
{
uint32_t v___x_218_; lean_object* v___x_219_; 
v___x_218_ = 35;
v___x_219_ = lean_box_uint32(v___x_218_);
return v___x_219_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_220_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14);
v___x_221_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15___boxed__const__1;
v___x_222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
return v___x_222_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16___boxed__const__1(void){
_start:
{
uint32_t v___x_223_; lean_object* v___x_224_; 
v___x_223_ = 63;
v___x_224_ = lean_box_uint32(v___x_223_);
return v___x_224_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_225_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15);
v___x_226_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16___boxed__const__1;
v___x_227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v___x_225_);
return v___x_227_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17___boxed__const__1(void){
_start:
{
uint32_t v___x_228_; lean_object* v___x_229_; 
v___x_228_ = 58;
v___x_229_ = lean_box_uint32(v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16);
v___x_231_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17___boxed__const__1;
v___x_232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_230_);
return v___x_232_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18___boxed__const__1(void){
_start:
{
uint32_t v___x_233_; lean_object* v___x_234_; 
v___x_233_ = 59;
v___x_234_ = lean_box_uint32(v___x_233_);
return v___x_234_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17);
v___x_236_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18___boxed__const__1;
v___x_237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v___x_235_);
return v___x_237_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars(void){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex_spec__0(lean_object* v_s_239_, lean_object* v_p_240_){
_start:
{
lean_object* v___y_242_; lean_object* v___y_243_; uint32_t v___y_247_; lean_object* v___x_259_; uint8_t v_decide_260_; 
v___x_259_ = lean_string_utf8_byte_size(v_s_239_);
v_decide_260_ = lean_nat_dec_eq(v_p_240_, v___x_259_);
if (v_decide_260_ == 0)
{
uint32_t v___x_261_; uint32_t v___x_262_; uint8_t v___x_263_; 
v___x_261_ = lean_string_utf8_get_fast(v_s_239_, v_p_240_);
v___x_262_ = 97;
v___x_263_ = lean_uint32_dec_le(v___x_262_, v___x_261_);
if (v___x_263_ == 0)
{
v___y_247_ = v___x_261_;
goto v___jp_246_;
}
else
{
uint32_t v___x_264_; uint8_t v___x_265_; 
v___x_264_ = 122;
v___x_265_ = lean_uint32_dec_le(v___x_261_, v___x_264_);
if (v___x_265_ == 0)
{
v___y_247_ = v___x_261_;
goto v___jp_246_;
}
else
{
uint32_t v___x_266_; uint32_t v___x_267_; 
v___x_266_ = 4294967264;
v___x_267_ = lean_uint32_add(v___x_261_, v___x_266_);
v___y_247_ = v___x_267_;
goto v___jp_246_;
}
}
}
else
{
lean_dec(v_p_240_);
return v_s_239_;
}
v___jp_241_:
{
lean_object* v___x_244_; 
v___x_244_ = lean_nat_add(v_p_240_, v___y_243_);
lean_dec(v_p_240_);
v_s_239_ = v___y_242_;
v_p_240_ = v___x_244_;
goto _start;
}
v___jp_246_:
{
lean_object* v___x_248_; uint32_t v___x_249_; uint8_t v___x_250_; 
lean_inc(v_p_240_);
v___x_248_ = lean_string_utf8_set(v_s_239_, v_p_240_, v___y_247_);
v___x_249_ = 127;
v___x_250_ = lean_uint32_dec_le(v___y_247_, v___x_249_);
if (v___x_250_ == 0)
{
uint32_t v___x_251_; uint8_t v___x_252_; 
v___x_251_ = 2047;
v___x_252_ = lean_uint32_dec_le(v___y_247_, v___x_251_);
if (v___x_252_ == 0)
{
uint32_t v___x_253_; uint8_t v___x_254_; 
v___x_253_ = 65535;
v___x_254_ = lean_uint32_dec_le(v___y_247_, v___x_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
v___x_255_ = lean_unsigned_to_nat(4u);
v___y_242_ = v___x_248_;
v___y_243_ = v___x_255_;
goto v___jp_241_;
}
else
{
lean_object* v___x_256_; 
v___x_256_ = lean_unsigned_to_nat(3u);
v___y_242_ = v___x_248_;
v___y_243_ = v___x_256_;
goto v___jp_241_;
}
}
else
{
lean_object* v___x_257_; 
v___x_257_ = lean_unsigned_to_nat(2u);
v___y_242_ = v___x_248_;
v___y_243_ = v___x_257_;
goto v___jp_241_;
}
}
else
{
lean_object* v___x_258_; 
v___x_258_ = lean_unsigned_to_nat(1u);
v___y_242_ = v___x_248_;
v___y_243_ = v___x_258_;
goto v___jp_241_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(uint8_t v_c_268_){
_start:
{
uint8_t v___x_269_; uint8_t v___x_270_; uint8_t v_d2_271_; uint8_t v_d1_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_269_ = 16;
v___x_270_ = 4;
v_d2_271_ = lean_uint8_shift_right(v_c_268_, v___x_270_);
v_d1_272_ = lean_uint8_mod(v_c_268_, v___x_269_);
v___x_273_ = lean_uint8_to_nat(v_d2_271_);
v___x_274_ = l_hexDigitRepr(v___x_273_);
v___x_275_ = lean_uint8_to_nat(v_d1_272_);
v___x_276_ = l_hexDigitRepr(v___x_275_);
v___x_277_ = lean_string_append(v___x_274_, v___x_276_);
lean_dec_ref(v___x_276_);
v___x_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = l_String_mapAux___at___00__private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex_spec__0(v___x_277_, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex___boxed(lean_object* v_c_280_){
_start:
{
uint8_t v_c_boxed_281_; lean_object* v_res_282_; 
v_c_boxed_281_ = lean_unbox(v_c_280_);
v_res_282_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(v_c_boxed_281_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1(lean_object* v_as_284_, size_t v_i_285_, size_t v_stop_286_, lean_object* v_b_287_){
_start:
{
uint8_t v___x_288_; 
v___x_288_ = lean_usize_dec_eq(v_i_285_, v_stop_286_);
if (v___x_288_ == 0)
{
uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; size_t v___x_294_; size_t v___x_295_; 
v___x_289_ = lean_byte_array_uget(v_as_284_, v_i_285_);
v___x_290_ = ((lean_object*)(l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1___closed__0));
v___x_291_ = lean_string_append(v_b_287_, v___x_290_);
v___x_292_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(v___x_289_);
v___x_293_ = lean_string_append(v___x_291_, v___x_292_);
lean_dec_ref(v___x_292_);
v___x_294_ = ((size_t)1ULL);
v___x_295_ = lean_usize_add(v_i_285_, v___x_294_);
v_i_285_ = v___x_295_;
v_b_287_ = v___x_293_;
goto _start;
}
else
{
return v_b_287_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1___boxed(lean_object* v_as_297_, lean_object* v_i_298_, lean_object* v_stop_299_, lean_object* v_b_300_){
_start:
{
size_t v_i_boxed_301_; size_t v_stop_boxed_302_; lean_object* v_res_303_; 
v_i_boxed_301_ = lean_unbox_usize(v_i_298_);
lean_dec(v_i_298_);
v_stop_boxed_302_ = lean_unbox_usize(v_stop_299_);
lean_dec(v_stop_299_);
v_res_303_ = l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1(v_as_297_, v_i_boxed_301_, v_stop_boxed_302_, v_b_300_);
lean_dec_ref(v_as_297_);
return v_res_303_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(uint32_t v_a_304_, lean_object* v_x_305_){
_start:
{
if (lean_obj_tag(v_x_305_) == 0)
{
uint8_t v___x_306_; 
v___x_306_ = 0;
return v___x_306_;
}
else
{
lean_object* v_head_307_; lean_object* v_tail_308_; uint32_t v___x_309_; uint8_t v___x_310_; 
v_head_307_ = lean_ctor_get(v_x_305_, 0);
v_tail_308_ = lean_ctor_get(v_x_305_, 1);
v___x_309_ = lean_unbox_uint32(v_head_307_);
v___x_310_ = lean_uint32_dec_eq(v_a_304_, v___x_309_);
if (v___x_310_ == 0)
{
v_x_305_ = v_tail_308_;
goto _start;
}
else
{
return v___x_310_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___boxed(lean_object* v_a_312_, lean_object* v_x_313_){
_start:
{
uint32_t v_a_boxed_314_; uint8_t v_res_315_; lean_object* v_r_316_; 
v_a_boxed_314_ = lean_unbox_uint32(v_a_312_);
lean_dec(v_a_312_);
v_res_315_ = l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(v_a_boxed_314_, v_x_313_);
lean_dec(v_x_313_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_uriEscapeAsciiChar(uint32_t v_c_317_){
_start:
{
lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_324_ = l_System_Uri_UriEscape_rfc3986ReservedChars;
v___x_325_ = l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(v_c_317_, v___x_324_);
if (v___x_325_ == 0)
{
uint32_t v___x_326_; uint8_t v___x_327_; 
v___x_326_ = 32;
v___x_327_ = lean_uint32_dec_lt(v_c_317_, v___x_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_328_ = lean_uint32_to_nat(v_c_317_);
v___x_329_ = lean_unsigned_to_nat(127u);
v___x_330_ = lean_nat_dec_lt(v___x_328_, v___x_329_);
lean_dec(v___x_328_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_331_ = ((lean_object*)(l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0));
v___x_332_ = lean_string_push(v___x_331_, v_c_317_);
v___x_333_ = lean_string_to_utf8(v___x_332_);
v___x_334_ = lean_unsigned_to_nat(0u);
v___x_335_ = lean_byte_array_size(v___x_333_);
v___x_336_ = lean_nat_dec_lt(v___x_334_, v___x_335_);
if (v___x_336_ == 0)
{
lean_dec_ref(v___x_333_);
return v___x_331_;
}
else
{
size_t v___x_337_; size_t v___x_338_; lean_object* v___x_339_; 
v___x_337_ = ((size_t)0ULL);
v___x_338_ = lean_usize_of_nat(v___x_335_);
v___x_339_ = l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1(v___x_333_, v___x_337_, v___x_338_, v___x_331_);
lean_dec_ref(v___x_333_);
return v___x_339_;
}
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = ((lean_object*)(l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0));
v___x_341_ = lean_string_push(v___x_340_, v_c_317_);
return v___x_341_;
}
}
else
{
goto v___jp_318_;
}
}
else
{
goto v___jp_318_;
}
v___jp_318_:
{
lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_319_ = ((lean_object*)(l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1___closed__0));
v___x_320_ = lean_uint32_to_nat(v_c_317_);
v___x_321_ = lean_uint8_of_nat(v___x_320_);
lean_dec(v___x_320_);
v___x_322_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(v___x_321_);
v___x_323_ = lean_string_append(v___x_319_, v___x_322_);
lean_dec_ref(v___x_322_);
return v___x_323_;
}
}
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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg(lean_object* v_uri_387_, lean_object* v___x_388_, lean_object* v_a_389_, lean_object* v_b_390_){
_start:
{
lean_object* v_countdown_391_; lean_object* v_inner_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_408_; 
v_countdown_391_ = lean_ctor_get(v_a_389_, 0);
v_inner_392_ = lean_ctor_get(v_a_389_, 1);
v_isSharedCheck_408_ = !lean_is_exclusive(v_a_389_);
if (v_isSharedCheck_408_ == 0)
{
v___x_394_ = v_a_389_;
v_isShared_395_ = v_isSharedCheck_408_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_inner_392_);
lean_inc(v_countdown_391_);
lean_dec(v_a_389_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_408_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = lean_nat_dec_eq(v_countdown_391_, v___x_396_);
if (v___x_397_ == 0)
{
uint8_t v_decide_398_; 
v_decide_398_ = lean_nat_dec_eq(v_inner_392_, v___x_388_);
if (v_decide_398_ == 0)
{
lean_object* v___x_399_; uint32_t v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_399_ = lean_string_utf8_next_fast(v_uri_387_, v_inner_392_);
v___x_400_ = lean_string_utf8_get_fast(v_uri_387_, v_inner_392_);
lean_dec(v_inner_392_);
v___x_401_ = lean_nat_sub(v_countdown_391_, v___x_396_);
lean_dec(v_countdown_391_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 1, v___x_399_);
lean_ctor_set(v___x_394_, 0, v___x_401_);
v___x_403_ = v___x_394_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v___x_399_);
v___x_403_ = v_reuseFailAlloc_407_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_box_uint32(v___x_400_);
v___x_405_ = lean_array_push(v_b_390_, v___x_404_);
v_a_389_ = v___x_403_;
v_b_390_ = v___x_405_;
goto _start;
}
}
else
{
lean_del_object(v___x_394_);
lean_dec(v_inner_392_);
lean_dec(v_countdown_391_);
return v_b_390_;
}
}
else
{
lean_del_object(v___x_394_);
lean_dec(v_inner_392_);
lean_dec(v_countdown_391_);
return v_b_390_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg___boxed(lean_object* v_uri_409_, lean_object* v___x_410_, lean_object* v_a_411_, lean_object* v_b_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg(v_uri_409_, v___x_410_, v_a_411_, v_b_412_);
lean_dec(v___x_410_);
lean_dec_ref(v_uri_409_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter(lean_object* v_uri_419_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = lean_string_utf8_byte_size(v_uri_419_);
v___x_422_ = ((lean_object*)(l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__0));
v___x_423_ = ((lean_object*)(l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__1));
v___x_424_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg(v_uri_419_, v___x_421_, v___x_422_, v___x_423_);
v___x_425_ = lean_array_to_list(v___x_424_);
if (lean_obj_tag(v___x_425_) == 1)
{
lean_object* v_tail_426_; 
v_tail_426_ = lean_ctor_get(v___x_425_, 1);
lean_inc(v_tail_426_);
if (lean_obj_tag(v_tail_426_) == 1)
{
lean_object* v_head_427_; lean_object* v_head_428_; lean_object* v_tail_429_; uint32_t v___x_430_; uint32_t v___x_431_; uint8_t v___x_432_; 
v_head_427_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_head_427_);
lean_dec_ref_known(v___x_425_, 2);
v_head_428_ = lean_ctor_get(v_tail_426_, 0);
lean_inc(v_head_428_);
v_tail_429_ = lean_ctor_get(v_tail_426_, 1);
lean_inc(v_tail_429_);
lean_dec_ref_known(v_tail_426_, 2);
v___x_430_ = 58;
v___x_431_ = lean_unbox_uint32(v_head_428_);
lean_dec(v_head_428_);
v___x_432_ = lean_uint32_dec_eq(v___x_431_, v___x_430_);
if (v___x_432_ == 0)
{
lean_dec(v_tail_429_);
lean_dec(v_head_427_);
return v_uri_419_;
}
else
{
if (lean_obj_tag(v_tail_429_) == 0)
{
uint32_t v___x_433_; uint32_t v___x_434_; uint8_t v___x_435_; 
v___x_433_ = 65;
v___x_434_ = lean_unbox_uint32(v_head_427_);
v___x_435_ = lean_uint32_dec_le(v___x_433_, v___x_434_);
if (v___x_435_ == 0)
{
lean_dec(v_head_427_);
return v_uri_419_;
}
else
{
uint32_t v___x_436_; uint32_t v___x_437_; uint8_t v___x_438_; 
v___x_436_ = 90;
v___x_437_ = lean_unbox_uint32(v_head_427_);
lean_dec(v_head_427_);
v___x_438_ = lean_uint32_dec_le(v___x_437_, v___x_436_);
if (v___x_438_ == 0)
{
return v_uri_419_;
}
else
{
uint32_t v___x_439_; uint8_t v___x_440_; 
v___x_439_ = lean_string_utf8_get(v_uri_419_, v___x_420_);
v___x_440_ = lean_uint32_dec_le(v___x_433_, v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; 
v___x_441_ = lean_string_utf8_set(v_uri_419_, v___x_420_, v___x_439_);
return v___x_441_;
}
else
{
uint8_t v___x_442_; 
v___x_442_ = lean_uint32_dec_le(v___x_439_, v___x_436_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; 
v___x_443_ = lean_string_utf8_set(v_uri_419_, v___x_420_, v___x_439_);
return v___x_443_;
}
else
{
uint32_t v___x_444_; uint32_t v___x_445_; lean_object* v___x_446_; 
v___x_444_ = 32;
v___x_445_ = lean_uint32_add(v___x_439_, v___x_444_);
v___x_446_ = lean_string_utf8_set(v_uri_419_, v___x_420_, v___x_445_);
return v___x_446_;
}
}
}
}
}
else
{
lean_dec(v_tail_429_);
lean_dec(v_head_427_);
return v_uri_419_;
}
}
}
else
{
lean_dec(v_tail_426_);
lean_dec_ref_known(v___x_425_, 2);
return v_uri_419_;
}
}
else
{
lean_dec(v___x_425_);
return v_uri_419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0(lean_object* v___x_447_, lean_object* v_uri_448_, lean_object* v___x_449_, lean_object* v_inst_450_, lean_object* v_R_451_, lean_object* v_a_452_, lean_object* v_b_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___redArg(v_uri_448_, v___x_449_, v_a_452_, v_b_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0___boxed(lean_object* v___x_455_, lean_object* v_uri_456_, lean_object* v___x_457_, lean_object* v_inst_458_, lean_object* v_R_459_, lean_object* v_a_460_, lean_object* v_b_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveLetter_spec__0(v___x_455_, v_uri_456_, v___x_457_, v_inst_458_, v_R_459_, v_a_460_, v_b_461_);
lean_dec(v___x_457_);
lean_dec_ref(v_uri_456_);
lean_dec_ref(v___x_455_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_Uri_pathToUri_spec__0(lean_object* v_s_463_, lean_object* v_p_464_){
_start:
{
lean_object* v___y_466_; lean_object* v___y_467_; uint32_t v___y_471_; lean_object* v___x_483_; uint8_t v_decide_484_; 
v___x_483_ = lean_string_utf8_byte_size(v_s_463_);
v_decide_484_ = lean_nat_dec_eq(v_p_464_, v___x_483_);
if (v_decide_484_ == 0)
{
uint32_t v___x_485_; uint32_t v___x_486_; uint8_t v___x_487_; 
v___x_485_ = lean_string_utf8_get_fast(v_s_463_, v_p_464_);
v___x_486_ = 92;
v___x_487_ = lean_uint32_dec_eq(v___x_485_, v___x_486_);
if (v___x_487_ == 0)
{
v___y_471_ = v___x_485_;
goto v___jp_470_;
}
else
{
uint32_t v___x_488_; 
v___x_488_ = 47;
v___y_471_ = v___x_488_;
goto v___jp_470_;
}
}
else
{
lean_dec(v_p_464_);
return v_s_463_;
}
v___jp_465_:
{
lean_object* v___x_468_; 
v___x_468_ = lean_nat_add(v_p_464_, v___y_467_);
lean_dec(v_p_464_);
v_s_463_ = v___y_466_;
v_p_464_ = v___x_468_;
goto _start;
}
v___jp_470_:
{
lean_object* v___x_472_; uint32_t v___x_473_; uint8_t v___x_474_; 
lean_inc(v_p_464_);
v___x_472_ = lean_string_utf8_set(v_s_463_, v_p_464_, v___y_471_);
v___x_473_ = 127;
v___x_474_ = lean_uint32_dec_le(v___y_471_, v___x_473_);
if (v___x_474_ == 0)
{
uint32_t v___x_475_; uint8_t v___x_476_; 
v___x_475_ = 2047;
v___x_476_ = lean_uint32_dec_le(v___y_471_, v___x_475_);
if (v___x_476_ == 0)
{
uint32_t v___x_477_; uint8_t v___x_478_; 
v___x_477_ = 65535;
v___x_478_ = lean_uint32_dec_le(v___y_471_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; 
v___x_479_ = lean_unsigned_to_nat(4u);
v___y_466_ = v___x_472_;
v___y_467_ = v___x_479_;
goto v___jp_465_;
}
else
{
lean_object* v___x_480_; 
v___x_480_ = lean_unsigned_to_nat(3u);
v___y_466_ = v___x_472_;
v___y_467_ = v___x_480_;
goto v___jp_465_;
}
}
else
{
lean_object* v___x_481_; 
v___x_481_ = lean_unsigned_to_nat(2u);
v___y_466_ = v___x_472_;
v___y_467_ = v___x_481_;
goto v___jp_465_;
}
}
else
{
lean_object* v___x_482_; 
v___x_482_ = lean_unsigned_to_nat(1u);
v___y_466_ = v___x_472_;
v___y_467_ = v___x_482_;
goto v___jp_465_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_pathToUri(lean_object* v_fname_492_){
_start:
{
lean_object* v___y_494_; lean_object* v_uri_498_; lean_object* v_uri_510_; uint8_t v___x_511_; 
v_uri_510_ = l_System_FilePath_normalize(v_fname_492_);
v___x_511_ = l_System_Platform_isWindows;
if (v___x_511_ == 0)
{
v_uri_498_ = v_uri_510_;
goto v___jp_497_;
}
else
{
lean_object* v_uri_512_; lean_object* v___x_513_; lean_object* v_uri_514_; 
v_uri_512_ = l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter(v_uri_510_);
v___x_513_ = lean_unsigned_to_nat(0u);
v_uri_514_ = l_String_mapAux___at___00System_Uri_pathToUri_spec__0(v_uri_512_, v___x_513_);
v_uri_498_ = v_uri_514_;
goto v___jp_497_;
}
v___jp_493_:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = ((lean_object*)(l_System_Uri_pathToUri___closed__0));
v___x_496_ = lean_string_append(v___x_495_, v___y_494_);
lean_dec_ref(v___y_494_);
return v___x_496_;
}
v___jp_497_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v_uri_502_; lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_499_ = ((lean_object*)(l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0));
v___x_500_ = lean_string_utf8_byte_size(v_uri_498_);
v___x_501_ = lean_unsigned_to_nat(0u);
v_uri_502_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(v___x_500_, v_uri_498_, v___x_501_, v___x_499_);
lean_dec_ref(v_uri_498_);
v___x_503_ = lean_string_utf8_byte_size(v_uri_502_);
v___x_504_ = lean_unsigned_to_nat(1u);
v___x_505_ = lean_nat_dec_le(v___x_504_, v___x_503_);
if (v___x_505_ == 0)
{
v___y_494_ = v_uri_502_;
goto v___jp_493_;
}
else
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = ((lean_object*)(l_System_Uri_pathToUri___closed__1));
v___x_507_ = lean_string_memcmp(v_uri_502_, v___x_506_, v___x_501_, v___x_501_, v___x_504_);
if (v___x_507_ == 0)
{
v___y_494_ = v_uri_502_;
goto v___jp_493_;
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = ((lean_object*)(l_System_Uri_pathToUri___closed__2));
v___x_509_ = lean_string_append(v___x_508_, v_uri_502_);
lean_dec_ref(v_uri_502_);
return v___x_509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg(lean_object* v_p_515_, lean_object* v_a_516_, lean_object* v_b_517_){
_start:
{
lean_object* v_countdown_518_; lean_object* v_inner_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_541_; 
v_countdown_518_ = lean_ctor_get(v_a_516_, 0);
v_inner_519_ = lean_ctor_get(v_a_516_, 1);
v_isSharedCheck_541_ = !lean_is_exclusive(v_a_516_);
if (v_isSharedCheck_541_ == 0)
{
v___x_521_ = v_a_516_;
v_isShared_522_ = v_isSharedCheck_541_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_inner_519_);
lean_inc(v_countdown_518_);
lean_dec(v_a_516_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_541_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_nat_dec_eq(v_countdown_518_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v_str_525_; lean_object* v_startInclusive_526_; lean_object* v_endExclusive_527_; lean_object* v___x_528_; uint8_t v_decide_529_; 
v_str_525_ = lean_ctor_get(v_p_515_, 0);
v_startInclusive_526_ = lean_ctor_get(v_p_515_, 1);
v_endExclusive_527_ = lean_ctor_get(v_p_515_, 2);
v___x_528_ = lean_nat_sub(v_endExclusive_527_, v_startInclusive_526_);
v_decide_529_ = lean_nat_dec_eq(v_inner_519_, v___x_528_);
lean_dec(v___x_528_);
if (v_decide_529_ == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; uint32_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_530_ = lean_nat_add(v_startInclusive_526_, v_inner_519_);
lean_dec(v_inner_519_);
v___x_531_ = lean_string_utf8_next_fast(v_str_525_, v___x_530_);
v___x_532_ = lean_nat_sub(v___x_531_, v_startInclusive_526_);
v___x_533_ = lean_string_utf8_get_fast(v_str_525_, v___x_530_);
lean_dec(v___x_530_);
v___x_534_ = lean_nat_sub(v_countdown_518_, v___x_523_);
lean_dec(v_countdown_518_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v___x_532_);
lean_ctor_set(v___x_521_, 0, v___x_534_);
v___x_536_ = v___x_521_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v___x_532_);
v___x_536_ = v_reuseFailAlloc_540_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_box_uint32(v___x_533_);
v___x_538_ = lean_array_push(v_b_517_, v___x_537_);
v_a_516_ = v___x_536_;
v_b_517_ = v___x_538_;
goto _start;
}
}
else
{
lean_del_object(v___x_521_);
lean_dec(v_inner_519_);
lean_dec(v_countdown_518_);
return v_b_517_;
}
}
else
{
lean_del_object(v___x_521_);
lean_dec(v_inner_519_);
lean_dec(v_countdown_518_);
return v_b_517_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg___boxed(lean_object* v_p_542_, lean_object* v_a_543_, lean_object* v_b_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg(v_p_542_, v_a_543_, v_b_544_);
lean_dec_ref(v_p_542_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression(lean_object* v_p_549_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_579_ = ((lean_object*)(l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression___closed__0));
v___x_580_ = ((lean_object*)(l___private_Init_System_Uri_0__System_Uri_normalizeDriveLetter___closed__1));
v___x_581_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg(v_p_549_, v___x_579_, v___x_580_);
v___x_582_ = lean_array_to_list(v___x_581_);
if (lean_obj_tag(v___x_582_) == 1)
{
lean_object* v_head_583_; lean_object* v_tail_584_; uint32_t v___x_585_; uint32_t v___x_586_; uint8_t v___x_587_; 
v_head_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_head_583_);
v_tail_584_ = lean_ctor_get(v___x_582_, 1);
lean_inc(v_tail_584_);
lean_dec_ref_known(v___x_582_, 2);
v___x_585_ = 47;
v___x_586_ = lean_unbox_uint32(v_head_583_);
lean_dec(v_head_583_);
v___x_587_ = lean_uint32_dec_eq(v___x_586_, v___x_585_);
if (v___x_587_ == 0)
{
lean_dec(v_tail_584_);
goto v___jp_574_;
}
else
{
if (lean_obj_tag(v_tail_584_) == 1)
{
lean_object* v_head_588_; lean_object* v_tail_589_; 
v_head_588_ = lean_ctor_get(v_tail_584_, 0);
lean_inc(v_head_588_);
v_tail_589_ = lean_ctor_get(v_tail_584_, 1);
lean_inc(v_tail_589_);
lean_dec_ref_known(v_tail_584_, 2);
if (lean_obj_tag(v_tail_589_) == 1)
{
lean_object* v_head_597_; lean_object* v_tail_598_; uint32_t v___x_599_; uint32_t v___x_600_; uint8_t v___x_601_; 
v_head_597_ = lean_ctor_get(v_tail_589_, 0);
lean_inc(v_head_597_);
v_tail_598_ = lean_ctor_get(v_tail_589_, 1);
lean_inc(v_tail_598_);
lean_dec_ref_known(v_tail_589_, 2);
v___x_599_ = 58;
v___x_600_ = lean_unbox_uint32(v_head_597_);
lean_dec(v_head_597_);
v___x_601_ = lean_uint32_dec_eq(v___x_600_, v___x_599_);
if (v___x_601_ == 0)
{
lean_dec(v_tail_598_);
lean_dec(v_head_588_);
goto v___jp_574_;
}
else
{
if (lean_obj_tag(v_tail_598_) == 0)
{
uint32_t v___x_602_; uint32_t v___x_603_; uint8_t v___x_604_; 
v___x_602_ = 65;
v___x_603_ = lean_unbox_uint32(v_head_588_);
v___x_604_ = lean_uint32_dec_le(v___x_602_, v___x_603_);
if (v___x_604_ == 0)
{
goto v___jp_590_;
}
else
{
uint32_t v___x_605_; uint32_t v___x_606_; uint8_t v___x_607_; 
v___x_605_ = 90;
v___x_606_ = lean_unbox_uint32(v_head_588_);
v___x_607_ = lean_uint32_dec_le(v___x_606_, v___x_605_);
if (v___x_607_ == 0)
{
goto v___jp_590_;
}
else
{
lean_dec(v_head_588_);
goto v___jp_555_;
}
}
}
else
{
lean_dec(v_tail_598_);
lean_dec(v_head_588_);
goto v___jp_574_;
}
}
}
else
{
lean_dec(v_tail_589_);
lean_dec(v_head_588_);
goto v___jp_574_;
}
v___jp_590_:
{
uint32_t v___x_591_; uint32_t v___x_592_; uint8_t v___x_593_; 
v___x_591_ = 97;
v___x_592_ = lean_unbox_uint32(v_head_588_);
v___x_593_ = lean_uint32_dec_le(v___x_591_, v___x_592_);
if (v___x_593_ == 0)
{
lean_dec(v_head_588_);
goto v___jp_550_;
}
else
{
uint32_t v___x_594_; uint32_t v___x_595_; uint8_t v___x_596_; 
v___x_594_ = 122;
v___x_595_ = lean_unbox_uint32(v_head_588_);
lean_dec(v_head_588_);
v___x_596_ = lean_uint32_dec_le(v___x_595_, v___x_594_);
if (v___x_596_ == 0)
{
goto v___jp_550_;
}
else
{
goto v___jp_555_;
}
}
}
}
else
{
lean_dec(v_tail_584_);
goto v___jp_574_;
}
}
}
else
{
lean_dec(v___x_582_);
goto v___jp_574_;
}
v___jp_550_:
{
lean_object* v_str_551_; lean_object* v_startInclusive_552_; lean_object* v_endExclusive_553_; lean_object* v___x_554_; 
v_str_551_ = lean_ctor_get(v_p_549_, 0);
v_startInclusive_552_ = lean_ctor_get(v_p_549_, 1);
v_endExclusive_553_ = lean_ctor_get(v_p_549_, 2);
v___x_554_ = lean_string_utf8_extract_fast(v_str_551_, v_startInclusive_552_, v_endExclusive_553_);
return v___x_554_;
}
v___jp_555_:
{
lean_object* v_str_556_; lean_object* v_startInclusive_557_; lean_object* v_endExclusive_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; uint32_t v___x_564_; uint32_t v___x_565_; uint8_t v___x_566_; 
v_str_556_ = lean_ctor_get(v_p_549_, 0);
v_startInclusive_557_ = lean_ctor_get(v_p_549_, 1);
v_endExclusive_558_ = lean_ctor_get(v_p_549_, 2);
v___x_559_ = lean_unsigned_to_nat(1u);
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = l_String_Slice_Pos_nextn(v_p_549_, v___x_560_, v___x_559_);
v___x_562_ = lean_nat_add(v_startInclusive_557_, v___x_561_);
lean_dec(v___x_561_);
v___x_563_ = lean_string_utf8_extract_fast(v_str_556_, v___x_562_, v_endExclusive_558_);
lean_dec(v___x_562_);
v___x_564_ = lean_string_utf8_get(v___x_563_, v___x_560_);
v___x_565_ = 97;
v___x_566_ = lean_uint32_dec_le(v___x_565_, v___x_564_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; 
v___x_567_ = lean_string_utf8_set(v___x_563_, v___x_560_, v___x_564_);
return v___x_567_;
}
else
{
uint32_t v___x_568_; uint8_t v___x_569_; 
v___x_568_ = 122;
v___x_569_ = lean_uint32_dec_le(v___x_564_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; 
v___x_570_ = lean_string_utf8_set(v___x_563_, v___x_560_, v___x_564_);
return v___x_570_;
}
else
{
uint32_t v___x_571_; uint32_t v___x_572_; lean_object* v___x_573_; 
v___x_571_ = 4294967264;
v___x_572_ = lean_uint32_add(v___x_564_, v___x_571_);
v___x_573_ = lean_string_utf8_set(v___x_563_, v___x_560_, v___x_572_);
return v___x_573_;
}
}
}
v___jp_574_:
{
lean_object* v_str_575_; lean_object* v_startInclusive_576_; lean_object* v_endExclusive_577_; lean_object* v___x_578_; 
v_str_575_ = lean_ctor_get(v_p_549_, 0);
v_startInclusive_576_ = lean_ctor_get(v_p_549_, 1);
v_endExclusive_577_ = lean_ctor_get(v_p_549_, 2);
v___x_578_ = lean_string_utf8_extract_fast(v_str_575_, v_startInclusive_576_, v_endExclusive_577_);
return v___x_578_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression___boxed(lean_object* v_p_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression(v_p_608_);
lean_dec_ref(v_p_608_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0(lean_object* v_p_610_, lean_object* v_inst_611_, lean_object* v_R_612_, lean_object* v_a_613_, lean_object* v_b_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___redArg(v_p_610_, v_a_613_, v_b_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0___boxed(lean_object* v_p_616_, lean_object* v_inst_617_, lean_object* v_R_618_, lean_object* v_a_619_, lean_object* v_b_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_Uri_0__System_Uri_normalizeDriveExpression_spec__0(v_p_616_, v_inst_617_, v_R_618_, v_a_619_, v_b_620_);
lean_dec_ref(v_p_616_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg(lean_object* v_s_622_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_623_ = lean_string_utf8_byte_size(v_s_622_);
v___x_624_ = lean_unsigned_to_nat(7u);
v___x_625_ = lean_nat_dec_le(v___x_624_, v___x_623_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; 
lean_dec_ref(v_s_622_);
v___x_626_ = lean_box(0);
return v___x_626_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_627_ = ((lean_object*)(l_System_Uri_pathToUri___closed__2));
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_string_memcmp(v_s_622_, v___x_627_, v___x_628_, v___x_628_, v___x_624_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; 
lean_dec_ref(v_s_622_);
v___x_630_ = lean_box(0);
return v___x_630_;
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
lean_inc_ref(v_s_622_);
v___x_631_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_631_, 0, v_s_622_);
lean_ctor_set(v___x_631_, 1, v___x_628_);
lean_ctor_set(v___x_631_, 2, v___x_623_);
v___x_632_ = l_String_Slice_pos_x21(v___x_631_, v___x_624_);
lean_dec_ref_known(v___x_631_, 3);
v___x_633_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_633_, 0, v_s_622_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
lean_ctor_set(v___x_633_, 2, v___x_623_);
v___x_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
return v___x_634_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0(lean_object* v_s_635_, lean_object* v_pat_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg(v_s_635_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___boxed(lean_object* v_s_638_, lean_object* v_pat_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0(v_s_638_, v_pat_639_);
lean_dec_ref(v_pat_639_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1(lean_object* v_s_641_, lean_object* v_pos_642_){
_start:
{
lean_object* v_str_643_; lean_object* v_startInclusive_644_; lean_object* v_endExclusive_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v_decide_649_; 
v_str_643_ = lean_ctor_get(v_s_641_, 0);
v_startInclusive_644_ = lean_ctor_get(v_s_641_, 1);
v_endExclusive_645_ = lean_ctor_get(v_s_641_, 2);
v___x_646_ = lean_nat_add(v_startInclusive_644_, v_pos_642_);
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = lean_nat_sub(v_endExclusive_645_, v___x_646_);
v_decide_649_ = lean_nat_dec_eq(v___x_647_, v___x_648_);
lean_dec(v___x_648_);
if (v_decide_649_ == 0)
{
uint32_t v___x_650_; uint32_t v___x_651_; uint8_t v___x_652_; 
v___x_650_ = lean_string_utf8_get_fast(v_str_643_, v___x_646_);
v___x_651_ = 47;
v___x_652_ = lean_uint32_dec_eq(v___x_650_, v___x_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_653_ = lean_string_utf8_next_fast(v_str_643_, v___x_646_);
v___x_654_ = lean_nat_sub(v___x_653_, v___x_646_);
lean_dec(v___x_646_);
v___x_655_ = lean_nat_add(v_pos_642_, v___x_654_);
lean_dec(v___x_654_);
v___x_656_ = lean_unsigned_to_nat(1u);
v___x_657_ = lean_nat_add(v_pos_642_, v___x_656_);
v___x_658_ = lean_nat_dec_le(v___x_657_, v___x_655_);
lean_dec(v___x_657_);
if (v___x_658_ == 0)
{
lean_dec(v___x_655_);
return v_pos_642_;
}
else
{
lean_dec(v_pos_642_);
v_pos_642_ = v___x_655_;
goto _start;
}
}
else
{
lean_dec(v___x_646_);
return v_pos_642_;
}
}
else
{
lean_dec(v___x_646_);
return v_pos_642_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1___boxed(lean_object* v_s_660_, lean_object* v_pos_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1(v_s_660_, v_pos_661_);
lean_dec_ref(v_s_660_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_Uri_fileUriToPath_x3f_spec__2(lean_object* v_s_663_, lean_object* v_p_664_){
_start:
{
lean_object* v___y_666_; lean_object* v___y_667_; uint32_t v___y_671_; lean_object* v___x_683_; uint8_t v_decide_684_; 
v___x_683_ = lean_string_utf8_byte_size(v_s_663_);
v_decide_684_ = lean_nat_dec_eq(v_p_664_, v___x_683_);
if (v_decide_684_ == 0)
{
uint32_t v___x_685_; uint32_t v___x_686_; uint8_t v___x_687_; 
v___x_685_ = lean_string_utf8_get_fast(v_s_663_, v_p_664_);
v___x_686_ = 47;
v___x_687_ = lean_uint32_dec_eq(v___x_685_, v___x_686_);
if (v___x_687_ == 0)
{
v___y_671_ = v___x_685_;
goto v___jp_670_;
}
else
{
uint32_t v___x_688_; 
v___x_688_ = 92;
v___y_671_ = v___x_688_;
goto v___jp_670_;
}
}
else
{
lean_dec(v_p_664_);
return v_s_663_;
}
v___jp_665_:
{
lean_object* v___x_668_; 
v___x_668_ = lean_nat_add(v_p_664_, v___y_667_);
lean_dec(v_p_664_);
v_s_663_ = v___y_666_;
v_p_664_ = v___x_668_;
goto _start;
}
v___jp_670_:
{
lean_object* v___x_672_; uint32_t v___x_673_; uint8_t v___x_674_; 
lean_inc(v_p_664_);
v___x_672_ = lean_string_utf8_set(v_s_663_, v_p_664_, v___y_671_);
v___x_673_ = 127;
v___x_674_ = lean_uint32_dec_le(v___y_671_, v___x_673_);
if (v___x_674_ == 0)
{
uint32_t v___x_675_; uint8_t v___x_676_; 
v___x_675_ = 2047;
v___x_676_ = lean_uint32_dec_le(v___y_671_, v___x_675_);
if (v___x_676_ == 0)
{
uint32_t v___x_677_; uint8_t v___x_678_; 
v___x_677_ = 65535;
v___x_678_ = lean_uint32_dec_le(v___y_671_, v___x_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; 
v___x_679_ = lean_unsigned_to_nat(4u);
v___y_666_ = v___x_672_;
v___y_667_ = v___x_679_;
goto v___jp_665_;
}
else
{
lean_object* v___x_680_; 
v___x_680_ = lean_unsigned_to_nat(3u);
v___y_666_ = v___x_672_;
v___y_667_ = v___x_680_;
goto v___jp_665_;
}
}
else
{
lean_object* v___x_681_; 
v___x_681_ = lean_unsigned_to_nat(2u);
v___y_666_ = v___x_672_;
v___y_667_ = v___x_681_;
goto v___jp_665_;
}
}
else
{
lean_object* v___x_682_; 
v___x_682_ = lean_unsigned_to_nat(1u);
v___y_666_ = v___x_672_;
v___y_667_ = v___x_682_;
goto v___jp_665_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_fileUriToPath_x3f(lean_object* v_uri_689_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = l_System_Uri_UriEscape_decodeUri(v_uri_689_);
v___x_691_ = l_String_dropPrefix_x3f___at___00System_Uri_fileUriToPath_x3f_spec__0___redArg(v___x_690_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v___x_692_; 
v___x_692_ = lean_box(0);
return v___x_692_;
}
else
{
lean_object* v_val_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_723_; 
v_val_693_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_723_ == 0)
{
v___x_695_ = v___x_691_;
v_isShared_696_ = v_isSharedCheck_723_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_val_693_);
lean_dec(v___x_691_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_723_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v_str_697_; lean_object* v_startInclusive_698_; lean_object* v_endExclusive_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_719_; 
v_str_697_ = lean_ctor_get(v_val_693_, 0);
lean_inc_ref(v_str_697_);
v_startInclusive_698_ = lean_ctor_get(v_val_693_, 1);
lean_inc(v_startInclusive_698_);
v_endExclusive_699_ = lean_ctor_get(v_val_693_, 2);
lean_inc(v_endExclusive_699_);
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1(v_val_693_, v___x_700_);
v_isSharedCheck_719_ = !lean_is_exclusive(v_val_693_);
if (v_isSharedCheck_719_ == 0)
{
lean_object* v_unused_720_; lean_object* v_unused_721_; lean_object* v_unused_722_; 
v_unused_720_ = lean_ctor_get(v_val_693_, 2);
lean_dec(v_unused_720_);
v_unused_721_ = lean_ctor_get(v_val_693_, 1);
lean_dec(v_unused_721_);
v_unused_722_ = lean_ctor_get(v_val_693_, 0);
lean_dec(v_unused_722_);
v___x_703_ = v_val_693_;
v_isShared_704_ = v_isSharedCheck_719_;
goto v_resetjp_702_;
}
else
{
lean_dec(v_val_693_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_719_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_705_ = lean_nat_add(v_startInclusive_698_, v___x_701_);
lean_dec(v___x_701_);
lean_dec(v_startInclusive_698_);
v___x_706_ = l_System_Platform_isWindows;
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_709_; 
lean_del_object(v___x_703_);
v___x_707_ = lean_string_utf8_extract_fast(v_str_697_, v___x_705_, v_endExclusive_699_);
lean_dec(v_endExclusive_699_);
lean_dec(v___x_705_);
lean_dec_ref(v_str_697_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_707_);
v___x_709_ = v___x_695_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
else
{
lean_object* v_p_712_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v___x_705_);
v_p_712_ = v___x_703_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_str_697_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v_endExclusive_699_);
v_p_712_ = v_reuseFailAlloc_718_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_713_ = l___private_Init_System_Uri_0__System_Uri_normalizeDriveExpression(v_p_712_);
lean_dec_ref(v_p_712_);
v___x_714_ = l_String_mapAux___at___00System_Uri_fileUriToPath_x3f_spec__2(v___x_713_, v___x_700_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_714_);
v___x_716_ = v___x_695_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
}
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
