// Lean compiler output
// Module: Init.System.Uri
// Imports: public import Init.System.FilePath import Init.Data.String.TakeDrop import Init.Data.String.Modify import Init.Data.String.Search import Init.Omega import Init.System.Platform import Init.While
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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
extern uint8_t l_System_Platform_isWindows;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_String_Pos_Raw_modify(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
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
lean_object* l_String_Slice_positions(lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00System_Uri_UriEscape_decodeUri_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00System_Uri_UriEscape_decodeUri_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint32_t l_System_Uri_fileUriToPath_x3f___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_System_Uri_fileUriToPath_x3f___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_Uri_fileUriToPath_x3f_spec__0(lean_object*, lean_object*);
static lean_once_cell_t l_System_Uri_fileUriToPath_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Uri_fileUriToPath_x3f___closed__0;
static const lean_closure_object l_System_Uri_fileUriToPath_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_System_Uri_fileUriToPath_x3f___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_System_Uri_fileUriToPath_x3f___closed__1 = (const lean_object*)&l_System_Uri_fileUriToPath_x3f___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00System_Uri_UriEscape_decodeUri_spec__0(lean_object* v_len_44_, lean_object* v_rawBytes_45_, lean_object* v_b_46_){
_start:
{
lean_object* v_fst_48_; lean_object* v_snd_49_; lean_object* v_fst_52_; lean_object* v_snd_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_99_; 
v_fst_52_ = lean_ctor_get(v_b_46_, 0);
v_snd_53_ = lean_ctor_get(v_b_46_, 1);
v_isSharedCheck_99_ = !lean_is_exclusive(v_b_46_);
if (v_isSharedCheck_99_ == 0)
{
v___x_55_ = v_b_46_;
v_isShared_56_ = v_isSharedCheck_99_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_snd_53_);
lean_inc(v_fst_52_);
lean_dec(v_b_46_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_99_;
goto v_resetjp_54_;
}
v___jp_47_:
{
lean_object* v___x_50_; 
v___x_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_50_, 0, v_fst_48_);
lean_ctor_set(v___x_50_, 1, v_snd_49_);
v_b_46_ = v___x_50_;
goto _start;
}
v_resetjp_54_:
{
uint8_t v___x_57_; 
v___x_57_ = lean_nat_dec_lt(v_snd_53_, v_len_44_);
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
uint8_t v_percent_61_; uint8_t v_c_62_; uint8_t v___x_67_; 
lean_del_object(v___x_55_);
v_percent_61_ = 37;
v_c_62_ = lean_byte_array_fget(v_rawBytes_45_, v_snd_53_);
v___x_67_ = lean_uint8_dec_eq(v_c_62_, v_percent_61_);
if (v___x_67_ == 0)
{
goto v___jp_63_;
}
else
{
lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_68_ = lean_unsigned_to_nat(1u);
v___x_69_ = lean_nat_add(v_snd_53_, v___x_68_);
v___x_70_ = lean_nat_dec_lt(v___x_69_, v_len_44_);
if (v___x_70_ == 0)
{
lean_dec(v___x_69_);
goto v___jp_63_;
}
else
{
uint8_t v_h1_71_; lean_object* v___x_72_; 
v_h1_71_ = lean_byte_array_fget(v_rawBytes_45_, v___x_69_);
lean_dec(v___x_69_);
v___x_72_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(v_h1_71_);
if (lean_obj_tag(v___x_72_) == 1)
{
lean_object* v_val_73_; lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v_val_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_val_73_);
lean_dec_ref(v___x_72_);
v___x_74_ = lean_unsigned_to_nat(2u);
v___x_75_ = lean_nat_add(v_snd_53_, v___x_74_);
v___x_76_ = lean_nat_dec_lt(v___x_75_, v_len_44_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; 
lean_dec(v_val_73_);
lean_dec(v_snd_53_);
v___x_77_ = lean_byte_array_push(v_fst_52_, v_c_62_);
v___x_78_ = lean_byte_array_push(v___x_77_, v_h1_71_);
v_fst_48_ = v___x_78_;
v_snd_49_ = v___x_75_;
goto v___jp_47_;
}
else
{
uint8_t v_h2_79_; lean_object* v___x_80_; 
v_h2_79_ = lean_byte_array_fget(v_rawBytes_45_, v___x_75_);
lean_dec(v___x_75_);
v___x_80_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(v_h2_79_);
if (lean_obj_tag(v___x_80_) == 1)
{
lean_object* v_val_81_; uint8_t v___x_82_; uint8_t v___x_83_; uint8_t v___x_84_; uint8_t v___x_85_; uint8_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v_val_81_ = lean_ctor_get(v___x_80_, 0);
lean_inc(v_val_81_);
lean_dec_ref(v___x_80_);
v___x_82_ = 4;
v___x_83_ = lean_unbox(v_val_73_);
lean_dec(v_val_73_);
v___x_84_ = lean_uint8_shift_left(v___x_83_, v___x_82_);
v___x_85_ = lean_unbox(v_val_81_);
lean_dec(v_val_81_);
v___x_86_ = lean_uint8_add(v___x_84_, v___x_85_);
v___x_87_ = lean_byte_array_push(v_fst_52_, v___x_86_);
v___x_88_ = lean_unsigned_to_nat(3u);
v___x_89_ = lean_nat_add(v_snd_53_, v___x_88_);
lean_dec(v_snd_53_);
v_fst_48_ = v___x_87_;
v_snd_49_ = v___x_89_;
goto v___jp_47_;
}
else
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
lean_dec(v___x_80_);
lean_dec(v_val_73_);
v___x_90_ = lean_byte_array_push(v_fst_52_, v_c_62_);
v___x_91_ = lean_byte_array_push(v___x_90_, v_h1_71_);
v___x_92_ = lean_byte_array_push(v___x_91_, v_h2_79_);
v___x_93_ = lean_unsigned_to_nat(3u);
v___x_94_ = lean_nat_add(v_snd_53_, v___x_93_);
lean_dec(v_snd_53_);
v_fst_48_ = v___x_92_;
v_snd_49_ = v___x_94_;
goto v___jp_47_;
}
}
}
else
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
lean_dec(v___x_72_);
v___x_95_ = lean_byte_array_push(v_fst_52_, v_c_62_);
v___x_96_ = lean_byte_array_push(v___x_95_, v_h1_71_);
v___x_97_ = lean_unsigned_to_nat(2u);
v___x_98_ = lean_nat_add(v_snd_53_, v___x_97_);
lean_dec(v_snd_53_);
v_fst_48_ = v___x_96_;
v_snd_49_ = v___x_98_;
goto v___jp_47_;
}
}
}
v___jp_63_:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_byte_array_push(v_fst_52_, v_c_62_);
v___x_65_ = lean_unsigned_to_nat(1u);
v___x_66_ = lean_nat_add(v_snd_53_, v___x_65_);
lean_dec(v_snd_53_);
v_fst_48_ = v___x_64_;
v_snd_49_ = v___x_66_;
goto v___jp_47_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00System_Uri_UriEscape_decodeUri_spec__0___boxed(lean_object* v_len_100_, lean_object* v_rawBytes_101_, lean_object* v_b_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00System_Uri_UriEscape_decodeUri_spec__0(v_len_100_, v_rawBytes_101_, v_b_102_);
lean_dec_ref(v_rawBytes_101_);
lean_dec(v_len_100_);
return v_res_103_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_decodeUri___closed__0(void){
_start:
{
lean_object* v_i_104_; lean_object* v_decoded_105_; lean_object* v___x_106_; 
v_i_104_ = lean_unsigned_to_nat(0u);
v_decoded_105_ = l_ByteArray_empty;
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v_decoded_105_);
lean_ctor_set(v___x_106_, 1, v_i_104_);
return v___x_106_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_decodeUri___closed__4(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_110_ = ((lean_object*)(l_System_Uri_UriEscape_decodeUri___closed__3));
v___x_111_ = lean_unsigned_to_nat(46u);
v___x_112_ = lean_unsigned_to_nat(193u);
v___x_113_ = ((lean_object*)(l_System_Uri_UriEscape_decodeUri___closed__2));
v___x_114_ = ((lean_object*)(l_System_Uri_UriEscape_decodeUri___closed__1));
v___x_115_ = l_mkPanicMessageWithDecl(v___x_114_, v___x_113_, v___x_112_, v___x_111_, v___x_110_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_decodeUri(lean_object* v_uri_116_){
_start:
{
lean_object* v_rawBytes_117_; lean_object* v_len_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v_fst_121_; uint8_t v___x_122_; 
v_rawBytes_117_ = lean_string_to_utf8(v_uri_116_);
v_len_118_ = lean_byte_array_size(v_rawBytes_117_);
v___x_119_ = lean_obj_once(&l_System_Uri_UriEscape_decodeUri___closed__0, &l_System_Uri_UriEscape_decodeUri___closed__0_once, _init_l_System_Uri_UriEscape_decodeUri___closed__0);
v___x_120_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00System_Uri_UriEscape_decodeUri_spec__0(v_len_118_, v_rawBytes_117_, v___x_119_);
lean_dec_ref(v_rawBytes_117_);
v_fst_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_fst_121_);
lean_dec_ref(v___x_120_);
v___x_122_ = lean_string_validate_utf8(v_fst_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; 
lean_dec(v_fst_121_);
v___x_123_ = lean_obj_once(&l_System_Uri_UriEscape_decodeUri___closed__4, &l_System_Uri_UriEscape_decodeUri___closed__4_once, _init_l_System_Uri_UriEscape_decodeUri___closed__4);
v___x_124_ = l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1(v___x_123_);
return v___x_124_;
}
else
{
lean_object* v___x_125_; 
v___x_125_ = lean_string_from_utf8_unchecked(v_fst_121_);
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_decodeUri___boxed(lean_object* v_uri_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_System_Uri_UriEscape_decodeUri(v_uri_126_);
lean_dec_ref(v_uri_126_);
return v_res_127_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_128_; lean_object* v___x_129_; 
v___x_128_ = 32;
v___x_129_ = lean_box_uint32(v___x_128_);
return v___x_129_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_130_ = lean_box(0);
v___x_131_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0___boxed__const__1;
v___x_132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___x_130_);
return v___x_132_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_133_; lean_object* v___x_134_; 
v___x_133_ = 37;
v___x_134_ = lean_box_uint32(v___x_133_);
return v___x_134_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__0);
v___x_136_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1___boxed__const__1;
v___x_137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___x_135_);
return v___x_137_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_138_; lean_object* v___x_139_; 
v___x_138_ = 42;
v___x_139_ = lean_box_uint32(v___x_138_);
return v___x_139_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__1);
v___x_141_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2___boxed__const__1;
v___x_142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set(v___x_142_, 1, v___x_140_);
return v___x_142_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_143_; lean_object* v___x_144_; 
v___x_143_ = 41;
v___x_144_ = lean_box_uint32(v___x_143_);
return v___x_144_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__2);
v___x_146_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3___boxed__const__1;
v___x_147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v___x_145_);
return v___x_147_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4___boxed__const__1(void){
_start:
{
uint32_t v___x_148_; lean_object* v___x_149_; 
v___x_148_ = 40;
v___x_149_ = lean_box_uint32(v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__3);
v___x_151_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4___boxed__const__1;
v___x_152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v___x_150_);
return v___x_152_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5___boxed__const__1(void){
_start:
{
uint32_t v___x_153_; lean_object* v___x_154_; 
v___x_153_ = 39;
v___x_154_ = lean_box_uint32(v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__4);
v___x_156_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5___boxed__const__1;
v___x_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_155_);
return v___x_157_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6___boxed__const__1(void){
_start:
{
uint32_t v___x_158_; lean_object* v___x_159_; 
v___x_158_ = 33;
v___x_159_ = lean_box_uint32(v___x_158_);
return v___x_159_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__5);
v___x_161_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6___boxed__const__1;
v___x_162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v___x_160_);
return v___x_162_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7___boxed__const__1(void){
_start:
{
uint32_t v___x_163_; lean_object* v___x_164_; 
v___x_163_ = 44;
v___x_164_ = lean_box_uint32(v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__6);
v___x_166_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7___boxed__const__1;
v___x_167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v___x_165_);
return v___x_167_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8___boxed__const__1(void){
_start:
{
uint32_t v___x_168_; lean_object* v___x_169_; 
v___x_168_ = 36;
v___x_169_ = lean_box_uint32(v___x_168_);
return v___x_169_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__7);
v___x_171_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8___boxed__const__1;
v___x_172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v___x_170_);
return v___x_172_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9___boxed__const__1(void){
_start:
{
uint32_t v___x_173_; lean_object* v___x_174_; 
v___x_173_ = 43;
v___x_174_ = lean_box_uint32(v___x_173_);
return v___x_174_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__8);
v___x_176_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9___boxed__const__1;
v___x_177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v___x_175_);
return v___x_177_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10___boxed__const__1(void){
_start:
{
uint32_t v___x_178_; lean_object* v___x_179_; 
v___x_178_ = 61;
v___x_179_ = lean_box_uint32(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__9);
v___x_181_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10___boxed__const__1;
v___x_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___x_180_);
return v___x_182_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11___boxed__const__1(void){
_start:
{
uint32_t v___x_183_; lean_object* v___x_184_; 
v___x_183_ = 38;
v___x_184_ = lean_box_uint32(v___x_183_);
return v___x_184_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__10);
v___x_186_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11___boxed__const__1;
v___x_187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v___x_185_);
return v___x_187_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12___boxed__const__1(void){
_start:
{
uint32_t v___x_188_; lean_object* v___x_189_; 
v___x_188_ = 64;
v___x_189_ = lean_box_uint32(v___x_188_);
return v___x_189_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__11);
v___x_191_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12___boxed__const__1;
v___x_192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_190_);
return v___x_192_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13___boxed__const__1(void){
_start:
{
uint32_t v___x_193_; lean_object* v___x_194_; 
v___x_193_ = 93;
v___x_194_ = lean_box_uint32(v___x_193_);
return v___x_194_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__12);
v___x_196_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13___boxed__const__1;
v___x_197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set(v___x_197_, 1, v___x_195_);
return v___x_197_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14___boxed__const__1(void){
_start:
{
uint32_t v___x_198_; lean_object* v___x_199_; 
v___x_198_ = 91;
v___x_199_ = lean_box_uint32(v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__13);
v___x_201_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14___boxed__const__1;
v___x_202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v___x_200_);
return v___x_202_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15___boxed__const__1(void){
_start:
{
uint32_t v___x_203_; lean_object* v___x_204_; 
v___x_203_ = 35;
v___x_204_ = lean_box_uint32(v___x_203_);
return v___x_204_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__14);
v___x_206_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15___boxed__const__1;
v___x_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v___x_205_);
return v___x_207_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16___boxed__const__1(void){
_start:
{
uint32_t v___x_208_; lean_object* v___x_209_; 
v___x_208_ = 63;
v___x_209_ = lean_box_uint32(v___x_208_);
return v___x_209_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__15);
v___x_211_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16___boxed__const__1;
v___x_212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v___x_210_);
return v___x_212_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17___boxed__const__1(void){
_start:
{
uint32_t v___x_213_; lean_object* v___x_214_; 
v___x_213_ = 58;
v___x_214_ = lean_box_uint32(v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__16);
v___x_216_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17___boxed__const__1;
v___x_217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v___x_215_);
return v___x_217_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18___boxed__const__1(void){
_start:
{
uint32_t v___x_218_; lean_object* v___x_219_; 
v___x_218_ = 59;
v___x_219_ = lean_box_uint32(v___x_218_);
return v___x_219_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_220_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__17);
v___x_221_ = l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18___boxed__const__1;
v___x_222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
return v___x_222_;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars(void){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_obj_once(&l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18, &l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18_once, _init_l_System_Uri_UriEscape_rfc3986ReservedChars___closed__18);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex_spec__0(lean_object* v_s_224_, lean_object* v_p_225_){
_start:
{
uint32_t v___y_227_; lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_232_ = lean_string_utf8_byte_size(v_s_224_);
v___x_233_ = lean_nat_dec_eq(v_p_225_, v___x_232_);
if (v___x_233_ == 0)
{
uint32_t v___x_234_; uint32_t v___x_235_; uint8_t v___x_236_; 
v___x_234_ = lean_string_utf8_get_fast(v_s_224_, v_p_225_);
v___x_235_ = 97;
v___x_236_ = lean_uint32_dec_le(v___x_235_, v___x_234_);
if (v___x_236_ == 0)
{
v___y_227_ = v___x_234_;
goto v___jp_226_;
}
else
{
uint32_t v___x_237_; uint8_t v___x_238_; 
v___x_237_ = 122;
v___x_238_ = lean_uint32_dec_le(v___x_234_, v___x_237_);
if (v___x_238_ == 0)
{
v___y_227_ = v___x_234_;
goto v___jp_226_;
}
else
{
uint32_t v___x_239_; uint32_t v___x_240_; 
v___x_239_ = 4294967264;
v___x_240_ = lean_uint32_add(v___x_234_, v___x_239_);
v___y_227_ = v___x_240_;
goto v___jp_226_;
}
}
}
else
{
lean_dec(v_p_225_);
return v_s_224_;
}
v___jp_226_:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
lean_inc(v_p_225_);
v___x_228_ = lean_string_utf8_set(v_s_224_, v_p_225_, v___y_227_);
v___x_229_ = l_Char_utf8Size(v___y_227_);
v___x_230_ = lean_nat_add(v_p_225_, v___x_229_);
lean_dec(v___x_229_);
lean_dec(v_p_225_);
v_s_224_ = v___x_228_;
v_p_225_ = v___x_230_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(uint8_t v_c_241_){
_start:
{
uint8_t v___x_242_; uint8_t v___x_243_; uint8_t v_d2_244_; uint8_t v_d1_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_242_ = 16;
v___x_243_ = 4;
v_d2_244_ = lean_uint8_shift_right(v_c_241_, v___x_243_);
v_d1_245_ = lean_uint8_mod(v_c_241_, v___x_242_);
v___x_246_ = lean_uint8_to_nat(v_d2_244_);
v___x_247_ = l_hexDigitRepr(v___x_246_);
v___x_248_ = lean_uint8_to_nat(v_d1_245_);
v___x_249_ = l_hexDigitRepr(v___x_248_);
v___x_250_ = lean_string_append(v___x_247_, v___x_249_);
lean_dec_ref(v___x_249_);
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = l_String_mapAux___at___00__private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex_spec__0(v___x_250_, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex___boxed(lean_object* v_c_253_){
_start:
{
uint8_t v_c_boxed_254_; lean_object* v_res_255_; 
v_c_boxed_254_ = lean_unbox(v_c_253_);
v_res_255_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(v_c_boxed_254_);
return v_res_255_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1(uint32_t v_a_256_, lean_object* v_x_257_){
_start:
{
if (lean_obj_tag(v_x_257_) == 0)
{
uint8_t v___x_258_; 
v___x_258_ = 0;
return v___x_258_;
}
else
{
lean_object* v_head_259_; lean_object* v_tail_260_; uint32_t v___x_261_; uint8_t v___x_262_; 
v_head_259_ = lean_ctor_get(v_x_257_, 0);
v_tail_260_ = lean_ctor_get(v_x_257_, 1);
v___x_261_ = lean_unbox_uint32(v_head_259_);
v___x_262_ = lean_uint32_dec_eq(v_a_256_, v___x_261_);
if (v___x_262_ == 0)
{
v_x_257_ = v_tail_260_;
goto _start;
}
else
{
return v___x_262_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1___boxed(lean_object* v_a_264_, lean_object* v_x_265_){
_start:
{
uint32_t v_a_boxed_266_; uint8_t v_res_267_; lean_object* v_r_268_; 
v_a_boxed_266_ = lean_unbox_uint32(v_a_264_);
lean_dec(v_a_264_);
v_res_267_ = l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1(v_a_boxed_266_, v_x_265_);
lean_dec(v_x_265_);
v_r_268_ = lean_box(v_res_267_);
return v_r_268_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(lean_object* v_as_270_, size_t v_i_271_, size_t v_stop_272_, lean_object* v_b_273_){
_start:
{
uint8_t v___x_274_; 
v___x_274_ = lean_usize_dec_eq(v_i_271_, v_stop_272_);
if (v___x_274_ == 0)
{
uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; size_t v___x_280_; size_t v___x_281_; 
v___x_275_ = lean_byte_array_uget(v_as_270_, v_i_271_);
v___x_276_ = ((lean_object*)(l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___closed__0));
v___x_277_ = lean_string_append(v_b_273_, v___x_276_);
v___x_278_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(v___x_275_);
v___x_279_ = lean_string_append(v___x_277_, v___x_278_);
lean_dec_ref(v___x_278_);
v___x_280_ = ((size_t)1ULL);
v___x_281_ = lean_usize_add(v_i_271_, v___x_280_);
v_i_271_ = v___x_281_;
v_b_273_ = v___x_279_;
goto _start;
}
else
{
return v_b_273_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___boxed(lean_object* v_as_283_, lean_object* v_i_284_, lean_object* v_stop_285_, lean_object* v_b_286_){
_start:
{
size_t v_i_boxed_287_; size_t v_stop_boxed_288_; lean_object* v_res_289_; 
v_i_boxed_287_ = lean_unbox_usize(v_i_284_);
lean_dec(v_i_284_);
v_stop_boxed_288_ = lean_unbox_usize(v_stop_285_);
lean_dec(v_stop_285_);
v_res_289_ = l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(v_as_283_, v_i_boxed_287_, v_stop_boxed_288_, v_b_286_);
lean_dec_ref(v_as_283_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_uriEscapeAsciiChar(uint32_t v_c_290_){
_start:
{
uint8_t v___y_292_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_316_ = l_System_Uri_UriEscape_rfc3986ReservedChars;
v___x_317_ = l_List_elem___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__1(v_c_290_, v___x_316_);
if (v___x_317_ == 0)
{
uint32_t v___x_318_; uint8_t v___x_319_; 
v___x_318_ = 32;
v___x_319_ = lean_uint32_dec_lt(v_c_290_, v___x_318_);
v___y_292_ = v___x_319_;
goto v___jp_291_;
}
else
{
v___y_292_ = v___x_317_;
goto v___jp_291_;
}
v___jp_291_:
{
if (v___y_292_ == 0)
{
lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_293_ = lean_uint32_to_nat(v_c_290_);
v___x_294_ = lean_unsigned_to_nat(127u);
v___x_295_ = lean_nat_dec_lt(v___x_293_, v___x_294_);
lean_dec(v___x_293_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_296_ = ((lean_object*)(l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0));
v___x_297_ = lean_string_push(v___x_296_, v_c_290_);
v___x_298_ = lean_string_to_utf8(v___x_297_);
lean_dec_ref(v___x_297_);
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = lean_byte_array_size(v___x_298_);
v___x_301_ = lean_nat_dec_lt(v___x_299_, v___x_300_);
if (v___x_301_ == 0)
{
lean_dec_ref(v___x_298_);
return v___x_296_;
}
else
{
uint8_t v___x_302_; 
v___x_302_ = lean_nat_dec_le(v___x_300_, v___x_300_);
if (v___x_302_ == 0)
{
if (v___x_301_ == 0)
{
lean_dec_ref(v___x_298_);
return v___x_296_;
}
else
{
size_t v___x_303_; size_t v___x_304_; lean_object* v___x_305_; 
v___x_303_ = ((size_t)0ULL);
v___x_304_ = lean_usize_of_nat(v___x_300_);
v___x_305_ = l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(v___x_298_, v___x_303_, v___x_304_, v___x_296_);
lean_dec_ref(v___x_298_);
return v___x_305_;
}
}
else
{
size_t v___x_306_; size_t v___x_307_; lean_object* v___x_308_; 
v___x_306_ = ((size_t)0ULL);
v___x_307_ = lean_usize_of_nat(v___x_300_);
v___x_308_ = l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(v___x_298_, v___x_306_, v___x_307_, v___x_296_);
lean_dec_ref(v___x_298_);
return v___x_308_;
}
}
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = ((lean_object*)(l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0));
v___x_310_ = lean_string_push(v___x_309_, v_c_290_);
return v___x_310_;
}
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_311_ = ((lean_object*)(l_ByteArray_foldlMUnsafe_fold___at___00System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___closed__0));
v___x_312_ = lean_uint32_to_nat(v_c_290_);
v___x_313_ = lean_uint8_of_nat(v___x_312_);
lean_dec(v___x_312_);
v___x_314_ = l___private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(v___x_313_);
v___x_315_ = lean_string_append(v___x_311_, v___x_314_);
lean_dec_ref(v___x_314_);
return v___x_315_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_uriEscapeAsciiChar___boxed(lean_object* v_c_320_){
_start:
{
uint32_t v_c_boxed_321_; lean_object* v_res_322_; 
v_c_boxed_321_ = lean_unbox_uint32(v_c_320_);
lean_dec(v_c_320_);
v_res_322_ = l_System_Uri_UriEscape_uriEscapeAsciiChar(v_c_boxed_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(lean_object* v___x_323_, lean_object* v_uri_324_, lean_object* v_a_325_, lean_object* v_b_326_){
_start:
{
lean_object* v_startInclusive_327_; lean_object* v_endExclusive_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v_startInclusive_327_ = lean_ctor_get(v___x_323_, 1);
v_endExclusive_328_ = lean_ctor_get(v___x_323_, 2);
v___x_329_ = lean_nat_sub(v_endExclusive_328_, v_startInclusive_327_);
v___x_330_ = lean_nat_dec_eq(v_a_325_, v___x_329_);
lean_dec(v___x_329_);
if (v___x_330_ == 0)
{
uint32_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_331_ = lean_string_utf8_get_fast(v_uri_324_, v_a_325_);
v___x_332_ = lean_string_utf8_next_fast(v_uri_324_, v_a_325_);
lean_dec(v_a_325_);
v___x_333_ = l_System_Uri_UriEscape_uriEscapeAsciiChar(v___x_331_);
v___x_334_ = lean_string_append(v_b_326_, v___x_333_);
lean_dec_ref(v___x_333_);
v_a_325_ = v___x_332_;
v_b_326_ = v___x_334_;
goto _start;
}
else
{
lean_dec(v_a_325_);
return v_b_326_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg___boxed(lean_object* v___x_336_, lean_object* v_uri_337_, lean_object* v_a_338_, lean_object* v_b_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(v___x_336_, v_uri_337_, v_a_338_, v_b_339_);
lean_dec_ref(v_uri_337_);
lean_dec_ref(v___x_336_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_escapeUri(lean_object* v_uri_341_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_342_ = ((lean_object*)(l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0));
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_string_utf8_byte_size(v_uri_341_);
lean_inc_ref(v_uri_341_);
v___x_345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_345_, 0, v_uri_341_);
lean_ctor_set(v___x_345_, 1, v___x_343_);
lean_ctor_set(v___x_345_, 2, v___x_344_);
v___x_346_ = l_String_Slice_positions(v___x_345_);
v___x_347_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(v___x_345_, v_uri_341_, v___x_346_, v___x_342_);
lean_dec_ref(v_uri_341_);
lean_dec_ref(v___x_345_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0(lean_object* v___x_348_, lean_object* v_uri_349_, lean_object* v_inst_350_, lean_object* v_R_351_, lean_object* v_a_352_, lean_object* v_b_353_, lean_object* v_c_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(v___x_348_, v_uri_349_, v_a_352_, v_b_353_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___boxed(lean_object* v___x_356_, lean_object* v_uri_357_, lean_object* v_inst_358_, lean_object* v_R_359_, lean_object* v_a_360_, lean_object* v_b_361_, lean_object* v_c_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0(v___x_356_, v_uri_357_, v_inst_358_, v_R_359_, v_a_360_, v_b_361_, v_c_362_);
lean_dec_ref(v_uri_357_);
lean_dec_ref(v___x_356_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_unescapeUri(lean_object* v_s_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_System_Uri_UriEscape_decodeUri(v_s_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_unescapeUri___boxed(lean_object* v_s_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_System_Uri_unescapeUri(v_s_366_);
lean_dec_ref(v_s_366_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_Uri_pathToUri_spec__0(lean_object* v_s_368_, lean_object* v_p_369_){
_start:
{
uint32_t v___y_371_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_376_ = lean_string_utf8_byte_size(v_s_368_);
v___x_377_ = lean_nat_dec_eq(v_p_369_, v___x_376_);
if (v___x_377_ == 0)
{
uint32_t v___x_378_; uint32_t v___x_379_; uint8_t v___x_380_; 
v___x_378_ = lean_string_utf8_get_fast(v_s_368_, v_p_369_);
v___x_379_ = 92;
v___x_380_ = lean_uint32_dec_eq(v___x_378_, v___x_379_);
if (v___x_380_ == 0)
{
v___y_371_ = v___x_378_;
goto v___jp_370_;
}
else
{
uint32_t v___x_381_; 
v___x_381_ = 47;
v___y_371_ = v___x_381_;
goto v___jp_370_;
}
}
else
{
lean_dec(v_p_369_);
return v_s_368_;
}
v___jp_370_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
lean_inc(v_p_369_);
v___x_372_ = lean_string_utf8_set(v_s_368_, v_p_369_, v___y_371_);
v___x_373_ = l_Char_utf8Size(v___y_371_);
v___x_374_ = lean_nat_add(v_p_369_, v___x_373_);
lean_dec(v___x_373_);
lean_dec(v_p_369_);
v_s_368_ = v___x_372_;
v_p_369_ = v___x_374_;
goto _start;
}
}
}
static lean_object* _init_l_System_Uri_pathToUri___closed__2(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l_System_Uri_pathToUri___closed__1));
v___x_385_ = lean_string_utf8_byte_size(v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_pathToUri(lean_object* v_fname_387_){
_start:
{
lean_object* v___y_389_; lean_object* v_uri_393_; lean_object* v_uri_408_; lean_object* v_uri_411_; uint8_t v___y_413_; uint8_t v___x_429_; 
v_uri_411_ = l_System_FilePath_normalize(v_fname_387_);
v___x_429_ = l_System_Platform_isWindows;
if (v___x_429_ == 0)
{
v_uri_393_ = v_uri_411_;
goto v___jp_392_;
}
else
{
lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; uint32_t v___y_434_; 
v___x_430_ = lean_unsigned_to_nat(2u);
v___x_431_ = lean_string_length(v_uri_411_);
v___x_432_ = lean_nat_dec_le(v___x_430_, v___x_431_);
if (v___x_432_ == 0)
{
v___y_413_ = v___x_432_;
goto v___jp_412_;
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = lean_string_utf8_byte_size(v_uri_411_);
lean_inc_ref(v_uri_411_);
v___x_441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_441_, 0, v_uri_411_);
lean_ctor_set(v___x_441_, 1, v___x_439_);
lean_ctor_set(v___x_441_, 2, v___x_440_);
v___x_442_ = l_String_Slice_Pos_get_x3f(v___x_441_, v___x_439_);
lean_dec_ref(v___x_441_);
if (lean_obj_tag(v___x_442_) == 0)
{
uint32_t v___x_443_; 
v___x_443_ = 65;
v___y_434_ = v___x_443_;
goto v___jp_433_;
}
else
{
lean_object* v_val_444_; uint32_t v___x_445_; 
v_val_444_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_val_444_);
lean_dec_ref(v___x_442_);
v___x_445_ = lean_unbox_uint32(v_val_444_);
lean_dec(v_val_444_);
v___y_434_ = v___x_445_;
goto v___jp_433_;
}
}
v___jp_433_:
{
uint32_t v___x_435_; uint8_t v___x_436_; 
v___x_435_ = 65;
v___x_436_ = lean_uint32_dec_le(v___x_435_, v___y_434_);
if (v___x_436_ == 0)
{
v_uri_408_ = v_uri_411_;
goto v___jp_407_;
}
else
{
uint32_t v___x_437_; uint8_t v___x_438_; 
v___x_437_ = 90;
v___x_438_ = lean_uint32_dec_le(v___y_434_, v___x_437_);
if (v___x_438_ == 0)
{
v_uri_408_ = v_uri_411_;
goto v___jp_407_;
}
else
{
v___y_413_ = v___x_432_;
goto v___jp_412_;
}
}
}
}
v___jp_388_:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = ((lean_object*)(l_System_Uri_pathToUri___closed__0));
v___x_391_ = lean_string_append(v___x_390_, v___y_389_);
lean_dec_ref(v___y_389_);
return v___x_391_;
}
v___jp_392_:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v_uri_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_394_ = ((lean_object*)(l_panic___at___00System_Uri_UriEscape_decodeUri_spec__1___closed__0));
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_396_ = lean_string_utf8_byte_size(v_uri_393_);
lean_inc_ref(v_uri_393_);
v___x_397_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_397_, 0, v_uri_393_);
lean_ctor_set(v___x_397_, 1, v___x_395_);
lean_ctor_set(v___x_397_, 2, v___x_396_);
v___x_398_ = l_String_Slice_positions(v___x_397_);
v_uri_399_ = l_WellFounded_opaqueFix_u2083___at___00System_Uri_escapeUri_spec__0___redArg(v___x_397_, v_uri_393_, v___x_398_, v___x_394_);
lean_dec_ref(v_uri_393_);
lean_dec_ref(v___x_397_);
v___x_400_ = ((lean_object*)(l_System_Uri_pathToUri___closed__1));
v___x_401_ = lean_string_utf8_byte_size(v_uri_399_);
v___x_402_ = lean_obj_once(&l_System_Uri_pathToUri___closed__2, &l_System_Uri_pathToUri___closed__2_once, _init_l_System_Uri_pathToUri___closed__2);
v___x_403_ = lean_nat_dec_le(v___x_402_, v___x_401_);
if (v___x_403_ == 0)
{
v___y_389_ = v_uri_399_;
goto v___jp_388_;
}
else
{
uint8_t v___x_404_; 
v___x_404_ = lean_string_memcmp(v_uri_399_, v___x_400_, v___x_395_, v___x_395_, v___x_402_);
if (v___x_404_ == 0)
{
v___y_389_ = v_uri_399_;
goto v___jp_388_;
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = ((lean_object*)(l_System_Uri_pathToUri___closed__3));
v___x_406_ = lean_string_append(v___x_405_, v_uri_399_);
lean_dec_ref(v_uri_399_);
return v___x_406_;
}
}
}
v___jp_407_:
{
lean_object* v___x_409_; lean_object* v_uri_410_; 
v___x_409_ = lean_unsigned_to_nat(0u);
v_uri_410_ = l_String_mapAux___at___00System_Uri_pathToUri_spec__0(v_uri_408_, v___x_409_);
v_uri_393_ = v_uri_410_;
goto v___jp_392_;
}
v___jp_412_:
{
if (v___y_413_ == 0)
{
v_uri_408_ = v_uri_411_;
goto v___jp_407_;
}
else
{
lean_object* v___x_414_; uint32_t v___x_415_; uint32_t v___x_416_; uint8_t v___x_417_; 
v___x_414_ = lean_unsigned_to_nat(1u);
v___x_415_ = lean_string_utf8_get(v_uri_411_, v___x_414_);
v___x_416_ = 58;
v___x_417_ = lean_uint32_dec_eq(v___x_415_, v___x_416_);
if (v___x_417_ == 0)
{
v_uri_408_ = v_uri_411_;
goto v___jp_407_;
}
else
{
lean_object* v___x_418_; uint32_t v___x_419_; uint32_t v___x_420_; uint8_t v___x_421_; 
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = lean_string_utf8_get(v_uri_411_, v___x_418_);
v___x_420_ = 65;
v___x_421_ = lean_uint32_dec_le(v___x_420_, v___x_419_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; 
v___x_422_ = lean_string_utf8_set(v_uri_411_, v___x_418_, v___x_419_);
v_uri_408_ = v___x_422_;
goto v___jp_407_;
}
else
{
uint32_t v___x_423_; uint8_t v___x_424_; 
v___x_423_ = 90;
v___x_424_ = lean_uint32_dec_le(v___x_419_, v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; 
v___x_425_ = lean_string_utf8_set(v_uri_411_, v___x_418_, v___x_419_);
v_uri_408_ = v___x_425_;
goto v___jp_407_;
}
else
{
uint32_t v___x_426_; uint32_t v___x_427_; lean_object* v___x_428_; 
v___x_426_ = 32;
v___x_427_ = lean_uint32_add(v___x_419_, v___x_426_);
v___x_428_ = lean_string_utf8_set(v_uri_411_, v___x_418_, v___x_427_);
v_uri_408_ = v___x_428_;
goto v___jp_407_;
}
}
}
}
}
}
}
LEAN_EXPORT uint32_t l_System_Uri_fileUriToPath_x3f___lam__0(uint32_t v___y_446_){
_start:
{
uint32_t v___x_447_; uint8_t v___x_448_; 
v___x_447_ = 97;
v___x_448_ = lean_uint32_dec_le(v___x_447_, v___y_446_);
if (v___x_448_ == 0)
{
return v___y_446_;
}
else
{
uint32_t v___x_449_; uint8_t v___x_450_; 
v___x_449_ = 122;
v___x_450_ = lean_uint32_dec_le(v___y_446_, v___x_449_);
if (v___x_450_ == 0)
{
return v___y_446_;
}
else
{
uint32_t v___x_451_; uint32_t v___x_452_; 
v___x_451_ = 4294967264;
v___x_452_ = lean_uint32_add(v___y_446_, v___x_451_);
return v___x_452_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_fileUriToPath_x3f___lam__0___boxed(lean_object* v___y_453_){
_start:
{
uint32_t v___y_1754__boxed_454_; uint32_t v_res_455_; lean_object* v_r_456_; 
v___y_1754__boxed_454_ = lean_unbox_uint32(v___y_453_);
lean_dec(v___y_453_);
v_res_455_ = l_System_Uri_fileUriToPath_x3f___lam__0(v___y_1754__boxed_454_);
v_r_456_ = lean_box_uint32(v_res_455_);
return v_r_456_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1(uint8_t v___x_457_, lean_object* v_s_458_, lean_object* v_pos_459_){
_start:
{
lean_object* v_str_460_; lean_object* v_startInclusive_461_; lean_object* v_endExclusive_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v_str_460_ = lean_ctor_get(v_s_458_, 0);
v_startInclusive_461_ = lean_ctor_get(v_s_458_, 1);
v_endExclusive_462_ = lean_ctor_get(v_s_458_, 2);
v___x_463_ = lean_nat_add(v_startInclusive_461_, v_pos_459_);
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = lean_nat_sub(v_endExclusive_462_, v___x_463_);
v___x_466_ = lean_nat_dec_eq(v___x_464_, v___x_465_);
lean_dec(v___x_465_);
if (v___x_466_ == 0)
{
uint32_t v___x_467_; uint32_t v___x_468_; uint8_t v___x_469_; 
v___x_467_ = lean_string_utf8_get_fast(v_str_460_, v___x_463_);
v___x_468_ = 47;
v___x_469_ = lean_uint32_dec_eq(v___x_467_, v___x_468_);
if (v___x_469_ == 0)
{
if (v___x_457_ == 0)
{
lean_dec(v___x_463_);
return v_pos_459_;
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_470_ = lean_string_utf8_next_fast(v_str_460_, v___x_463_);
v___x_471_ = lean_nat_sub(v___x_470_, v___x_463_);
lean_dec(v___x_463_);
v___x_472_ = lean_nat_add(v_pos_459_, v___x_471_);
lean_dec(v___x_471_);
v___x_473_ = lean_nat_dec_lt(v_pos_459_, v___x_472_);
if (v___x_473_ == 0)
{
lean_dec(v___x_472_);
return v_pos_459_;
}
else
{
lean_dec(v_pos_459_);
v_pos_459_ = v___x_472_;
goto _start;
}
}
}
else
{
lean_dec(v___x_463_);
return v_pos_459_;
}
}
else
{
lean_dec(v___x_463_);
return v_pos_459_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1___boxed(lean_object* v___x_475_, lean_object* v_s_476_, lean_object* v_pos_477_){
_start:
{
uint8_t v___x_1769__boxed_478_; lean_object* v_res_479_; 
v___x_1769__boxed_478_ = lean_unbox(v___x_475_);
v_res_479_ = l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1(v___x_1769__boxed_478_, v_s_476_, v_pos_477_);
lean_dec_ref(v_s_476_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_Uri_fileUriToPath_x3f_spec__0(lean_object* v_s_480_, lean_object* v_p_481_){
_start:
{
uint32_t v___y_483_; lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_488_ = lean_string_utf8_byte_size(v_s_480_);
v___x_489_ = lean_nat_dec_eq(v_p_481_, v___x_488_);
if (v___x_489_ == 0)
{
uint32_t v___x_490_; uint32_t v___x_491_; uint8_t v___x_492_; 
v___x_490_ = lean_string_utf8_get_fast(v_s_480_, v_p_481_);
v___x_491_ = 47;
v___x_492_ = lean_uint32_dec_eq(v___x_490_, v___x_491_);
if (v___x_492_ == 0)
{
v___y_483_ = v___x_490_;
goto v___jp_482_;
}
else
{
uint32_t v___x_493_; 
v___x_493_ = 92;
v___y_483_ = v___x_493_;
goto v___jp_482_;
}
}
else
{
lean_dec(v_p_481_);
return v_s_480_;
}
v___jp_482_:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
lean_inc(v_p_481_);
v___x_484_ = lean_string_utf8_set(v_s_480_, v_p_481_, v___y_483_);
v___x_485_ = l_Char_utf8Size(v___y_483_);
v___x_486_ = lean_nat_add(v_p_481_, v___x_485_);
lean_dec(v___x_485_);
lean_dec(v_p_481_);
v_s_480_ = v___x_484_;
v_p_481_ = v___x_486_;
goto _start;
}
}
}
static lean_object* _init_l_System_Uri_fileUriToPath_x3f___closed__0(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l_System_Uri_pathToUri___closed__3));
v___x_495_ = lean_string_utf8_byte_size(v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_System_Uri_fileUriToPath_x3f(lean_object* v_uri_497_){
_start:
{
lean_object* v_p_499_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_503_ = ((lean_object*)(l_System_Uri_pathToUri___closed__3));
v___x_504_ = lean_string_utf8_byte_size(v_uri_497_);
v___x_505_ = lean_obj_once(&l_System_Uri_fileUriToPath_x3f___closed__0, &l_System_Uri_fileUriToPath_x3f___closed__0_once, _init_l_System_Uri_fileUriToPath_x3f___closed__0);
v___x_506_ = lean_nat_dec_le(v___x_505_, v___x_504_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; 
v___x_507_ = lean_box(0);
return v___x_507_;
}
else
{
lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = lean_string_memcmp(v_uri_497_, v___x_503_, v___x_508_, v___x_508_, v___x_505_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; 
v___x_510_ = lean_box(0);
return v___x_510_;
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v_p_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v_p_520_; uint8_t v___x_521_; 
v___x_511_ = l_System_Uri_UriEscape_decodeUri(v_uri_497_);
v___x_512_ = lean_unsigned_to_nat(7u);
v___x_513_ = lean_string_utf8_byte_size(v___x_511_);
lean_inc_ref(v___x_511_);
v___x_514_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_514_, 0, v___x_511_);
lean_ctor_set(v___x_514_, 1, v___x_508_);
lean_ctor_set(v___x_514_, 2, v___x_513_);
v___x_515_ = l_String_Slice_Pos_nextn(v___x_514_, v___x_508_, v___x_512_);
lean_dec_ref(v___x_514_);
v_p_516_ = lean_string_utf8_extract(v___x_511_, v___x_515_, v___x_513_);
lean_dec(v___x_515_);
lean_dec_ref(v___x_511_);
v___x_517_ = lean_string_utf8_byte_size(v_p_516_);
lean_inc_ref(v_p_516_);
v___x_518_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_518_, 0, v_p_516_);
lean_ctor_set(v___x_518_, 1, v___x_508_);
lean_ctor_set(v___x_518_, 2, v___x_517_);
v___x_519_ = l_String_Slice_Pos_skipWhile___at___00System_Uri_fileUriToPath_x3f_spec__1(v___x_509_, v___x_518_, v___x_508_);
lean_dec_ref(v___x_518_);
v_p_520_ = lean_string_utf8_extract(v_p_516_, v___x_519_, v___x_517_);
lean_dec(v___x_519_);
lean_dec_ref(v_p_516_);
v___x_521_ = l_System_Platform_isWindows;
if (v___x_521_ == 0)
{
lean_object* v___x_522_; 
v___x_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_522_, 0, v_p_520_);
return v___x_522_;
}
else
{
lean_object* v___f_523_; uint8_t v___y_536_; uint32_t v___y_538_; uint8_t v___y_544_; uint32_t v___y_552_; lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___f_523_ = ((lean_object*)(l_System_Uri_fileUriToPath_x3f___closed__1));
v___x_555_ = lean_unsigned_to_nat(2u);
v___x_556_ = lean_string_length(v_p_520_);
v___x_557_ = lean_nat_dec_le(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
v___y_544_ = v___x_557_;
goto v___jp_543_;
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_558_ = lean_string_utf8_byte_size(v_p_520_);
lean_inc_ref(v_p_520_);
v___x_559_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_559_, 0, v_p_520_);
lean_ctor_set(v___x_559_, 1, v___x_508_);
lean_ctor_set(v___x_559_, 2, v___x_558_);
v___x_560_ = l_String_Slice_Pos_get_x3f(v___x_559_, v___x_508_);
lean_dec_ref(v___x_559_);
if (lean_obj_tag(v___x_560_) == 0)
{
uint32_t v___x_561_; 
v___x_561_ = 65;
v___y_552_ = v___x_561_;
goto v___jp_551_;
}
else
{
lean_object* v_val_562_; uint32_t v___x_563_; 
v_val_562_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_val_562_);
lean_dec_ref(v___x_560_);
v___x_563_ = lean_unbox_uint32(v_val_562_);
lean_dec(v_val_562_);
v___y_552_ = v___x_563_;
goto v___jp_551_;
}
}
v___jp_524_:
{
lean_object* v___x_525_; uint32_t v___x_526_; uint32_t v___x_527_; uint8_t v___x_528_; 
v___x_525_ = lean_unsigned_to_nat(2u);
v___x_526_ = lean_string_utf8_get(v_p_520_, v___x_525_);
v___x_527_ = 58;
v___x_528_ = lean_uint32_dec_eq(v___x_526_, v___x_527_);
if (v___x_528_ == 0)
{
v_p_499_ = v_p_520_;
goto v___jp_498_;
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v_p_534_; 
v___x_529_ = lean_unsigned_to_nat(1u);
v___x_530_ = lean_string_utf8_byte_size(v_p_520_);
lean_inc_ref(v_p_520_);
v___x_531_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_531_, 0, v_p_520_);
lean_ctor_set(v___x_531_, 1, v___x_508_);
lean_ctor_set(v___x_531_, 2, v___x_530_);
v___x_532_ = l_String_Slice_Pos_nextn(v___x_531_, v___x_508_, v___x_529_);
lean_dec_ref(v___x_531_);
v___x_533_ = lean_string_utf8_extract(v_p_520_, v___x_532_, v___x_530_);
lean_dec(v___x_532_);
lean_dec_ref(v_p_520_);
v_p_534_ = l_String_Pos_Raw_modify(v___x_533_, v___x_508_, v___f_523_);
v_p_499_ = v_p_534_;
goto v___jp_498_;
}
}
v___jp_535_:
{
if (v___y_536_ == 0)
{
v_p_499_ = v_p_520_;
goto v___jp_498_;
}
else
{
goto v___jp_524_;
}
}
v___jp_537_:
{
uint32_t v___x_539_; uint8_t v___x_540_; 
v___x_539_ = 97;
v___x_540_ = lean_uint32_dec_le(v___x_539_, v___y_538_);
if (v___x_540_ == 0)
{
v___y_536_ = v___x_540_;
goto v___jp_535_;
}
else
{
uint32_t v___x_541_; uint8_t v___x_542_; 
v___x_541_ = 122;
v___x_542_ = lean_uint32_dec_le(v___y_538_, v___x_541_);
v___y_536_ = v___x_542_;
goto v___jp_535_;
}
}
v___jp_543_:
{
if (v___y_544_ == 0)
{
v_p_499_ = v_p_520_;
goto v___jp_498_;
}
else
{
lean_object* v___x_545_; uint32_t v___x_546_; uint32_t v___x_547_; uint8_t v___x_548_; 
v___x_545_ = lean_unsigned_to_nat(1u);
v___x_546_ = lean_string_utf8_get(v_p_520_, v___x_545_);
v___x_547_ = 65;
v___x_548_ = lean_uint32_dec_le(v___x_547_, v___x_546_);
if (v___x_548_ == 0)
{
v___y_538_ = v___x_546_;
goto v___jp_537_;
}
else
{
uint32_t v___x_549_; uint8_t v___x_550_; 
v___x_549_ = 90;
v___x_550_ = lean_uint32_dec_le(v___x_546_, v___x_549_);
if (v___x_550_ == 0)
{
v___y_538_ = v___x_546_;
goto v___jp_537_;
}
else
{
goto v___jp_524_;
}
}
}
}
v___jp_551_:
{
uint32_t v___x_553_; uint8_t v___x_554_; 
v___x_553_ = 47;
v___x_554_ = lean_uint32_dec_eq(v___y_552_, v___x_553_);
v___y_544_ = v___x_554_;
goto v___jp_543_;
}
}
}
}
v___jp_498_:
{
lean_object* v___x_500_; lean_object* v_p_501_; lean_object* v___x_502_; 
v___x_500_ = lean_unsigned_to_nat(0u);
v_p_501_ = l_String_mapAux___at___00System_Uri_fileUriToPath_x3f_spec__0(v_p_499_, v___x_500_);
v___x_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_502_, 0, v_p_501_);
return v___x_502_;
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_fileUriToPath_x3f___boxed(lean_object* v_uri_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_System_Uri_fileUriToPath_x3f(v_uri_564_);
lean_dec_ref(v_uri_564_);
return v_res_565_;
}
}
lean_object* runtime_initialize_Init_System_FilePath(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
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
