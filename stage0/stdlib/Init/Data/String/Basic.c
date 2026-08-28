// Lean compiler output
// Module: Init.Data.String.Basic
// Imports: public import Init.Data.String.Decode public import Init.Data.String.Defs import Init.Data.ByteArray.Lemmas import Init.Data.Char.Lemmas public import Init.Data.Char.Basic import Init.ByCases import Init.Data.Array.Bootstrap import Init.Data.Array.Lemmas import Init.Data.List.Nat.TakeDrop import Init.Data.List.Sublist import Init.Data.List.TakeDrop import Init.Data.Option.Lemmas import Init.Omega
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
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_instInhabitedSlice;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_land(uint8_t, uint8_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint32_t lean_uint8_to_uint32(uint8_t);
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
uint32_t lean_uint32_lor(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_ByteArray_utf8Decode_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_ByteArray_utf8Decode_x3f___closed__0 = (const lean_object*)&l_ByteArray_utf8Decode_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8___boxed(lean_object*);
LEAN_EXPORT uint8_t l_instDecidableIsValidUTF8(lean_object*);
LEAN_EXPORT lean_object* l_instDecidableIsValidUTF8___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8_x3f(lean_object*);
static const lean_string_object l_String_fromUTF8_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_String_fromUTF8_x21___closed__0 = (const lean_object*)&l_String_fromUTF8_x21___closed__0_value;
static const lean_string_object l_String_fromUTF8_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Init.Data.String.Basic"};
static const lean_object* l_String_fromUTF8_x21___closed__1 = (const lean_object*)&l_String_fromUTF8_x21___closed__1_value;
static const lean_string_object l_String_fromUTF8_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "String.fromUTF8!"};
static const lean_object* l_String_fromUTF8_x21___closed__2 = (const lean_object*)&l_String_fromUTF8_x21___closed__2_value;
static const lean_string_object l_String_fromUTF8_x21___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid UTF-8 string"};
static const lean_object* l_String_fromUTF8_x21___closed__3 = (const lean_object*)&l_String_fromUTF8_x21___closed__3_value;
static lean_once_cell_t l_String_fromUTF8_x21___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_fromUTF8_x21___closed__4;
LEAN_EXPORT lean_object* l_String_fromUTF8_x21(lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_toArray(lean_object*);
lean_object* lean_string_data(lean_object*);
LEAN_EXPORT lean_object* l_String_toList___boxed(lean_object*);
lean_object* lean_string_data(lean_object*);
LEAN_EXPORT lean_object* l_String_data___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instLT;
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_decidableLT___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instLE;
LEAN_EXPORT uint8_t l_String_decLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_decLE___boxed(lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValid___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableIsValid(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableIsValid___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_extract___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_extract___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_copy(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_copy___boxed(lean_object*);
LEAN_EXPORT uint8_t l_String_Pos_Raw_isValidForSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValidForSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableIsValidForSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableIsValidForSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_str(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_str___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStart(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStart___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_sliceTo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_sliceTo___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_slice(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_slice___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_slice_x21_spec__0(lean_object*);
static const lean_string_object l_String_Slice_slice_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "String.Slice.slice!"};
static const lean_object* l_String_Slice_slice_x21___closed__0 = (const lean_object*)&l_String_Slice_slice_x21___closed__0_value;
static const lean_string_object l_String_Slice_slice_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "Starting position must be less than or equal to end position."};
static const lean_object* l_String_Slice_slice_x21___closed__1 = (const lean_object*)&l_String_Slice_slice_x21___closed__1_value;
static lean_once_cell_t l_String_Slice_slice_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_slice_x21___closed__2;
LEAN_EXPORT lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_slice_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21___boxed(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_decodeChar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_String_Slice_Pos_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_String_Slice_Pos_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1;
LEAN_EXPORT uint32_t l_panic___at___00String_Slice_Pos_get_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed(lean_object*);
static const lean_string_object l_String_Slice_Pos_get_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "String.Slice.Pos.get!"};
static const lean_object* l_String_Slice_Pos_get_x21___closed__0 = (const lean_object*)&l_String_Slice_Pos_get_x21___closed__0_value;
static const lean_string_object l_String_Slice_Pos_get_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Cannot retrieve character at end position"};
static const lean_object* l_String_Slice_Pos_get_x21___closed__1 = (const lean_object*)&l_String_Slice_Pos_get_x21___closed__1_value;
static lean_once_cell_t l_String_Slice_Pos_get_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_Pos_get_x21___closed__2;
LEAN_EXPORT uint32_t l_String_Slice_Pos_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_String_Pos_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_get___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_String_Pos_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_get___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_get_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_String_Pos_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_get_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Pos_byte___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_byte___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Pos_byte(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_byte___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofCopy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_next(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_String_Slice_Pos_next_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "String.Slice.Pos.next!"};
static const lean_object* l_String_Slice_Pos_next_x21___closed__0 = (const lean_object*)&l_String_Slice_Pos_next_x21___closed__0_value;
static const lean_string_object l_String_Slice_Pos_next_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Cannot advance the end position"};
static const lean_object* l_String_Slice_Pos_next_x21___closed__1 = (const lean_object*)&l_String_Slice_Pos_next_x21___closed__1_value;
static lean_once_cell_t l_String_Slice_Pos_next_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_Pos_next_x21___closed__2;
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_pos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_pos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_String_Slice_pos_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "String.Slice.pos!"};
static const lean_object* l_String_Slice_pos_x21___closed__0 = (const lean_object*)&l_String_Slice_pos_x21___closed__0_value;
static const lean_string_object l_String_Slice_pos_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Offset is not at a valid UTF-8 character boundary"};
static const lean_object* l_String_Slice_pos_x21___closed__1 = (const lean_object*)&l_String_Slice_pos_x21___closed__1_value;
static lean_once_cell_t l_String_Slice_pos_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_pos_x21___closed__2;
LEAN_EXPORT lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_pos_x21___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_next___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_next_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_next_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_next_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_next_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_pos___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_pos___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_pos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_pos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_pos_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_pos_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_pos_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_cast(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_String_Pos_Raw_utf8GetAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_String_utf8GetAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8GetAux___boxed(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_get___boxed(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_get_opt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x3f___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_get_opt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_get_x3f___boxed(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_bang(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x21___boxed(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_bang(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_get_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8SetAux(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8SetAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_sliceTo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_replaceEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_sliceFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_replaceStart(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_slice___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_slice(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_slice_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_slice_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_slice_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_sliceTo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofSlice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_slice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_Pos_sliceOrPanic___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "String.Slice.Pos.sliceOrPanic"};
static const lean_object* l_String_Slice_Pos_sliceOrPanic___redArg___closed__0 = (const lean_object*)&l_String_Slice_Pos_sliceOrPanic___redArg___closed__0_value;
static const lean_string_object l_String_Slice_Pos_sliceOrPanic___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Position is outside of the bounds of the slice."};
static const lean_object* l_String_Slice_Pos_sliceOrPanic___redArg___closed__1 = (const lean_object*)&l_String_Slice_Pos_sliceOrPanic___redArg___closed__1_value;
static lean_once_cell_t l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_Pos_sliceOrPanic___redArg___closed__2;
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_Pos_ofSlice_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "String.Slice.Pos.ofSlice!"};
static const lean_object* l_String_Slice_Pos_ofSlice_x21___redArg___closed__0 = (const lean_object*)&l_String_Slice_Pos_ofSlice_x21___redArg___closed__0_value;
static lean_once_cell_t l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_Pos_ofSlice_x21___redArg___closed__1;
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_Pos_slice_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "String.Slice.Pos.slice!"};
static const lean_object* l_String_Slice_Pos_slice_x21___redArg___closed__0 = (const lean_object*)&l_String_Slice_Pos_slice_x21___redArg___closed__0_value;
static const lean_string_object l_String_Slice_Pos_slice_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 126, .m_capacity = 126, .m_length = 125, .m_data = "Starting position must be less than or equal to end position and position must be between starting position and end position."};
static const lean_object* l_String_Slice_Pos_slice_x21___redArg___closed__1 = (const lean_object*)&l_String_Slice_Pos_slice_x21___redArg___closed__1_value;
static lean_once_cell_t l_String_Slice_Pos_slice_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_Pos_slice_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_slice_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_extract___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_next___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_next___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8PrevAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8PrevAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_prev___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_prev___boxed(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_atEnd___boxed(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_atEnd___boxed(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x27___boxed(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_get_x27___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_next_x27___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_next_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_firstDiffPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_firstDiffPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_offsetOfPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_offsetOfPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_offsetofpos(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Pos_Raw_substrEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_substrEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_substrEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_substrEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go___redArg(lean_object* v_b_1_, lean_object* v_i_2_, lean_object* v_acc_3_){
_start:
{
uint32_t v_val_5_; lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = lean_byte_array_size(v_b_1_);
v___x_12_ = lean_nat_dec_lt(v_i_2_, v___x_11_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; 
lean_dec(v_i_2_);
v___x_13_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_13_, 0, v_acc_3_);
return v___x_13_;
}
else
{
if (v___x_12_ == 0)
{
lean_object* v___x_14_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_14_ = lean_box(0);
return v___x_14_;
}
else
{
uint8_t v___x_15_; uint8_t v___x_16_; uint8_t v___x_17_; uint8_t v___x_18_; uint8_t v___x_19_; 
v___x_15_ = lean_byte_array_fget(v_b_1_, v_i_2_);
v___x_16_ = 128;
v___x_17_ = lean_uint8_land(v___x_15_, v___x_16_);
v___x_18_ = 0;
v___x_19_ = lean_uint8_dec_eq(v___x_17_, v___x_18_);
if (v___x_19_ == 0)
{
uint8_t v___x_20_; uint8_t v___x_21_; uint8_t v___x_22_; uint8_t v___x_23_; 
v___x_20_ = 224;
v___x_21_ = lean_uint8_land(v___x_15_, v___x_20_);
v___x_22_ = 192;
v___x_23_ = lean_uint8_dec_eq(v___x_21_, v___x_22_);
if (v___x_23_ == 0)
{
uint8_t v___x_24_; uint8_t v___x_25_; uint8_t v___x_26_; 
v___x_24_ = 240;
v___x_25_ = lean_uint8_land(v___x_15_, v___x_24_);
v___x_26_ = lean_uint8_dec_eq(v___x_25_, v___x_20_);
if (v___x_26_ == 0)
{
uint8_t v___x_27_; uint8_t v___x_28_; uint8_t v___x_29_; 
v___x_27_ = 248;
v___x_28_ = lean_uint8_land(v___x_15_, v___x_27_);
v___x_29_ = lean_uint8_dec_eq(v___x_28_, v___x_24_);
if (v___x_29_ == 0)
{
lean_object* v___x_30_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_30_ = lean_box(0);
return v___x_30_;
}
else
{
lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_31_ = lean_unsigned_to_nat(3u);
v___x_32_ = lean_nat_add(v_i_2_, v___x_31_);
v___x_33_ = lean_nat_dec_lt(v___x_32_, v___x_11_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; 
lean_dec(v___x_32_);
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_34_ = lean_box(0);
return v___x_34_;
}
else
{
lean_object* v___x_35_; lean_object* v___x_36_; uint8_t v___x_37_; uint8_t v___x_38_; uint8_t v___x_39_; 
v___x_35_ = lean_unsigned_to_nat(1u);
v___x_36_ = lean_nat_add(v_i_2_, v___x_35_);
v___x_37_ = lean_byte_array_fget(v_b_1_, v___x_36_);
lean_dec(v___x_36_);
v___x_38_ = lean_uint8_land(v___x_37_, v___x_22_);
v___x_39_ = lean_uint8_dec_eq(v___x_38_, v___x_16_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; 
lean_dec(v___x_32_);
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_40_ = lean_box(0);
return v___x_40_;
}
else
{
lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; uint8_t v___x_44_; uint8_t v___x_45_; 
v___x_41_ = lean_unsigned_to_nat(2u);
v___x_42_ = lean_nat_add(v_i_2_, v___x_41_);
v___x_43_ = lean_byte_array_fget(v_b_1_, v___x_42_);
lean_dec(v___x_42_);
v___x_44_ = lean_uint8_land(v___x_43_, v___x_22_);
v___x_45_ = lean_uint8_dec_eq(v___x_44_, v___x_16_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; 
lean_dec(v___x_32_);
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_46_ = lean_box(0);
return v___x_46_;
}
else
{
uint8_t v___x_47_; uint8_t v___x_48_; uint8_t v___x_49_; 
v___x_47_ = lean_byte_array_fget(v_b_1_, v___x_32_);
lean_dec(v___x_32_);
v___x_48_ = lean_uint8_land(v___x_47_, v___x_22_);
v___x_49_ = lean_uint8_dec_eq(v___x_48_, v___x_16_);
if (v___x_49_ == 0)
{
lean_object* v___x_50_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_50_ = lean_box(0);
return v___x_50_;
}
else
{
uint8_t v___x_51_; uint8_t v_b_u2080_52_; uint8_t v___x_53_; uint8_t v_b_u2081_54_; uint8_t v_b_u2082_55_; uint8_t v_b_u2083_56_; uint32_t v___x_57_; uint32_t v___x_58_; uint32_t v___x_59_; uint32_t v___x_60_; uint32_t v___x_61_; uint32_t v___x_62_; uint32_t v___x_63_; uint32_t v___x_64_; uint32_t v___x_65_; uint32_t v___x_66_; uint32_t v___x_67_; uint32_t v___x_68_; uint32_t v_r_69_; uint32_t v___x_70_; uint8_t v___x_71_; 
v___x_51_ = 7;
v_b_u2080_52_ = lean_uint8_land(v___x_15_, v___x_51_);
v___x_53_ = 63;
v_b_u2081_54_ = lean_uint8_land(v___x_37_, v___x_53_);
v_b_u2082_55_ = lean_uint8_land(v___x_43_, v___x_53_);
v_b_u2083_56_ = lean_uint8_land(v___x_47_, v___x_53_);
v___x_57_ = lean_uint8_to_uint32(v_b_u2080_52_);
v___x_58_ = 18;
v___x_59_ = lean_uint32_shift_left(v___x_57_, v___x_58_);
v___x_60_ = lean_uint8_to_uint32(v_b_u2081_54_);
v___x_61_ = 12;
v___x_62_ = lean_uint32_shift_left(v___x_60_, v___x_61_);
v___x_63_ = lean_uint32_lor(v___x_59_, v___x_62_);
v___x_64_ = lean_uint8_to_uint32(v_b_u2082_55_);
v___x_65_ = 6;
v___x_66_ = lean_uint32_shift_left(v___x_64_, v___x_65_);
v___x_67_ = lean_uint32_lor(v___x_63_, v___x_66_);
v___x_68_ = lean_uint8_to_uint32(v_b_u2083_56_);
v_r_69_ = lean_uint32_lor(v___x_67_, v___x_68_);
v___x_70_ = 65536;
v___x_71_ = lean_uint32_dec_lt(v_r_69_, v___x_70_);
if (v___x_71_ == 0)
{
uint32_t v___x_72_; uint8_t v___x_73_; 
v___x_72_ = 1114111;
v___x_73_ = lean_uint32_dec_lt(v___x_72_, v_r_69_);
if (v___x_73_ == 0)
{
v_val_5_ = v_r_69_;
goto v___jp_4_;
}
else
{
lean_object* v___x_74_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_74_ = lean_box(0);
return v___x_74_;
}
}
else
{
lean_object* v___x_75_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_75_ = lean_box(0);
return v___x_75_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_76_ = lean_unsigned_to_nat(2u);
v___x_77_ = lean_nat_add(v_i_2_, v___x_76_);
v___x_78_ = lean_nat_dec_lt(v___x_77_, v___x_11_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; 
lean_dec(v___x_77_);
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_79_ = lean_box(0);
return v___x_79_;
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; uint8_t v___x_83_; uint8_t v___x_84_; 
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = lean_nat_add(v_i_2_, v___x_80_);
v___x_82_ = lean_byte_array_fget(v_b_1_, v___x_81_);
lean_dec(v___x_81_);
v___x_83_ = lean_uint8_land(v___x_82_, v___x_22_);
v___x_84_ = lean_uint8_dec_eq(v___x_83_, v___x_16_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; 
lean_dec(v___x_77_);
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_85_ = lean_box(0);
return v___x_85_;
}
else
{
uint8_t v___x_86_; uint8_t v___x_87_; uint8_t v___x_88_; 
v___x_86_ = lean_byte_array_fget(v_b_1_, v___x_77_);
lean_dec(v___x_77_);
v___x_87_ = lean_uint8_land(v___x_86_, v___x_22_);
v___x_88_ = lean_uint8_dec_eq(v___x_87_, v___x_16_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_89_ = lean_box(0);
return v___x_89_;
}
else
{
uint8_t v___x_90_; uint8_t v_b_u2080_91_; uint8_t v___x_92_; uint8_t v_b_u2081_93_; uint8_t v_b_u2082_94_; uint32_t v___x_95_; uint32_t v___x_96_; uint32_t v___x_97_; uint32_t v___x_98_; uint32_t v___x_99_; uint32_t v___x_100_; uint32_t v___x_101_; uint32_t v___x_102_; uint32_t v_r_103_; uint8_t v___y_105_; uint32_t v___x_107_; uint8_t v___x_108_; 
v___x_90_ = 15;
v_b_u2080_91_ = lean_uint8_land(v___x_15_, v___x_90_);
v___x_92_ = 63;
v_b_u2081_93_ = lean_uint8_land(v___x_82_, v___x_92_);
v_b_u2082_94_ = lean_uint8_land(v___x_86_, v___x_92_);
v___x_95_ = lean_uint8_to_uint32(v_b_u2080_91_);
v___x_96_ = 12;
v___x_97_ = lean_uint32_shift_left(v___x_95_, v___x_96_);
v___x_98_ = lean_uint8_to_uint32(v_b_u2081_93_);
v___x_99_ = 6;
v___x_100_ = lean_uint32_shift_left(v___x_98_, v___x_99_);
v___x_101_ = lean_uint32_lor(v___x_97_, v___x_100_);
v___x_102_ = lean_uint8_to_uint32(v_b_u2082_94_);
v_r_103_ = lean_uint32_lor(v___x_101_, v___x_102_);
v___x_107_ = 2048;
v___x_108_ = lean_uint32_dec_lt(v_r_103_, v___x_107_);
if (v___x_108_ == 0)
{
uint32_t v___x_109_; uint8_t v___x_110_; 
v___x_109_ = 55296;
v___x_110_ = lean_uint32_dec_le(v___x_109_, v_r_103_);
if (v___x_110_ == 0)
{
v___y_105_ = v___x_110_;
goto v___jp_104_;
}
else
{
uint32_t v___x_111_; uint8_t v___x_112_; 
v___x_111_ = 57343;
v___x_112_ = lean_uint32_dec_le(v_r_103_, v___x_111_);
v___y_105_ = v___x_112_;
goto v___jp_104_;
}
}
else
{
lean_object* v___x_113_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_113_ = lean_box(0);
return v___x_113_;
}
v___jp_104_:
{
if (v___y_105_ == 0)
{
v_val_5_ = v_r_103_;
goto v___jp_4_;
}
else
{
lean_object* v___x_106_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_106_ = lean_box(0);
return v___x_106_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_114_ = lean_unsigned_to_nat(1u);
v___x_115_ = lean_nat_add(v_i_2_, v___x_114_);
v___x_116_ = lean_nat_dec_lt(v___x_115_, v___x_11_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; 
lean_dec(v___x_115_);
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_117_ = lean_box(0);
return v___x_117_;
}
else
{
uint8_t v___x_118_; uint8_t v___x_119_; uint8_t v___x_120_; 
v___x_118_ = lean_byte_array_fget(v_b_1_, v___x_115_);
lean_dec(v___x_115_);
v___x_119_ = lean_uint8_land(v___x_118_, v___x_22_);
v___x_120_ = lean_uint8_dec_eq(v___x_119_, v___x_16_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_121_ = lean_box(0);
return v___x_121_;
}
else
{
uint8_t v___x_122_; uint8_t v_b_u2080_123_; uint8_t v___x_124_; uint8_t v_b_u2081_125_; uint32_t v___x_126_; uint32_t v___x_127_; uint32_t v___x_128_; uint32_t v___x_129_; uint32_t v_r_130_; uint32_t v___x_131_; uint8_t v___x_132_; 
v___x_122_ = 31;
v_b_u2080_123_ = lean_uint8_land(v___x_15_, v___x_122_);
v___x_124_ = 63;
v_b_u2081_125_ = lean_uint8_land(v___x_118_, v___x_124_);
v___x_126_ = lean_uint8_to_uint32(v_b_u2080_123_);
v___x_127_ = 6;
v___x_128_ = lean_uint32_shift_left(v___x_126_, v___x_127_);
v___x_129_ = lean_uint8_to_uint32(v_b_u2081_125_);
v_r_130_ = lean_uint32_lor(v___x_128_, v___x_129_);
v___x_131_ = 128;
v___x_132_ = lean_uint32_dec_lt(v_r_130_, v___x_131_);
if (v___x_132_ == 0)
{
v_val_5_ = v_r_130_;
goto v___jp_4_;
}
else
{
lean_object* v___x_133_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_133_ = lean_box(0);
return v___x_133_;
}
}
}
}
}
else
{
uint32_t v___x_134_; 
v___x_134_ = lean_uint8_to_uint32(v___x_15_);
v_val_5_ = v___x_134_;
goto v___jp_4_;
}
}
}
v___jp_4_:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_6_ = l_Char_utf8Size(v_val_5_);
v___x_7_ = lean_nat_add(v_i_2_, v___x_6_);
lean_dec(v___x_6_);
lean_dec(v_i_2_);
v___x_8_ = lean_box_uint32(v_val_5_);
v___x_9_ = lean_array_push(v_acc_3_, v___x_8_);
v_i_2_ = v___x_7_;
v_acc_3_ = v___x_9_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go___redArg___boxed(lean_object* v_b_135_, lean_object* v_i_136_, lean_object* v_acc_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_ByteArray_utf8Decode_x3f_go___redArg(v_b_135_, v_i_136_, v_acc_137_);
lean_dec_ref(v_b_135_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go(lean_object* v_b_139_, lean_object* v_i_140_, lean_object* v_acc_141_, lean_object* v_hi_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_ByteArray_utf8Decode_x3f_go___redArg(v_b_139_, v_i_140_, v_acc_141_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go___boxed(lean_object* v_b_144_, lean_object* v_i_145_, lean_object* v_acc_146_, lean_object* v_hi_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_ByteArray_utf8Decode_x3f_go(v_b_144_, v_i_145_, v_acc_146_, v_hi_147_);
lean_dec_ref(v_b_144_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__1_splitter___redArg(lean_object* v_x_149_, lean_object* v_h__1_150_, lean_object* v_h__2_151_){
_start:
{
if (lean_obj_tag(v_x_149_) == 0)
{
lean_object* v___x_152_; 
lean_dec(v_h__2_151_);
v___x_152_ = lean_apply_1(v_h__1_150_, lean_box(0));
return v___x_152_;
}
else
{
lean_object* v_val_153_; lean_object* v___x_154_; 
lean_dec(v_h__1_150_);
v_val_153_ = lean_ctor_get(v_x_149_, 0);
lean_inc(v_val_153_);
lean_dec_ref_known(v_x_149_, 1);
v___x_154_ = lean_apply_2(v_h__2_151_, v_val_153_, lean_box(0));
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__1_splitter(lean_object* v_motive_155_, lean_object* v_x_156_, lean_object* v_h__1_157_, lean_object* v_h__2_158_){
_start:
{
if (lean_obj_tag(v_x_156_) == 0)
{
lean_object* v___x_159_; 
lean_dec(v_h__2_158_);
v___x_159_ = lean_apply_1(v_h__1_157_, lean_box(0));
return v___x_159_;
}
else
{
lean_object* v_val_160_; lean_object* v___x_161_; 
lean_dec(v_h__1_157_);
v_val_160_ = lean_ctor_get(v_x_156_, 0);
lean_inc(v_val_160_);
lean_dec_ref_known(v_x_156_, 1);
v___x_161_ = lean_apply_2(v_h__2_158_, v_val_160_, lean_box(0));
return v___x_161_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f(lean_object* v_b_164_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = ((lean_object*)(l_ByteArray_utf8Decode_x3f___closed__0));
v___x_167_ = l_ByteArray_utf8Decode_x3f_go___redArg(v_b_164_, v___x_165_, v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f___boxed(lean_object* v_b_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_ByteArray_utf8Decode_x3f(v_b_168_);
lean_dec_ref(v_b_168_);
return v_res_169_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8_go___redArg(lean_object* v_b_170_, lean_object* v_i_171_){
_start:
{
lean_object* v___y_173_; uint8_t v___y_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_195_ = lean_byte_array_size(v_b_170_);
v___x_196_ = lean_nat_dec_lt(v_i_171_, v___x_195_);
if (v___x_196_ == 0)
{
uint8_t v___x_197_; 
lean_dec(v_i_171_);
v___x_197_ = 1;
return v___x_197_;
}
else
{
if (v___x_196_ == 0)
{
lean_dec(v_i_171_);
return v___x_196_;
}
else
{
uint8_t v___x_198_; uint8_t v___x_199_; uint8_t v___x_200_; uint8_t v___x_201_; uint8_t v___x_202_; 
v___x_198_ = lean_byte_array_fget(v_b_170_, v_i_171_);
v___x_199_ = 128;
v___x_200_ = lean_uint8_land(v___x_198_, v___x_199_);
v___x_201_ = 0;
v___x_202_ = lean_uint8_dec_eq(v___x_200_, v___x_201_);
if (v___x_202_ == 0)
{
uint8_t v___x_203_; uint8_t v___x_204_; uint8_t v___x_205_; uint8_t v___x_206_; 
v___x_203_ = 224;
v___x_204_ = lean_uint8_land(v___x_198_, v___x_203_);
v___x_205_ = 192;
v___x_206_ = lean_uint8_dec_eq(v___x_204_, v___x_205_);
if (v___x_206_ == 0)
{
uint8_t v___x_207_; uint8_t v___x_208_; uint8_t v___x_209_; 
v___x_207_ = 240;
v___x_208_ = lean_uint8_land(v___x_198_, v___x_207_);
v___x_209_ = lean_uint8_dec_eq(v___x_208_, v___x_203_);
if (v___x_209_ == 0)
{
uint8_t v___x_210_; uint8_t v___x_211_; uint8_t v___x_212_; 
v___x_210_ = 248;
v___x_211_ = lean_uint8_land(v___x_198_, v___x_210_);
v___x_212_ = lean_uint8_dec_eq(v___x_211_, v___x_207_);
if (v___x_212_ == 0)
{
lean_dec(v_i_171_);
return v___x_212_;
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_213_ = lean_unsigned_to_nat(3u);
v___x_214_ = lean_nat_add(v_i_171_, v___x_213_);
v___x_215_ = lean_nat_dec_lt(v___x_214_, v___x_195_);
if (v___x_215_ == 0)
{
lean_dec(v___x_214_);
lean_dec(v_i_171_);
return v___x_215_;
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; uint8_t v___x_219_; uint8_t v___x_220_; 
v___x_216_ = lean_unsigned_to_nat(1u);
v___x_217_ = lean_nat_add(v_i_171_, v___x_216_);
v___x_218_ = lean_byte_array_fget(v_b_170_, v___x_217_);
lean_dec(v___x_217_);
v___x_219_ = lean_uint8_land(v___x_218_, v___x_205_);
v___x_220_ = lean_uint8_dec_eq(v___x_219_, v___x_199_);
if (v___x_220_ == 0)
{
lean_dec(v___x_214_);
lean_dec(v_i_171_);
return v___x_220_;
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; uint8_t v___x_224_; uint8_t v___x_225_; 
v___x_221_ = lean_unsigned_to_nat(2u);
v___x_222_ = lean_nat_add(v_i_171_, v___x_221_);
v___x_223_ = lean_byte_array_fget(v_b_170_, v___x_222_);
lean_dec(v___x_222_);
v___x_224_ = lean_uint8_land(v___x_223_, v___x_205_);
v___x_225_ = lean_uint8_dec_eq(v___x_224_, v___x_199_);
if (v___x_225_ == 0)
{
lean_dec(v___x_214_);
lean_dec(v_i_171_);
return v___x_209_;
}
else
{
uint8_t v___x_226_; uint8_t v___x_227_; uint8_t v___x_228_; 
v___x_226_ = lean_byte_array_fget(v_b_170_, v___x_214_);
lean_dec(v___x_214_);
v___x_227_ = lean_uint8_land(v___x_226_, v___x_205_);
v___x_228_ = lean_uint8_dec_eq(v___x_227_, v___x_199_);
if (v___x_228_ == 0)
{
lean_dec(v_i_171_);
return v___x_209_;
}
else
{
uint8_t v___x_229_; uint8_t v_b_u2080_230_; uint8_t v___x_231_; uint8_t v_b_u2081_232_; uint8_t v_b_u2082_233_; uint8_t v_b_u2083_234_; uint32_t v___x_235_; uint32_t v___x_236_; uint32_t v___x_237_; uint32_t v___x_238_; uint32_t v___x_239_; uint32_t v___x_240_; uint32_t v___x_241_; uint32_t v___x_242_; uint32_t v___x_243_; uint32_t v___x_244_; uint32_t v___x_245_; uint32_t v___x_246_; uint32_t v_r_247_; uint32_t v___x_248_; uint8_t v___x_249_; 
v___x_229_ = 7;
v_b_u2080_230_ = lean_uint8_land(v___x_198_, v___x_229_);
v___x_231_ = 63;
v_b_u2081_232_ = lean_uint8_land(v___x_218_, v___x_231_);
v_b_u2082_233_ = lean_uint8_land(v___x_223_, v___x_231_);
v_b_u2083_234_ = lean_uint8_land(v___x_226_, v___x_231_);
v___x_235_ = lean_uint8_to_uint32(v_b_u2080_230_);
v___x_236_ = 18;
v___x_237_ = lean_uint32_shift_left(v___x_235_, v___x_236_);
v___x_238_ = lean_uint8_to_uint32(v_b_u2081_232_);
v___x_239_ = 12;
v___x_240_ = lean_uint32_shift_left(v___x_238_, v___x_239_);
v___x_241_ = lean_uint32_lor(v___x_237_, v___x_240_);
v___x_242_ = lean_uint8_to_uint32(v_b_u2082_233_);
v___x_243_ = 6;
v___x_244_ = lean_uint32_shift_left(v___x_242_, v___x_243_);
v___x_245_ = lean_uint32_lor(v___x_241_, v___x_244_);
v___x_246_ = lean_uint8_to_uint32(v_b_u2083_234_);
v_r_247_ = lean_uint32_lor(v___x_245_, v___x_246_);
v___x_248_ = 65536;
v___x_249_ = lean_uint32_dec_le(v___x_248_, v_r_247_);
if (v___x_249_ == 0)
{
v___y_194_ = v___x_249_;
goto v___jp_193_;
}
else
{
uint32_t v___x_250_; uint8_t v___x_251_; 
v___x_250_ = 1114111;
v___x_251_ = lean_uint32_dec_le(v_r_247_, v___x_250_);
v___y_194_ = v___x_251_;
goto v___jp_193_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_252_ = lean_unsigned_to_nat(2u);
v___x_253_ = lean_nat_add(v_i_171_, v___x_252_);
v___x_254_ = lean_nat_dec_lt(v___x_253_, v___x_195_);
if (v___x_254_ == 0)
{
lean_dec(v___x_253_);
lean_dec(v_i_171_);
return v___x_254_;
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; uint8_t v___x_258_; uint8_t v___x_259_; 
v___x_255_ = lean_unsigned_to_nat(1u);
v___x_256_ = lean_nat_add(v_i_171_, v___x_255_);
v___x_257_ = lean_byte_array_fget(v_b_170_, v___x_256_);
lean_dec(v___x_256_);
v___x_258_ = lean_uint8_land(v___x_257_, v___x_205_);
v___x_259_ = lean_uint8_dec_eq(v___x_258_, v___x_199_);
if (v___x_259_ == 0)
{
lean_dec(v___x_253_);
lean_dec(v_i_171_);
return v___x_259_;
}
else
{
uint8_t v___x_260_; uint8_t v___x_261_; uint8_t v___x_262_; 
v___x_260_ = lean_byte_array_fget(v_b_170_, v___x_253_);
lean_dec(v___x_253_);
v___x_261_ = lean_uint8_land(v___x_260_, v___x_205_);
v___x_262_ = lean_uint8_dec_eq(v___x_261_, v___x_199_);
if (v___x_262_ == 0)
{
lean_dec(v_i_171_);
return v___x_262_;
}
else
{
uint8_t v___x_263_; uint8_t v_b_u2080_264_; uint8_t v___x_265_; uint8_t v_b_u2081_266_; uint8_t v_b_u2082_267_; uint32_t v___x_268_; uint32_t v___x_269_; uint32_t v___x_270_; uint32_t v___x_271_; uint32_t v___x_272_; uint32_t v___x_273_; uint32_t v___x_274_; uint32_t v___x_275_; uint32_t v_r_276_; uint32_t v___x_277_; uint8_t v___x_278_; uint8_t v___y_280_; uint32_t v___x_281_; uint8_t v___x_282_; 
v___x_263_ = 15;
v_b_u2080_264_ = lean_uint8_land(v___x_198_, v___x_263_);
v___x_265_ = 63;
v_b_u2081_266_ = lean_uint8_land(v___x_257_, v___x_265_);
v_b_u2082_267_ = lean_uint8_land(v___x_260_, v___x_265_);
v___x_268_ = lean_uint8_to_uint32(v_b_u2080_264_);
v___x_269_ = 12;
v___x_270_ = lean_uint32_shift_left(v___x_268_, v___x_269_);
v___x_271_ = lean_uint8_to_uint32(v_b_u2081_266_);
v___x_272_ = 6;
v___x_273_ = lean_uint32_shift_left(v___x_271_, v___x_272_);
v___x_274_ = lean_uint32_lor(v___x_270_, v___x_273_);
v___x_275_ = lean_uint8_to_uint32(v_b_u2082_267_);
v_r_276_ = lean_uint32_lor(v___x_274_, v___x_275_);
v___x_277_ = 2048;
v___x_278_ = lean_uint32_dec_le(v___x_277_, v_r_276_);
v___x_281_ = 55296;
v___x_282_ = lean_uint32_dec_lt(v_r_276_, v___x_281_);
if (v___x_282_ == 0)
{
uint32_t v___x_283_; uint8_t v___x_284_; 
v___x_283_ = 57343;
v___x_284_ = lean_uint32_dec_lt(v___x_283_, v_r_276_);
v___y_280_ = v___x_284_;
goto v___jp_279_;
}
else
{
v___y_280_ = v___x_282_;
goto v___jp_279_;
}
v___jp_279_:
{
if (v___x_278_ == 0)
{
v___y_194_ = v___x_278_;
goto v___jp_193_;
}
else
{
v___y_194_ = v___y_280_;
goto v___jp_193_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_285_ = lean_unsigned_to_nat(1u);
v___x_286_ = lean_nat_add(v_i_171_, v___x_285_);
v___x_287_ = lean_nat_dec_lt(v___x_286_, v___x_195_);
if (v___x_287_ == 0)
{
lean_dec(v___x_286_);
lean_dec(v_i_171_);
return v___x_287_;
}
else
{
uint8_t v___x_288_; uint8_t v___x_289_; uint8_t v___x_290_; 
v___x_288_ = lean_byte_array_fget(v_b_170_, v___x_286_);
lean_dec(v___x_286_);
v___x_289_ = lean_uint8_land(v___x_288_, v___x_205_);
v___x_290_ = lean_uint8_dec_eq(v___x_289_, v___x_199_);
if (v___x_290_ == 0)
{
lean_dec(v_i_171_);
return v___x_290_;
}
else
{
uint8_t v___x_291_; uint8_t v_b_u2080_292_; uint8_t v___x_293_; uint8_t v_b_u2081_294_; uint32_t v___x_295_; uint32_t v___x_296_; uint32_t v___x_297_; uint32_t v___x_298_; uint32_t v_r_299_; uint32_t v___x_300_; uint8_t v___x_301_; 
v___x_291_ = 31;
v_b_u2080_292_ = lean_uint8_land(v___x_198_, v___x_291_);
v___x_293_ = 63;
v_b_u2081_294_ = lean_uint8_land(v___x_288_, v___x_293_);
v___x_295_ = lean_uint8_to_uint32(v_b_u2080_292_);
v___x_296_ = 6;
v___x_297_ = lean_uint32_shift_left(v___x_295_, v___x_296_);
v___x_298_ = lean_uint8_to_uint32(v_b_u2081_294_);
v_r_299_ = lean_uint32_lor(v___x_297_, v___x_298_);
v___x_300_ = 128;
v___x_301_ = lean_uint32_dec_le(v___x_300_, v_r_299_);
v___y_194_ = v___x_301_;
goto v___jp_193_;
}
}
}
}
else
{
goto v___jp_176_;
}
}
}
v___jp_172_:
{
lean_object* v___x_174_; 
v___x_174_ = lean_nat_add(v_i_171_, v___y_173_);
lean_dec(v_i_171_);
v_i_171_ = v___x_174_;
goto _start;
}
v___jp_176_:
{
uint8_t v___x_177_; uint8_t v___x_178_; uint8_t v___x_179_; uint8_t v___x_180_; uint8_t v___x_181_; 
v___x_177_ = lean_byte_array_fget(v_b_170_, v_i_171_);
v___x_178_ = 128;
v___x_179_ = lean_uint8_land(v___x_177_, v___x_178_);
v___x_180_ = 0;
v___x_181_ = lean_uint8_dec_eq(v___x_179_, v___x_180_);
if (v___x_181_ == 0)
{
uint8_t v___x_182_; uint8_t v___x_183_; uint8_t v___x_184_; uint8_t v___x_185_; 
v___x_182_ = 224;
v___x_183_ = lean_uint8_land(v___x_177_, v___x_182_);
v___x_184_ = 192;
v___x_185_ = lean_uint8_dec_eq(v___x_183_, v___x_184_);
if (v___x_185_ == 0)
{
uint8_t v___x_186_; uint8_t v___x_187_; uint8_t v___x_188_; 
v___x_186_ = 240;
v___x_187_ = lean_uint8_land(v___x_177_, v___x_186_);
v___x_188_ = lean_uint8_dec_eq(v___x_187_, v___x_182_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; 
v___x_189_ = lean_unsigned_to_nat(4u);
v___y_173_ = v___x_189_;
goto v___jp_172_;
}
else
{
lean_object* v___x_190_; 
v___x_190_ = lean_unsigned_to_nat(3u);
v___y_173_ = v___x_190_;
goto v___jp_172_;
}
}
else
{
lean_object* v___x_191_; 
v___x_191_ = lean_unsigned_to_nat(2u);
v___y_173_ = v___x_191_;
goto v___jp_172_;
}
}
else
{
lean_object* v___x_192_; 
v___x_192_ = lean_unsigned_to_nat(1u);
v___y_173_ = v___x_192_;
goto v___jp_172_;
}
}
v___jp_193_:
{
if (v___y_194_ == 0)
{
lean_dec(v_i_171_);
return v___y_194_;
}
else
{
goto v___jp_176_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___redArg___boxed(lean_object* v_b_302_, lean_object* v_i_303_){
_start:
{
uint8_t v_res_304_; lean_object* v_r_305_; 
v_res_304_ = l_ByteArray_validateUTF8_go___redArg(v_b_302_, v_i_303_);
lean_dec_ref(v_b_302_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8_go(lean_object* v_b_306_, lean_object* v_i_307_, lean_object* v_hi_308_){
_start:
{
uint8_t v___x_309_; 
v___x_309_ = l_ByteArray_validateUTF8_go___redArg(v_b_306_, v_i_307_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___boxed(lean_object* v_b_310_, lean_object* v_i_311_, lean_object* v_hi_312_){
_start:
{
uint8_t v_res_313_; lean_object* v_r_314_; 
v_res_313_ = l_ByteArray_validateUTF8_go(v_b_310_, v_i_311_, v_hi_312_);
lean_dec_ref(v_b_310_);
v_r_314_ = lean_box(v_res_313_);
return v_r_314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(uint8_t v_x_315_, lean_object* v_h__1_316_, lean_object* v_h__2_317_){
_start:
{
if (v_x_315_ == 0)
{
lean_object* v___x_318_; 
lean_dec(v_h__2_317_);
v___x_318_ = lean_apply_1(v_h__1_316_, lean_box(0));
return v___x_318_;
}
else
{
lean_object* v___x_319_; 
lean_dec(v_h__1_316_);
v___x_319_ = lean_apply_1(v_h__2_317_, lean_box(0));
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg___boxed(lean_object* v_x_320_, lean_object* v_h__1_321_, lean_object* v_h__2_322_){
_start:
{
uint8_t v_x_26__boxed_323_; lean_object* v_res_324_; 
v_x_26__boxed_323_ = lean_unbox(v_x_320_);
v_res_324_ = l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(v_x_26__boxed_323_, v_h__1_321_, v_h__2_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(lean_object* v_motive_325_, uint8_t v_x_326_, lean_object* v_h__1_327_, lean_object* v_h__2_328_){
_start:
{
if (v_x_326_ == 0)
{
lean_object* v___x_329_; 
lean_dec(v_h__2_328_);
v___x_329_ = lean_apply_1(v_h__1_327_, lean_box(0));
return v___x_329_;
}
else
{
lean_object* v___x_330_; 
lean_dec(v_h__1_327_);
v___x_330_ = lean_apply_1(v_h__2_328_, lean_box(0));
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___boxed(lean_object* v_motive_331_, lean_object* v_x_332_, lean_object* v_h__1_333_, lean_object* v_h__2_334_){
_start:
{
uint8_t v_x_33__boxed_335_; lean_object* v_res_336_; 
v_x_33__boxed_335_ = lean_unbox(v_x_332_);
v_res_336_ = l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(v_motive_331_, v_x_33__boxed_335_, v_h__1_333_, v_h__2_334_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8___boxed(lean_object* v_b_338_){
_start:
{
uint8_t v_res_339_; lean_object* v_r_340_; 
v_res_339_ = lean_string_validate_utf8(v_b_338_);
lean_dec_ref(v_b_338_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT uint8_t l_instDecidableIsValidUTF8(lean_object* v_b_341_){
_start:
{
uint8_t v___x_342_; 
v___x_342_ = lean_string_validate_utf8(v_b_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_instDecidableIsValidUTF8___boxed(lean_object* v_b_343_){
_start:
{
uint8_t v_res_344_; lean_object* v_r_345_; 
v_res_344_ = l_instDecidableIsValidUTF8(v_b_343_);
lean_dec_ref(v_b_343_);
v_r_345_ = lean_box(v_res_344_);
return v_r_345_;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_x3f(lean_object* v_a_346_){
_start:
{
uint8_t v___x_347_; 
v___x_347_ = lean_string_validate_utf8(v_a_346_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; 
lean_dec_ref(v_a_346_);
v___x_348_ = lean_box(0);
return v___x_348_;
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_string_from_utf8_unchecked(v_a_346_);
v___x_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
}
static lean_object* _init_l_String_fromUTF8_x21___closed__4(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_355_ = ((lean_object*)(l_String_fromUTF8_x21___closed__3));
v___x_356_ = lean_unsigned_to_nat(46u);
v___x_357_ = lean_unsigned_to_nat(193u);
v___x_358_ = ((lean_object*)(l_String_fromUTF8_x21___closed__2));
v___x_359_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_360_ = l_mkPanicMessageWithDecl(v___x_359_, v___x_358_, v___x_357_, v___x_356_, v___x_355_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_x21(lean_object* v_a_361_){
_start:
{
uint8_t v___x_362_; 
v___x_362_ = lean_string_validate_utf8(v_a_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec_ref(v_a_361_);
v___x_363_ = ((lean_object*)(l_String_fromUTF8_x21___closed__0));
v___x_364_ = lean_obj_once(&l_String_fromUTF8_x21___closed__4, &l_String_fromUTF8_x21___closed__4_once, _init_l_String_fromUTF8_x21___closed__4);
v___x_365_ = l_panic___redArg(v___x_363_, v___x_364_);
return v___x_365_;
}
else
{
lean_object* v___x_366_; 
v___x_366_ = lean_string_from_utf8_unchecked(v_a_361_);
return v___x_366_;
}
}
}
LEAN_EXPORT lean_object* l_String_Internal_toArray(lean_object* v_b_367_){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v_val_372_; 
v___x_368_ = lean_string_to_utf8(v_b_367_);
v___x_369_ = lean_unsigned_to_nat(0u);
v___x_370_ = ((lean_object*)(l_ByteArray_utf8Decode_x3f___closed__0));
v___x_371_ = l_ByteArray_utf8Decode_x3f_go___redArg(v___x_368_, v___x_369_, v___x_370_);
lean_dec_ref(v___x_368_);
v_val_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_val_372_);
lean_dec(v___x_371_);
return v_val_372_;
}
}
LEAN_EXPORT lean_object* l_String_toList___boxed(lean_object* v_s_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = lean_string_data(v_s_374_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_String_data___boxed(lean_object* v_b_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = lean_string_data(v_b_377_);
return v_res_378_;
}
}
static lean_object* _init_l_String_instLT(void){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = lean_box(0);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_String_decidableLT___boxed(lean_object* v_s_u2081_382_, lean_object* v_s_u2082_383_){
_start:
{
uint8_t v_res_384_; lean_object* v_r_385_; 
v_res_384_ = lean_string_dec_lt(v_s_u2081_382_, v_s_u2082_383_);
lean_dec_ref(v_s_u2082_383_);
lean_dec_ref(v_s_u2081_382_);
v_r_385_ = lean_box(v_res_384_);
return v_r_385_;
}
}
static lean_object* _init_l_String_instLE(void){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = lean_box(0);
return v___x_386_;
}
}
LEAN_EXPORT uint8_t l_String_decLE(lean_object* v_s_u2081_387_, lean_object* v_s_u2082_388_){
_start:
{
uint8_t v___x_389_; 
v___x_389_ = lean_string_dec_lt(v_s_u2082_388_, v_s_u2081_387_);
if (v___x_389_ == 0)
{
uint8_t v___x_390_; 
v___x_390_ = 1;
return v___x_390_;
}
else
{
uint8_t v___x_391_; 
v___x_391_ = 0;
return v___x_391_;
}
}
}
LEAN_EXPORT lean_object* l_String_decLE___boxed(lean_object* v_s_u2081_392_, lean_object* v_s_u2082_393_){
_start:
{
uint8_t v_res_394_; lean_object* v_r_395_; 
v_res_394_ = l_String_decLE(v_s_u2081_392_, v_s_u2082_393_);
lean_dec_ref(v_s_u2082_393_);
lean_dec_ref(v_s_u2081_392_);
v_r_395_ = lean_box(v_res_394_);
return v_r_395_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValid___boxed(lean_object* v_s_398_, lean_object* v_p_399_){
_start:
{
uint8_t v_res_400_; lean_object* v_r_401_; 
v_res_400_ = lean_string_is_valid_pos(v_s_398_, v_p_399_);
lean_dec(v_p_399_);
lean_dec_ref(v_s_398_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsValid(lean_object* v_s_402_, lean_object* v_p_403_){
_start:
{
uint8_t v___x_404_; 
v___x_404_ = lean_string_is_valid_pos(v_s_402_, v_p_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsValid___boxed(lean_object* v_s_405_, lean_object* v_p_406_){
_start:
{
uint8_t v_res_407_; lean_object* v_r_408_; 
v_res_407_ = l_String_instDecidableIsValid(v_s_405_, v_p_406_);
lean_dec(v_p_406_);
lean_dec_ref(v_s_405_);
v_r_408_ = lean_box(v_res_407_);
return v_r_408_;
}
}
LEAN_EXPORT lean_object* l_String_extract___boxed(lean_object* v_s_412_, lean_object* v_b_413_, lean_object* v_e_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = lean_string_utf8_extract_fast(v_s_412_, v_b_413_, v_e_414_);
lean_dec(v_e_414_);
lean_dec(v_b_413_);
lean_dec_ref(v_s_412_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_extract(lean_object* v_s_416_, lean_object* v_b_417_, lean_object* v_e_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = lean_string_utf8_extract_fast(v_s_416_, v_b_417_, v_e_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_extract___boxed(lean_object* v_s_420_, lean_object* v_b_421_, lean_object* v_e_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_String_Pos_extract(v_s_420_, v_b_421_, v_e_422_);
lean_dec(v_e_422_);
lean_dec(v_b_421_);
lean_dec_ref(v_s_420_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_copy(lean_object* v_s_424_){
_start:
{
lean_object* v_str_425_; lean_object* v_startInclusive_426_; lean_object* v_endExclusive_427_; lean_object* v___x_428_; 
v_str_425_ = lean_ctor_get(v_s_424_, 0);
v_startInclusive_426_ = lean_ctor_get(v_s_424_, 1);
v_endExclusive_427_ = lean_ctor_get(v_s_424_, 2);
v___x_428_ = lean_string_utf8_extract_fast(v_str_425_, v_startInclusive_426_, v_endExclusive_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_copy___boxed(lean_object* v_s_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_String_Slice_copy(v_s_429_);
lean_dec_ref(v_s_429_);
return v_res_430_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_isValidForSlice(lean_object* v_s_431_, lean_object* v_p_432_){
_start:
{
lean_object* v_str_433_; lean_object* v_startInclusive_434_; lean_object* v_endExclusive_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v_str_433_ = lean_ctor_get(v_s_431_, 0);
v_startInclusive_434_ = lean_ctor_get(v_s_431_, 1);
v_endExclusive_435_ = lean_ctor_get(v_s_431_, 2);
v___x_436_ = lean_nat_sub(v_endExclusive_435_, v_startInclusive_434_);
v___x_437_ = lean_unsigned_to_nat(1u);
v___x_438_ = lean_nat_add(v_p_432_, v___x_437_);
v___x_439_ = lean_nat_dec_le(v___x_438_, v___x_436_);
lean_dec(v___x_438_);
if (v___x_439_ == 0)
{
uint8_t v_decide_440_; 
v_decide_440_ = lean_nat_dec_eq(v_p_432_, v___x_436_);
lean_dec(v___x_436_);
return v_decide_440_;
}
else
{
lean_object* v___x_441_; uint8_t v___x_442_; uint8_t v___x_443_; uint8_t v___x_444_; uint8_t v___x_445_; uint8_t v___x_446_; 
lean_dec(v___x_436_);
v___x_441_ = lean_nat_add(v_startInclusive_434_, v_p_432_);
v___x_442_ = lean_string_get_byte_fast(v_str_433_, v___x_441_);
v___x_443_ = 128;
v___x_444_ = lean_uint8_land(v___x_442_, v___x_443_);
v___x_445_ = 0;
v___x_446_ = lean_uint8_dec_eq(v___x_444_, v___x_445_);
if (v___x_446_ == 0)
{
uint8_t v___x_447_; uint8_t v___x_448_; uint8_t v___x_449_; uint8_t v___x_450_; uint8_t v___x_451_; uint8_t v___x_452_; uint8_t v___x_453_; 
v___x_447_ = 224;
v___x_448_ = lean_uint8_land(v___x_442_, v___x_447_);
v___x_449_ = 192;
v___x_450_ = lean_uint8_dec_eq(v___x_448_, v___x_449_);
v___x_451_ = 240;
v___x_452_ = lean_uint8_land(v___x_442_, v___x_451_);
v___x_453_ = lean_uint8_dec_eq(v___x_452_, v___x_447_);
if (v___x_453_ == 0)
{
if (v___x_450_ == 0)
{
uint8_t v___x_454_; uint8_t v___x_455_; uint8_t v___x_456_; 
v___x_454_ = 248;
v___x_455_ = lean_uint8_land(v___x_442_, v___x_454_);
v___x_456_ = lean_uint8_dec_eq(v___x_455_, v___x_451_);
return v___x_456_;
}
else
{
return v___x_450_;
}
}
else
{
if (v___x_450_ == 0)
{
return v___x_453_;
}
else
{
return v___x_450_;
}
}
}
else
{
return v___x_446_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValidForSlice___boxed(lean_object* v_s_457_, lean_object* v_p_458_){
_start:
{
uint8_t v_res_459_; lean_object* v_r_460_; 
v_res_459_ = l_String_Pos_Raw_isValidForSlice(v_s_457_, v_p_458_);
lean_dec(v_p_458_);
lean_dec_ref(v_s_457_);
v_r_460_ = lean_box(v_res_459_);
return v_r_460_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsValidForSlice(lean_object* v_s_461_, lean_object* v_p_462_){
_start:
{
uint8_t v___x_463_; 
v___x_463_ = l_String_Pos_Raw_isValidForSlice(v_s_461_, v_p_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsValidForSlice___boxed(lean_object* v_s_464_, lean_object* v_p_465_){
_start:
{
uint8_t v_res_466_; lean_object* v_r_467_; 
v_res_466_ = l_String_instDecidableIsValidForSlice(v_s_464_, v_p_465_);
lean_dec(v_p_465_);
lean_dec_ref(v_s_464_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str(lean_object* v_s_468_, lean_object* v_pos_469_){
_start:
{
lean_object* v_startInclusive_470_; lean_object* v___x_471_; 
v_startInclusive_470_ = lean_ctor_get(v_s_468_, 1);
v___x_471_ = lean_nat_add(v_startInclusive_470_, v_pos_469_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str___boxed(lean_object* v_s_472_, lean_object* v_pos_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_String_Slice_Pos_str(v_s_472_, v_pos_473_);
lean_dec(v_pos_473_);
lean_dec_ref(v_s_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg(lean_object* v_s_475_, lean_object* v_pos_476_){
_start:
{
lean_object* v_startInclusive_477_; lean_object* v___x_478_; 
v_startInclusive_477_ = lean_ctor_get(v_s_475_, 1);
v___x_478_ = lean_nat_sub(v_pos_476_, v_startInclusive_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg___boxed(lean_object* v_s_479_, lean_object* v_pos_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_String_Slice_Pos_ofStr___redArg(v_s_479_, v_pos_480_);
lean_dec(v_pos_480_);
lean_dec_ref(v_s_479_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr(lean_object* v_s_482_, lean_object* v_pos_483_, lean_object* v_h_u2081_484_, lean_object* v_h_u2082_485_){
_start:
{
lean_object* v_startInclusive_486_; lean_object* v___x_487_; 
v_startInclusive_486_ = lean_ctor_get(v_s_482_, 1);
v___x_487_ = lean_nat_sub(v_pos_483_, v_startInclusive_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___boxed(lean_object* v_s_488_, lean_object* v_pos_489_, lean_object* v_h_u2081_490_, lean_object* v_h_u2082_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_String_Slice_Pos_ofStr(v_s_488_, v_pos_489_, v_h_u2081_490_, v_h_u2082_491_);
lean_dec(v_pos_489_);
lean_dec_ref(v_s_488_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom(lean_object* v_s_493_, lean_object* v_pos_494_){
_start:
{
lean_object* v_str_495_; lean_object* v_startInclusive_496_; lean_object* v_endExclusive_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_505_; 
v_str_495_ = lean_ctor_get(v_s_493_, 0);
v_startInclusive_496_ = lean_ctor_get(v_s_493_, 1);
v_endExclusive_497_ = lean_ctor_get(v_s_493_, 2);
v_isSharedCheck_505_ = !lean_is_exclusive(v_s_493_);
if (v_isSharedCheck_505_ == 0)
{
v___x_499_ = v_s_493_;
v_isShared_500_ = v_isSharedCheck_505_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_endExclusive_497_);
lean_inc(v_startInclusive_496_);
lean_inc(v_str_495_);
lean_dec(v_s_493_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_505_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_501_ = lean_nat_add(v_startInclusive_496_, v_pos_494_);
lean_dec(v_startInclusive_496_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 1, v___x_501_);
v___x_503_ = v___x_499_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_str_495_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_504_, 2, v_endExclusive_497_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom___boxed(lean_object* v_s_506_, lean_object* v_pos_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_String_Slice_sliceFrom(v_s_506_, v_pos_507_);
lean_dec(v_pos_507_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStart(lean_object* v_s_509_, lean_object* v_pos_510_){
_start:
{
lean_object* v_str_511_; lean_object* v_startInclusive_512_; lean_object* v_endExclusive_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_521_; 
v_str_511_ = lean_ctor_get(v_s_509_, 0);
v_startInclusive_512_ = lean_ctor_get(v_s_509_, 1);
v_endExclusive_513_ = lean_ctor_get(v_s_509_, 2);
v_isSharedCheck_521_ = !lean_is_exclusive(v_s_509_);
if (v_isSharedCheck_521_ == 0)
{
v___x_515_ = v_s_509_;
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_endExclusive_513_);
lean_inc(v_startInclusive_512_);
lean_inc(v_str_511_);
lean_dec(v_s_509_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_517_ = lean_nat_add(v_startInclusive_512_, v_pos_510_);
lean_dec(v_startInclusive_512_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 1, v___x_517_);
v___x_519_ = v___x_515_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_str_511_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_520_, 2, v_endExclusive_513_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStart___boxed(lean_object* v_s_522_, lean_object* v_pos_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_String_Slice_replaceStart(v_s_522_, v_pos_523_);
lean_dec(v_pos_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceTo(lean_object* v_s_525_, lean_object* v_pos_526_){
_start:
{
lean_object* v_str_527_; lean_object* v_startInclusive_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_536_; 
v_str_527_ = lean_ctor_get(v_s_525_, 0);
v_startInclusive_528_ = lean_ctor_get(v_s_525_, 1);
v_isSharedCheck_536_ = !lean_is_exclusive(v_s_525_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; 
v_unused_537_ = lean_ctor_get(v_s_525_, 2);
lean_dec(v_unused_537_);
v___x_530_ = v_s_525_;
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_startInclusive_528_);
lean_inc(v_str_527_);
lean_dec(v_s_525_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_532_ = lean_nat_add(v_startInclusive_528_, v_pos_526_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 2, v___x_532_);
v___x_534_ = v___x_530_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_str_527_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_startInclusive_528_);
lean_ctor_set(v_reuseFailAlloc_535_, 2, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceTo___boxed(lean_object* v_s_538_, lean_object* v_pos_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_String_Slice_sliceTo(v_s_538_, v_pos_539_);
lean_dec(v_pos_539_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd(lean_object* v_s_541_, lean_object* v_pos_542_){
_start:
{
lean_object* v_str_543_; lean_object* v_startInclusive_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_552_; 
v_str_543_ = lean_ctor_get(v_s_541_, 0);
v_startInclusive_544_ = lean_ctor_get(v_s_541_, 1);
v_isSharedCheck_552_ = !lean_is_exclusive(v_s_541_);
if (v_isSharedCheck_552_ == 0)
{
lean_object* v_unused_553_; 
v_unused_553_ = lean_ctor_get(v_s_541_, 2);
lean_dec(v_unused_553_);
v___x_546_ = v_s_541_;
v_isShared_547_ = v_isSharedCheck_552_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_startInclusive_544_);
lean_inc(v_str_543_);
lean_dec(v_s_541_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_552_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_548_ = lean_nat_add(v_startInclusive_544_, v_pos_542_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 2, v___x_548_);
v___x_550_ = v___x_546_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_str_543_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_startInclusive_544_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd___boxed(lean_object* v_s_554_, lean_object* v_pos_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_String_Slice_replaceEnd(v_s_554_, v_pos_555_);
lean_dec(v_pos_555_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg(lean_object* v_s_557_, lean_object* v_newStart_558_, lean_object* v_newEnd_559_){
_start:
{
lean_object* v_str_560_; lean_object* v_startInclusive_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_570_; 
v_str_560_ = lean_ctor_get(v_s_557_, 0);
v_startInclusive_561_ = lean_ctor_get(v_s_557_, 1);
v_isSharedCheck_570_ = !lean_is_exclusive(v_s_557_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; 
v_unused_571_ = lean_ctor_get(v_s_557_, 2);
lean_dec(v_unused_571_);
v___x_563_ = v_s_557_;
v_isShared_564_ = v_isSharedCheck_570_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_startInclusive_561_);
lean_inc(v_str_560_);
lean_dec(v_s_557_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_570_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_565_ = lean_nat_add(v_startInclusive_561_, v_newStart_558_);
v___x_566_ = lean_nat_add(v_startInclusive_561_, v_newEnd_559_);
lean_dec(v_startInclusive_561_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 2, v___x_566_);
lean_ctor_set(v___x_563_, 1, v___x_565_);
v___x_568_ = v___x_563_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_str_560_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v___x_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg___boxed(lean_object* v_s_572_, lean_object* v_newStart_573_, lean_object* v_newEnd_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_String_Slice_slice___redArg(v_s_572_, v_newStart_573_, v_newEnd_574_);
lean_dec(v_newEnd_574_);
lean_dec(v_newStart_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice(lean_object* v_s_576_, lean_object* v_newStart_577_, lean_object* v_newEnd_578_, lean_object* v_h_579_){
_start:
{
lean_object* v_str_580_; lean_object* v_startInclusive_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_590_; 
v_str_580_ = lean_ctor_get(v_s_576_, 0);
v_startInclusive_581_ = lean_ctor_get(v_s_576_, 1);
v_isSharedCheck_590_ = !lean_is_exclusive(v_s_576_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; 
v_unused_591_ = lean_ctor_get(v_s_576_, 2);
lean_dec(v_unused_591_);
v___x_583_ = v_s_576_;
v_isShared_584_ = v_isSharedCheck_590_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_startInclusive_581_);
lean_inc(v_str_580_);
lean_dec(v_s_576_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_590_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_585_ = lean_nat_add(v_startInclusive_581_, v_newStart_577_);
v___x_586_ = lean_nat_add(v_startInclusive_581_, v_newEnd_578_);
lean_dec(v_startInclusive_581_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 2, v___x_586_);
lean_ctor_set(v___x_583_, 1, v___x_585_);
v___x_588_ = v___x_583_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_str_580_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___boxed(lean_object* v_s_592_, lean_object* v_newStart_593_, lean_object* v_newEnd_594_, lean_object* v_h_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_String_Slice_slice(v_s_592_, v_newStart_593_, v_newEnd_594_, v_h_595_);
lean_dec(v_newEnd_594_);
lean_dec(v_newStart_593_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg(lean_object* v_s_597_, lean_object* v_newStart_598_, lean_object* v_newEnd_599_){
_start:
{
lean_object* v_str_600_; lean_object* v_startInclusive_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_610_; 
v_str_600_ = lean_ctor_get(v_s_597_, 0);
v_startInclusive_601_ = lean_ctor_get(v_s_597_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v_s_597_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; 
v_unused_611_ = lean_ctor_get(v_s_597_, 2);
lean_dec(v_unused_611_);
v___x_603_ = v_s_597_;
v_isShared_604_ = v_isSharedCheck_610_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_startInclusive_601_);
lean_inc(v_str_600_);
lean_dec(v_s_597_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_610_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_605_ = lean_nat_add(v_startInclusive_601_, v_newStart_598_);
v___x_606_ = lean_nat_add(v_startInclusive_601_, v_newEnd_599_);
lean_dec(v_startInclusive_601_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 2, v___x_606_);
lean_ctor_set(v___x_603_, 1, v___x_605_);
v___x_608_ = v___x_603_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_str_600_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg___boxed(lean_object* v_s_612_, lean_object* v_newStart_613_, lean_object* v_newEnd_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_String_Slice_replaceStartEnd___redArg(v_s_612_, v_newStart_613_, v_newEnd_614_);
lean_dec(v_newEnd_614_);
lean_dec(v_newStart_613_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd(lean_object* v_s_616_, lean_object* v_newStart_617_, lean_object* v_newEnd_618_, lean_object* v_h_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_String_Slice_replaceStartEnd___redArg(v_s_616_, v_newStart_617_, v_newEnd_618_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___boxed(lean_object* v_s_621_, lean_object* v_newStart_622_, lean_object* v_newEnd_623_, lean_object* v_h_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_String_Slice_replaceStartEnd(v_s_621_, v_newStart_622_, v_newEnd_623_, v_h_624_);
lean_dec(v_newEnd_623_);
lean_dec(v_newStart_622_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f(lean_object* v_s_626_, lean_object* v_newStart_627_, lean_object* v_newEnd_628_){
_start:
{
uint8_t v___x_629_; 
v___x_629_ = lean_nat_dec_le(v_newStart_627_, v_newEnd_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; 
lean_dec_ref(v_s_626_);
v___x_630_ = lean_box(0);
return v___x_630_;
}
else
{
lean_object* v_str_631_; lean_object* v_startInclusive_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_642_; 
v_str_631_ = lean_ctor_get(v_s_626_, 0);
v_startInclusive_632_ = lean_ctor_get(v_s_626_, 1);
v_isSharedCheck_642_ = !lean_is_exclusive(v_s_626_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; 
v_unused_643_ = lean_ctor_get(v_s_626_, 2);
lean_dec(v_unused_643_);
v___x_634_ = v_s_626_;
v_isShared_635_ = v_isSharedCheck_642_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_startInclusive_632_);
lean_inc(v_str_631_);
lean_dec(v_s_626_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_642_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_636_ = lean_nat_add(v_startInclusive_632_, v_newStart_627_);
v___x_637_ = lean_nat_add(v_startInclusive_632_, v_newEnd_628_);
lean_dec(v_startInclusive_632_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 2, v___x_637_);
lean_ctor_set(v___x_634_, 1, v___x_636_);
v___x_639_ = v___x_634_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_str_631_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_641_, 2, v___x_637_);
v___x_639_ = v_reuseFailAlloc_641_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_640_; 
v___x_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
return v___x_640_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f___boxed(lean_object* v_s_644_, lean_object* v_newStart_645_, lean_object* v_newEnd_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_String_Slice_slice_x3f(v_s_644_, v_newStart_645_, v_newEnd_646_);
lean_dec(v_newEnd_646_);
lean_dec(v_newStart_645_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_slice_x21_spec__0(lean_object* v_msg_648_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = l_String_instInhabitedSlice;
v___x_650_ = lean_panic_fn_borrowed(v___x_649_, v_msg_648_);
return v___x_650_;
}
}
static lean_object* _init_l_String_Slice_slice_x21___closed__2(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_653_ = ((lean_object*)(l_String_Slice_slice_x21___closed__1));
v___x_654_ = lean_unsigned_to_nat(4u);
v___x_655_ = lean_unsigned_to_nat(1096u);
v___x_656_ = ((lean_object*)(l_String_Slice_slice_x21___closed__0));
v___x_657_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_658_ = l_mkPanicMessageWithDecl(v___x_657_, v___x_656_, v___x_655_, v___x_654_, v___x_653_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x21(lean_object* v_s_659_, lean_object* v_newStart_660_, lean_object* v_newEnd_661_){
_start:
{
uint8_t v___x_662_; 
v___x_662_ = lean_nat_dec_le(v_newStart_660_, v_newEnd_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; lean_object* v___x_664_; 
lean_dec_ref(v_s_659_);
v___x_663_ = lean_obj_once(&l_String_Slice_slice_x21___closed__2, &l_String_Slice_slice_x21___closed__2_once, _init_l_String_Slice_slice_x21___closed__2);
v___x_664_ = l_panic___at___00String_Slice_slice_x21_spec__0(v___x_663_);
return v___x_664_;
}
else
{
lean_object* v_str_665_; lean_object* v_startInclusive_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_675_; 
v_str_665_ = lean_ctor_get(v_s_659_, 0);
v_startInclusive_666_ = lean_ctor_get(v_s_659_, 1);
v_isSharedCheck_675_ = !lean_is_exclusive(v_s_659_);
if (v_isSharedCheck_675_ == 0)
{
lean_object* v_unused_676_; 
v_unused_676_ = lean_ctor_get(v_s_659_, 2);
lean_dec(v_unused_676_);
v___x_668_ = v_s_659_;
v_isShared_669_ = v_isSharedCheck_675_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_startInclusive_666_);
lean_inc(v_str_665_);
lean_dec(v_s_659_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_675_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_670_ = lean_nat_add(v_startInclusive_666_, v_newStart_660_);
v___x_671_ = lean_nat_add(v_startInclusive_666_, v_newEnd_661_);
lean_dec(v_startInclusive_666_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 2, v___x_671_);
lean_ctor_set(v___x_668_, 1, v___x_670_);
v___x_673_ = v___x_668_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_str_665_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x21___boxed(lean_object* v_s_677_, lean_object* v_newStart_678_, lean_object* v_newEnd_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_String_Slice_slice_x21(v_s_677_, v_newStart_678_, v_newEnd_679_);
lean_dec(v_newEnd_679_);
lean_dec(v_newStart_678_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21(lean_object* v_s_681_, lean_object* v_newStart_682_, lean_object* v_newEnd_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_String_Slice_slice_x21(v_s_681_, v_newStart_682_, v_newEnd_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21___boxed(lean_object* v_s_685_, lean_object* v_newStart_686_, lean_object* v_newEnd_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_String_Slice_replaceStartEnd_x21(v_s_685_, v_newStart_686_, v_newEnd_687_);
lean_dec(v_newEnd_687_);
lean_dec(v_newStart_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_String_decodeChar___boxed(lean_object* v_s_692_, lean_object* v_byteIdx_693_, lean_object* v_h_694_){
_start:
{
uint32_t v_res_695_; lean_object* v_r_696_; 
v_res_695_ = lean_string_utf8_get_fast(v_s_692_, v_byteIdx_693_);
lean_dec(v_byteIdx_693_);
lean_dec_ref(v_s_692_);
v_r_696_ = lean_box_uint32(v_res_695_);
return v_r_696_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get___redArg(lean_object* v_s_697_, lean_object* v_pos_698_){
_start:
{
lean_object* v_str_699_; lean_object* v_startInclusive_700_; lean_object* v___x_701_; uint32_t v___x_702_; 
v_str_699_ = lean_ctor_get(v_s_697_, 0);
v_startInclusive_700_ = lean_ctor_get(v_s_697_, 1);
v___x_701_ = lean_nat_add(v_startInclusive_700_, v_pos_698_);
v___x_702_ = lean_string_utf8_get_fast(v_str_699_, v___x_701_);
lean_dec(v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___redArg___boxed(lean_object* v_s_703_, lean_object* v_pos_704_){
_start:
{
uint32_t v_res_705_; lean_object* v_r_706_; 
v_res_705_ = l_String_Slice_Pos_get___redArg(v_s_703_, v_pos_704_);
lean_dec(v_pos_704_);
lean_dec_ref(v_s_703_);
v_r_706_ = lean_box_uint32(v_res_705_);
return v_r_706_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get(lean_object* v_s_707_, lean_object* v_pos_708_, lean_object* v_h_709_){
_start:
{
lean_object* v_str_710_; lean_object* v_startInclusive_711_; lean_object* v___x_712_; uint32_t v___x_713_; 
v_str_710_ = lean_ctor_get(v_s_707_, 0);
v_startInclusive_711_ = lean_ctor_get(v_s_707_, 1);
v___x_712_ = lean_nat_add(v_startInclusive_711_, v_pos_708_);
v___x_713_ = lean_string_utf8_get_fast(v_str_710_, v___x_712_);
lean_dec(v___x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___boxed(lean_object* v_s_714_, lean_object* v_pos_715_, lean_object* v_h_716_){
_start:
{
uint32_t v_res_717_; lean_object* v_r_718_; 
v_res_717_ = l_String_Slice_Pos_get(v_s_714_, v_pos_715_, v_h_716_);
lean_dec(v_pos_715_);
lean_dec_ref(v_s_714_);
v_r_718_ = lean_box_uint32(v_res_717_);
return v_r_718_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f(lean_object* v_s_719_, lean_object* v_pos_720_){
_start:
{
lean_object* v_str_721_; lean_object* v_startInclusive_722_; lean_object* v_endExclusive_723_; lean_object* v___x_724_; uint8_t v_decide_725_; 
v_str_721_ = lean_ctor_get(v_s_719_, 0);
v_startInclusive_722_ = lean_ctor_get(v_s_719_, 1);
v_endExclusive_723_ = lean_ctor_get(v_s_719_, 2);
v___x_724_ = lean_nat_sub(v_endExclusive_723_, v_startInclusive_722_);
v_decide_725_ = lean_nat_dec_eq(v_pos_720_, v___x_724_);
lean_dec(v___x_724_);
if (v_decide_725_ == 0)
{
lean_object* v___x_726_; uint32_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_726_ = lean_nat_add(v_startInclusive_722_, v_pos_720_);
v___x_727_ = lean_string_utf8_get_fast(v_str_721_, v___x_726_);
lean_dec(v___x_726_);
v___x_728_ = lean_box_uint32(v___x_727_);
v___x_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
else
{
lean_object* v___x_730_; 
v___x_730_ = lean_box(0);
return v___x_730_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f___boxed(lean_object* v_s_731_, lean_object* v_pos_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_String_Slice_Pos_get_x3f(v_s_731_, v_pos_732_);
lean_dec(v_pos_732_);
lean_dec_ref(v_s_731_);
return v_res_733_;
}
}
static lean_object* _init_l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1(void){
_start:
{
uint32_t v___x_734_; lean_object* v___x_735_; 
v___x_734_ = 65;
v___x_735_ = lean_box_uint32(v___x_734_);
return v___x_735_;
}
}
LEAN_EXPORT uint32_t l_panic___at___00String_Slice_Pos_get_x21_spec__0(lean_object* v_msg_736_){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; uint32_t v___x_739_; 
v___x_737_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1;
v___x_738_ = lean_panic_fn_borrowed(v___x_737_, v_msg_736_);
v___x_739_ = lean_unbox_uint32(v___x_738_);
lean_dec(v___x_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed(lean_object* v_msg_740_){
_start:
{
uint32_t v_res_741_; lean_object* v_r_742_; 
v_res_741_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v_msg_740_);
v_r_742_ = lean_box_uint32(v_res_741_);
return v_r_742_;
}
}
static lean_object* _init_l_String_Slice_Pos_get_x21___closed__2(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_745_ = ((lean_object*)(l_String_Slice_Pos_get_x21___closed__1));
v___x_746_ = lean_unsigned_to_nat(29u);
v___x_747_ = lean_unsigned_to_nat(1181u);
v___x_748_ = ((lean_object*)(l_String_Slice_Pos_get_x21___closed__0));
v___x_749_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_750_ = l_mkPanicMessageWithDecl(v___x_749_, v___x_748_, v___x_747_, v___x_746_, v___x_745_);
return v___x_750_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get_x21(lean_object* v_s_751_, lean_object* v_pos_752_){
_start:
{
lean_object* v_str_753_; lean_object* v_startInclusive_754_; lean_object* v_endExclusive_755_; lean_object* v___x_756_; uint8_t v_decide_757_; 
v_str_753_ = lean_ctor_get(v_s_751_, 0);
v_startInclusive_754_ = lean_ctor_get(v_s_751_, 1);
v_endExclusive_755_ = lean_ctor_get(v_s_751_, 2);
v___x_756_ = lean_nat_sub(v_endExclusive_755_, v_startInclusive_754_);
v_decide_757_ = lean_nat_dec_eq(v_pos_752_, v___x_756_);
lean_dec(v___x_756_);
if (v_decide_757_ == 0)
{
lean_object* v___x_758_; uint32_t v___x_759_; 
v___x_758_ = lean_nat_add(v_startInclusive_754_, v_pos_752_);
v___x_759_ = lean_string_utf8_get_fast(v_str_753_, v___x_758_);
lean_dec(v___x_758_);
return v___x_759_;
}
else
{
lean_object* v___x_760_; uint32_t v___x_761_; 
v___x_760_ = lean_obj_once(&l_String_Slice_Pos_get_x21___closed__2, &l_String_Slice_Pos_get_x21___closed__2_once, _init_l_String_Slice_Pos_get_x21___closed__2);
v___x_761_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v___x_760_);
return v___x_761_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x21___boxed(lean_object* v_s_762_, lean_object* v_pos_763_){
_start:
{
uint32_t v_res_764_; lean_object* v_r_765_; 
v_res_764_ = l_String_Slice_Pos_get_x21(v_s_762_, v_pos_763_);
lean_dec(v_pos_763_);
lean_dec_ref(v_s_762_);
v_r_765_ = lean_box_uint32(v_res_764_);
return v_r_765_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg(lean_object* v_pos_766_){
_start:
{
lean_inc(v_pos_766_);
return v_pos_766_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg___boxed(lean_object* v_pos_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_String_Pos_toSlice___redArg(v_pos_767_);
lean_dec(v_pos_767_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice(lean_object* v_s_769_, lean_object* v_pos_770_){
_start:
{
lean_inc(v_pos_770_);
return v_pos_770_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___boxed(lean_object* v_s_771_, lean_object* v_pos_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_String_Pos_toSlice(v_s_771_, v_pos_772_);
lean_dec(v_pos_772_);
lean_dec_ref(v_s_771_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg(lean_object* v_pos_774_){
_start:
{
lean_inc(v_pos_774_);
return v_pos_774_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg___boxed(lean_object* v_pos_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_String_Pos_ofToSlice___redArg(v_pos_775_);
lean_dec(v_pos_775_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice(lean_object* v_s_777_, lean_object* v_pos_778_){
_start:
{
lean_inc(v_pos_778_);
return v_pos_778_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___boxed(lean_object* v_s_779_, lean_object* v_pos_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_String_Pos_ofToSlice(v_s_779_, v_pos_780_);
lean_dec(v_pos_780_);
lean_dec_ref(v_s_779_);
return v_res_781_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get___redArg(lean_object* v_s_782_, lean_object* v_pos_783_){
_start:
{
uint32_t v___x_784_; 
v___x_784_ = lean_string_utf8_get_fast(v_s_782_, v_pos_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get___redArg___boxed(lean_object* v_s_785_, lean_object* v_pos_786_){
_start:
{
uint32_t v_res_787_; lean_object* v_r_788_; 
v_res_787_ = l_String_Pos_get___redArg(v_s_785_, v_pos_786_);
lean_dec(v_pos_786_);
lean_dec_ref(v_s_785_);
v_r_788_ = lean_box_uint32(v_res_787_);
return v_r_788_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get(lean_object* v_s_789_, lean_object* v_pos_790_, lean_object* v_h_791_){
_start:
{
uint32_t v___x_792_; 
v___x_792_ = lean_string_utf8_get_fast(v_s_789_, v_pos_790_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get___boxed(lean_object* v_s_793_, lean_object* v_pos_794_, lean_object* v_h_795_){
_start:
{
uint32_t v_res_796_; lean_object* v_r_797_; 
v_res_796_ = l_String_Pos_get(v_s_793_, v_pos_794_, v_h_795_);
lean_dec(v_pos_794_);
lean_dec_ref(v_s_793_);
v_r_797_ = lean_box_uint32(v_res_796_);
return v_r_797_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x3f(lean_object* v_s_798_, lean_object* v_pos_799_){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = lean_string_utf8_byte_size(v_s_798_);
v___x_802_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_802_, 0, v_s_798_);
lean_ctor_set(v___x_802_, 1, v___x_800_);
lean_ctor_set(v___x_802_, 2, v___x_801_);
v___x_803_ = l_String_Slice_Pos_get_x3f(v___x_802_, v_pos_799_);
lean_dec_ref_known(v___x_802_, 3);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x3f___boxed(lean_object* v_s_804_, lean_object* v_pos_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_String_Pos_get_x3f(v_s_804_, v_pos_805_);
lean_dec(v_pos_805_);
return v_res_806_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get_x21(lean_object* v_s_807_, lean_object* v_pos_808_){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; uint32_t v___x_812_; 
v___x_809_ = lean_unsigned_to_nat(0u);
v___x_810_ = lean_string_utf8_byte_size(v_s_807_);
v___x_811_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_811_, 0, v_s_807_);
lean_ctor_set(v___x_811_, 1, v___x_809_);
lean_ctor_set(v___x_811_, 2, v___x_810_);
v___x_812_ = l_String_Slice_Pos_get_x21(v___x_811_, v_pos_808_);
lean_dec_ref_known(v___x_811_, 3);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x21___boxed(lean_object* v_s_813_, lean_object* v_pos_814_){
_start:
{
uint32_t v_res_815_; lean_object* v_r_816_; 
v_res_815_ = l_String_Pos_get_x21(v_s_813_, v_pos_814_);
lean_dec(v_pos_814_);
v_r_816_ = lean_box_uint32(v_res_815_);
return v_r_816_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_byte___redArg(lean_object* v_s_817_, lean_object* v_pos_818_){
_start:
{
uint8_t v___x_819_; 
v___x_819_ = lean_string_get_byte_fast(v_s_817_, v_pos_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_byte___redArg___boxed(lean_object* v_s_820_, lean_object* v_pos_821_){
_start:
{
uint8_t v_res_822_; lean_object* v_r_823_; 
v_res_822_ = l_String_Pos_byte___redArg(v_s_820_, v_pos_821_);
lean_dec_ref(v_s_820_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_byte(lean_object* v_s_824_, lean_object* v_pos_825_, lean_object* v_h_826_){
_start:
{
uint8_t v___x_827_; 
v___x_827_ = lean_string_get_byte_fast(v_s_824_, v_pos_825_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_byte___boxed(lean_object* v_s_828_, lean_object* v_pos_829_, lean_object* v_h_830_){
_start:
{
uint8_t v_res_831_; lean_object* v_r_832_; 
v_res_831_ = l_String_Pos_byte(v_s_828_, v_pos_829_, v_h_830_);
lean_dec_ref(v_s_828_);
v_r_832_ = lean_box(v_res_831_);
return v_r_832_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg(lean_object* v_pos_833_){
_start:
{
lean_inc(v_pos_833_);
return v_pos_833_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg___boxed(lean_object* v_pos_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_String_Pos_ofCopy___redArg(v_pos_834_);
lean_dec(v_pos_834_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy(lean_object* v_s_836_, lean_object* v_pos_837_){
_start:
{
lean_inc(v_pos_837_);
return v_pos_837_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___boxed(lean_object* v_s_838_, lean_object* v_pos_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_String_Pos_ofCopy(v_s_838_, v_pos_839_);
lean_dec(v_pos_839_);
lean_dec_ref(v_s_838_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg(lean_object* v_pos_841_){
_start:
{
lean_inc(v_pos_841_);
return v_pos_841_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg___boxed(lean_object* v_pos_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_String_Slice_Pos_copy___redArg(v_pos_842_);
lean_dec(v_pos_842_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy(lean_object* v_s_844_, lean_object* v_pos_845_){
_start:
{
lean_inc(v_pos_845_);
return v_pos_845_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___boxed(lean_object* v_s_846_, lean_object* v_pos_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_String_Slice_Pos_copy(v_s_846_, v_pos_847_);
lean_dec(v_pos_847_);
lean_dec_ref(v_s_846_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg(lean_object* v_pos_849_){
_start:
{
lean_inc(v_pos_849_);
return v_pos_849_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg___boxed(lean_object* v_pos_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_String_Slice_Pos_toCopy___redArg(v_pos_850_);
lean_dec(v_pos_850_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy(lean_object* v_s_852_, lean_object* v_pos_853_){
_start:
{
lean_inc(v_pos_853_);
return v_pos_853_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___boxed(lean_object* v_s_854_, lean_object* v_pos_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_String_Slice_Pos_toCopy(v_s_854_, v_pos_855_);
lean_dec(v_pos_855_);
lean_dec_ref(v_s_854_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg(lean_object* v_p_u2080_857_, lean_object* v_pos_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = lean_nat_add(v_p_u2080_857_, v_pos_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg___boxed(lean_object* v_p_u2080_860_, lean_object* v_pos_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_String_Slice_Pos_ofSliceFrom___redArg(v_p_u2080_860_, v_pos_861_);
lean_dec(v_pos_861_);
lean_dec(v_p_u2080_860_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom(lean_object* v_s_863_, lean_object* v_p_u2080_864_, lean_object* v_pos_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = lean_nat_add(v_p_u2080_864_, v_pos_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___boxed(lean_object* v_s_867_, lean_object* v_p_u2080_868_, lean_object* v_pos_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_String_Slice_Pos_ofSliceFrom(v_s_867_, v_p_u2080_868_, v_pos_869_);
lean_dec(v_pos_869_);
lean_dec(v_p_u2080_868_);
lean_dec_ref(v_s_867_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg(lean_object* v_p_u2080_871_, lean_object* v_pos_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = lean_nat_add(v_p_u2080_871_, v_pos_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg___boxed(lean_object* v_p_u2080_874_, lean_object* v_pos_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_String_Slice_Pos_ofReplaceStart___redArg(v_p_u2080_874_, v_pos_875_);
lean_dec(v_pos_875_);
lean_dec(v_p_u2080_874_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart(lean_object* v_s_877_, lean_object* v_p_u2080_878_, lean_object* v_pos_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = lean_nat_add(v_p_u2080_878_, v_pos_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___boxed(lean_object* v_s_881_, lean_object* v_p_u2080_882_, lean_object* v_pos_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_String_Slice_Pos_ofReplaceStart(v_s_881_, v_p_u2080_882_, v_pos_883_);
lean_dec(v_pos_883_);
lean_dec(v_p_u2080_882_);
lean_dec_ref(v_s_881_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg(lean_object* v_p_u2080_885_, lean_object* v_pos_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = lean_nat_sub(v_pos_886_, v_p_u2080_885_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg___boxed(lean_object* v_p_u2080_888_, lean_object* v_pos_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_String_Slice_Pos_sliceFrom___redArg(v_p_u2080_888_, v_pos_889_);
lean_dec(v_pos_889_);
lean_dec(v_p_u2080_888_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom(lean_object* v_s_891_, lean_object* v_p_u2080_892_, lean_object* v_pos_893_, lean_object* v_h_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = lean_nat_sub(v_pos_893_, v_p_u2080_892_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___boxed(lean_object* v_s_896_, lean_object* v_p_u2080_897_, lean_object* v_pos_898_, lean_object* v_h_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_String_Slice_Pos_sliceFrom(v_s_896_, v_p_u2080_897_, v_pos_898_, v_h_899_);
lean_dec(v_pos_898_);
lean_dec(v_p_u2080_897_);
lean_dec_ref(v_s_896_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg(lean_object* v_p_u2080_901_, lean_object* v_pos_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = lean_nat_sub(v_pos_902_, v_p_u2080_901_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg___boxed(lean_object* v_p_u2080_904_, lean_object* v_pos_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_String_Slice_Pos_toReplaceStart___redArg(v_p_u2080_904_, v_pos_905_);
lean_dec(v_pos_905_);
lean_dec(v_p_u2080_904_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart(lean_object* v_s_907_, lean_object* v_p_u2080_908_, lean_object* v_pos_909_, lean_object* v_h_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = lean_nat_sub(v_pos_909_, v_p_u2080_908_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___boxed(lean_object* v_s_912_, lean_object* v_p_u2080_913_, lean_object* v_pos_914_, lean_object* v_h_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_String_Slice_Pos_toReplaceStart(v_s_912_, v_p_u2080_913_, v_pos_914_, v_h_915_);
lean_dec(v_pos_914_);
lean_dec(v_p_u2080_913_);
lean_dec_ref(v_s_912_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg(lean_object* v_pos_917_){
_start:
{
lean_inc(v_pos_917_);
return v_pos_917_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg___boxed(lean_object* v_pos_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_String_Slice_Pos_ofSliceTo___redArg(v_pos_918_);
lean_dec(v_pos_918_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo(lean_object* v_s_920_, lean_object* v_p_u2080_921_, lean_object* v_pos_922_){
_start:
{
lean_inc(v_pos_922_);
return v_pos_922_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___boxed(lean_object* v_s_923_, lean_object* v_p_u2080_924_, lean_object* v_pos_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_String_Slice_Pos_ofSliceTo(v_s_923_, v_p_u2080_924_, v_pos_925_);
lean_dec(v_pos_925_);
lean_dec(v_p_u2080_924_);
lean_dec_ref(v_s_923_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg(lean_object* v_pos_927_){
_start:
{
lean_inc(v_pos_927_);
return v_pos_927_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg___boxed(lean_object* v_pos_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_String_Slice_Pos_ofReplaceEnd___redArg(v_pos_928_);
lean_dec(v_pos_928_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd(lean_object* v_s_930_, lean_object* v_p_u2080_931_, lean_object* v_pos_932_){
_start:
{
lean_inc(v_pos_932_);
return v_pos_932_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___boxed(lean_object* v_s_933_, lean_object* v_p_u2080_934_, lean_object* v_pos_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_String_Slice_Pos_ofReplaceEnd(v_s_933_, v_p_u2080_934_, v_pos_935_);
lean_dec(v_pos_935_);
lean_dec(v_p_u2080_934_);
lean_dec_ref(v_s_933_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg(lean_object* v_pos_937_){
_start:
{
lean_inc(v_pos_937_);
return v_pos_937_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg___boxed(lean_object* v_pos_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_String_Slice_Pos_sliceTo___redArg(v_pos_938_);
lean_dec(v_pos_938_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo(lean_object* v_s_940_, lean_object* v_p_u2080_941_, lean_object* v_pos_942_, lean_object* v_h_943_){
_start:
{
lean_inc(v_pos_942_);
return v_pos_942_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___boxed(lean_object* v_s_944_, lean_object* v_p_u2080_945_, lean_object* v_pos_946_, lean_object* v_h_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_String_Slice_Pos_sliceTo(v_s_944_, v_p_u2080_945_, v_pos_946_, v_h_947_);
lean_dec(v_pos_946_);
lean_dec(v_p_u2080_945_);
lean_dec_ref(v_s_944_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg(lean_object* v_pos_949_){
_start:
{
lean_inc(v_pos_949_);
return v_pos_949_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg___boxed(lean_object* v_pos_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_String_Slice_Pos_toReplaceEnd___redArg(v_pos_950_);
lean_dec(v_pos_950_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd(lean_object* v_s_952_, lean_object* v_p_u2080_953_, lean_object* v_pos_954_, lean_object* v_h_955_){
_start:
{
lean_inc(v_pos_954_);
return v_pos_954_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___boxed(lean_object* v_s_956_, lean_object* v_p_u2080_957_, lean_object* v_pos_958_, lean_object* v_h_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_String_Slice_Pos_toReplaceEnd(v_s_956_, v_p_u2080_957_, v_pos_958_, v_h_959_);
lean_dec(v_pos_958_);
lean_dec(v_p_u2080_957_);
lean_dec_ref(v_s_956_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg(lean_object* v_s_961_, lean_object* v_pos_962_){
_start:
{
lean_object* v_str_963_; lean_object* v_startInclusive_964_; lean_object* v___x_965_; uint8_t v___x_966_; uint8_t v___x_967_; uint8_t v___x_968_; uint8_t v___x_969_; uint8_t v___x_970_; 
v_str_963_ = lean_ctor_get(v_s_961_, 0);
v_startInclusive_964_ = lean_ctor_get(v_s_961_, 1);
v___x_965_ = lean_nat_add(v_startInclusive_964_, v_pos_962_);
v___x_966_ = lean_string_get_byte_fast(v_str_963_, v___x_965_);
v___x_967_ = 128;
v___x_968_ = lean_uint8_land(v___x_966_, v___x_967_);
v___x_969_ = 0;
v___x_970_ = lean_uint8_dec_eq(v___x_968_, v___x_969_);
if (v___x_970_ == 0)
{
uint8_t v___x_971_; uint8_t v___x_972_; uint8_t v___x_973_; uint8_t v___x_974_; 
v___x_971_ = 224;
v___x_972_ = lean_uint8_land(v___x_966_, v___x_971_);
v___x_973_ = 192;
v___x_974_ = lean_uint8_dec_eq(v___x_972_, v___x_973_);
if (v___x_974_ == 0)
{
uint8_t v___x_975_; uint8_t v___x_976_; uint8_t v___x_977_; 
v___x_975_ = 240;
v___x_976_ = lean_uint8_land(v___x_966_, v___x_975_);
v___x_977_ = lean_uint8_dec_eq(v___x_976_, v___x_971_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = lean_unsigned_to_nat(4u);
v___x_979_ = lean_nat_add(v_pos_962_, v___x_978_);
return v___x_979_;
}
else
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = lean_unsigned_to_nat(3u);
v___x_981_ = lean_nat_add(v_pos_962_, v___x_980_);
return v___x_981_;
}
}
else
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_unsigned_to_nat(2u);
v___x_983_ = lean_nat_add(v_pos_962_, v___x_982_);
return v___x_983_;
}
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = lean_unsigned_to_nat(1u);
v___x_985_ = lean_nat_add(v_pos_962_, v___x_984_);
return v___x_985_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg___boxed(lean_object* v_s_986_, lean_object* v_pos_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_String_Slice_Pos_next___redArg(v_s_986_, v_pos_987_);
lean_dec(v_pos_987_);
lean_dec_ref(v_s_986_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next(lean_object* v_s_989_, lean_object* v_pos_990_, lean_object* v_h_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_String_Slice_Pos_next___redArg(v_s_989_, v_pos_990_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___boxed(lean_object* v_s_993_, lean_object* v_pos_994_, lean_object* v_h_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_String_Slice_Pos_next(v_s_993_, v_pos_994_, v_h_995_);
lean_dec(v_pos_994_);
lean_dec_ref(v_s_993_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f(lean_object* v_s_997_, lean_object* v_pos_998_){
_start:
{
lean_object* v_startInclusive_999_; lean_object* v_endExclusive_1000_; lean_object* v___x_1001_; uint8_t v_decide_1002_; 
v_startInclusive_999_ = lean_ctor_get(v_s_997_, 1);
v_endExclusive_1000_ = lean_ctor_get(v_s_997_, 2);
v___x_1001_ = lean_nat_sub(v_endExclusive_1000_, v_startInclusive_999_);
v_decide_1002_ = lean_nat_dec_eq(v_pos_998_, v___x_1001_);
lean_dec(v___x_1001_);
if (v_decide_1002_ == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = l_String_Slice_Pos_next___redArg(v_s_997_, v_pos_998_);
v___x_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
return v___x_1004_;
}
else
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_box(0);
return v___x_1005_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f___boxed(lean_object* v_s_1006_, lean_object* v_pos_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_String_Slice_Pos_next_x3f(v_s_1006_, v_pos_1007_);
lean_dec(v_pos_1007_);
lean_dec_ref(v_s_1006_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(lean_object* v_msg_1009_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_unsigned_to_nat(0u);
v___x_1011_ = lean_panic_fn_borrowed(v___x_1010_, v_msg_1009_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0(lean_object* v_s_1012_, lean_object* v_msg_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v_msg_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___boxed(lean_object* v_s_1015_, lean_object* v_msg_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0(v_s_1015_, v_msg_1016_);
lean_dec_ref(v_s_1015_);
return v_res_1017_;
}
}
static lean_object* _init_l_String_Slice_Pos_next_x21___closed__2(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1020_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__1));
v___x_1021_ = lean_unsigned_to_nat(29u);
v___x_1022_ = lean_unsigned_to_nat(1573u);
v___x_1023_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__0));
v___x_1024_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1025_ = l_mkPanicMessageWithDecl(v___x_1024_, v___x_1023_, v___x_1022_, v___x_1021_, v___x_1020_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21(lean_object* v_s_1026_, lean_object* v_pos_1027_){
_start:
{
lean_object* v_startInclusive_1028_; lean_object* v_endExclusive_1029_; lean_object* v___x_1030_; uint8_t v_decide_1031_; 
v_startInclusive_1028_ = lean_ctor_get(v_s_1026_, 1);
v_endExclusive_1029_ = lean_ctor_get(v_s_1026_, 2);
v___x_1030_ = lean_nat_sub(v_endExclusive_1029_, v_startInclusive_1028_);
v_decide_1031_ = lean_nat_dec_eq(v_pos_1027_, v___x_1030_);
lean_dec(v___x_1030_);
if (v_decide_1031_ == 0)
{
lean_object* v___x_1032_; 
v___x_1032_ = l_String_Slice_Pos_next___redArg(v_s_1026_, v_pos_1027_);
return v___x_1032_;
}
else
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = lean_obj_once(&l_String_Slice_Pos_next_x21___closed__2, &l_String_Slice_Pos_next_x21___closed__2_once, _init_l_String_Slice_Pos_next_x21___closed__2);
v___x_1034_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_1033_);
return v___x_1034_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21___boxed(lean_object* v_s_1035_, lean_object* v_pos_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_String_Slice_Pos_next_x21(v_s_1035_, v_pos_1036_);
lean_dec(v_pos_1036_);
lean_dec_ref(v_s_1035_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg(lean_object* v_s_1038_, lean_object* v_off_1039_){
_start:
{
uint8_t v___y_1041_; lean_object* v_str_1047_; lean_object* v_startInclusive_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; uint8_t v___x_1051_; uint8_t v___x_1052_; uint8_t v___x_1053_; uint8_t v___x_1054_; 
v_str_1047_ = lean_ctor_get(v_s_1038_, 0);
v_startInclusive_1048_ = lean_ctor_get(v_s_1038_, 1);
v___x_1049_ = lean_nat_add(v_startInclusive_1048_, v_off_1039_);
v___x_1050_ = lean_string_get_byte_fast(v_str_1047_, v___x_1049_);
v___x_1051_ = 128;
v___x_1052_ = lean_uint8_land(v___x_1050_, v___x_1051_);
v___x_1053_ = 0;
v___x_1054_ = lean_uint8_dec_eq(v___x_1052_, v___x_1053_);
if (v___x_1054_ == 0)
{
uint8_t v___x_1055_; uint8_t v___x_1056_; uint8_t v___x_1057_; uint8_t v___x_1058_; uint8_t v___x_1059_; uint8_t v___x_1060_; uint8_t v___x_1061_; 
v___x_1055_ = 224;
v___x_1056_ = lean_uint8_land(v___x_1050_, v___x_1055_);
v___x_1057_ = 192;
v___x_1058_ = lean_uint8_dec_eq(v___x_1056_, v___x_1057_);
v___x_1059_ = 240;
v___x_1060_ = lean_uint8_land(v___x_1050_, v___x_1059_);
v___x_1061_ = lean_uint8_dec_eq(v___x_1060_, v___x_1055_);
if (v___x_1061_ == 0)
{
if (v___x_1058_ == 0)
{
uint8_t v___x_1062_; uint8_t v___x_1063_; uint8_t v___x_1064_; 
v___x_1062_ = 248;
v___x_1063_ = lean_uint8_land(v___x_1050_, v___x_1062_);
v___x_1064_ = lean_uint8_dec_eq(v___x_1063_, v___x_1059_);
v___y_1041_ = v___x_1064_;
goto v___jp_1040_;
}
else
{
v___y_1041_ = v___x_1058_;
goto v___jp_1040_;
}
}
else
{
if (v___x_1058_ == 0)
{
v___y_1041_ = v___x_1061_;
goto v___jp_1040_;
}
else
{
v___y_1041_ = v___x_1058_;
goto v___jp_1040_;
}
}
}
else
{
v___y_1041_ = v___x_1054_;
goto v___jp_1040_;
}
v___jp_1040_:
{
if (v___y_1041_ == 0)
{
lean_object* v_zero_1042_; uint8_t v_isZero_1043_; lean_object* v_one_1044_; lean_object* v_n_1045_; 
v_zero_1042_ = lean_unsigned_to_nat(0u);
v_isZero_1043_ = lean_nat_dec_eq(v_off_1039_, v_zero_1042_);
v_one_1044_ = lean_unsigned_to_nat(1u);
v_n_1045_ = lean_nat_sub(v_off_1039_, v_one_1044_);
lean_dec(v_off_1039_);
v_off_1039_ = v_n_1045_;
goto _start;
}
else
{
return v_off_1039_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg___boxed(lean_object* v_s_1065_, lean_object* v_off_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1065_, v_off_1066_);
lean_dec_ref(v_s_1065_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go(lean_object* v_s_1068_, lean_object* v_off_1069_, lean_object* v_h_u2081_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1068_, v_off_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___boxed(lean_object* v_s_1072_, lean_object* v_off_1073_, lean_object* v_h_u2081_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_String_Slice_Pos_prevAux_go(v_s_1072_, v_off_1073_, v_h_u2081_1074_);
lean_dec_ref(v_s_1072_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg(lean_object* v_s_1076_, lean_object* v_pos_1077_){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1078_ = lean_unsigned_to_nat(1u);
v___x_1079_ = lean_nat_sub(v_pos_1077_, v___x_1078_);
v___x_1080_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1076_, v___x_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg___boxed(lean_object* v_s_1081_, lean_object* v_pos_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_String_Slice_Pos_prevAux___redArg(v_s_1081_, v_pos_1082_);
lean_dec(v_pos_1082_);
lean_dec_ref(v_s_1081_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux(lean_object* v_s_1084_, lean_object* v_pos_1085_, lean_object* v_h_1086_){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1087_ = lean_unsigned_to_nat(1u);
v___x_1088_ = lean_nat_sub(v_pos_1085_, v___x_1087_);
v___x_1089_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1084_, v___x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___boxed(lean_object* v_s_1090_, lean_object* v_pos_1091_, lean_object* v_h_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_String_Slice_Pos_prevAux(v_s_1090_, v_pos_1091_, v_h_1092_);
lean_dec(v_pos_1091_);
lean_dec_ref(v_s_1090_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(lean_object* v_off_1094_, lean_object* v_h__1_1095_, lean_object* v_h__2_1096_){
_start:
{
lean_object* v_zero_1097_; uint8_t v_isZero_1098_; 
v_zero_1097_ = lean_unsigned_to_nat(0u);
v_isZero_1098_ = lean_nat_dec_eq(v_off_1094_, v_zero_1097_);
if (v_isZero_1098_ == 1)
{
lean_object* v___x_1099_; 
lean_dec(v_h__2_1096_);
v___x_1099_ = lean_apply_3(v_h__1_1095_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1099_;
}
else
{
lean_object* v_one_1100_; lean_object* v_n_1101_; lean_object* v___x_1102_; 
lean_dec(v_h__1_1095_);
v_one_1100_ = lean_unsigned_to_nat(1u);
v_n_1101_ = lean_nat_sub(v_off_1094_, v_one_1100_);
v___x_1102_ = lean_apply_4(v_h__2_1096_, v_n_1101_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg___boxed(lean_object* v_off_1103_, lean_object* v_h__1_1104_, lean_object* v_h__2_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(v_off_1103_, v_h__1_1104_, v_h__2_1105_);
lean_dec(v_off_1103_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(lean_object* v_s_1107_, lean_object* v_motive_1108_, lean_object* v_off_1109_, lean_object* v_h_u2081_1110_, lean_object* v_hbyte_1111_, lean_object* v_this_1112_, lean_object* v_h__1_1113_, lean_object* v_h__2_1114_){
_start:
{
lean_object* v_zero_1115_; uint8_t v_isZero_1116_; 
v_zero_1115_ = lean_unsigned_to_nat(0u);
v_isZero_1116_ = lean_nat_dec_eq(v_off_1109_, v_zero_1115_);
if (v_isZero_1116_ == 1)
{
lean_object* v___x_1117_; 
lean_dec(v_h__2_1114_);
v___x_1117_ = lean_apply_3(v_h__1_1113_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1117_;
}
else
{
lean_object* v_one_1118_; lean_object* v_n_1119_; lean_object* v___x_1120_; 
lean_dec(v_h__1_1113_);
v_one_1118_ = lean_unsigned_to_nat(1u);
v_n_1119_ = lean_nat_sub(v_off_1109_, v_one_1118_);
v___x_1120_ = lean_apply_4(v_h__2_1114_, v_n_1119_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___boxed(lean_object* v_s_1121_, lean_object* v_motive_1122_, lean_object* v_off_1123_, lean_object* v_h_u2081_1124_, lean_object* v_hbyte_1125_, lean_object* v_this_1126_, lean_object* v_h__1_1127_, lean_object* v_h__2_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(v_s_1121_, v_motive_1122_, v_off_1123_, v_h_u2081_1124_, v_hbyte_1125_, v_this_1126_, v_h__1_1127_, v_h__2_1128_);
lean_dec(v_off_1123_);
lean_dec_ref(v_s_1121_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg(lean_object* v_off_1130_){
_start:
{
lean_inc(v_off_1130_);
return v_off_1130_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg___boxed(lean_object* v_off_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_String_Slice_pos___redArg(v_off_1131_);
lean_dec(v_off_1131_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos(lean_object* v_s_1133_, lean_object* v_off_1134_, lean_object* v_h_1135_){
_start:
{
lean_inc(v_off_1134_);
return v_off_1134_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___boxed(lean_object* v_s_1136_, lean_object* v_off_1137_, lean_object* v_h_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_String_Slice_pos(v_s_1136_, v_off_1137_, v_h_1138_);
lean_dec(v_off_1137_);
lean_dec_ref(v_s_1136_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f(lean_object* v_s_1140_, lean_object* v_off_1141_){
_start:
{
uint8_t v___x_1142_; 
v___x_1142_ = l_String_Pos_Raw_isValidForSlice(v_s_1140_, v_off_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; 
lean_dec(v_off_1141_);
v___x_1143_ = lean_box(0);
return v___x_1143_;
}
else
{
lean_object* v___x_1144_; 
v___x_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1144_, 0, v_off_1141_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f___boxed(lean_object* v_s_1145_, lean_object* v_off_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_String_Slice_pos_x3f(v_s_1145_, v_off_1146_);
lean_dec_ref(v_s_1145_);
return v_res_1147_;
}
}
static lean_object* _init_l_String_Slice_pos_x21___closed__2(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1150_ = ((lean_object*)(l_String_Slice_pos_x21___closed__1));
v___x_1151_ = lean_unsigned_to_nat(4u);
v___x_1152_ = lean_unsigned_to_nat(1661u);
v___x_1153_ = ((lean_object*)(l_String_Slice_pos_x21___closed__0));
v___x_1154_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1155_ = l_mkPanicMessageWithDecl(v___x_1154_, v___x_1153_, v___x_1152_, v___x_1151_, v___x_1150_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21(lean_object* v_s_1156_, lean_object* v_off_1157_){
_start:
{
uint8_t v___x_1158_; 
v___x_1158_ = l_String_Pos_Raw_isValidForSlice(v_s_1156_, v_off_1157_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = lean_obj_once(&l_String_Slice_pos_x21___closed__2, &l_String_Slice_pos_x21___closed__2_once, _init_l_String_Slice_pos_x21___closed__2);
v___x_1160_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_1159_);
return v___x_1160_;
}
else
{
lean_inc(v_off_1157_);
return v_off_1157_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21___boxed(lean_object* v_s_1161_, lean_object* v_off_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_String_Slice_pos_x21(v_s_1161_, v_off_1162_);
lean_dec(v_off_1162_);
lean_dec_ref(v_s_1161_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next___boxed(lean_object* v_s_1167_, lean_object* v_pos_1168_, lean_object* v_h_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = lean_string_utf8_next_fast(v_s_1167_, v_pos_1168_);
lean_dec(v_pos_1168_);
lean_dec_ref(v_s_1167_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x3f(lean_object* v_s_1171_, lean_object* v_pos_1172_){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = lean_string_utf8_byte_size(v_s_1171_);
v___x_1175_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1175_, 0, v_s_1171_);
lean_ctor_set(v___x_1175_, 1, v___x_1173_);
lean_ctor_set(v___x_1175_, 2, v___x_1174_);
v___x_1176_ = l_String_Slice_Pos_next_x3f(v___x_1175_, v_pos_1172_);
lean_dec_ref_known(v___x_1175_, 3);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_box(0);
return v___x_1177_;
}
else
{
lean_object* v_val_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
v_val_1178_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1176_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_val_1178_);
lean_dec(v___x_1176_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_val_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x3f___boxed(lean_object* v_s_1186_, lean_object* v_pos_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_String_Pos_next_x3f(v_s_1186_, v_pos_1187_);
lean_dec(v_pos_1187_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21(lean_object* v_s_1189_, lean_object* v_pos_1190_){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1191_ = lean_unsigned_to_nat(0u);
v___x_1192_ = lean_string_utf8_byte_size(v_s_1189_);
v___x_1193_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1193_, 0, v_s_1189_);
lean_ctor_set(v___x_1193_, 1, v___x_1191_);
lean_ctor_set(v___x_1193_, 2, v___x_1192_);
v___x_1194_ = l_String_Slice_Pos_next_x21(v___x_1193_, v_pos_1190_);
lean_dec_ref_known(v___x_1193_, 3);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21___boxed(lean_object* v_s_1195_, lean_object* v_pos_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_String_Pos_next_x21(v_s_1195_, v_pos_1196_);
lean_dec(v_pos_1196_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg(lean_object* v_off_1198_){
_start:
{
lean_inc(v_off_1198_);
return v_off_1198_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg___boxed(lean_object* v_off_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_String_pos___redArg(v_off_1199_);
lean_dec(v_off_1199_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_String_pos(lean_object* v_s_1201_, lean_object* v_off_1202_, lean_object* v_h_1203_){
_start:
{
lean_inc(v_off_1202_);
return v_off_1202_;
}
}
LEAN_EXPORT lean_object* l_String_pos___boxed(lean_object* v_s_1204_, lean_object* v_off_1205_, lean_object* v_h_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_String_pos(v_s_1204_, v_off_1205_, v_h_1206_);
lean_dec(v_off_1205_);
lean_dec_ref(v_s_1204_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x3f(lean_object* v_s_1208_, lean_object* v_off_1209_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1210_ = lean_unsigned_to_nat(0u);
v___x_1211_ = lean_string_utf8_byte_size(v_s_1208_);
v___x_1212_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1212_, 0, v_s_1208_);
lean_ctor_set(v___x_1212_, 1, v___x_1210_);
lean_ctor_set(v___x_1212_, 2, v___x_1211_);
v___x_1213_ = l_String_Slice_pos_x3f(v___x_1212_, v_off_1209_);
lean_dec_ref_known(v___x_1212_, 3);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_box(0);
return v___x_1214_;
}
else
{
lean_object* v_val_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
v_val_1215_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1213_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_val_1215_);
lean_dec(v___x_1213_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_val_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_pos_x21(lean_object* v_s_1223_, lean_object* v_off_1224_){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1225_ = lean_unsigned_to_nat(0u);
v___x_1226_ = lean_string_utf8_byte_size(v_s_1223_);
v___x_1227_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1227_, 0, v_s_1223_);
lean_ctor_set(v___x_1227_, 1, v___x_1225_);
lean_ctor_set(v___x_1227_, 2, v___x_1226_);
v___x_1228_ = l_String_Slice_pos_x21(v___x_1227_, v_off_1224_);
lean_dec_ref_known(v___x_1227_, 3);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x21___boxed(lean_object* v_s_1229_, lean_object* v_off_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_String_pos_x21(v_s_1229_, v_off_1230_);
lean_dec(v_off_1230_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg(lean_object* v_pos_1232_){
_start:
{
lean_inc(v_pos_1232_);
return v_pos_1232_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg___boxed(lean_object* v_pos_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_String_Slice_Pos_cast___redArg(v_pos_1233_);
lean_dec(v_pos_1233_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast(lean_object* v_s_1235_, lean_object* v_t_1236_, lean_object* v_pos_1237_, lean_object* v_h_1238_){
_start:
{
lean_inc(v_pos_1237_);
return v_pos_1237_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___boxed(lean_object* v_s_1239_, lean_object* v_t_1240_, lean_object* v_pos_1241_, lean_object* v_h_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_String_Slice_Pos_cast(v_s_1239_, v_t_1240_, v_pos_1241_, v_h_1242_);
lean_dec(v_pos_1241_);
lean_dec_ref(v_t_1240_);
lean_dec_ref(v_s_1239_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg(lean_object* v_pos_1244_){
_start:
{
lean_inc(v_pos_1244_);
return v_pos_1244_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg___boxed(lean_object* v_pos_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_String_Pos_cast___redArg(v_pos_1245_);
lean_dec(v_pos_1245_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast(lean_object* v_s_1247_, lean_object* v_t_1248_, lean_object* v_pos_1249_, lean_object* v_h_1250_){
_start:
{
lean_inc(v_pos_1249_);
return v_pos_1249_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___boxed(lean_object* v_s_1251_, lean_object* v_t_1252_, lean_object* v_pos_1253_, lean_object* v_h_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_String_Pos_cast(v_s_1251_, v_t_1252_, v_pos_1253_, v_h_1254_);
lean_dec(v_pos_1253_);
lean_dec_ref(v_t_1252_);
lean_dec_ref(v_s_1251_);
return v_res_1255_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_Raw_utf8GetAux(lean_object* v_x_1256_, lean_object* v_x_1257_, lean_object* v_x_1258_){
_start:
{
if (lean_obj_tag(v_x_1256_) == 0)
{
uint32_t v___x_1259_; 
lean_dec(v_x_1257_);
v___x_1259_ = 65;
return v___x_1259_;
}
else
{
lean_object* v_head_1260_; lean_object* v_tail_1261_; uint8_t v_decide_1262_; 
v_head_1260_ = lean_ctor_get(v_x_1256_, 0);
v_tail_1261_ = lean_ctor_get(v_x_1256_, 1);
v_decide_1262_ = lean_nat_dec_eq(v_x_1257_, v_x_1258_);
if (v_decide_1262_ == 0)
{
uint32_t v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = lean_unbox_uint32(v_head_1260_);
v___x_1264_ = l_Char_utf8Size(v___x_1263_);
v___x_1265_ = lean_nat_add(v_x_1257_, v___x_1264_);
lean_dec(v___x_1264_);
lean_dec(v_x_1257_);
v_x_1256_ = v_tail_1261_;
v_x_1257_ = v___x_1265_;
goto _start;
}
else
{
uint32_t v___x_1267_; 
lean_dec(v_x_1257_);
v___x_1267_ = lean_unbox_uint32(v_head_1260_);
return v___x_1267_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux___boxed(lean_object* v_x_1268_, lean_object* v_x_1269_, lean_object* v_x_1270_){
_start:
{
uint32_t v_res_1271_; lean_object* v_r_1272_; 
v_res_1271_ = l_String_Pos_Raw_utf8GetAux(v_x_1268_, v_x_1269_, v_x_1270_);
lean_dec(v_x_1270_);
lean_dec(v_x_1268_);
v_r_1272_ = lean_box_uint32(v_res_1271_);
return v_r_1272_;
}
}
LEAN_EXPORT uint32_t l_String_utf8GetAux(lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
uint32_t v___x_1276_; 
v___x_1276_ = l_String_Pos_Raw_utf8GetAux(v_a_1273_, v_a_1274_, v_a_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux___boxed(lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
uint32_t v_res_1280_; lean_object* v_r_1281_; 
v_res_1280_ = l_String_utf8GetAux(v_a_1277_, v_a_1278_, v_a_1279_);
lean_dec(v_a_1279_);
lean_dec(v_a_1277_);
v_r_1281_ = lean_box_uint32(v_res_1280_);
return v_r_1281_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get___boxed(lean_object* v_s_1284_, lean_object* v_p_1285_){
_start:
{
uint32_t v_res_1286_; lean_object* v_r_1287_; 
v_res_1286_ = lean_string_utf8_get(v_s_1284_, v_p_1285_);
lean_dec(v_p_1285_);
lean_dec_ref(v_s_1284_);
v_r_1287_ = lean_box_uint32(v_res_1286_);
return v_r_1287_;
}
}
LEAN_EXPORT lean_object* l_String_get___boxed(lean_object* v_s_1290_, lean_object* v_p_1291_){
_start:
{
uint32_t v_res_1292_; lean_object* v_r_1293_; 
v_res_1292_ = lean_string_utf8_get(v_s_1290_, v_p_1291_);
lean_dec(v_p_1291_);
lean_dec_ref(v_s_1290_);
v_r_1293_ = lean_box_uint32(v_res_1292_);
return v_r_1293_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f(lean_object* v_x_1294_, lean_object* v_x_1295_, lean_object* v_x_1296_){
_start:
{
if (lean_obj_tag(v_x_1294_) == 0)
{
lean_object* v___x_1297_; 
lean_dec(v_x_1295_);
v___x_1297_ = lean_box(0);
return v___x_1297_;
}
else
{
lean_object* v_head_1298_; lean_object* v_tail_1299_; uint8_t v_decide_1300_; 
v_head_1298_ = lean_ctor_get(v_x_1294_, 0);
v_tail_1299_ = lean_ctor_get(v_x_1294_, 1);
v_decide_1300_ = lean_nat_dec_eq(v_x_1295_, v_x_1296_);
if (v_decide_1300_ == 0)
{
uint32_t v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1301_ = lean_unbox_uint32(v_head_1298_);
v___x_1302_ = l_Char_utf8Size(v___x_1301_);
v___x_1303_ = lean_nat_add(v_x_1295_, v___x_1302_);
lean_dec(v___x_1302_);
lean_dec(v_x_1295_);
v_x_1294_ = v_tail_1299_;
v_x_1295_ = v___x_1303_;
goto _start;
}
else
{
lean_object* v___x_1305_; 
lean_dec(v_x_1295_);
lean_inc(v_head_1298_);
v___x_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1305_, 0, v_head_1298_);
return v___x_1305_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f___boxed(lean_object* v_x_1306_, lean_object* v_x_1307_, lean_object* v_x_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_String_Pos_Raw_utf8GetAux_x3f(v_x_1306_, v_x_1307_, v_x_1308_);
lean_dec(v_x_1308_);
lean_dec(v_x_1306_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f(lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_String_Pos_Raw_utf8GetAux_x3f(v_a_1310_, v_a_1311_, v_a_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f___boxed(lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_String_utf8GetAux_x3f(v_a_1314_, v_a_1315_, v_a_1316_);
lean_dec(v_a_1316_);
lean_dec(v_a_1314_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1320_, lean_object* v_a_00___x40___internal___hyg_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1320_, v_a_00___x40___internal___hyg_1321_);
lean_dec(v_a_00___x40___internal___hyg_1321_);
lean_dec_ref(v_a_00___x40___internal___hyg_1320_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_String_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1325_, lean_object* v_a_00___x40___internal___hyg_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1325_, v_a_00___x40___internal___hyg_1326_);
lean_dec(v_a_00___x40___internal___hyg_1326_);
lean_dec_ref(v_a_00___x40___internal___hyg_1325_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x21___boxed(lean_object* v_s_1330_, lean_object* v_p_1331_){
_start:
{
uint32_t v_res_1332_; lean_object* v_r_1333_; 
v_res_1332_ = lean_string_utf8_get_bang(v_s_1330_, v_p_1331_);
lean_dec(v_p_1331_);
lean_dec_ref(v_s_1330_);
v_r_1333_ = lean_box_uint32(v_res_1332_);
return v_r_1333_;
}
}
LEAN_EXPORT lean_object* l_String_get_x21___boxed(lean_object* v_s_1336_, lean_object* v_p_1337_){
_start:
{
uint32_t v_res_1338_; lean_object* v_r_1339_; 
v_res_1338_ = lean_string_utf8_get_bang(v_s_1336_, v_p_1337_);
lean_dec(v_p_1337_);
lean_dec_ref(v_s_1336_);
v_r_1339_ = lean_box_uint32(v_res_1338_);
return v_r_1339_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux(uint32_t v_c_x27_1340_, lean_object* v_x_1341_, lean_object* v_x_1342_, lean_object* v_x_1343_){
_start:
{
if (lean_obj_tag(v_x_1341_) == 0)
{
return v_x_1341_;
}
else
{
lean_object* v_head_1344_; lean_object* v_tail_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1361_; 
v_head_1344_ = lean_ctor_get(v_x_1341_, 0);
v_tail_1345_ = lean_ctor_get(v_x_1341_, 1);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_x_1341_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1347_ = v_x_1341_;
v_isShared_1348_ = v_isSharedCheck_1361_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_tail_1345_);
lean_inc(v_head_1344_);
lean_dec(v_x_1341_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1361_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
uint8_t v_decide_1349_; 
v_decide_1349_ = lean_nat_dec_eq(v_x_1342_, v_x_1343_);
if (v_decide_1349_ == 0)
{
uint32_t v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1350_ = lean_unbox_uint32(v_head_1344_);
v___x_1351_ = l_Char_utf8Size(v___x_1350_);
v___x_1352_ = lean_nat_add(v_x_1342_, v___x_1351_);
lean_dec(v___x_1351_);
v___x_1353_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1340_, v_tail_1345_, v___x_1352_, v_x_1343_);
lean_dec(v___x_1352_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 1, v___x_1353_);
v___x_1355_ = v___x_1347_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_head_1344_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
else
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
lean_dec(v_head_1344_);
v___x_1357_ = lean_box_uint32(v_c_x27_1340_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1357_);
v___x_1359_ = v___x_1347_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_tail_1345_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux___boxed(lean_object* v_c_x27_1362_, lean_object* v_x_1363_, lean_object* v_x_1364_, lean_object* v_x_1365_){
_start:
{
uint32_t v_c_x27_boxed_1366_; lean_object* v_res_1367_; 
v_c_x27_boxed_1366_ = lean_unbox_uint32(v_c_x27_1362_);
lean_dec(v_c_x27_1362_);
v_res_1367_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_boxed_1366_, v_x_1363_, v_x_1364_, v_x_1365_);
lean_dec(v_x_1365_);
lean_dec(v_x_1364_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux(uint32_t v_c_x27_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux___boxed(lean_object* v_c_x27_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
uint32_t v_c_x27_boxed_1377_; lean_object* v_res_1378_; 
v_c_x27_boxed_1377_ = lean_unbox_uint32(v_c_x27_1373_);
lean_dec(v_c_x27_1373_);
v_res_1378_ = l_String_utf8SetAux(v_c_x27_boxed_1377_, v_a_1374_, v_a_1375_, v_a_1376_);
lean_dec(v_a_1376_);
lean_dec(v_a_1375_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg(lean_object* v_s_1379_, lean_object* v_pos_1380_){
_start:
{
lean_object* v_str_1381_; lean_object* v_startInclusive_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v_str_1381_ = lean_ctor_get(v_s_1379_, 0);
v_startInclusive_1382_ = lean_ctor_get(v_s_1379_, 1);
v___x_1383_ = lean_nat_add(v_startInclusive_1382_, v_pos_1380_);
v___x_1384_ = lean_string_utf8_next_fast(v_str_1381_, v___x_1383_);
lean_dec(v___x_1383_);
v___x_1385_ = lean_nat_sub(v___x_1384_, v_startInclusive_1382_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg___boxed(lean_object* v_s_1386_, lean_object* v_pos_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_String_Slice_Pos_nextFast___redArg(v_s_1386_, v_pos_1387_);
lean_dec(v_pos_1387_);
lean_dec_ref(v_s_1386_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast(lean_object* v_s_1389_, lean_object* v_pos_1390_, lean_object* v_h_1391_){
_start:
{
lean_object* v_str_1392_; lean_object* v_startInclusive_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v_str_1392_ = lean_ctor_get(v_s_1389_, 0);
v_startInclusive_1393_ = lean_ctor_get(v_s_1389_, 1);
v___x_1394_ = lean_nat_add(v_startInclusive_1393_, v_pos_1390_);
v___x_1395_ = lean_string_utf8_next_fast(v_str_1392_, v___x_1394_);
lean_dec(v___x_1394_);
v___x_1396_ = lean_nat_sub(v___x_1395_, v_startInclusive_1393_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___boxed(lean_object* v_s_1397_, lean_object* v_pos_1398_, lean_object* v_h_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_String_Slice_Pos_nextFast(v_s_1397_, v_pos_1398_, v_h_1399_);
lean_dec(v_pos_1398_);
lean_dec_ref(v_s_1397_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_String_sliceTo(lean_object* v_s_1401_, lean_object* v_p_1402_){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = lean_unsigned_to_nat(0u);
v___x_1404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1404_, 0, v_s_1401_);
lean_ctor_set(v___x_1404_, 1, v___x_1403_);
lean_ctor_set(v___x_1404_, 2, v_p_1402_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_String_replaceEnd(lean_object* v_s_1405_, lean_object* v_p_1406_){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = lean_unsigned_to_nat(0u);
v___x_1408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1408_, 0, v_s_1405_);
lean_ctor_set(v___x_1408_, 1, v___x_1407_);
lean_ctor_set(v___x_1408_, 2, v_p_1406_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_String_sliceFrom(lean_object* v_s_1409_, lean_object* v_p_1410_){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = lean_string_utf8_byte_size(v_s_1409_);
v___x_1412_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1412_, 0, v_s_1409_);
lean_ctor_set(v___x_1412_, 1, v_p_1410_);
lean_ctor_set(v___x_1412_, 2, v___x_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStart(lean_object* v_s_1413_, lean_object* v_p_1414_){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = lean_string_utf8_byte_size(v_s_1413_);
v___x_1416_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1416_, 0, v_s_1413_);
lean_ctor_set(v___x_1416_, 1, v_p_1414_);
lean_ctor_set(v___x_1416_, 2, v___x_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_String_slice___redArg(lean_object* v_s_1417_, lean_object* v_startInclusive_1418_, lean_object* v_endExclusive_1419_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1420_, 0, v_s_1417_);
lean_ctor_set(v___x_1420_, 1, v_startInclusive_1418_);
lean_ctor_set(v___x_1420_, 2, v_endExclusive_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_String_slice(lean_object* v_s_1421_, lean_object* v_startInclusive_1422_, lean_object* v_endExclusive_1423_, lean_object* v_h_1424_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1425_, 0, v_s_1421_);
lean_ctor_set(v___x_1425_, 1, v_startInclusive_1422_);
lean_ctor_set(v___x_1425_, 2, v_endExclusive_1423_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x3f(lean_object* v_s_1426_, lean_object* v_startInclusive_1427_, lean_object* v_endExclusive_1428_){
_start:
{
uint8_t v___x_1429_; 
v___x_1429_ = lean_nat_dec_le(v_startInclusive_1427_, v_endExclusive_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; 
lean_dec(v_endExclusive_1428_);
lean_dec(v_startInclusive_1427_);
lean_dec_ref(v_s_1426_);
v___x_1430_ = lean_box(0);
return v___x_1430_;
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1431_, 0, v_s_1426_);
lean_ctor_set(v___x_1431_, 1, v_startInclusive_1427_);
lean_ctor_set(v___x_1431_, 2, v_endExclusive_1428_);
v___x_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
return v___x_1432_;
}
}
}
LEAN_EXPORT lean_object* l_String_slice_x21(lean_object* v_s_1433_, lean_object* v_p_u2081_1434_, lean_object* v_p_u2082_1435_){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1436_ = lean_unsigned_to_nat(0u);
v___x_1437_ = lean_string_utf8_byte_size(v_s_1433_);
v___x_1438_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1438_, 0, v_s_1433_);
lean_ctor_set(v___x_1438_, 1, v___x_1436_);
lean_ctor_set(v___x_1438_, 2, v___x_1437_);
v___x_1439_ = l_String_Slice_slice_x21(v___x_1438_, v_p_u2081_1434_, v_p_u2082_1435_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x21___boxed(lean_object* v_s_1440_, lean_object* v_p_u2081_1441_, lean_object* v_p_u2082_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_String_slice_x21(v_s_1440_, v_p_u2081_1441_, v_p_u2082_1442_);
lean_dec(v_p_u2082_1442_);
lean_dec(v_p_u2081_1441_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21(lean_object* v_s_1444_, lean_object* v_p_u2081_1445_, lean_object* v_p_u2082_1446_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l_String_slice_x21(v_s_1444_, v_p_u2081_1445_, v_p_u2082_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21___boxed(lean_object* v_s_1448_, lean_object* v_p_u2081_1449_, lean_object* v_p_u2082_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_String_replaceStartEnd_x21(v_s_1448_, v_p_u2081_1449_, v_p_u2082_1450_);
lean_dec(v_p_u2082_1450_);
lean_dec(v_p_u2081_1449_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg(lean_object* v_p_u2080_1452_, lean_object* v_pos_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = lean_nat_add(v_p_u2080_1452_, v_pos_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg___boxed(lean_object* v_p_u2080_1455_, lean_object* v_pos_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_String_Pos_ofSliceFrom___redArg(v_p_u2080_1455_, v_pos_1456_);
lean_dec(v_pos_1456_);
lean_dec(v_p_u2080_1455_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom(lean_object* v_s_1458_, lean_object* v_p_u2080_1459_, lean_object* v_pos_1460_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = lean_nat_add(v_p_u2080_1459_, v_pos_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___boxed(lean_object* v_s_1462_, lean_object* v_p_u2080_1463_, lean_object* v_pos_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_String_Pos_ofSliceFrom(v_s_1462_, v_p_u2080_1463_, v_pos_1464_);
lean_dec(v_pos_1464_);
lean_dec(v_p_u2080_1463_);
lean_dec_ref(v_s_1462_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg(lean_object* v_p_u2080_1466_, lean_object* v_pos_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = lean_nat_add(v_p_u2080_1466_, v_pos_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg___boxed(lean_object* v_p_u2080_1469_, lean_object* v_pos_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_String_Pos_ofReplaceStart___redArg(v_p_u2080_1469_, v_pos_1470_);
lean_dec(v_pos_1470_);
lean_dec(v_p_u2080_1469_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart(lean_object* v_s_1472_, lean_object* v_p_u2080_1473_, lean_object* v_pos_1474_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = lean_nat_add(v_p_u2080_1473_, v_pos_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___boxed(lean_object* v_s_1476_, lean_object* v_p_u2080_1477_, lean_object* v_pos_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_String_Pos_ofReplaceStart(v_s_1476_, v_p_u2080_1477_, v_pos_1478_);
lean_dec(v_pos_1478_);
lean_dec(v_p_u2080_1477_);
lean_dec_ref(v_s_1476_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg(lean_object* v_p_u2080_1480_, lean_object* v_pos_1481_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = lean_nat_sub(v_pos_1481_, v_p_u2080_1480_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg___boxed(lean_object* v_p_u2080_1483_, lean_object* v_pos_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_String_Pos_sliceFrom___redArg(v_p_u2080_1483_, v_pos_1484_);
lean_dec(v_pos_1484_);
lean_dec(v_p_u2080_1483_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom(lean_object* v_s_1486_, lean_object* v_p_u2080_1487_, lean_object* v_pos_1488_, lean_object* v_h_1489_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_nat_sub(v_pos_1488_, v_p_u2080_1487_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___boxed(lean_object* v_s_1491_, lean_object* v_p_u2080_1492_, lean_object* v_pos_1493_, lean_object* v_h_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_String_Pos_sliceFrom(v_s_1491_, v_p_u2080_1492_, v_pos_1493_, v_h_1494_);
lean_dec(v_pos_1493_);
lean_dec(v_p_u2080_1492_);
lean_dec_ref(v_s_1491_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg(lean_object* v_p_u2080_1496_, lean_object* v_pos_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = lean_nat_sub(v_pos_1497_, v_p_u2080_1496_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg___boxed(lean_object* v_p_u2080_1499_, lean_object* v_pos_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_String_Pos_toReplaceStart___redArg(v_p_u2080_1499_, v_pos_1500_);
lean_dec(v_pos_1500_);
lean_dec(v_p_u2080_1499_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart(lean_object* v_s_1502_, lean_object* v_p_u2080_1503_, lean_object* v_pos_1504_, lean_object* v_h_1505_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_nat_sub(v_pos_1504_, v_p_u2080_1503_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___boxed(lean_object* v_s_1507_, lean_object* v_p_u2080_1508_, lean_object* v_pos_1509_, lean_object* v_h_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_String_Pos_toReplaceStart(v_s_1507_, v_p_u2080_1508_, v_pos_1509_, v_h_1510_);
lean_dec(v_pos_1509_);
lean_dec(v_p_u2080_1508_);
lean_dec_ref(v_s_1507_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg(lean_object* v_pos_1512_){
_start:
{
lean_inc(v_pos_1512_);
return v_pos_1512_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg___boxed(lean_object* v_pos_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_String_Pos_ofSliceTo___redArg(v_pos_1513_);
lean_dec(v_pos_1513_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo(lean_object* v_s_1515_, lean_object* v_p_u2080_1516_, lean_object* v_pos_1517_){
_start:
{
lean_inc(v_pos_1517_);
return v_pos_1517_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___boxed(lean_object* v_s_1518_, lean_object* v_p_u2080_1519_, lean_object* v_pos_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_String_Pos_ofSliceTo(v_s_1518_, v_p_u2080_1519_, v_pos_1520_);
lean_dec(v_pos_1520_);
lean_dec(v_p_u2080_1519_);
lean_dec_ref(v_s_1518_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg(lean_object* v_pos_1522_){
_start:
{
lean_inc(v_pos_1522_);
return v_pos_1522_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg___boxed(lean_object* v_pos_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_String_Pos_ofReplaceEnd___redArg(v_pos_1523_);
lean_dec(v_pos_1523_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd(lean_object* v_s_1525_, lean_object* v_p_u2080_1526_, lean_object* v_pos_1527_){
_start:
{
lean_inc(v_pos_1527_);
return v_pos_1527_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___boxed(lean_object* v_s_1528_, lean_object* v_p_u2080_1529_, lean_object* v_pos_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_String_Pos_ofReplaceEnd(v_s_1528_, v_p_u2080_1529_, v_pos_1530_);
lean_dec(v_pos_1530_);
lean_dec(v_p_u2080_1529_);
lean_dec_ref(v_s_1528_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg(lean_object* v_pos_1532_){
_start:
{
lean_inc(v_pos_1532_);
return v_pos_1532_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg___boxed(lean_object* v_pos_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_String_Pos_sliceTo___redArg(v_pos_1533_);
lean_dec(v_pos_1533_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo(lean_object* v_s_1535_, lean_object* v_p_u2080_1536_, lean_object* v_pos_1537_, lean_object* v_h_1538_){
_start:
{
lean_inc(v_pos_1537_);
return v_pos_1537_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___boxed(lean_object* v_s_1539_, lean_object* v_p_u2080_1540_, lean_object* v_pos_1541_, lean_object* v_h_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_String_Pos_sliceTo(v_s_1539_, v_p_u2080_1540_, v_pos_1541_, v_h_1542_);
lean_dec(v_pos_1541_);
lean_dec(v_p_u2080_1540_);
lean_dec_ref(v_s_1539_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg(lean_object* v_pos_1544_){
_start:
{
lean_inc(v_pos_1544_);
return v_pos_1544_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg___boxed(lean_object* v_pos_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_String_Pos_toReplaceEnd___redArg(v_pos_1545_);
lean_dec(v_pos_1545_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd(lean_object* v_s_1547_, lean_object* v_p_u2080_1548_, lean_object* v_pos_1549_, lean_object* v_h_1550_){
_start:
{
lean_inc(v_pos_1549_);
return v_pos_1549_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___boxed(lean_object* v_s_1551_, lean_object* v_p_u2080_1552_, lean_object* v_pos_1553_, lean_object* v_h_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_String_Pos_toReplaceEnd(v_s_1551_, v_p_u2080_1552_, v_pos_1553_, v_h_1554_);
lean_dec(v_pos_1553_);
lean_dec(v_p_u2080_1552_);
lean_dec_ref(v_s_1551_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg(lean_object* v_p_u2080_1556_, lean_object* v_pos_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_nat_add(v_p_u2080_1556_, v_pos_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1559_, lean_object* v_pos_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_String_Slice_Pos_ofSlice___redArg(v_p_u2080_1559_, v_pos_1560_);
lean_dec(v_pos_1560_);
lean_dec(v_p_u2080_1559_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice(lean_object* v_s_1562_, lean_object* v_p_u2080_1563_, lean_object* v_p_u2081_1564_, lean_object* v_h_1565_, lean_object* v_pos_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = lean_nat_add(v_p_u2080_1563_, v_pos_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___boxed(lean_object* v_s_1568_, lean_object* v_p_u2080_1569_, lean_object* v_p_u2081_1570_, lean_object* v_h_1571_, lean_object* v_pos_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_String_Slice_Pos_ofSlice(v_s_1568_, v_p_u2080_1569_, v_p_u2081_1570_, v_h_1571_, v_pos_1572_);
lean_dec(v_pos_1572_);
lean_dec(v_p_u2081_1570_);
lean_dec(v_p_u2080_1569_);
lean_dec_ref(v_s_1568_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg(lean_object* v_p_u2080_1574_, lean_object* v_pos_1575_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_nat_add(v_p_u2080_1574_, v_pos_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1577_, lean_object* v_pos_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_String_Pos_ofSlice___redArg(v_p_u2080_1577_, v_pos_1578_);
lean_dec(v_pos_1578_);
lean_dec(v_p_u2080_1577_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice(lean_object* v_s_1580_, lean_object* v_p_u2080_1581_, lean_object* v_p_u2081_1582_, lean_object* v_h_1583_, lean_object* v_pos_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_nat_add(v_p_u2080_1581_, v_pos_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___boxed(lean_object* v_s_1586_, lean_object* v_p_u2080_1587_, lean_object* v_p_u2081_1588_, lean_object* v_h_1589_, lean_object* v_pos_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_String_Pos_ofSlice(v_s_1586_, v_p_u2080_1587_, v_p_u2081_1588_, v_h_1589_, v_pos_1590_);
lean_dec(v_pos_1590_);
lean_dec(v_p_u2081_1588_);
lean_dec(v_p_u2080_1587_);
lean_dec_ref(v_s_1586_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg(lean_object* v_pos_1592_, lean_object* v_p_u2080_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_nat_sub(v_pos_1592_, v_p_u2080_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg___boxed(lean_object* v_pos_1595_, lean_object* v_p_u2080_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_String_Slice_Pos_slice___redArg(v_pos_1595_, v_p_u2080_1596_);
lean_dec(v_p_u2080_1596_);
lean_dec(v_pos_1595_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice(lean_object* v_s_1598_, lean_object* v_pos_1599_, lean_object* v_p_u2080_1600_, lean_object* v_p_u2081_1601_, lean_object* v_h_u2081_1602_, lean_object* v_h_u2082_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = lean_nat_sub(v_pos_1599_, v_p_u2080_1600_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___boxed(lean_object* v_s_1605_, lean_object* v_pos_1606_, lean_object* v_p_u2080_1607_, lean_object* v_p_u2081_1608_, lean_object* v_h_u2081_1609_, lean_object* v_h_u2082_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_String_Slice_Pos_slice(v_s_1605_, v_pos_1606_, v_p_u2080_1607_, v_p_u2081_1608_, v_h_u2081_1609_, v_h_u2082_1610_);
lean_dec(v_p_u2081_1608_);
lean_dec(v_p_u2080_1607_);
lean_dec(v_pos_1606_);
lean_dec_ref(v_s_1605_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg(lean_object* v_pos_1612_, lean_object* v_p_u2080_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_nat_sub(v_pos_1612_, v_p_u2080_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg___boxed(lean_object* v_pos_1615_, lean_object* v_p_u2080_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_String_Pos_slice___redArg(v_pos_1615_, v_p_u2080_1616_);
lean_dec(v_p_u2080_1616_);
lean_dec(v_pos_1615_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice(lean_object* v_s_1618_, lean_object* v_pos_1619_, lean_object* v_p_u2080_1620_, lean_object* v_p_u2081_1621_, lean_object* v_h_u2081_1622_, lean_object* v_h_u2082_1623_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = lean_nat_sub(v_pos_1619_, v_p_u2080_1620_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___boxed(lean_object* v_s_1625_, lean_object* v_pos_1626_, lean_object* v_p_u2080_1627_, lean_object* v_p_u2081_1628_, lean_object* v_h_u2081_1629_, lean_object* v_h_u2082_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_String_Pos_slice(v_s_1625_, v_pos_1626_, v_p_u2080_1627_, v_p_u2081_1628_, v_h_u2081_1629_, v_h_u2082_1630_);
lean_dec(v_p_u2081_1628_);
lean_dec(v_p_u2080_1627_);
lean_dec(v_pos_1626_);
lean_dec_ref(v_s_1625_);
return v_res_1631_;
}
}
static lean_object* _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2(void){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1634_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__1));
v___x_1635_ = lean_unsigned_to_nat(4u);
v___x_1636_ = lean_unsigned_to_nat(2676u);
v___x_1637_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__0));
v___x_1638_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1639_ = l_mkPanicMessageWithDecl(v___x_1638_, v___x_1637_, v___x_1636_, v___x_1635_, v___x_1634_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg(lean_object* v_pos_1640_, lean_object* v_p_u2080_1641_, lean_object* v_p_u2081_1642_){
_start:
{
uint8_t v___y_1644_; uint8_t v___x_1649_; 
v___x_1649_ = lean_nat_dec_le(v_p_u2080_1641_, v_pos_1640_);
if (v___x_1649_ == 0)
{
v___y_1644_ = v___x_1649_;
goto v___jp_1643_;
}
else
{
uint8_t v___x_1650_; 
v___x_1650_ = lean_nat_dec_le(v_pos_1640_, v_p_u2081_1642_);
v___y_1644_ = v___x_1650_;
goto v___jp_1643_;
}
v___jp_1643_:
{
if (v___y_1644_ == 0)
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1645_ = lean_unsigned_to_nat(0u);
v___x_1646_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1647_ = l_panic___redArg(v___x_1645_, v___x_1646_);
return v___x_1647_;
}
else
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_nat_sub(v_pos_1640_, v_p_u2080_1641_);
return v___x_1648_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1651_, lean_object* v_p_u2080_1652_, lean_object* v_p_u2081_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_String_Slice_Pos_sliceOrPanic___redArg(v_pos_1651_, v_p_u2080_1652_, v_p_u2081_1653_);
lean_dec(v_p_u2081_1653_);
lean_dec(v_p_u2080_1652_);
lean_dec(v_pos_1651_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic(lean_object* v_s_1655_, lean_object* v_pos_1656_, lean_object* v_p_u2080_1657_, lean_object* v_p_u2081_1658_, lean_object* v_h_1659_){
_start:
{
uint8_t v___y_1661_; uint8_t v___x_1666_; 
v___x_1666_ = lean_nat_dec_le(v_p_u2080_1657_, v_pos_1656_);
if (v___x_1666_ == 0)
{
v___y_1661_ = v___x_1666_;
goto v___jp_1660_;
}
else
{
uint8_t v___x_1667_; 
v___x_1667_ = lean_nat_dec_le(v_pos_1656_, v_p_u2081_1658_);
v___y_1661_ = v___x_1667_;
goto v___jp_1660_;
}
v___jp_1660_:
{
if (v___y_1661_ == 0)
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1662_ = lean_unsigned_to_nat(0u);
v___x_1663_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1664_ = l_panic___redArg(v___x_1662_, v___x_1663_);
return v___x_1664_;
}
else
{
lean_object* v___x_1665_; 
v___x_1665_ = lean_nat_sub(v_pos_1656_, v_p_u2080_1657_);
return v___x_1665_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___boxed(lean_object* v_s_1668_, lean_object* v_pos_1669_, lean_object* v_p_u2080_1670_, lean_object* v_p_u2081_1671_, lean_object* v_h_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_String_Slice_Pos_sliceOrPanic(v_s_1668_, v_pos_1669_, v_p_u2080_1670_, v_p_u2081_1671_, v_h_1672_);
lean_dec(v_p_u2081_1671_);
lean_dec(v_p_u2080_1670_);
lean_dec(v_pos_1669_);
lean_dec_ref(v_s_1668_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg(lean_object* v_pos_1674_, lean_object* v_p_u2080_1675_, lean_object* v_p_u2081_1676_){
_start:
{
uint8_t v___y_1678_; uint8_t v___x_1683_; 
v___x_1683_ = lean_nat_dec_le(v_p_u2080_1675_, v_pos_1674_);
if (v___x_1683_ == 0)
{
v___y_1678_ = v___x_1683_;
goto v___jp_1677_;
}
else
{
uint8_t v___x_1684_; 
v___x_1684_ = lean_nat_dec_le(v_pos_1674_, v_p_u2081_1676_);
v___y_1678_ = v___x_1684_;
goto v___jp_1677_;
}
v___jp_1677_:
{
if (v___y_1678_ == 0)
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = lean_unsigned_to_nat(0u);
v___x_1680_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1681_ = l_panic___redArg(v___x_1679_, v___x_1680_);
return v___x_1681_;
}
else
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_nat_sub(v_pos_1674_, v_p_u2080_1675_);
return v___x_1682_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1685_, lean_object* v_p_u2080_1686_, lean_object* v_p_u2081_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_String_Pos_sliceOrPanic___redArg(v_pos_1685_, v_p_u2080_1686_, v_p_u2081_1687_);
lean_dec(v_p_u2081_1687_);
lean_dec(v_p_u2080_1686_);
lean_dec(v_pos_1685_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic(lean_object* v_s_1689_, lean_object* v_pos_1690_, lean_object* v_p_u2080_1691_, lean_object* v_p_u2081_1692_, lean_object* v_h_1693_){
_start:
{
uint8_t v___y_1695_; uint8_t v___x_1700_; 
v___x_1700_ = lean_nat_dec_le(v_p_u2080_1691_, v_pos_1690_);
if (v___x_1700_ == 0)
{
v___y_1695_ = v___x_1700_;
goto v___jp_1694_;
}
else
{
uint8_t v___x_1701_; 
v___x_1701_ = lean_nat_dec_le(v_pos_1690_, v_p_u2081_1692_);
v___y_1695_ = v___x_1701_;
goto v___jp_1694_;
}
v___jp_1694_:
{
if (v___y_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1696_ = lean_unsigned_to_nat(0u);
v___x_1697_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1698_ = l_panic___redArg(v___x_1696_, v___x_1697_);
return v___x_1698_;
}
else
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_nat_sub(v_pos_1690_, v_p_u2080_1691_);
return v___x_1699_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___boxed(lean_object* v_s_1702_, lean_object* v_pos_1703_, lean_object* v_p_u2080_1704_, lean_object* v_p_u2081_1705_, lean_object* v_h_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_String_Pos_sliceOrPanic(v_s_1702_, v_pos_1703_, v_p_u2080_1704_, v_p_u2081_1705_, v_h_1706_);
lean_dec(v_p_u2081_1705_);
lean_dec(v_p_u2080_1704_);
lean_dec(v_pos_1703_);
lean_dec_ref(v_s_1702_);
return v_res_1707_;
}
}
static lean_object* _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1709_ = ((lean_object*)(l_String_Slice_slice_x21___closed__1));
v___x_1710_ = lean_unsigned_to_nat(4u);
v___x_1711_ = lean_unsigned_to_nat(2700u);
v___x_1712_ = ((lean_object*)(l_String_Slice_Pos_ofSlice_x21___redArg___closed__0));
v___x_1713_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1714_ = l_mkPanicMessageWithDecl(v___x_1713_, v___x_1712_, v___x_1711_, v___x_1710_, v___x_1709_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1715_, lean_object* v_p_u2081_1716_, lean_object* v_pos_1717_){
_start:
{
uint8_t v___x_1718_; 
v___x_1718_ = lean_nat_dec_le(v_p_u2080_1715_, v_p_u2081_1716_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = lean_unsigned_to_nat(0u);
v___x_1720_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1721_ = l_panic___redArg(v___x_1719_, v___x_1720_);
return v___x_1721_;
}
else
{
lean_object* v___x_1722_; 
v___x_1722_ = lean_nat_add(v_p_u2080_1715_, v_pos_1717_);
return v___x_1722_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1723_, lean_object* v_p_u2081_1724_, lean_object* v_pos_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_String_Slice_Pos_ofSlice_x21___redArg(v_p_u2080_1723_, v_p_u2081_1724_, v_pos_1725_);
lean_dec(v_pos_1725_);
lean_dec(v_p_u2081_1724_);
lean_dec(v_p_u2080_1723_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21(lean_object* v_s_1727_, lean_object* v_p_u2080_1728_, lean_object* v_p_u2081_1729_, lean_object* v_pos_1730_){
_start:
{
uint8_t v___x_1731_; 
v___x_1731_ = lean_nat_dec_le(v_p_u2080_1728_, v_p_u2081_1729_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1732_ = lean_unsigned_to_nat(0u);
v___x_1733_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1734_ = l_panic___redArg(v___x_1732_, v___x_1733_);
return v___x_1734_;
}
else
{
lean_object* v___x_1735_; 
v___x_1735_ = lean_nat_add(v_p_u2080_1728_, v_pos_1730_);
return v___x_1735_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___boxed(lean_object* v_s_1736_, lean_object* v_p_u2080_1737_, lean_object* v_p_u2081_1738_, lean_object* v_pos_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_String_Slice_Pos_ofSlice_x21(v_s_1736_, v_p_u2080_1737_, v_p_u2081_1738_, v_pos_1739_);
lean_dec(v_pos_1739_);
lean_dec(v_p_u2081_1738_);
lean_dec(v_p_u2080_1737_);
lean_dec_ref(v_s_1736_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1741_, lean_object* v_p_u2081_1742_, lean_object* v_pos_1743_){
_start:
{
uint8_t v___x_1744_; 
v___x_1744_ = lean_nat_dec_le(v_p_u2080_1741_, v_p_u2081_1742_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1745_ = lean_unsigned_to_nat(0u);
v___x_1746_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1747_ = l_panic___redArg(v___x_1745_, v___x_1746_);
return v___x_1747_;
}
else
{
lean_object* v___x_1748_; 
v___x_1748_ = lean_nat_add(v_p_u2080_1741_, v_pos_1743_);
return v___x_1748_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1749_, lean_object* v_p_u2081_1750_, lean_object* v_pos_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_String_Pos_ofSlice_x21___redArg(v_p_u2080_1749_, v_p_u2081_1750_, v_pos_1751_);
lean_dec(v_pos_1751_);
lean_dec(v_p_u2081_1750_);
lean_dec(v_p_u2080_1749_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21(lean_object* v_s_1753_, lean_object* v_p_u2080_1754_, lean_object* v_p_u2081_1755_, lean_object* v_pos_1756_){
_start:
{
uint8_t v___x_1757_; 
v___x_1757_ = lean_nat_dec_le(v_p_u2080_1754_, v_p_u2081_1755_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1758_ = lean_unsigned_to_nat(0u);
v___x_1759_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1760_ = l_panic___redArg(v___x_1758_, v___x_1759_);
return v___x_1760_;
}
else
{
lean_object* v___x_1761_; 
v___x_1761_ = lean_nat_add(v_p_u2080_1754_, v_pos_1756_);
return v___x_1761_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___boxed(lean_object* v_s_1762_, lean_object* v_p_u2080_1763_, lean_object* v_p_u2081_1764_, lean_object* v_pos_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_String_Pos_ofSlice_x21(v_s_1762_, v_p_u2080_1763_, v_p_u2081_1764_, v_pos_1765_);
lean_dec(v_pos_1765_);
lean_dec(v_p_u2081_1764_);
lean_dec(v_p_u2080_1763_);
lean_dec_ref(v_s_1762_);
return v_res_1766_;
}
}
static lean_object* _init_l_String_Slice_Pos_slice_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1769_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__1));
v___x_1770_ = lean_unsigned_to_nat(4u);
v___x_1771_ = lean_unsigned_to_nat(2718u);
v___x_1772_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__0));
v___x_1773_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1774_ = l_mkPanicMessageWithDecl(v___x_1773_, v___x_1772_, v___x_1771_, v___x_1770_, v___x_1769_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg(lean_object* v_pos_1775_, lean_object* v_p_u2080_1776_, lean_object* v_p_u2081_1777_){
_start:
{
uint8_t v___y_1779_; uint8_t v___x_1784_; 
v___x_1784_ = lean_nat_dec_le(v_p_u2080_1776_, v_pos_1775_);
if (v___x_1784_ == 0)
{
v___y_1779_ = v___x_1784_;
goto v___jp_1778_;
}
else
{
uint8_t v___x_1785_; 
v___x_1785_ = lean_nat_dec_le(v_pos_1775_, v_p_u2081_1777_);
v___y_1779_ = v___x_1785_;
goto v___jp_1778_;
}
v___jp_1778_:
{
if (v___y_1779_ == 0)
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1780_ = lean_unsigned_to_nat(0u);
v___x_1781_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1782_ = l_panic___redArg(v___x_1780_, v___x_1781_);
return v___x_1782_;
}
else
{
lean_object* v___x_1783_; 
v___x_1783_ = lean_nat_sub(v_pos_1775_, v_p_u2080_1776_);
return v___x_1783_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1786_, lean_object* v_p_u2080_1787_, lean_object* v_p_u2081_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_String_Slice_Pos_slice_x21___redArg(v_pos_1786_, v_p_u2080_1787_, v_p_u2081_1788_);
lean_dec(v_p_u2081_1788_);
lean_dec(v_p_u2080_1787_);
lean_dec(v_pos_1786_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21(lean_object* v_s_1790_, lean_object* v_pos_1791_, lean_object* v_p_u2080_1792_, lean_object* v_p_u2081_1793_){
_start:
{
uint8_t v___y_1795_; uint8_t v___x_1800_; 
v___x_1800_ = lean_nat_dec_le(v_p_u2080_1792_, v_pos_1791_);
if (v___x_1800_ == 0)
{
v___y_1795_ = v___x_1800_;
goto v___jp_1794_;
}
else
{
uint8_t v___x_1801_; 
v___x_1801_ = lean_nat_dec_le(v_pos_1791_, v_p_u2081_1793_);
v___y_1795_ = v___x_1801_;
goto v___jp_1794_;
}
v___jp_1794_:
{
if (v___y_1795_ == 0)
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1796_ = lean_unsigned_to_nat(0u);
v___x_1797_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1798_ = l_panic___redArg(v___x_1796_, v___x_1797_);
return v___x_1798_;
}
else
{
lean_object* v___x_1799_; 
v___x_1799_ = lean_nat_sub(v_pos_1791_, v_p_u2080_1792_);
return v___x_1799_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___boxed(lean_object* v_s_1802_, lean_object* v_pos_1803_, lean_object* v_p_u2080_1804_, lean_object* v_p_u2081_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_String_Slice_Pos_slice_x21(v_s_1802_, v_pos_1803_, v_p_u2080_1804_, v_p_u2081_1805_);
lean_dec(v_p_u2081_1805_);
lean_dec(v_p_u2080_1804_);
lean_dec(v_pos_1803_);
lean_dec_ref(v_s_1802_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg(lean_object* v_pos_1807_, lean_object* v_p_u2080_1808_, lean_object* v_p_u2081_1809_){
_start:
{
uint8_t v___y_1811_; uint8_t v___x_1816_; 
v___x_1816_ = lean_nat_dec_le(v_p_u2080_1808_, v_pos_1807_);
if (v___x_1816_ == 0)
{
v___y_1811_ = v___x_1816_;
goto v___jp_1810_;
}
else
{
uint8_t v___x_1817_; 
v___x_1817_ = lean_nat_dec_le(v_pos_1807_, v_p_u2081_1809_);
v___y_1811_ = v___x_1817_;
goto v___jp_1810_;
}
v___jp_1810_:
{
if (v___y_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = lean_unsigned_to_nat(0u);
v___x_1813_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1814_ = l_panic___redArg(v___x_1812_, v___x_1813_);
return v___x_1814_;
}
else
{
lean_object* v___x_1815_; 
v___x_1815_ = lean_nat_sub(v_pos_1807_, v_p_u2080_1808_);
return v___x_1815_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1818_, lean_object* v_p_u2080_1819_, lean_object* v_p_u2081_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_String_Pos_slice_x21___redArg(v_pos_1818_, v_p_u2080_1819_, v_p_u2081_1820_);
lean_dec(v_p_u2081_1820_);
lean_dec(v_p_u2080_1819_);
lean_dec(v_pos_1818_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21(lean_object* v_s_1822_, lean_object* v_pos_1823_, lean_object* v_p_u2080_1824_, lean_object* v_p_u2081_1825_){
_start:
{
uint8_t v___y_1827_; uint8_t v___x_1832_; 
v___x_1832_ = lean_nat_dec_le(v_p_u2080_1824_, v_pos_1823_);
if (v___x_1832_ == 0)
{
v___y_1827_ = v___x_1832_;
goto v___jp_1826_;
}
else
{
uint8_t v___x_1833_; 
v___x_1833_ = lean_nat_dec_le(v_pos_1823_, v_p_u2081_1825_);
v___y_1827_ = v___x_1833_;
goto v___jp_1826_;
}
v___jp_1826_:
{
if (v___y_1827_ == 0)
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1828_ = lean_unsigned_to_nat(0u);
v___x_1829_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1830_ = l_panic___redArg(v___x_1828_, v___x_1829_);
return v___x_1830_;
}
else
{
lean_object* v___x_1831_; 
v___x_1831_ = lean_nat_sub(v_pos_1823_, v_p_u2080_1824_);
return v___x_1831_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___boxed(lean_object* v_s_1834_, lean_object* v_pos_1835_, lean_object* v_p_u2080_1836_, lean_object* v_p_u2081_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_String_Pos_slice_x21(v_s_1834_, v_pos_1835_, v_p_u2080_1836_, v_p_u2081_1837_);
lean_dec(v_p_u2081_1837_);
lean_dec(v_p_u2080_1836_);
lean_dec(v_pos_1835_);
lean_dec_ref(v_s_1834_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract(lean_object* v_s_1839_, lean_object* v_p_u2080_1840_, lean_object* v_p_u2081_1841_){
_start:
{
lean_object* v_str_1842_; lean_object* v_startInclusive_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v_str_1842_ = lean_ctor_get(v_s_1839_, 0);
v_startInclusive_1843_ = lean_ctor_get(v_s_1839_, 1);
v___x_1844_ = lean_nat_add(v_startInclusive_1843_, v_p_u2080_1840_);
v___x_1845_ = lean_nat_add(v_startInclusive_1843_, v_p_u2081_1841_);
v___x_1846_ = lean_string_utf8_extract_fast(v_str_1842_, v___x_1844_, v___x_1845_);
lean_dec(v___x_1845_);
lean_dec(v___x_1844_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract___boxed(lean_object* v_s_1847_, lean_object* v_p_u2080_1848_, lean_object* v_p_u2081_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_String_Slice_extract(v_s_1847_, v_p_u2080_1848_, v_p_u2081_1849_);
lean_dec(v_p_u2081_1849_);
lean_dec(v_p_u2080_1848_);
lean_dec_ref(v_s_1847_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn(lean_object* v_s_1851_, lean_object* v_p_1852_, lean_object* v_n_1853_){
_start:
{
lean_object* v_str_1854_; lean_object* v_startInclusive_1855_; lean_object* v_endExclusive_1856_; lean_object* v_zero_1857_; uint8_t v_isZero_1858_; 
v_str_1854_ = lean_ctor_get(v_s_1851_, 0);
v_startInclusive_1855_ = lean_ctor_get(v_s_1851_, 1);
v_endExclusive_1856_ = lean_ctor_get(v_s_1851_, 2);
v_zero_1857_ = lean_unsigned_to_nat(0u);
v_isZero_1858_ = lean_nat_dec_eq(v_n_1853_, v_zero_1857_);
if (v_isZero_1858_ == 1)
{
lean_dec(v_n_1853_);
return v_p_1852_;
}
else
{
lean_object* v___x_1859_; uint8_t v_decide_1860_; lean_object* v_one_1861_; lean_object* v_n_1862_; 
v___x_1859_ = lean_nat_sub(v_endExclusive_1856_, v_startInclusive_1855_);
v_decide_1860_ = lean_nat_dec_eq(v_p_1852_, v___x_1859_);
lean_dec(v___x_1859_);
v_one_1861_ = lean_unsigned_to_nat(1u);
v_n_1862_ = lean_nat_sub(v_n_1853_, v_one_1861_);
lean_dec(v_n_1853_);
if (v_decide_1860_ == 0)
{
goto v___jp_1863_;
}
else
{
if (v_isZero_1858_ == 0)
{
lean_dec(v_n_1862_);
return v_p_1852_;
}
else
{
goto v___jp_1863_;
}
}
v___jp_1863_:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1864_ = lean_nat_add(v_startInclusive_1855_, v_p_1852_);
lean_dec(v_p_1852_);
v___x_1865_ = lean_string_utf8_next_fast(v_str_1854_, v___x_1864_);
lean_dec(v___x_1864_);
v___x_1866_ = lean_nat_sub(v___x_1865_, v_startInclusive_1855_);
v_p_1852_ = v___x_1866_;
v_n_1853_ = v_n_1862_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn___boxed(lean_object* v_s_1868_, lean_object* v_p_1869_, lean_object* v_n_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_String_Slice_Pos_nextn(v_s_1868_, v_p_1869_, v_n_1870_);
lean_dec_ref(v_s_1868_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_nextn(lean_object* v_s_1872_, lean_object* v_p_1873_, lean_object* v_n_1874_){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1875_ = lean_unsigned_to_nat(0u);
v___x_1876_ = lean_string_utf8_byte_size(v_s_1872_);
v___x_1877_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1877_, 0, v_s_1872_);
lean_ctor_set(v___x_1877_, 1, v___x_1875_);
lean_ctor_set(v___x_1877_, 2, v___x_1876_);
v___x_1878_ = l_String_Slice_Pos_nextn(v___x_1877_, v_p_1873_, v_n_1874_);
lean_dec_ref_known(v___x_1877_, 3);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(lean_object* v_n_1879_, lean_object* v_h__1_1880_, lean_object* v_h__2_1881_){
_start:
{
lean_object* v_zero_1882_; uint8_t v_isZero_1883_; 
v_zero_1882_ = lean_unsigned_to_nat(0u);
v_isZero_1883_ = lean_nat_dec_eq(v_n_1879_, v_zero_1882_);
if (v_isZero_1883_ == 1)
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
lean_dec(v_h__2_1881_);
v___x_1884_ = lean_box(0);
v___x_1885_ = lean_apply_1(v_h__1_1880_, v___x_1884_);
return v___x_1885_;
}
else
{
lean_object* v_one_1886_; lean_object* v_n_1887_; lean_object* v___x_1888_; 
lean_dec(v_h__1_1880_);
v_one_1886_ = lean_unsigned_to_nat(1u);
v_n_1887_ = lean_nat_sub(v_n_1879_, v_one_1886_);
v___x_1888_ = lean_apply_1(v_h__2_1881_, v_n_1887_);
return v___x_1888_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg___boxed(lean_object* v_n_1889_, lean_object* v_h__1_1890_, lean_object* v_h__2_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(v_n_1889_, v_h__1_1890_, v_h__2_1891_);
lean_dec(v_n_1889_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(lean_object* v_motive_1893_, lean_object* v_n_1894_, lean_object* v_h__1_1895_, lean_object* v_h__2_1896_){
_start:
{
lean_object* v_zero_1897_; uint8_t v_isZero_1898_; 
v_zero_1897_ = lean_unsigned_to_nat(0u);
v_isZero_1898_ = lean_nat_dec_eq(v_n_1894_, v_zero_1897_);
if (v_isZero_1898_ == 1)
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
lean_dec(v_h__2_1896_);
v___x_1899_ = lean_box(0);
v___x_1900_ = lean_apply_1(v_h__1_1895_, v___x_1899_);
return v___x_1900_;
}
else
{
lean_object* v_one_1901_; lean_object* v_n_1902_; lean_object* v___x_1903_; 
lean_dec(v_h__1_1895_);
v_one_1901_ = lean_unsigned_to_nat(1u);
v_n_1902_ = lean_nat_sub(v_n_1894_, v_one_1901_);
v___x_1903_ = lean_apply_1(v_h__2_1896_, v_n_1902_);
return v___x_1903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___boxed(lean_object* v_motive_1904_, lean_object* v_n_1905_, lean_object* v_h__1_1906_, lean_object* v_h__2_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(v_motive_1904_, v_n_1905_, v_h__1_1906_, v_h__2_1907_);
lean_dec(v_n_1905_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next___boxed(lean_object* v_s_1911_, lean_object* v_p_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = lean_string_utf8_next(v_s_1911_, v_p_1912_);
lean_dec(v_p_1912_);
lean_dec_ref(v_s_1911_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_String_next___boxed(lean_object* v_s_1916_, lean_object* v_p_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = lean_string_utf8_next(v_s_1916_, v_p_1917_);
lean_dec(v_p_1917_);
lean_dec_ref(v_s_1916_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux(lean_object* v_x_1919_, lean_object* v_x_1920_, lean_object* v_x_1921_){
_start:
{
if (lean_obj_tag(v_x_1919_) == 0)
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
lean_dec(v_x_1920_);
v___x_1922_ = lean_unsigned_to_nat(1u);
v___x_1923_ = lean_nat_sub(v_x_1921_, v___x_1922_);
return v___x_1923_;
}
else
{
lean_object* v_head_1924_; lean_object* v_tail_1925_; uint32_t v___x_1926_; lean_object* v___x_1927_; lean_object* v_i_x27_1928_; uint8_t v___x_1929_; 
v_head_1924_ = lean_ctor_get(v_x_1919_, 0);
v_tail_1925_ = lean_ctor_get(v_x_1919_, 1);
v___x_1926_ = lean_unbox_uint32(v_head_1924_);
v___x_1927_ = l_Char_utf8Size(v___x_1926_);
v_i_x27_1928_ = lean_nat_add(v_x_1920_, v___x_1927_);
lean_dec(v___x_1927_);
v___x_1929_ = lean_nat_dec_le(v_x_1921_, v_i_x27_1928_);
if (v___x_1929_ == 0)
{
lean_dec(v_x_1920_);
v_x_1919_ = v_tail_1925_;
v_x_1920_ = v_i_x27_1928_;
goto _start;
}
else
{
lean_dec(v_i_x27_1928_);
return v_x_1920_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux___boxed(lean_object* v_x_1931_, lean_object* v_x_1932_, lean_object* v_x_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_String_Pos_Raw_utf8PrevAux(v_x_1931_, v_x_1932_, v_x_1933_);
lean_dec(v_x_1933_);
lean_dec(v_x_1931_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux(lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_){
_start:
{
lean_object* v___x_1938_; 
v___x_1938_ = l_String_Pos_Raw_utf8PrevAux(v_a_1935_, v_a_1936_, v_a_1937_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux___boxed(lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_String_utf8PrevAux(v_a_1939_, v_a_1940_, v_a_1941_);
lean_dec(v_a_1941_);
lean_dec(v_a_1939_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_prev___boxed(lean_object* v_a_00___x40___internal___hyg_1945_, lean_object* v_a_00___x40___internal___hyg_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_1945_, v_a_00___x40___internal___hyg_1946_);
lean_dec(v_a_00___x40___internal___hyg_1946_);
lean_dec_ref(v_a_00___x40___internal___hyg_1945_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_String_prev___boxed(lean_object* v_a_00___x40___internal___hyg_1950_, lean_object* v_a_00___x40___internal___hyg_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_1950_, v_a_00___x40___internal___hyg_1951_);
lean_dec(v_a_00___x40___internal___hyg_1951_);
lean_dec_ref(v_a_00___x40___internal___hyg_1950_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_1955_, lean_object* v_a_00___x40___internal___hyg_1956_){
_start:
{
uint8_t v_res_1957_; lean_object* v_r_1958_; 
v_res_1957_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_1955_, v_a_00___x40___internal___hyg_1956_);
lean_dec(v_a_00___x40___internal___hyg_1956_);
lean_dec_ref(v_a_00___x40___internal___hyg_1955_);
v_r_1958_ = lean_box(v_res_1957_);
return v_r_1958_;
}
}
LEAN_EXPORT lean_object* l_String_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_1961_, lean_object* v_a_00___x40___internal___hyg_1962_){
_start:
{
uint8_t v_res_1963_; lean_object* v_r_1964_; 
v_res_1963_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_1961_, v_a_00___x40___internal___hyg_1962_);
lean_dec(v_a_00___x40___internal___hyg_1962_);
lean_dec_ref(v_a_00___x40___internal___hyg_1961_);
v_r_1964_ = lean_box(v_res_1963_);
return v_r_1964_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x27___boxed(lean_object* v_s_1968_, lean_object* v_p_1969_, lean_object* v_h_1970_){
_start:
{
uint32_t v_res_1971_; lean_object* v_r_1972_; 
v_res_1971_ = lean_string_utf8_get_fast(v_s_1968_, v_p_1969_);
lean_dec(v_p_1969_);
lean_dec_ref(v_s_1968_);
v_r_1972_ = lean_box_uint32(v_res_1971_);
return v_r_1972_;
}
}
LEAN_EXPORT lean_object* l_String_get_x27___boxed(lean_object* v_s_1976_, lean_object* v_p_1977_, lean_object* v_h_1978_){
_start:
{
uint32_t v_res_1979_; lean_object* v_r_1980_; 
v_res_1979_ = lean_string_utf8_get_fast(v_s_1976_, v_p_1977_);
lean_dec(v_p_1977_);
lean_dec_ref(v_s_1976_);
v_r_1980_ = lean_box_uint32(v_res_1979_);
return v_r_1980_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next_x27___boxed(lean_object* v_s_1984_, lean_object* v_p_1985_, lean_object* v_h_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = lean_string_utf8_next_fast(v_s_1984_, v_p_1985_);
lean_dec(v_p_1985_);
lean_dec_ref(v_s_1984_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_String_next_x27___boxed(lean_object* v_s_1991_, lean_object* v_p_1992_, lean_object* v_h_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = lean_string_utf8_next_fast(v_s_1991_, v_p_1992_);
lean_dec(v_p_1992_);
lean_dec_ref(v_s_1991_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter___redArg(lean_object* v_x_1995_, lean_object* v_x_1996_, lean_object* v_x_1997_, lean_object* v_h__1_1998_, lean_object* v_h__2_1999_){
_start:
{
if (lean_obj_tag(v_x_1995_) == 0)
{
lean_object* v___x_2000_; 
lean_dec(v_h__2_1999_);
v___x_2000_ = lean_apply_2(v_h__1_1998_, v_x_1996_, v_x_1997_);
return v___x_2000_;
}
else
{
lean_object* v_head_2001_; lean_object* v_tail_2002_; lean_object* v___x_2003_; 
lean_dec(v_h__1_1998_);
v_head_2001_ = lean_ctor_get(v_x_1995_, 0);
lean_inc(v_head_2001_);
v_tail_2002_ = lean_ctor_get(v_x_1995_, 1);
lean_inc(v_tail_2002_);
lean_dec_ref_known(v_x_1995_, 2);
v___x_2003_ = lean_apply_4(v_h__2_1999_, v_head_2001_, v_tail_2002_, v_x_1996_, v_x_1997_);
return v___x_2003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter(lean_object* v_motive_2004_, lean_object* v_x_2005_, lean_object* v_x_2006_, lean_object* v_x_2007_, lean_object* v_h__1_2008_, lean_object* v_h__2_2009_){
_start:
{
if (lean_obj_tag(v_x_2005_) == 0)
{
lean_object* v___x_2010_; 
lean_dec(v_h__2_2009_);
v___x_2010_ = lean_apply_2(v_h__1_2008_, v_x_2006_, v_x_2007_);
return v___x_2010_;
}
else
{
lean_object* v_head_2011_; lean_object* v_tail_2012_; lean_object* v___x_2013_; 
lean_dec(v_h__1_2008_);
v_head_2011_ = lean_ctor_get(v_x_2005_, 0);
lean_inc(v_head_2011_);
v_tail_2012_ = lean_ctor_get(v_x_2005_, 1);
lean_inc(v_tail_2012_);
lean_dec_ref_known(v_x_2005_, 2);
v___x_2013_ = lean_apply_4(v_h__2_2009_, v_head_2011_, v_tail_2012_, v_x_2006_, v_x_2007_);
return v___x_2013_;
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop(lean_object* v_a_2014_, lean_object* v_b_2015_, lean_object* v_stopPos_2016_, lean_object* v_i_2017_){
_start:
{
uint8_t v___y_2019_; lean_object* v___x_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; uint8_t v___y_2026_; 
v___x_2022_ = lean_unsigned_to_nat(1u);
v___x_2023_ = lean_nat_add(v_i_2017_, v___x_2022_);
v___x_2024_ = lean_nat_dec_le(v___x_2023_, v_stopPos_2016_);
lean_dec(v___x_2023_);
if (v___x_2024_ == 0)
{
return v_i_2017_;
}
else
{
uint32_t v___x_2027_; uint32_t v___x_2028_; uint8_t v___x_2029_; 
v___x_2027_ = lean_string_utf8_get(v_a_2014_, v_i_2017_);
v___x_2028_ = lean_string_utf8_get(v_b_2015_, v_i_2017_);
v___x_2029_ = lean_uint32_dec_eq(v___x_2027_, v___x_2028_);
if (v___x_2029_ == 0)
{
v___y_2026_ = v___x_2024_;
goto v___jp_2025_;
}
else
{
uint8_t v___x_2030_; 
v___x_2030_ = 0;
v___y_2026_ = v___x_2030_;
goto v___jp_2025_;
}
}
v___jp_2018_:
{
if (v___y_2019_ == 0)
{
lean_object* v___x_2020_; 
v___x_2020_ = lean_string_utf8_next(v_a_2014_, v_i_2017_);
lean_dec(v_i_2017_);
v_i_2017_ = v___x_2020_;
goto _start;
}
else
{
return v_i_2017_;
}
}
v___jp_2025_:
{
if (v___x_2024_ == 0)
{
v___y_2019_ = v___x_2024_;
goto v___jp_2018_;
}
else
{
v___y_2019_ = v___y_2026_;
goto v___jp_2018_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop___boxed(lean_object* v_a_2031_, lean_object* v_b_2032_, lean_object* v_stopPos_2033_, lean_object* v_i_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_String_firstDiffPos_loop(v_a_2031_, v_b_2032_, v_stopPos_2033_, v_i_2034_);
lean_dec(v_stopPos_2033_);
lean_dec_ref(v_b_2032_);
lean_dec_ref(v_a_2031_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos(lean_object* v_a_2036_, lean_object* v_b_2037_){
_start:
{
lean_object* v___y_2039_; lean_object* v___x_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; 
v___x_2042_ = lean_string_utf8_byte_size(v_a_2036_);
v___x_2043_ = lean_string_utf8_byte_size(v_b_2037_);
v___x_2044_ = lean_nat_dec_le(v___x_2042_, v___x_2043_);
if (v___x_2044_ == 0)
{
v___y_2039_ = v___x_2043_;
goto v___jp_2038_;
}
else
{
v___y_2039_ = v___x_2042_;
goto v___jp_2038_;
}
v___jp_2038_:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2040_ = lean_unsigned_to_nat(0u);
v___x_2041_ = l_String_firstDiffPos_loop(v_a_2036_, v_b_2037_, v___y_2039_, v___x_2040_);
lean_dec(v___y_2039_);
return v___x_2041_;
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos___boxed(lean_object* v_a_2045_, lean_object* v_b_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_String_firstDiffPos(v_a_2045_, v_b_2046_);
lean_dec_ref(v_b_2046_);
lean_dec_ref(v_a_2045_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082(lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_){
_start:
{
if (lean_obj_tag(v_a_2048_) == 0)
{
return v_a_2048_;
}
else
{
lean_object* v_head_2051_; lean_object* v_tail_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2065_; 
v_head_2051_ = lean_ctor_get(v_a_2048_, 0);
v_tail_2052_ = lean_ctor_get(v_a_2048_, 1);
v_isSharedCheck_2065_ = !lean_is_exclusive(v_a_2048_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2054_ = v_a_2048_;
v_isShared_2055_ = v_isSharedCheck_2065_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_tail_2052_);
lean_inc(v_head_2051_);
lean_dec(v_a_2048_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2065_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
uint8_t v_decide_2056_; 
v_decide_2056_ = lean_nat_dec_eq(v_a_2049_, v_a_2050_);
if (v_decide_2056_ == 0)
{
uint32_t v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2062_; 
v___x_2057_ = lean_unbox_uint32(v_head_2051_);
v___x_2058_ = l_Char_utf8Size(v___x_2057_);
v___x_2059_ = lean_nat_add(v_a_2049_, v___x_2058_);
lean_dec(v___x_2058_);
v___x_2060_ = l_String_Pos_Raw_extract_go_u2082(v_tail_2052_, v___x_2059_, v_a_2050_);
lean_dec(v___x_2059_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 1, v___x_2060_);
v___x_2062_ = v___x_2054_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_head_2051_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
else
{
lean_object* v___x_2064_; 
lean_del_object(v___x_2054_);
lean_dec(v_tail_2052_);
lean_dec(v_head_2051_);
v___x_2064_ = lean_box(0);
return v___x_2064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082___boxed(lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_String_Pos_Raw_extract_go_u2082(v_a_2066_, v_a_2067_, v_a_2068_);
lean_dec(v_a_2068_);
lean_dec(v_a_2067_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081(lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_){
_start:
{
if (lean_obj_tag(v_a_2070_) == 0)
{
lean_dec(v_a_2071_);
return v_a_2070_;
}
else
{
lean_object* v_head_2074_; lean_object* v_tail_2075_; uint8_t v_decide_2076_; 
v_head_2074_ = lean_ctor_get(v_a_2070_, 0);
v_tail_2075_ = lean_ctor_get(v_a_2070_, 1);
v_decide_2076_ = lean_nat_dec_eq(v_a_2071_, v_a_2072_);
if (v_decide_2076_ == 0)
{
uint32_t v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
lean_inc(v_tail_2075_);
lean_inc(v_head_2074_);
lean_dec_ref_known(v_a_2070_, 2);
v___x_2077_ = lean_unbox_uint32(v_head_2074_);
lean_dec(v_head_2074_);
v___x_2078_ = l_Char_utf8Size(v___x_2077_);
v___x_2079_ = lean_nat_add(v_a_2071_, v___x_2078_);
lean_dec(v___x_2078_);
lean_dec(v_a_2071_);
v_a_2070_ = v_tail_2075_;
v_a_2071_ = v___x_2079_;
goto _start;
}
else
{
lean_object* v___x_2081_; 
v___x_2081_ = l_String_Pos_Raw_extract_go_u2082(v_a_2070_, v_a_2071_, v_a_2073_);
lean_dec(v_a_2071_);
return v___x_2081_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081___boxed(lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_String_Pos_Raw_extract_go_u2081(v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
lean_dec(v_a_2085_);
lean_dec(v_a_2084_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract___boxed(lean_object* v_a_00___x40___internal___hyg_2090_, lean_object* v_a_00___x40___internal___hyg_2091_, lean_object* v_a_00___x40___internal___hyg_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = lean_string_utf8_extract(v_a_00___x40___internal___hyg_2090_, v_a_00___x40___internal___hyg_2091_, v_a_00___x40___internal___hyg_2092_);
lean_dec(v_a_00___x40___internal___hyg_2092_);
lean_dec(v_a_00___x40___internal___hyg_2091_);
lean_dec_ref(v_a_00___x40___internal___hyg_2090_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux(lean_object* v_s_2094_, lean_object* v_pos_2095_, lean_object* v_i_2096_, lean_object* v_offset_2097_){
_start:
{
uint8_t v___x_2098_; 
v___x_2098_ = lean_nat_dec_le(v_pos_2095_, v_i_2096_);
if (v___x_2098_ == 0)
{
uint8_t v___x_2099_; 
v___x_2099_ = lean_string_utf8_at_end(v_s_2094_, v_i_2096_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2100_ = lean_string_utf8_next(v_s_2094_, v_i_2096_);
lean_dec(v_i_2096_);
v___x_2101_ = lean_unsigned_to_nat(1u);
v___x_2102_ = lean_nat_add(v_offset_2097_, v___x_2101_);
lean_dec(v_offset_2097_);
v_i_2096_ = v___x_2100_;
v_offset_2097_ = v___x_2102_;
goto _start;
}
else
{
lean_dec(v_i_2096_);
return v_offset_2097_;
}
}
else
{
lean_dec(v_i_2096_);
return v_offset_2097_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux___boxed(lean_object* v_s_2104_, lean_object* v_pos_2105_, lean_object* v_i_2106_, lean_object* v_offset_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2104_, v_pos_2105_, v_i_2106_, v_offset_2107_);
lean_dec(v_pos_2105_);
lean_dec_ref(v_s_2104_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos(lean_object* v_s_2109_, lean_object* v_pos_2110_){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = lean_unsigned_to_nat(0u);
v___x_2112_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2109_, v_pos_2110_, v___x_2111_, v___x_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos___boxed(lean_object* v_s_2113_, lean_object* v_pos_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l_String_Pos_Raw_offsetOfPos(v_s_2113_, v_pos_2114_);
lean_dec(v_pos_2114_);
lean_dec_ref(v_s_2113_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos(lean_object* v_s_2116_, lean_object* v_pos_2117_){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = lean_unsigned_to_nat(0u);
v___x_2119_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2116_, v_pos_2117_, v___x_2118_, v___x_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos___boxed(lean_object* v_s_2120_, lean_object* v_pos_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_String_offsetOfPos(v_s_2120_, v_pos_2121_);
lean_dec(v_pos_2121_);
lean_dec_ref(v_s_2120_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* lean_string_offsetofpos(lean_object* v_s_2123_, lean_object* v_pos_2124_){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = lean_unsigned_to_nat(0u);
v___x_2126_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2123_, v_pos_2124_, v___x_2125_, v___x_2125_);
lean_dec(v_pos_2124_);
lean_dec_ref(v_s_2123_);
return v___x_2126_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(lean_object* v_s1_2127_, lean_object* v_s2_2128_, lean_object* v_off1_2129_, lean_object* v_off2_2130_, lean_object* v_stop1_2131_){
_start:
{
uint8_t v___x_2132_; 
v___x_2132_ = lean_nat_dec_lt(v_off1_2129_, v_stop1_2131_);
if (v___x_2132_ == 0)
{
uint8_t v___x_2133_; 
lean_dec(v_off2_2130_);
lean_dec(v_off1_2129_);
v___x_2133_ = 1;
return v___x_2133_;
}
else
{
uint32_t v_c_u2081_2134_; uint32_t v_c_u2082_2135_; uint8_t v___x_2136_; 
v_c_u2081_2134_ = lean_string_utf8_get(v_s1_2127_, v_off1_2129_);
v_c_u2082_2135_ = lean_string_utf8_get(v_s2_2128_, v_off2_2130_);
v___x_2136_ = lean_uint32_dec_eq(v_c_u2081_2134_, v_c_u2082_2135_);
if (v___x_2136_ == 0)
{
lean_dec(v_off2_2130_);
lean_dec(v_off1_2129_);
return v___x_2136_;
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2137_ = l_Char_utf8Size(v_c_u2081_2134_);
v___x_2138_ = lean_nat_add(v_off1_2129_, v___x_2137_);
lean_dec(v___x_2137_);
lean_dec(v_off1_2129_);
v___x_2139_ = l_Char_utf8Size(v_c_u2082_2135_);
v___x_2140_ = lean_nat_add(v_off2_2130_, v___x_2139_);
lean_dec(v___x_2139_);
lean_dec(v_off2_2130_);
v_off1_2129_ = v___x_2138_;
v_off2_2130_ = v___x_2140_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop___boxed(lean_object* v_s1_2142_, lean_object* v_s2_2143_, lean_object* v_off1_2144_, lean_object* v_off2_2145_, lean_object* v_stop1_2146_){
_start:
{
uint8_t v_res_2147_; lean_object* v_r_2148_; 
v_res_2147_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2142_, v_s2_2143_, v_off1_2144_, v_off2_2145_, v_stop1_2146_);
lean_dec(v_stop1_2146_);
lean_dec_ref(v_s2_2143_);
lean_dec_ref(v_s1_2142_);
v_r_2148_ = lean_box(v_res_2147_);
return v_r_2148_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_substrEq(lean_object* v_s1_2149_, lean_object* v_pos1_2150_, lean_object* v_s2_2151_, lean_object* v_pos2_2152_, lean_object* v_sz_2153_){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2154_ = lean_nat_add(v_pos1_2150_, v_sz_2153_);
v___x_2155_ = lean_string_utf8_byte_size(v_s1_2149_);
v___x_2156_ = lean_nat_dec_le(v___x_2154_, v___x_2155_);
if (v___x_2156_ == 0)
{
lean_dec(v___x_2154_);
lean_dec(v_pos2_2152_);
lean_dec(v_pos1_2150_);
return v___x_2156_;
}
else
{
lean_object* v___x_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; 
v___x_2157_ = lean_nat_add(v_pos2_2152_, v_sz_2153_);
v___x_2158_ = lean_string_utf8_byte_size(v_s2_2151_);
v___x_2159_ = lean_nat_dec_le(v___x_2157_, v___x_2158_);
lean_dec(v___x_2157_);
if (v___x_2159_ == 0)
{
lean_dec(v___x_2154_);
lean_dec(v_pos2_2152_);
lean_dec(v_pos1_2150_);
return v___x_2159_;
}
else
{
uint8_t v___x_2160_; 
v___x_2160_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2149_, v_s2_2151_, v_pos1_2150_, v_pos2_2152_, v___x_2154_);
lean_dec(v___x_2154_);
return v___x_2160_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_substrEq___boxed(lean_object* v_s1_2161_, lean_object* v_pos1_2162_, lean_object* v_s2_2163_, lean_object* v_pos2_2164_, lean_object* v_sz_2165_){
_start:
{
uint8_t v_res_2166_; lean_object* v_r_2167_; 
v_res_2166_ = l_String_Pos_Raw_substrEq(v_s1_2161_, v_pos1_2162_, v_s2_2163_, v_pos2_2164_, v_sz_2165_);
lean_dec(v_sz_2165_);
lean_dec_ref(v_s2_2163_);
lean_dec_ref(v_s1_2161_);
v_r_2167_ = lean_box(v_res_2166_);
return v_r_2167_;
}
}
LEAN_EXPORT uint8_t l_String_substrEq(lean_object* v_s1_2168_, lean_object* v_pos1_2169_, lean_object* v_s2_2170_, lean_object* v_pos2_2171_, lean_object* v_sz_2172_){
_start:
{
uint8_t v___x_2173_; 
v___x_2173_ = l_String_Pos_Raw_substrEq(v_s1_2168_, v_pos1_2169_, v_s2_2170_, v_pos2_2171_, v_sz_2172_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l_String_substrEq___boxed(lean_object* v_s1_2174_, lean_object* v_pos1_2175_, lean_object* v_s2_2176_, lean_object* v_pos2_2177_, lean_object* v_sz_2178_){
_start:
{
uint8_t v_res_2179_; lean_object* v_r_2180_; 
v_res_2179_ = l_String_substrEq(v_s1_2174_, v_pos1_2175_, v_s2_2176_, v_pos2_2177_, v_sz_2178_);
lean_dec(v_sz_2178_);
lean_dec_ref(v_s2_2176_);
lean_dec_ref(v_s1_2174_);
v_r_2180_ = lean_box(v_res_2179_);
return v_r_2180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object* v_x_2181_, lean_object* v_x_2182_, lean_object* v_h__1_2183_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = lean_apply_2(v_h__1_2183_, v_x_2181_, v_x_2182_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object* v_motive_2185_, lean_object* v_x_2186_, lean_object* v_x_2187_, lean_object* v_h__1_2188_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = lean_apply_2(v_h__1_2188_, v_x_2186_, v_x_2187_);
return v___x_2189_;
}
}
lean_object* runtime_initialize_Init_Data_String_Decode(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Decode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_instLT = _init_l_String_instLT();
lean_mark_persistent(l_String_instLT);
l_String_instLE = _init_l_String_instLE();
lean_mark_persistent(l_String_instLE);
l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1 = _init_l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1();
lean_mark_persistent(l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Decode(uint8_t builtin);
lean_object* initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Decode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
