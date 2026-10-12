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
uint8_t v___x_90_; uint8_t v_b_u2080_91_; uint8_t v___x_92_; uint8_t v_b_u2081_93_; uint8_t v_b_u2082_94_; uint32_t v___x_95_; uint32_t v___x_96_; uint32_t v___x_97_; uint32_t v___x_98_; uint32_t v___x_99_; uint32_t v___x_100_; uint32_t v___x_101_; uint32_t v___x_102_; uint32_t v_r_103_; uint32_t v___x_104_; uint8_t v___x_105_; 
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
v___x_104_ = 2048;
v___x_105_ = lean_uint32_dec_lt(v_r_103_, v___x_104_);
if (v___x_105_ == 0)
{
uint32_t v___x_106_; uint8_t v___x_107_; 
v___x_106_ = 55296;
v___x_107_ = lean_uint32_dec_le(v___x_106_, v_r_103_);
if (v___x_107_ == 0)
{
v_val_5_ = v_r_103_;
goto v___jp_4_;
}
else
{
uint32_t v___x_108_; uint8_t v___x_109_; 
v___x_108_ = 57343;
v___x_109_ = lean_uint32_dec_le(v_r_103_, v___x_108_);
if (v___x_109_ == 0)
{
v_val_5_ = v_r_103_;
goto v___jp_4_;
}
else
{
lean_object* v___x_110_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_110_ = lean_box(0);
return v___x_110_;
}
}
}
else
{
lean_object* v___x_111_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_111_ = lean_box(0);
return v___x_111_;
}
}
}
}
}
}
else
{
lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_112_ = lean_unsigned_to_nat(1u);
v___x_113_ = lean_nat_add(v_i_2_, v___x_112_);
v___x_114_ = lean_nat_dec_lt(v___x_113_, v___x_11_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
lean_dec(v___x_113_);
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_115_ = lean_box(0);
return v___x_115_;
}
else
{
uint8_t v___x_116_; uint8_t v___x_117_; uint8_t v___x_118_; 
v___x_116_ = lean_byte_array_fget(v_b_1_, v___x_113_);
lean_dec(v___x_113_);
v___x_117_ = lean_uint8_land(v___x_116_, v___x_22_);
v___x_118_ = lean_uint8_dec_eq(v___x_117_, v___x_16_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_119_ = lean_box(0);
return v___x_119_;
}
else
{
uint8_t v___x_120_; uint8_t v_b_u2080_121_; uint8_t v___x_122_; uint8_t v_b_u2081_123_; uint32_t v___x_124_; uint32_t v___x_125_; uint32_t v___x_126_; uint32_t v___x_127_; uint32_t v_r_128_; uint32_t v___x_129_; uint8_t v___x_130_; 
v___x_120_ = 31;
v_b_u2080_121_ = lean_uint8_land(v___x_15_, v___x_120_);
v___x_122_ = 63;
v_b_u2081_123_ = lean_uint8_land(v___x_116_, v___x_122_);
v___x_124_ = lean_uint8_to_uint32(v_b_u2080_121_);
v___x_125_ = 6;
v___x_126_ = lean_uint32_shift_left(v___x_124_, v___x_125_);
v___x_127_ = lean_uint8_to_uint32(v_b_u2081_123_);
v_r_128_ = lean_uint32_lor(v___x_126_, v___x_127_);
v___x_129_ = 128;
v___x_130_ = lean_uint32_dec_lt(v_r_128_, v___x_129_);
if (v___x_130_ == 0)
{
v_val_5_ = v_r_128_;
goto v___jp_4_;
}
else
{
lean_object* v___x_131_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_131_ = lean_box(0);
return v___x_131_;
}
}
}
}
}
else
{
uint32_t v___x_132_; 
v___x_132_ = lean_uint8_to_uint32(v___x_15_);
v_val_5_ = v___x_132_;
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
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go___redArg___boxed(lean_object* v_b_133_, lean_object* v_i_134_, lean_object* v_acc_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_ByteArray_utf8Decode_x3f_go___redArg(v_b_133_, v_i_134_, v_acc_135_);
lean_dec_ref(v_b_133_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go(lean_object* v_b_137_, lean_object* v_i_138_, lean_object* v_acc_139_, lean_object* v_hi_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_ByteArray_utf8Decode_x3f_go___redArg(v_b_137_, v_i_138_, v_acc_139_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go___boxed(lean_object* v_b_142_, lean_object* v_i_143_, lean_object* v_acc_144_, lean_object* v_hi_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_ByteArray_utf8Decode_x3f_go(v_b_142_, v_i_143_, v_acc_144_, v_hi_145_);
lean_dec_ref(v_b_142_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__1_splitter___redArg(lean_object* v_x_147_, lean_object* v_h__1_148_, lean_object* v_h__2_149_){
_start:
{
if (lean_obj_tag(v_x_147_) == 0)
{
lean_object* v___x_150_; 
lean_dec(v_h__2_149_);
v___x_150_ = lean_apply_1(v_h__1_148_, lean_box(0));
return v___x_150_;
}
else
{
lean_object* v_val_151_; lean_object* v___x_152_; 
lean_dec(v_h__1_148_);
v_val_151_ = lean_ctor_get(v_x_147_, 0);
lean_inc(v_val_151_);
lean_dec_ref_known(v_x_147_, 1);
v___x_152_ = lean_apply_2(v_h__2_149_, v_val_151_, lean_box(0));
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__1_splitter(lean_object* v_motive_153_, lean_object* v_x_154_, lean_object* v_h__1_155_, lean_object* v_h__2_156_){
_start:
{
if (lean_obj_tag(v_x_154_) == 0)
{
lean_object* v___x_157_; 
lean_dec(v_h__2_156_);
v___x_157_ = lean_apply_1(v_h__1_155_, lean_box(0));
return v___x_157_;
}
else
{
lean_object* v_val_158_; lean_object* v___x_159_; 
lean_dec(v_h__1_155_);
v_val_158_ = lean_ctor_get(v_x_154_, 0);
lean_inc(v_val_158_);
lean_dec_ref_known(v_x_154_, 1);
v___x_159_ = lean_apply_2(v_h__2_156_, v_val_158_, lean_box(0));
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f(lean_object* v_b_162_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = lean_unsigned_to_nat(0u);
v___x_164_ = ((lean_object*)(l_ByteArray_utf8Decode_x3f___closed__0));
v___x_165_ = l_ByteArray_utf8Decode_x3f_go___redArg(v_b_162_, v___x_163_, v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f___boxed(lean_object* v_b_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_ByteArray_utf8Decode_x3f(v_b_166_);
lean_dec_ref(v_b_166_);
return v_res_167_;
}
}
uint8_t l_ByteArray_validateUTF8_go___redArg(lean_object* v_b_168_, lean_object* v_i_169_){
_start:
{
lean_object* v___y_171_; uint8_t v___y_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = lean_byte_array_size(v_b_168_);
v___x_194_ = lean_nat_dec_lt(v_i_169_, v___x_193_);
if (v___x_194_ == 0)
{
uint8_t v___x_195_; 
lean_dec(v_i_169_);
v___x_195_ = 1;
return v___x_195_;
}
else
{
if (v___x_194_ == 0)
{
lean_dec(v_i_169_);
return v___x_194_;
}
else
{
uint8_t v___x_196_; uint8_t v___x_197_; uint8_t v___x_198_; uint8_t v___x_199_; uint8_t v___x_200_; 
v___x_196_ = lean_byte_array_fget(v_b_168_, v_i_169_);
v___x_197_ = 128;
v___x_198_ = lean_uint8_land(v___x_196_, v___x_197_);
v___x_199_ = 0;
v___x_200_ = lean_uint8_dec_eq(v___x_198_, v___x_199_);
if (v___x_200_ == 0)
{
uint8_t v___x_201_; uint8_t v___x_202_; uint8_t v___x_203_; uint8_t v___x_204_; 
v___x_201_ = 224;
v___x_202_ = lean_uint8_land(v___x_196_, v___x_201_);
v___x_203_ = 192;
v___x_204_ = lean_uint8_dec_eq(v___x_202_, v___x_203_);
if (v___x_204_ == 0)
{
uint8_t v___x_205_; uint8_t v___x_206_; uint8_t v___x_207_; 
v___x_205_ = 240;
v___x_206_ = lean_uint8_land(v___x_196_, v___x_205_);
v___x_207_ = lean_uint8_dec_eq(v___x_206_, v___x_201_);
if (v___x_207_ == 0)
{
uint8_t v___x_208_; uint8_t v___x_209_; uint8_t v___x_210_; 
v___x_208_ = 248;
v___x_209_ = lean_uint8_land(v___x_196_, v___x_208_);
v___x_210_ = lean_uint8_dec_eq(v___x_209_, v___x_205_);
if (v___x_210_ == 0)
{
lean_dec(v_i_169_);
return v___x_210_;
}
else
{
lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_211_ = lean_unsigned_to_nat(3u);
v___x_212_ = lean_nat_add(v_i_169_, v___x_211_);
v___x_213_ = lean_nat_dec_lt(v___x_212_, v___x_193_);
if (v___x_213_ == 0)
{
lean_dec(v___x_212_);
lean_dec(v_i_169_);
return v___x_213_;
}
else
{
lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; uint8_t v___x_217_; uint8_t v___x_218_; 
v___x_214_ = lean_unsigned_to_nat(1u);
v___x_215_ = lean_nat_add(v_i_169_, v___x_214_);
v___x_216_ = lean_byte_array_fget(v_b_168_, v___x_215_);
lean_dec(v___x_215_);
v___x_217_ = lean_uint8_land(v___x_216_, v___x_203_);
v___x_218_ = lean_uint8_dec_eq(v___x_217_, v___x_197_);
if (v___x_218_ == 0)
{
lean_dec(v___x_212_);
lean_dec(v_i_169_);
return v___x_218_;
}
else
{
lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; uint8_t v___x_222_; uint8_t v___x_223_; 
v___x_219_ = lean_unsigned_to_nat(2u);
v___x_220_ = lean_nat_add(v_i_169_, v___x_219_);
v___x_221_ = lean_byte_array_fget(v_b_168_, v___x_220_);
lean_dec(v___x_220_);
v___x_222_ = lean_uint8_land(v___x_221_, v___x_203_);
v___x_223_ = lean_uint8_dec_eq(v___x_222_, v___x_197_);
if (v___x_223_ == 0)
{
lean_dec(v___x_212_);
lean_dec(v_i_169_);
return v___x_207_;
}
else
{
uint8_t v___x_224_; uint8_t v___x_225_; uint8_t v___x_226_; 
v___x_224_ = lean_byte_array_fget(v_b_168_, v___x_212_);
lean_dec(v___x_212_);
v___x_225_ = lean_uint8_land(v___x_224_, v___x_203_);
v___x_226_ = lean_uint8_dec_eq(v___x_225_, v___x_197_);
if (v___x_226_ == 0)
{
lean_dec(v_i_169_);
return v___x_207_;
}
else
{
uint8_t v___x_227_; uint8_t v_b_u2080_228_; uint8_t v___x_229_; uint8_t v_b_u2081_230_; uint8_t v_b_u2082_231_; uint8_t v_b_u2083_232_; uint32_t v___x_233_; uint32_t v___x_234_; uint32_t v___x_235_; uint32_t v___x_236_; uint32_t v___x_237_; uint32_t v___x_238_; uint32_t v___x_239_; uint32_t v___x_240_; uint32_t v___x_241_; uint32_t v___x_242_; uint32_t v___x_243_; uint32_t v___x_244_; uint32_t v_r_245_; uint32_t v___x_246_; uint8_t v___x_247_; 
v___x_227_ = 7;
v_b_u2080_228_ = lean_uint8_land(v___x_196_, v___x_227_);
v___x_229_ = 63;
v_b_u2081_230_ = lean_uint8_land(v___x_216_, v___x_229_);
v_b_u2082_231_ = lean_uint8_land(v___x_221_, v___x_229_);
v_b_u2083_232_ = lean_uint8_land(v___x_224_, v___x_229_);
v___x_233_ = lean_uint8_to_uint32(v_b_u2080_228_);
v___x_234_ = 18;
v___x_235_ = lean_uint32_shift_left(v___x_233_, v___x_234_);
v___x_236_ = lean_uint8_to_uint32(v_b_u2081_230_);
v___x_237_ = 12;
v___x_238_ = lean_uint32_shift_left(v___x_236_, v___x_237_);
v___x_239_ = lean_uint32_lor(v___x_235_, v___x_238_);
v___x_240_ = lean_uint8_to_uint32(v_b_u2082_231_);
v___x_241_ = 6;
v___x_242_ = lean_uint32_shift_left(v___x_240_, v___x_241_);
v___x_243_ = lean_uint32_lor(v___x_239_, v___x_242_);
v___x_244_ = lean_uint8_to_uint32(v_b_u2083_232_);
v_r_245_ = lean_uint32_lor(v___x_243_, v___x_244_);
v___x_246_ = 65536;
v___x_247_ = lean_uint32_dec_le(v___x_246_, v_r_245_);
if (v___x_247_ == 0)
{
lean_dec(v_i_169_);
return v___x_207_;
}
else
{
uint32_t v___x_248_; uint8_t v___x_249_; 
v___x_248_ = 1114111;
v___x_249_ = lean_uint32_dec_le(v_r_245_, v___x_248_);
v___y_192_ = v___x_249_;
goto v___jp_191_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_250_ = lean_unsigned_to_nat(2u);
v___x_251_ = lean_nat_add(v_i_169_, v___x_250_);
v___x_252_ = lean_nat_dec_lt(v___x_251_, v___x_193_);
if (v___x_252_ == 0)
{
lean_dec(v___x_251_);
lean_dec(v_i_169_);
return v___x_252_;
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; uint8_t v___x_256_; uint8_t v___x_257_; 
v___x_253_ = lean_unsigned_to_nat(1u);
v___x_254_ = lean_nat_add(v_i_169_, v___x_253_);
v___x_255_ = lean_byte_array_fget(v_b_168_, v___x_254_);
lean_dec(v___x_254_);
v___x_256_ = lean_uint8_land(v___x_255_, v___x_203_);
v___x_257_ = lean_uint8_dec_eq(v___x_256_, v___x_197_);
if (v___x_257_ == 0)
{
lean_dec(v___x_251_);
lean_dec(v_i_169_);
return v___x_257_;
}
else
{
uint8_t v___x_258_; uint8_t v___x_259_; uint8_t v___x_260_; 
v___x_258_ = lean_byte_array_fget(v_b_168_, v___x_251_);
lean_dec(v___x_251_);
v___x_259_ = lean_uint8_land(v___x_258_, v___x_203_);
v___x_260_ = lean_uint8_dec_eq(v___x_259_, v___x_197_);
if (v___x_260_ == 0)
{
lean_dec(v_i_169_);
return v___x_204_;
}
else
{
uint8_t v___x_261_; uint8_t v_b_u2080_262_; uint8_t v___x_263_; uint8_t v_b_u2081_264_; uint8_t v_b_u2082_265_; uint32_t v___x_266_; uint32_t v___x_267_; uint32_t v___x_268_; uint32_t v___x_269_; uint32_t v___x_270_; uint32_t v___x_271_; uint32_t v___x_272_; uint32_t v___x_273_; uint32_t v_r_274_; uint32_t v___x_275_; uint8_t v___x_276_; 
v___x_261_ = 15;
v_b_u2080_262_ = lean_uint8_land(v___x_196_, v___x_261_);
v___x_263_ = 63;
v_b_u2081_264_ = lean_uint8_land(v___x_255_, v___x_263_);
v_b_u2082_265_ = lean_uint8_land(v___x_258_, v___x_263_);
v___x_266_ = lean_uint8_to_uint32(v_b_u2080_262_);
v___x_267_ = 12;
v___x_268_ = lean_uint32_shift_left(v___x_266_, v___x_267_);
v___x_269_ = lean_uint8_to_uint32(v_b_u2081_264_);
v___x_270_ = 6;
v___x_271_ = lean_uint32_shift_left(v___x_269_, v___x_270_);
v___x_272_ = lean_uint32_lor(v___x_268_, v___x_271_);
v___x_273_ = lean_uint8_to_uint32(v_b_u2082_265_);
v_r_274_ = lean_uint32_lor(v___x_272_, v___x_273_);
v___x_275_ = 2048;
v___x_276_ = lean_uint32_dec_le(v___x_275_, v_r_274_);
if (v___x_276_ == 0)
{
lean_dec(v_i_169_);
return v___x_204_;
}
else
{
uint32_t v___x_277_; uint8_t v___x_278_; 
v___x_277_ = 55296;
v___x_278_ = lean_uint32_dec_lt(v_r_274_, v___x_277_);
if (v___x_278_ == 0)
{
uint32_t v___x_279_; uint8_t v___x_280_; 
v___x_279_ = 57343;
v___x_280_ = lean_uint32_dec_lt(v___x_279_, v_r_274_);
v___y_192_ = v___x_280_;
goto v___jp_191_;
}
else
{
goto v___jp_174_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_281_ = lean_unsigned_to_nat(1u);
v___x_282_ = lean_nat_add(v_i_169_, v___x_281_);
v___x_283_ = lean_nat_dec_lt(v___x_282_, v___x_193_);
if (v___x_283_ == 0)
{
lean_dec(v___x_282_);
lean_dec(v_i_169_);
return v___x_283_;
}
else
{
uint8_t v___x_284_; uint8_t v___x_285_; uint8_t v___x_286_; 
v___x_284_ = lean_byte_array_fget(v_b_168_, v___x_282_);
lean_dec(v___x_282_);
v___x_285_ = lean_uint8_land(v___x_284_, v___x_203_);
v___x_286_ = lean_uint8_dec_eq(v___x_285_, v___x_197_);
if (v___x_286_ == 0)
{
lean_dec(v_i_169_);
return v___x_286_;
}
else
{
uint8_t v___x_287_; uint8_t v_b_u2080_288_; uint8_t v___x_289_; uint8_t v_b_u2081_290_; uint32_t v___x_291_; uint32_t v___x_292_; uint32_t v___x_293_; uint32_t v___x_294_; uint32_t v_r_295_; uint32_t v___x_296_; uint8_t v___x_297_; 
v___x_287_ = 31;
v_b_u2080_288_ = lean_uint8_land(v___x_196_, v___x_287_);
v___x_289_ = 63;
v_b_u2081_290_ = lean_uint8_land(v___x_284_, v___x_289_);
v___x_291_ = lean_uint8_to_uint32(v_b_u2080_288_);
v___x_292_ = 6;
v___x_293_ = lean_uint32_shift_left(v___x_291_, v___x_292_);
v___x_294_ = lean_uint8_to_uint32(v_b_u2081_290_);
v_r_295_ = lean_uint32_lor(v___x_293_, v___x_294_);
v___x_296_ = 128;
v___x_297_ = lean_uint32_dec_le(v___x_296_, v_r_295_);
v___y_192_ = v___x_297_;
goto v___jp_191_;
}
}
}
}
else
{
goto v___jp_174_;
}
}
}
v___jp_170_:
{
lean_object* v___x_172_; 
v___x_172_ = lean_nat_add(v_i_169_, v___y_171_);
lean_dec(v_i_169_);
v_i_169_ = v___x_172_;
goto _start;
}
v___jp_174_:
{
uint8_t v___x_175_; uint8_t v___x_176_; uint8_t v___x_177_; uint8_t v___x_178_; uint8_t v___x_179_; 
v___x_175_ = lean_byte_array_fget(v_b_168_, v_i_169_);
v___x_176_ = 128;
v___x_177_ = lean_uint8_land(v___x_175_, v___x_176_);
v___x_178_ = 0;
v___x_179_ = lean_uint8_dec_eq(v___x_177_, v___x_178_);
if (v___x_179_ == 0)
{
uint8_t v___x_180_; uint8_t v___x_181_; uint8_t v___x_182_; uint8_t v___x_183_; 
v___x_180_ = 224;
v___x_181_ = lean_uint8_land(v___x_175_, v___x_180_);
v___x_182_ = 192;
v___x_183_ = lean_uint8_dec_eq(v___x_181_, v___x_182_);
if (v___x_183_ == 0)
{
uint8_t v___x_184_; uint8_t v___x_185_; uint8_t v___x_186_; 
v___x_184_ = 240;
v___x_185_ = lean_uint8_land(v___x_175_, v___x_184_);
v___x_186_ = lean_uint8_dec_eq(v___x_185_, v___x_180_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; 
v___x_187_ = lean_unsigned_to_nat(4u);
v___y_171_ = v___x_187_;
goto v___jp_170_;
}
else
{
lean_object* v___x_188_; 
v___x_188_ = lean_unsigned_to_nat(3u);
v___y_171_ = v___x_188_;
goto v___jp_170_;
}
}
else
{
lean_object* v___x_189_; 
v___x_189_ = lean_unsigned_to_nat(2u);
v___y_171_ = v___x_189_;
goto v___jp_170_;
}
}
else
{
lean_object* v___x_190_; 
v___x_190_ = lean_unsigned_to_nat(1u);
v___y_171_ = v___x_190_;
goto v___jp_170_;
}
}
v___jp_191_:
{
if (v___y_192_ == 0)
{
lean_dec(v_i_169_);
return v___y_192_;
}
else
{
goto v___jp_174_;
}
}
}
}
LEAN_EXPORT void l_ByteArray_validateUTF8_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_b_168_ = stack[0].m_obj;
lean_object* v_i_169_ = stack[1].m_obj;
uint8_t v_res_298_;
v_res_298_ = l_ByteArray_validateUTF8_go___redArg(v_b_168_, v_i_169_);
stack->m_num = v_res_298_;
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___redArg___boxed(lean_object* v_b_299_, lean_object* v_i_300_){
_start:
{
uint8_t v_res_301_; lean_object* v_r_302_; 
v_res_301_ = l_ByteArray_validateUTF8_go___redArg(v_b_299_, v_i_300_);
lean_dec_ref(v_b_299_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
uint8_t l_ByteArray_validateUTF8_go(lean_object* v_b_303_, lean_object* v_i_304_, lean_object* v_hi_305_){
_start:
{
uint8_t v___x_306_; 
v___x_306_ = l_ByteArray_validateUTF8_go___redArg(v_b_303_, v_i_304_);
return v___x_306_;
}
}
LEAN_EXPORT void l_ByteArray_validateUTF8_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_b_303_ = stack[0].m_obj;
lean_object* v_i_304_ = stack[1].m_obj;
uint8_t v_res_307_;
v_res_307_ = l_ByteArray_validateUTF8_go(v_b_303_, v_i_304_, lean_box(0));
stack->m_num = v_res_307_;
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___boxed(lean_object* v_b_308_, lean_object* v_i_309_, lean_object* v_hi_310_){
_start:
{
uint8_t v_res_311_; lean_object* v_r_312_; 
v_res_311_ = l_ByteArray_validateUTF8_go(v_b_308_, v_i_309_, v_hi_310_);
lean_dec_ref(v_b_308_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(uint8_t v_x_313_, lean_object* v_h__1_314_, lean_object* v_h__2_315_){
_start:
{
if (v_x_313_ == 0)
{
lean_object* v___x_316_; 
lean_dec(v_h__2_315_);
v___x_316_ = lean_apply_1(v_h__1_314_, lean_box(0));
return v___x_316_;
}
else
{
lean_object* v___x_317_; 
lean_dec(v_h__1_314_);
v___x_317_ = lean_apply_1(v_h__2_315_, lean_box(0));
return v___x_317_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_313_ = stack[0].m_num;
lean_object* v_h__1_314_ = stack[1].m_obj;
lean_object* v_h__2_315_ = stack[2].m_obj;
lean_object* v_res_318_;
v_res_318_ = l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(v_x_313_, v_h__1_314_, v_h__2_315_);
stack->m_obj
 = v_res_318_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg___boxed(lean_object* v_x_319_, lean_object* v_h__1_320_, lean_object* v_h__2_321_){
_start:
{
uint8_t v_x_26__boxed_322_; lean_object* v_res_323_; 
v_x_26__boxed_322_ = lean_unbox(v_x_319_);
v_res_323_ = l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(v_x_26__boxed_322_, v_h__1_320_, v_h__2_321_);
return v_res_323_;
}
}
lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(lean_object* v_motive_324_, uint8_t v_x_325_, lean_object* v_h__1_326_, lean_object* v_h__2_327_){
_start:
{
if (v_x_325_ == 0)
{
lean_object* v___x_328_; 
lean_dec(v_h__2_327_);
v___x_328_ = lean_apply_1(v_h__1_326_, lean_box(0));
return v___x_328_;
}
else
{
lean_object* v___x_329_; 
lean_dec(v_h__1_326_);
v___x_329_ = lean_apply_1(v_h__2_327_, lean_box(0));
return v___x_329_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_325_ = stack[1].m_num;
lean_object* v_h__1_326_ = stack[2].m_obj;
lean_object* v_h__2_327_ = stack[3].m_obj;
lean_object* v_res_330_;
v_res_330_ = l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(lean_box(0), v_x_325_, v_h__1_326_, v_h__2_327_);
stack->m_obj
 = v_res_330_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___boxed(lean_object* v_motive_331_, lean_object* v_x_332_, lean_object* v_h__1_333_, lean_object* v_h__2_334_){
_start:
{
uint8_t v_x_37__boxed_335_; lean_object* v_res_336_; 
v_x_37__boxed_335_ = lean_unbox(v_x_332_);
v_res_336_ = l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(v_motive_331_, v_x_37__boxed_335_, v_h__1_333_, v_h__2_334_);
return v_res_336_;
}
}
LEAN_EXPORT void l_ByteArray_validateUTF8_0interp(lean_interpreter_value* stack)
{
lean_object* v_b_337_ = stack[0].m_obj;
uint8_t v_res_338_;
v_res_338_ = lean_string_validate_utf8(v_b_337_);
stack->m_num = v_res_338_;
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8___boxed(lean_object* v_b_339_){
_start:
{
uint8_t v_res_340_; lean_object* v_r_341_; 
v_res_340_ = lean_string_validate_utf8(v_b_339_);
lean_dec_ref(v_b_339_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
uint8_t l_instDecidableIsValidUTF8(lean_object* v_b_342_){
_start:
{
uint8_t v___x_343_; 
v___x_343_ = lean_string_validate_utf8(v_b_342_);
return v___x_343_;
}
}
LEAN_EXPORT void l_instDecidableIsValidUTF8_0interp(lean_interpreter_value* stack)
{
lean_object* v_b_342_ = stack[0].m_obj;
uint8_t v_res_344_;
v_res_344_ = l_instDecidableIsValidUTF8(v_b_342_);
stack->m_num = v_res_344_;
}
LEAN_EXPORT lean_object* l_instDecidableIsValidUTF8___boxed(lean_object* v_b_345_){
_start:
{
uint8_t v_res_346_; lean_object* v_r_347_; 
v_res_346_ = l_instDecidableIsValidUTF8(v_b_345_);
lean_dec_ref(v_b_345_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_x3f(lean_object* v_a_348_){
_start:
{
uint8_t v___x_349_; 
v___x_349_ = lean_string_validate_utf8(v_a_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; 
lean_dec_ref(v_a_348_);
v___x_350_ = lean_box(0);
return v___x_350_;
}
else
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_string_from_utf8_unchecked(v_a_348_);
v___x_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
return v___x_352_;
}
}
}
static lean_object* _init_l_String_fromUTF8_x21___closed__4(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_357_ = ((lean_object*)(l_String_fromUTF8_x21___closed__3));
v___x_358_ = lean_unsigned_to_nat(46u);
v___x_359_ = lean_unsigned_to_nat(193u);
v___x_360_ = ((lean_object*)(l_String_fromUTF8_x21___closed__2));
v___x_361_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_362_ = l_mkPanicMessageWithDecl(v___x_361_, v___x_360_, v___x_359_, v___x_358_, v___x_357_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_x21(lean_object* v_a_363_){
_start:
{
uint8_t v___x_364_; 
v___x_364_ = lean_string_validate_utf8(v_a_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
lean_dec_ref(v_a_363_);
v___x_365_ = ((lean_object*)(l_String_fromUTF8_x21___closed__0));
v___x_366_ = lean_obj_once(&l_String_fromUTF8_x21___closed__4, &l_String_fromUTF8_x21___closed__4_once, _init_l_String_fromUTF8_x21___closed__4);
v___x_367_ = l_panic___redArg(v___x_365_, v___x_366_);
return v___x_367_;
}
else
{
lean_object* v___x_368_; 
v___x_368_ = lean_string_from_utf8_unchecked(v_a_363_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l_String_Internal_toArray(lean_object* v_b_369_){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v_val_374_; 
v___x_370_ = lean_string_to_utf8(v_b_369_);
v___x_371_ = lean_unsigned_to_nat(0u);
v___x_372_ = ((lean_object*)(l_ByteArray_utf8Decode_x3f___closed__0));
v___x_373_ = l_ByteArray_utf8Decode_x3f_go___redArg(v___x_370_, v___x_371_, v___x_372_);
lean_dec_ref(v___x_370_);
v_val_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_val_374_);
lean_dec(v___x_373_);
return v_val_374_;
}
}
static lean_object* _init_l_String_instLT(void){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = lean_box(0);
return v___x_375_;
}
}
LEAN_EXPORT void l_String_decidableLT_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_u2081_376_ = stack[0].m_obj;
lean_object* v_s_u2082_377_ = stack[1].m_obj;
uint8_t v_res_378_;
v_res_378_ = lean_string_dec_lt(v_s_u2081_376_, v_s_u2082_377_);
stack->m_num = v_res_378_;
}
LEAN_EXPORT lean_object* l_String_decidableLT___boxed(lean_object* v_s_u2081_379_, lean_object* v_s_u2082_380_){
_start:
{
uint8_t v_res_381_; lean_object* v_r_382_; 
v_res_381_ = lean_string_dec_lt(v_s_u2081_379_, v_s_u2082_380_);
lean_dec_ref(v_s_u2082_380_);
lean_dec_ref(v_s_u2081_379_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
static lean_object* _init_l_String_instLE(void){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = lean_box(0);
return v___x_383_;
}
}
uint8_t l_String_decLE(lean_object* v_s_u2081_384_, lean_object* v_s_u2082_385_){
_start:
{
uint8_t v___x_386_; 
v___x_386_ = lean_string_dec_lt(v_s_u2082_385_, v_s_u2081_384_);
if (v___x_386_ == 0)
{
uint8_t v___x_387_; 
v___x_387_ = 1;
return v___x_387_;
}
else
{
uint8_t v___x_388_; 
v___x_388_ = 0;
return v___x_388_;
}
}
}
LEAN_EXPORT void l_String_decLE_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_u2081_384_ = stack[0].m_obj;
lean_object* v_s_u2082_385_ = stack[1].m_obj;
uint8_t v_res_389_;
v_res_389_ = l_String_decLE(v_s_u2081_384_, v_s_u2082_385_);
stack->m_num = v_res_389_;
}
LEAN_EXPORT lean_object* l_String_decLE___boxed(lean_object* v_s_u2081_390_, lean_object* v_s_u2082_391_){
_start:
{
uint8_t v_res_392_; lean_object* v_r_393_; 
v_res_392_ = l_String_decLE(v_s_u2081_390_, v_s_u2082_391_);
lean_dec_ref(v_s_u2082_391_);
lean_dec_ref(v_s_u2081_390_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
LEAN_EXPORT void l_String_Pos_Raw_isValid_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_394_ = stack[0].m_obj;
lean_object* v_p_395_ = stack[1].m_obj;
uint8_t v_res_396_;
v_res_396_ = lean_string_is_valid_pos(v_s_394_, v_p_395_);
stack->m_num = v_res_396_;
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValid___boxed(lean_object* v_s_397_, lean_object* v_p_398_){
_start:
{
uint8_t v_res_399_; lean_object* v_r_400_; 
v_res_399_ = lean_string_is_valid_pos(v_s_397_, v_p_398_);
lean_dec(v_p_398_);
lean_dec_ref(v_s_397_);
v_r_400_ = lean_box(v_res_399_);
return v_r_400_;
}
}
uint8_t l_String_instDecidableIsValid(lean_object* v_s_401_, lean_object* v_p_402_){
_start:
{
uint8_t v___x_403_; 
v___x_403_ = lean_string_is_valid_pos(v_s_401_, v_p_402_);
return v___x_403_;
}
}
LEAN_EXPORT void l_String_instDecidableIsValid_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_401_ = stack[0].m_obj;
lean_object* v_p_402_ = stack[1].m_obj;
uint8_t v_res_404_;
v_res_404_ = l_String_instDecidableIsValid(v_s_401_, v_p_402_);
stack->m_num = v_res_404_;
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
LEAN_EXPORT void l_String_extract_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_409_ = stack[0].m_obj;
lean_object* v_b_410_ = stack[1].m_obj;
lean_object* v_e_411_ = stack[2].m_obj;
lean_object* v_res_412_;
v_res_412_ = lean_string_utf8_extract_fast(v_s_409_, v_b_410_, v_e_411_);
stack->m_obj
 = v_res_412_;
}
LEAN_EXPORT lean_object* l_String_extract___boxed(lean_object* v_s_413_, lean_object* v_b_414_, lean_object* v_e_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = lean_string_utf8_extract_fast(v_s_413_, v_b_414_, v_e_415_);
lean_dec(v_e_415_);
lean_dec(v_b_414_);
lean_dec_ref(v_s_413_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_extract(lean_object* v_s_417_, lean_object* v_b_418_, lean_object* v_e_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = lean_string_utf8_extract_fast(v_s_417_, v_b_418_, v_e_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_extract___boxed(lean_object* v_s_421_, lean_object* v_b_422_, lean_object* v_e_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_String_Pos_extract(v_s_421_, v_b_422_, v_e_423_);
lean_dec(v_e_423_);
lean_dec(v_b_422_);
lean_dec_ref(v_s_421_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_copy(lean_object* v_s_425_){
_start:
{
lean_object* v_str_426_; lean_object* v_startInclusive_427_; lean_object* v_endExclusive_428_; lean_object* v___x_429_; 
v_str_426_ = lean_ctor_get(v_s_425_, 0);
v_startInclusive_427_ = lean_ctor_get(v_s_425_, 1);
v_endExclusive_428_ = lean_ctor_get(v_s_425_, 2);
v___x_429_ = lean_string_utf8_extract_fast(v_str_426_, v_startInclusive_427_, v_endExclusive_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_copy___boxed(lean_object* v_s_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_String_Slice_copy(v_s_430_);
lean_dec_ref(v_s_430_);
return v_res_431_;
}
}
uint8_t l_String_Pos_Raw_isValidForSlice(lean_object* v_s_432_, lean_object* v_p_433_){
_start:
{
lean_object* v_str_434_; lean_object* v_startInclusive_435_; lean_object* v_endExclusive_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v_str_434_ = lean_ctor_get(v_s_432_, 0);
v_startInclusive_435_ = lean_ctor_get(v_s_432_, 1);
v_endExclusive_436_ = lean_ctor_get(v_s_432_, 2);
v___x_437_ = lean_nat_sub(v_endExclusive_436_, v_startInclusive_435_);
v___x_438_ = lean_unsigned_to_nat(1u);
v___x_439_ = lean_nat_add(v_p_433_, v___x_438_);
v___x_440_ = lean_nat_dec_le(v___x_439_, v___x_437_);
lean_dec(v___x_439_);
if (v___x_440_ == 0)
{
uint8_t v_decide_441_; 
v_decide_441_ = lean_nat_dec_eq(v_p_433_, v___x_437_);
lean_dec(v___x_437_);
return v_decide_441_;
}
else
{
lean_object* v___x_442_; uint8_t v___x_443_; uint8_t v___x_444_; uint8_t v___x_445_; uint8_t v___x_446_; uint8_t v___x_447_; 
lean_dec(v___x_437_);
v___x_442_ = lean_nat_add(v_startInclusive_435_, v_p_433_);
v___x_443_ = lean_string_get_byte_fast(v_str_434_, v___x_442_);
v___x_444_ = 128;
v___x_445_ = lean_uint8_land(v___x_443_, v___x_444_);
v___x_446_ = 0;
v___x_447_ = lean_uint8_dec_eq(v___x_445_, v___x_446_);
if (v___x_447_ == 0)
{
uint8_t v___x_448_; uint8_t v___x_449_; uint8_t v___x_450_; uint8_t v___x_451_; 
v___x_448_ = 224;
v___x_449_ = lean_uint8_land(v___x_443_, v___x_448_);
v___x_450_ = 192;
v___x_451_ = lean_uint8_dec_eq(v___x_449_, v___x_450_);
if (v___x_451_ == 0)
{
uint8_t v___x_452_; uint8_t v___x_453_; uint8_t v___x_454_; 
v___x_452_ = 240;
v___x_453_ = lean_uint8_land(v___x_443_, v___x_452_);
v___x_454_ = lean_uint8_dec_eq(v___x_453_, v___x_448_);
if (v___x_454_ == 0)
{
uint8_t v___x_455_; uint8_t v___x_456_; uint8_t v___x_457_; 
v___x_455_ = 248;
v___x_456_ = lean_uint8_land(v___x_443_, v___x_455_);
v___x_457_ = lean_uint8_dec_eq(v___x_456_, v___x_452_);
return v___x_457_;
}
else
{
return v___x_454_;
}
}
else
{
return v___x_451_;
}
}
else
{
return v___x_447_;
}
}
}
}
LEAN_EXPORT void l_String_Pos_Raw_isValidForSlice_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_432_ = stack[0].m_obj;
lean_object* v_p_433_ = stack[1].m_obj;
uint8_t v_res_458_;
v_res_458_ = l_String_Pos_Raw_isValidForSlice(v_s_432_, v_p_433_);
stack->m_num = v_res_458_;
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValidForSlice___boxed(lean_object* v_s_459_, lean_object* v_p_460_){
_start:
{
uint8_t v_res_461_; lean_object* v_r_462_; 
v_res_461_ = l_String_Pos_Raw_isValidForSlice(v_s_459_, v_p_460_);
lean_dec(v_p_460_);
lean_dec_ref(v_s_459_);
v_r_462_ = lean_box(v_res_461_);
return v_r_462_;
}
}
uint8_t l_String_instDecidableIsValidForSlice(lean_object* v_s_463_, lean_object* v_p_464_){
_start:
{
uint8_t v___x_465_; 
v___x_465_ = l_String_Pos_Raw_isValidForSlice(v_s_463_, v_p_464_);
return v___x_465_;
}
}
LEAN_EXPORT void l_String_instDecidableIsValidForSlice_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_463_ = stack[0].m_obj;
lean_object* v_p_464_ = stack[1].m_obj;
uint8_t v_res_466_;
v_res_466_ = l_String_instDecidableIsValidForSlice(v_s_463_, v_p_464_);
stack->m_num = v_res_466_;
}
LEAN_EXPORT lean_object* l_String_instDecidableIsValidForSlice___boxed(lean_object* v_s_467_, lean_object* v_p_468_){
_start:
{
uint8_t v_res_469_; lean_object* v_r_470_; 
v_res_469_ = l_String_instDecidableIsValidForSlice(v_s_467_, v_p_468_);
lean_dec(v_p_468_);
lean_dec_ref(v_s_467_);
v_r_470_ = lean_box(v_res_469_);
return v_r_470_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str(lean_object* v_s_471_, lean_object* v_pos_472_){
_start:
{
lean_object* v_startInclusive_473_; lean_object* v___x_474_; 
v_startInclusive_473_ = lean_ctor_get(v_s_471_, 1);
v___x_474_ = lean_nat_add(v_startInclusive_473_, v_pos_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str___boxed(lean_object* v_s_475_, lean_object* v_pos_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_String_Slice_Pos_str(v_s_475_, v_pos_476_);
lean_dec(v_pos_476_);
lean_dec_ref(v_s_475_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg(lean_object* v_s_478_, lean_object* v_pos_479_){
_start:
{
lean_object* v_startInclusive_480_; lean_object* v___x_481_; 
v_startInclusive_480_ = lean_ctor_get(v_s_478_, 1);
v___x_481_ = lean_nat_sub(v_pos_479_, v_startInclusive_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg___boxed(lean_object* v_s_482_, lean_object* v_pos_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_String_Slice_Pos_ofStr___redArg(v_s_482_, v_pos_483_);
lean_dec(v_pos_483_);
lean_dec_ref(v_s_482_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr(lean_object* v_s_485_, lean_object* v_pos_486_, lean_object* v_h_u2081_487_, lean_object* v_h_u2082_488_){
_start:
{
lean_object* v_startInclusive_489_; lean_object* v___x_490_; 
v_startInclusive_489_ = lean_ctor_get(v_s_485_, 1);
v___x_490_ = lean_nat_sub(v_pos_486_, v_startInclusive_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___boxed(lean_object* v_s_491_, lean_object* v_pos_492_, lean_object* v_h_u2081_493_, lean_object* v_h_u2082_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_String_Slice_Pos_ofStr(v_s_491_, v_pos_492_, v_h_u2081_493_, v_h_u2082_494_);
lean_dec(v_pos_492_);
lean_dec_ref(v_s_491_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom(lean_object* v_s_496_, lean_object* v_pos_497_){
_start:
{
lean_object* v_str_498_; lean_object* v_startInclusive_499_; lean_object* v_endExclusive_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_508_; 
v_str_498_ = lean_ctor_get(v_s_496_, 0);
v_startInclusive_499_ = lean_ctor_get(v_s_496_, 1);
v_endExclusive_500_ = lean_ctor_get(v_s_496_, 2);
v_isSharedCheck_508_ = !lean_is_exclusive(v_s_496_);
if (v_isSharedCheck_508_ == 0)
{
v___x_502_ = v_s_496_;
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_endExclusive_500_);
lean_inc(v_startInclusive_499_);
lean_inc(v_str_498_);
lean_dec(v_s_496_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_504_ = lean_nat_add(v_startInclusive_499_, v_pos_497_);
lean_dec(v_startInclusive_499_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 1, v___x_504_);
v___x_506_ = v___x_502_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_str_498_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_507_, 2, v_endExclusive_500_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom___boxed(lean_object* v_s_509_, lean_object* v_pos_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_String_Slice_sliceFrom(v_s_509_, v_pos_510_);
lean_dec(v_pos_510_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStart(lean_object* v_s_512_, lean_object* v_pos_513_){
_start:
{
lean_object* v_str_514_; lean_object* v_startInclusive_515_; lean_object* v_endExclusive_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_524_; 
v_str_514_ = lean_ctor_get(v_s_512_, 0);
v_startInclusive_515_ = lean_ctor_get(v_s_512_, 1);
v_endExclusive_516_ = lean_ctor_get(v_s_512_, 2);
v_isSharedCheck_524_ = !lean_is_exclusive(v_s_512_);
if (v_isSharedCheck_524_ == 0)
{
v___x_518_ = v_s_512_;
v_isShared_519_ = v_isSharedCheck_524_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_endExclusive_516_);
lean_inc(v_startInclusive_515_);
lean_inc(v_str_514_);
lean_dec(v_s_512_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_524_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_520_ = lean_nat_add(v_startInclusive_515_, v_pos_513_);
lean_dec(v_startInclusive_515_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 1, v___x_520_);
v___x_522_ = v___x_518_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_str_514_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v_endExclusive_516_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStart___boxed(lean_object* v_s_525_, lean_object* v_pos_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_String_Slice_replaceStart(v_s_525_, v_pos_526_);
lean_dec(v_pos_526_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceTo(lean_object* v_s_528_, lean_object* v_pos_529_){
_start:
{
lean_object* v_str_530_; lean_object* v_startInclusive_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_539_; 
v_str_530_ = lean_ctor_get(v_s_528_, 0);
v_startInclusive_531_ = lean_ctor_get(v_s_528_, 1);
v_isSharedCheck_539_ = !lean_is_exclusive(v_s_528_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; 
v_unused_540_ = lean_ctor_get(v_s_528_, 2);
lean_dec(v_unused_540_);
v___x_533_ = v_s_528_;
v_isShared_534_ = v_isSharedCheck_539_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_startInclusive_531_);
lean_inc(v_str_530_);
lean_dec(v_s_528_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_539_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_535_ = lean_nat_add(v_startInclusive_531_, v_pos_529_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 2, v___x_535_);
v___x_537_ = v___x_533_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_str_530_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_startInclusive_531_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceTo___boxed(lean_object* v_s_541_, lean_object* v_pos_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_String_Slice_sliceTo(v_s_541_, v_pos_542_);
lean_dec(v_pos_542_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd(lean_object* v_s_544_, lean_object* v_pos_545_){
_start:
{
lean_object* v_str_546_; lean_object* v_startInclusive_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_555_; 
v_str_546_ = lean_ctor_get(v_s_544_, 0);
v_startInclusive_547_ = lean_ctor_get(v_s_544_, 1);
v_isSharedCheck_555_ = !lean_is_exclusive(v_s_544_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; 
v_unused_556_ = lean_ctor_get(v_s_544_, 2);
lean_dec(v_unused_556_);
v___x_549_ = v_s_544_;
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_startInclusive_547_);
lean_inc(v_str_546_);
lean_dec(v_s_544_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = lean_nat_add(v_startInclusive_547_, v_pos_545_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 2, v___x_551_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_str_546_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_startInclusive_547_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd___boxed(lean_object* v_s_557_, lean_object* v_pos_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_String_Slice_replaceEnd(v_s_557_, v_pos_558_);
lean_dec(v_pos_558_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg(lean_object* v_s_560_, lean_object* v_newStart_561_, lean_object* v_newEnd_562_){
_start:
{
lean_object* v_str_563_; lean_object* v_startInclusive_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_573_; 
v_str_563_ = lean_ctor_get(v_s_560_, 0);
v_startInclusive_564_ = lean_ctor_get(v_s_560_, 1);
v_isSharedCheck_573_ = !lean_is_exclusive(v_s_560_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; 
v_unused_574_ = lean_ctor_get(v_s_560_, 2);
lean_dec(v_unused_574_);
v___x_566_ = v_s_560_;
v_isShared_567_ = v_isSharedCheck_573_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_startInclusive_564_);
lean_inc(v_str_563_);
lean_dec(v_s_560_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_573_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_568_ = lean_nat_add(v_startInclusive_564_, v_newStart_561_);
v___x_569_ = lean_nat_add(v_startInclusive_564_, v_newEnd_562_);
lean_dec(v_startInclusive_564_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 2, v___x_569_);
lean_ctor_set(v___x_566_, 1, v___x_568_);
v___x_571_ = v___x_566_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_str_563_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg___boxed(lean_object* v_s_575_, lean_object* v_newStart_576_, lean_object* v_newEnd_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_String_Slice_slice___redArg(v_s_575_, v_newStart_576_, v_newEnd_577_);
lean_dec(v_newEnd_577_);
lean_dec(v_newStart_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice(lean_object* v_s_579_, lean_object* v_newStart_580_, lean_object* v_newEnd_581_, lean_object* v_h_582_){
_start:
{
lean_object* v_str_583_; lean_object* v_startInclusive_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_593_; 
v_str_583_ = lean_ctor_get(v_s_579_, 0);
v_startInclusive_584_ = lean_ctor_get(v_s_579_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v_s_579_);
if (v_isSharedCheck_593_ == 0)
{
lean_object* v_unused_594_; 
v_unused_594_ = lean_ctor_get(v_s_579_, 2);
lean_dec(v_unused_594_);
v___x_586_ = v_s_579_;
v_isShared_587_ = v_isSharedCheck_593_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_startInclusive_584_);
lean_inc(v_str_583_);
lean_dec(v_s_579_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_593_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_588_ = lean_nat_add(v_startInclusive_584_, v_newStart_580_);
v___x_589_ = lean_nat_add(v_startInclusive_584_, v_newEnd_581_);
lean_dec(v_startInclusive_584_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 2, v___x_589_);
lean_ctor_set(v___x_586_, 1, v___x_588_);
v___x_591_ = v___x_586_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_str_583_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_592_, 2, v___x_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___boxed(lean_object* v_s_595_, lean_object* v_newStart_596_, lean_object* v_newEnd_597_, lean_object* v_h_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_String_Slice_slice(v_s_595_, v_newStart_596_, v_newEnd_597_, v_h_598_);
lean_dec(v_newEnd_597_);
lean_dec(v_newStart_596_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg(lean_object* v_s_600_, lean_object* v_newStart_601_, lean_object* v_newEnd_602_){
_start:
{
lean_object* v_str_603_; lean_object* v_startInclusive_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_613_; 
v_str_603_ = lean_ctor_get(v_s_600_, 0);
v_startInclusive_604_ = lean_ctor_get(v_s_600_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v_s_600_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; 
v_unused_614_ = lean_ctor_get(v_s_600_, 2);
lean_dec(v_unused_614_);
v___x_606_ = v_s_600_;
v_isShared_607_ = v_isSharedCheck_613_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_startInclusive_604_);
lean_inc(v_str_603_);
lean_dec(v_s_600_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_613_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_608_ = lean_nat_add(v_startInclusive_604_, v_newStart_601_);
v___x_609_ = lean_nat_add(v_startInclusive_604_, v_newEnd_602_);
lean_dec(v_startInclusive_604_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 2, v___x_609_);
lean_ctor_set(v___x_606_, 1, v___x_608_);
v___x_611_ = v___x_606_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_str_603_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg___boxed(lean_object* v_s_615_, lean_object* v_newStart_616_, lean_object* v_newEnd_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_String_Slice_replaceStartEnd___redArg(v_s_615_, v_newStart_616_, v_newEnd_617_);
lean_dec(v_newEnd_617_);
lean_dec(v_newStart_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd(lean_object* v_s_619_, lean_object* v_newStart_620_, lean_object* v_newEnd_621_, lean_object* v_h_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_String_Slice_replaceStartEnd___redArg(v_s_619_, v_newStart_620_, v_newEnd_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___boxed(lean_object* v_s_624_, lean_object* v_newStart_625_, lean_object* v_newEnd_626_, lean_object* v_h_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_String_Slice_replaceStartEnd(v_s_624_, v_newStart_625_, v_newEnd_626_, v_h_627_);
lean_dec(v_newEnd_626_);
lean_dec(v_newStart_625_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f(lean_object* v_s_629_, lean_object* v_newStart_630_, lean_object* v_newEnd_631_){
_start:
{
uint8_t v___x_632_; 
v___x_632_ = lean_nat_dec_le(v_newStart_630_, v_newEnd_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
lean_dec_ref(v_s_629_);
v___x_633_ = lean_box(0);
return v___x_633_;
}
else
{
lean_object* v_str_634_; lean_object* v_startInclusive_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_645_; 
v_str_634_ = lean_ctor_get(v_s_629_, 0);
v_startInclusive_635_ = lean_ctor_get(v_s_629_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_s_629_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; 
v_unused_646_ = lean_ctor_get(v_s_629_, 2);
lean_dec(v_unused_646_);
v___x_637_ = v_s_629_;
v_isShared_638_ = v_isSharedCheck_645_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_startInclusive_635_);
lean_inc(v_str_634_);
lean_dec(v_s_629_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_645_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
v___x_639_ = lean_nat_add(v_startInclusive_635_, v_newStart_630_);
v___x_640_ = lean_nat_add(v_startInclusive_635_, v_newEnd_631_);
lean_dec(v_startInclusive_635_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 2, v___x_640_);
lean_ctor_set(v___x_637_, 1, v___x_639_);
v___x_642_ = v___x_637_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_str_634_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v___x_640_);
v___x_642_ = v_reuseFailAlloc_644_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_643_; 
v___x_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f___boxed(lean_object* v_s_647_, lean_object* v_newStart_648_, lean_object* v_newEnd_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_String_Slice_slice_x3f(v_s_647_, v_newStart_648_, v_newEnd_649_);
lean_dec(v_newEnd_649_);
lean_dec(v_newStart_648_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_slice_x21_spec__0(lean_object* v_msg_651_){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = l_String_instInhabitedSlice;
v___x_653_ = lean_panic_fn_borrowed(v___x_652_, v_msg_651_);
return v___x_653_;
}
}
static lean_object* _init_l_String_Slice_slice_x21___closed__2(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_656_ = ((lean_object*)(l_String_Slice_slice_x21___closed__1));
v___x_657_ = lean_unsigned_to_nat(4u);
v___x_658_ = lean_unsigned_to_nat(1046u);
v___x_659_ = ((lean_object*)(l_String_Slice_slice_x21___closed__0));
v___x_660_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_661_ = l_mkPanicMessageWithDecl(v___x_660_, v___x_659_, v___x_658_, v___x_657_, v___x_656_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x21(lean_object* v_s_662_, lean_object* v_newStart_663_, lean_object* v_newEnd_664_){
_start:
{
uint8_t v___x_665_; 
v___x_665_ = lean_nat_dec_le(v_newStart_663_, v_newEnd_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; 
lean_dec_ref(v_s_662_);
v___x_666_ = lean_obj_once(&l_String_Slice_slice_x21___closed__2, &l_String_Slice_slice_x21___closed__2_once, _init_l_String_Slice_slice_x21___closed__2);
v___x_667_ = l_panic___at___00String_Slice_slice_x21_spec__0(v___x_666_);
return v___x_667_;
}
else
{
lean_object* v_str_668_; lean_object* v_startInclusive_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_678_; 
v_str_668_ = lean_ctor_get(v_s_662_, 0);
v_startInclusive_669_ = lean_ctor_get(v_s_662_, 1);
v_isSharedCheck_678_ = !lean_is_exclusive(v_s_662_);
if (v_isSharedCheck_678_ == 0)
{
lean_object* v_unused_679_; 
v_unused_679_ = lean_ctor_get(v_s_662_, 2);
lean_dec(v_unused_679_);
v___x_671_ = v_s_662_;
v_isShared_672_ = v_isSharedCheck_678_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_startInclusive_669_);
lean_inc(v_str_668_);
lean_dec(v_s_662_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_678_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_673_ = lean_nat_add(v_startInclusive_669_, v_newStart_663_);
v___x_674_ = lean_nat_add(v_startInclusive_669_, v_newEnd_664_);
lean_dec(v_startInclusive_669_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 2, v___x_674_);
lean_ctor_set(v___x_671_, 1, v___x_673_);
v___x_676_ = v___x_671_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_str_668_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_677_, 2, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x21___boxed(lean_object* v_s_680_, lean_object* v_newStart_681_, lean_object* v_newEnd_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_String_Slice_slice_x21(v_s_680_, v_newStart_681_, v_newEnd_682_);
lean_dec(v_newEnd_682_);
lean_dec(v_newStart_681_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21(lean_object* v_s_684_, lean_object* v_newStart_685_, lean_object* v_newEnd_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_String_Slice_slice_x21(v_s_684_, v_newStart_685_, v_newEnd_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21___boxed(lean_object* v_s_688_, lean_object* v_newStart_689_, lean_object* v_newEnd_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_String_Slice_replaceStartEnd_x21(v_s_688_, v_newStart_689_, v_newEnd_690_);
lean_dec(v_newEnd_690_);
lean_dec(v_newStart_689_);
return v_res_691_;
}
}
LEAN_EXPORT void l_String_decodeChar_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_692_ = stack[0].m_obj;
lean_object* v_byteIdx_693_ = stack[1].m_obj;
uint32_t v_res_695_;
v_res_695_ = lean_string_utf8_get_fast(v_s_692_, v_byteIdx_693_);
stack->m_num = v_res_695_;
}
LEAN_EXPORT lean_object* l_String_decodeChar___boxed(lean_object* v_s_696_, lean_object* v_byteIdx_697_, lean_object* v_h_698_){
_start:
{
uint32_t v_res_699_; lean_object* v_r_700_; 
v_res_699_ = lean_string_utf8_get_fast(v_s_696_, v_byteIdx_697_);
lean_dec(v_byteIdx_697_);
lean_dec_ref(v_s_696_);
v_r_700_ = lean_box_uint32(v_res_699_);
return v_r_700_;
}
}
uint32_t l_String_Slice_Pos_get___redArg(lean_object* v_s_701_, lean_object* v_pos_702_){
_start:
{
lean_object* v_str_703_; lean_object* v_startInclusive_704_; lean_object* v___x_705_; uint32_t v___x_706_; 
v_str_703_ = lean_ctor_get(v_s_701_, 0);
v_startInclusive_704_ = lean_ctor_get(v_s_701_, 1);
v___x_705_ = lean_nat_add(v_startInclusive_704_, v_pos_702_);
v___x_706_ = lean_string_utf8_get_fast(v_str_703_, v___x_705_);
lean_dec(v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT void l_String_Slice_Pos_get___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_701_ = stack[0].m_obj;
lean_object* v_pos_702_ = stack[1].m_obj;
uint32_t v_res_707_;
v_res_707_ = l_String_Slice_Pos_get___redArg(v_s_701_, v_pos_702_);
stack->m_num = v_res_707_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___redArg___boxed(lean_object* v_s_708_, lean_object* v_pos_709_){
_start:
{
uint32_t v_res_710_; lean_object* v_r_711_; 
v_res_710_ = l_String_Slice_Pos_get___redArg(v_s_708_, v_pos_709_);
lean_dec(v_pos_709_);
lean_dec_ref(v_s_708_);
v_r_711_ = lean_box_uint32(v_res_710_);
return v_r_711_;
}
}
uint32_t l_String_Slice_Pos_get(lean_object* v_s_712_, lean_object* v_pos_713_, lean_object* v_h_714_){
_start:
{
lean_object* v_str_715_; lean_object* v_startInclusive_716_; lean_object* v___x_717_; uint32_t v___x_718_; 
v_str_715_ = lean_ctor_get(v_s_712_, 0);
v_startInclusive_716_ = lean_ctor_get(v_s_712_, 1);
v___x_717_ = lean_nat_add(v_startInclusive_716_, v_pos_713_);
v___x_718_ = lean_string_utf8_get_fast(v_str_715_, v___x_717_);
lean_dec(v___x_717_);
return v___x_718_;
}
}
LEAN_EXPORT void l_String_Slice_Pos_get_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_712_ = stack[0].m_obj;
lean_object* v_pos_713_ = stack[1].m_obj;
uint32_t v_res_719_;
v_res_719_ = l_String_Slice_Pos_get(v_s_712_, v_pos_713_, lean_box(0));
stack->m_num = v_res_719_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___boxed(lean_object* v_s_720_, lean_object* v_pos_721_, lean_object* v_h_722_){
_start:
{
uint32_t v_res_723_; lean_object* v_r_724_; 
v_res_723_ = l_String_Slice_Pos_get(v_s_720_, v_pos_721_, v_h_722_);
lean_dec(v_pos_721_);
lean_dec_ref(v_s_720_);
v_r_724_ = lean_box_uint32(v_res_723_);
return v_r_724_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f(lean_object* v_s_725_, lean_object* v_pos_726_){
_start:
{
lean_object* v_str_727_; lean_object* v_startInclusive_728_; lean_object* v_endExclusive_729_; lean_object* v___x_730_; uint8_t v_decide_731_; 
v_str_727_ = lean_ctor_get(v_s_725_, 0);
v_startInclusive_728_ = lean_ctor_get(v_s_725_, 1);
v_endExclusive_729_ = lean_ctor_get(v_s_725_, 2);
v___x_730_ = lean_nat_sub(v_endExclusive_729_, v_startInclusive_728_);
v_decide_731_ = lean_nat_dec_eq(v_pos_726_, v___x_730_);
lean_dec(v___x_730_);
if (v_decide_731_ == 0)
{
lean_object* v___x_732_; uint32_t v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_732_ = lean_nat_add(v_startInclusive_728_, v_pos_726_);
v___x_733_ = lean_string_utf8_get_fast(v_str_727_, v___x_732_);
lean_dec(v___x_732_);
v___x_734_ = lean_box_uint32(v___x_733_);
v___x_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
return v___x_735_;
}
else
{
lean_object* v___x_736_; 
v___x_736_ = lean_box(0);
return v___x_736_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f___boxed(lean_object* v_s_737_, lean_object* v_pos_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_String_Slice_Pos_get_x3f(v_s_737_, v_pos_738_);
lean_dec(v_pos_738_);
lean_dec_ref(v_s_737_);
return v_res_739_;
}
}
static lean_object* _init_l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1(void){
_start:
{
uint32_t v___x_740_; lean_object* v___x_741_; 
v___x_740_ = 65;
v___x_741_ = lean_box_uint32(v___x_740_);
return v___x_741_;
}
}
uint32_t l_panic___at___00String_Slice_Pos_get_x21_spec__0(lean_object* v_msg_742_){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; uint32_t v___x_745_; 
v___x_743_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1;
v___x_744_ = lean_panic_fn_borrowed(v___x_743_, v_msg_742_);
v___x_745_ = lean_unbox_uint32(v___x_744_);
lean_dec(v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT void l_panic___at___00String_Slice_Pos_get_x21_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_742_ = stack[0].m_obj;
uint32_t v_res_746_;
v_res_746_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v_msg_742_);
stack->m_num = v_res_746_;
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed(lean_object* v_msg_747_){
_start:
{
uint32_t v_res_748_; lean_object* v_r_749_; 
v_res_748_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v_msg_747_);
v_r_749_ = lean_box_uint32(v_res_748_);
return v_r_749_;
}
}
static lean_object* _init_l_String_Slice_Pos_get_x21___closed__2(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_752_ = ((lean_object*)(l_String_Slice_Pos_get_x21___closed__1));
v___x_753_ = lean_unsigned_to_nat(29u);
v___x_754_ = lean_unsigned_to_nat(1131u);
v___x_755_ = ((lean_object*)(l_String_Slice_Pos_get_x21___closed__0));
v___x_756_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_757_ = l_mkPanicMessageWithDecl(v___x_756_, v___x_755_, v___x_754_, v___x_753_, v___x_752_);
return v___x_757_;
}
}
uint32_t l_String_Slice_Pos_get_x21(lean_object* v_s_758_, lean_object* v_pos_759_){
_start:
{
lean_object* v_str_760_; lean_object* v_startInclusive_761_; lean_object* v_endExclusive_762_; lean_object* v___x_763_; uint8_t v_decide_764_; 
v_str_760_ = lean_ctor_get(v_s_758_, 0);
v_startInclusive_761_ = lean_ctor_get(v_s_758_, 1);
v_endExclusive_762_ = lean_ctor_get(v_s_758_, 2);
v___x_763_ = lean_nat_sub(v_endExclusive_762_, v_startInclusive_761_);
v_decide_764_ = lean_nat_dec_eq(v_pos_759_, v___x_763_);
lean_dec(v___x_763_);
if (v_decide_764_ == 0)
{
lean_object* v___x_765_; uint32_t v___x_766_; 
v___x_765_ = lean_nat_add(v_startInclusive_761_, v_pos_759_);
v___x_766_ = lean_string_utf8_get_fast(v_str_760_, v___x_765_);
lean_dec(v___x_765_);
return v___x_766_;
}
else
{
lean_object* v___x_767_; uint32_t v___x_768_; 
v___x_767_ = lean_obj_once(&l_String_Slice_Pos_get_x21___closed__2, &l_String_Slice_Pos_get_x21___closed__2_once, _init_l_String_Slice_Pos_get_x21___closed__2);
v___x_768_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v___x_767_);
return v___x_768_;
}
}
}
LEAN_EXPORT void l_String_Slice_Pos_get_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_758_ = stack[0].m_obj;
lean_object* v_pos_759_ = stack[1].m_obj;
uint32_t v_res_769_;
v_res_769_ = l_String_Slice_Pos_get_x21(v_s_758_, v_pos_759_);
stack->m_num = v_res_769_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x21___boxed(lean_object* v_s_770_, lean_object* v_pos_771_){
_start:
{
uint32_t v_res_772_; lean_object* v_r_773_; 
v_res_772_ = l_String_Slice_Pos_get_x21(v_s_770_, v_pos_771_);
lean_dec(v_pos_771_);
lean_dec_ref(v_s_770_);
v_r_773_ = lean_box_uint32(v_res_772_);
return v_r_773_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg(lean_object* v_pos_774_){
_start:
{
lean_inc(v_pos_774_);
return v_pos_774_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg___boxed(lean_object* v_pos_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_String_Pos_toSlice___redArg(v_pos_775_);
lean_dec(v_pos_775_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice(lean_object* v_s_777_, lean_object* v_pos_778_){
_start:
{
lean_inc(v_pos_778_);
return v_pos_778_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___boxed(lean_object* v_s_779_, lean_object* v_pos_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_String_Pos_toSlice(v_s_779_, v_pos_780_);
lean_dec(v_pos_780_);
lean_dec_ref(v_s_779_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg(lean_object* v_pos_782_){
_start:
{
lean_inc(v_pos_782_);
return v_pos_782_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg___boxed(lean_object* v_pos_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_String_Pos_ofToSlice___redArg(v_pos_783_);
lean_dec(v_pos_783_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice(lean_object* v_s_785_, lean_object* v_pos_786_){
_start:
{
lean_inc(v_pos_786_);
return v_pos_786_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___boxed(lean_object* v_s_787_, lean_object* v_pos_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_String_Pos_ofToSlice(v_s_787_, v_pos_788_);
lean_dec(v_pos_788_);
lean_dec_ref(v_s_787_);
return v_res_789_;
}
}
uint32_t l_String_Pos_get___redArg(lean_object* v_s_790_, lean_object* v_pos_791_){
_start:
{
uint32_t v___x_792_; 
v___x_792_ = lean_string_utf8_get_fast(v_s_790_, v_pos_791_);
return v___x_792_;
}
}
LEAN_EXPORT void l_String_Pos_get___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_790_ = stack[0].m_obj;
lean_object* v_pos_791_ = stack[1].m_obj;
uint32_t v_res_793_;
v_res_793_ = l_String_Pos_get___redArg(v_s_790_, v_pos_791_);
stack->m_num = v_res_793_;
}
LEAN_EXPORT lean_object* l_String_Pos_get___redArg___boxed(lean_object* v_s_794_, lean_object* v_pos_795_){
_start:
{
uint32_t v_res_796_; lean_object* v_r_797_; 
v_res_796_ = l_String_Pos_get___redArg(v_s_794_, v_pos_795_);
lean_dec(v_pos_795_);
lean_dec_ref(v_s_794_);
v_r_797_ = lean_box_uint32(v_res_796_);
return v_r_797_;
}
}
uint32_t l_String_Pos_get(lean_object* v_s_798_, lean_object* v_pos_799_, lean_object* v_h_800_){
_start:
{
uint32_t v___x_801_; 
v___x_801_ = lean_string_utf8_get_fast(v_s_798_, v_pos_799_);
return v___x_801_;
}
}
LEAN_EXPORT void l_String_Pos_get_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_798_ = stack[0].m_obj;
lean_object* v_pos_799_ = stack[1].m_obj;
uint32_t v_res_802_;
v_res_802_ = l_String_Pos_get(v_s_798_, v_pos_799_, lean_box(0));
stack->m_num = v_res_802_;
}
LEAN_EXPORT lean_object* l_String_Pos_get___boxed(lean_object* v_s_803_, lean_object* v_pos_804_, lean_object* v_h_805_){
_start:
{
uint32_t v_res_806_; lean_object* v_r_807_; 
v_res_806_ = l_String_Pos_get(v_s_803_, v_pos_804_, v_h_805_);
lean_dec(v_pos_804_);
lean_dec_ref(v_s_803_);
v_r_807_ = lean_box_uint32(v_res_806_);
return v_r_807_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x3f(lean_object* v_s_808_, lean_object* v_pos_809_){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = lean_string_utf8_byte_size(v_s_808_);
v___x_812_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_812_, 0, v_s_808_);
lean_ctor_set(v___x_812_, 1, v___x_810_);
lean_ctor_set(v___x_812_, 2, v___x_811_);
v___x_813_ = l_String_Slice_Pos_get_x3f(v___x_812_, v_pos_809_);
lean_dec_ref_known(v___x_812_, 3);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x3f___boxed(lean_object* v_s_814_, lean_object* v_pos_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_String_Pos_get_x3f(v_s_814_, v_pos_815_);
lean_dec(v_pos_815_);
return v_res_816_;
}
}
uint32_t l_String_Pos_get_x21(lean_object* v_s_817_, lean_object* v_pos_818_){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; uint32_t v___x_822_; 
v___x_819_ = lean_unsigned_to_nat(0u);
v___x_820_ = lean_string_utf8_byte_size(v_s_817_);
v___x_821_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_821_, 0, v_s_817_);
lean_ctor_set(v___x_821_, 1, v___x_819_);
lean_ctor_set(v___x_821_, 2, v___x_820_);
v___x_822_ = l_String_Slice_Pos_get_x21(v___x_821_, v_pos_818_);
lean_dec_ref_known(v___x_821_, 3);
return v___x_822_;
}
}
LEAN_EXPORT void l_String_Pos_get_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_817_ = stack[0].m_obj;
lean_object* v_pos_818_ = stack[1].m_obj;
uint32_t v_res_823_;
v_res_823_ = l_String_Pos_get_x21(v_s_817_, v_pos_818_);
stack->m_num = v_res_823_;
}
LEAN_EXPORT lean_object* l_String_Pos_get_x21___boxed(lean_object* v_s_824_, lean_object* v_pos_825_){
_start:
{
uint32_t v_res_826_; lean_object* v_r_827_; 
v_res_826_ = l_String_Pos_get_x21(v_s_824_, v_pos_825_);
lean_dec(v_pos_825_);
v_r_827_ = lean_box_uint32(v_res_826_);
return v_r_827_;
}
}
uint8_t l_String_Pos_byte___redArg(lean_object* v_s_828_, lean_object* v_pos_829_){
_start:
{
uint8_t v___x_830_; 
v___x_830_ = lean_string_get_byte_fast(v_s_828_, v_pos_829_);
return v___x_830_;
}
}
LEAN_EXPORT void l_String_Pos_byte___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_828_ = stack[0].m_obj;
lean_object* v_pos_829_ = stack[1].m_obj;
uint8_t v_res_831_;
v_res_831_ = l_String_Pos_byte___redArg(v_s_828_, v_pos_829_);
stack->m_num = v_res_831_;
}
LEAN_EXPORT lean_object* l_String_Pos_byte___redArg___boxed(lean_object* v_s_832_, lean_object* v_pos_833_){
_start:
{
uint8_t v_res_834_; lean_object* v_r_835_; 
v_res_834_ = l_String_Pos_byte___redArg(v_s_832_, v_pos_833_);
lean_dec_ref(v_s_832_);
v_r_835_ = lean_box(v_res_834_);
return v_r_835_;
}
}
uint8_t l_String_Pos_byte(lean_object* v_s_836_, lean_object* v_pos_837_, lean_object* v_h_838_){
_start:
{
uint8_t v___x_839_; 
v___x_839_ = lean_string_get_byte_fast(v_s_836_, v_pos_837_);
return v___x_839_;
}
}
LEAN_EXPORT void l_String_Pos_byte_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_836_ = stack[0].m_obj;
lean_object* v_pos_837_ = stack[1].m_obj;
uint8_t v_res_840_;
v_res_840_ = l_String_Pos_byte(v_s_836_, v_pos_837_, lean_box(0));
stack->m_num = v_res_840_;
}
LEAN_EXPORT lean_object* l_String_Pos_byte___boxed(lean_object* v_s_841_, lean_object* v_pos_842_, lean_object* v_h_843_){
_start:
{
uint8_t v_res_844_; lean_object* v_r_845_; 
v_res_844_ = l_String_Pos_byte(v_s_841_, v_pos_842_, v_h_843_);
lean_dec_ref(v_s_841_);
v_r_845_ = lean_box(v_res_844_);
return v_r_845_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg(lean_object* v_pos_846_){
_start:
{
lean_inc(v_pos_846_);
return v_pos_846_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg___boxed(lean_object* v_pos_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_String_Pos_ofCopy___redArg(v_pos_847_);
lean_dec(v_pos_847_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy(lean_object* v_s_849_, lean_object* v_pos_850_){
_start:
{
lean_inc(v_pos_850_);
return v_pos_850_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___boxed(lean_object* v_s_851_, lean_object* v_pos_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_String_Pos_ofCopy(v_s_851_, v_pos_852_);
lean_dec(v_pos_852_);
lean_dec_ref(v_s_851_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg(lean_object* v_pos_854_){
_start:
{
lean_inc(v_pos_854_);
return v_pos_854_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg___boxed(lean_object* v_pos_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_String_Slice_Pos_copy___redArg(v_pos_855_);
lean_dec(v_pos_855_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy(lean_object* v_s_857_, lean_object* v_pos_858_){
_start:
{
lean_inc(v_pos_858_);
return v_pos_858_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___boxed(lean_object* v_s_859_, lean_object* v_pos_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_String_Slice_Pos_copy(v_s_859_, v_pos_860_);
lean_dec(v_pos_860_);
lean_dec_ref(v_s_859_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg(lean_object* v_pos_862_){
_start:
{
lean_inc(v_pos_862_);
return v_pos_862_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg___boxed(lean_object* v_pos_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_String_Slice_Pos_toCopy___redArg(v_pos_863_);
lean_dec(v_pos_863_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy(lean_object* v_s_865_, lean_object* v_pos_866_){
_start:
{
lean_inc(v_pos_866_);
return v_pos_866_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___boxed(lean_object* v_s_867_, lean_object* v_pos_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_String_Slice_Pos_toCopy(v_s_867_, v_pos_868_);
lean_dec(v_pos_868_);
lean_dec_ref(v_s_867_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg(lean_object* v_p_u2080_870_, lean_object* v_pos_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = lean_nat_add(v_p_u2080_870_, v_pos_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg___boxed(lean_object* v_p_u2080_873_, lean_object* v_pos_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_String_Slice_Pos_ofSliceFrom___redArg(v_p_u2080_873_, v_pos_874_);
lean_dec(v_pos_874_);
lean_dec(v_p_u2080_873_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom(lean_object* v_s_876_, lean_object* v_p_u2080_877_, lean_object* v_pos_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = lean_nat_add(v_p_u2080_877_, v_pos_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___boxed(lean_object* v_s_880_, lean_object* v_p_u2080_881_, lean_object* v_pos_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_String_Slice_Pos_ofSliceFrom(v_s_880_, v_p_u2080_881_, v_pos_882_);
lean_dec(v_pos_882_);
lean_dec(v_p_u2080_881_);
lean_dec_ref(v_s_880_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg(lean_object* v_p_u2080_884_, lean_object* v_pos_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = lean_nat_add(v_p_u2080_884_, v_pos_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg___boxed(lean_object* v_p_u2080_887_, lean_object* v_pos_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_String_Slice_Pos_ofReplaceStart___redArg(v_p_u2080_887_, v_pos_888_);
lean_dec(v_pos_888_);
lean_dec(v_p_u2080_887_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart(lean_object* v_s_890_, lean_object* v_p_u2080_891_, lean_object* v_pos_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = lean_nat_add(v_p_u2080_891_, v_pos_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___boxed(lean_object* v_s_894_, lean_object* v_p_u2080_895_, lean_object* v_pos_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_String_Slice_Pos_ofReplaceStart(v_s_894_, v_p_u2080_895_, v_pos_896_);
lean_dec(v_pos_896_);
lean_dec(v_p_u2080_895_);
lean_dec_ref(v_s_894_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg(lean_object* v_p_u2080_898_, lean_object* v_pos_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = lean_nat_sub(v_pos_899_, v_p_u2080_898_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg___boxed(lean_object* v_p_u2080_901_, lean_object* v_pos_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_String_Slice_Pos_sliceFrom___redArg(v_p_u2080_901_, v_pos_902_);
lean_dec(v_pos_902_);
lean_dec(v_p_u2080_901_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom(lean_object* v_s_904_, lean_object* v_p_u2080_905_, lean_object* v_pos_906_, lean_object* v_h_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = lean_nat_sub(v_pos_906_, v_p_u2080_905_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___boxed(lean_object* v_s_909_, lean_object* v_p_u2080_910_, lean_object* v_pos_911_, lean_object* v_h_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_String_Slice_Pos_sliceFrom(v_s_909_, v_p_u2080_910_, v_pos_911_, v_h_912_);
lean_dec(v_pos_911_);
lean_dec(v_p_u2080_910_);
lean_dec_ref(v_s_909_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg(lean_object* v_p_u2080_914_, lean_object* v_pos_915_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = lean_nat_sub(v_pos_915_, v_p_u2080_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg___boxed(lean_object* v_p_u2080_917_, lean_object* v_pos_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_String_Slice_Pos_toReplaceStart___redArg(v_p_u2080_917_, v_pos_918_);
lean_dec(v_pos_918_);
lean_dec(v_p_u2080_917_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart(lean_object* v_s_920_, lean_object* v_p_u2080_921_, lean_object* v_pos_922_, lean_object* v_h_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = lean_nat_sub(v_pos_922_, v_p_u2080_921_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___boxed(lean_object* v_s_925_, lean_object* v_p_u2080_926_, lean_object* v_pos_927_, lean_object* v_h_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_String_Slice_Pos_toReplaceStart(v_s_925_, v_p_u2080_926_, v_pos_927_, v_h_928_);
lean_dec(v_pos_927_);
lean_dec(v_p_u2080_926_);
lean_dec_ref(v_s_925_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg(lean_object* v_pos_930_){
_start:
{
lean_inc(v_pos_930_);
return v_pos_930_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg___boxed(lean_object* v_pos_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_String_Slice_Pos_ofSliceTo___redArg(v_pos_931_);
lean_dec(v_pos_931_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo(lean_object* v_s_933_, lean_object* v_p_u2080_934_, lean_object* v_pos_935_){
_start:
{
lean_inc(v_pos_935_);
return v_pos_935_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___boxed(lean_object* v_s_936_, lean_object* v_p_u2080_937_, lean_object* v_pos_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_String_Slice_Pos_ofSliceTo(v_s_936_, v_p_u2080_937_, v_pos_938_);
lean_dec(v_pos_938_);
lean_dec(v_p_u2080_937_);
lean_dec_ref(v_s_936_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg(lean_object* v_pos_940_){
_start:
{
lean_inc(v_pos_940_);
return v_pos_940_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg___boxed(lean_object* v_pos_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_String_Slice_Pos_ofReplaceEnd___redArg(v_pos_941_);
lean_dec(v_pos_941_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd(lean_object* v_s_943_, lean_object* v_p_u2080_944_, lean_object* v_pos_945_){
_start:
{
lean_inc(v_pos_945_);
return v_pos_945_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___boxed(lean_object* v_s_946_, lean_object* v_p_u2080_947_, lean_object* v_pos_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_String_Slice_Pos_ofReplaceEnd(v_s_946_, v_p_u2080_947_, v_pos_948_);
lean_dec(v_pos_948_);
lean_dec(v_p_u2080_947_);
lean_dec_ref(v_s_946_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg(lean_object* v_pos_950_){
_start:
{
lean_inc(v_pos_950_);
return v_pos_950_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg___boxed(lean_object* v_pos_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_String_Slice_Pos_sliceTo___redArg(v_pos_951_);
lean_dec(v_pos_951_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo(lean_object* v_s_953_, lean_object* v_p_u2080_954_, lean_object* v_pos_955_, lean_object* v_h_956_){
_start:
{
lean_inc(v_pos_955_);
return v_pos_955_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___boxed(lean_object* v_s_957_, lean_object* v_p_u2080_958_, lean_object* v_pos_959_, lean_object* v_h_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_String_Slice_Pos_sliceTo(v_s_957_, v_p_u2080_958_, v_pos_959_, v_h_960_);
lean_dec(v_pos_959_);
lean_dec(v_p_u2080_958_);
lean_dec_ref(v_s_957_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg(lean_object* v_pos_962_){
_start:
{
lean_inc(v_pos_962_);
return v_pos_962_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg___boxed(lean_object* v_pos_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_String_Slice_Pos_toReplaceEnd___redArg(v_pos_963_);
lean_dec(v_pos_963_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd(lean_object* v_s_965_, lean_object* v_p_u2080_966_, lean_object* v_pos_967_, lean_object* v_h_968_){
_start:
{
lean_inc(v_pos_967_);
return v_pos_967_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___boxed(lean_object* v_s_969_, lean_object* v_p_u2080_970_, lean_object* v_pos_971_, lean_object* v_h_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_String_Slice_Pos_toReplaceEnd(v_s_969_, v_p_u2080_970_, v_pos_971_, v_h_972_);
lean_dec(v_pos_971_);
lean_dec(v_p_u2080_970_);
lean_dec_ref(v_s_969_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg(lean_object* v_s_974_, lean_object* v_pos_975_){
_start:
{
lean_object* v_str_976_; lean_object* v_startInclusive_977_; lean_object* v___x_978_; uint8_t v___x_979_; uint8_t v___x_980_; uint8_t v___x_981_; uint8_t v___x_982_; uint8_t v___x_983_; 
v_str_976_ = lean_ctor_get(v_s_974_, 0);
v_startInclusive_977_ = lean_ctor_get(v_s_974_, 1);
v___x_978_ = lean_nat_add(v_startInclusive_977_, v_pos_975_);
v___x_979_ = lean_string_get_byte_fast(v_str_976_, v___x_978_);
v___x_980_ = 128;
v___x_981_ = lean_uint8_land(v___x_979_, v___x_980_);
v___x_982_ = 0;
v___x_983_ = lean_uint8_dec_eq(v___x_981_, v___x_982_);
if (v___x_983_ == 0)
{
uint8_t v___x_984_; uint8_t v___x_985_; uint8_t v___x_986_; uint8_t v___x_987_; 
v___x_984_ = 224;
v___x_985_ = lean_uint8_land(v___x_979_, v___x_984_);
v___x_986_ = 192;
v___x_987_ = lean_uint8_dec_eq(v___x_985_, v___x_986_);
if (v___x_987_ == 0)
{
uint8_t v___x_988_; uint8_t v___x_989_; uint8_t v___x_990_; 
v___x_988_ = 240;
v___x_989_ = lean_uint8_land(v___x_979_, v___x_988_);
v___x_990_ = lean_uint8_dec_eq(v___x_989_, v___x_984_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = lean_unsigned_to_nat(4u);
v___x_992_ = lean_nat_add(v_pos_975_, v___x_991_);
return v___x_992_;
}
else
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = lean_unsigned_to_nat(3u);
v___x_994_ = lean_nat_add(v_pos_975_, v___x_993_);
return v___x_994_;
}
}
else
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = lean_unsigned_to_nat(2u);
v___x_996_ = lean_nat_add(v_pos_975_, v___x_995_);
return v___x_996_;
}
}
else
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_unsigned_to_nat(1u);
v___x_998_ = lean_nat_add(v_pos_975_, v___x_997_);
return v___x_998_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg___boxed(lean_object* v_s_999_, lean_object* v_pos_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_String_Slice_Pos_next___redArg(v_s_999_, v_pos_1000_);
lean_dec(v_pos_1000_);
lean_dec_ref(v_s_999_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next(lean_object* v_s_1002_, lean_object* v_pos_1003_, lean_object* v_h_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_String_Slice_Pos_next___redArg(v_s_1002_, v_pos_1003_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___boxed(lean_object* v_s_1006_, lean_object* v_pos_1007_, lean_object* v_h_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_String_Slice_Pos_next(v_s_1006_, v_pos_1007_, v_h_1008_);
lean_dec(v_pos_1007_);
lean_dec_ref(v_s_1006_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f(lean_object* v_s_1010_, lean_object* v_pos_1011_){
_start:
{
lean_object* v_startInclusive_1012_; lean_object* v_endExclusive_1013_; lean_object* v___x_1014_; uint8_t v_decide_1015_; 
v_startInclusive_1012_ = lean_ctor_get(v_s_1010_, 1);
v_endExclusive_1013_ = lean_ctor_get(v_s_1010_, 2);
v___x_1014_ = lean_nat_sub(v_endExclusive_1013_, v_startInclusive_1012_);
v_decide_1015_ = lean_nat_dec_eq(v_pos_1011_, v___x_1014_);
lean_dec(v___x_1014_);
if (v_decide_1015_ == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = l_String_Slice_Pos_next___redArg(v_s_1010_, v_pos_1011_);
v___x_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
return v___x_1017_;
}
else
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_box(0);
return v___x_1018_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f___boxed(lean_object* v_s_1019_, lean_object* v_pos_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_String_Slice_Pos_next_x3f(v_s_1019_, v_pos_1020_);
lean_dec(v_pos_1020_);
lean_dec_ref(v_s_1019_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(lean_object* v_msg_1022_){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_unsigned_to_nat(0u);
v___x_1024_ = lean_panic_fn_borrowed(v___x_1023_, v_msg_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0(lean_object* v_s_1025_, lean_object* v_msg_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v_msg_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___boxed(lean_object* v_s_1028_, lean_object* v_msg_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0(v_s_1028_, v_msg_1029_);
lean_dec_ref(v_s_1028_);
return v_res_1030_;
}
}
static lean_object* _init_l_String_Slice_Pos_next_x21___closed__2(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1033_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__1));
v___x_1034_ = lean_unsigned_to_nat(29u);
v___x_1035_ = lean_unsigned_to_nat(1518u);
v___x_1036_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__0));
v___x_1037_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1038_ = l_mkPanicMessageWithDecl(v___x_1037_, v___x_1036_, v___x_1035_, v___x_1034_, v___x_1033_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21(lean_object* v_s_1039_, lean_object* v_pos_1040_){
_start:
{
lean_object* v_startInclusive_1041_; lean_object* v_endExclusive_1042_; lean_object* v___x_1043_; uint8_t v_decide_1044_; 
v_startInclusive_1041_ = lean_ctor_get(v_s_1039_, 1);
v_endExclusive_1042_ = lean_ctor_get(v_s_1039_, 2);
v___x_1043_ = lean_nat_sub(v_endExclusive_1042_, v_startInclusive_1041_);
v_decide_1044_ = lean_nat_dec_eq(v_pos_1040_, v___x_1043_);
lean_dec(v___x_1043_);
if (v_decide_1044_ == 0)
{
lean_object* v___x_1045_; 
v___x_1045_ = l_String_Slice_Pos_next___redArg(v_s_1039_, v_pos_1040_);
return v___x_1045_;
}
else
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = lean_obj_once(&l_String_Slice_Pos_next_x21___closed__2, &l_String_Slice_Pos_next_x21___closed__2_once, _init_l_String_Slice_Pos_next_x21___closed__2);
v___x_1047_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_1046_);
return v___x_1047_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21___boxed(lean_object* v_s_1048_, lean_object* v_pos_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_String_Slice_Pos_next_x21(v_s_1048_, v_pos_1049_);
lean_dec(v_pos_1049_);
lean_dec_ref(v_s_1048_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg(lean_object* v_s_1051_, lean_object* v_off_1052_){
_start:
{
uint8_t v___y_1054_; lean_object* v_str_1060_; lean_object* v_startInclusive_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; uint8_t v___x_1064_; uint8_t v___x_1065_; uint8_t v___x_1066_; uint8_t v___x_1067_; 
v_str_1060_ = lean_ctor_get(v_s_1051_, 0);
v_startInclusive_1061_ = lean_ctor_get(v_s_1051_, 1);
v___x_1062_ = lean_nat_add(v_startInclusive_1061_, v_off_1052_);
v___x_1063_ = lean_string_get_byte_fast(v_str_1060_, v___x_1062_);
v___x_1064_ = 128;
v___x_1065_ = lean_uint8_land(v___x_1063_, v___x_1064_);
v___x_1066_ = 0;
v___x_1067_ = lean_uint8_dec_eq(v___x_1065_, v___x_1066_);
if (v___x_1067_ == 0)
{
uint8_t v___x_1068_; uint8_t v___x_1069_; uint8_t v___x_1070_; uint8_t v___x_1071_; 
v___x_1068_ = 224;
v___x_1069_ = lean_uint8_land(v___x_1063_, v___x_1068_);
v___x_1070_ = 192;
v___x_1071_ = lean_uint8_dec_eq(v___x_1069_, v___x_1070_);
if (v___x_1071_ == 0)
{
uint8_t v___x_1072_; uint8_t v___x_1073_; uint8_t v___x_1074_; 
v___x_1072_ = 240;
v___x_1073_ = lean_uint8_land(v___x_1063_, v___x_1072_);
v___x_1074_ = lean_uint8_dec_eq(v___x_1073_, v___x_1068_);
if (v___x_1074_ == 0)
{
uint8_t v___x_1075_; uint8_t v___x_1076_; uint8_t v___x_1077_; 
v___x_1075_ = 248;
v___x_1076_ = lean_uint8_land(v___x_1063_, v___x_1075_);
v___x_1077_ = lean_uint8_dec_eq(v___x_1076_, v___x_1072_);
v___y_1054_ = v___x_1077_;
goto v___jp_1053_;
}
else
{
v___y_1054_ = v___x_1074_;
goto v___jp_1053_;
}
}
else
{
v___y_1054_ = v___x_1071_;
goto v___jp_1053_;
}
}
else
{
v___y_1054_ = v___x_1067_;
goto v___jp_1053_;
}
v___jp_1053_:
{
if (v___y_1054_ == 0)
{
lean_object* v_zero_1055_; uint8_t v_isZero_1056_; lean_object* v_one_1057_; lean_object* v_n_1058_; 
v_zero_1055_ = lean_unsigned_to_nat(0u);
v_isZero_1056_ = lean_nat_dec_eq(v_off_1052_, v_zero_1055_);
v_one_1057_ = lean_unsigned_to_nat(1u);
v_n_1058_ = lean_nat_sub(v_off_1052_, v_one_1057_);
lean_dec(v_off_1052_);
v_off_1052_ = v_n_1058_;
goto _start;
}
else
{
return v_off_1052_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg___boxed(lean_object* v_s_1078_, lean_object* v_off_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1078_, v_off_1079_);
lean_dec_ref(v_s_1078_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go(lean_object* v_s_1081_, lean_object* v_off_1082_, lean_object* v_h_u2081_1083_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1081_, v_off_1082_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___boxed(lean_object* v_s_1085_, lean_object* v_off_1086_, lean_object* v_h_u2081_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_String_Slice_Pos_prevAux_go(v_s_1085_, v_off_1086_, v_h_u2081_1087_);
lean_dec_ref(v_s_1085_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg(lean_object* v_s_1089_, lean_object* v_pos_1090_){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = lean_unsigned_to_nat(1u);
v___x_1092_ = lean_nat_sub(v_pos_1090_, v___x_1091_);
v___x_1093_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1089_, v___x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg___boxed(lean_object* v_s_1094_, lean_object* v_pos_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_String_Slice_Pos_prevAux___redArg(v_s_1094_, v_pos_1095_);
lean_dec(v_pos_1095_);
lean_dec_ref(v_s_1094_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux(lean_object* v_s_1097_, lean_object* v_pos_1098_, lean_object* v_h_1099_){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1100_ = lean_unsigned_to_nat(1u);
v___x_1101_ = lean_nat_sub(v_pos_1098_, v___x_1100_);
v___x_1102_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1097_, v___x_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___boxed(lean_object* v_s_1103_, lean_object* v_pos_1104_, lean_object* v_h_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_String_Slice_Pos_prevAux(v_s_1103_, v_pos_1104_, v_h_1105_);
lean_dec(v_pos_1104_);
lean_dec_ref(v_s_1103_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(lean_object* v_off_1107_, lean_object* v_h__1_1108_, lean_object* v_h__2_1109_){
_start:
{
lean_object* v_zero_1110_; uint8_t v_isZero_1111_; 
v_zero_1110_ = lean_unsigned_to_nat(0u);
v_isZero_1111_ = lean_nat_dec_eq(v_off_1107_, v_zero_1110_);
if (v_isZero_1111_ == 1)
{
lean_object* v___x_1112_; 
lean_dec(v_h__2_1109_);
v___x_1112_ = lean_apply_3(v_h__1_1108_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1112_;
}
else
{
lean_object* v_one_1113_; lean_object* v_n_1114_; lean_object* v___x_1115_; 
lean_dec(v_h__1_1108_);
v_one_1113_ = lean_unsigned_to_nat(1u);
v_n_1114_ = lean_nat_sub(v_off_1107_, v_one_1113_);
v___x_1115_ = lean_apply_4(v_h__2_1109_, v_n_1114_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg___boxed(lean_object* v_off_1116_, lean_object* v_h__1_1117_, lean_object* v_h__2_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(v_off_1116_, v_h__1_1117_, v_h__2_1118_);
lean_dec(v_off_1116_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(lean_object* v_s_1120_, lean_object* v_motive_1121_, lean_object* v_off_1122_, lean_object* v_h_u2081_1123_, lean_object* v_hbyte_1124_, lean_object* v_this_1125_, lean_object* v_h__1_1126_, lean_object* v_h__2_1127_){
_start:
{
lean_object* v_zero_1128_; uint8_t v_isZero_1129_; 
v_zero_1128_ = lean_unsigned_to_nat(0u);
v_isZero_1129_ = lean_nat_dec_eq(v_off_1122_, v_zero_1128_);
if (v_isZero_1129_ == 1)
{
lean_object* v___x_1130_; 
lean_dec(v_h__2_1127_);
v___x_1130_ = lean_apply_3(v_h__1_1126_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1130_;
}
else
{
lean_object* v_one_1131_; lean_object* v_n_1132_; lean_object* v___x_1133_; 
lean_dec(v_h__1_1126_);
v_one_1131_ = lean_unsigned_to_nat(1u);
v_n_1132_ = lean_nat_sub(v_off_1122_, v_one_1131_);
v___x_1133_ = lean_apply_4(v_h__2_1127_, v_n_1132_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___boxed(lean_object* v_s_1134_, lean_object* v_motive_1135_, lean_object* v_off_1136_, lean_object* v_h_u2081_1137_, lean_object* v_hbyte_1138_, lean_object* v_this_1139_, lean_object* v_h__1_1140_, lean_object* v_h__2_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(v_s_1134_, v_motive_1135_, v_off_1136_, v_h_u2081_1137_, v_hbyte_1138_, v_this_1139_, v_h__1_1140_, v_h__2_1141_);
lean_dec(v_off_1136_);
lean_dec_ref(v_s_1134_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg(lean_object* v_off_1143_){
_start:
{
lean_inc(v_off_1143_);
return v_off_1143_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg___boxed(lean_object* v_off_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_String_Slice_pos___redArg(v_off_1144_);
lean_dec(v_off_1144_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos(lean_object* v_s_1146_, lean_object* v_off_1147_, lean_object* v_h_1148_){
_start:
{
lean_inc(v_off_1147_);
return v_off_1147_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___boxed(lean_object* v_s_1149_, lean_object* v_off_1150_, lean_object* v_h_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_String_Slice_pos(v_s_1149_, v_off_1150_, v_h_1151_);
lean_dec(v_off_1150_);
lean_dec_ref(v_s_1149_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f(lean_object* v_s_1153_, lean_object* v_off_1154_){
_start:
{
uint8_t v___x_1155_; 
v___x_1155_ = l_String_Pos_Raw_isValidForSlice(v_s_1153_, v_off_1154_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
lean_dec(v_off_1154_);
v___x_1156_ = lean_box(0);
return v___x_1156_;
}
else
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1157_, 0, v_off_1154_);
return v___x_1157_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f___boxed(lean_object* v_s_1158_, lean_object* v_off_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_String_Slice_pos_x3f(v_s_1158_, v_off_1159_);
lean_dec_ref(v_s_1158_);
return v_res_1160_;
}
}
static lean_object* _init_l_String_Slice_pos_x21___closed__2(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1163_ = ((lean_object*)(l_String_Slice_pos_x21___closed__1));
v___x_1164_ = lean_unsigned_to_nat(4u);
v___x_1165_ = lean_unsigned_to_nat(1606u);
v___x_1166_ = ((lean_object*)(l_String_Slice_pos_x21___closed__0));
v___x_1167_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1168_ = l_mkPanicMessageWithDecl(v___x_1167_, v___x_1166_, v___x_1165_, v___x_1164_, v___x_1163_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21(lean_object* v_s_1169_, lean_object* v_off_1170_){
_start:
{
uint8_t v___x_1171_; 
v___x_1171_ = l_String_Pos_Raw_isValidForSlice(v_s_1169_, v_off_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = lean_obj_once(&l_String_Slice_pos_x21___closed__2, &l_String_Slice_pos_x21___closed__2_once, _init_l_String_Slice_pos_x21___closed__2);
v___x_1173_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_1172_);
return v___x_1173_;
}
else
{
lean_inc(v_off_1170_);
return v_off_1170_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21___boxed(lean_object* v_s_1174_, lean_object* v_off_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_String_Slice_pos_x21(v_s_1174_, v_off_1175_);
lean_dec(v_off_1175_);
lean_dec_ref(v_s_1174_);
return v_res_1176_;
}
}
LEAN_EXPORT void l_String_Pos_next_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1177_ = stack[0].m_obj;
lean_object* v_pos_1178_ = stack[1].m_obj;
lean_object* v_res_1180_;
v_res_1180_ = lean_string_utf8_next_fast(v_s_1177_, v_pos_1178_);
stack->m_obj
 = v_res_1180_;
}
LEAN_EXPORT lean_object* l_String_Pos_next___boxed(lean_object* v_s_1181_, lean_object* v_pos_1182_, lean_object* v_h_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = lean_string_utf8_next_fast(v_s_1181_, v_pos_1182_);
lean_dec(v_pos_1182_);
lean_dec_ref(v_s_1181_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x3f(lean_object* v_s_1185_, lean_object* v_pos_1186_){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1187_ = lean_unsigned_to_nat(0u);
v___x_1188_ = lean_string_utf8_byte_size(v_s_1185_);
v___x_1189_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1189_, 0, v_s_1185_);
lean_ctor_set(v___x_1189_, 1, v___x_1187_);
lean_ctor_set(v___x_1189_, 2, v___x_1188_);
v___x_1190_ = l_String_Slice_Pos_next_x3f(v___x_1189_, v_pos_1186_);
lean_dec_ref_known(v___x_1189_, 3);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v___x_1191_; 
v___x_1191_ = lean_box(0);
return v___x_1191_;
}
else
{
lean_object* v_val_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
v_val_1192_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1190_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_val_1192_);
lean_dec(v___x_1190_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_val_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x3f___boxed(lean_object* v_s_1200_, lean_object* v_pos_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_String_Pos_next_x3f(v_s_1200_, v_pos_1201_);
lean_dec(v_pos_1201_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21(lean_object* v_s_1203_, lean_object* v_pos_1204_){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1205_ = lean_unsigned_to_nat(0u);
v___x_1206_ = lean_string_utf8_byte_size(v_s_1203_);
v___x_1207_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1207_, 0, v_s_1203_);
lean_ctor_set(v___x_1207_, 1, v___x_1205_);
lean_ctor_set(v___x_1207_, 2, v___x_1206_);
v___x_1208_ = l_String_Slice_Pos_next_x21(v___x_1207_, v_pos_1204_);
lean_dec_ref_known(v___x_1207_, 3);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21___boxed(lean_object* v_s_1209_, lean_object* v_pos_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_String_Pos_next_x21(v_s_1209_, v_pos_1210_);
lean_dec(v_pos_1210_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg(lean_object* v_off_1212_){
_start:
{
lean_inc(v_off_1212_);
return v_off_1212_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg___boxed(lean_object* v_off_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_String_pos___redArg(v_off_1213_);
lean_dec(v_off_1213_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_String_pos(lean_object* v_s_1215_, lean_object* v_off_1216_, lean_object* v_h_1217_){
_start:
{
lean_inc(v_off_1216_);
return v_off_1216_;
}
}
LEAN_EXPORT lean_object* l_String_pos___boxed(lean_object* v_s_1218_, lean_object* v_off_1219_, lean_object* v_h_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_String_pos(v_s_1218_, v_off_1219_, v_h_1220_);
lean_dec(v_off_1219_);
lean_dec_ref(v_s_1218_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x3f(lean_object* v_s_1222_, lean_object* v_off_1223_){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1224_ = lean_unsigned_to_nat(0u);
v___x_1225_ = lean_string_utf8_byte_size(v_s_1222_);
v___x_1226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1226_, 0, v_s_1222_);
lean_ctor_set(v___x_1226_, 1, v___x_1224_);
lean_ctor_set(v___x_1226_, 2, v___x_1225_);
v___x_1227_ = l_String_Slice_pos_x3f(v___x_1226_, v_off_1223_);
lean_dec_ref_known(v___x_1226_, 3);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v___x_1228_; 
v___x_1228_ = lean_box(0);
return v___x_1228_;
}
else
{
lean_object* v_val_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
v_val_1229_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1227_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_val_1229_);
lean_dec(v___x_1227_);
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
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_val_1229_);
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
LEAN_EXPORT lean_object* l_String_pos_x21(lean_object* v_s_1237_, lean_object* v_off_1238_){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1239_ = lean_unsigned_to_nat(0u);
v___x_1240_ = lean_string_utf8_byte_size(v_s_1237_);
v___x_1241_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1241_, 0, v_s_1237_);
lean_ctor_set(v___x_1241_, 1, v___x_1239_);
lean_ctor_set(v___x_1241_, 2, v___x_1240_);
v___x_1242_ = l_String_Slice_pos_x21(v___x_1241_, v_off_1238_);
lean_dec_ref_known(v___x_1241_, 3);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x21___boxed(lean_object* v_s_1243_, lean_object* v_off_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_String_pos_x21(v_s_1243_, v_off_1244_);
lean_dec(v_off_1244_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg(lean_object* v_pos_1246_){
_start:
{
lean_inc(v_pos_1246_);
return v_pos_1246_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg___boxed(lean_object* v_pos_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_String_Slice_Pos_cast___redArg(v_pos_1247_);
lean_dec(v_pos_1247_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast(lean_object* v_s_1249_, lean_object* v_t_1250_, lean_object* v_pos_1251_, lean_object* v_h_1252_){
_start:
{
lean_inc(v_pos_1251_);
return v_pos_1251_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___boxed(lean_object* v_s_1253_, lean_object* v_t_1254_, lean_object* v_pos_1255_, lean_object* v_h_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_String_Slice_Pos_cast(v_s_1253_, v_t_1254_, v_pos_1255_, v_h_1256_);
lean_dec(v_pos_1255_);
lean_dec_ref(v_t_1254_);
lean_dec_ref(v_s_1253_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg(lean_object* v_pos_1258_){
_start:
{
lean_inc(v_pos_1258_);
return v_pos_1258_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg___boxed(lean_object* v_pos_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_String_Pos_cast___redArg(v_pos_1259_);
lean_dec(v_pos_1259_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast(lean_object* v_s_1261_, lean_object* v_t_1262_, lean_object* v_pos_1263_, lean_object* v_h_1264_){
_start:
{
lean_inc(v_pos_1263_);
return v_pos_1263_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___boxed(lean_object* v_s_1265_, lean_object* v_t_1266_, lean_object* v_pos_1267_, lean_object* v_h_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_String_Pos_cast(v_s_1265_, v_t_1266_, v_pos_1267_, v_h_1268_);
lean_dec(v_pos_1267_);
lean_dec_ref(v_t_1266_);
lean_dec_ref(v_s_1265_);
return v_res_1269_;
}
}
uint32_t l_String_Pos_Raw_utf8GetAux(lean_object* v_x_1270_, lean_object* v_x_1271_, lean_object* v_x_1272_){
_start:
{
if (lean_obj_tag(v_x_1270_) == 0)
{
uint32_t v___x_1273_; 
lean_dec(v_x_1271_);
v___x_1273_ = 65;
return v___x_1273_;
}
else
{
lean_object* v_head_1274_; lean_object* v_tail_1275_; uint8_t v_decide_1276_; 
v_head_1274_ = lean_ctor_get(v_x_1270_, 0);
v_tail_1275_ = lean_ctor_get(v_x_1270_, 1);
v_decide_1276_ = lean_nat_dec_eq(v_x_1271_, v_x_1272_);
if (v_decide_1276_ == 0)
{
uint32_t v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1277_ = lean_unbox_uint32(v_head_1274_);
v___x_1278_ = l_Char_utf8Size(v___x_1277_);
v___x_1279_ = lean_nat_add(v_x_1271_, v___x_1278_);
lean_dec(v___x_1278_);
lean_dec(v_x_1271_);
v_x_1270_ = v_tail_1275_;
v_x_1271_ = v___x_1279_;
goto _start;
}
else
{
uint32_t v___x_1281_; 
lean_dec(v_x_1271_);
v___x_1281_ = lean_unbox_uint32(v_head_1274_);
return v___x_1281_;
}
}
}
}
LEAN_EXPORT void l_String_Pos_Raw_utf8GetAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1270_ = stack[0].m_obj;
lean_object* v_x_1271_ = stack[1].m_obj;
lean_object* v_x_1272_ = stack[2].m_obj;
uint32_t v_res_1282_;
v_res_1282_ = l_String_Pos_Raw_utf8GetAux(v_x_1270_, v_x_1271_, v_x_1272_);
stack->m_num = v_res_1282_;
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux___boxed(lean_object* v_x_1283_, lean_object* v_x_1284_, lean_object* v_x_1285_){
_start:
{
uint32_t v_res_1286_; lean_object* v_r_1287_; 
v_res_1286_ = l_String_Pos_Raw_utf8GetAux(v_x_1283_, v_x_1284_, v_x_1285_);
lean_dec(v_x_1285_);
lean_dec(v_x_1283_);
v_r_1287_ = lean_box_uint32(v_res_1286_);
return v_r_1287_;
}
}
uint32_t l_String_utf8GetAux(lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
uint32_t v___x_1291_; 
v___x_1291_ = l_String_Pos_Raw_utf8GetAux(v_a_1288_, v_a_1289_, v_a_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT void l_String_utf8GetAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1288_ = stack[0].m_obj;
lean_object* v_a_1289_ = stack[1].m_obj;
lean_object* v_a_1290_ = stack[2].m_obj;
uint32_t v_res_1292_;
v_res_1292_ = l_String_utf8GetAux(v_a_1288_, v_a_1289_, v_a_1290_);
stack->m_num = v_res_1292_;
}
LEAN_EXPORT lean_object* l_String_utf8GetAux___boxed(lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_){
_start:
{
uint32_t v_res_1296_; lean_object* v_r_1297_; 
v_res_1296_ = l_String_utf8GetAux(v_a_1293_, v_a_1294_, v_a_1295_);
lean_dec(v_a_1295_);
lean_dec(v_a_1293_);
v_r_1297_ = lean_box_uint32(v_res_1296_);
return v_r_1297_;
}
}
LEAN_EXPORT void l_String_Pos_Raw_get_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1298_ = stack[0].m_obj;
lean_object* v_p_1299_ = stack[1].m_obj;
uint32_t v_res_1300_;
v_res_1300_ = lean_string_utf8_get(v_s_1298_, v_p_1299_);
stack->m_num = v_res_1300_;
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get___boxed(lean_object* v_s_1301_, lean_object* v_p_1302_){
_start:
{
uint32_t v_res_1303_; lean_object* v_r_1304_; 
v_res_1303_ = lean_string_utf8_get(v_s_1301_, v_p_1302_);
lean_dec(v_p_1302_);
lean_dec_ref(v_s_1301_);
v_r_1304_ = lean_box_uint32(v_res_1303_);
return v_r_1304_;
}
}
LEAN_EXPORT void l_String_get_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1305_ = stack[0].m_obj;
lean_object* v_p_1306_ = stack[1].m_obj;
uint32_t v_res_1307_;
v_res_1307_ = lean_string_utf8_get(v_s_1305_, v_p_1306_);
stack->m_num = v_res_1307_;
}
LEAN_EXPORT lean_object* l_String_get___boxed(lean_object* v_s_1308_, lean_object* v_p_1309_){
_start:
{
uint32_t v_res_1310_; lean_object* v_r_1311_; 
v_res_1310_ = lean_string_utf8_get(v_s_1308_, v_p_1309_);
lean_dec(v_p_1309_);
lean_dec_ref(v_s_1308_);
v_r_1311_ = lean_box_uint32(v_res_1310_);
return v_r_1311_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f(lean_object* v_x_1312_, lean_object* v_x_1313_, lean_object* v_x_1314_){
_start:
{
if (lean_obj_tag(v_x_1312_) == 0)
{
lean_object* v___x_1315_; 
lean_dec(v_x_1313_);
v___x_1315_ = lean_box(0);
return v___x_1315_;
}
else
{
lean_object* v_head_1316_; lean_object* v_tail_1317_; uint8_t v_decide_1318_; 
v_head_1316_ = lean_ctor_get(v_x_1312_, 0);
v_tail_1317_ = lean_ctor_get(v_x_1312_, 1);
v_decide_1318_ = lean_nat_dec_eq(v_x_1313_, v_x_1314_);
if (v_decide_1318_ == 0)
{
uint32_t v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = lean_unbox_uint32(v_head_1316_);
v___x_1320_ = l_Char_utf8Size(v___x_1319_);
v___x_1321_ = lean_nat_add(v_x_1313_, v___x_1320_);
lean_dec(v___x_1320_);
lean_dec(v_x_1313_);
v_x_1312_ = v_tail_1317_;
v_x_1313_ = v___x_1321_;
goto _start;
}
else
{
lean_object* v___x_1323_; 
lean_dec(v_x_1313_);
lean_inc(v_head_1316_);
v___x_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1323_, 0, v_head_1316_);
return v___x_1323_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f___boxed(lean_object* v_x_1324_, lean_object* v_x_1325_, lean_object* v_x_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_String_Pos_Raw_utf8GetAux_x3f(v_x_1324_, v_x_1325_, v_x_1326_);
lean_dec(v_x_1326_);
lean_dec(v_x_1324_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f(lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_String_Pos_Raw_utf8GetAux_x3f(v_a_1328_, v_a_1329_, v_a_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f___boxed(lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_String_utf8GetAux_x3f(v_a_1332_, v_a_1333_, v_a_1334_);
lean_dec(v_a_1334_);
lean_dec(v_a_1332_);
return v_res_1335_;
}
}
LEAN_EXPORT void l_String_Pos_Raw_get_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_1336_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_1337_ = stack[1].m_obj;
lean_object* v_res_1338_;
v_res_1338_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1336_, v_a_00___x40___internal___hyg_1337_);
stack->m_obj
 = v_res_1338_;
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1339_, lean_object* v_a_00___x40___internal___hyg_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1339_, v_a_00___x40___internal___hyg_1340_);
lean_dec(v_a_00___x40___internal___hyg_1340_);
lean_dec_ref(v_a_00___x40___internal___hyg_1339_);
return v_res_1341_;
}
}
LEAN_EXPORT void l_String_get_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_1342_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_1343_ = stack[1].m_obj;
lean_object* v_res_1344_;
v_res_1344_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1342_, v_a_00___x40___internal___hyg_1343_);
stack->m_obj
 = v_res_1344_;
}
LEAN_EXPORT lean_object* l_String_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1345_, lean_object* v_a_00___x40___internal___hyg_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1345_, v_a_00___x40___internal___hyg_1346_);
lean_dec(v_a_00___x40___internal___hyg_1346_);
lean_dec_ref(v_a_00___x40___internal___hyg_1345_);
return v_res_1347_;
}
}
LEAN_EXPORT void l_String_Pos_Raw_get_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1348_ = stack[0].m_obj;
lean_object* v_p_1349_ = stack[1].m_obj;
uint32_t v_res_1350_;
v_res_1350_ = lean_string_utf8_get_bang(v_s_1348_, v_p_1349_);
stack->m_num = v_res_1350_;
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x21___boxed(lean_object* v_s_1351_, lean_object* v_p_1352_){
_start:
{
uint32_t v_res_1353_; lean_object* v_r_1354_; 
v_res_1353_ = lean_string_utf8_get_bang(v_s_1351_, v_p_1352_);
lean_dec(v_p_1352_);
lean_dec_ref(v_s_1351_);
v_r_1354_ = lean_box_uint32(v_res_1353_);
return v_r_1354_;
}
}
LEAN_EXPORT void l_String_get_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1355_ = stack[0].m_obj;
lean_object* v_p_1356_ = stack[1].m_obj;
uint32_t v_res_1357_;
v_res_1357_ = lean_string_utf8_get_bang(v_s_1355_, v_p_1356_);
stack->m_num = v_res_1357_;
}
LEAN_EXPORT lean_object* l_String_get_x21___boxed(lean_object* v_s_1358_, lean_object* v_p_1359_){
_start:
{
uint32_t v_res_1360_; lean_object* v_r_1361_; 
v_res_1360_ = lean_string_utf8_get_bang(v_s_1358_, v_p_1359_);
lean_dec(v_p_1359_);
lean_dec_ref(v_s_1358_);
v_r_1361_ = lean_box_uint32(v_res_1360_);
return v_r_1361_;
}
}
lean_object* l_String_Pos_Raw_utf8SetAux(uint32_t v_c_x27_1362_, lean_object* v_x_1363_, lean_object* v_x_1364_, lean_object* v_x_1365_){
_start:
{
if (lean_obj_tag(v_x_1363_) == 0)
{
return v_x_1363_;
}
else
{
lean_object* v_head_1366_; lean_object* v_tail_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1383_; 
v_head_1366_ = lean_ctor_get(v_x_1363_, 0);
v_tail_1367_ = lean_ctor_get(v_x_1363_, 1);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_x_1363_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1369_ = v_x_1363_;
v_isShared_1370_ = v_isSharedCheck_1383_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_tail_1367_);
lean_inc(v_head_1366_);
lean_dec(v_x_1363_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1383_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
uint8_t v_decide_1371_; 
v_decide_1371_ = lean_nat_dec_eq(v_x_1364_, v_x_1365_);
if (v_decide_1371_ == 0)
{
uint32_t v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1372_ = lean_unbox_uint32(v_head_1366_);
v___x_1373_ = l_Char_utf8Size(v___x_1372_);
v___x_1374_ = lean_nat_add(v_x_1364_, v___x_1373_);
lean_dec(v___x_1373_);
v___x_1375_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1362_, v_tail_1367_, v___x_1374_, v_x_1365_);
lean_dec(v___x_1374_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 1, v___x_1375_);
v___x_1377_ = v___x_1369_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_head_1366_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1381_; 
lean_dec(v_head_1366_);
v___x_1379_ = lean_box_uint32(v_c_x27_1362_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v___x_1379_);
v___x_1381_ = v___x_1369_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_tail_1367_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
}
LEAN_EXPORT void l_String_Pos_Raw_utf8SetAux_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_x27_1362_ = stack[0].m_num;
lean_object* v_x_1363_ = stack[1].m_obj;
lean_object* v_x_1364_ = stack[2].m_obj;
lean_object* v_x_1365_ = stack[3].m_obj;
lean_object* v_res_1384_;
v_res_1384_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1362_, v_x_1363_, v_x_1364_, v_x_1365_);
stack->m_obj
 = v_res_1384_;
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux___boxed(lean_object* v_c_x27_1385_, lean_object* v_x_1386_, lean_object* v_x_1387_, lean_object* v_x_1388_){
_start:
{
uint32_t v_c_x27_boxed_1389_; lean_object* v_res_1390_; 
v_c_x27_boxed_1389_ = lean_unbox_uint32(v_c_x27_1385_);
lean_dec(v_c_x27_1385_);
v_res_1390_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_boxed_1389_, v_x_1386_, v_x_1387_, v_x_1388_);
lean_dec(v_x_1388_);
lean_dec(v_x_1387_);
return v_res_1390_;
}
}
lean_object* l_String_utf8SetAux(uint32_t v_c_x27_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1391_, v_a_1392_, v_a_1393_, v_a_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT void l_String_utf8SetAux_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_x27_1391_ = stack[0].m_num;
lean_object* v_a_1392_ = stack[1].m_obj;
lean_object* v_a_1393_ = stack[2].m_obj;
lean_object* v_a_1394_ = stack[3].m_obj;
lean_object* v_res_1396_;
v_res_1396_ = l_String_utf8SetAux(v_c_x27_1391_, v_a_1392_, v_a_1393_, v_a_1394_);
stack->m_obj
 = v_res_1396_;
}
LEAN_EXPORT lean_object* l_String_utf8SetAux___boxed(lean_object* v_c_x27_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_){
_start:
{
uint32_t v_c_x27_boxed_1401_; lean_object* v_res_1402_; 
v_c_x27_boxed_1401_ = lean_unbox_uint32(v_c_x27_1397_);
lean_dec(v_c_x27_1397_);
v_res_1402_ = l_String_utf8SetAux(v_c_x27_boxed_1401_, v_a_1398_, v_a_1399_, v_a_1400_);
lean_dec(v_a_1400_);
lean_dec(v_a_1399_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg(lean_object* v_s_1403_, lean_object* v_pos_1404_){
_start:
{
lean_object* v_str_1405_; lean_object* v_startInclusive_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v_str_1405_ = lean_ctor_get(v_s_1403_, 0);
v_startInclusive_1406_ = lean_ctor_get(v_s_1403_, 1);
v___x_1407_ = lean_nat_add(v_startInclusive_1406_, v_pos_1404_);
v___x_1408_ = lean_string_utf8_next_fast(v_str_1405_, v___x_1407_);
lean_dec(v___x_1407_);
v___x_1409_ = lean_nat_sub(v___x_1408_, v_startInclusive_1406_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg___boxed(lean_object* v_s_1410_, lean_object* v_pos_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_String_Slice_Pos_nextFast___redArg(v_s_1410_, v_pos_1411_);
lean_dec(v_pos_1411_);
lean_dec_ref(v_s_1410_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast(lean_object* v_s_1413_, lean_object* v_pos_1414_, lean_object* v_h_1415_){
_start:
{
lean_object* v_str_1416_; lean_object* v_startInclusive_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v_str_1416_ = lean_ctor_get(v_s_1413_, 0);
v_startInclusive_1417_ = lean_ctor_get(v_s_1413_, 1);
v___x_1418_ = lean_nat_add(v_startInclusive_1417_, v_pos_1414_);
v___x_1419_ = lean_string_utf8_next_fast(v_str_1416_, v___x_1418_);
lean_dec(v___x_1418_);
v___x_1420_ = lean_nat_sub(v___x_1419_, v_startInclusive_1417_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___boxed(lean_object* v_s_1421_, lean_object* v_pos_1422_, lean_object* v_h_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_String_Slice_Pos_nextFast(v_s_1421_, v_pos_1422_, v_h_1423_);
lean_dec(v_pos_1422_);
lean_dec_ref(v_s_1421_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_String_sliceTo(lean_object* v_s_1425_, lean_object* v_p_1426_){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = lean_unsigned_to_nat(0u);
v___x_1428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1428_, 0, v_s_1425_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
lean_ctor_set(v___x_1428_, 2, v_p_1426_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_String_replaceEnd(lean_object* v_s_1429_, lean_object* v_p_1430_){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = lean_unsigned_to_nat(0u);
v___x_1432_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1432_, 0, v_s_1429_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
lean_ctor_set(v___x_1432_, 2, v_p_1430_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_String_sliceFrom(lean_object* v_s_1433_, lean_object* v_p_1434_){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = lean_string_utf8_byte_size(v_s_1433_);
v___x_1436_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1436_, 0, v_s_1433_);
lean_ctor_set(v___x_1436_, 1, v_p_1434_);
lean_ctor_set(v___x_1436_, 2, v___x_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStart(lean_object* v_s_1437_, lean_object* v_p_1438_){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = lean_string_utf8_byte_size(v_s_1437_);
v___x_1440_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1440_, 0, v_s_1437_);
lean_ctor_set(v___x_1440_, 1, v_p_1438_);
lean_ctor_set(v___x_1440_, 2, v___x_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_String_slice___redArg(lean_object* v_s_1441_, lean_object* v_startInclusive_1442_, lean_object* v_endExclusive_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1444_, 0, v_s_1441_);
lean_ctor_set(v___x_1444_, 1, v_startInclusive_1442_);
lean_ctor_set(v___x_1444_, 2, v_endExclusive_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_String_slice(lean_object* v_s_1445_, lean_object* v_startInclusive_1446_, lean_object* v_endExclusive_1447_, lean_object* v_h_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1449_, 0, v_s_1445_);
lean_ctor_set(v___x_1449_, 1, v_startInclusive_1446_);
lean_ctor_set(v___x_1449_, 2, v_endExclusive_1447_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x3f(lean_object* v_s_1450_, lean_object* v_startInclusive_1451_, lean_object* v_endExclusive_1452_){
_start:
{
uint8_t v___x_1453_; 
v___x_1453_ = lean_nat_dec_le(v_startInclusive_1451_, v_endExclusive_1452_);
if (v___x_1453_ == 0)
{
lean_object* v___x_1454_; 
lean_dec(v_endExclusive_1452_);
lean_dec(v_startInclusive_1451_);
lean_dec_ref(v_s_1450_);
v___x_1454_ = lean_box(0);
return v___x_1454_;
}
else
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1455_, 0, v_s_1450_);
lean_ctor_set(v___x_1455_, 1, v_startInclusive_1451_);
lean_ctor_set(v___x_1455_, 2, v_endExclusive_1452_);
v___x_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
return v___x_1456_;
}
}
}
LEAN_EXPORT lean_object* l_String_slice_x21(lean_object* v_s_1457_, lean_object* v_p_u2081_1458_, lean_object* v_p_u2082_1459_){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1460_ = lean_unsigned_to_nat(0u);
v___x_1461_ = lean_string_utf8_byte_size(v_s_1457_);
v___x_1462_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1462_, 0, v_s_1457_);
lean_ctor_set(v___x_1462_, 1, v___x_1460_);
lean_ctor_set(v___x_1462_, 2, v___x_1461_);
v___x_1463_ = l_String_Slice_slice_x21(v___x_1462_, v_p_u2081_1458_, v_p_u2082_1459_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x21___boxed(lean_object* v_s_1464_, lean_object* v_p_u2081_1465_, lean_object* v_p_u2082_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_String_slice_x21(v_s_1464_, v_p_u2081_1465_, v_p_u2082_1466_);
lean_dec(v_p_u2082_1466_);
lean_dec(v_p_u2081_1465_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21(lean_object* v_s_1468_, lean_object* v_p_u2081_1469_, lean_object* v_p_u2082_1470_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_String_slice_x21(v_s_1468_, v_p_u2081_1469_, v_p_u2082_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21___boxed(lean_object* v_s_1472_, lean_object* v_p_u2081_1473_, lean_object* v_p_u2082_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_String_replaceStartEnd_x21(v_s_1472_, v_p_u2081_1473_, v_p_u2082_1474_);
lean_dec(v_p_u2082_1474_);
lean_dec(v_p_u2081_1473_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg(lean_object* v_p_u2080_1476_, lean_object* v_pos_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = lean_nat_add(v_p_u2080_1476_, v_pos_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg___boxed(lean_object* v_p_u2080_1479_, lean_object* v_pos_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_String_Pos_ofSliceFrom___redArg(v_p_u2080_1479_, v_pos_1480_);
lean_dec(v_pos_1480_);
lean_dec(v_p_u2080_1479_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom(lean_object* v_s_1482_, lean_object* v_p_u2080_1483_, lean_object* v_pos_1484_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = lean_nat_add(v_p_u2080_1483_, v_pos_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___boxed(lean_object* v_s_1486_, lean_object* v_p_u2080_1487_, lean_object* v_pos_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_String_Pos_ofSliceFrom(v_s_1486_, v_p_u2080_1487_, v_pos_1488_);
lean_dec(v_pos_1488_);
lean_dec(v_p_u2080_1487_);
lean_dec_ref(v_s_1486_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg(lean_object* v_p_u2080_1490_, lean_object* v_pos_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = lean_nat_add(v_p_u2080_1490_, v_pos_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg___boxed(lean_object* v_p_u2080_1493_, lean_object* v_pos_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_String_Pos_ofReplaceStart___redArg(v_p_u2080_1493_, v_pos_1494_);
lean_dec(v_pos_1494_);
lean_dec(v_p_u2080_1493_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart(lean_object* v_s_1496_, lean_object* v_p_u2080_1497_, lean_object* v_pos_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_nat_add(v_p_u2080_1497_, v_pos_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___boxed(lean_object* v_s_1500_, lean_object* v_p_u2080_1501_, lean_object* v_pos_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_String_Pos_ofReplaceStart(v_s_1500_, v_p_u2080_1501_, v_pos_1502_);
lean_dec(v_pos_1502_);
lean_dec(v_p_u2080_1501_);
lean_dec_ref(v_s_1500_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg(lean_object* v_p_u2080_1504_, lean_object* v_pos_1505_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_nat_sub(v_pos_1505_, v_p_u2080_1504_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg___boxed(lean_object* v_p_u2080_1507_, lean_object* v_pos_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_String_Pos_sliceFrom___redArg(v_p_u2080_1507_, v_pos_1508_);
lean_dec(v_pos_1508_);
lean_dec(v_p_u2080_1507_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom(lean_object* v_s_1510_, lean_object* v_p_u2080_1511_, lean_object* v_pos_1512_, lean_object* v_h_1513_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_nat_sub(v_pos_1512_, v_p_u2080_1511_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___boxed(lean_object* v_s_1515_, lean_object* v_p_u2080_1516_, lean_object* v_pos_1517_, lean_object* v_h_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_String_Pos_sliceFrom(v_s_1515_, v_p_u2080_1516_, v_pos_1517_, v_h_1518_);
lean_dec(v_pos_1517_);
lean_dec(v_p_u2080_1516_);
lean_dec_ref(v_s_1515_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg(lean_object* v_p_u2080_1520_, lean_object* v_pos_1521_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_nat_sub(v_pos_1521_, v_p_u2080_1520_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg___boxed(lean_object* v_p_u2080_1523_, lean_object* v_pos_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_String_Pos_toReplaceStart___redArg(v_p_u2080_1523_, v_pos_1524_);
lean_dec(v_pos_1524_);
lean_dec(v_p_u2080_1523_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart(lean_object* v_s_1526_, lean_object* v_p_u2080_1527_, lean_object* v_pos_1528_, lean_object* v_h_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_nat_sub(v_pos_1528_, v_p_u2080_1527_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___boxed(lean_object* v_s_1531_, lean_object* v_p_u2080_1532_, lean_object* v_pos_1533_, lean_object* v_h_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_String_Pos_toReplaceStart(v_s_1531_, v_p_u2080_1532_, v_pos_1533_, v_h_1534_);
lean_dec(v_pos_1533_);
lean_dec(v_p_u2080_1532_);
lean_dec_ref(v_s_1531_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg(lean_object* v_pos_1536_){
_start:
{
lean_inc(v_pos_1536_);
return v_pos_1536_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg___boxed(lean_object* v_pos_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_String_Pos_ofSliceTo___redArg(v_pos_1537_);
lean_dec(v_pos_1537_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo(lean_object* v_s_1539_, lean_object* v_p_u2080_1540_, lean_object* v_pos_1541_){
_start:
{
lean_inc(v_pos_1541_);
return v_pos_1541_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___boxed(lean_object* v_s_1542_, lean_object* v_p_u2080_1543_, lean_object* v_pos_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_String_Pos_ofSliceTo(v_s_1542_, v_p_u2080_1543_, v_pos_1544_);
lean_dec(v_pos_1544_);
lean_dec(v_p_u2080_1543_);
lean_dec_ref(v_s_1542_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg(lean_object* v_pos_1546_){
_start:
{
lean_inc(v_pos_1546_);
return v_pos_1546_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg___boxed(lean_object* v_pos_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_String_Pos_ofReplaceEnd___redArg(v_pos_1547_);
lean_dec(v_pos_1547_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd(lean_object* v_s_1549_, lean_object* v_p_u2080_1550_, lean_object* v_pos_1551_){
_start:
{
lean_inc(v_pos_1551_);
return v_pos_1551_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___boxed(lean_object* v_s_1552_, lean_object* v_p_u2080_1553_, lean_object* v_pos_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_String_Pos_ofReplaceEnd(v_s_1552_, v_p_u2080_1553_, v_pos_1554_);
lean_dec(v_pos_1554_);
lean_dec(v_p_u2080_1553_);
lean_dec_ref(v_s_1552_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg(lean_object* v_pos_1556_){
_start:
{
lean_inc(v_pos_1556_);
return v_pos_1556_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg___boxed(lean_object* v_pos_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_String_Pos_sliceTo___redArg(v_pos_1557_);
lean_dec(v_pos_1557_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo(lean_object* v_s_1559_, lean_object* v_p_u2080_1560_, lean_object* v_pos_1561_, lean_object* v_h_1562_){
_start:
{
lean_inc(v_pos_1561_);
return v_pos_1561_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___boxed(lean_object* v_s_1563_, lean_object* v_p_u2080_1564_, lean_object* v_pos_1565_, lean_object* v_h_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_String_Pos_sliceTo(v_s_1563_, v_p_u2080_1564_, v_pos_1565_, v_h_1566_);
lean_dec(v_pos_1565_);
lean_dec(v_p_u2080_1564_);
lean_dec_ref(v_s_1563_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg(lean_object* v_pos_1568_){
_start:
{
lean_inc(v_pos_1568_);
return v_pos_1568_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg___boxed(lean_object* v_pos_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_String_Pos_toReplaceEnd___redArg(v_pos_1569_);
lean_dec(v_pos_1569_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd(lean_object* v_s_1571_, lean_object* v_p_u2080_1572_, lean_object* v_pos_1573_, lean_object* v_h_1574_){
_start:
{
lean_inc(v_pos_1573_);
return v_pos_1573_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___boxed(lean_object* v_s_1575_, lean_object* v_p_u2080_1576_, lean_object* v_pos_1577_, lean_object* v_h_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_String_Pos_toReplaceEnd(v_s_1575_, v_p_u2080_1576_, v_pos_1577_, v_h_1578_);
lean_dec(v_pos_1577_);
lean_dec(v_p_u2080_1576_);
lean_dec_ref(v_s_1575_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg(lean_object* v_p_u2080_1580_, lean_object* v_pos_1581_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_nat_add(v_p_u2080_1580_, v_pos_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1583_, lean_object* v_pos_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_String_Slice_Pos_ofSlice___redArg(v_p_u2080_1583_, v_pos_1584_);
lean_dec(v_pos_1584_);
lean_dec(v_p_u2080_1583_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice(lean_object* v_s_1586_, lean_object* v_p_u2080_1587_, lean_object* v_p_u2081_1588_, lean_object* v_h_1589_, lean_object* v_pos_1590_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = lean_nat_add(v_p_u2080_1587_, v_pos_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___boxed(lean_object* v_s_1592_, lean_object* v_p_u2080_1593_, lean_object* v_p_u2081_1594_, lean_object* v_h_1595_, lean_object* v_pos_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_String_Slice_Pos_ofSlice(v_s_1592_, v_p_u2080_1593_, v_p_u2081_1594_, v_h_1595_, v_pos_1596_);
lean_dec(v_pos_1596_);
lean_dec(v_p_u2081_1594_);
lean_dec(v_p_u2080_1593_);
lean_dec_ref(v_s_1592_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg(lean_object* v_p_u2080_1598_, lean_object* v_pos_1599_){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = lean_nat_add(v_p_u2080_1598_, v_pos_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1601_, lean_object* v_pos_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_String_Pos_ofSlice___redArg(v_p_u2080_1601_, v_pos_1602_);
lean_dec(v_pos_1602_);
lean_dec(v_p_u2080_1601_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice(lean_object* v_s_1604_, lean_object* v_p_u2080_1605_, lean_object* v_p_u2081_1606_, lean_object* v_h_1607_, lean_object* v_pos_1608_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = lean_nat_add(v_p_u2080_1605_, v_pos_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___boxed(lean_object* v_s_1610_, lean_object* v_p_u2080_1611_, lean_object* v_p_u2081_1612_, lean_object* v_h_1613_, lean_object* v_pos_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_String_Pos_ofSlice(v_s_1610_, v_p_u2080_1611_, v_p_u2081_1612_, v_h_1613_, v_pos_1614_);
lean_dec(v_pos_1614_);
lean_dec(v_p_u2081_1612_);
lean_dec(v_p_u2080_1611_);
lean_dec_ref(v_s_1610_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg(lean_object* v_pos_1616_, lean_object* v_p_u2080_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_nat_sub(v_pos_1616_, v_p_u2080_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg___boxed(lean_object* v_pos_1619_, lean_object* v_p_u2080_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_String_Slice_Pos_slice___redArg(v_pos_1619_, v_p_u2080_1620_);
lean_dec(v_p_u2080_1620_);
lean_dec(v_pos_1619_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice(lean_object* v_s_1622_, lean_object* v_pos_1623_, lean_object* v_p_u2080_1624_, lean_object* v_p_u2081_1625_, lean_object* v_h_u2081_1626_, lean_object* v_h_u2082_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = lean_nat_sub(v_pos_1623_, v_p_u2080_1624_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___boxed(lean_object* v_s_1629_, lean_object* v_pos_1630_, lean_object* v_p_u2080_1631_, lean_object* v_p_u2081_1632_, lean_object* v_h_u2081_1633_, lean_object* v_h_u2082_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_String_Slice_Pos_slice(v_s_1629_, v_pos_1630_, v_p_u2080_1631_, v_p_u2081_1632_, v_h_u2081_1633_, v_h_u2082_1634_);
lean_dec(v_p_u2081_1632_);
lean_dec(v_p_u2080_1631_);
lean_dec(v_pos_1630_);
lean_dec_ref(v_s_1629_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg(lean_object* v_pos_1636_, lean_object* v_p_u2080_1637_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = lean_nat_sub(v_pos_1636_, v_p_u2080_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg___boxed(lean_object* v_pos_1639_, lean_object* v_p_u2080_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_String_Pos_slice___redArg(v_pos_1639_, v_p_u2080_1640_);
lean_dec(v_p_u2080_1640_);
lean_dec(v_pos_1639_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice(lean_object* v_s_1642_, lean_object* v_pos_1643_, lean_object* v_p_u2080_1644_, lean_object* v_p_u2081_1645_, lean_object* v_h_u2081_1646_, lean_object* v_h_u2082_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_nat_sub(v_pos_1643_, v_p_u2080_1644_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___boxed(lean_object* v_s_1649_, lean_object* v_pos_1650_, lean_object* v_p_u2080_1651_, lean_object* v_p_u2081_1652_, lean_object* v_h_u2081_1653_, lean_object* v_h_u2082_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_String_Pos_slice(v_s_1649_, v_pos_1650_, v_p_u2080_1651_, v_p_u2081_1652_, v_h_u2081_1653_, v_h_u2082_1654_);
lean_dec(v_p_u2081_1652_);
lean_dec(v_p_u2080_1651_);
lean_dec(v_pos_1650_);
lean_dec_ref(v_s_1649_);
return v_res_1655_;
}
}
static lean_object* _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1658_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__1));
v___x_1659_ = lean_unsigned_to_nat(4u);
v___x_1660_ = lean_unsigned_to_nat(2621u);
v___x_1661_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__0));
v___x_1662_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1663_ = l_mkPanicMessageWithDecl(v___x_1662_, v___x_1661_, v___x_1660_, v___x_1659_, v___x_1658_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg(lean_object* v_pos_1664_, lean_object* v_p_u2080_1665_, lean_object* v_p_u2081_1666_){
_start:
{
uint8_t v___y_1668_; uint8_t v___x_1673_; 
v___x_1673_ = lean_nat_dec_le(v_p_u2080_1665_, v_pos_1664_);
if (v___x_1673_ == 0)
{
v___y_1668_ = v___x_1673_;
goto v___jp_1667_;
}
else
{
uint8_t v___x_1674_; 
v___x_1674_ = lean_nat_dec_le(v_pos_1664_, v_p_u2081_1666_);
v___y_1668_ = v___x_1674_;
goto v___jp_1667_;
}
v___jp_1667_:
{
if (v___y_1668_ == 0)
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = lean_unsigned_to_nat(0u);
v___x_1670_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1671_ = l_panic___redArg(v___x_1669_, v___x_1670_);
return v___x_1671_;
}
else
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_nat_sub(v_pos_1664_, v_p_u2080_1665_);
return v___x_1672_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1675_, lean_object* v_p_u2080_1676_, lean_object* v_p_u2081_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_String_Slice_Pos_sliceOrPanic___redArg(v_pos_1675_, v_p_u2080_1676_, v_p_u2081_1677_);
lean_dec(v_p_u2081_1677_);
lean_dec(v_p_u2080_1676_);
lean_dec(v_pos_1675_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic(lean_object* v_s_1679_, lean_object* v_pos_1680_, lean_object* v_p_u2080_1681_, lean_object* v_p_u2081_1682_, lean_object* v_h_1683_){
_start:
{
uint8_t v___y_1685_; uint8_t v___x_1690_; 
v___x_1690_ = lean_nat_dec_le(v_p_u2080_1681_, v_pos_1680_);
if (v___x_1690_ == 0)
{
v___y_1685_ = v___x_1690_;
goto v___jp_1684_;
}
else
{
uint8_t v___x_1691_; 
v___x_1691_ = lean_nat_dec_le(v_pos_1680_, v_p_u2081_1682_);
v___y_1685_ = v___x_1691_;
goto v___jp_1684_;
}
v___jp_1684_:
{
if (v___y_1685_ == 0)
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = lean_unsigned_to_nat(0u);
v___x_1687_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1688_ = l_panic___redArg(v___x_1686_, v___x_1687_);
return v___x_1688_;
}
else
{
lean_object* v___x_1689_; 
v___x_1689_ = lean_nat_sub(v_pos_1680_, v_p_u2080_1681_);
return v___x_1689_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___boxed(lean_object* v_s_1692_, lean_object* v_pos_1693_, lean_object* v_p_u2080_1694_, lean_object* v_p_u2081_1695_, lean_object* v_h_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_String_Slice_Pos_sliceOrPanic(v_s_1692_, v_pos_1693_, v_p_u2080_1694_, v_p_u2081_1695_, v_h_1696_);
lean_dec(v_p_u2081_1695_);
lean_dec(v_p_u2080_1694_);
lean_dec(v_pos_1693_);
lean_dec_ref(v_s_1692_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg(lean_object* v_pos_1698_, lean_object* v_p_u2080_1699_, lean_object* v_p_u2081_1700_){
_start:
{
uint8_t v___y_1702_; uint8_t v___x_1707_; 
v___x_1707_ = lean_nat_dec_le(v_p_u2080_1699_, v_pos_1698_);
if (v___x_1707_ == 0)
{
v___y_1702_ = v___x_1707_;
goto v___jp_1701_;
}
else
{
uint8_t v___x_1708_; 
v___x_1708_ = lean_nat_dec_le(v_pos_1698_, v_p_u2081_1700_);
v___y_1702_ = v___x_1708_;
goto v___jp_1701_;
}
v___jp_1701_:
{
if (v___y_1702_ == 0)
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1703_ = lean_unsigned_to_nat(0u);
v___x_1704_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1705_ = l_panic___redArg(v___x_1703_, v___x_1704_);
return v___x_1705_;
}
else
{
lean_object* v___x_1706_; 
v___x_1706_ = lean_nat_sub(v_pos_1698_, v_p_u2080_1699_);
return v___x_1706_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1709_, lean_object* v_p_u2080_1710_, lean_object* v_p_u2081_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_String_Pos_sliceOrPanic___redArg(v_pos_1709_, v_p_u2080_1710_, v_p_u2081_1711_);
lean_dec(v_p_u2081_1711_);
lean_dec(v_p_u2080_1710_);
lean_dec(v_pos_1709_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic(lean_object* v_s_1713_, lean_object* v_pos_1714_, lean_object* v_p_u2080_1715_, lean_object* v_p_u2081_1716_, lean_object* v_h_1717_){
_start:
{
uint8_t v___y_1719_; uint8_t v___x_1724_; 
v___x_1724_ = lean_nat_dec_le(v_p_u2080_1715_, v_pos_1714_);
if (v___x_1724_ == 0)
{
v___y_1719_ = v___x_1724_;
goto v___jp_1718_;
}
else
{
uint8_t v___x_1725_; 
v___x_1725_ = lean_nat_dec_le(v_pos_1714_, v_p_u2081_1716_);
v___y_1719_ = v___x_1725_;
goto v___jp_1718_;
}
v___jp_1718_:
{
if (v___y_1719_ == 0)
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1720_ = lean_unsigned_to_nat(0u);
v___x_1721_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1722_ = l_panic___redArg(v___x_1720_, v___x_1721_);
return v___x_1722_;
}
else
{
lean_object* v___x_1723_; 
v___x_1723_ = lean_nat_sub(v_pos_1714_, v_p_u2080_1715_);
return v___x_1723_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___boxed(lean_object* v_s_1726_, lean_object* v_pos_1727_, lean_object* v_p_u2080_1728_, lean_object* v_p_u2081_1729_, lean_object* v_h_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_String_Pos_sliceOrPanic(v_s_1726_, v_pos_1727_, v_p_u2080_1728_, v_p_u2081_1729_, v_h_1730_);
lean_dec(v_p_u2081_1729_);
lean_dec(v_p_u2080_1728_);
lean_dec(v_pos_1727_);
lean_dec_ref(v_s_1726_);
return v_res_1731_;
}
}
static lean_object* _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1733_ = ((lean_object*)(l_String_Slice_slice_x21___closed__1));
v___x_1734_ = lean_unsigned_to_nat(4u);
v___x_1735_ = lean_unsigned_to_nat(2645u);
v___x_1736_ = ((lean_object*)(l_String_Slice_Pos_ofSlice_x21___redArg___closed__0));
v___x_1737_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1738_ = l_mkPanicMessageWithDecl(v___x_1737_, v___x_1736_, v___x_1735_, v___x_1734_, v___x_1733_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1739_, lean_object* v_p_u2081_1740_, lean_object* v_pos_1741_){
_start:
{
uint8_t v___x_1742_; 
v___x_1742_ = lean_nat_dec_le(v_p_u2080_1739_, v_p_u2081_1740_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1743_ = lean_unsigned_to_nat(0u);
v___x_1744_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1745_ = l_panic___redArg(v___x_1743_, v___x_1744_);
return v___x_1745_;
}
else
{
lean_object* v___x_1746_; 
v___x_1746_ = lean_nat_add(v_p_u2080_1739_, v_pos_1741_);
return v___x_1746_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1747_, lean_object* v_p_u2081_1748_, lean_object* v_pos_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_String_Slice_Pos_ofSlice_x21___redArg(v_p_u2080_1747_, v_p_u2081_1748_, v_pos_1749_);
lean_dec(v_pos_1749_);
lean_dec(v_p_u2081_1748_);
lean_dec(v_p_u2080_1747_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21(lean_object* v_s_1751_, lean_object* v_p_u2080_1752_, lean_object* v_p_u2081_1753_, lean_object* v_pos_1754_){
_start:
{
uint8_t v___x_1755_; 
v___x_1755_ = lean_nat_dec_le(v_p_u2080_1752_, v_p_u2081_1753_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1756_ = lean_unsigned_to_nat(0u);
v___x_1757_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1758_ = l_panic___redArg(v___x_1756_, v___x_1757_);
return v___x_1758_;
}
else
{
lean_object* v___x_1759_; 
v___x_1759_ = lean_nat_add(v_p_u2080_1752_, v_pos_1754_);
return v___x_1759_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___boxed(lean_object* v_s_1760_, lean_object* v_p_u2080_1761_, lean_object* v_p_u2081_1762_, lean_object* v_pos_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_String_Slice_Pos_ofSlice_x21(v_s_1760_, v_p_u2080_1761_, v_p_u2081_1762_, v_pos_1763_);
lean_dec(v_pos_1763_);
lean_dec(v_p_u2081_1762_);
lean_dec(v_p_u2080_1761_);
lean_dec_ref(v_s_1760_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1765_, lean_object* v_p_u2081_1766_, lean_object* v_pos_1767_){
_start:
{
uint8_t v___x_1768_; 
v___x_1768_ = lean_nat_dec_le(v_p_u2080_1765_, v_p_u2081_1766_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1769_ = lean_unsigned_to_nat(0u);
v___x_1770_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1771_ = l_panic___redArg(v___x_1769_, v___x_1770_);
return v___x_1771_;
}
else
{
lean_object* v___x_1772_; 
v___x_1772_ = lean_nat_add(v_p_u2080_1765_, v_pos_1767_);
return v___x_1772_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1773_, lean_object* v_p_u2081_1774_, lean_object* v_pos_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_String_Pos_ofSlice_x21___redArg(v_p_u2080_1773_, v_p_u2081_1774_, v_pos_1775_);
lean_dec(v_pos_1775_);
lean_dec(v_p_u2081_1774_);
lean_dec(v_p_u2080_1773_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21(lean_object* v_s_1777_, lean_object* v_p_u2080_1778_, lean_object* v_p_u2081_1779_, lean_object* v_pos_1780_){
_start:
{
uint8_t v___x_1781_; 
v___x_1781_ = lean_nat_dec_le(v_p_u2080_1778_, v_p_u2081_1779_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1782_ = lean_unsigned_to_nat(0u);
v___x_1783_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1784_ = l_panic___redArg(v___x_1782_, v___x_1783_);
return v___x_1784_;
}
else
{
lean_object* v___x_1785_; 
v___x_1785_ = lean_nat_add(v_p_u2080_1778_, v_pos_1780_);
return v___x_1785_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___boxed(lean_object* v_s_1786_, lean_object* v_p_u2080_1787_, lean_object* v_p_u2081_1788_, lean_object* v_pos_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_String_Pos_ofSlice_x21(v_s_1786_, v_p_u2080_1787_, v_p_u2081_1788_, v_pos_1789_);
lean_dec(v_pos_1789_);
lean_dec(v_p_u2081_1788_);
lean_dec(v_p_u2080_1787_);
lean_dec_ref(v_s_1786_);
return v_res_1790_;
}
}
static lean_object* _init_l_String_Slice_Pos_slice_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1793_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__1));
v___x_1794_ = lean_unsigned_to_nat(4u);
v___x_1795_ = lean_unsigned_to_nat(2663u);
v___x_1796_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__0));
v___x_1797_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1798_ = l_mkPanicMessageWithDecl(v___x_1797_, v___x_1796_, v___x_1795_, v___x_1794_, v___x_1793_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg(lean_object* v_pos_1799_, lean_object* v_p_u2080_1800_, lean_object* v_p_u2081_1801_){
_start:
{
uint8_t v___y_1803_; uint8_t v___x_1808_; 
v___x_1808_ = lean_nat_dec_le(v_p_u2080_1800_, v_pos_1799_);
if (v___x_1808_ == 0)
{
v___y_1803_ = v___x_1808_;
goto v___jp_1802_;
}
else
{
uint8_t v___x_1809_; 
v___x_1809_ = lean_nat_dec_le(v_pos_1799_, v_p_u2081_1801_);
v___y_1803_ = v___x_1809_;
goto v___jp_1802_;
}
v___jp_1802_:
{
if (v___y_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = lean_unsigned_to_nat(0u);
v___x_1805_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1806_ = l_panic___redArg(v___x_1804_, v___x_1805_);
return v___x_1806_;
}
else
{
lean_object* v___x_1807_; 
v___x_1807_ = lean_nat_sub(v_pos_1799_, v_p_u2080_1800_);
return v___x_1807_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1810_, lean_object* v_p_u2080_1811_, lean_object* v_p_u2081_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_String_Slice_Pos_slice_x21___redArg(v_pos_1810_, v_p_u2080_1811_, v_p_u2081_1812_);
lean_dec(v_p_u2081_1812_);
lean_dec(v_p_u2080_1811_);
lean_dec(v_pos_1810_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21(lean_object* v_s_1814_, lean_object* v_pos_1815_, lean_object* v_p_u2080_1816_, lean_object* v_p_u2081_1817_){
_start:
{
uint8_t v___y_1819_; uint8_t v___x_1824_; 
v___x_1824_ = lean_nat_dec_le(v_p_u2080_1816_, v_pos_1815_);
if (v___x_1824_ == 0)
{
v___y_1819_ = v___x_1824_;
goto v___jp_1818_;
}
else
{
uint8_t v___x_1825_; 
v___x_1825_ = lean_nat_dec_le(v_pos_1815_, v_p_u2081_1817_);
v___y_1819_ = v___x_1825_;
goto v___jp_1818_;
}
v___jp_1818_:
{
if (v___y_1819_ == 0)
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = lean_unsigned_to_nat(0u);
v___x_1821_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1822_ = l_panic___redArg(v___x_1820_, v___x_1821_);
return v___x_1822_;
}
else
{
lean_object* v___x_1823_; 
v___x_1823_ = lean_nat_sub(v_pos_1815_, v_p_u2080_1816_);
return v___x_1823_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___boxed(lean_object* v_s_1826_, lean_object* v_pos_1827_, lean_object* v_p_u2080_1828_, lean_object* v_p_u2081_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_String_Slice_Pos_slice_x21(v_s_1826_, v_pos_1827_, v_p_u2080_1828_, v_p_u2081_1829_);
lean_dec(v_p_u2081_1829_);
lean_dec(v_p_u2080_1828_);
lean_dec(v_pos_1827_);
lean_dec_ref(v_s_1826_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg(lean_object* v_pos_1831_, lean_object* v_p_u2080_1832_, lean_object* v_p_u2081_1833_){
_start:
{
uint8_t v___y_1835_; uint8_t v___x_1840_; 
v___x_1840_ = lean_nat_dec_le(v_p_u2080_1832_, v_pos_1831_);
if (v___x_1840_ == 0)
{
v___y_1835_ = v___x_1840_;
goto v___jp_1834_;
}
else
{
uint8_t v___x_1841_; 
v___x_1841_ = lean_nat_dec_le(v_pos_1831_, v_p_u2081_1833_);
v___y_1835_ = v___x_1841_;
goto v___jp_1834_;
}
v___jp_1834_:
{
if (v___y_1835_ == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1836_ = lean_unsigned_to_nat(0u);
v___x_1837_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1838_ = l_panic___redArg(v___x_1836_, v___x_1837_);
return v___x_1838_;
}
else
{
lean_object* v___x_1839_; 
v___x_1839_ = lean_nat_sub(v_pos_1831_, v_p_u2080_1832_);
return v___x_1839_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1842_, lean_object* v_p_u2080_1843_, lean_object* v_p_u2081_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_String_Pos_slice_x21___redArg(v_pos_1842_, v_p_u2080_1843_, v_p_u2081_1844_);
lean_dec(v_p_u2081_1844_);
lean_dec(v_p_u2080_1843_);
lean_dec(v_pos_1842_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21(lean_object* v_s_1846_, lean_object* v_pos_1847_, lean_object* v_p_u2080_1848_, lean_object* v_p_u2081_1849_){
_start:
{
uint8_t v___y_1851_; uint8_t v___x_1856_; 
v___x_1856_ = lean_nat_dec_le(v_p_u2080_1848_, v_pos_1847_);
if (v___x_1856_ == 0)
{
v___y_1851_ = v___x_1856_;
goto v___jp_1850_;
}
else
{
uint8_t v___x_1857_; 
v___x_1857_ = lean_nat_dec_le(v_pos_1847_, v_p_u2081_1849_);
v___y_1851_ = v___x_1857_;
goto v___jp_1850_;
}
v___jp_1850_:
{
if (v___y_1851_ == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = lean_unsigned_to_nat(0u);
v___x_1853_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1854_ = l_panic___redArg(v___x_1852_, v___x_1853_);
return v___x_1854_;
}
else
{
lean_object* v___x_1855_; 
v___x_1855_ = lean_nat_sub(v_pos_1847_, v_p_u2080_1848_);
return v___x_1855_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___boxed(lean_object* v_s_1858_, lean_object* v_pos_1859_, lean_object* v_p_u2080_1860_, lean_object* v_p_u2081_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_String_Pos_slice_x21(v_s_1858_, v_pos_1859_, v_p_u2080_1860_, v_p_u2081_1861_);
lean_dec(v_p_u2081_1861_);
lean_dec(v_p_u2080_1860_);
lean_dec(v_pos_1859_);
lean_dec_ref(v_s_1858_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract(lean_object* v_s_1863_, lean_object* v_p_u2080_1864_, lean_object* v_p_u2081_1865_){
_start:
{
lean_object* v_str_1866_; lean_object* v_startInclusive_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v_str_1866_ = lean_ctor_get(v_s_1863_, 0);
v_startInclusive_1867_ = lean_ctor_get(v_s_1863_, 1);
v___x_1868_ = lean_nat_add(v_startInclusive_1867_, v_p_u2080_1864_);
v___x_1869_ = lean_nat_add(v_startInclusive_1867_, v_p_u2081_1865_);
v___x_1870_ = lean_string_utf8_extract_fast(v_str_1866_, v___x_1868_, v___x_1869_);
lean_dec(v___x_1869_);
lean_dec(v___x_1868_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract___boxed(lean_object* v_s_1871_, lean_object* v_p_u2080_1872_, lean_object* v_p_u2081_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_String_Slice_extract(v_s_1871_, v_p_u2080_1872_, v_p_u2081_1873_);
lean_dec(v_p_u2081_1873_);
lean_dec(v_p_u2080_1872_);
lean_dec_ref(v_s_1871_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn(lean_object* v_s_1875_, lean_object* v_p_1876_, lean_object* v_n_1877_){
_start:
{
lean_object* v_zero_1878_; uint8_t v_isZero_1879_; 
v_zero_1878_ = lean_unsigned_to_nat(0u);
v_isZero_1879_ = lean_nat_dec_eq(v_n_1877_, v_zero_1878_);
if (v_isZero_1879_ == 1)
{
lean_dec(v_n_1877_);
return v_p_1876_;
}
else
{
lean_object* v_str_1880_; lean_object* v_startInclusive_1881_; lean_object* v_endExclusive_1882_; lean_object* v_one_1883_; lean_object* v_n_1884_; lean_object* v___x_1890_; uint8_t v_decide_1891_; 
v_str_1880_ = lean_ctor_get(v_s_1875_, 0);
v_startInclusive_1881_ = lean_ctor_get(v_s_1875_, 1);
v_endExclusive_1882_ = lean_ctor_get(v_s_1875_, 2);
v_one_1883_ = lean_unsigned_to_nat(1u);
v_n_1884_ = lean_nat_sub(v_n_1877_, v_one_1883_);
lean_dec(v_n_1877_);
v___x_1890_ = lean_nat_sub(v_endExclusive_1882_, v_startInclusive_1881_);
v_decide_1891_ = lean_nat_dec_eq(v_p_1876_, v___x_1890_);
lean_dec(v___x_1890_);
if (v_decide_1891_ == 0)
{
goto v___jp_1885_;
}
else
{
if (v_isZero_1879_ == 0)
{
lean_dec(v_n_1884_);
return v_p_1876_;
}
else
{
goto v___jp_1885_;
}
}
v___jp_1885_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1886_ = lean_nat_add(v_startInclusive_1881_, v_p_1876_);
lean_dec(v_p_1876_);
v___x_1887_ = lean_string_utf8_next_fast(v_str_1880_, v___x_1886_);
lean_dec(v___x_1886_);
v___x_1888_ = lean_nat_sub(v___x_1887_, v_startInclusive_1881_);
v_p_1876_ = v___x_1888_;
v_n_1877_ = v_n_1884_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn___boxed(lean_object* v_s_1892_, lean_object* v_p_1893_, lean_object* v_n_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_String_Slice_Pos_nextn(v_s_1892_, v_p_1893_, v_n_1894_);
lean_dec_ref(v_s_1892_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_nextn(lean_object* v_s_1896_, lean_object* v_p_1897_, lean_object* v_n_1898_){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1899_ = lean_unsigned_to_nat(0u);
v___x_1900_ = lean_string_utf8_byte_size(v_s_1896_);
v___x_1901_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1901_, 0, v_s_1896_);
lean_ctor_set(v___x_1901_, 1, v___x_1899_);
lean_ctor_set(v___x_1901_, 2, v___x_1900_);
v___x_1902_ = l_String_Slice_Pos_nextn(v___x_1901_, v_p_1897_, v_n_1898_);
lean_dec_ref_known(v___x_1901_, 3);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(lean_object* v_n_1903_, lean_object* v_h__1_1904_, lean_object* v_h__2_1905_){
_start:
{
lean_object* v_zero_1906_; uint8_t v_isZero_1907_; 
v_zero_1906_ = lean_unsigned_to_nat(0u);
v_isZero_1907_ = lean_nat_dec_eq(v_n_1903_, v_zero_1906_);
if (v_isZero_1907_ == 1)
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
lean_dec(v_h__2_1905_);
v___x_1908_ = lean_box(0);
v___x_1909_ = lean_apply_1(v_h__1_1904_, v___x_1908_);
return v___x_1909_;
}
else
{
lean_object* v_one_1910_; lean_object* v_n_1911_; lean_object* v___x_1912_; 
lean_dec(v_h__1_1904_);
v_one_1910_ = lean_unsigned_to_nat(1u);
v_n_1911_ = lean_nat_sub(v_n_1903_, v_one_1910_);
v___x_1912_ = lean_apply_1(v_h__2_1905_, v_n_1911_);
return v___x_1912_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg___boxed(lean_object* v_n_1913_, lean_object* v_h__1_1914_, lean_object* v_h__2_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(v_n_1913_, v_h__1_1914_, v_h__2_1915_);
lean_dec(v_n_1913_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(lean_object* v_motive_1917_, lean_object* v_n_1918_, lean_object* v_h__1_1919_, lean_object* v_h__2_1920_){
_start:
{
lean_object* v_zero_1921_; uint8_t v_isZero_1922_; 
v_zero_1921_ = lean_unsigned_to_nat(0u);
v_isZero_1922_ = lean_nat_dec_eq(v_n_1918_, v_zero_1921_);
if (v_isZero_1922_ == 1)
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
lean_dec(v_h__2_1920_);
v___x_1923_ = lean_box(0);
v___x_1924_ = lean_apply_1(v_h__1_1919_, v___x_1923_);
return v___x_1924_;
}
else
{
lean_object* v_one_1925_; lean_object* v_n_1926_; lean_object* v___x_1927_; 
lean_dec(v_h__1_1919_);
v_one_1925_ = lean_unsigned_to_nat(1u);
v_n_1926_ = lean_nat_sub(v_n_1918_, v_one_1925_);
v___x_1927_ = lean_apply_1(v_h__2_1920_, v_n_1926_);
return v___x_1927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___boxed(lean_object* v_motive_1928_, lean_object* v_n_1929_, lean_object* v_h__1_1930_, lean_object* v_h__2_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(v_motive_1928_, v_n_1929_, v_h__1_1930_, v_h__2_1931_);
lean_dec(v_n_1929_);
return v_res_1932_;
}
}
LEAN_EXPORT void l_String_Pos_Raw_next_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1933_ = stack[0].m_obj;
lean_object* v_p_1934_ = stack[1].m_obj;
lean_object* v_res_1935_;
v_res_1935_ = lean_string_utf8_next(v_s_1933_, v_p_1934_);
stack->m_obj
 = v_res_1935_;
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next___boxed(lean_object* v_s_1936_, lean_object* v_p_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = lean_string_utf8_next(v_s_1936_, v_p_1937_);
lean_dec(v_p_1937_);
lean_dec_ref(v_s_1936_);
return v_res_1938_;
}
}
LEAN_EXPORT void l_String_next_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1939_ = stack[0].m_obj;
lean_object* v_p_1940_ = stack[1].m_obj;
lean_object* v_res_1941_;
v_res_1941_ = lean_string_utf8_next(v_s_1939_, v_p_1940_);
stack->m_obj
 = v_res_1941_;
}
LEAN_EXPORT lean_object* l_String_next___boxed(lean_object* v_s_1942_, lean_object* v_p_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = lean_string_utf8_next(v_s_1942_, v_p_1943_);
lean_dec(v_p_1943_);
lean_dec_ref(v_s_1942_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux(lean_object* v_x_1945_, lean_object* v_x_1946_, lean_object* v_x_1947_){
_start:
{
if (lean_obj_tag(v_x_1945_) == 0)
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
lean_dec(v_x_1946_);
v___x_1948_ = lean_unsigned_to_nat(1u);
v___x_1949_ = lean_nat_sub(v_x_1947_, v___x_1948_);
return v___x_1949_;
}
else
{
lean_object* v_head_1950_; lean_object* v_tail_1951_; uint32_t v___x_1952_; lean_object* v___x_1953_; lean_object* v_i_x27_1954_; uint8_t v___x_1955_; 
v_head_1950_ = lean_ctor_get(v_x_1945_, 0);
v_tail_1951_ = lean_ctor_get(v_x_1945_, 1);
v___x_1952_ = lean_unbox_uint32(v_head_1950_);
v___x_1953_ = l_Char_utf8Size(v___x_1952_);
v_i_x27_1954_ = lean_nat_add(v_x_1946_, v___x_1953_);
lean_dec(v___x_1953_);
v___x_1955_ = lean_nat_dec_le(v_x_1947_, v_i_x27_1954_);
if (v___x_1955_ == 0)
{
lean_dec(v_x_1946_);
v_x_1945_ = v_tail_1951_;
v_x_1946_ = v_i_x27_1954_;
goto _start;
}
else
{
lean_dec(v_i_x27_1954_);
return v_x_1946_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux___boxed(lean_object* v_x_1957_, lean_object* v_x_1958_, lean_object* v_x_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_String_Pos_Raw_utf8PrevAux(v_x_1957_, v_x_1958_, v_x_1959_);
lean_dec(v_x_1959_);
lean_dec(v_x_1957_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux(lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_String_Pos_Raw_utf8PrevAux(v_a_1961_, v_a_1962_, v_a_1963_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux___boxed(lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_String_utf8PrevAux(v_a_1965_, v_a_1966_, v_a_1967_);
lean_dec(v_a_1967_);
lean_dec(v_a_1965_);
return v_res_1968_;
}
}
LEAN_EXPORT void l_String_Pos_Raw_prev_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_1969_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_1970_ = stack[1].m_obj;
lean_object* v_res_1971_;
v_res_1971_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_1969_, v_a_00___x40___internal___hyg_1970_);
stack->m_obj
 = v_res_1971_;
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_prev___boxed(lean_object* v_a_00___x40___internal___hyg_1972_, lean_object* v_a_00___x40___internal___hyg_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_1972_, v_a_00___x40___internal___hyg_1973_);
lean_dec(v_a_00___x40___internal___hyg_1973_);
lean_dec_ref(v_a_00___x40___internal___hyg_1972_);
return v_res_1974_;
}
}
LEAN_EXPORT void l_String_prev_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_1975_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_1976_ = stack[1].m_obj;
lean_object* v_res_1977_;
v_res_1977_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_1975_, v_a_00___x40___internal___hyg_1976_);
stack->m_obj
 = v_res_1977_;
}
LEAN_EXPORT lean_object* l_String_prev___boxed(lean_object* v_a_00___x40___internal___hyg_1978_, lean_object* v_a_00___x40___internal___hyg_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_1978_, v_a_00___x40___internal___hyg_1979_);
lean_dec(v_a_00___x40___internal___hyg_1979_);
lean_dec_ref(v_a_00___x40___internal___hyg_1978_);
return v_res_1980_;
}
}
LEAN_EXPORT void l_String_Pos_Raw_atEnd_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_1981_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_1982_ = stack[1].m_obj;
uint8_t v_res_1983_;
v_res_1983_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_1981_, v_a_00___x40___internal___hyg_1982_);
stack->m_num = v_res_1983_;
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_1984_, lean_object* v_a_00___x40___internal___hyg_1985_){
_start:
{
uint8_t v_res_1986_; lean_object* v_r_1987_; 
v_res_1986_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_1984_, v_a_00___x40___internal___hyg_1985_);
lean_dec(v_a_00___x40___internal___hyg_1985_);
lean_dec_ref(v_a_00___x40___internal___hyg_1984_);
v_r_1987_ = lean_box(v_res_1986_);
return v_r_1987_;
}
}
LEAN_EXPORT void l_String_atEnd_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_1988_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_1989_ = stack[1].m_obj;
uint8_t v_res_1990_;
v_res_1990_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_1988_, v_a_00___x40___internal___hyg_1989_);
stack->m_num = v_res_1990_;
}
LEAN_EXPORT lean_object* l_String_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_1991_, lean_object* v_a_00___x40___internal___hyg_1992_){
_start:
{
uint8_t v_res_1993_; lean_object* v_r_1994_; 
v_res_1993_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_1991_, v_a_00___x40___internal___hyg_1992_);
lean_dec(v_a_00___x40___internal___hyg_1992_);
lean_dec_ref(v_a_00___x40___internal___hyg_1991_);
v_r_1994_ = lean_box(v_res_1993_);
return v_r_1994_;
}
}
LEAN_EXPORT void l_String_Pos_Raw_get_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1995_ = stack[0].m_obj;
lean_object* v_p_1996_ = stack[1].m_obj;
uint32_t v_res_1998_;
v_res_1998_ = lean_string_utf8_get_fast(v_s_1995_, v_p_1996_);
stack->m_num = v_res_1998_;
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x27___boxed(lean_object* v_s_1999_, lean_object* v_p_2000_, lean_object* v_h_2001_){
_start:
{
uint32_t v_res_2002_; lean_object* v_r_2003_; 
v_res_2002_ = lean_string_utf8_get_fast(v_s_1999_, v_p_2000_);
lean_dec(v_p_2000_);
lean_dec_ref(v_s_1999_);
v_r_2003_ = lean_box_uint32(v_res_2002_);
return v_r_2003_;
}
}
LEAN_EXPORT void l_String_get_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2004_ = stack[0].m_obj;
lean_object* v_p_2005_ = stack[1].m_obj;
uint32_t v_res_2007_;
v_res_2007_ = lean_string_utf8_get_fast(v_s_2004_, v_p_2005_);
stack->m_num = v_res_2007_;
}
LEAN_EXPORT lean_object* l_String_get_x27___boxed(lean_object* v_s_2008_, lean_object* v_p_2009_, lean_object* v_h_2010_){
_start:
{
uint32_t v_res_2011_; lean_object* v_r_2012_; 
v_res_2011_ = lean_string_utf8_get_fast(v_s_2008_, v_p_2009_);
lean_dec(v_p_2009_);
lean_dec_ref(v_s_2008_);
v_r_2012_ = lean_box_uint32(v_res_2011_);
return v_r_2012_;
}
}
LEAN_EXPORT void l_String_Pos_Raw_next_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2013_ = stack[0].m_obj;
lean_object* v_p_2014_ = stack[1].m_obj;
lean_object* v_res_2016_;
v_res_2016_ = lean_string_utf8_next_fast(v_s_2013_, v_p_2014_);
stack->m_obj
 = v_res_2016_;
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next_x27___boxed(lean_object* v_s_2017_, lean_object* v_p_2018_, lean_object* v_h_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = lean_string_utf8_next_fast(v_s_2017_, v_p_2018_);
lean_dec(v_p_2018_);
lean_dec_ref(v_s_2017_);
return v_res_2020_;
}
}
LEAN_EXPORT void l_String_next_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2021_ = stack[0].m_obj;
lean_object* v_p_2022_ = stack[1].m_obj;
lean_object* v_res_2024_;
v_res_2024_ = lean_string_utf8_next_fast(v_s_2021_, v_p_2022_);
stack->m_obj
 = v_res_2024_;
}
LEAN_EXPORT lean_object* l_String_next_x27___boxed(lean_object* v_s_2025_, lean_object* v_p_2026_, lean_object* v_h_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = lean_string_utf8_next_fast(v_s_2025_, v_p_2026_);
lean_dec(v_p_2026_);
lean_dec_ref(v_s_2025_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop(lean_object* v_a_2029_, lean_object* v_b_2030_, lean_object* v_stopPos_2031_, lean_object* v_i_2032_){
_start:
{
uint8_t v___y_2034_; lean_object* v___x_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; uint8_t v___y_2041_; 
v___x_2037_ = lean_unsigned_to_nat(1u);
v___x_2038_ = lean_nat_add(v_i_2032_, v___x_2037_);
v___x_2039_ = lean_nat_dec_le(v___x_2038_, v_stopPos_2031_);
lean_dec(v___x_2038_);
if (v___x_2039_ == 0)
{
return v_i_2032_;
}
else
{
uint32_t v___x_2042_; uint32_t v___x_2043_; uint8_t v___x_2044_; 
v___x_2042_ = lean_string_utf8_get(v_a_2029_, v_i_2032_);
v___x_2043_ = lean_string_utf8_get(v_b_2030_, v_i_2032_);
v___x_2044_ = lean_uint32_dec_eq(v___x_2042_, v___x_2043_);
if (v___x_2044_ == 0)
{
v___y_2041_ = v___x_2039_;
goto v___jp_2040_;
}
else
{
uint8_t v___x_2045_; 
v___x_2045_ = 0;
v___y_2041_ = v___x_2045_;
goto v___jp_2040_;
}
}
v___jp_2033_:
{
if (v___y_2034_ == 0)
{
lean_object* v___x_2035_; 
v___x_2035_ = lean_string_utf8_next(v_a_2029_, v_i_2032_);
lean_dec(v_i_2032_);
v_i_2032_ = v___x_2035_;
goto _start;
}
else
{
return v_i_2032_;
}
}
v___jp_2040_:
{
if (v___x_2039_ == 0)
{
v___y_2034_ = v___x_2039_;
goto v___jp_2033_;
}
else
{
v___y_2034_ = v___y_2041_;
goto v___jp_2033_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop___boxed(lean_object* v_a_2046_, lean_object* v_b_2047_, lean_object* v_stopPos_2048_, lean_object* v_i_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_String_firstDiffPos_loop(v_a_2046_, v_b_2047_, v_stopPos_2048_, v_i_2049_);
lean_dec(v_stopPos_2048_);
lean_dec_ref(v_b_2047_);
lean_dec_ref(v_a_2046_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos(lean_object* v_a_2051_, lean_object* v_b_2052_){
_start:
{
lean_object* v___y_2054_; lean_object* v___x_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; 
v___x_2057_ = lean_string_utf8_byte_size(v_a_2051_);
v___x_2058_ = lean_string_utf8_byte_size(v_b_2052_);
v___x_2059_ = lean_nat_dec_le(v___x_2057_, v___x_2058_);
if (v___x_2059_ == 0)
{
v___y_2054_ = v___x_2058_;
goto v___jp_2053_;
}
else
{
v___y_2054_ = v___x_2057_;
goto v___jp_2053_;
}
v___jp_2053_:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = lean_unsigned_to_nat(0u);
v___x_2056_ = l_String_firstDiffPos_loop(v_a_2051_, v_b_2052_, v___y_2054_, v___x_2055_);
lean_dec(v___y_2054_);
return v___x_2056_;
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos___boxed(lean_object* v_a_2060_, lean_object* v_b_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_String_firstDiffPos(v_a_2060_, v_b_2061_);
lean_dec_ref(v_b_2061_);
lean_dec_ref(v_a_2060_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082(lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
if (lean_obj_tag(v_a_2063_) == 0)
{
return v_a_2063_;
}
else
{
lean_object* v_head_2066_; lean_object* v_tail_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2080_; 
v_head_2066_ = lean_ctor_get(v_a_2063_, 0);
v_tail_2067_ = lean_ctor_get(v_a_2063_, 1);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_a_2063_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2069_ = v_a_2063_;
v_isShared_2070_ = v_isSharedCheck_2080_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_tail_2067_);
lean_inc(v_head_2066_);
lean_dec(v_a_2063_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2080_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
uint8_t v_decide_2071_; 
v_decide_2071_ = lean_nat_dec_eq(v_a_2064_, v_a_2065_);
if (v_decide_2071_ == 0)
{
uint32_t v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2072_ = lean_unbox_uint32(v_head_2066_);
v___x_2073_ = l_Char_utf8Size(v___x_2072_);
v___x_2074_ = lean_nat_add(v_a_2064_, v___x_2073_);
lean_dec(v___x_2073_);
v___x_2075_ = l_String_Pos_Raw_extract_go_u2082(v_tail_2067_, v___x_2074_, v_a_2065_);
lean_dec(v___x_2074_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 1, v___x_2075_);
v___x_2077_ = v___x_2069_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_head_2066_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
else
{
lean_object* v___x_2079_; 
lean_del_object(v___x_2069_);
lean_dec(v_tail_2067_);
lean_dec(v_head_2066_);
v___x_2079_ = lean_box(0);
return v___x_2079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082___boxed(lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_String_Pos_Raw_extract_go_u2082(v_a_2081_, v_a_2082_, v_a_2083_);
lean_dec(v_a_2083_);
lean_dec(v_a_2082_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081(lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_){
_start:
{
if (lean_obj_tag(v_a_2085_) == 0)
{
lean_dec(v_a_2086_);
return v_a_2085_;
}
else
{
lean_object* v_head_2089_; lean_object* v_tail_2090_; uint8_t v_decide_2091_; 
v_head_2089_ = lean_ctor_get(v_a_2085_, 0);
v_tail_2090_ = lean_ctor_get(v_a_2085_, 1);
v_decide_2091_ = lean_nat_dec_eq(v_a_2086_, v_a_2087_);
if (v_decide_2091_ == 0)
{
uint32_t v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
lean_inc(v_tail_2090_);
lean_inc(v_head_2089_);
lean_dec_ref_known(v_a_2085_, 2);
v___x_2092_ = lean_unbox_uint32(v_head_2089_);
lean_dec(v_head_2089_);
v___x_2093_ = l_Char_utf8Size(v___x_2092_);
v___x_2094_ = lean_nat_add(v_a_2086_, v___x_2093_);
lean_dec(v___x_2093_);
lean_dec(v_a_2086_);
v_a_2085_ = v_tail_2090_;
v_a_2086_ = v___x_2094_;
goto _start;
}
else
{
lean_object* v___x_2096_; 
v___x_2096_ = l_String_Pos_Raw_extract_go_u2082(v_a_2085_, v_a_2086_, v_a_2088_);
lean_dec(v_a_2086_);
return v___x_2096_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081___boxed(lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_String_Pos_Raw_extract_go_u2081(v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
lean_dec(v_a_2100_);
lean_dec(v_a_2099_);
return v_res_2101_;
}
}
LEAN_EXPORT void l_String_Pos_Raw_extract_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_2102_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_2103_ = stack[1].m_obj;
lean_object* v_a_00___x40___internal___hyg_2104_ = stack[2].m_obj;
lean_object* v_res_2105_;
v_res_2105_ = lean_string_utf8_extract(v_a_00___x40___internal___hyg_2102_, v_a_00___x40___internal___hyg_2103_, v_a_00___x40___internal___hyg_2104_);
stack->m_obj
 = v_res_2105_;
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract___boxed(lean_object* v_a_00___x40___internal___hyg_2106_, lean_object* v_a_00___x40___internal___hyg_2107_, lean_object* v_a_00___x40___internal___hyg_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = lean_string_utf8_extract(v_a_00___x40___internal___hyg_2106_, v_a_00___x40___internal___hyg_2107_, v_a_00___x40___internal___hyg_2108_);
lean_dec(v_a_00___x40___internal___hyg_2108_);
lean_dec(v_a_00___x40___internal___hyg_2107_);
lean_dec_ref(v_a_00___x40___internal___hyg_2106_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux(lean_object* v_s_2110_, lean_object* v_pos_2111_, lean_object* v_i_2112_, lean_object* v_offset_2113_){
_start:
{
uint8_t v___x_2114_; 
v___x_2114_ = lean_nat_dec_le(v_pos_2111_, v_i_2112_);
if (v___x_2114_ == 0)
{
uint8_t v___x_2115_; 
v___x_2115_ = lean_string_utf8_at_end(v_s_2110_, v_i_2112_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2116_ = lean_string_utf8_next(v_s_2110_, v_i_2112_);
lean_dec(v_i_2112_);
v___x_2117_ = lean_unsigned_to_nat(1u);
v___x_2118_ = lean_nat_add(v_offset_2113_, v___x_2117_);
lean_dec(v_offset_2113_);
v_i_2112_ = v___x_2116_;
v_offset_2113_ = v___x_2118_;
goto _start;
}
else
{
lean_dec(v_i_2112_);
return v_offset_2113_;
}
}
else
{
lean_dec(v_i_2112_);
return v_offset_2113_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux___boxed(lean_object* v_s_2120_, lean_object* v_pos_2121_, lean_object* v_i_2122_, lean_object* v_offset_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2120_, v_pos_2121_, v_i_2122_, v_offset_2123_);
lean_dec(v_pos_2121_);
lean_dec_ref(v_s_2120_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos(lean_object* v_s_2125_, lean_object* v_pos_2126_){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = lean_unsigned_to_nat(0u);
v___x_2128_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2125_, v_pos_2126_, v___x_2127_, v___x_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos___boxed(lean_object* v_s_2129_, lean_object* v_pos_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_String_Pos_Raw_offsetOfPos(v_s_2129_, v_pos_2130_);
lean_dec(v_pos_2130_);
lean_dec_ref(v_s_2129_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos(lean_object* v_s_2132_, lean_object* v_pos_2133_){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = lean_unsigned_to_nat(0u);
v___x_2135_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2132_, v_pos_2133_, v___x_2134_, v___x_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos___boxed(lean_object* v_s_2136_, lean_object* v_pos_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_String_offsetOfPos(v_s_2136_, v_pos_2137_);
lean_dec(v_pos_2137_);
lean_dec_ref(v_s_2136_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* lean_string_offsetofpos(lean_object* v_s_2139_, lean_object* v_pos_2140_){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = lean_unsigned_to_nat(0u);
v___x_2142_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2139_, v_pos_2140_, v___x_2141_, v___x_2141_);
lean_dec(v_pos_2140_);
lean_dec_ref(v_s_2139_);
return v___x_2142_;
}
}
uint8_t l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(lean_object* v_s1_2143_, lean_object* v_s2_2144_, lean_object* v_off1_2145_, lean_object* v_off2_2146_, lean_object* v_stop1_2147_){
_start:
{
uint8_t v___x_2148_; 
v___x_2148_ = lean_nat_dec_lt(v_off1_2145_, v_stop1_2147_);
if (v___x_2148_ == 0)
{
uint8_t v___x_2149_; 
lean_dec(v_off2_2146_);
lean_dec(v_off1_2145_);
v___x_2149_ = 1;
return v___x_2149_;
}
else
{
uint32_t v_c_u2081_2150_; uint32_t v_c_u2082_2151_; uint8_t v___x_2152_; 
v_c_u2081_2150_ = lean_string_utf8_get(v_s1_2143_, v_off1_2145_);
v_c_u2082_2151_ = lean_string_utf8_get(v_s2_2144_, v_off2_2146_);
v___x_2152_ = lean_uint32_dec_eq(v_c_u2081_2150_, v_c_u2082_2151_);
if (v___x_2152_ == 0)
{
lean_dec(v_off2_2146_);
lean_dec(v_off1_2145_);
return v___x_2152_;
}
else
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2153_ = l_Char_utf8Size(v_c_u2081_2150_);
v___x_2154_ = lean_nat_add(v_off1_2145_, v___x_2153_);
lean_dec(v___x_2153_);
lean_dec(v_off1_2145_);
v___x_2155_ = l_Char_utf8Size(v_c_u2082_2151_);
v___x_2156_ = lean_nat_add(v_off2_2146_, v___x_2155_);
lean_dec(v___x_2155_);
lean_dec(v_off2_2146_);
v_off1_2145_ = v___x_2154_;
v_off2_2146_ = v___x_2156_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_s1_2143_ = stack[0].m_obj;
lean_object* v_s2_2144_ = stack[1].m_obj;
lean_object* v_off1_2145_ = stack[2].m_obj;
lean_object* v_off2_2146_ = stack[3].m_obj;
lean_object* v_stop1_2147_ = stack[4].m_obj;
uint8_t v_res_2158_;
v_res_2158_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2143_, v_s2_2144_, v_off1_2145_, v_off2_2146_, v_stop1_2147_);
stack->m_num = v_res_2158_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop___boxed(lean_object* v_s1_2159_, lean_object* v_s2_2160_, lean_object* v_off1_2161_, lean_object* v_off2_2162_, lean_object* v_stop1_2163_){
_start:
{
uint8_t v_res_2164_; lean_object* v_r_2165_; 
v_res_2164_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2159_, v_s2_2160_, v_off1_2161_, v_off2_2162_, v_stop1_2163_);
lean_dec(v_stop1_2163_);
lean_dec_ref(v_s2_2160_);
lean_dec_ref(v_s1_2159_);
v_r_2165_ = lean_box(v_res_2164_);
return v_r_2165_;
}
}
uint8_t l_String_Pos_Raw_substrEq(lean_object* v_s1_2166_, lean_object* v_pos1_2167_, lean_object* v_s2_2168_, lean_object* v_pos2_2169_, lean_object* v_sz_2170_){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2171_ = lean_nat_add(v_pos1_2167_, v_sz_2170_);
v___x_2172_ = lean_string_utf8_byte_size(v_s1_2166_);
v___x_2173_ = lean_nat_dec_le(v___x_2171_, v___x_2172_);
if (v___x_2173_ == 0)
{
lean_dec(v___x_2171_);
lean_dec(v_pos2_2169_);
lean_dec(v_pos1_2167_);
return v___x_2173_;
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; uint8_t v___x_2176_; 
v___x_2174_ = lean_nat_add(v_pos2_2169_, v_sz_2170_);
v___x_2175_ = lean_string_utf8_byte_size(v_s2_2168_);
v___x_2176_ = lean_nat_dec_le(v___x_2174_, v___x_2175_);
lean_dec(v___x_2174_);
if (v___x_2176_ == 0)
{
lean_dec(v___x_2171_);
lean_dec(v_pos2_2169_);
lean_dec(v_pos1_2167_);
return v___x_2176_;
}
else
{
uint8_t v___x_2177_; 
v___x_2177_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2166_, v_s2_2168_, v_pos1_2167_, v_pos2_2169_, v___x_2171_);
lean_dec(v___x_2171_);
return v___x_2177_;
}
}
}
}
LEAN_EXPORT void l_String_Pos_Raw_substrEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_s1_2166_ = stack[0].m_obj;
lean_object* v_pos1_2167_ = stack[1].m_obj;
lean_object* v_s2_2168_ = stack[2].m_obj;
lean_object* v_pos2_2169_ = stack[3].m_obj;
lean_object* v_sz_2170_ = stack[4].m_obj;
uint8_t v_res_2178_;
v_res_2178_ = l_String_Pos_Raw_substrEq(v_s1_2166_, v_pos1_2167_, v_s2_2168_, v_pos2_2169_, v_sz_2170_);
stack->m_num = v_res_2178_;
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_substrEq___boxed(lean_object* v_s1_2179_, lean_object* v_pos1_2180_, lean_object* v_s2_2181_, lean_object* v_pos2_2182_, lean_object* v_sz_2183_){
_start:
{
uint8_t v_res_2184_; lean_object* v_r_2185_; 
v_res_2184_ = l_String_Pos_Raw_substrEq(v_s1_2179_, v_pos1_2180_, v_s2_2181_, v_pos2_2182_, v_sz_2183_);
lean_dec(v_sz_2183_);
lean_dec_ref(v_s2_2181_);
lean_dec_ref(v_s1_2179_);
v_r_2185_ = lean_box(v_res_2184_);
return v_r_2185_;
}
}
uint8_t l_String_substrEq(lean_object* v_s1_2186_, lean_object* v_pos1_2187_, lean_object* v_s2_2188_, lean_object* v_pos2_2189_, lean_object* v_sz_2190_){
_start:
{
uint8_t v___x_2191_; 
v___x_2191_ = l_String_Pos_Raw_substrEq(v_s1_2186_, v_pos1_2187_, v_s2_2188_, v_pos2_2189_, v_sz_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT void l_String_substrEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_s1_2186_ = stack[0].m_obj;
lean_object* v_pos1_2187_ = stack[1].m_obj;
lean_object* v_s2_2188_ = stack[2].m_obj;
lean_object* v_pos2_2189_ = stack[3].m_obj;
lean_object* v_sz_2190_ = stack[4].m_obj;
uint8_t v_res_2192_;
v_res_2192_ = l_String_substrEq(v_s1_2186_, v_pos1_2187_, v_s2_2188_, v_pos2_2189_, v_sz_2190_);
stack->m_num = v_res_2192_;
}
LEAN_EXPORT lean_object* l_String_substrEq___boxed(lean_object* v_s1_2193_, lean_object* v_pos1_2194_, lean_object* v_s2_2195_, lean_object* v_pos2_2196_, lean_object* v_sz_2197_){
_start:
{
uint8_t v_res_2198_; lean_object* v_r_2199_; 
v_res_2198_ = l_String_substrEq(v_s1_2193_, v_pos1_2194_, v_s2_2195_, v_pos2_2196_, v_sz_2197_);
lean_dec(v_sz_2197_);
lean_dec_ref(v_s2_2195_);
lean_dec_ref(v_s1_2193_);
v_r_2199_ = lean_box(v_res_2198_);
return v_r_2199_;
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
