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
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8_go___redArg(lean_object* v_b_168_, lean_object* v_i_169_){
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
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___redArg___boxed(lean_object* v_b_298_, lean_object* v_i_299_){
_start:
{
uint8_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = l_ByteArray_validateUTF8_go___redArg(v_b_298_, v_i_299_);
lean_dec_ref(v_b_298_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8_go(lean_object* v_b_302_, lean_object* v_i_303_, lean_object* v_hi_304_){
_start:
{
uint8_t v___x_305_; 
v___x_305_ = l_ByteArray_validateUTF8_go___redArg(v_b_302_, v_i_303_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___boxed(lean_object* v_b_306_, lean_object* v_i_307_, lean_object* v_hi_308_){
_start:
{
uint8_t v_res_309_; lean_object* v_r_310_; 
v_res_309_ = l_ByteArray_validateUTF8_go(v_b_306_, v_i_307_, v_hi_308_);
lean_dec_ref(v_b_306_);
v_r_310_ = lean_box(v_res_309_);
return v_r_310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(uint8_t v_x_311_, lean_object* v_h__1_312_, lean_object* v_h__2_313_){
_start:
{
if (v_x_311_ == 0)
{
lean_object* v___x_314_; 
lean_dec(v_h__2_313_);
v___x_314_ = lean_apply_1(v_h__1_312_, lean_box(0));
return v___x_314_;
}
else
{
lean_object* v___x_315_; 
lean_dec(v_h__1_312_);
v___x_315_ = lean_apply_1(v_h__2_313_, lean_box(0));
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg___boxed(lean_object* v_x_316_, lean_object* v_h__1_317_, lean_object* v_h__2_318_){
_start:
{
uint8_t v_x_26__boxed_319_; lean_object* v_res_320_; 
v_x_26__boxed_319_ = lean_unbox(v_x_316_);
v_res_320_ = l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(v_x_26__boxed_319_, v_h__1_317_, v_h__2_318_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(lean_object* v_motive_321_, uint8_t v_x_322_, lean_object* v_h__1_323_, lean_object* v_h__2_324_){
_start:
{
if (v_x_322_ == 0)
{
lean_object* v___x_325_; 
lean_dec(v_h__2_324_);
v___x_325_ = lean_apply_1(v_h__1_323_, lean_box(0));
return v___x_325_;
}
else
{
lean_object* v___x_326_; 
lean_dec(v_h__1_323_);
v___x_326_ = lean_apply_1(v_h__2_324_, lean_box(0));
return v___x_326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___boxed(lean_object* v_motive_327_, lean_object* v_x_328_, lean_object* v_h__1_329_, lean_object* v_h__2_330_){
_start:
{
uint8_t v_x_33__boxed_331_; lean_object* v_res_332_; 
v_x_33__boxed_331_ = lean_unbox(v_x_328_);
v_res_332_ = l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(v_motive_327_, v_x_33__boxed_331_, v_h__1_329_, v_h__2_330_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8___boxed(lean_object* v_b_334_){
_start:
{
uint8_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = lean_string_validate_utf8(v_b_334_);
lean_dec_ref(v_b_334_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT uint8_t l_instDecidableIsValidUTF8(lean_object* v_b_337_){
_start:
{
uint8_t v___x_338_; 
v___x_338_ = lean_string_validate_utf8(v_b_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_instDecidableIsValidUTF8___boxed(lean_object* v_b_339_){
_start:
{
uint8_t v_res_340_; lean_object* v_r_341_; 
v_res_340_ = l_instDecidableIsValidUTF8(v_b_339_);
lean_dec_ref(v_b_339_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_x3f(lean_object* v_a_342_){
_start:
{
uint8_t v___x_343_; 
v___x_343_ = lean_string_validate_utf8(v_a_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; 
lean_dec_ref(v_a_342_);
v___x_344_ = lean_box(0);
return v___x_344_;
}
else
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_string_from_utf8_unchecked(v_a_342_);
v___x_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
}
static lean_object* _init_l_String_fromUTF8_x21___closed__4(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_351_ = ((lean_object*)(l_String_fromUTF8_x21___closed__3));
v___x_352_ = lean_unsigned_to_nat(46u);
v___x_353_ = lean_unsigned_to_nat(193u);
v___x_354_ = ((lean_object*)(l_String_fromUTF8_x21___closed__2));
v___x_355_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_356_ = l_mkPanicMessageWithDecl(v___x_355_, v___x_354_, v___x_353_, v___x_352_, v___x_351_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_x21(lean_object* v_a_357_){
_start:
{
uint8_t v___x_358_; 
v___x_358_ = lean_string_validate_utf8(v_a_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec_ref(v_a_357_);
v___x_359_ = ((lean_object*)(l_String_fromUTF8_x21___closed__0));
v___x_360_ = lean_obj_once(&l_String_fromUTF8_x21___closed__4, &l_String_fromUTF8_x21___closed__4_once, _init_l_String_fromUTF8_x21___closed__4);
v___x_361_ = l_panic___redArg(v___x_359_, v___x_360_);
return v___x_361_;
}
else
{
lean_object* v___x_362_; 
v___x_362_ = lean_string_from_utf8_unchecked(v_a_357_);
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l_String_Internal_toArray(lean_object* v_b_363_){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_val_368_; 
v___x_364_ = lean_string_to_utf8(v_b_363_);
v___x_365_ = lean_unsigned_to_nat(0u);
v___x_366_ = ((lean_object*)(l_ByteArray_utf8Decode_x3f___closed__0));
v___x_367_ = l_ByteArray_utf8Decode_x3f_go___redArg(v___x_364_, v___x_365_, v___x_366_);
lean_dec_ref(v___x_364_);
v_val_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_val_368_);
lean_dec(v___x_367_);
return v_val_368_;
}
}
static lean_object* _init_l_String_instLT(void){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = lean_box(0);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_String_decidableLT___boxed(lean_object* v_s_u2081_372_, lean_object* v_s_u2082_373_){
_start:
{
uint8_t v_res_374_; lean_object* v_r_375_; 
v_res_374_ = lean_string_dec_lt(v_s_u2081_372_, v_s_u2082_373_);
lean_dec_ref(v_s_u2082_373_);
lean_dec_ref(v_s_u2081_372_);
v_r_375_ = lean_box(v_res_374_);
return v_r_375_;
}
}
static lean_object* _init_l_String_instLE(void){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = lean_box(0);
return v___x_376_;
}
}
LEAN_EXPORT uint8_t l_String_decLE(lean_object* v_s_u2081_377_, lean_object* v_s_u2082_378_){
_start:
{
uint8_t v___x_379_; 
v___x_379_ = lean_string_dec_lt(v_s_u2082_378_, v_s_u2081_377_);
if (v___x_379_ == 0)
{
uint8_t v___x_380_; 
v___x_380_ = 1;
return v___x_380_;
}
else
{
uint8_t v___x_381_; 
v___x_381_ = 0;
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l_String_decLE___boxed(lean_object* v_s_u2081_382_, lean_object* v_s_u2082_383_){
_start:
{
uint8_t v_res_384_; lean_object* v_r_385_; 
v_res_384_ = l_String_decLE(v_s_u2081_382_, v_s_u2082_383_);
lean_dec_ref(v_s_u2082_383_);
lean_dec_ref(v_s_u2081_382_);
v_r_385_ = lean_box(v_res_384_);
return v_r_385_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValid___boxed(lean_object* v_s_388_, lean_object* v_p_389_){
_start:
{
uint8_t v_res_390_; lean_object* v_r_391_; 
v_res_390_ = lean_string_is_valid_pos(v_s_388_, v_p_389_);
lean_dec(v_p_389_);
lean_dec_ref(v_s_388_);
v_r_391_ = lean_box(v_res_390_);
return v_r_391_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsValid(lean_object* v_s_392_, lean_object* v_p_393_){
_start:
{
uint8_t v___x_394_; 
v___x_394_ = lean_string_is_valid_pos(v_s_392_, v_p_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsValid___boxed(lean_object* v_s_395_, lean_object* v_p_396_){
_start:
{
uint8_t v_res_397_; lean_object* v_r_398_; 
v_res_397_ = l_String_instDecidableIsValid(v_s_395_, v_p_396_);
lean_dec(v_p_396_);
lean_dec_ref(v_s_395_);
v_r_398_ = lean_box(v_res_397_);
return v_r_398_;
}
}
LEAN_EXPORT lean_object* l_String_extract___boxed(lean_object* v_s_402_, lean_object* v_b_403_, lean_object* v_e_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = lean_string_utf8_extract_fast(v_s_402_, v_b_403_, v_e_404_);
lean_dec(v_e_404_);
lean_dec(v_b_403_);
lean_dec_ref(v_s_402_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_extract(lean_object* v_s_406_, lean_object* v_b_407_, lean_object* v_e_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = lean_string_utf8_extract_fast(v_s_406_, v_b_407_, v_e_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_extract___boxed(lean_object* v_s_410_, lean_object* v_b_411_, lean_object* v_e_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_String_Pos_extract(v_s_410_, v_b_411_, v_e_412_);
lean_dec(v_e_412_);
lean_dec(v_b_411_);
lean_dec_ref(v_s_410_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_copy(lean_object* v_s_414_){
_start:
{
lean_object* v_str_415_; lean_object* v_startInclusive_416_; lean_object* v_endExclusive_417_; lean_object* v___x_418_; 
v_str_415_ = lean_ctor_get(v_s_414_, 0);
v_startInclusive_416_ = lean_ctor_get(v_s_414_, 1);
v_endExclusive_417_ = lean_ctor_get(v_s_414_, 2);
v___x_418_ = lean_string_utf8_extract_fast(v_str_415_, v_startInclusive_416_, v_endExclusive_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_copy___boxed(lean_object* v_s_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_String_Slice_copy(v_s_419_);
lean_dec_ref(v_s_419_);
return v_res_420_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_isValidForSlice(lean_object* v_s_421_, lean_object* v_p_422_){
_start:
{
lean_object* v_str_423_; lean_object* v_startInclusive_424_; lean_object* v_endExclusive_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_str_423_ = lean_ctor_get(v_s_421_, 0);
v_startInclusive_424_ = lean_ctor_get(v_s_421_, 1);
v_endExclusive_425_ = lean_ctor_get(v_s_421_, 2);
v___x_426_ = lean_nat_sub(v_endExclusive_425_, v_startInclusive_424_);
v___x_427_ = lean_unsigned_to_nat(1u);
v___x_428_ = lean_nat_add(v_p_422_, v___x_427_);
v___x_429_ = lean_nat_dec_le(v___x_428_, v___x_426_);
lean_dec(v___x_428_);
if (v___x_429_ == 0)
{
uint8_t v_decide_430_; 
v_decide_430_ = lean_nat_dec_eq(v_p_422_, v___x_426_);
lean_dec(v___x_426_);
return v_decide_430_;
}
else
{
lean_object* v___x_431_; uint8_t v___x_432_; uint8_t v___x_433_; uint8_t v___x_434_; uint8_t v___x_435_; uint8_t v___x_436_; 
lean_dec(v___x_426_);
v___x_431_ = lean_nat_add(v_startInclusive_424_, v_p_422_);
v___x_432_ = lean_string_get_byte_fast(v_str_423_, v___x_431_);
v___x_433_ = 128;
v___x_434_ = lean_uint8_land(v___x_432_, v___x_433_);
v___x_435_ = 0;
v___x_436_ = lean_uint8_dec_eq(v___x_434_, v___x_435_);
if (v___x_436_ == 0)
{
uint8_t v___x_437_; uint8_t v___x_438_; uint8_t v___x_439_; uint8_t v___x_440_; 
v___x_437_ = 224;
v___x_438_ = lean_uint8_land(v___x_432_, v___x_437_);
v___x_439_ = 192;
v___x_440_ = lean_uint8_dec_eq(v___x_438_, v___x_439_);
if (v___x_440_ == 0)
{
uint8_t v___x_441_; uint8_t v___x_442_; uint8_t v___x_443_; 
v___x_441_ = 240;
v___x_442_ = lean_uint8_land(v___x_432_, v___x_441_);
v___x_443_ = lean_uint8_dec_eq(v___x_442_, v___x_437_);
if (v___x_443_ == 0)
{
uint8_t v___x_444_; uint8_t v___x_445_; uint8_t v___x_446_; 
v___x_444_ = 248;
v___x_445_ = lean_uint8_land(v___x_432_, v___x_444_);
v___x_446_ = lean_uint8_dec_eq(v___x_445_, v___x_441_);
return v___x_446_;
}
else
{
return v___x_443_;
}
}
else
{
return v___x_440_;
}
}
else
{
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValidForSlice___boxed(lean_object* v_s_447_, lean_object* v_p_448_){
_start:
{
uint8_t v_res_449_; lean_object* v_r_450_; 
v_res_449_ = l_String_Pos_Raw_isValidForSlice(v_s_447_, v_p_448_);
lean_dec(v_p_448_);
lean_dec_ref(v_s_447_);
v_r_450_ = lean_box(v_res_449_);
return v_r_450_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsValidForSlice(lean_object* v_s_451_, lean_object* v_p_452_){
_start:
{
uint8_t v___x_453_; 
v___x_453_ = l_String_Pos_Raw_isValidForSlice(v_s_451_, v_p_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsValidForSlice___boxed(lean_object* v_s_454_, lean_object* v_p_455_){
_start:
{
uint8_t v_res_456_; lean_object* v_r_457_; 
v_res_456_ = l_String_instDecidableIsValidForSlice(v_s_454_, v_p_455_);
lean_dec(v_p_455_);
lean_dec_ref(v_s_454_);
v_r_457_ = lean_box(v_res_456_);
return v_r_457_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str(lean_object* v_s_458_, lean_object* v_pos_459_){
_start:
{
lean_object* v_startInclusive_460_; lean_object* v___x_461_; 
v_startInclusive_460_ = lean_ctor_get(v_s_458_, 1);
v___x_461_ = lean_nat_add(v_startInclusive_460_, v_pos_459_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str___boxed(lean_object* v_s_462_, lean_object* v_pos_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_String_Slice_Pos_str(v_s_462_, v_pos_463_);
lean_dec(v_pos_463_);
lean_dec_ref(v_s_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg(lean_object* v_s_465_, lean_object* v_pos_466_){
_start:
{
lean_object* v_startInclusive_467_; lean_object* v___x_468_; 
v_startInclusive_467_ = lean_ctor_get(v_s_465_, 1);
v___x_468_ = lean_nat_sub(v_pos_466_, v_startInclusive_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg___boxed(lean_object* v_s_469_, lean_object* v_pos_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_String_Slice_Pos_ofStr___redArg(v_s_469_, v_pos_470_);
lean_dec(v_pos_470_);
lean_dec_ref(v_s_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr(lean_object* v_s_472_, lean_object* v_pos_473_, lean_object* v_h_u2081_474_, lean_object* v_h_u2082_475_){
_start:
{
lean_object* v_startInclusive_476_; lean_object* v___x_477_; 
v_startInclusive_476_ = lean_ctor_get(v_s_472_, 1);
v___x_477_ = lean_nat_sub(v_pos_473_, v_startInclusive_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___boxed(lean_object* v_s_478_, lean_object* v_pos_479_, lean_object* v_h_u2081_480_, lean_object* v_h_u2082_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_String_Slice_Pos_ofStr(v_s_478_, v_pos_479_, v_h_u2081_480_, v_h_u2082_481_);
lean_dec(v_pos_479_);
lean_dec_ref(v_s_478_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom(lean_object* v_s_483_, lean_object* v_pos_484_){
_start:
{
lean_object* v_str_485_; lean_object* v_startInclusive_486_; lean_object* v_endExclusive_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_495_; 
v_str_485_ = lean_ctor_get(v_s_483_, 0);
v_startInclusive_486_ = lean_ctor_get(v_s_483_, 1);
v_endExclusive_487_ = lean_ctor_get(v_s_483_, 2);
v_isSharedCheck_495_ = !lean_is_exclusive(v_s_483_);
if (v_isSharedCheck_495_ == 0)
{
v___x_489_ = v_s_483_;
v_isShared_490_ = v_isSharedCheck_495_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_endExclusive_487_);
lean_inc(v_startInclusive_486_);
lean_inc(v_str_485_);
lean_dec(v_s_483_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_495_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_491_ = lean_nat_add(v_startInclusive_486_, v_pos_484_);
lean_dec(v_startInclusive_486_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v___x_491_);
v___x_493_ = v___x_489_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_str_485_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_494_, 2, v_endExclusive_487_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom___boxed(lean_object* v_s_496_, lean_object* v_pos_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_String_Slice_sliceFrom(v_s_496_, v_pos_497_);
lean_dec(v_pos_497_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStart(lean_object* v_s_499_, lean_object* v_pos_500_){
_start:
{
lean_object* v_str_501_; lean_object* v_startInclusive_502_; lean_object* v_endExclusive_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_511_; 
v_str_501_ = lean_ctor_get(v_s_499_, 0);
v_startInclusive_502_ = lean_ctor_get(v_s_499_, 1);
v_endExclusive_503_ = lean_ctor_get(v_s_499_, 2);
v_isSharedCheck_511_ = !lean_is_exclusive(v_s_499_);
if (v_isSharedCheck_511_ == 0)
{
v___x_505_ = v_s_499_;
v_isShared_506_ = v_isSharedCheck_511_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_endExclusive_503_);
lean_inc(v_startInclusive_502_);
lean_inc(v_str_501_);
lean_dec(v_s_499_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_511_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v___x_509_; 
v___x_507_ = lean_nat_add(v_startInclusive_502_, v_pos_500_);
lean_dec(v_startInclusive_502_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 1, v___x_507_);
v___x_509_ = v___x_505_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_str_501_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v_endExclusive_503_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStart___boxed(lean_object* v_s_512_, lean_object* v_pos_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_String_Slice_replaceStart(v_s_512_, v_pos_513_);
lean_dec(v_pos_513_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceTo(lean_object* v_s_515_, lean_object* v_pos_516_){
_start:
{
lean_object* v_str_517_; lean_object* v_startInclusive_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_526_; 
v_str_517_ = lean_ctor_get(v_s_515_, 0);
v_startInclusive_518_ = lean_ctor_get(v_s_515_, 1);
v_isSharedCheck_526_ = !lean_is_exclusive(v_s_515_);
if (v_isSharedCheck_526_ == 0)
{
lean_object* v_unused_527_; 
v_unused_527_ = lean_ctor_get(v_s_515_, 2);
lean_dec(v_unused_527_);
v___x_520_ = v_s_515_;
v_isShared_521_ = v_isSharedCheck_526_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_startInclusive_518_);
lean_inc(v_str_517_);
lean_dec(v_s_515_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_526_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_522_ = lean_nat_add(v_startInclusive_518_, v_pos_516_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 2, v___x_522_);
v___x_524_ = v___x_520_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_str_517_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_startInclusive_518_);
lean_ctor_set(v_reuseFailAlloc_525_, 2, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceTo___boxed(lean_object* v_s_528_, lean_object* v_pos_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_String_Slice_sliceTo(v_s_528_, v_pos_529_);
lean_dec(v_pos_529_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd(lean_object* v_s_531_, lean_object* v_pos_532_){
_start:
{
lean_object* v_str_533_; lean_object* v_startInclusive_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_542_; 
v_str_533_ = lean_ctor_get(v_s_531_, 0);
v_startInclusive_534_ = lean_ctor_get(v_s_531_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v_s_531_);
if (v_isSharedCheck_542_ == 0)
{
lean_object* v_unused_543_; 
v_unused_543_ = lean_ctor_get(v_s_531_, 2);
lean_dec(v_unused_543_);
v___x_536_ = v_s_531_;
v_isShared_537_ = v_isSharedCheck_542_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_startInclusive_534_);
lean_inc(v_str_533_);
lean_dec(v_s_531_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_542_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = lean_nat_add(v_startInclusive_534_, v_pos_532_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 2, v___x_538_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_str_533_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_startInclusive_534_);
lean_ctor_set(v_reuseFailAlloc_541_, 2, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd___boxed(lean_object* v_s_544_, lean_object* v_pos_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_String_Slice_replaceEnd(v_s_544_, v_pos_545_);
lean_dec(v_pos_545_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg(lean_object* v_s_547_, lean_object* v_newStart_548_, lean_object* v_newEnd_549_){
_start:
{
lean_object* v_str_550_; lean_object* v_startInclusive_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_560_; 
v_str_550_ = lean_ctor_get(v_s_547_, 0);
v_startInclusive_551_ = lean_ctor_get(v_s_547_, 1);
v_isSharedCheck_560_ = !lean_is_exclusive(v_s_547_);
if (v_isSharedCheck_560_ == 0)
{
lean_object* v_unused_561_; 
v_unused_561_ = lean_ctor_get(v_s_547_, 2);
lean_dec(v_unused_561_);
v___x_553_ = v_s_547_;
v_isShared_554_ = v_isSharedCheck_560_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_startInclusive_551_);
lean_inc(v_str_550_);
lean_dec(v_s_547_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_560_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_555_ = lean_nat_add(v_startInclusive_551_, v_newStart_548_);
v___x_556_ = lean_nat_add(v_startInclusive_551_, v_newEnd_549_);
lean_dec(v_startInclusive_551_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 2, v___x_556_);
lean_ctor_set(v___x_553_, 1, v___x_555_);
v___x_558_ = v___x_553_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_str_550_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_559_, 2, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg___boxed(lean_object* v_s_562_, lean_object* v_newStart_563_, lean_object* v_newEnd_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_String_Slice_slice___redArg(v_s_562_, v_newStart_563_, v_newEnd_564_);
lean_dec(v_newEnd_564_);
lean_dec(v_newStart_563_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice(lean_object* v_s_566_, lean_object* v_newStart_567_, lean_object* v_newEnd_568_, lean_object* v_h_569_){
_start:
{
lean_object* v_str_570_; lean_object* v_startInclusive_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_580_; 
v_str_570_ = lean_ctor_get(v_s_566_, 0);
v_startInclusive_571_ = lean_ctor_get(v_s_566_, 1);
v_isSharedCheck_580_ = !lean_is_exclusive(v_s_566_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; 
v_unused_581_ = lean_ctor_get(v_s_566_, 2);
lean_dec(v_unused_581_);
v___x_573_ = v_s_566_;
v_isShared_574_ = v_isSharedCheck_580_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_startInclusive_571_);
lean_inc(v_str_570_);
lean_dec(v_s_566_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_580_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_575_ = lean_nat_add(v_startInclusive_571_, v_newStart_567_);
v___x_576_ = lean_nat_add(v_startInclusive_571_, v_newEnd_568_);
lean_dec(v_startInclusive_571_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 2, v___x_576_);
lean_ctor_set(v___x_573_, 1, v___x_575_);
v___x_578_ = v___x_573_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_str_570_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_579_, 2, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___boxed(lean_object* v_s_582_, lean_object* v_newStart_583_, lean_object* v_newEnd_584_, lean_object* v_h_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_String_Slice_slice(v_s_582_, v_newStart_583_, v_newEnd_584_, v_h_585_);
lean_dec(v_newEnd_584_);
lean_dec(v_newStart_583_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg(lean_object* v_s_587_, lean_object* v_newStart_588_, lean_object* v_newEnd_589_){
_start:
{
lean_object* v_str_590_; lean_object* v_startInclusive_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_600_; 
v_str_590_ = lean_ctor_get(v_s_587_, 0);
v_startInclusive_591_ = lean_ctor_get(v_s_587_, 1);
v_isSharedCheck_600_ = !lean_is_exclusive(v_s_587_);
if (v_isSharedCheck_600_ == 0)
{
lean_object* v_unused_601_; 
v_unused_601_ = lean_ctor_get(v_s_587_, 2);
lean_dec(v_unused_601_);
v___x_593_ = v_s_587_;
v_isShared_594_ = v_isSharedCheck_600_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_startInclusive_591_);
lean_inc(v_str_590_);
lean_dec(v_s_587_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_600_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_595_ = lean_nat_add(v_startInclusive_591_, v_newStart_588_);
v___x_596_ = lean_nat_add(v_startInclusive_591_, v_newEnd_589_);
lean_dec(v_startInclusive_591_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 2, v___x_596_);
lean_ctor_set(v___x_593_, 1, v___x_595_);
v___x_598_ = v___x_593_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_str_590_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_599_, 2, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg___boxed(lean_object* v_s_602_, lean_object* v_newStart_603_, lean_object* v_newEnd_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_String_Slice_replaceStartEnd___redArg(v_s_602_, v_newStart_603_, v_newEnd_604_);
lean_dec(v_newEnd_604_);
lean_dec(v_newStart_603_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd(lean_object* v_s_606_, lean_object* v_newStart_607_, lean_object* v_newEnd_608_, lean_object* v_h_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_String_Slice_replaceStartEnd___redArg(v_s_606_, v_newStart_607_, v_newEnd_608_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___boxed(lean_object* v_s_611_, lean_object* v_newStart_612_, lean_object* v_newEnd_613_, lean_object* v_h_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_String_Slice_replaceStartEnd(v_s_611_, v_newStart_612_, v_newEnd_613_, v_h_614_);
lean_dec(v_newEnd_613_);
lean_dec(v_newStart_612_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f(lean_object* v_s_616_, lean_object* v_newStart_617_, lean_object* v_newEnd_618_){
_start:
{
uint8_t v___x_619_; 
v___x_619_ = lean_nat_dec_le(v_newStart_617_, v_newEnd_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
lean_dec_ref(v_s_616_);
v___x_620_ = lean_box(0);
return v___x_620_;
}
else
{
lean_object* v_str_621_; lean_object* v_startInclusive_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_632_; 
v_str_621_ = lean_ctor_get(v_s_616_, 0);
v_startInclusive_622_ = lean_ctor_get(v_s_616_, 1);
v_isSharedCheck_632_ = !lean_is_exclusive(v_s_616_);
if (v_isSharedCheck_632_ == 0)
{
lean_object* v_unused_633_; 
v_unused_633_ = lean_ctor_get(v_s_616_, 2);
lean_dec(v_unused_633_);
v___x_624_ = v_s_616_;
v_isShared_625_ = v_isSharedCheck_632_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_startInclusive_622_);
lean_inc(v_str_621_);
lean_dec(v_s_616_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_632_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_626_ = lean_nat_add(v_startInclusive_622_, v_newStart_617_);
v___x_627_ = lean_nat_add(v_startInclusive_622_, v_newEnd_618_);
lean_dec(v_startInclusive_622_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 2, v___x_627_);
lean_ctor_set(v___x_624_, 1, v___x_626_);
v___x_629_ = v___x_624_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_str_621_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_631_, 2, v___x_627_);
v___x_629_ = v_reuseFailAlloc_631_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_630_; 
v___x_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f___boxed(lean_object* v_s_634_, lean_object* v_newStart_635_, lean_object* v_newEnd_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_String_Slice_slice_x3f(v_s_634_, v_newStart_635_, v_newEnd_636_);
lean_dec(v_newEnd_636_);
lean_dec(v_newStart_635_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_slice_x21_spec__0(lean_object* v_msg_638_){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = l_String_instInhabitedSlice;
v___x_640_ = lean_panic_fn_borrowed(v___x_639_, v_msg_638_);
return v___x_640_;
}
}
static lean_object* _init_l_String_Slice_slice_x21___closed__2(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_643_ = ((lean_object*)(l_String_Slice_slice_x21___closed__1));
v___x_644_ = lean_unsigned_to_nat(4u);
v___x_645_ = lean_unsigned_to_nat(1046u);
v___x_646_ = ((lean_object*)(l_String_Slice_slice_x21___closed__0));
v___x_647_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_648_ = l_mkPanicMessageWithDecl(v___x_647_, v___x_646_, v___x_645_, v___x_644_, v___x_643_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x21(lean_object* v_s_649_, lean_object* v_newStart_650_, lean_object* v_newEnd_651_){
_start:
{
uint8_t v___x_652_; 
v___x_652_ = lean_nat_dec_le(v_newStart_650_, v_newEnd_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; 
lean_dec_ref(v_s_649_);
v___x_653_ = lean_obj_once(&l_String_Slice_slice_x21___closed__2, &l_String_Slice_slice_x21___closed__2_once, _init_l_String_Slice_slice_x21___closed__2);
v___x_654_ = l_panic___at___00String_Slice_slice_x21_spec__0(v___x_653_);
return v___x_654_;
}
else
{
lean_object* v_str_655_; lean_object* v_startInclusive_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_665_; 
v_str_655_ = lean_ctor_get(v_s_649_, 0);
v_startInclusive_656_ = lean_ctor_get(v_s_649_, 1);
v_isSharedCheck_665_ = !lean_is_exclusive(v_s_649_);
if (v_isSharedCheck_665_ == 0)
{
lean_object* v_unused_666_; 
v_unused_666_ = lean_ctor_get(v_s_649_, 2);
lean_dec(v_unused_666_);
v___x_658_ = v_s_649_;
v_isShared_659_ = v_isSharedCheck_665_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_startInclusive_656_);
lean_inc(v_str_655_);
lean_dec(v_s_649_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_665_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_660_ = lean_nat_add(v_startInclusive_656_, v_newStart_650_);
v___x_661_ = lean_nat_add(v_startInclusive_656_, v_newEnd_651_);
lean_dec(v_startInclusive_656_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 2, v___x_661_);
lean_ctor_set(v___x_658_, 1, v___x_660_);
v___x_663_ = v___x_658_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_str_655_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_664_, 2, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x21___boxed(lean_object* v_s_667_, lean_object* v_newStart_668_, lean_object* v_newEnd_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_String_Slice_slice_x21(v_s_667_, v_newStart_668_, v_newEnd_669_);
lean_dec(v_newEnd_669_);
lean_dec(v_newStart_668_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21(lean_object* v_s_671_, lean_object* v_newStart_672_, lean_object* v_newEnd_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_String_Slice_slice_x21(v_s_671_, v_newStart_672_, v_newEnd_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21___boxed(lean_object* v_s_675_, lean_object* v_newStart_676_, lean_object* v_newEnd_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_String_Slice_replaceStartEnd_x21(v_s_675_, v_newStart_676_, v_newEnd_677_);
lean_dec(v_newEnd_677_);
lean_dec(v_newStart_676_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_String_decodeChar___boxed(lean_object* v_s_682_, lean_object* v_byteIdx_683_, lean_object* v_h_684_){
_start:
{
uint32_t v_res_685_; lean_object* v_r_686_; 
v_res_685_ = lean_string_utf8_get_fast(v_s_682_, v_byteIdx_683_);
lean_dec(v_byteIdx_683_);
lean_dec_ref(v_s_682_);
v_r_686_ = lean_box_uint32(v_res_685_);
return v_r_686_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get___redArg(lean_object* v_s_687_, lean_object* v_pos_688_){
_start:
{
lean_object* v_str_689_; lean_object* v_startInclusive_690_; lean_object* v___x_691_; uint32_t v___x_692_; 
v_str_689_ = lean_ctor_get(v_s_687_, 0);
v_startInclusive_690_ = lean_ctor_get(v_s_687_, 1);
v___x_691_ = lean_nat_add(v_startInclusive_690_, v_pos_688_);
v___x_692_ = lean_string_utf8_get_fast(v_str_689_, v___x_691_);
lean_dec(v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___redArg___boxed(lean_object* v_s_693_, lean_object* v_pos_694_){
_start:
{
uint32_t v_res_695_; lean_object* v_r_696_; 
v_res_695_ = l_String_Slice_Pos_get___redArg(v_s_693_, v_pos_694_);
lean_dec(v_pos_694_);
lean_dec_ref(v_s_693_);
v_r_696_ = lean_box_uint32(v_res_695_);
return v_r_696_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get(lean_object* v_s_697_, lean_object* v_pos_698_, lean_object* v_h_699_){
_start:
{
lean_object* v_str_700_; lean_object* v_startInclusive_701_; lean_object* v___x_702_; uint32_t v___x_703_; 
v_str_700_ = lean_ctor_get(v_s_697_, 0);
v_startInclusive_701_ = lean_ctor_get(v_s_697_, 1);
v___x_702_ = lean_nat_add(v_startInclusive_701_, v_pos_698_);
v___x_703_ = lean_string_utf8_get_fast(v_str_700_, v___x_702_);
lean_dec(v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___boxed(lean_object* v_s_704_, lean_object* v_pos_705_, lean_object* v_h_706_){
_start:
{
uint32_t v_res_707_; lean_object* v_r_708_; 
v_res_707_ = l_String_Slice_Pos_get(v_s_704_, v_pos_705_, v_h_706_);
lean_dec(v_pos_705_);
lean_dec_ref(v_s_704_);
v_r_708_ = lean_box_uint32(v_res_707_);
return v_r_708_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f(lean_object* v_s_709_, lean_object* v_pos_710_){
_start:
{
lean_object* v_str_711_; lean_object* v_startInclusive_712_; lean_object* v_endExclusive_713_; lean_object* v___x_714_; uint8_t v_decide_715_; 
v_str_711_ = lean_ctor_get(v_s_709_, 0);
v_startInclusive_712_ = lean_ctor_get(v_s_709_, 1);
v_endExclusive_713_ = lean_ctor_get(v_s_709_, 2);
v___x_714_ = lean_nat_sub(v_endExclusive_713_, v_startInclusive_712_);
v_decide_715_ = lean_nat_dec_eq(v_pos_710_, v___x_714_);
lean_dec(v___x_714_);
if (v_decide_715_ == 0)
{
lean_object* v___x_716_; uint32_t v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_716_ = lean_nat_add(v_startInclusive_712_, v_pos_710_);
v___x_717_ = lean_string_utf8_get_fast(v_str_711_, v___x_716_);
lean_dec(v___x_716_);
v___x_718_ = lean_box_uint32(v___x_717_);
v___x_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
else
{
lean_object* v___x_720_; 
v___x_720_ = lean_box(0);
return v___x_720_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f___boxed(lean_object* v_s_721_, lean_object* v_pos_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_String_Slice_Pos_get_x3f(v_s_721_, v_pos_722_);
lean_dec(v_pos_722_);
lean_dec_ref(v_s_721_);
return v_res_723_;
}
}
static lean_object* _init_l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1(void){
_start:
{
uint32_t v___x_724_; lean_object* v___x_725_; 
v___x_724_ = 65;
v___x_725_ = lean_box_uint32(v___x_724_);
return v___x_725_;
}
}
LEAN_EXPORT uint32_t l_panic___at___00String_Slice_Pos_get_x21_spec__0(lean_object* v_msg_726_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; uint32_t v___x_729_; 
v___x_727_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1;
v___x_728_ = lean_panic_fn_borrowed(v___x_727_, v_msg_726_);
v___x_729_ = lean_unbox_uint32(v___x_728_);
lean_dec(v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed(lean_object* v_msg_730_){
_start:
{
uint32_t v_res_731_; lean_object* v_r_732_; 
v_res_731_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v_msg_730_);
v_r_732_ = lean_box_uint32(v_res_731_);
return v_r_732_;
}
}
static lean_object* _init_l_String_Slice_Pos_get_x21___closed__2(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_735_ = ((lean_object*)(l_String_Slice_Pos_get_x21___closed__1));
v___x_736_ = lean_unsigned_to_nat(29u);
v___x_737_ = lean_unsigned_to_nat(1131u);
v___x_738_ = ((lean_object*)(l_String_Slice_Pos_get_x21___closed__0));
v___x_739_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_740_ = l_mkPanicMessageWithDecl(v___x_739_, v___x_738_, v___x_737_, v___x_736_, v___x_735_);
return v___x_740_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get_x21(lean_object* v_s_741_, lean_object* v_pos_742_){
_start:
{
lean_object* v_str_743_; lean_object* v_startInclusive_744_; lean_object* v_endExclusive_745_; lean_object* v___x_746_; uint8_t v_decide_747_; 
v_str_743_ = lean_ctor_get(v_s_741_, 0);
v_startInclusive_744_ = lean_ctor_get(v_s_741_, 1);
v_endExclusive_745_ = lean_ctor_get(v_s_741_, 2);
v___x_746_ = lean_nat_sub(v_endExclusive_745_, v_startInclusive_744_);
v_decide_747_ = lean_nat_dec_eq(v_pos_742_, v___x_746_);
lean_dec(v___x_746_);
if (v_decide_747_ == 0)
{
lean_object* v___x_748_; uint32_t v___x_749_; 
v___x_748_ = lean_nat_add(v_startInclusive_744_, v_pos_742_);
v___x_749_ = lean_string_utf8_get_fast(v_str_743_, v___x_748_);
lean_dec(v___x_748_);
return v___x_749_;
}
else
{
lean_object* v___x_750_; uint32_t v___x_751_; 
v___x_750_ = lean_obj_once(&l_String_Slice_Pos_get_x21___closed__2, &l_String_Slice_Pos_get_x21___closed__2_once, _init_l_String_Slice_Pos_get_x21___closed__2);
v___x_751_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v___x_750_);
return v___x_751_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x21___boxed(lean_object* v_s_752_, lean_object* v_pos_753_){
_start:
{
uint32_t v_res_754_; lean_object* v_r_755_; 
v_res_754_ = l_String_Slice_Pos_get_x21(v_s_752_, v_pos_753_);
lean_dec(v_pos_753_);
lean_dec_ref(v_s_752_);
v_r_755_ = lean_box_uint32(v_res_754_);
return v_r_755_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg(lean_object* v_pos_756_){
_start:
{
lean_inc(v_pos_756_);
return v_pos_756_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg___boxed(lean_object* v_pos_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_String_Pos_toSlice___redArg(v_pos_757_);
lean_dec(v_pos_757_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice(lean_object* v_s_759_, lean_object* v_pos_760_){
_start:
{
lean_inc(v_pos_760_);
return v_pos_760_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___boxed(lean_object* v_s_761_, lean_object* v_pos_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_String_Pos_toSlice(v_s_761_, v_pos_762_);
lean_dec(v_pos_762_);
lean_dec_ref(v_s_761_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg(lean_object* v_pos_764_){
_start:
{
lean_inc(v_pos_764_);
return v_pos_764_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg___boxed(lean_object* v_pos_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_String_Pos_ofToSlice___redArg(v_pos_765_);
lean_dec(v_pos_765_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice(lean_object* v_s_767_, lean_object* v_pos_768_){
_start:
{
lean_inc(v_pos_768_);
return v_pos_768_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___boxed(lean_object* v_s_769_, lean_object* v_pos_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_String_Pos_ofToSlice(v_s_769_, v_pos_770_);
lean_dec(v_pos_770_);
lean_dec_ref(v_s_769_);
return v_res_771_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get___redArg(lean_object* v_s_772_, lean_object* v_pos_773_){
_start:
{
uint32_t v___x_774_; 
v___x_774_ = lean_string_utf8_get_fast(v_s_772_, v_pos_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get___redArg___boxed(lean_object* v_s_775_, lean_object* v_pos_776_){
_start:
{
uint32_t v_res_777_; lean_object* v_r_778_; 
v_res_777_ = l_String_Pos_get___redArg(v_s_775_, v_pos_776_);
lean_dec(v_pos_776_);
lean_dec_ref(v_s_775_);
v_r_778_ = lean_box_uint32(v_res_777_);
return v_r_778_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get(lean_object* v_s_779_, lean_object* v_pos_780_, lean_object* v_h_781_){
_start:
{
uint32_t v___x_782_; 
v___x_782_ = lean_string_utf8_get_fast(v_s_779_, v_pos_780_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get___boxed(lean_object* v_s_783_, lean_object* v_pos_784_, lean_object* v_h_785_){
_start:
{
uint32_t v_res_786_; lean_object* v_r_787_; 
v_res_786_ = l_String_Pos_get(v_s_783_, v_pos_784_, v_h_785_);
lean_dec(v_pos_784_);
lean_dec_ref(v_s_783_);
v_r_787_ = lean_box_uint32(v_res_786_);
return v_r_787_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x3f(lean_object* v_s_788_, lean_object* v_pos_789_){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_790_ = lean_unsigned_to_nat(0u);
v___x_791_ = lean_string_utf8_byte_size(v_s_788_);
v___x_792_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_792_, 0, v_s_788_);
lean_ctor_set(v___x_792_, 1, v___x_790_);
lean_ctor_set(v___x_792_, 2, v___x_791_);
v___x_793_ = l_String_Slice_Pos_get_x3f(v___x_792_, v_pos_789_);
lean_dec_ref_known(v___x_792_, 3);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x3f___boxed(lean_object* v_s_794_, lean_object* v_pos_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_String_Pos_get_x3f(v_s_794_, v_pos_795_);
lean_dec(v_pos_795_);
return v_res_796_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get_x21(lean_object* v_s_797_, lean_object* v_pos_798_){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; uint32_t v___x_802_; 
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = lean_string_utf8_byte_size(v_s_797_);
v___x_801_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_801_, 0, v_s_797_);
lean_ctor_set(v___x_801_, 1, v___x_799_);
lean_ctor_set(v___x_801_, 2, v___x_800_);
v___x_802_ = l_String_Slice_Pos_get_x21(v___x_801_, v_pos_798_);
lean_dec_ref_known(v___x_801_, 3);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x21___boxed(lean_object* v_s_803_, lean_object* v_pos_804_){
_start:
{
uint32_t v_res_805_; lean_object* v_r_806_; 
v_res_805_ = l_String_Pos_get_x21(v_s_803_, v_pos_804_);
lean_dec(v_pos_804_);
v_r_806_ = lean_box_uint32(v_res_805_);
return v_r_806_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_byte___redArg(lean_object* v_s_807_, lean_object* v_pos_808_){
_start:
{
uint8_t v___x_809_; 
v___x_809_ = lean_string_get_byte_fast(v_s_807_, v_pos_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_byte___redArg___boxed(lean_object* v_s_810_, lean_object* v_pos_811_){
_start:
{
uint8_t v_res_812_; lean_object* v_r_813_; 
v_res_812_ = l_String_Pos_byte___redArg(v_s_810_, v_pos_811_);
lean_dec_ref(v_s_810_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_byte(lean_object* v_s_814_, lean_object* v_pos_815_, lean_object* v_h_816_){
_start:
{
uint8_t v___x_817_; 
v___x_817_ = lean_string_get_byte_fast(v_s_814_, v_pos_815_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_byte___boxed(lean_object* v_s_818_, lean_object* v_pos_819_, lean_object* v_h_820_){
_start:
{
uint8_t v_res_821_; lean_object* v_r_822_; 
v_res_821_ = l_String_Pos_byte(v_s_818_, v_pos_819_, v_h_820_);
lean_dec_ref(v_s_818_);
v_r_822_ = lean_box(v_res_821_);
return v_r_822_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg(lean_object* v_pos_823_){
_start:
{
lean_inc(v_pos_823_);
return v_pos_823_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg___boxed(lean_object* v_pos_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_String_Pos_ofCopy___redArg(v_pos_824_);
lean_dec(v_pos_824_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy(lean_object* v_s_826_, lean_object* v_pos_827_){
_start:
{
lean_inc(v_pos_827_);
return v_pos_827_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___boxed(lean_object* v_s_828_, lean_object* v_pos_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_String_Pos_ofCopy(v_s_828_, v_pos_829_);
lean_dec(v_pos_829_);
lean_dec_ref(v_s_828_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg(lean_object* v_pos_831_){
_start:
{
lean_inc(v_pos_831_);
return v_pos_831_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg___boxed(lean_object* v_pos_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_String_Slice_Pos_copy___redArg(v_pos_832_);
lean_dec(v_pos_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy(lean_object* v_s_834_, lean_object* v_pos_835_){
_start:
{
lean_inc(v_pos_835_);
return v_pos_835_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___boxed(lean_object* v_s_836_, lean_object* v_pos_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_String_Slice_Pos_copy(v_s_836_, v_pos_837_);
lean_dec(v_pos_837_);
lean_dec_ref(v_s_836_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg(lean_object* v_pos_839_){
_start:
{
lean_inc(v_pos_839_);
return v_pos_839_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg___boxed(lean_object* v_pos_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_String_Slice_Pos_toCopy___redArg(v_pos_840_);
lean_dec(v_pos_840_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy(lean_object* v_s_842_, lean_object* v_pos_843_){
_start:
{
lean_inc(v_pos_843_);
return v_pos_843_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___boxed(lean_object* v_s_844_, lean_object* v_pos_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_String_Slice_Pos_toCopy(v_s_844_, v_pos_845_);
lean_dec(v_pos_845_);
lean_dec_ref(v_s_844_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg(lean_object* v_p_u2080_847_, lean_object* v_pos_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = lean_nat_add(v_p_u2080_847_, v_pos_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg___boxed(lean_object* v_p_u2080_850_, lean_object* v_pos_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_String_Slice_Pos_ofSliceFrom___redArg(v_p_u2080_850_, v_pos_851_);
lean_dec(v_pos_851_);
lean_dec(v_p_u2080_850_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom(lean_object* v_s_853_, lean_object* v_p_u2080_854_, lean_object* v_pos_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = lean_nat_add(v_p_u2080_854_, v_pos_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___boxed(lean_object* v_s_857_, lean_object* v_p_u2080_858_, lean_object* v_pos_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_String_Slice_Pos_ofSliceFrom(v_s_857_, v_p_u2080_858_, v_pos_859_);
lean_dec(v_pos_859_);
lean_dec(v_p_u2080_858_);
lean_dec_ref(v_s_857_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg(lean_object* v_p_u2080_861_, lean_object* v_pos_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = lean_nat_add(v_p_u2080_861_, v_pos_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg___boxed(lean_object* v_p_u2080_864_, lean_object* v_pos_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_String_Slice_Pos_ofReplaceStart___redArg(v_p_u2080_864_, v_pos_865_);
lean_dec(v_pos_865_);
lean_dec(v_p_u2080_864_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart(lean_object* v_s_867_, lean_object* v_p_u2080_868_, lean_object* v_pos_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = lean_nat_add(v_p_u2080_868_, v_pos_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___boxed(lean_object* v_s_871_, lean_object* v_p_u2080_872_, lean_object* v_pos_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_String_Slice_Pos_ofReplaceStart(v_s_871_, v_p_u2080_872_, v_pos_873_);
lean_dec(v_pos_873_);
lean_dec(v_p_u2080_872_);
lean_dec_ref(v_s_871_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg(lean_object* v_p_u2080_875_, lean_object* v_pos_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = lean_nat_sub(v_pos_876_, v_p_u2080_875_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg___boxed(lean_object* v_p_u2080_878_, lean_object* v_pos_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_String_Slice_Pos_sliceFrom___redArg(v_p_u2080_878_, v_pos_879_);
lean_dec(v_pos_879_);
lean_dec(v_p_u2080_878_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom(lean_object* v_s_881_, lean_object* v_p_u2080_882_, lean_object* v_pos_883_, lean_object* v_h_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = lean_nat_sub(v_pos_883_, v_p_u2080_882_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___boxed(lean_object* v_s_886_, lean_object* v_p_u2080_887_, lean_object* v_pos_888_, lean_object* v_h_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_String_Slice_Pos_sliceFrom(v_s_886_, v_p_u2080_887_, v_pos_888_, v_h_889_);
lean_dec(v_pos_888_);
lean_dec(v_p_u2080_887_);
lean_dec_ref(v_s_886_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg(lean_object* v_p_u2080_891_, lean_object* v_pos_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = lean_nat_sub(v_pos_892_, v_p_u2080_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg___boxed(lean_object* v_p_u2080_894_, lean_object* v_pos_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_String_Slice_Pos_toReplaceStart___redArg(v_p_u2080_894_, v_pos_895_);
lean_dec(v_pos_895_);
lean_dec(v_p_u2080_894_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart(lean_object* v_s_897_, lean_object* v_p_u2080_898_, lean_object* v_pos_899_, lean_object* v_h_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = lean_nat_sub(v_pos_899_, v_p_u2080_898_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___boxed(lean_object* v_s_902_, lean_object* v_p_u2080_903_, lean_object* v_pos_904_, lean_object* v_h_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_String_Slice_Pos_toReplaceStart(v_s_902_, v_p_u2080_903_, v_pos_904_, v_h_905_);
lean_dec(v_pos_904_);
lean_dec(v_p_u2080_903_);
lean_dec_ref(v_s_902_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg(lean_object* v_pos_907_){
_start:
{
lean_inc(v_pos_907_);
return v_pos_907_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg___boxed(lean_object* v_pos_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_String_Slice_Pos_ofSliceTo___redArg(v_pos_908_);
lean_dec(v_pos_908_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo(lean_object* v_s_910_, lean_object* v_p_u2080_911_, lean_object* v_pos_912_){
_start:
{
lean_inc(v_pos_912_);
return v_pos_912_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___boxed(lean_object* v_s_913_, lean_object* v_p_u2080_914_, lean_object* v_pos_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_String_Slice_Pos_ofSliceTo(v_s_913_, v_p_u2080_914_, v_pos_915_);
lean_dec(v_pos_915_);
lean_dec(v_p_u2080_914_);
lean_dec_ref(v_s_913_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg(lean_object* v_pos_917_){
_start:
{
lean_inc(v_pos_917_);
return v_pos_917_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg___boxed(lean_object* v_pos_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_String_Slice_Pos_ofReplaceEnd___redArg(v_pos_918_);
lean_dec(v_pos_918_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd(lean_object* v_s_920_, lean_object* v_p_u2080_921_, lean_object* v_pos_922_){
_start:
{
lean_inc(v_pos_922_);
return v_pos_922_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___boxed(lean_object* v_s_923_, lean_object* v_p_u2080_924_, lean_object* v_pos_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_String_Slice_Pos_ofReplaceEnd(v_s_923_, v_p_u2080_924_, v_pos_925_);
lean_dec(v_pos_925_);
lean_dec(v_p_u2080_924_);
lean_dec_ref(v_s_923_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg(lean_object* v_pos_927_){
_start:
{
lean_inc(v_pos_927_);
return v_pos_927_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg___boxed(lean_object* v_pos_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_String_Slice_Pos_sliceTo___redArg(v_pos_928_);
lean_dec(v_pos_928_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo(lean_object* v_s_930_, lean_object* v_p_u2080_931_, lean_object* v_pos_932_, lean_object* v_h_933_){
_start:
{
lean_inc(v_pos_932_);
return v_pos_932_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___boxed(lean_object* v_s_934_, lean_object* v_p_u2080_935_, lean_object* v_pos_936_, lean_object* v_h_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_String_Slice_Pos_sliceTo(v_s_934_, v_p_u2080_935_, v_pos_936_, v_h_937_);
lean_dec(v_pos_936_);
lean_dec(v_p_u2080_935_);
lean_dec_ref(v_s_934_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg(lean_object* v_pos_939_){
_start:
{
lean_inc(v_pos_939_);
return v_pos_939_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg___boxed(lean_object* v_pos_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_String_Slice_Pos_toReplaceEnd___redArg(v_pos_940_);
lean_dec(v_pos_940_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd(lean_object* v_s_942_, lean_object* v_p_u2080_943_, lean_object* v_pos_944_, lean_object* v_h_945_){
_start:
{
lean_inc(v_pos_944_);
return v_pos_944_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___boxed(lean_object* v_s_946_, lean_object* v_p_u2080_947_, lean_object* v_pos_948_, lean_object* v_h_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_String_Slice_Pos_toReplaceEnd(v_s_946_, v_p_u2080_947_, v_pos_948_, v_h_949_);
lean_dec(v_pos_948_);
lean_dec(v_p_u2080_947_);
lean_dec_ref(v_s_946_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg(lean_object* v_s_951_, lean_object* v_pos_952_){
_start:
{
lean_object* v_str_953_; lean_object* v_startInclusive_954_; lean_object* v___x_955_; uint8_t v___x_956_; uint8_t v___x_957_; uint8_t v___x_958_; uint8_t v___x_959_; uint8_t v___x_960_; 
v_str_953_ = lean_ctor_get(v_s_951_, 0);
v_startInclusive_954_ = lean_ctor_get(v_s_951_, 1);
v___x_955_ = lean_nat_add(v_startInclusive_954_, v_pos_952_);
v___x_956_ = lean_string_get_byte_fast(v_str_953_, v___x_955_);
v___x_957_ = 128;
v___x_958_ = lean_uint8_land(v___x_956_, v___x_957_);
v___x_959_ = 0;
v___x_960_ = lean_uint8_dec_eq(v___x_958_, v___x_959_);
if (v___x_960_ == 0)
{
uint8_t v___x_961_; uint8_t v___x_962_; uint8_t v___x_963_; uint8_t v___x_964_; 
v___x_961_ = 224;
v___x_962_ = lean_uint8_land(v___x_956_, v___x_961_);
v___x_963_ = 192;
v___x_964_ = lean_uint8_dec_eq(v___x_962_, v___x_963_);
if (v___x_964_ == 0)
{
uint8_t v___x_965_; uint8_t v___x_966_; uint8_t v___x_967_; 
v___x_965_ = 240;
v___x_966_ = lean_uint8_land(v___x_956_, v___x_965_);
v___x_967_ = lean_uint8_dec_eq(v___x_966_, v___x_961_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_unsigned_to_nat(4u);
v___x_969_ = lean_nat_add(v_pos_952_, v___x_968_);
return v___x_969_;
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_unsigned_to_nat(3u);
v___x_971_ = lean_nat_add(v_pos_952_, v___x_970_);
return v___x_971_;
}
}
else
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = lean_unsigned_to_nat(2u);
v___x_973_ = lean_nat_add(v_pos_952_, v___x_972_);
return v___x_973_;
}
}
else
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_unsigned_to_nat(1u);
v___x_975_ = lean_nat_add(v_pos_952_, v___x_974_);
return v___x_975_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg___boxed(lean_object* v_s_976_, lean_object* v_pos_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_String_Slice_Pos_next___redArg(v_s_976_, v_pos_977_);
lean_dec(v_pos_977_);
lean_dec_ref(v_s_976_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next(lean_object* v_s_979_, lean_object* v_pos_980_, lean_object* v_h_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_String_Slice_Pos_next___redArg(v_s_979_, v_pos_980_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___boxed(lean_object* v_s_983_, lean_object* v_pos_984_, lean_object* v_h_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_String_Slice_Pos_next(v_s_983_, v_pos_984_, v_h_985_);
lean_dec(v_pos_984_);
lean_dec_ref(v_s_983_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f(lean_object* v_s_987_, lean_object* v_pos_988_){
_start:
{
lean_object* v_startInclusive_989_; lean_object* v_endExclusive_990_; lean_object* v___x_991_; uint8_t v_decide_992_; 
v_startInclusive_989_ = lean_ctor_get(v_s_987_, 1);
v_endExclusive_990_ = lean_ctor_get(v_s_987_, 2);
v___x_991_ = lean_nat_sub(v_endExclusive_990_, v_startInclusive_989_);
v_decide_992_ = lean_nat_dec_eq(v_pos_988_, v___x_991_);
lean_dec(v___x_991_);
if (v_decide_992_ == 0)
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = l_String_Slice_Pos_next___redArg(v_s_987_, v_pos_988_);
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
return v___x_994_;
}
else
{
lean_object* v___x_995_; 
v___x_995_ = lean_box(0);
return v___x_995_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f___boxed(lean_object* v_s_996_, lean_object* v_pos_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_String_Slice_Pos_next_x3f(v_s_996_, v_pos_997_);
lean_dec(v_pos_997_);
lean_dec_ref(v_s_996_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(lean_object* v_msg_999_){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_unsigned_to_nat(0u);
v___x_1001_ = lean_panic_fn_borrowed(v___x_1000_, v_msg_999_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0(lean_object* v_s_1002_, lean_object* v_msg_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v_msg_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___boxed(lean_object* v_s_1005_, lean_object* v_msg_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0(v_s_1005_, v_msg_1006_);
lean_dec_ref(v_s_1005_);
return v_res_1007_;
}
}
static lean_object* _init_l_String_Slice_Pos_next_x21___closed__2(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1010_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__1));
v___x_1011_ = lean_unsigned_to_nat(29u);
v___x_1012_ = lean_unsigned_to_nat(1518u);
v___x_1013_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__0));
v___x_1014_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1015_ = l_mkPanicMessageWithDecl(v___x_1014_, v___x_1013_, v___x_1012_, v___x_1011_, v___x_1010_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21(lean_object* v_s_1016_, lean_object* v_pos_1017_){
_start:
{
lean_object* v_startInclusive_1018_; lean_object* v_endExclusive_1019_; lean_object* v___x_1020_; uint8_t v_decide_1021_; 
v_startInclusive_1018_ = lean_ctor_get(v_s_1016_, 1);
v_endExclusive_1019_ = lean_ctor_get(v_s_1016_, 2);
v___x_1020_ = lean_nat_sub(v_endExclusive_1019_, v_startInclusive_1018_);
v_decide_1021_ = lean_nat_dec_eq(v_pos_1017_, v___x_1020_);
lean_dec(v___x_1020_);
if (v_decide_1021_ == 0)
{
lean_object* v___x_1022_; 
v___x_1022_ = l_String_Slice_Pos_next___redArg(v_s_1016_, v_pos_1017_);
return v___x_1022_;
}
else
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_obj_once(&l_String_Slice_Pos_next_x21___closed__2, &l_String_Slice_Pos_next_x21___closed__2_once, _init_l_String_Slice_Pos_next_x21___closed__2);
v___x_1024_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_1023_);
return v___x_1024_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21___boxed(lean_object* v_s_1025_, lean_object* v_pos_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_String_Slice_Pos_next_x21(v_s_1025_, v_pos_1026_);
lean_dec(v_pos_1026_);
lean_dec_ref(v_s_1025_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg(lean_object* v_s_1028_, lean_object* v_off_1029_){
_start:
{
uint8_t v___y_1031_; lean_object* v_str_1037_; lean_object* v_startInclusive_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; uint8_t v___x_1041_; uint8_t v___x_1042_; uint8_t v___x_1043_; uint8_t v___x_1044_; 
v_str_1037_ = lean_ctor_get(v_s_1028_, 0);
v_startInclusive_1038_ = lean_ctor_get(v_s_1028_, 1);
v___x_1039_ = lean_nat_add(v_startInclusive_1038_, v_off_1029_);
v___x_1040_ = lean_string_get_byte_fast(v_str_1037_, v___x_1039_);
v___x_1041_ = 128;
v___x_1042_ = lean_uint8_land(v___x_1040_, v___x_1041_);
v___x_1043_ = 0;
v___x_1044_ = lean_uint8_dec_eq(v___x_1042_, v___x_1043_);
if (v___x_1044_ == 0)
{
uint8_t v___x_1045_; uint8_t v___x_1046_; uint8_t v___x_1047_; uint8_t v___x_1048_; 
v___x_1045_ = 224;
v___x_1046_ = lean_uint8_land(v___x_1040_, v___x_1045_);
v___x_1047_ = 192;
v___x_1048_ = lean_uint8_dec_eq(v___x_1046_, v___x_1047_);
if (v___x_1048_ == 0)
{
uint8_t v___x_1049_; uint8_t v___x_1050_; uint8_t v___x_1051_; 
v___x_1049_ = 240;
v___x_1050_ = lean_uint8_land(v___x_1040_, v___x_1049_);
v___x_1051_ = lean_uint8_dec_eq(v___x_1050_, v___x_1045_);
if (v___x_1051_ == 0)
{
uint8_t v___x_1052_; uint8_t v___x_1053_; uint8_t v___x_1054_; 
v___x_1052_ = 248;
v___x_1053_ = lean_uint8_land(v___x_1040_, v___x_1052_);
v___x_1054_ = lean_uint8_dec_eq(v___x_1053_, v___x_1049_);
v___y_1031_ = v___x_1054_;
goto v___jp_1030_;
}
else
{
v___y_1031_ = v___x_1051_;
goto v___jp_1030_;
}
}
else
{
v___y_1031_ = v___x_1048_;
goto v___jp_1030_;
}
}
else
{
v___y_1031_ = v___x_1044_;
goto v___jp_1030_;
}
v___jp_1030_:
{
if (v___y_1031_ == 0)
{
lean_object* v_zero_1032_; uint8_t v_isZero_1033_; lean_object* v_one_1034_; lean_object* v_n_1035_; 
v_zero_1032_ = lean_unsigned_to_nat(0u);
v_isZero_1033_ = lean_nat_dec_eq(v_off_1029_, v_zero_1032_);
v_one_1034_ = lean_unsigned_to_nat(1u);
v_n_1035_ = lean_nat_sub(v_off_1029_, v_one_1034_);
lean_dec(v_off_1029_);
v_off_1029_ = v_n_1035_;
goto _start;
}
else
{
return v_off_1029_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg___boxed(lean_object* v_s_1055_, lean_object* v_off_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1055_, v_off_1056_);
lean_dec_ref(v_s_1055_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go(lean_object* v_s_1058_, lean_object* v_off_1059_, lean_object* v_h_u2081_1060_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1058_, v_off_1059_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___boxed(lean_object* v_s_1062_, lean_object* v_off_1063_, lean_object* v_h_u2081_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_String_Slice_Pos_prevAux_go(v_s_1062_, v_off_1063_, v_h_u2081_1064_);
lean_dec_ref(v_s_1062_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg(lean_object* v_s_1066_, lean_object* v_pos_1067_){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = lean_unsigned_to_nat(1u);
v___x_1069_ = lean_nat_sub(v_pos_1067_, v___x_1068_);
v___x_1070_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1066_, v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg___boxed(lean_object* v_s_1071_, lean_object* v_pos_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_String_Slice_Pos_prevAux___redArg(v_s_1071_, v_pos_1072_);
lean_dec(v_pos_1072_);
lean_dec_ref(v_s_1071_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux(lean_object* v_s_1074_, lean_object* v_pos_1075_, lean_object* v_h_1076_){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1077_ = lean_unsigned_to_nat(1u);
v___x_1078_ = lean_nat_sub(v_pos_1075_, v___x_1077_);
v___x_1079_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1074_, v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___boxed(lean_object* v_s_1080_, lean_object* v_pos_1081_, lean_object* v_h_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_String_Slice_Pos_prevAux(v_s_1080_, v_pos_1081_, v_h_1082_);
lean_dec(v_pos_1081_);
lean_dec_ref(v_s_1080_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(lean_object* v_off_1084_, lean_object* v_h__1_1085_, lean_object* v_h__2_1086_){
_start:
{
lean_object* v_zero_1087_; uint8_t v_isZero_1088_; 
v_zero_1087_ = lean_unsigned_to_nat(0u);
v_isZero_1088_ = lean_nat_dec_eq(v_off_1084_, v_zero_1087_);
if (v_isZero_1088_ == 1)
{
lean_object* v___x_1089_; 
lean_dec(v_h__2_1086_);
v___x_1089_ = lean_apply_3(v_h__1_1085_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1089_;
}
else
{
lean_object* v_one_1090_; lean_object* v_n_1091_; lean_object* v___x_1092_; 
lean_dec(v_h__1_1085_);
v_one_1090_ = lean_unsigned_to_nat(1u);
v_n_1091_ = lean_nat_sub(v_off_1084_, v_one_1090_);
v___x_1092_ = lean_apply_4(v_h__2_1086_, v_n_1091_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1092_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg___boxed(lean_object* v_off_1093_, lean_object* v_h__1_1094_, lean_object* v_h__2_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(v_off_1093_, v_h__1_1094_, v_h__2_1095_);
lean_dec(v_off_1093_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(lean_object* v_s_1097_, lean_object* v_motive_1098_, lean_object* v_off_1099_, lean_object* v_h_u2081_1100_, lean_object* v_hbyte_1101_, lean_object* v_this_1102_, lean_object* v_h__1_1103_, lean_object* v_h__2_1104_){
_start:
{
lean_object* v_zero_1105_; uint8_t v_isZero_1106_; 
v_zero_1105_ = lean_unsigned_to_nat(0u);
v_isZero_1106_ = lean_nat_dec_eq(v_off_1099_, v_zero_1105_);
if (v_isZero_1106_ == 1)
{
lean_object* v___x_1107_; 
lean_dec(v_h__2_1104_);
v___x_1107_ = lean_apply_3(v_h__1_1103_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1107_;
}
else
{
lean_object* v_one_1108_; lean_object* v_n_1109_; lean_object* v___x_1110_; 
lean_dec(v_h__1_1103_);
v_one_1108_ = lean_unsigned_to_nat(1u);
v_n_1109_ = lean_nat_sub(v_off_1099_, v_one_1108_);
v___x_1110_ = lean_apply_4(v_h__2_1104_, v_n_1109_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1110_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___boxed(lean_object* v_s_1111_, lean_object* v_motive_1112_, lean_object* v_off_1113_, lean_object* v_h_u2081_1114_, lean_object* v_hbyte_1115_, lean_object* v_this_1116_, lean_object* v_h__1_1117_, lean_object* v_h__2_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(v_s_1111_, v_motive_1112_, v_off_1113_, v_h_u2081_1114_, v_hbyte_1115_, v_this_1116_, v_h__1_1117_, v_h__2_1118_);
lean_dec(v_off_1113_);
lean_dec_ref(v_s_1111_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg(lean_object* v_off_1120_){
_start:
{
lean_inc(v_off_1120_);
return v_off_1120_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg___boxed(lean_object* v_off_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_String_Slice_pos___redArg(v_off_1121_);
lean_dec(v_off_1121_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos(lean_object* v_s_1123_, lean_object* v_off_1124_, lean_object* v_h_1125_){
_start:
{
lean_inc(v_off_1124_);
return v_off_1124_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___boxed(lean_object* v_s_1126_, lean_object* v_off_1127_, lean_object* v_h_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_String_Slice_pos(v_s_1126_, v_off_1127_, v_h_1128_);
lean_dec(v_off_1127_);
lean_dec_ref(v_s_1126_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f(lean_object* v_s_1130_, lean_object* v_off_1131_){
_start:
{
uint8_t v___x_1132_; 
v___x_1132_ = l_String_Pos_Raw_isValidForSlice(v_s_1130_, v_off_1131_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; 
lean_dec(v_off_1131_);
v___x_1133_ = lean_box(0);
return v___x_1133_;
}
else
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1134_, 0, v_off_1131_);
return v___x_1134_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f___boxed(lean_object* v_s_1135_, lean_object* v_off_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_String_Slice_pos_x3f(v_s_1135_, v_off_1136_);
lean_dec_ref(v_s_1135_);
return v_res_1137_;
}
}
static lean_object* _init_l_String_Slice_pos_x21___closed__2(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1140_ = ((lean_object*)(l_String_Slice_pos_x21___closed__1));
v___x_1141_ = lean_unsigned_to_nat(4u);
v___x_1142_ = lean_unsigned_to_nat(1606u);
v___x_1143_ = ((lean_object*)(l_String_Slice_pos_x21___closed__0));
v___x_1144_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1145_ = l_mkPanicMessageWithDecl(v___x_1144_, v___x_1143_, v___x_1142_, v___x_1141_, v___x_1140_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21(lean_object* v_s_1146_, lean_object* v_off_1147_){
_start:
{
uint8_t v___x_1148_; 
v___x_1148_ = l_String_Pos_Raw_isValidForSlice(v_s_1146_, v_off_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = lean_obj_once(&l_String_Slice_pos_x21___closed__2, &l_String_Slice_pos_x21___closed__2_once, _init_l_String_Slice_pos_x21___closed__2);
v___x_1150_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_1149_);
return v___x_1150_;
}
else
{
lean_inc(v_off_1147_);
return v_off_1147_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21___boxed(lean_object* v_s_1151_, lean_object* v_off_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_String_Slice_pos_x21(v_s_1151_, v_off_1152_);
lean_dec(v_off_1152_);
lean_dec_ref(v_s_1151_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next___boxed(lean_object* v_s_1157_, lean_object* v_pos_1158_, lean_object* v_h_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = lean_string_utf8_next_fast(v_s_1157_, v_pos_1158_);
lean_dec(v_pos_1158_);
lean_dec_ref(v_s_1157_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x3f(lean_object* v_s_1161_, lean_object* v_pos_1162_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1163_ = lean_unsigned_to_nat(0u);
v___x_1164_ = lean_string_utf8_byte_size(v_s_1161_);
v___x_1165_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1165_, 0, v_s_1161_);
lean_ctor_set(v___x_1165_, 1, v___x_1163_);
lean_ctor_set(v___x_1165_, 2, v___x_1164_);
v___x_1166_ = l_String_Slice_Pos_next_x3f(v___x_1165_, v_pos_1162_);
lean_dec_ref_known(v___x_1165_, 3);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_box(0);
return v___x_1167_;
}
else
{
lean_object* v_val_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
v_val_1168_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1166_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_val_1168_);
lean_dec(v___x_1166_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_val_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x3f___boxed(lean_object* v_s_1176_, lean_object* v_pos_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_String_Pos_next_x3f(v_s_1176_, v_pos_1177_);
lean_dec(v_pos_1177_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21(lean_object* v_s_1179_, lean_object* v_pos_1180_){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1181_ = lean_unsigned_to_nat(0u);
v___x_1182_ = lean_string_utf8_byte_size(v_s_1179_);
v___x_1183_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1183_, 0, v_s_1179_);
lean_ctor_set(v___x_1183_, 1, v___x_1181_);
lean_ctor_set(v___x_1183_, 2, v___x_1182_);
v___x_1184_ = l_String_Slice_Pos_next_x21(v___x_1183_, v_pos_1180_);
lean_dec_ref_known(v___x_1183_, 3);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21___boxed(lean_object* v_s_1185_, lean_object* v_pos_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_String_Pos_next_x21(v_s_1185_, v_pos_1186_);
lean_dec(v_pos_1186_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg(lean_object* v_off_1188_){
_start:
{
lean_inc(v_off_1188_);
return v_off_1188_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg___boxed(lean_object* v_off_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_String_pos___redArg(v_off_1189_);
lean_dec(v_off_1189_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_String_pos(lean_object* v_s_1191_, lean_object* v_off_1192_, lean_object* v_h_1193_){
_start:
{
lean_inc(v_off_1192_);
return v_off_1192_;
}
}
LEAN_EXPORT lean_object* l_String_pos___boxed(lean_object* v_s_1194_, lean_object* v_off_1195_, lean_object* v_h_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_String_pos(v_s_1194_, v_off_1195_, v_h_1196_);
lean_dec(v_off_1195_);
lean_dec_ref(v_s_1194_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x3f(lean_object* v_s_1198_, lean_object* v_off_1199_){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1200_ = lean_unsigned_to_nat(0u);
v___x_1201_ = lean_string_utf8_byte_size(v_s_1198_);
v___x_1202_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1202_, 0, v_s_1198_);
lean_ctor_set(v___x_1202_, 1, v___x_1200_);
lean_ctor_set(v___x_1202_, 2, v___x_1201_);
v___x_1203_ = l_String_Slice_pos_x3f(v___x_1202_, v_off_1199_);
lean_dec_ref_known(v___x_1202_, 3);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_box(0);
return v___x_1204_;
}
else
{
lean_object* v_val_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
v_val_1205_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1203_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_val_1205_);
lean_dec(v___x_1203_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_val_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_pos_x21(lean_object* v_s_1213_, lean_object* v_off_1214_){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1215_ = lean_unsigned_to_nat(0u);
v___x_1216_ = lean_string_utf8_byte_size(v_s_1213_);
v___x_1217_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1217_, 0, v_s_1213_);
lean_ctor_set(v___x_1217_, 1, v___x_1215_);
lean_ctor_set(v___x_1217_, 2, v___x_1216_);
v___x_1218_ = l_String_Slice_pos_x21(v___x_1217_, v_off_1214_);
lean_dec_ref_known(v___x_1217_, 3);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x21___boxed(lean_object* v_s_1219_, lean_object* v_off_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_String_pos_x21(v_s_1219_, v_off_1220_);
lean_dec(v_off_1220_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg(lean_object* v_pos_1222_){
_start:
{
lean_inc(v_pos_1222_);
return v_pos_1222_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg___boxed(lean_object* v_pos_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_String_Slice_Pos_cast___redArg(v_pos_1223_);
lean_dec(v_pos_1223_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast(lean_object* v_s_1225_, lean_object* v_t_1226_, lean_object* v_pos_1227_, lean_object* v_h_1228_){
_start:
{
lean_inc(v_pos_1227_);
return v_pos_1227_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___boxed(lean_object* v_s_1229_, lean_object* v_t_1230_, lean_object* v_pos_1231_, lean_object* v_h_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_String_Slice_Pos_cast(v_s_1229_, v_t_1230_, v_pos_1231_, v_h_1232_);
lean_dec(v_pos_1231_);
lean_dec_ref(v_t_1230_);
lean_dec_ref(v_s_1229_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg(lean_object* v_pos_1234_){
_start:
{
lean_inc(v_pos_1234_);
return v_pos_1234_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg___boxed(lean_object* v_pos_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_String_Pos_cast___redArg(v_pos_1235_);
lean_dec(v_pos_1235_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast(lean_object* v_s_1237_, lean_object* v_t_1238_, lean_object* v_pos_1239_, lean_object* v_h_1240_){
_start:
{
lean_inc(v_pos_1239_);
return v_pos_1239_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___boxed(lean_object* v_s_1241_, lean_object* v_t_1242_, lean_object* v_pos_1243_, lean_object* v_h_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_String_Pos_cast(v_s_1241_, v_t_1242_, v_pos_1243_, v_h_1244_);
lean_dec(v_pos_1243_);
lean_dec_ref(v_t_1242_);
lean_dec_ref(v_s_1241_);
return v_res_1245_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_Raw_utf8GetAux(lean_object* v_x_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_){
_start:
{
if (lean_obj_tag(v_x_1246_) == 0)
{
uint32_t v___x_1249_; 
lean_dec(v_x_1247_);
v___x_1249_ = 65;
return v___x_1249_;
}
else
{
lean_object* v_head_1250_; lean_object* v_tail_1251_; uint8_t v_decide_1252_; 
v_head_1250_ = lean_ctor_get(v_x_1246_, 0);
v_tail_1251_ = lean_ctor_get(v_x_1246_, 1);
v_decide_1252_ = lean_nat_dec_eq(v_x_1247_, v_x_1248_);
if (v_decide_1252_ == 0)
{
uint32_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1253_ = lean_unbox_uint32(v_head_1250_);
v___x_1254_ = l_Char_utf8Size(v___x_1253_);
v___x_1255_ = lean_nat_add(v_x_1247_, v___x_1254_);
lean_dec(v___x_1254_);
lean_dec(v_x_1247_);
v_x_1246_ = v_tail_1251_;
v_x_1247_ = v___x_1255_;
goto _start;
}
else
{
uint32_t v___x_1257_; 
lean_dec(v_x_1247_);
v___x_1257_ = lean_unbox_uint32(v_head_1250_);
return v___x_1257_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux___boxed(lean_object* v_x_1258_, lean_object* v_x_1259_, lean_object* v_x_1260_){
_start:
{
uint32_t v_res_1261_; lean_object* v_r_1262_; 
v_res_1261_ = l_String_Pos_Raw_utf8GetAux(v_x_1258_, v_x_1259_, v_x_1260_);
lean_dec(v_x_1260_);
lean_dec(v_x_1258_);
v_r_1262_ = lean_box_uint32(v_res_1261_);
return v_r_1262_;
}
}
LEAN_EXPORT uint32_t l_String_utf8GetAux(lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_){
_start:
{
uint32_t v___x_1266_; 
v___x_1266_ = l_String_Pos_Raw_utf8GetAux(v_a_1263_, v_a_1264_, v_a_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux___boxed(lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_){
_start:
{
uint32_t v_res_1270_; lean_object* v_r_1271_; 
v_res_1270_ = l_String_utf8GetAux(v_a_1267_, v_a_1268_, v_a_1269_);
lean_dec(v_a_1269_);
lean_dec(v_a_1267_);
v_r_1271_ = lean_box_uint32(v_res_1270_);
return v_r_1271_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get___boxed(lean_object* v_s_1274_, lean_object* v_p_1275_){
_start:
{
uint32_t v_res_1276_; lean_object* v_r_1277_; 
v_res_1276_ = lean_string_utf8_get(v_s_1274_, v_p_1275_);
lean_dec(v_p_1275_);
lean_dec_ref(v_s_1274_);
v_r_1277_ = lean_box_uint32(v_res_1276_);
return v_r_1277_;
}
}
LEAN_EXPORT lean_object* l_String_get___boxed(lean_object* v_s_1280_, lean_object* v_p_1281_){
_start:
{
uint32_t v_res_1282_; lean_object* v_r_1283_; 
v_res_1282_ = lean_string_utf8_get(v_s_1280_, v_p_1281_);
lean_dec(v_p_1281_);
lean_dec_ref(v_s_1280_);
v_r_1283_ = lean_box_uint32(v_res_1282_);
return v_r_1283_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f(lean_object* v_x_1284_, lean_object* v_x_1285_, lean_object* v_x_1286_){
_start:
{
if (lean_obj_tag(v_x_1284_) == 0)
{
lean_object* v___x_1287_; 
lean_dec(v_x_1285_);
v___x_1287_ = lean_box(0);
return v___x_1287_;
}
else
{
lean_object* v_head_1288_; lean_object* v_tail_1289_; uint8_t v_decide_1290_; 
v_head_1288_ = lean_ctor_get(v_x_1284_, 0);
v_tail_1289_ = lean_ctor_get(v_x_1284_, 1);
v_decide_1290_ = lean_nat_dec_eq(v_x_1285_, v_x_1286_);
if (v_decide_1290_ == 0)
{
uint32_t v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1291_ = lean_unbox_uint32(v_head_1288_);
v___x_1292_ = l_Char_utf8Size(v___x_1291_);
v___x_1293_ = lean_nat_add(v_x_1285_, v___x_1292_);
lean_dec(v___x_1292_);
lean_dec(v_x_1285_);
v_x_1284_ = v_tail_1289_;
v_x_1285_ = v___x_1293_;
goto _start;
}
else
{
lean_object* v___x_1295_; 
lean_dec(v_x_1285_);
lean_inc(v_head_1288_);
v___x_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1295_, 0, v_head_1288_);
return v___x_1295_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f___boxed(lean_object* v_x_1296_, lean_object* v_x_1297_, lean_object* v_x_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_String_Pos_Raw_utf8GetAux_x3f(v_x_1296_, v_x_1297_, v_x_1298_);
lean_dec(v_x_1298_);
lean_dec(v_x_1296_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f(lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_String_Pos_Raw_utf8GetAux_x3f(v_a_1300_, v_a_1301_, v_a_1302_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f___boxed(lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_String_utf8GetAux_x3f(v_a_1304_, v_a_1305_, v_a_1306_);
lean_dec(v_a_1306_);
lean_dec(v_a_1304_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1310_, lean_object* v_a_00___x40___internal___hyg_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1310_, v_a_00___x40___internal___hyg_1311_);
lean_dec(v_a_00___x40___internal___hyg_1311_);
lean_dec_ref(v_a_00___x40___internal___hyg_1310_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_String_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1315_, lean_object* v_a_00___x40___internal___hyg_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1315_, v_a_00___x40___internal___hyg_1316_);
lean_dec(v_a_00___x40___internal___hyg_1316_);
lean_dec_ref(v_a_00___x40___internal___hyg_1315_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x21___boxed(lean_object* v_s_1320_, lean_object* v_p_1321_){
_start:
{
uint32_t v_res_1322_; lean_object* v_r_1323_; 
v_res_1322_ = lean_string_utf8_get_bang(v_s_1320_, v_p_1321_);
lean_dec(v_p_1321_);
lean_dec_ref(v_s_1320_);
v_r_1323_ = lean_box_uint32(v_res_1322_);
return v_r_1323_;
}
}
LEAN_EXPORT lean_object* l_String_get_x21___boxed(lean_object* v_s_1326_, lean_object* v_p_1327_){
_start:
{
uint32_t v_res_1328_; lean_object* v_r_1329_; 
v_res_1328_ = lean_string_utf8_get_bang(v_s_1326_, v_p_1327_);
lean_dec(v_p_1327_);
lean_dec_ref(v_s_1326_);
v_r_1329_ = lean_box_uint32(v_res_1328_);
return v_r_1329_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux(uint32_t v_c_x27_1330_, lean_object* v_x_1331_, lean_object* v_x_1332_, lean_object* v_x_1333_){
_start:
{
if (lean_obj_tag(v_x_1331_) == 0)
{
return v_x_1331_;
}
else
{
lean_object* v_head_1334_; lean_object* v_tail_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1351_; 
v_head_1334_ = lean_ctor_get(v_x_1331_, 0);
v_tail_1335_ = lean_ctor_get(v_x_1331_, 1);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_x_1331_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1337_ = v_x_1331_;
v_isShared_1338_ = v_isSharedCheck_1351_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_tail_1335_);
lean_inc(v_head_1334_);
lean_dec(v_x_1331_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1351_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
uint8_t v_decide_1339_; 
v_decide_1339_ = lean_nat_dec_eq(v_x_1332_, v_x_1333_);
if (v_decide_1339_ == 0)
{
uint32_t v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1340_ = lean_unbox_uint32(v_head_1334_);
v___x_1341_ = l_Char_utf8Size(v___x_1340_);
v___x_1342_ = lean_nat_add(v_x_1332_, v___x_1341_);
lean_dec(v___x_1341_);
v___x_1343_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1330_, v_tail_1335_, v___x_1342_, v_x_1333_);
lean_dec(v___x_1342_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 1, v___x_1343_);
v___x_1345_ = v___x_1337_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_head_1334_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
else
{
lean_object* v___x_1347_; lean_object* v___x_1349_; 
lean_dec(v_head_1334_);
v___x_1347_ = lean_box_uint32(v_c_x27_1330_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1347_);
v___x_1349_ = v___x_1337_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_tail_1335_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux___boxed(lean_object* v_c_x27_1352_, lean_object* v_x_1353_, lean_object* v_x_1354_, lean_object* v_x_1355_){
_start:
{
uint32_t v_c_x27_boxed_1356_; lean_object* v_res_1357_; 
v_c_x27_boxed_1356_ = lean_unbox_uint32(v_c_x27_1352_);
lean_dec(v_c_x27_1352_);
v_res_1357_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_boxed_1356_, v_x_1353_, v_x_1354_, v_x_1355_);
lean_dec(v_x_1355_);
lean_dec(v_x_1354_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux(uint32_t v_c_x27_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1358_, v_a_1359_, v_a_1360_, v_a_1361_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux___boxed(lean_object* v_c_x27_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_){
_start:
{
uint32_t v_c_x27_boxed_1367_; lean_object* v_res_1368_; 
v_c_x27_boxed_1367_ = lean_unbox_uint32(v_c_x27_1363_);
lean_dec(v_c_x27_1363_);
v_res_1368_ = l_String_utf8SetAux(v_c_x27_boxed_1367_, v_a_1364_, v_a_1365_, v_a_1366_);
lean_dec(v_a_1366_);
lean_dec(v_a_1365_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg(lean_object* v_s_1369_, lean_object* v_pos_1370_){
_start:
{
lean_object* v_str_1371_; lean_object* v_startInclusive_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v_str_1371_ = lean_ctor_get(v_s_1369_, 0);
v_startInclusive_1372_ = lean_ctor_get(v_s_1369_, 1);
v___x_1373_ = lean_nat_add(v_startInclusive_1372_, v_pos_1370_);
v___x_1374_ = lean_string_utf8_next_fast(v_str_1371_, v___x_1373_);
lean_dec(v___x_1373_);
v___x_1375_ = lean_nat_sub(v___x_1374_, v_startInclusive_1372_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg___boxed(lean_object* v_s_1376_, lean_object* v_pos_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_String_Slice_Pos_nextFast___redArg(v_s_1376_, v_pos_1377_);
lean_dec(v_pos_1377_);
lean_dec_ref(v_s_1376_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast(lean_object* v_s_1379_, lean_object* v_pos_1380_, lean_object* v_h_1381_){
_start:
{
lean_object* v_str_1382_; lean_object* v_startInclusive_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v_str_1382_ = lean_ctor_get(v_s_1379_, 0);
v_startInclusive_1383_ = lean_ctor_get(v_s_1379_, 1);
v___x_1384_ = lean_nat_add(v_startInclusive_1383_, v_pos_1380_);
v___x_1385_ = lean_string_utf8_next_fast(v_str_1382_, v___x_1384_);
lean_dec(v___x_1384_);
v___x_1386_ = lean_nat_sub(v___x_1385_, v_startInclusive_1383_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___boxed(lean_object* v_s_1387_, lean_object* v_pos_1388_, lean_object* v_h_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_String_Slice_Pos_nextFast(v_s_1387_, v_pos_1388_, v_h_1389_);
lean_dec(v_pos_1388_);
lean_dec_ref(v_s_1387_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_String_sliceTo(lean_object* v_s_1391_, lean_object* v_p_1392_){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = lean_unsigned_to_nat(0u);
v___x_1394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1394_, 0, v_s_1391_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
lean_ctor_set(v___x_1394_, 2, v_p_1392_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_String_replaceEnd(lean_object* v_s_1395_, lean_object* v_p_1396_){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = lean_unsigned_to_nat(0u);
v___x_1398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1398_, 0, v_s_1395_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
lean_ctor_set(v___x_1398_, 2, v_p_1396_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_String_sliceFrom(lean_object* v_s_1399_, lean_object* v_p_1400_){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = lean_string_utf8_byte_size(v_s_1399_);
v___x_1402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1402_, 0, v_s_1399_);
lean_ctor_set(v___x_1402_, 1, v_p_1400_);
lean_ctor_set(v___x_1402_, 2, v___x_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStart(lean_object* v_s_1403_, lean_object* v_p_1404_){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = lean_string_utf8_byte_size(v_s_1403_);
v___x_1406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1406_, 0, v_s_1403_);
lean_ctor_set(v___x_1406_, 1, v_p_1404_);
lean_ctor_set(v___x_1406_, 2, v___x_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_String_slice___redArg(lean_object* v_s_1407_, lean_object* v_startInclusive_1408_, lean_object* v_endExclusive_1409_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1410_, 0, v_s_1407_);
lean_ctor_set(v___x_1410_, 1, v_startInclusive_1408_);
lean_ctor_set(v___x_1410_, 2, v_endExclusive_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_String_slice(lean_object* v_s_1411_, lean_object* v_startInclusive_1412_, lean_object* v_endExclusive_1413_, lean_object* v_h_1414_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1415_, 0, v_s_1411_);
lean_ctor_set(v___x_1415_, 1, v_startInclusive_1412_);
lean_ctor_set(v___x_1415_, 2, v_endExclusive_1413_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x3f(lean_object* v_s_1416_, lean_object* v_startInclusive_1417_, lean_object* v_endExclusive_1418_){
_start:
{
uint8_t v___x_1419_; 
v___x_1419_ = lean_nat_dec_le(v_startInclusive_1417_, v_endExclusive_1418_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; 
lean_dec(v_endExclusive_1418_);
lean_dec(v_startInclusive_1417_);
lean_dec_ref(v_s_1416_);
v___x_1420_ = lean_box(0);
return v___x_1420_;
}
else
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1421_, 0, v_s_1416_);
lean_ctor_set(v___x_1421_, 1, v_startInclusive_1417_);
lean_ctor_set(v___x_1421_, 2, v_endExclusive_1418_);
v___x_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
return v___x_1422_;
}
}
}
LEAN_EXPORT lean_object* l_String_slice_x21(lean_object* v_s_1423_, lean_object* v_p_u2081_1424_, lean_object* v_p_u2082_1425_){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1426_ = lean_unsigned_to_nat(0u);
v___x_1427_ = lean_string_utf8_byte_size(v_s_1423_);
v___x_1428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1428_, 0, v_s_1423_);
lean_ctor_set(v___x_1428_, 1, v___x_1426_);
lean_ctor_set(v___x_1428_, 2, v___x_1427_);
v___x_1429_ = l_String_Slice_slice_x21(v___x_1428_, v_p_u2081_1424_, v_p_u2082_1425_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x21___boxed(lean_object* v_s_1430_, lean_object* v_p_u2081_1431_, lean_object* v_p_u2082_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_String_slice_x21(v_s_1430_, v_p_u2081_1431_, v_p_u2082_1432_);
lean_dec(v_p_u2082_1432_);
lean_dec(v_p_u2081_1431_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21(lean_object* v_s_1434_, lean_object* v_p_u2081_1435_, lean_object* v_p_u2082_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_String_slice_x21(v_s_1434_, v_p_u2081_1435_, v_p_u2082_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21___boxed(lean_object* v_s_1438_, lean_object* v_p_u2081_1439_, lean_object* v_p_u2082_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_String_replaceStartEnd_x21(v_s_1438_, v_p_u2081_1439_, v_p_u2082_1440_);
lean_dec(v_p_u2082_1440_);
lean_dec(v_p_u2081_1439_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg(lean_object* v_p_u2080_1442_, lean_object* v_pos_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_nat_add(v_p_u2080_1442_, v_pos_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg___boxed(lean_object* v_p_u2080_1445_, lean_object* v_pos_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_String_Pos_ofSliceFrom___redArg(v_p_u2080_1445_, v_pos_1446_);
lean_dec(v_pos_1446_);
lean_dec(v_p_u2080_1445_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom(lean_object* v_s_1448_, lean_object* v_p_u2080_1449_, lean_object* v_pos_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = lean_nat_add(v_p_u2080_1449_, v_pos_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___boxed(lean_object* v_s_1452_, lean_object* v_p_u2080_1453_, lean_object* v_pos_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_String_Pos_ofSliceFrom(v_s_1452_, v_p_u2080_1453_, v_pos_1454_);
lean_dec(v_pos_1454_);
lean_dec(v_p_u2080_1453_);
lean_dec_ref(v_s_1452_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg(lean_object* v_p_u2080_1456_, lean_object* v_pos_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = lean_nat_add(v_p_u2080_1456_, v_pos_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg___boxed(lean_object* v_p_u2080_1459_, lean_object* v_pos_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_String_Pos_ofReplaceStart___redArg(v_p_u2080_1459_, v_pos_1460_);
lean_dec(v_pos_1460_);
lean_dec(v_p_u2080_1459_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart(lean_object* v_s_1462_, lean_object* v_p_u2080_1463_, lean_object* v_pos_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = lean_nat_add(v_p_u2080_1463_, v_pos_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___boxed(lean_object* v_s_1466_, lean_object* v_p_u2080_1467_, lean_object* v_pos_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_String_Pos_ofReplaceStart(v_s_1466_, v_p_u2080_1467_, v_pos_1468_);
lean_dec(v_pos_1468_);
lean_dec(v_p_u2080_1467_);
lean_dec_ref(v_s_1466_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg(lean_object* v_p_u2080_1470_, lean_object* v_pos_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = lean_nat_sub(v_pos_1471_, v_p_u2080_1470_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg___boxed(lean_object* v_p_u2080_1473_, lean_object* v_pos_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_String_Pos_sliceFrom___redArg(v_p_u2080_1473_, v_pos_1474_);
lean_dec(v_pos_1474_);
lean_dec(v_p_u2080_1473_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom(lean_object* v_s_1476_, lean_object* v_p_u2080_1477_, lean_object* v_pos_1478_, lean_object* v_h_1479_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_nat_sub(v_pos_1478_, v_p_u2080_1477_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___boxed(lean_object* v_s_1481_, lean_object* v_p_u2080_1482_, lean_object* v_pos_1483_, lean_object* v_h_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_String_Pos_sliceFrom(v_s_1481_, v_p_u2080_1482_, v_pos_1483_, v_h_1484_);
lean_dec(v_pos_1483_);
lean_dec(v_p_u2080_1482_);
lean_dec_ref(v_s_1481_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg(lean_object* v_p_u2080_1486_, lean_object* v_pos_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_nat_sub(v_pos_1487_, v_p_u2080_1486_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg___boxed(lean_object* v_p_u2080_1489_, lean_object* v_pos_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_String_Pos_toReplaceStart___redArg(v_p_u2080_1489_, v_pos_1490_);
lean_dec(v_pos_1490_);
lean_dec(v_p_u2080_1489_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart(lean_object* v_s_1492_, lean_object* v_p_u2080_1493_, lean_object* v_pos_1494_, lean_object* v_h_1495_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_nat_sub(v_pos_1494_, v_p_u2080_1493_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___boxed(lean_object* v_s_1497_, lean_object* v_p_u2080_1498_, lean_object* v_pos_1499_, lean_object* v_h_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_String_Pos_toReplaceStart(v_s_1497_, v_p_u2080_1498_, v_pos_1499_, v_h_1500_);
lean_dec(v_pos_1499_);
lean_dec(v_p_u2080_1498_);
lean_dec_ref(v_s_1497_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg(lean_object* v_pos_1502_){
_start:
{
lean_inc(v_pos_1502_);
return v_pos_1502_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg___boxed(lean_object* v_pos_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_String_Pos_ofSliceTo___redArg(v_pos_1503_);
lean_dec(v_pos_1503_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo(lean_object* v_s_1505_, lean_object* v_p_u2080_1506_, lean_object* v_pos_1507_){
_start:
{
lean_inc(v_pos_1507_);
return v_pos_1507_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___boxed(lean_object* v_s_1508_, lean_object* v_p_u2080_1509_, lean_object* v_pos_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_String_Pos_ofSliceTo(v_s_1508_, v_p_u2080_1509_, v_pos_1510_);
lean_dec(v_pos_1510_);
lean_dec(v_p_u2080_1509_);
lean_dec_ref(v_s_1508_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg(lean_object* v_pos_1512_){
_start:
{
lean_inc(v_pos_1512_);
return v_pos_1512_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg___boxed(lean_object* v_pos_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_String_Pos_ofReplaceEnd___redArg(v_pos_1513_);
lean_dec(v_pos_1513_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd(lean_object* v_s_1515_, lean_object* v_p_u2080_1516_, lean_object* v_pos_1517_){
_start:
{
lean_inc(v_pos_1517_);
return v_pos_1517_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___boxed(lean_object* v_s_1518_, lean_object* v_p_u2080_1519_, lean_object* v_pos_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_String_Pos_ofReplaceEnd(v_s_1518_, v_p_u2080_1519_, v_pos_1520_);
lean_dec(v_pos_1520_);
lean_dec(v_p_u2080_1519_);
lean_dec_ref(v_s_1518_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg(lean_object* v_pos_1522_){
_start:
{
lean_inc(v_pos_1522_);
return v_pos_1522_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg___boxed(lean_object* v_pos_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_String_Pos_sliceTo___redArg(v_pos_1523_);
lean_dec(v_pos_1523_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo(lean_object* v_s_1525_, lean_object* v_p_u2080_1526_, lean_object* v_pos_1527_, lean_object* v_h_1528_){
_start:
{
lean_inc(v_pos_1527_);
return v_pos_1527_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___boxed(lean_object* v_s_1529_, lean_object* v_p_u2080_1530_, lean_object* v_pos_1531_, lean_object* v_h_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_String_Pos_sliceTo(v_s_1529_, v_p_u2080_1530_, v_pos_1531_, v_h_1532_);
lean_dec(v_pos_1531_);
lean_dec(v_p_u2080_1530_);
lean_dec_ref(v_s_1529_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg(lean_object* v_pos_1534_){
_start:
{
lean_inc(v_pos_1534_);
return v_pos_1534_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg___boxed(lean_object* v_pos_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_String_Pos_toReplaceEnd___redArg(v_pos_1535_);
lean_dec(v_pos_1535_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd(lean_object* v_s_1537_, lean_object* v_p_u2080_1538_, lean_object* v_pos_1539_, lean_object* v_h_1540_){
_start:
{
lean_inc(v_pos_1539_);
return v_pos_1539_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___boxed(lean_object* v_s_1541_, lean_object* v_p_u2080_1542_, lean_object* v_pos_1543_, lean_object* v_h_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_String_Pos_toReplaceEnd(v_s_1541_, v_p_u2080_1542_, v_pos_1543_, v_h_1544_);
lean_dec(v_pos_1543_);
lean_dec(v_p_u2080_1542_);
lean_dec_ref(v_s_1541_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg(lean_object* v_p_u2080_1546_, lean_object* v_pos_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = lean_nat_add(v_p_u2080_1546_, v_pos_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1549_, lean_object* v_pos_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_String_Slice_Pos_ofSlice___redArg(v_p_u2080_1549_, v_pos_1550_);
lean_dec(v_pos_1550_);
lean_dec(v_p_u2080_1549_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice(lean_object* v_s_1552_, lean_object* v_p_u2080_1553_, lean_object* v_p_u2081_1554_, lean_object* v_h_1555_, lean_object* v_pos_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = lean_nat_add(v_p_u2080_1553_, v_pos_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___boxed(lean_object* v_s_1558_, lean_object* v_p_u2080_1559_, lean_object* v_p_u2081_1560_, lean_object* v_h_1561_, lean_object* v_pos_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_String_Slice_Pos_ofSlice(v_s_1558_, v_p_u2080_1559_, v_p_u2081_1560_, v_h_1561_, v_pos_1562_);
lean_dec(v_pos_1562_);
lean_dec(v_p_u2081_1560_);
lean_dec(v_p_u2080_1559_);
lean_dec_ref(v_s_1558_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg(lean_object* v_p_u2080_1564_, lean_object* v_pos_1565_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_nat_add(v_p_u2080_1564_, v_pos_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1567_, lean_object* v_pos_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_String_Pos_ofSlice___redArg(v_p_u2080_1567_, v_pos_1568_);
lean_dec(v_pos_1568_);
lean_dec(v_p_u2080_1567_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice(lean_object* v_s_1570_, lean_object* v_p_u2080_1571_, lean_object* v_p_u2081_1572_, lean_object* v_h_1573_, lean_object* v_pos_1574_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_nat_add(v_p_u2080_1571_, v_pos_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___boxed(lean_object* v_s_1576_, lean_object* v_p_u2080_1577_, lean_object* v_p_u2081_1578_, lean_object* v_h_1579_, lean_object* v_pos_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_String_Pos_ofSlice(v_s_1576_, v_p_u2080_1577_, v_p_u2081_1578_, v_h_1579_, v_pos_1580_);
lean_dec(v_pos_1580_);
lean_dec(v_p_u2081_1578_);
lean_dec(v_p_u2080_1577_);
lean_dec_ref(v_s_1576_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg(lean_object* v_pos_1582_, lean_object* v_p_u2080_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = lean_nat_sub(v_pos_1582_, v_p_u2080_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg___boxed(lean_object* v_pos_1585_, lean_object* v_p_u2080_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_String_Slice_Pos_slice___redArg(v_pos_1585_, v_p_u2080_1586_);
lean_dec(v_p_u2080_1586_);
lean_dec(v_pos_1585_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice(lean_object* v_s_1588_, lean_object* v_pos_1589_, lean_object* v_p_u2080_1590_, lean_object* v_p_u2081_1591_, lean_object* v_h_u2081_1592_, lean_object* v_h_u2082_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_nat_sub(v_pos_1589_, v_p_u2080_1590_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___boxed(lean_object* v_s_1595_, lean_object* v_pos_1596_, lean_object* v_p_u2080_1597_, lean_object* v_p_u2081_1598_, lean_object* v_h_u2081_1599_, lean_object* v_h_u2082_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_String_Slice_Pos_slice(v_s_1595_, v_pos_1596_, v_p_u2080_1597_, v_p_u2081_1598_, v_h_u2081_1599_, v_h_u2082_1600_);
lean_dec(v_p_u2081_1598_);
lean_dec(v_p_u2080_1597_);
lean_dec(v_pos_1596_);
lean_dec_ref(v_s_1595_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg(lean_object* v_pos_1602_, lean_object* v_p_u2080_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = lean_nat_sub(v_pos_1602_, v_p_u2080_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg___boxed(lean_object* v_pos_1605_, lean_object* v_p_u2080_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_String_Pos_slice___redArg(v_pos_1605_, v_p_u2080_1606_);
lean_dec(v_p_u2080_1606_);
lean_dec(v_pos_1605_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice(lean_object* v_s_1608_, lean_object* v_pos_1609_, lean_object* v_p_u2080_1610_, lean_object* v_p_u2081_1611_, lean_object* v_h_u2081_1612_, lean_object* v_h_u2082_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_nat_sub(v_pos_1609_, v_p_u2080_1610_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___boxed(lean_object* v_s_1615_, lean_object* v_pos_1616_, lean_object* v_p_u2080_1617_, lean_object* v_p_u2081_1618_, lean_object* v_h_u2081_1619_, lean_object* v_h_u2082_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_String_Pos_slice(v_s_1615_, v_pos_1616_, v_p_u2080_1617_, v_p_u2081_1618_, v_h_u2081_1619_, v_h_u2082_1620_);
lean_dec(v_p_u2081_1618_);
lean_dec(v_p_u2080_1617_);
lean_dec(v_pos_1616_);
lean_dec_ref(v_s_1615_);
return v_res_1621_;
}
}
static lean_object* _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2(void){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1624_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__1));
v___x_1625_ = lean_unsigned_to_nat(4u);
v___x_1626_ = lean_unsigned_to_nat(2621u);
v___x_1627_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__0));
v___x_1628_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1629_ = l_mkPanicMessageWithDecl(v___x_1628_, v___x_1627_, v___x_1626_, v___x_1625_, v___x_1624_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg(lean_object* v_pos_1630_, lean_object* v_p_u2080_1631_, lean_object* v_p_u2081_1632_){
_start:
{
uint8_t v___y_1634_; uint8_t v___x_1639_; 
v___x_1639_ = lean_nat_dec_le(v_p_u2080_1631_, v_pos_1630_);
if (v___x_1639_ == 0)
{
v___y_1634_ = v___x_1639_;
goto v___jp_1633_;
}
else
{
uint8_t v___x_1640_; 
v___x_1640_ = lean_nat_dec_le(v_pos_1630_, v_p_u2081_1632_);
v___y_1634_ = v___x_1640_;
goto v___jp_1633_;
}
v___jp_1633_:
{
if (v___y_1634_ == 0)
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1635_ = lean_unsigned_to_nat(0u);
v___x_1636_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1637_ = l_panic___redArg(v___x_1635_, v___x_1636_);
return v___x_1637_;
}
else
{
lean_object* v___x_1638_; 
v___x_1638_ = lean_nat_sub(v_pos_1630_, v_p_u2080_1631_);
return v___x_1638_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1641_, lean_object* v_p_u2080_1642_, lean_object* v_p_u2081_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_String_Slice_Pos_sliceOrPanic___redArg(v_pos_1641_, v_p_u2080_1642_, v_p_u2081_1643_);
lean_dec(v_p_u2081_1643_);
lean_dec(v_p_u2080_1642_);
lean_dec(v_pos_1641_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic(lean_object* v_s_1645_, lean_object* v_pos_1646_, lean_object* v_p_u2080_1647_, lean_object* v_p_u2081_1648_, lean_object* v_h_1649_){
_start:
{
uint8_t v___y_1651_; uint8_t v___x_1656_; 
v___x_1656_ = lean_nat_dec_le(v_p_u2080_1647_, v_pos_1646_);
if (v___x_1656_ == 0)
{
v___y_1651_ = v___x_1656_;
goto v___jp_1650_;
}
else
{
uint8_t v___x_1657_; 
v___x_1657_ = lean_nat_dec_le(v_pos_1646_, v_p_u2081_1648_);
v___y_1651_ = v___x_1657_;
goto v___jp_1650_;
}
v___jp_1650_:
{
if (v___y_1651_ == 0)
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1652_ = lean_unsigned_to_nat(0u);
v___x_1653_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1654_ = l_panic___redArg(v___x_1652_, v___x_1653_);
return v___x_1654_;
}
else
{
lean_object* v___x_1655_; 
v___x_1655_ = lean_nat_sub(v_pos_1646_, v_p_u2080_1647_);
return v___x_1655_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___boxed(lean_object* v_s_1658_, lean_object* v_pos_1659_, lean_object* v_p_u2080_1660_, lean_object* v_p_u2081_1661_, lean_object* v_h_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_String_Slice_Pos_sliceOrPanic(v_s_1658_, v_pos_1659_, v_p_u2080_1660_, v_p_u2081_1661_, v_h_1662_);
lean_dec(v_p_u2081_1661_);
lean_dec(v_p_u2080_1660_);
lean_dec(v_pos_1659_);
lean_dec_ref(v_s_1658_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg(lean_object* v_pos_1664_, lean_object* v_p_u2080_1665_, lean_object* v_p_u2081_1666_){
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
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1675_, lean_object* v_p_u2080_1676_, lean_object* v_p_u2081_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_String_Pos_sliceOrPanic___redArg(v_pos_1675_, v_p_u2080_1676_, v_p_u2081_1677_);
lean_dec(v_p_u2081_1677_);
lean_dec(v_p_u2080_1676_);
lean_dec(v_pos_1675_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic(lean_object* v_s_1679_, lean_object* v_pos_1680_, lean_object* v_p_u2080_1681_, lean_object* v_p_u2081_1682_, lean_object* v_h_1683_){
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
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___boxed(lean_object* v_s_1692_, lean_object* v_pos_1693_, lean_object* v_p_u2080_1694_, lean_object* v_p_u2081_1695_, lean_object* v_h_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_String_Pos_sliceOrPanic(v_s_1692_, v_pos_1693_, v_p_u2080_1694_, v_p_u2081_1695_, v_h_1696_);
lean_dec(v_p_u2081_1695_);
lean_dec(v_p_u2080_1694_);
lean_dec(v_pos_1693_);
lean_dec_ref(v_s_1692_);
return v_res_1697_;
}
}
static lean_object* _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1699_ = ((lean_object*)(l_String_Slice_slice_x21___closed__1));
v___x_1700_ = lean_unsigned_to_nat(4u);
v___x_1701_ = lean_unsigned_to_nat(2645u);
v___x_1702_ = ((lean_object*)(l_String_Slice_Pos_ofSlice_x21___redArg___closed__0));
v___x_1703_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1704_ = l_mkPanicMessageWithDecl(v___x_1703_, v___x_1702_, v___x_1701_, v___x_1700_, v___x_1699_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1705_, lean_object* v_p_u2081_1706_, lean_object* v_pos_1707_){
_start:
{
uint8_t v___x_1708_; 
v___x_1708_ = lean_nat_dec_le(v_p_u2080_1705_, v_p_u2081_1706_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1709_ = lean_unsigned_to_nat(0u);
v___x_1710_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1711_ = l_panic___redArg(v___x_1709_, v___x_1710_);
return v___x_1711_;
}
else
{
lean_object* v___x_1712_; 
v___x_1712_ = lean_nat_add(v_p_u2080_1705_, v_pos_1707_);
return v___x_1712_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1713_, lean_object* v_p_u2081_1714_, lean_object* v_pos_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_String_Slice_Pos_ofSlice_x21___redArg(v_p_u2080_1713_, v_p_u2081_1714_, v_pos_1715_);
lean_dec(v_pos_1715_);
lean_dec(v_p_u2081_1714_);
lean_dec(v_p_u2080_1713_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21(lean_object* v_s_1717_, lean_object* v_p_u2080_1718_, lean_object* v_p_u2081_1719_, lean_object* v_pos_1720_){
_start:
{
uint8_t v___x_1721_; 
v___x_1721_ = lean_nat_dec_le(v_p_u2080_1718_, v_p_u2081_1719_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1722_ = lean_unsigned_to_nat(0u);
v___x_1723_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1724_ = l_panic___redArg(v___x_1722_, v___x_1723_);
return v___x_1724_;
}
else
{
lean_object* v___x_1725_; 
v___x_1725_ = lean_nat_add(v_p_u2080_1718_, v_pos_1720_);
return v___x_1725_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___boxed(lean_object* v_s_1726_, lean_object* v_p_u2080_1727_, lean_object* v_p_u2081_1728_, lean_object* v_pos_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_String_Slice_Pos_ofSlice_x21(v_s_1726_, v_p_u2080_1727_, v_p_u2081_1728_, v_pos_1729_);
lean_dec(v_pos_1729_);
lean_dec(v_p_u2081_1728_);
lean_dec(v_p_u2080_1727_);
lean_dec_ref(v_s_1726_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1731_, lean_object* v_p_u2081_1732_, lean_object* v_pos_1733_){
_start:
{
uint8_t v___x_1734_; 
v___x_1734_ = lean_nat_dec_le(v_p_u2080_1731_, v_p_u2081_1732_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1735_ = lean_unsigned_to_nat(0u);
v___x_1736_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1737_ = l_panic___redArg(v___x_1735_, v___x_1736_);
return v___x_1737_;
}
else
{
lean_object* v___x_1738_; 
v___x_1738_ = lean_nat_add(v_p_u2080_1731_, v_pos_1733_);
return v___x_1738_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1739_, lean_object* v_p_u2081_1740_, lean_object* v_pos_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_String_Pos_ofSlice_x21___redArg(v_p_u2080_1739_, v_p_u2081_1740_, v_pos_1741_);
lean_dec(v_pos_1741_);
lean_dec(v_p_u2081_1740_);
lean_dec(v_p_u2080_1739_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21(lean_object* v_s_1743_, lean_object* v_p_u2080_1744_, lean_object* v_p_u2081_1745_, lean_object* v_pos_1746_){
_start:
{
uint8_t v___x_1747_; 
v___x_1747_ = lean_nat_dec_le(v_p_u2080_1744_, v_p_u2081_1745_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1748_ = lean_unsigned_to_nat(0u);
v___x_1749_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1750_ = l_panic___redArg(v___x_1748_, v___x_1749_);
return v___x_1750_;
}
else
{
lean_object* v___x_1751_; 
v___x_1751_ = lean_nat_add(v_p_u2080_1744_, v_pos_1746_);
return v___x_1751_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___boxed(lean_object* v_s_1752_, lean_object* v_p_u2080_1753_, lean_object* v_p_u2081_1754_, lean_object* v_pos_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_String_Pos_ofSlice_x21(v_s_1752_, v_p_u2080_1753_, v_p_u2081_1754_, v_pos_1755_);
lean_dec(v_pos_1755_);
lean_dec(v_p_u2081_1754_);
lean_dec(v_p_u2080_1753_);
lean_dec_ref(v_s_1752_);
return v_res_1756_;
}
}
static lean_object* _init_l_String_Slice_Pos_slice_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1759_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__1));
v___x_1760_ = lean_unsigned_to_nat(4u);
v___x_1761_ = lean_unsigned_to_nat(2663u);
v___x_1762_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__0));
v___x_1763_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1764_ = l_mkPanicMessageWithDecl(v___x_1763_, v___x_1762_, v___x_1761_, v___x_1760_, v___x_1759_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg(lean_object* v_pos_1765_, lean_object* v_p_u2080_1766_, lean_object* v_p_u2081_1767_){
_start:
{
uint8_t v___y_1769_; uint8_t v___x_1774_; 
v___x_1774_ = lean_nat_dec_le(v_p_u2080_1766_, v_pos_1765_);
if (v___x_1774_ == 0)
{
v___y_1769_ = v___x_1774_;
goto v___jp_1768_;
}
else
{
uint8_t v___x_1775_; 
v___x_1775_ = lean_nat_dec_le(v_pos_1765_, v_p_u2081_1767_);
v___y_1769_ = v___x_1775_;
goto v___jp_1768_;
}
v___jp_1768_:
{
if (v___y_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1770_ = lean_unsigned_to_nat(0u);
v___x_1771_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1772_ = l_panic___redArg(v___x_1770_, v___x_1771_);
return v___x_1772_;
}
else
{
lean_object* v___x_1773_; 
v___x_1773_ = lean_nat_sub(v_pos_1765_, v_p_u2080_1766_);
return v___x_1773_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1776_, lean_object* v_p_u2080_1777_, lean_object* v_p_u2081_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_String_Slice_Pos_slice_x21___redArg(v_pos_1776_, v_p_u2080_1777_, v_p_u2081_1778_);
lean_dec(v_p_u2081_1778_);
lean_dec(v_p_u2080_1777_);
lean_dec(v_pos_1776_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21(lean_object* v_s_1780_, lean_object* v_pos_1781_, lean_object* v_p_u2080_1782_, lean_object* v_p_u2081_1783_){
_start:
{
uint8_t v___y_1785_; uint8_t v___x_1790_; 
v___x_1790_ = lean_nat_dec_le(v_p_u2080_1782_, v_pos_1781_);
if (v___x_1790_ == 0)
{
v___y_1785_ = v___x_1790_;
goto v___jp_1784_;
}
else
{
uint8_t v___x_1791_; 
v___x_1791_ = lean_nat_dec_le(v_pos_1781_, v_p_u2081_1783_);
v___y_1785_ = v___x_1791_;
goto v___jp_1784_;
}
v___jp_1784_:
{
if (v___y_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1786_ = lean_unsigned_to_nat(0u);
v___x_1787_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1788_ = l_panic___redArg(v___x_1786_, v___x_1787_);
return v___x_1788_;
}
else
{
lean_object* v___x_1789_; 
v___x_1789_ = lean_nat_sub(v_pos_1781_, v_p_u2080_1782_);
return v___x_1789_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___boxed(lean_object* v_s_1792_, lean_object* v_pos_1793_, lean_object* v_p_u2080_1794_, lean_object* v_p_u2081_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_String_Slice_Pos_slice_x21(v_s_1792_, v_pos_1793_, v_p_u2080_1794_, v_p_u2081_1795_);
lean_dec(v_p_u2081_1795_);
lean_dec(v_p_u2080_1794_);
lean_dec(v_pos_1793_);
lean_dec_ref(v_s_1792_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg(lean_object* v_pos_1797_, lean_object* v_p_u2080_1798_, lean_object* v_p_u2081_1799_){
_start:
{
uint8_t v___y_1801_; uint8_t v___x_1806_; 
v___x_1806_ = lean_nat_dec_le(v_p_u2080_1798_, v_pos_1797_);
if (v___x_1806_ == 0)
{
v___y_1801_ = v___x_1806_;
goto v___jp_1800_;
}
else
{
uint8_t v___x_1807_; 
v___x_1807_ = lean_nat_dec_le(v_pos_1797_, v_p_u2081_1799_);
v___y_1801_ = v___x_1807_;
goto v___jp_1800_;
}
v___jp_1800_:
{
if (v___y_1801_ == 0)
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = lean_unsigned_to_nat(0u);
v___x_1803_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1804_ = l_panic___redArg(v___x_1802_, v___x_1803_);
return v___x_1804_;
}
else
{
lean_object* v___x_1805_; 
v___x_1805_ = lean_nat_sub(v_pos_1797_, v_p_u2080_1798_);
return v___x_1805_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1808_, lean_object* v_p_u2080_1809_, lean_object* v_p_u2081_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_String_Pos_slice_x21___redArg(v_pos_1808_, v_p_u2080_1809_, v_p_u2081_1810_);
lean_dec(v_p_u2081_1810_);
lean_dec(v_p_u2080_1809_);
lean_dec(v_pos_1808_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21(lean_object* v_s_1812_, lean_object* v_pos_1813_, lean_object* v_p_u2080_1814_, lean_object* v_p_u2081_1815_){
_start:
{
uint8_t v___y_1817_; uint8_t v___x_1822_; 
v___x_1822_ = lean_nat_dec_le(v_p_u2080_1814_, v_pos_1813_);
if (v___x_1822_ == 0)
{
v___y_1817_ = v___x_1822_;
goto v___jp_1816_;
}
else
{
uint8_t v___x_1823_; 
v___x_1823_ = lean_nat_dec_le(v_pos_1813_, v_p_u2081_1815_);
v___y_1817_ = v___x_1823_;
goto v___jp_1816_;
}
v___jp_1816_:
{
if (v___y_1817_ == 0)
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1818_ = lean_unsigned_to_nat(0u);
v___x_1819_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1820_ = l_panic___redArg(v___x_1818_, v___x_1819_);
return v___x_1820_;
}
else
{
lean_object* v___x_1821_; 
v___x_1821_ = lean_nat_sub(v_pos_1813_, v_p_u2080_1814_);
return v___x_1821_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___boxed(lean_object* v_s_1824_, lean_object* v_pos_1825_, lean_object* v_p_u2080_1826_, lean_object* v_p_u2081_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_String_Pos_slice_x21(v_s_1824_, v_pos_1825_, v_p_u2080_1826_, v_p_u2081_1827_);
lean_dec(v_p_u2081_1827_);
lean_dec(v_p_u2080_1826_);
lean_dec(v_pos_1825_);
lean_dec_ref(v_s_1824_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract(lean_object* v_s_1829_, lean_object* v_p_u2080_1830_, lean_object* v_p_u2081_1831_){
_start:
{
lean_object* v_str_1832_; lean_object* v_startInclusive_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v_str_1832_ = lean_ctor_get(v_s_1829_, 0);
v_startInclusive_1833_ = lean_ctor_get(v_s_1829_, 1);
v___x_1834_ = lean_nat_add(v_startInclusive_1833_, v_p_u2080_1830_);
v___x_1835_ = lean_nat_add(v_startInclusive_1833_, v_p_u2081_1831_);
v___x_1836_ = lean_string_utf8_extract_fast(v_str_1832_, v___x_1834_, v___x_1835_);
lean_dec(v___x_1835_);
lean_dec(v___x_1834_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract___boxed(lean_object* v_s_1837_, lean_object* v_p_u2080_1838_, lean_object* v_p_u2081_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_String_Slice_extract(v_s_1837_, v_p_u2080_1838_, v_p_u2081_1839_);
lean_dec(v_p_u2081_1839_);
lean_dec(v_p_u2080_1838_);
lean_dec_ref(v_s_1837_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn(lean_object* v_s_1841_, lean_object* v_p_1842_, lean_object* v_n_1843_){
_start:
{
lean_object* v_zero_1844_; uint8_t v_isZero_1845_; 
v_zero_1844_ = lean_unsigned_to_nat(0u);
v_isZero_1845_ = lean_nat_dec_eq(v_n_1843_, v_zero_1844_);
if (v_isZero_1845_ == 1)
{
lean_dec(v_n_1843_);
return v_p_1842_;
}
else
{
lean_object* v_str_1846_; lean_object* v_startInclusive_1847_; lean_object* v_endExclusive_1848_; lean_object* v_one_1849_; lean_object* v_n_1850_; lean_object* v___x_1856_; uint8_t v_decide_1857_; 
v_str_1846_ = lean_ctor_get(v_s_1841_, 0);
v_startInclusive_1847_ = lean_ctor_get(v_s_1841_, 1);
v_endExclusive_1848_ = lean_ctor_get(v_s_1841_, 2);
v_one_1849_ = lean_unsigned_to_nat(1u);
v_n_1850_ = lean_nat_sub(v_n_1843_, v_one_1849_);
lean_dec(v_n_1843_);
v___x_1856_ = lean_nat_sub(v_endExclusive_1848_, v_startInclusive_1847_);
v_decide_1857_ = lean_nat_dec_eq(v_p_1842_, v___x_1856_);
lean_dec(v___x_1856_);
if (v_decide_1857_ == 0)
{
goto v___jp_1851_;
}
else
{
if (v_isZero_1845_ == 0)
{
lean_dec(v_n_1850_);
return v_p_1842_;
}
else
{
goto v___jp_1851_;
}
}
v___jp_1851_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = lean_nat_add(v_startInclusive_1847_, v_p_1842_);
lean_dec(v_p_1842_);
v___x_1853_ = lean_string_utf8_next_fast(v_str_1846_, v___x_1852_);
lean_dec(v___x_1852_);
v___x_1854_ = lean_nat_sub(v___x_1853_, v_startInclusive_1847_);
v_p_1842_ = v___x_1854_;
v_n_1843_ = v_n_1850_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn___boxed(lean_object* v_s_1858_, lean_object* v_p_1859_, lean_object* v_n_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_String_Slice_Pos_nextn(v_s_1858_, v_p_1859_, v_n_1860_);
lean_dec_ref(v_s_1858_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_nextn(lean_object* v_s_1862_, lean_object* v_p_1863_, lean_object* v_n_1864_){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1865_ = lean_unsigned_to_nat(0u);
v___x_1866_ = lean_string_utf8_byte_size(v_s_1862_);
v___x_1867_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1867_, 0, v_s_1862_);
lean_ctor_set(v___x_1867_, 1, v___x_1865_);
lean_ctor_set(v___x_1867_, 2, v___x_1866_);
v___x_1868_ = l_String_Slice_Pos_nextn(v___x_1867_, v_p_1863_, v_n_1864_);
lean_dec_ref_known(v___x_1867_, 3);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(lean_object* v_n_1869_, lean_object* v_h__1_1870_, lean_object* v_h__2_1871_){
_start:
{
lean_object* v_zero_1872_; uint8_t v_isZero_1873_; 
v_zero_1872_ = lean_unsigned_to_nat(0u);
v_isZero_1873_ = lean_nat_dec_eq(v_n_1869_, v_zero_1872_);
if (v_isZero_1873_ == 1)
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
lean_dec(v_h__2_1871_);
v___x_1874_ = lean_box(0);
v___x_1875_ = lean_apply_1(v_h__1_1870_, v___x_1874_);
return v___x_1875_;
}
else
{
lean_object* v_one_1876_; lean_object* v_n_1877_; lean_object* v___x_1878_; 
lean_dec(v_h__1_1870_);
v_one_1876_ = lean_unsigned_to_nat(1u);
v_n_1877_ = lean_nat_sub(v_n_1869_, v_one_1876_);
v___x_1878_ = lean_apply_1(v_h__2_1871_, v_n_1877_);
return v___x_1878_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg___boxed(lean_object* v_n_1879_, lean_object* v_h__1_1880_, lean_object* v_h__2_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(v_n_1879_, v_h__1_1880_, v_h__2_1881_);
lean_dec(v_n_1879_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(lean_object* v_motive_1883_, lean_object* v_n_1884_, lean_object* v_h__1_1885_, lean_object* v_h__2_1886_){
_start:
{
lean_object* v_zero_1887_; uint8_t v_isZero_1888_; 
v_zero_1887_ = lean_unsigned_to_nat(0u);
v_isZero_1888_ = lean_nat_dec_eq(v_n_1884_, v_zero_1887_);
if (v_isZero_1888_ == 1)
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
lean_dec(v_h__2_1886_);
v___x_1889_ = lean_box(0);
v___x_1890_ = lean_apply_1(v_h__1_1885_, v___x_1889_);
return v___x_1890_;
}
else
{
lean_object* v_one_1891_; lean_object* v_n_1892_; lean_object* v___x_1893_; 
lean_dec(v_h__1_1885_);
v_one_1891_ = lean_unsigned_to_nat(1u);
v_n_1892_ = lean_nat_sub(v_n_1884_, v_one_1891_);
v___x_1893_ = lean_apply_1(v_h__2_1886_, v_n_1892_);
return v___x_1893_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___boxed(lean_object* v_motive_1894_, lean_object* v_n_1895_, lean_object* v_h__1_1896_, lean_object* v_h__2_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(v_motive_1894_, v_n_1895_, v_h__1_1896_, v_h__2_1897_);
lean_dec(v_n_1895_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next___boxed(lean_object* v_s_1901_, lean_object* v_p_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = lean_string_utf8_next(v_s_1901_, v_p_1902_);
lean_dec(v_p_1902_);
lean_dec_ref(v_s_1901_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_String_next___boxed(lean_object* v_s_1906_, lean_object* v_p_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = lean_string_utf8_next(v_s_1906_, v_p_1907_);
lean_dec(v_p_1907_);
lean_dec_ref(v_s_1906_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux(lean_object* v_x_1909_, lean_object* v_x_1910_, lean_object* v_x_1911_){
_start:
{
if (lean_obj_tag(v_x_1909_) == 0)
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
lean_dec(v_x_1910_);
v___x_1912_ = lean_unsigned_to_nat(1u);
v___x_1913_ = lean_nat_sub(v_x_1911_, v___x_1912_);
return v___x_1913_;
}
else
{
lean_object* v_head_1914_; lean_object* v_tail_1915_; uint32_t v___x_1916_; lean_object* v___x_1917_; lean_object* v_i_x27_1918_; uint8_t v___x_1919_; 
v_head_1914_ = lean_ctor_get(v_x_1909_, 0);
v_tail_1915_ = lean_ctor_get(v_x_1909_, 1);
v___x_1916_ = lean_unbox_uint32(v_head_1914_);
v___x_1917_ = l_Char_utf8Size(v___x_1916_);
v_i_x27_1918_ = lean_nat_add(v_x_1910_, v___x_1917_);
lean_dec(v___x_1917_);
v___x_1919_ = lean_nat_dec_le(v_x_1911_, v_i_x27_1918_);
if (v___x_1919_ == 0)
{
lean_dec(v_x_1910_);
v_x_1909_ = v_tail_1915_;
v_x_1910_ = v_i_x27_1918_;
goto _start;
}
else
{
lean_dec(v_i_x27_1918_);
return v_x_1910_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux___boxed(lean_object* v_x_1921_, lean_object* v_x_1922_, lean_object* v_x_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_String_Pos_Raw_utf8PrevAux(v_x_1921_, v_x_1922_, v_x_1923_);
lean_dec(v_x_1923_);
lean_dec(v_x_1921_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux(lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = l_String_Pos_Raw_utf8PrevAux(v_a_1925_, v_a_1926_, v_a_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux___boxed(lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_String_utf8PrevAux(v_a_1929_, v_a_1930_, v_a_1931_);
lean_dec(v_a_1931_);
lean_dec(v_a_1929_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_prev___boxed(lean_object* v_a_00___x40___internal___hyg_1935_, lean_object* v_a_00___x40___internal___hyg_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_1935_, v_a_00___x40___internal___hyg_1936_);
lean_dec(v_a_00___x40___internal___hyg_1936_);
lean_dec_ref(v_a_00___x40___internal___hyg_1935_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_String_prev___boxed(lean_object* v_a_00___x40___internal___hyg_1940_, lean_object* v_a_00___x40___internal___hyg_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_1940_, v_a_00___x40___internal___hyg_1941_);
lean_dec(v_a_00___x40___internal___hyg_1941_);
lean_dec_ref(v_a_00___x40___internal___hyg_1940_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_1945_, lean_object* v_a_00___x40___internal___hyg_1946_){
_start:
{
uint8_t v_res_1947_; lean_object* v_r_1948_; 
v_res_1947_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_1945_, v_a_00___x40___internal___hyg_1946_);
lean_dec(v_a_00___x40___internal___hyg_1946_);
lean_dec_ref(v_a_00___x40___internal___hyg_1945_);
v_r_1948_ = lean_box(v_res_1947_);
return v_r_1948_;
}
}
LEAN_EXPORT lean_object* l_String_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_1951_, lean_object* v_a_00___x40___internal___hyg_1952_){
_start:
{
uint8_t v_res_1953_; lean_object* v_r_1954_; 
v_res_1953_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_1951_, v_a_00___x40___internal___hyg_1952_);
lean_dec(v_a_00___x40___internal___hyg_1952_);
lean_dec_ref(v_a_00___x40___internal___hyg_1951_);
v_r_1954_ = lean_box(v_res_1953_);
return v_r_1954_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x27___boxed(lean_object* v_s_1958_, lean_object* v_p_1959_, lean_object* v_h_1960_){
_start:
{
uint32_t v_res_1961_; lean_object* v_r_1962_; 
v_res_1961_ = lean_string_utf8_get_fast(v_s_1958_, v_p_1959_);
lean_dec(v_p_1959_);
lean_dec_ref(v_s_1958_);
v_r_1962_ = lean_box_uint32(v_res_1961_);
return v_r_1962_;
}
}
LEAN_EXPORT lean_object* l_String_get_x27___boxed(lean_object* v_s_1966_, lean_object* v_p_1967_, lean_object* v_h_1968_){
_start:
{
uint32_t v_res_1969_; lean_object* v_r_1970_; 
v_res_1969_ = lean_string_utf8_get_fast(v_s_1966_, v_p_1967_);
lean_dec(v_p_1967_);
lean_dec_ref(v_s_1966_);
v_r_1970_ = lean_box_uint32(v_res_1969_);
return v_r_1970_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next_x27___boxed(lean_object* v_s_1974_, lean_object* v_p_1975_, lean_object* v_h_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = lean_string_utf8_next_fast(v_s_1974_, v_p_1975_);
lean_dec(v_p_1975_);
lean_dec_ref(v_s_1974_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_String_next_x27___boxed(lean_object* v_s_1981_, lean_object* v_p_1982_, lean_object* v_h_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = lean_string_utf8_next_fast(v_s_1981_, v_p_1982_);
lean_dec(v_p_1982_);
lean_dec_ref(v_s_1981_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter___redArg(lean_object* v_x_1985_, lean_object* v_x_1986_, lean_object* v_x_1987_, lean_object* v_h__1_1988_, lean_object* v_h__2_1989_){
_start:
{
if (lean_obj_tag(v_x_1985_) == 0)
{
lean_object* v___x_1990_; 
lean_dec(v_h__2_1989_);
v___x_1990_ = lean_apply_2(v_h__1_1988_, v_x_1986_, v_x_1987_);
return v___x_1990_;
}
else
{
lean_object* v_head_1991_; lean_object* v_tail_1992_; lean_object* v___x_1993_; 
lean_dec(v_h__1_1988_);
v_head_1991_ = lean_ctor_get(v_x_1985_, 0);
lean_inc(v_head_1991_);
v_tail_1992_ = lean_ctor_get(v_x_1985_, 1);
lean_inc(v_tail_1992_);
lean_dec_ref_known(v_x_1985_, 2);
v___x_1993_ = lean_apply_4(v_h__2_1989_, v_head_1991_, v_tail_1992_, v_x_1986_, v_x_1987_);
return v___x_1993_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter(lean_object* v_motive_1994_, lean_object* v_x_1995_, lean_object* v_x_1996_, lean_object* v_x_1997_, lean_object* v_h__1_1998_, lean_object* v_h__2_1999_){
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
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop(lean_object* v_a_2004_, lean_object* v_b_2005_, lean_object* v_stopPos_2006_, lean_object* v_i_2007_){
_start:
{
uint8_t v___y_2009_; lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; uint8_t v___y_2016_; 
v___x_2012_ = lean_unsigned_to_nat(1u);
v___x_2013_ = lean_nat_add(v_i_2007_, v___x_2012_);
v___x_2014_ = lean_nat_dec_le(v___x_2013_, v_stopPos_2006_);
lean_dec(v___x_2013_);
if (v___x_2014_ == 0)
{
return v_i_2007_;
}
else
{
uint32_t v___x_2017_; uint32_t v___x_2018_; uint8_t v___x_2019_; 
v___x_2017_ = lean_string_utf8_get(v_a_2004_, v_i_2007_);
v___x_2018_ = lean_string_utf8_get(v_b_2005_, v_i_2007_);
v___x_2019_ = lean_uint32_dec_eq(v___x_2017_, v___x_2018_);
if (v___x_2019_ == 0)
{
v___y_2016_ = v___x_2014_;
goto v___jp_2015_;
}
else
{
uint8_t v___x_2020_; 
v___x_2020_ = 0;
v___y_2016_ = v___x_2020_;
goto v___jp_2015_;
}
}
v___jp_2008_:
{
if (v___y_2009_ == 0)
{
lean_object* v___x_2010_; 
v___x_2010_ = lean_string_utf8_next(v_a_2004_, v_i_2007_);
lean_dec(v_i_2007_);
v_i_2007_ = v___x_2010_;
goto _start;
}
else
{
return v_i_2007_;
}
}
v___jp_2015_:
{
if (v___x_2014_ == 0)
{
v___y_2009_ = v___x_2014_;
goto v___jp_2008_;
}
else
{
v___y_2009_ = v___y_2016_;
goto v___jp_2008_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop___boxed(lean_object* v_a_2021_, lean_object* v_b_2022_, lean_object* v_stopPos_2023_, lean_object* v_i_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_String_firstDiffPos_loop(v_a_2021_, v_b_2022_, v_stopPos_2023_, v_i_2024_);
lean_dec(v_stopPos_2023_);
lean_dec_ref(v_b_2022_);
lean_dec_ref(v_a_2021_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos(lean_object* v_a_2026_, lean_object* v_b_2027_){
_start:
{
lean_object* v___y_2029_; lean_object* v___x_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v___x_2032_ = lean_string_utf8_byte_size(v_a_2026_);
v___x_2033_ = lean_string_utf8_byte_size(v_b_2027_);
v___x_2034_ = lean_nat_dec_le(v___x_2032_, v___x_2033_);
if (v___x_2034_ == 0)
{
v___y_2029_ = v___x_2033_;
goto v___jp_2028_;
}
else
{
v___y_2029_ = v___x_2032_;
goto v___jp_2028_;
}
v___jp_2028_:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = lean_unsigned_to_nat(0u);
v___x_2031_ = l_String_firstDiffPos_loop(v_a_2026_, v_b_2027_, v___y_2029_, v___x_2030_);
lean_dec(v___y_2029_);
return v___x_2031_;
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos___boxed(lean_object* v_a_2035_, lean_object* v_b_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_String_firstDiffPos(v_a_2035_, v_b_2036_);
lean_dec_ref(v_b_2036_);
lean_dec_ref(v_a_2035_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082(lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_){
_start:
{
if (lean_obj_tag(v_a_2038_) == 0)
{
return v_a_2038_;
}
else
{
lean_object* v_head_2041_; lean_object* v_tail_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2055_; 
v_head_2041_ = lean_ctor_get(v_a_2038_, 0);
v_tail_2042_ = lean_ctor_get(v_a_2038_, 1);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_a_2038_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2044_ = v_a_2038_;
v_isShared_2045_ = v_isSharedCheck_2055_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_tail_2042_);
lean_inc(v_head_2041_);
lean_dec(v_a_2038_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2055_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
uint8_t v_decide_2046_; 
v_decide_2046_ = lean_nat_dec_eq(v_a_2039_, v_a_2040_);
if (v_decide_2046_ == 0)
{
uint32_t v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2052_; 
v___x_2047_ = lean_unbox_uint32(v_head_2041_);
v___x_2048_ = l_Char_utf8Size(v___x_2047_);
v___x_2049_ = lean_nat_add(v_a_2039_, v___x_2048_);
lean_dec(v___x_2048_);
v___x_2050_ = l_String_Pos_Raw_extract_go_u2082(v_tail_2042_, v___x_2049_, v_a_2040_);
lean_dec(v___x_2049_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 1, v___x_2050_);
v___x_2052_ = v___x_2044_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_head_2041_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
else
{
lean_object* v___x_2054_; 
lean_del_object(v___x_2044_);
lean_dec(v_tail_2042_);
lean_dec(v_head_2041_);
v___x_2054_ = lean_box(0);
return v___x_2054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082___boxed(lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_String_Pos_Raw_extract_go_u2082(v_a_2056_, v_a_2057_, v_a_2058_);
lean_dec(v_a_2058_);
lean_dec(v_a_2057_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081(lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_){
_start:
{
if (lean_obj_tag(v_a_2060_) == 0)
{
lean_dec(v_a_2061_);
return v_a_2060_;
}
else
{
lean_object* v_head_2064_; lean_object* v_tail_2065_; uint8_t v_decide_2066_; 
v_head_2064_ = lean_ctor_get(v_a_2060_, 0);
v_tail_2065_ = lean_ctor_get(v_a_2060_, 1);
v_decide_2066_ = lean_nat_dec_eq(v_a_2061_, v_a_2062_);
if (v_decide_2066_ == 0)
{
uint32_t v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
lean_inc(v_tail_2065_);
lean_inc(v_head_2064_);
lean_dec_ref_known(v_a_2060_, 2);
v___x_2067_ = lean_unbox_uint32(v_head_2064_);
lean_dec(v_head_2064_);
v___x_2068_ = l_Char_utf8Size(v___x_2067_);
v___x_2069_ = lean_nat_add(v_a_2061_, v___x_2068_);
lean_dec(v___x_2068_);
lean_dec(v_a_2061_);
v_a_2060_ = v_tail_2065_;
v_a_2061_ = v___x_2069_;
goto _start;
}
else
{
lean_object* v___x_2071_; 
v___x_2071_ = l_String_Pos_Raw_extract_go_u2082(v_a_2060_, v_a_2061_, v_a_2063_);
lean_dec(v_a_2061_);
return v___x_2071_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081___boxed(lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_String_Pos_Raw_extract_go_u2081(v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_);
lean_dec(v_a_2075_);
lean_dec(v_a_2074_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract___boxed(lean_object* v_a_00___x40___internal___hyg_2080_, lean_object* v_a_00___x40___internal___hyg_2081_, lean_object* v_a_00___x40___internal___hyg_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = lean_string_utf8_extract(v_a_00___x40___internal___hyg_2080_, v_a_00___x40___internal___hyg_2081_, v_a_00___x40___internal___hyg_2082_);
lean_dec(v_a_00___x40___internal___hyg_2082_);
lean_dec(v_a_00___x40___internal___hyg_2081_);
lean_dec_ref(v_a_00___x40___internal___hyg_2080_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux(lean_object* v_s_2084_, lean_object* v_pos_2085_, lean_object* v_i_2086_, lean_object* v_offset_2087_){
_start:
{
uint8_t v___x_2088_; 
v___x_2088_ = lean_nat_dec_le(v_pos_2085_, v_i_2086_);
if (v___x_2088_ == 0)
{
uint8_t v___x_2089_; 
v___x_2089_ = lean_string_utf8_at_end(v_s_2084_, v_i_2086_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2090_ = lean_string_utf8_next(v_s_2084_, v_i_2086_);
lean_dec(v_i_2086_);
v___x_2091_ = lean_unsigned_to_nat(1u);
v___x_2092_ = lean_nat_add(v_offset_2087_, v___x_2091_);
lean_dec(v_offset_2087_);
v_i_2086_ = v___x_2090_;
v_offset_2087_ = v___x_2092_;
goto _start;
}
else
{
lean_dec(v_i_2086_);
return v_offset_2087_;
}
}
else
{
lean_dec(v_i_2086_);
return v_offset_2087_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux___boxed(lean_object* v_s_2094_, lean_object* v_pos_2095_, lean_object* v_i_2096_, lean_object* v_offset_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2094_, v_pos_2095_, v_i_2096_, v_offset_2097_);
lean_dec(v_pos_2095_);
lean_dec_ref(v_s_2094_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos(lean_object* v_s_2099_, lean_object* v_pos_2100_){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = lean_unsigned_to_nat(0u);
v___x_2102_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2099_, v_pos_2100_, v___x_2101_, v___x_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos___boxed(lean_object* v_s_2103_, lean_object* v_pos_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_String_Pos_Raw_offsetOfPos(v_s_2103_, v_pos_2104_);
lean_dec(v_pos_2104_);
lean_dec_ref(v_s_2103_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos(lean_object* v_s_2106_, lean_object* v_pos_2107_){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2108_ = lean_unsigned_to_nat(0u);
v___x_2109_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2106_, v_pos_2107_, v___x_2108_, v___x_2108_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos___boxed(lean_object* v_s_2110_, lean_object* v_pos_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_String_offsetOfPos(v_s_2110_, v_pos_2111_);
lean_dec(v_pos_2111_);
lean_dec_ref(v_s_2110_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* lean_string_offsetofpos(lean_object* v_s_2113_, lean_object* v_pos_2114_){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = lean_unsigned_to_nat(0u);
v___x_2116_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2113_, v_pos_2114_, v___x_2115_, v___x_2115_);
lean_dec(v_pos_2114_);
lean_dec_ref(v_s_2113_);
return v___x_2116_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(lean_object* v_s1_2117_, lean_object* v_s2_2118_, lean_object* v_off1_2119_, lean_object* v_off2_2120_, lean_object* v_stop1_2121_){
_start:
{
uint8_t v___x_2122_; 
v___x_2122_ = lean_nat_dec_lt(v_off1_2119_, v_stop1_2121_);
if (v___x_2122_ == 0)
{
uint8_t v___x_2123_; 
lean_dec(v_off2_2120_);
lean_dec(v_off1_2119_);
v___x_2123_ = 1;
return v___x_2123_;
}
else
{
uint32_t v_c_u2081_2124_; uint32_t v_c_u2082_2125_; uint8_t v___x_2126_; 
v_c_u2081_2124_ = lean_string_utf8_get(v_s1_2117_, v_off1_2119_);
v_c_u2082_2125_ = lean_string_utf8_get(v_s2_2118_, v_off2_2120_);
v___x_2126_ = lean_uint32_dec_eq(v_c_u2081_2124_, v_c_u2082_2125_);
if (v___x_2126_ == 0)
{
lean_dec(v_off2_2120_);
lean_dec(v_off1_2119_);
return v___x_2126_;
}
else
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2127_ = l_Char_utf8Size(v_c_u2081_2124_);
v___x_2128_ = lean_nat_add(v_off1_2119_, v___x_2127_);
lean_dec(v___x_2127_);
lean_dec(v_off1_2119_);
v___x_2129_ = l_Char_utf8Size(v_c_u2082_2125_);
v___x_2130_ = lean_nat_add(v_off2_2120_, v___x_2129_);
lean_dec(v___x_2129_);
lean_dec(v_off2_2120_);
v_off1_2119_ = v___x_2128_;
v_off2_2120_ = v___x_2130_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop___boxed(lean_object* v_s1_2132_, lean_object* v_s2_2133_, lean_object* v_off1_2134_, lean_object* v_off2_2135_, lean_object* v_stop1_2136_){
_start:
{
uint8_t v_res_2137_; lean_object* v_r_2138_; 
v_res_2137_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2132_, v_s2_2133_, v_off1_2134_, v_off2_2135_, v_stop1_2136_);
lean_dec(v_stop1_2136_);
lean_dec_ref(v_s2_2133_);
lean_dec_ref(v_s1_2132_);
v_r_2138_ = lean_box(v_res_2137_);
return v_r_2138_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_substrEq(lean_object* v_s1_2139_, lean_object* v_pos1_2140_, lean_object* v_s2_2141_, lean_object* v_pos2_2142_, lean_object* v_sz_2143_){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
v___x_2144_ = lean_nat_add(v_pos1_2140_, v_sz_2143_);
v___x_2145_ = lean_string_utf8_byte_size(v_s1_2139_);
v___x_2146_ = lean_nat_dec_le(v___x_2144_, v___x_2145_);
if (v___x_2146_ == 0)
{
lean_dec(v___x_2144_);
lean_dec(v_pos2_2142_);
lean_dec(v_pos1_2140_);
return v___x_2146_;
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2148_; uint8_t v___x_2149_; 
v___x_2147_ = lean_nat_add(v_pos2_2142_, v_sz_2143_);
v___x_2148_ = lean_string_utf8_byte_size(v_s2_2141_);
v___x_2149_ = lean_nat_dec_le(v___x_2147_, v___x_2148_);
lean_dec(v___x_2147_);
if (v___x_2149_ == 0)
{
lean_dec(v___x_2144_);
lean_dec(v_pos2_2142_);
lean_dec(v_pos1_2140_);
return v___x_2149_;
}
else
{
uint8_t v___x_2150_; 
v___x_2150_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2139_, v_s2_2141_, v_pos1_2140_, v_pos2_2142_, v___x_2144_);
lean_dec(v___x_2144_);
return v___x_2150_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_substrEq___boxed(lean_object* v_s1_2151_, lean_object* v_pos1_2152_, lean_object* v_s2_2153_, lean_object* v_pos2_2154_, lean_object* v_sz_2155_){
_start:
{
uint8_t v_res_2156_; lean_object* v_r_2157_; 
v_res_2156_ = l_String_Pos_Raw_substrEq(v_s1_2151_, v_pos1_2152_, v_s2_2153_, v_pos2_2154_, v_sz_2155_);
lean_dec(v_sz_2155_);
lean_dec_ref(v_s2_2153_);
lean_dec_ref(v_s1_2151_);
v_r_2157_ = lean_box(v_res_2156_);
return v_r_2157_;
}
}
LEAN_EXPORT uint8_t l_String_substrEq(lean_object* v_s1_2158_, lean_object* v_pos1_2159_, lean_object* v_s2_2160_, lean_object* v_pos2_2161_, lean_object* v_sz_2162_){
_start:
{
uint8_t v___x_2163_; 
v___x_2163_ = l_String_Pos_Raw_substrEq(v_s1_2158_, v_pos1_2159_, v_s2_2160_, v_pos2_2161_, v_sz_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_String_substrEq___boxed(lean_object* v_s1_2164_, lean_object* v_pos1_2165_, lean_object* v_s2_2166_, lean_object* v_pos2_2167_, lean_object* v_sz_2168_){
_start:
{
uint8_t v_res_2169_; lean_object* v_r_2170_; 
v_res_2169_ = l_String_substrEq(v_s1_2164_, v_pos1_2165_, v_s2_2166_, v_pos2_2167_, v_sz_2168_);
lean_dec(v_sz_2168_);
lean_dec_ref(v_s2_2166_);
lean_dec_ref(v_s1_2164_);
v_r_2170_ = lean_box(v_res_2169_);
return v_r_2170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object* v_x_2171_, lean_object* v_x_2172_, lean_object* v_h__1_2173_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = lean_apply_2(v_h__1_2173_, v_x_2171_, v_x_2172_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object* v_motive_2175_, lean_object* v_x_2176_, lean_object* v_x_2177_, lean_object* v_h__1_2178_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = lean_apply_2(v_h__1_2178_, v_x_2176_, v_x_2177_);
return v___x_2179_;
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
