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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
uint32_t v___y_5_; lean_object* v___y_6_; uint32_t v_val_12_; lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_23_ = lean_byte_array_size(v_b_1_);
v___x_24_ = lean_nat_dec_lt(v_i_2_, v___x_23_);
if (v___x_24_ == 0)
{
lean_object* v___x_25_; 
lean_dec(v_i_2_);
v___x_25_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_25_, 0, v_acc_3_);
return v___x_25_;
}
else
{
uint8_t v___x_26_; uint8_t v___x_27_; uint8_t v___x_28_; uint8_t v___x_29_; uint8_t v___x_30_; 
v___x_26_ = lean_byte_array_fget(v_b_1_, v_i_2_);
v___x_27_ = 128;
v___x_28_ = lean_uint8_land(v___x_26_, v___x_27_);
v___x_29_ = 0;
v___x_30_ = lean_uint8_dec_eq(v___x_28_, v___x_29_);
if (v___x_30_ == 0)
{
uint8_t v___x_31_; uint8_t v___x_32_; uint8_t v___x_33_; uint8_t v___x_34_; 
v___x_31_ = 224;
v___x_32_ = lean_uint8_land(v___x_26_, v___x_31_);
v___x_33_ = 192;
v___x_34_ = lean_uint8_dec_eq(v___x_32_, v___x_33_);
if (v___x_34_ == 0)
{
uint8_t v___x_35_; uint8_t v___x_36_; uint8_t v___x_37_; 
v___x_35_ = 240;
v___x_36_ = lean_uint8_land(v___x_26_, v___x_35_);
v___x_37_ = lean_uint8_dec_eq(v___x_36_, v___x_31_);
if (v___x_37_ == 0)
{
uint8_t v___x_38_; uint8_t v___x_39_; uint8_t v___x_40_; 
v___x_38_ = 248;
v___x_39_ = lean_uint8_land(v___x_26_, v___x_38_);
v___x_40_ = lean_uint8_dec_eq(v___x_39_, v___x_35_);
if (v___x_40_ == 0)
{
lean_object* v___x_41_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_41_ = lean_box(0);
return v___x_41_;
}
else
{
lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_42_ = lean_unsigned_to_nat(3u);
v___x_43_ = lean_nat_add(v_i_2_, v___x_42_);
v___x_44_ = lean_nat_dec_lt(v___x_43_, v___x_23_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; 
lean_dec(v___x_43_);
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_45_ = lean_box(0);
return v___x_45_;
}
else
{
lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; uint8_t v___x_49_; uint8_t v___x_50_; 
v___x_46_ = lean_unsigned_to_nat(1u);
v___x_47_ = lean_nat_add(v_i_2_, v___x_46_);
v___x_48_ = lean_byte_array_fget(v_b_1_, v___x_47_);
lean_dec(v___x_47_);
v___x_49_ = lean_uint8_land(v___x_48_, v___x_33_);
v___x_50_ = lean_uint8_dec_eq(v___x_49_, v___x_27_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; 
lean_dec(v___x_43_);
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_51_ = lean_box(0);
return v___x_51_;
}
else
{
lean_object* v___x_52_; lean_object* v___x_53_; uint8_t v___x_54_; uint8_t v___x_55_; uint8_t v___x_56_; 
v___x_52_ = lean_unsigned_to_nat(2u);
v___x_53_ = lean_nat_add(v_i_2_, v___x_52_);
v___x_54_ = lean_byte_array_fget(v_b_1_, v___x_53_);
lean_dec(v___x_53_);
v___x_55_ = lean_uint8_land(v___x_54_, v___x_33_);
v___x_56_ = lean_uint8_dec_eq(v___x_55_, v___x_27_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; 
lean_dec(v___x_43_);
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_57_ = lean_box(0);
return v___x_57_;
}
else
{
uint8_t v___x_58_; uint8_t v___x_59_; uint8_t v___x_60_; 
v___x_58_ = lean_byte_array_fget(v_b_1_, v___x_43_);
lean_dec(v___x_43_);
v___x_59_ = lean_uint8_land(v___x_58_, v___x_33_);
v___x_60_ = lean_uint8_dec_eq(v___x_59_, v___x_27_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_61_ = lean_box(0);
return v___x_61_;
}
else
{
uint8_t v___x_62_; uint8_t v_b_u2080_63_; uint8_t v___x_64_; uint8_t v_b_u2081_65_; uint8_t v_b_u2082_66_; uint8_t v_b_u2083_67_; uint32_t v___x_68_; uint32_t v___x_69_; uint32_t v___x_70_; uint32_t v___x_71_; uint32_t v___x_72_; uint32_t v___x_73_; uint32_t v___x_74_; uint32_t v___x_75_; uint32_t v___x_76_; uint32_t v___x_77_; uint32_t v___x_78_; uint32_t v___x_79_; uint32_t v_r_80_; uint32_t v___x_81_; uint8_t v___x_82_; 
v___x_62_ = 7;
v_b_u2080_63_ = lean_uint8_land(v___x_26_, v___x_62_);
v___x_64_ = 63;
v_b_u2081_65_ = lean_uint8_land(v___x_48_, v___x_64_);
v_b_u2082_66_ = lean_uint8_land(v___x_54_, v___x_64_);
v_b_u2083_67_ = lean_uint8_land(v___x_58_, v___x_64_);
v___x_68_ = lean_uint8_to_uint32(v_b_u2080_63_);
v___x_69_ = 18;
v___x_70_ = lean_uint32_shift_left(v___x_68_, v___x_69_);
v___x_71_ = lean_uint8_to_uint32(v_b_u2081_65_);
v___x_72_ = 12;
v___x_73_ = lean_uint32_shift_left(v___x_71_, v___x_72_);
v___x_74_ = lean_uint32_lor(v___x_70_, v___x_73_);
v___x_75_ = lean_uint8_to_uint32(v_b_u2082_66_);
v___x_76_ = 6;
v___x_77_ = lean_uint32_shift_left(v___x_75_, v___x_76_);
v___x_78_ = lean_uint32_lor(v___x_74_, v___x_77_);
v___x_79_ = lean_uint8_to_uint32(v_b_u2083_67_);
v_r_80_ = lean_uint32_lor(v___x_78_, v___x_79_);
v___x_81_ = 65536;
v___x_82_ = lean_uint32_dec_lt(v_r_80_, v___x_81_);
if (v___x_82_ == 0)
{
uint32_t v___x_83_; uint8_t v___x_84_; 
v___x_83_ = 1114111;
v___x_84_ = lean_uint32_dec_lt(v___x_83_, v_r_80_);
if (v___x_84_ == 0)
{
v_val_12_ = v_r_80_;
goto v___jp_11_;
}
else
{
lean_object* v___x_85_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_85_ = lean_box(0);
return v___x_85_;
}
}
else
{
lean_object* v___x_86_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_86_ = lean_box(0);
return v___x_86_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_87_ = lean_unsigned_to_nat(2u);
v___x_88_ = lean_nat_add(v_i_2_, v___x_87_);
v___x_89_ = lean_nat_dec_lt(v___x_88_, v___x_23_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; 
lean_dec(v___x_88_);
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_90_ = lean_box(0);
return v___x_90_;
}
else
{
lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; uint8_t v___x_94_; uint8_t v___x_95_; 
v___x_91_ = lean_unsigned_to_nat(1u);
v___x_92_ = lean_nat_add(v_i_2_, v___x_91_);
v___x_93_ = lean_byte_array_fget(v_b_1_, v___x_92_);
lean_dec(v___x_92_);
v___x_94_ = lean_uint8_land(v___x_93_, v___x_33_);
v___x_95_ = lean_uint8_dec_eq(v___x_94_, v___x_27_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; 
lean_dec(v___x_88_);
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_96_ = lean_box(0);
return v___x_96_;
}
else
{
uint8_t v___x_97_; uint8_t v___x_98_; uint8_t v___x_99_; 
v___x_97_ = lean_byte_array_fget(v_b_1_, v___x_88_);
lean_dec(v___x_88_);
v___x_98_ = lean_uint8_land(v___x_97_, v___x_33_);
v___x_99_ = lean_uint8_dec_eq(v___x_98_, v___x_27_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_100_ = lean_box(0);
return v___x_100_;
}
else
{
uint8_t v___x_101_; uint8_t v_b_u2080_102_; uint8_t v___x_103_; uint8_t v_b_u2081_104_; uint8_t v_b_u2082_105_; uint32_t v___x_106_; uint32_t v___x_107_; uint32_t v___x_108_; uint32_t v___x_109_; uint32_t v___x_110_; uint32_t v___x_111_; uint32_t v___x_112_; uint32_t v___x_113_; uint32_t v_r_114_; uint32_t v___x_115_; uint8_t v___x_116_; 
v___x_101_ = 15;
v_b_u2080_102_ = lean_uint8_land(v___x_26_, v___x_101_);
v___x_103_ = 63;
v_b_u2081_104_ = lean_uint8_land(v___x_93_, v___x_103_);
v_b_u2082_105_ = lean_uint8_land(v___x_97_, v___x_103_);
v___x_106_ = lean_uint8_to_uint32(v_b_u2080_102_);
v___x_107_ = 12;
v___x_108_ = lean_uint32_shift_left(v___x_106_, v___x_107_);
v___x_109_ = lean_uint8_to_uint32(v_b_u2081_104_);
v___x_110_ = 6;
v___x_111_ = lean_uint32_shift_left(v___x_109_, v___x_110_);
v___x_112_ = lean_uint32_lor(v___x_108_, v___x_111_);
v___x_113_ = lean_uint8_to_uint32(v_b_u2082_105_);
v_r_114_ = lean_uint32_lor(v___x_112_, v___x_113_);
v___x_115_ = 2048;
v___x_116_ = lean_uint32_dec_lt(v_r_114_, v___x_115_);
if (v___x_116_ == 0)
{
uint32_t v___x_117_; uint8_t v___x_118_; 
v___x_117_ = 55296;
v___x_118_ = lean_uint32_dec_le(v___x_117_, v_r_114_);
if (v___x_118_ == 0)
{
v_val_12_ = v_r_114_;
goto v___jp_11_;
}
else
{
uint32_t v___x_119_; uint8_t v___x_120_; 
v___x_119_ = 57343;
v___x_120_ = lean_uint32_dec_le(v_r_114_, v___x_119_);
if (v___x_120_ == 0)
{
v_val_12_ = v_r_114_;
goto v___jp_11_;
}
else
{
lean_object* v___x_121_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_121_ = lean_box(0);
return v___x_121_;
}
}
}
else
{
lean_object* v___x_122_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_122_ = lean_box(0);
return v___x_122_;
}
}
}
}
}
}
else
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_123_ = lean_unsigned_to_nat(1u);
v___x_124_ = lean_nat_add(v_i_2_, v___x_123_);
v___x_125_ = lean_nat_dec_lt(v___x_124_, v___x_23_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
lean_dec(v___x_124_);
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_126_ = lean_box(0);
return v___x_126_;
}
else
{
uint8_t v___x_127_; uint8_t v___x_128_; uint8_t v___x_129_; 
v___x_127_ = lean_byte_array_fget(v_b_1_, v___x_124_);
lean_dec(v___x_124_);
v___x_128_ = lean_uint8_land(v___x_127_, v___x_33_);
v___x_129_ = lean_uint8_dec_eq(v___x_128_, v___x_27_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_130_ = lean_box(0);
return v___x_130_;
}
else
{
uint8_t v___x_131_; uint8_t v_b_u2080_132_; uint8_t v___x_133_; uint8_t v_b_u2081_134_; uint32_t v___x_135_; uint32_t v___x_136_; uint32_t v___x_137_; uint32_t v___x_138_; uint32_t v_r_139_; uint32_t v___x_140_; uint8_t v___x_141_; 
v___x_131_ = 31;
v_b_u2080_132_ = lean_uint8_land(v___x_26_, v___x_131_);
v___x_133_ = 63;
v_b_u2081_134_ = lean_uint8_land(v___x_127_, v___x_133_);
v___x_135_ = lean_uint8_to_uint32(v_b_u2080_132_);
v___x_136_ = 6;
v___x_137_ = lean_uint32_shift_left(v___x_135_, v___x_136_);
v___x_138_ = lean_uint8_to_uint32(v_b_u2081_134_);
v_r_139_ = lean_uint32_lor(v___x_137_, v___x_138_);
v___x_140_ = 128;
v___x_141_ = lean_uint32_dec_lt(v_r_139_, v___x_140_);
if (v___x_141_ == 0)
{
v_val_12_ = v_r_139_;
goto v___jp_11_;
}
else
{
lean_object* v___x_142_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_142_ = lean_box(0);
return v___x_142_;
}
}
}
}
}
else
{
uint32_t v___x_143_; 
v___x_143_ = lean_uint8_to_uint32(v___x_26_);
v_val_12_ = v___x_143_;
goto v___jp_11_;
}
}
v___jp_4_:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = lean_nat_add(v_i_2_, v___y_6_);
lean_dec(v_i_2_);
v___x_8_ = lean_box_uint32(v___y_5_);
v___x_9_ = lean_array_push(v_acc_3_, v___x_8_);
v_i_2_ = v___x_7_;
v_acc_3_ = v___x_9_;
goto _start;
}
v___jp_11_:
{
uint32_t v___x_13_; uint8_t v___x_14_; 
v___x_13_ = 127;
v___x_14_ = lean_uint32_dec_le(v_val_12_, v___x_13_);
if (v___x_14_ == 0)
{
uint32_t v___x_15_; uint8_t v___x_16_; 
v___x_15_ = 2047;
v___x_16_ = lean_uint32_dec_le(v_val_12_, v___x_15_);
if (v___x_16_ == 0)
{
uint32_t v___x_17_; uint8_t v___x_18_; 
v___x_17_ = 65535;
v___x_18_ = lean_uint32_dec_le(v_val_12_, v___x_17_);
if (v___x_18_ == 0)
{
lean_object* v___x_19_; 
v___x_19_ = lean_unsigned_to_nat(4u);
v___y_5_ = v_val_12_;
v___y_6_ = v___x_19_;
goto v___jp_4_;
}
else
{
lean_object* v___x_20_; 
v___x_20_ = lean_unsigned_to_nat(3u);
v___y_5_ = v_val_12_;
v___y_6_ = v___x_20_;
goto v___jp_4_;
}
}
else
{
lean_object* v___x_21_; 
v___x_21_ = lean_unsigned_to_nat(2u);
v___y_5_ = v_val_12_;
v___y_6_ = v___x_21_;
goto v___jp_4_;
}
}
else
{
lean_object* v___x_22_; 
v___x_22_ = lean_unsigned_to_nat(1u);
v___y_5_ = v_val_12_;
v___y_6_ = v___x_22_;
goto v___jp_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go___redArg___boxed(lean_object* v_b_144_, lean_object* v_i_145_, lean_object* v_acc_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_ByteArray_utf8Decode_x3f_go___redArg(v_b_144_, v_i_145_, v_acc_146_);
lean_dec_ref(v_b_144_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go(lean_object* v_b_148_, lean_object* v_i_149_, lean_object* v_acc_150_, lean_object* v_hi_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_ByteArray_utf8Decode_x3f_go___redArg(v_b_148_, v_i_149_, v_acc_150_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go___boxed(lean_object* v_b_153_, lean_object* v_i_154_, lean_object* v_acc_155_, lean_object* v_hi_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_ByteArray_utf8Decode_x3f_go(v_b_153_, v_i_154_, v_acc_155_, v_hi_156_);
lean_dec_ref(v_b_153_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__1_splitter___redArg(lean_object* v_x_158_, lean_object* v_h__1_159_, lean_object* v_h__2_160_){
_start:
{
if (lean_obj_tag(v_x_158_) == 0)
{
lean_object* v___x_161_; 
lean_dec(v_h__2_160_);
v___x_161_ = lean_apply_1(v_h__1_159_, lean_box(0));
return v___x_161_;
}
else
{
lean_object* v_val_162_; lean_object* v___x_163_; 
lean_dec(v_h__1_159_);
v_val_162_ = lean_ctor_get(v_x_158_, 0);
lean_inc(v_val_162_);
lean_dec_ref_known(v_x_158_, 1);
v___x_163_ = lean_apply_2(v_h__2_160_, v_val_162_, lean_box(0));
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__1_splitter(lean_object* v_motive_164_, lean_object* v_x_165_, lean_object* v_h__1_166_, lean_object* v_h__2_167_){
_start:
{
if (lean_obj_tag(v_x_165_) == 0)
{
lean_object* v___x_168_; 
lean_dec(v_h__2_167_);
v___x_168_ = lean_apply_1(v_h__1_166_, lean_box(0));
return v___x_168_;
}
else
{
lean_object* v_val_169_; lean_object* v___x_170_; 
lean_dec(v_h__1_166_);
v_val_169_ = lean_ctor_get(v_x_165_, 0);
lean_inc(v_val_169_);
lean_dec_ref_known(v_x_165_, 1);
v___x_170_ = lean_apply_2(v_h__2_167_, v_val_169_, lean_box(0));
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f(lean_object* v_b_173_){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = lean_unsigned_to_nat(0u);
v___x_175_ = ((lean_object*)(l_ByteArray_utf8Decode_x3f___closed__0));
v___x_176_ = l_ByteArray_utf8Decode_x3f_go___redArg(v_b_173_, v___x_174_, v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f___boxed(lean_object* v_b_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_ByteArray_utf8Decode_x3f(v_b_177_);
lean_dec_ref(v_b_177_);
return v_res_178_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8_go___redArg(lean_object* v_b_179_, lean_object* v_i_180_){
_start:
{
lean_object* v___y_182_; uint8_t v___y_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_204_ = lean_byte_array_size(v_b_179_);
v___x_205_ = lean_nat_dec_lt(v_i_180_, v___x_204_);
if (v___x_205_ == 0)
{
uint8_t v___x_206_; 
lean_dec(v_i_180_);
v___x_206_ = 1;
return v___x_206_;
}
else
{
uint8_t v___x_207_; uint8_t v___x_208_; uint8_t v___x_209_; uint8_t v___x_210_; uint8_t v___x_211_; 
v___x_207_ = lean_byte_array_fget(v_b_179_, v_i_180_);
v___x_208_ = 128;
v___x_209_ = lean_uint8_land(v___x_207_, v___x_208_);
v___x_210_ = 0;
v___x_211_ = lean_uint8_dec_eq(v___x_209_, v___x_210_);
if (v___x_211_ == 0)
{
uint8_t v___x_212_; uint8_t v___x_213_; uint8_t v___x_214_; uint8_t v___x_215_; 
v___x_212_ = 224;
v___x_213_ = lean_uint8_land(v___x_207_, v___x_212_);
v___x_214_ = 192;
v___x_215_ = lean_uint8_dec_eq(v___x_213_, v___x_214_);
if (v___x_215_ == 0)
{
uint8_t v___x_216_; uint8_t v___x_217_; uint8_t v___x_218_; 
v___x_216_ = 240;
v___x_217_ = lean_uint8_land(v___x_207_, v___x_216_);
v___x_218_ = lean_uint8_dec_eq(v___x_217_, v___x_212_);
if (v___x_218_ == 0)
{
uint8_t v___x_219_; uint8_t v___x_220_; uint8_t v___x_221_; 
v___x_219_ = 248;
v___x_220_ = lean_uint8_land(v___x_207_, v___x_219_);
v___x_221_ = lean_uint8_dec_eq(v___x_220_, v___x_216_);
if (v___x_221_ == 0)
{
lean_dec(v_i_180_);
return v___x_221_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_222_ = lean_unsigned_to_nat(3u);
v___x_223_ = lean_nat_add(v_i_180_, v___x_222_);
v___x_224_ = lean_nat_dec_lt(v___x_223_, v___x_204_);
if (v___x_224_ == 0)
{
lean_dec(v___x_223_);
lean_dec(v_i_180_);
return v___x_224_;
}
else
{
lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; uint8_t v___x_228_; uint8_t v___x_229_; 
v___x_225_ = lean_unsigned_to_nat(1u);
v___x_226_ = lean_nat_add(v_i_180_, v___x_225_);
v___x_227_ = lean_byte_array_fget(v_b_179_, v___x_226_);
lean_dec(v___x_226_);
v___x_228_ = lean_uint8_land(v___x_227_, v___x_214_);
v___x_229_ = lean_uint8_dec_eq(v___x_228_, v___x_208_);
if (v___x_229_ == 0)
{
lean_dec(v___x_223_);
lean_dec(v_i_180_);
return v___x_229_;
}
else
{
lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; uint8_t v___x_233_; uint8_t v___x_234_; 
v___x_230_ = lean_unsigned_to_nat(2u);
v___x_231_ = lean_nat_add(v_i_180_, v___x_230_);
v___x_232_ = lean_byte_array_fget(v_b_179_, v___x_231_);
lean_dec(v___x_231_);
v___x_233_ = lean_uint8_land(v___x_232_, v___x_214_);
v___x_234_ = lean_uint8_dec_eq(v___x_233_, v___x_208_);
if (v___x_234_ == 0)
{
lean_dec(v___x_223_);
lean_dec(v_i_180_);
return v___x_218_;
}
else
{
uint8_t v___x_235_; uint8_t v___x_236_; uint8_t v___x_237_; 
v___x_235_ = lean_byte_array_fget(v_b_179_, v___x_223_);
lean_dec(v___x_223_);
v___x_236_ = lean_uint8_land(v___x_235_, v___x_214_);
v___x_237_ = lean_uint8_dec_eq(v___x_236_, v___x_208_);
if (v___x_237_ == 0)
{
lean_dec(v_i_180_);
return v___x_218_;
}
else
{
uint8_t v___x_238_; uint8_t v_b_u2080_239_; uint8_t v___x_240_; uint8_t v_b_u2081_241_; uint8_t v_b_u2082_242_; uint8_t v_b_u2083_243_; uint32_t v___x_244_; uint32_t v___x_245_; uint32_t v___x_246_; uint32_t v___x_247_; uint32_t v___x_248_; uint32_t v___x_249_; uint32_t v___x_250_; uint32_t v___x_251_; uint32_t v___x_252_; uint32_t v___x_253_; uint32_t v___x_254_; uint32_t v___x_255_; uint32_t v_r_256_; uint32_t v___x_257_; uint8_t v___x_258_; 
v___x_238_ = 7;
v_b_u2080_239_ = lean_uint8_land(v___x_207_, v___x_238_);
v___x_240_ = 63;
v_b_u2081_241_ = lean_uint8_land(v___x_227_, v___x_240_);
v_b_u2082_242_ = lean_uint8_land(v___x_232_, v___x_240_);
v_b_u2083_243_ = lean_uint8_land(v___x_235_, v___x_240_);
v___x_244_ = lean_uint8_to_uint32(v_b_u2080_239_);
v___x_245_ = 18;
v___x_246_ = lean_uint32_shift_left(v___x_244_, v___x_245_);
v___x_247_ = lean_uint8_to_uint32(v_b_u2081_241_);
v___x_248_ = 12;
v___x_249_ = lean_uint32_shift_left(v___x_247_, v___x_248_);
v___x_250_ = lean_uint32_lor(v___x_246_, v___x_249_);
v___x_251_ = lean_uint8_to_uint32(v_b_u2082_242_);
v___x_252_ = 6;
v___x_253_ = lean_uint32_shift_left(v___x_251_, v___x_252_);
v___x_254_ = lean_uint32_lor(v___x_250_, v___x_253_);
v___x_255_ = lean_uint8_to_uint32(v_b_u2083_243_);
v_r_256_ = lean_uint32_lor(v___x_254_, v___x_255_);
v___x_257_ = 65536;
v___x_258_ = lean_uint32_dec_le(v___x_257_, v_r_256_);
if (v___x_258_ == 0)
{
lean_dec(v_i_180_);
return v___x_218_;
}
else
{
uint32_t v___x_259_; uint8_t v___x_260_; 
v___x_259_ = 1114111;
v___x_260_ = lean_uint32_dec_le(v_r_256_, v___x_259_);
v___y_203_ = v___x_260_;
goto v___jp_202_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_261_ = lean_unsigned_to_nat(2u);
v___x_262_ = lean_nat_add(v_i_180_, v___x_261_);
v___x_263_ = lean_nat_dec_lt(v___x_262_, v___x_204_);
if (v___x_263_ == 0)
{
lean_dec(v___x_262_);
lean_dec(v_i_180_);
return v___x_263_;
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; uint8_t v___x_267_; uint8_t v___x_268_; 
v___x_264_ = lean_unsigned_to_nat(1u);
v___x_265_ = lean_nat_add(v_i_180_, v___x_264_);
v___x_266_ = lean_byte_array_fget(v_b_179_, v___x_265_);
lean_dec(v___x_265_);
v___x_267_ = lean_uint8_land(v___x_266_, v___x_214_);
v___x_268_ = lean_uint8_dec_eq(v___x_267_, v___x_208_);
if (v___x_268_ == 0)
{
lean_dec(v___x_262_);
lean_dec(v_i_180_);
return v___x_268_;
}
else
{
uint8_t v___x_269_; uint8_t v___x_270_; uint8_t v___x_271_; 
v___x_269_ = lean_byte_array_fget(v_b_179_, v___x_262_);
lean_dec(v___x_262_);
v___x_270_ = lean_uint8_land(v___x_269_, v___x_214_);
v___x_271_ = lean_uint8_dec_eq(v___x_270_, v___x_208_);
if (v___x_271_ == 0)
{
lean_dec(v_i_180_);
return v___x_215_;
}
else
{
uint8_t v___x_272_; uint8_t v_b_u2080_273_; uint8_t v___x_274_; uint8_t v_b_u2081_275_; uint8_t v_b_u2082_276_; uint32_t v___x_277_; uint32_t v___x_278_; uint32_t v___x_279_; uint32_t v___x_280_; uint32_t v___x_281_; uint32_t v___x_282_; uint32_t v___x_283_; uint32_t v___x_284_; uint32_t v_r_285_; uint32_t v___x_286_; uint8_t v___x_287_; 
v___x_272_ = 15;
v_b_u2080_273_ = lean_uint8_land(v___x_207_, v___x_272_);
v___x_274_ = 63;
v_b_u2081_275_ = lean_uint8_land(v___x_266_, v___x_274_);
v_b_u2082_276_ = lean_uint8_land(v___x_269_, v___x_274_);
v___x_277_ = lean_uint8_to_uint32(v_b_u2080_273_);
v___x_278_ = 12;
v___x_279_ = lean_uint32_shift_left(v___x_277_, v___x_278_);
v___x_280_ = lean_uint8_to_uint32(v_b_u2081_275_);
v___x_281_ = 6;
v___x_282_ = lean_uint32_shift_left(v___x_280_, v___x_281_);
v___x_283_ = lean_uint32_lor(v___x_279_, v___x_282_);
v___x_284_ = lean_uint8_to_uint32(v_b_u2082_276_);
v_r_285_ = lean_uint32_lor(v___x_283_, v___x_284_);
v___x_286_ = 2048;
v___x_287_ = lean_uint32_dec_le(v___x_286_, v_r_285_);
if (v___x_287_ == 0)
{
lean_dec(v_i_180_);
return v___x_215_;
}
else
{
uint32_t v___x_288_; uint8_t v___x_289_; 
v___x_288_ = 55296;
v___x_289_ = lean_uint32_dec_lt(v_r_285_, v___x_288_);
if (v___x_289_ == 0)
{
uint32_t v___x_290_; uint8_t v___x_291_; 
v___x_290_ = 57343;
v___x_291_ = lean_uint32_dec_lt(v___x_290_, v_r_285_);
v___y_203_ = v___x_291_;
goto v___jp_202_;
}
else
{
goto v___jp_185_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_292_ = lean_unsigned_to_nat(1u);
v___x_293_ = lean_nat_add(v_i_180_, v___x_292_);
v___x_294_ = lean_nat_dec_lt(v___x_293_, v___x_204_);
if (v___x_294_ == 0)
{
lean_dec(v___x_293_);
lean_dec(v_i_180_);
return v___x_294_;
}
else
{
uint8_t v___x_295_; uint8_t v___x_296_; uint8_t v___x_297_; 
v___x_295_ = lean_byte_array_fget(v_b_179_, v___x_293_);
lean_dec(v___x_293_);
v___x_296_ = lean_uint8_land(v___x_295_, v___x_214_);
v___x_297_ = lean_uint8_dec_eq(v___x_296_, v___x_208_);
if (v___x_297_ == 0)
{
lean_dec(v_i_180_);
return v___x_297_;
}
else
{
uint8_t v___x_298_; uint8_t v_b_u2080_299_; uint8_t v___x_300_; uint8_t v_b_u2081_301_; uint32_t v___x_302_; uint32_t v___x_303_; uint32_t v___x_304_; uint32_t v___x_305_; uint32_t v_r_306_; uint32_t v___x_307_; uint8_t v___x_308_; 
v___x_298_ = 31;
v_b_u2080_299_ = lean_uint8_land(v___x_207_, v___x_298_);
v___x_300_ = 63;
v_b_u2081_301_ = lean_uint8_land(v___x_295_, v___x_300_);
v___x_302_ = lean_uint8_to_uint32(v_b_u2080_299_);
v___x_303_ = 6;
v___x_304_ = lean_uint32_shift_left(v___x_302_, v___x_303_);
v___x_305_ = lean_uint8_to_uint32(v_b_u2081_301_);
v_r_306_ = lean_uint32_lor(v___x_304_, v___x_305_);
v___x_307_ = 128;
v___x_308_ = lean_uint32_dec_le(v___x_307_, v_r_306_);
v___y_203_ = v___x_308_;
goto v___jp_202_;
}
}
}
}
else
{
goto v___jp_185_;
}
}
v___jp_181_:
{
lean_object* v___x_183_; 
v___x_183_ = lean_nat_add(v_i_180_, v___y_182_);
lean_dec(v_i_180_);
v_i_180_ = v___x_183_;
goto _start;
}
v___jp_185_:
{
uint8_t v___x_186_; uint8_t v___x_187_; uint8_t v___x_188_; uint8_t v___x_189_; uint8_t v___x_190_; 
v___x_186_ = lean_byte_array_fget(v_b_179_, v_i_180_);
v___x_187_ = 128;
v___x_188_ = lean_uint8_land(v___x_186_, v___x_187_);
v___x_189_ = 0;
v___x_190_ = lean_uint8_dec_eq(v___x_188_, v___x_189_);
if (v___x_190_ == 0)
{
uint8_t v___x_191_; uint8_t v___x_192_; uint8_t v___x_193_; uint8_t v___x_194_; 
v___x_191_ = 224;
v___x_192_ = lean_uint8_land(v___x_186_, v___x_191_);
v___x_193_ = 192;
v___x_194_ = lean_uint8_dec_eq(v___x_192_, v___x_193_);
if (v___x_194_ == 0)
{
uint8_t v___x_195_; uint8_t v___x_196_; uint8_t v___x_197_; 
v___x_195_ = 240;
v___x_196_ = lean_uint8_land(v___x_186_, v___x_195_);
v___x_197_ = lean_uint8_dec_eq(v___x_196_, v___x_191_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; 
v___x_198_ = lean_unsigned_to_nat(4u);
v___y_182_ = v___x_198_;
goto v___jp_181_;
}
else
{
lean_object* v___x_199_; 
v___x_199_ = lean_unsigned_to_nat(3u);
v___y_182_ = v___x_199_;
goto v___jp_181_;
}
}
else
{
lean_object* v___x_200_; 
v___x_200_ = lean_unsigned_to_nat(2u);
v___y_182_ = v___x_200_;
goto v___jp_181_;
}
}
else
{
lean_object* v___x_201_; 
v___x_201_ = lean_unsigned_to_nat(1u);
v___y_182_ = v___x_201_;
goto v___jp_181_;
}
}
v___jp_202_:
{
if (v___y_203_ == 0)
{
lean_dec(v_i_180_);
return v___y_203_;
}
else
{
goto v___jp_185_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___redArg___boxed(lean_object* v_b_309_, lean_object* v_i_310_){
_start:
{
uint8_t v_res_311_; lean_object* v_r_312_; 
v_res_311_ = l_ByteArray_validateUTF8_go___redArg(v_b_309_, v_i_310_);
lean_dec_ref(v_b_309_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8_go(lean_object* v_b_313_, lean_object* v_i_314_, lean_object* v_hi_315_){
_start:
{
uint8_t v___x_316_; 
v___x_316_ = l_ByteArray_validateUTF8_go___redArg(v_b_313_, v_i_314_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___boxed(lean_object* v_b_317_, lean_object* v_i_318_, lean_object* v_hi_319_){
_start:
{
uint8_t v_res_320_; lean_object* v_r_321_; 
v_res_320_ = l_ByteArray_validateUTF8_go(v_b_317_, v_i_318_, v_hi_319_);
lean_dec_ref(v_b_317_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(uint8_t v_x_322_, lean_object* v_h__1_323_, lean_object* v_h__2_324_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg___boxed(lean_object* v_x_327_, lean_object* v_h__1_328_, lean_object* v_h__2_329_){
_start:
{
uint8_t v_x_26__boxed_330_; lean_object* v_res_331_; 
v_x_26__boxed_330_ = lean_unbox(v_x_327_);
v_res_331_ = l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(v_x_26__boxed_330_, v_h__1_328_, v_h__2_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(lean_object* v_motive_332_, uint8_t v_x_333_, lean_object* v_h__1_334_, lean_object* v_h__2_335_){
_start:
{
if (v_x_333_ == 0)
{
lean_object* v___x_336_; 
lean_dec(v_h__2_335_);
v___x_336_ = lean_apply_1(v_h__1_334_, lean_box(0));
return v___x_336_;
}
else
{
lean_object* v___x_337_; 
lean_dec(v_h__1_334_);
v___x_337_ = lean_apply_1(v_h__2_335_, lean_box(0));
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___boxed(lean_object* v_motive_338_, lean_object* v_x_339_, lean_object* v_h__1_340_, lean_object* v_h__2_341_){
_start:
{
uint8_t v_x_33__boxed_342_; lean_object* v_res_343_; 
v_x_33__boxed_342_ = lean_unbox(v_x_339_);
v_res_343_ = l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(v_motive_338_, v_x_33__boxed_342_, v_h__1_340_, v_h__2_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8___boxed(lean_object* v_b_345_){
_start:
{
uint8_t v_res_346_; lean_object* v_r_347_; 
v_res_346_ = lean_string_validate_utf8(v_b_345_);
lean_dec_ref(v_b_345_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT uint8_t l_instDecidableIsValidUTF8(lean_object* v_b_348_){
_start:
{
uint8_t v___x_349_; 
v___x_349_ = lean_string_validate_utf8(v_b_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_instDecidableIsValidUTF8___boxed(lean_object* v_b_350_){
_start:
{
uint8_t v_res_351_; lean_object* v_r_352_; 
v_res_351_ = l_instDecidableIsValidUTF8(v_b_350_);
lean_dec_ref(v_b_350_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_x3f(lean_object* v_a_353_){
_start:
{
uint8_t v___x_354_; 
v___x_354_ = lean_string_validate_utf8(v_a_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; 
lean_dec_ref(v_a_353_);
v___x_355_ = lean_box(0);
return v___x_355_;
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_string_from_utf8_unchecked(v_a_353_);
v___x_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
}
static lean_object* _init_l_String_fromUTF8_x21___closed__4(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_362_ = ((lean_object*)(l_String_fromUTF8_x21___closed__3));
v___x_363_ = lean_unsigned_to_nat(46u);
v___x_364_ = lean_unsigned_to_nat(193u);
v___x_365_ = ((lean_object*)(l_String_fromUTF8_x21___closed__2));
v___x_366_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_367_ = l_mkPanicMessageWithDecl(v___x_366_, v___x_365_, v___x_364_, v___x_363_, v___x_362_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_x21(lean_object* v_a_368_){
_start:
{
uint8_t v___x_369_; 
v___x_369_ = lean_string_validate_utf8(v_a_368_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
lean_dec_ref(v_a_368_);
v___x_370_ = ((lean_object*)(l_String_fromUTF8_x21___closed__0));
v___x_371_ = lean_obj_once(&l_String_fromUTF8_x21___closed__4, &l_String_fromUTF8_x21___closed__4_once, _init_l_String_fromUTF8_x21___closed__4);
v___x_372_ = l_panic___redArg(v___x_370_, v___x_371_);
return v___x_372_;
}
else
{
lean_object* v___x_373_; 
v___x_373_ = lean_string_from_utf8_unchecked(v_a_368_);
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* l_String_Internal_toArray(lean_object* v_b_374_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v_val_379_; 
v___x_375_ = lean_string_to_utf8(v_b_374_);
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = ((lean_object*)(l_ByteArray_utf8Decode_x3f___closed__0));
v___x_378_ = l_ByteArray_utf8Decode_x3f_go___redArg(v___x_375_, v___x_376_, v___x_377_);
lean_dec_ref(v___x_375_);
v_val_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_val_379_);
lean_dec(v___x_378_);
return v_val_379_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValid___boxed(lean_object* v_s_382_, lean_object* v_p_383_){
_start:
{
uint8_t v_res_384_; lean_object* v_r_385_; 
v_res_384_ = lean_string_is_valid_pos(v_s_382_, v_p_383_);
lean_dec(v_p_383_);
lean_dec_ref(v_s_382_);
v_r_385_ = lean_box(v_res_384_);
return v_r_385_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsValid(lean_object* v_s_386_, lean_object* v_p_387_){
_start:
{
uint8_t v___x_388_; 
v___x_388_ = lean_string_is_valid_pos(v_s_386_, v_p_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsValid___boxed(lean_object* v_s_389_, lean_object* v_p_390_){
_start:
{
uint8_t v_res_391_; lean_object* v_r_392_; 
v_res_391_ = l_String_instDecidableIsValid(v_s_389_, v_p_390_);
lean_dec(v_p_390_);
lean_dec_ref(v_s_389_);
v_r_392_ = lean_box(v_res_391_);
return v_r_392_;
}
}
LEAN_EXPORT lean_object* l_String_extract___boxed(lean_object* v_s_396_, lean_object* v_b_397_, lean_object* v_e_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = lean_string_utf8_extract_fast(v_s_396_, v_b_397_, v_e_398_);
lean_dec(v_e_398_);
lean_dec(v_b_397_);
lean_dec_ref(v_s_396_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_extract(lean_object* v_s_400_, lean_object* v_b_401_, lean_object* v_e_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = lean_string_utf8_extract_fast(v_s_400_, v_b_401_, v_e_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_extract___boxed(lean_object* v_s_404_, lean_object* v_b_405_, lean_object* v_e_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_String_Pos_extract(v_s_404_, v_b_405_, v_e_406_);
lean_dec(v_e_406_);
lean_dec(v_b_405_);
lean_dec_ref(v_s_404_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_copy(lean_object* v_s_408_){
_start:
{
lean_object* v_str_409_; lean_object* v_startInclusive_410_; lean_object* v_endExclusive_411_; lean_object* v___x_412_; 
v_str_409_ = lean_ctor_get(v_s_408_, 0);
v_startInclusive_410_ = lean_ctor_get(v_s_408_, 1);
v_endExclusive_411_ = lean_ctor_get(v_s_408_, 2);
v___x_412_ = lean_string_utf8_extract_fast(v_str_409_, v_startInclusive_410_, v_endExclusive_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_copy___boxed(lean_object* v_s_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_String_Slice_copy(v_s_413_);
lean_dec_ref(v_s_413_);
return v_res_414_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_isValidForSlice(lean_object* v_s_415_, lean_object* v_p_416_){
_start:
{
lean_object* v_str_417_; lean_object* v_startInclusive_418_; lean_object* v_endExclusive_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v_str_417_ = lean_ctor_get(v_s_415_, 0);
v_startInclusive_418_ = lean_ctor_get(v_s_415_, 1);
v_endExclusive_419_ = lean_ctor_get(v_s_415_, 2);
v___x_420_ = lean_nat_sub(v_endExclusive_419_, v_startInclusive_418_);
v___x_421_ = lean_unsigned_to_nat(1u);
v___x_422_ = lean_nat_add(v_p_416_, v___x_421_);
v___x_423_ = lean_nat_dec_le(v___x_422_, v___x_420_);
lean_dec(v___x_422_);
if (v___x_423_ == 0)
{
uint8_t v_decide_424_; 
v_decide_424_ = lean_nat_dec_eq(v_p_416_, v___x_420_);
lean_dec(v___x_420_);
return v_decide_424_;
}
else
{
lean_object* v___x_425_; uint8_t v___x_426_; uint8_t v___x_427_; uint8_t v___x_428_; uint8_t v___x_429_; uint8_t v___x_430_; 
lean_dec(v___x_420_);
v___x_425_ = lean_nat_add(v_startInclusive_418_, v_p_416_);
v___x_426_ = lean_string_get_byte_fast(v_str_417_, v___x_425_);
v___x_427_ = 128;
v___x_428_ = lean_uint8_land(v___x_426_, v___x_427_);
v___x_429_ = 0;
v___x_430_ = lean_uint8_dec_eq(v___x_428_, v___x_429_);
if (v___x_430_ == 0)
{
uint8_t v___x_431_; uint8_t v___x_432_; uint8_t v___x_433_; uint8_t v___x_434_; 
v___x_431_ = 224;
v___x_432_ = lean_uint8_land(v___x_426_, v___x_431_);
v___x_433_ = 192;
v___x_434_ = lean_uint8_dec_eq(v___x_432_, v___x_433_);
if (v___x_434_ == 0)
{
uint8_t v___x_435_; uint8_t v___x_436_; uint8_t v___x_437_; 
v___x_435_ = 240;
v___x_436_ = lean_uint8_land(v___x_426_, v___x_435_);
v___x_437_ = lean_uint8_dec_eq(v___x_436_, v___x_431_);
if (v___x_437_ == 0)
{
uint8_t v___x_438_; uint8_t v___x_439_; uint8_t v___x_440_; 
v___x_438_ = 248;
v___x_439_ = lean_uint8_land(v___x_426_, v___x_438_);
v___x_440_ = lean_uint8_dec_eq(v___x_439_, v___x_435_);
return v___x_440_;
}
else
{
return v___x_437_;
}
}
else
{
return v___x_434_;
}
}
else
{
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValidForSlice___boxed(lean_object* v_s_441_, lean_object* v_p_442_){
_start:
{
uint8_t v_res_443_; lean_object* v_r_444_; 
v_res_443_ = l_String_Pos_Raw_isValidForSlice(v_s_441_, v_p_442_);
lean_dec(v_p_442_);
lean_dec_ref(v_s_441_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsValidForSlice(lean_object* v_s_445_, lean_object* v_p_446_){
_start:
{
uint8_t v___x_447_; 
v___x_447_ = l_String_Pos_Raw_isValidForSlice(v_s_445_, v_p_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsValidForSlice___boxed(lean_object* v_s_448_, lean_object* v_p_449_){
_start:
{
uint8_t v_res_450_; lean_object* v_r_451_; 
v_res_450_ = l_String_instDecidableIsValidForSlice(v_s_448_, v_p_449_);
lean_dec(v_p_449_);
lean_dec_ref(v_s_448_);
v_r_451_ = lean_box(v_res_450_);
return v_r_451_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str(lean_object* v_s_452_, lean_object* v_pos_453_){
_start:
{
lean_object* v_startInclusive_454_; lean_object* v___x_455_; 
v_startInclusive_454_ = lean_ctor_get(v_s_452_, 1);
v___x_455_ = lean_nat_add(v_startInclusive_454_, v_pos_453_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str___boxed(lean_object* v_s_456_, lean_object* v_pos_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_String_Slice_Pos_str(v_s_456_, v_pos_457_);
lean_dec(v_pos_457_);
lean_dec_ref(v_s_456_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg(lean_object* v_s_459_, lean_object* v_pos_460_){
_start:
{
lean_object* v_startInclusive_461_; lean_object* v___x_462_; 
v_startInclusive_461_ = lean_ctor_get(v_s_459_, 1);
v___x_462_ = lean_nat_sub(v_pos_460_, v_startInclusive_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg___boxed(lean_object* v_s_463_, lean_object* v_pos_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_String_Slice_Pos_ofStr___redArg(v_s_463_, v_pos_464_);
lean_dec(v_pos_464_);
lean_dec_ref(v_s_463_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr(lean_object* v_s_466_, lean_object* v_pos_467_, lean_object* v_h_u2081_468_, lean_object* v_h_u2082_469_){
_start:
{
lean_object* v_startInclusive_470_; lean_object* v___x_471_; 
v_startInclusive_470_ = lean_ctor_get(v_s_466_, 1);
v___x_471_ = lean_nat_sub(v_pos_467_, v_startInclusive_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___boxed(lean_object* v_s_472_, lean_object* v_pos_473_, lean_object* v_h_u2081_474_, lean_object* v_h_u2082_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_String_Slice_Pos_ofStr(v_s_472_, v_pos_473_, v_h_u2081_474_, v_h_u2082_475_);
lean_dec(v_pos_473_);
lean_dec_ref(v_s_472_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom(lean_object* v_s_477_, lean_object* v_pos_478_){
_start:
{
lean_object* v_str_479_; lean_object* v_startInclusive_480_; lean_object* v_endExclusive_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_489_; 
v_str_479_ = lean_ctor_get(v_s_477_, 0);
v_startInclusive_480_ = lean_ctor_get(v_s_477_, 1);
v_endExclusive_481_ = lean_ctor_get(v_s_477_, 2);
v_isSharedCheck_489_ = !lean_is_exclusive(v_s_477_);
if (v_isSharedCheck_489_ == 0)
{
v___x_483_ = v_s_477_;
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_endExclusive_481_);
lean_inc(v_startInclusive_480_);
lean_inc(v_str_479_);
lean_dec(v_s_477_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_485_ = lean_nat_add(v_startInclusive_480_, v_pos_478_);
lean_dec(v_startInclusive_480_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 1, v___x_485_);
v___x_487_ = v___x_483_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_str_479_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_488_, 2, v_endExclusive_481_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom___boxed(lean_object* v_s_490_, lean_object* v_pos_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_String_Slice_sliceFrom(v_s_490_, v_pos_491_);
lean_dec(v_pos_491_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStart(lean_object* v_s_493_, lean_object* v_pos_494_){
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
LEAN_EXPORT lean_object* l_String_Slice_replaceStart___boxed(lean_object* v_s_506_, lean_object* v_pos_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_String_Slice_replaceStart(v_s_506_, v_pos_507_);
lean_dec(v_pos_507_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceTo(lean_object* v_s_509_, lean_object* v_pos_510_){
_start:
{
lean_object* v_str_511_; lean_object* v_startInclusive_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_520_; 
v_str_511_ = lean_ctor_get(v_s_509_, 0);
v_startInclusive_512_ = lean_ctor_get(v_s_509_, 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v_s_509_);
if (v_isSharedCheck_520_ == 0)
{
lean_object* v_unused_521_; 
v_unused_521_ = lean_ctor_get(v_s_509_, 2);
lean_dec(v_unused_521_);
v___x_514_ = v_s_509_;
v_isShared_515_ = v_isSharedCheck_520_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_startInclusive_512_);
lean_inc(v_str_511_);
lean_dec(v_s_509_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_520_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_516_ = lean_nat_add(v_startInclusive_512_, v_pos_510_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 2, v___x_516_);
v___x_518_ = v___x_514_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_str_511_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_startInclusive_512_);
lean_ctor_set(v_reuseFailAlloc_519_, 2, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceTo___boxed(lean_object* v_s_522_, lean_object* v_pos_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_String_Slice_sliceTo(v_s_522_, v_pos_523_);
lean_dec(v_pos_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd(lean_object* v_s_525_, lean_object* v_pos_526_){
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
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd___boxed(lean_object* v_s_538_, lean_object* v_pos_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_String_Slice_replaceEnd(v_s_538_, v_pos_539_);
lean_dec(v_pos_539_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg(lean_object* v_s_541_, lean_object* v_newStart_542_, lean_object* v_newEnd_543_){
_start:
{
lean_object* v_str_544_; lean_object* v_startInclusive_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_554_; 
v_str_544_ = lean_ctor_get(v_s_541_, 0);
v_startInclusive_545_ = lean_ctor_get(v_s_541_, 1);
v_isSharedCheck_554_ = !lean_is_exclusive(v_s_541_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; 
v_unused_555_ = lean_ctor_get(v_s_541_, 2);
lean_dec(v_unused_555_);
v___x_547_ = v_s_541_;
v_isShared_548_ = v_isSharedCheck_554_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_startInclusive_545_);
lean_inc(v_str_544_);
lean_dec(v_s_541_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_554_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_549_ = lean_nat_add(v_startInclusive_545_, v_newStart_542_);
v___x_550_ = lean_nat_add(v_startInclusive_545_, v_newEnd_543_);
lean_dec(v_startInclusive_545_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 2, v___x_550_);
lean_ctor_set(v___x_547_, 1, v___x_549_);
v___x_552_ = v___x_547_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_str_544_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg___boxed(lean_object* v_s_556_, lean_object* v_newStart_557_, lean_object* v_newEnd_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_String_Slice_slice___redArg(v_s_556_, v_newStart_557_, v_newEnd_558_);
lean_dec(v_newEnd_558_);
lean_dec(v_newStart_557_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice(lean_object* v_s_560_, lean_object* v_newStart_561_, lean_object* v_newEnd_562_, lean_object* v_h_563_){
_start:
{
lean_object* v_str_564_; lean_object* v_startInclusive_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_574_; 
v_str_564_ = lean_ctor_get(v_s_560_, 0);
v_startInclusive_565_ = lean_ctor_get(v_s_560_, 1);
v_isSharedCheck_574_ = !lean_is_exclusive(v_s_560_);
if (v_isSharedCheck_574_ == 0)
{
lean_object* v_unused_575_; 
v_unused_575_ = lean_ctor_get(v_s_560_, 2);
lean_dec(v_unused_575_);
v___x_567_ = v_s_560_;
v_isShared_568_ = v_isSharedCheck_574_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_startInclusive_565_);
lean_inc(v_str_564_);
lean_dec(v_s_560_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_574_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_569_ = lean_nat_add(v_startInclusive_565_, v_newStart_561_);
v___x_570_ = lean_nat_add(v_startInclusive_565_, v_newEnd_562_);
lean_dec(v_startInclusive_565_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 2, v___x_570_);
lean_ctor_set(v___x_567_, 1, v___x_569_);
v___x_572_ = v___x_567_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_str_564_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_573_, 2, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___boxed(lean_object* v_s_576_, lean_object* v_newStart_577_, lean_object* v_newEnd_578_, lean_object* v_h_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_String_Slice_slice(v_s_576_, v_newStart_577_, v_newEnd_578_, v_h_579_);
lean_dec(v_newEnd_578_);
lean_dec(v_newStart_577_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg(lean_object* v_s_581_, lean_object* v_newStart_582_, lean_object* v_newEnd_583_){
_start:
{
lean_object* v_str_584_; lean_object* v_startInclusive_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_594_; 
v_str_584_ = lean_ctor_get(v_s_581_, 0);
v_startInclusive_585_ = lean_ctor_get(v_s_581_, 1);
v_isSharedCheck_594_ = !lean_is_exclusive(v_s_581_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; 
v_unused_595_ = lean_ctor_get(v_s_581_, 2);
lean_dec(v_unused_595_);
v___x_587_ = v_s_581_;
v_isShared_588_ = v_isSharedCheck_594_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_startInclusive_585_);
lean_inc(v_str_584_);
lean_dec(v_s_581_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_594_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_589_ = lean_nat_add(v_startInclusive_585_, v_newStart_582_);
v___x_590_ = lean_nat_add(v_startInclusive_585_, v_newEnd_583_);
lean_dec(v_startInclusive_585_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 2, v___x_590_);
lean_ctor_set(v___x_587_, 1, v___x_589_);
v___x_592_ = v___x_587_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_str_584_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v___x_589_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg___boxed(lean_object* v_s_596_, lean_object* v_newStart_597_, lean_object* v_newEnd_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_String_Slice_replaceStartEnd___redArg(v_s_596_, v_newStart_597_, v_newEnd_598_);
lean_dec(v_newEnd_598_);
lean_dec(v_newStart_597_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd(lean_object* v_s_600_, lean_object* v_newStart_601_, lean_object* v_newEnd_602_, lean_object* v_h_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_String_Slice_replaceStartEnd___redArg(v_s_600_, v_newStart_601_, v_newEnd_602_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___boxed(lean_object* v_s_605_, lean_object* v_newStart_606_, lean_object* v_newEnd_607_, lean_object* v_h_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_String_Slice_replaceStartEnd(v_s_605_, v_newStart_606_, v_newEnd_607_, v_h_608_);
lean_dec(v_newEnd_607_);
lean_dec(v_newStart_606_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f(lean_object* v_s_610_, lean_object* v_newStart_611_, lean_object* v_newEnd_612_){
_start:
{
uint8_t v___x_613_; 
v___x_613_ = lean_nat_dec_le(v_newStart_611_, v_newEnd_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; 
lean_dec_ref(v_s_610_);
v___x_614_ = lean_box(0);
return v___x_614_;
}
else
{
lean_object* v_str_615_; lean_object* v_startInclusive_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_626_; 
v_str_615_ = lean_ctor_get(v_s_610_, 0);
v_startInclusive_616_ = lean_ctor_get(v_s_610_, 1);
v_isSharedCheck_626_ = !lean_is_exclusive(v_s_610_);
if (v_isSharedCheck_626_ == 0)
{
lean_object* v_unused_627_; 
v_unused_627_ = lean_ctor_get(v_s_610_, 2);
lean_dec(v_unused_627_);
v___x_618_ = v_s_610_;
v_isShared_619_ = v_isSharedCheck_626_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_startInclusive_616_);
lean_inc(v_str_615_);
lean_dec(v_s_610_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_626_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
v___x_620_ = lean_nat_add(v_startInclusive_616_, v_newStart_611_);
v___x_621_ = lean_nat_add(v_startInclusive_616_, v_newEnd_612_);
lean_dec(v_startInclusive_616_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 2, v___x_621_);
lean_ctor_set(v___x_618_, 1, v___x_620_);
v___x_623_ = v___x_618_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_str_615_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_625_, 2, v___x_621_);
v___x_623_ = v_reuseFailAlloc_625_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_624_; 
v___x_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
return v___x_624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f___boxed(lean_object* v_s_628_, lean_object* v_newStart_629_, lean_object* v_newEnd_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_String_Slice_slice_x3f(v_s_628_, v_newStart_629_, v_newEnd_630_);
lean_dec(v_newEnd_630_);
lean_dec(v_newStart_629_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_slice_x21_spec__0(lean_object* v_msg_632_){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = l_String_instInhabitedSlice;
v___x_634_ = lean_panic_fn_borrowed(v___x_633_, v_msg_632_);
return v___x_634_;
}
}
static lean_object* _init_l_String_Slice_slice_x21___closed__2(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_637_ = ((lean_object*)(l_String_Slice_slice_x21___closed__1));
v___x_638_ = lean_unsigned_to_nat(4u);
v___x_639_ = lean_unsigned_to_nat(1026u);
v___x_640_ = ((lean_object*)(l_String_Slice_slice_x21___closed__0));
v___x_641_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_642_ = l_mkPanicMessageWithDecl(v___x_641_, v___x_640_, v___x_639_, v___x_638_, v___x_637_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x21(lean_object* v_s_643_, lean_object* v_newStart_644_, lean_object* v_newEnd_645_){
_start:
{
uint8_t v___x_646_; 
v___x_646_ = lean_nat_dec_le(v_newStart_644_, v_newEnd_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; 
lean_dec_ref(v_s_643_);
v___x_647_ = lean_obj_once(&l_String_Slice_slice_x21___closed__2, &l_String_Slice_slice_x21___closed__2_once, _init_l_String_Slice_slice_x21___closed__2);
v___x_648_ = l_panic___at___00String_Slice_slice_x21_spec__0(v___x_647_);
return v___x_648_;
}
else
{
lean_object* v_str_649_; lean_object* v_startInclusive_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_659_; 
v_str_649_ = lean_ctor_get(v_s_643_, 0);
v_startInclusive_650_ = lean_ctor_get(v_s_643_, 1);
v_isSharedCheck_659_ = !lean_is_exclusive(v_s_643_);
if (v_isSharedCheck_659_ == 0)
{
lean_object* v_unused_660_; 
v_unused_660_ = lean_ctor_get(v_s_643_, 2);
lean_dec(v_unused_660_);
v___x_652_ = v_s_643_;
v_isShared_653_ = v_isSharedCheck_659_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_startInclusive_650_);
lean_inc(v_str_649_);
lean_dec(v_s_643_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_659_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
v___x_654_ = lean_nat_add(v_startInclusive_650_, v_newStart_644_);
v___x_655_ = lean_nat_add(v_startInclusive_650_, v_newEnd_645_);
lean_dec(v_startInclusive_650_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 2, v___x_655_);
lean_ctor_set(v___x_652_, 1, v___x_654_);
v___x_657_ = v___x_652_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_str_649_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_658_, 2, v___x_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x21___boxed(lean_object* v_s_661_, lean_object* v_newStart_662_, lean_object* v_newEnd_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_String_Slice_slice_x21(v_s_661_, v_newStart_662_, v_newEnd_663_);
lean_dec(v_newEnd_663_);
lean_dec(v_newStart_662_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21(lean_object* v_s_665_, lean_object* v_newStart_666_, lean_object* v_newEnd_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_String_Slice_slice_x21(v_s_665_, v_newStart_666_, v_newEnd_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21___boxed(lean_object* v_s_669_, lean_object* v_newStart_670_, lean_object* v_newEnd_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_String_Slice_replaceStartEnd_x21(v_s_669_, v_newStart_670_, v_newEnd_671_);
lean_dec(v_newEnd_671_);
lean_dec(v_newStart_670_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_String_decodeChar___boxed(lean_object* v_s_676_, lean_object* v_byteIdx_677_, lean_object* v_h_678_){
_start:
{
uint32_t v_res_679_; lean_object* v_r_680_; 
v_res_679_ = lean_string_utf8_get_fast(v_s_676_, v_byteIdx_677_);
lean_dec(v_byteIdx_677_);
lean_dec_ref(v_s_676_);
v_r_680_ = lean_box_uint32(v_res_679_);
return v_r_680_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get___redArg(lean_object* v_s_681_, lean_object* v_pos_682_){
_start:
{
lean_object* v_str_683_; lean_object* v_startInclusive_684_; lean_object* v___x_685_; uint32_t v___x_686_; 
v_str_683_ = lean_ctor_get(v_s_681_, 0);
v_startInclusive_684_ = lean_ctor_get(v_s_681_, 1);
v___x_685_ = lean_nat_add(v_startInclusive_684_, v_pos_682_);
v___x_686_ = lean_string_utf8_get_fast(v_str_683_, v___x_685_);
lean_dec(v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___redArg___boxed(lean_object* v_s_687_, lean_object* v_pos_688_){
_start:
{
uint32_t v_res_689_; lean_object* v_r_690_; 
v_res_689_ = l_String_Slice_Pos_get___redArg(v_s_687_, v_pos_688_);
lean_dec(v_pos_688_);
lean_dec_ref(v_s_687_);
v_r_690_ = lean_box_uint32(v_res_689_);
return v_r_690_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get(lean_object* v_s_691_, lean_object* v_pos_692_, lean_object* v_h_693_){
_start:
{
lean_object* v_str_694_; lean_object* v_startInclusive_695_; lean_object* v___x_696_; uint32_t v___x_697_; 
v_str_694_ = lean_ctor_get(v_s_691_, 0);
v_startInclusive_695_ = lean_ctor_get(v_s_691_, 1);
v___x_696_ = lean_nat_add(v_startInclusive_695_, v_pos_692_);
v___x_697_ = lean_string_utf8_get_fast(v_str_694_, v___x_696_);
lean_dec(v___x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___boxed(lean_object* v_s_698_, lean_object* v_pos_699_, lean_object* v_h_700_){
_start:
{
uint32_t v_res_701_; lean_object* v_r_702_; 
v_res_701_ = l_String_Slice_Pos_get(v_s_698_, v_pos_699_, v_h_700_);
lean_dec(v_pos_699_);
lean_dec_ref(v_s_698_);
v_r_702_ = lean_box_uint32(v_res_701_);
return v_r_702_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f(lean_object* v_s_703_, lean_object* v_pos_704_){
_start:
{
lean_object* v_str_705_; lean_object* v_startInclusive_706_; lean_object* v_endExclusive_707_; lean_object* v___x_708_; uint8_t v_decide_709_; 
v_str_705_ = lean_ctor_get(v_s_703_, 0);
v_startInclusive_706_ = lean_ctor_get(v_s_703_, 1);
v_endExclusive_707_ = lean_ctor_get(v_s_703_, 2);
v___x_708_ = lean_nat_sub(v_endExclusive_707_, v_startInclusive_706_);
v_decide_709_ = lean_nat_dec_eq(v_pos_704_, v___x_708_);
lean_dec(v___x_708_);
if (v_decide_709_ == 0)
{
lean_object* v___x_710_; uint32_t v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_710_ = lean_nat_add(v_startInclusive_706_, v_pos_704_);
v___x_711_ = lean_string_utf8_get_fast(v_str_705_, v___x_710_);
lean_dec(v___x_710_);
v___x_712_ = lean_box_uint32(v___x_711_);
v___x_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
return v___x_713_;
}
else
{
lean_object* v___x_714_; 
v___x_714_ = lean_box(0);
return v___x_714_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f___boxed(lean_object* v_s_715_, lean_object* v_pos_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_String_Slice_Pos_get_x3f(v_s_715_, v_pos_716_);
lean_dec(v_pos_716_);
lean_dec_ref(v_s_715_);
return v_res_717_;
}
}
static lean_object* _init_l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1(void){
_start:
{
uint32_t v___x_718_; lean_object* v___x_719_; 
v___x_718_ = 65;
v___x_719_ = lean_box_uint32(v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT uint32_t l_panic___at___00String_Slice_Pos_get_x21_spec__0(lean_object* v_msg_720_){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; uint32_t v___x_723_; 
v___x_721_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1;
v___x_722_ = lean_panic_fn_borrowed(v___x_721_, v_msg_720_);
v___x_723_ = lean_unbox_uint32(v___x_722_);
lean_dec(v___x_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed(lean_object* v_msg_724_){
_start:
{
uint32_t v_res_725_; lean_object* v_r_726_; 
v_res_725_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v_msg_724_);
v_r_726_ = lean_box_uint32(v_res_725_);
return v_r_726_;
}
}
static lean_object* _init_l_String_Slice_Pos_get_x21___closed__2(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_729_ = ((lean_object*)(l_String_Slice_Pos_get_x21___closed__1));
v___x_730_ = lean_unsigned_to_nat(29u);
v___x_731_ = lean_unsigned_to_nat(1111u);
v___x_732_ = ((lean_object*)(l_String_Slice_Pos_get_x21___closed__0));
v___x_733_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_734_ = l_mkPanicMessageWithDecl(v___x_733_, v___x_732_, v___x_731_, v___x_730_, v___x_729_);
return v___x_734_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get_x21(lean_object* v_s_735_, lean_object* v_pos_736_){
_start:
{
lean_object* v_str_737_; lean_object* v_startInclusive_738_; lean_object* v_endExclusive_739_; lean_object* v___x_740_; uint8_t v_decide_741_; 
v_str_737_ = lean_ctor_get(v_s_735_, 0);
v_startInclusive_738_ = lean_ctor_get(v_s_735_, 1);
v_endExclusive_739_ = lean_ctor_get(v_s_735_, 2);
v___x_740_ = lean_nat_sub(v_endExclusive_739_, v_startInclusive_738_);
v_decide_741_ = lean_nat_dec_eq(v_pos_736_, v___x_740_);
lean_dec(v___x_740_);
if (v_decide_741_ == 0)
{
lean_object* v___x_742_; uint32_t v___x_743_; 
v___x_742_ = lean_nat_add(v_startInclusive_738_, v_pos_736_);
v___x_743_ = lean_string_utf8_get_fast(v_str_737_, v___x_742_);
lean_dec(v___x_742_);
return v___x_743_;
}
else
{
lean_object* v___x_744_; uint32_t v___x_745_; 
v___x_744_ = lean_obj_once(&l_String_Slice_Pos_get_x21___closed__2, &l_String_Slice_Pos_get_x21___closed__2_once, _init_l_String_Slice_Pos_get_x21___closed__2);
v___x_745_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v___x_744_);
return v___x_745_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x21___boxed(lean_object* v_s_746_, lean_object* v_pos_747_){
_start:
{
uint32_t v_res_748_; lean_object* v_r_749_; 
v_res_748_ = l_String_Slice_Pos_get_x21(v_s_746_, v_pos_747_);
lean_dec(v_pos_747_);
lean_dec_ref(v_s_746_);
v_r_749_ = lean_box_uint32(v_res_748_);
return v_r_749_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg(lean_object* v_pos_750_){
_start:
{
lean_inc(v_pos_750_);
return v_pos_750_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg___boxed(lean_object* v_pos_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_String_Pos_toSlice___redArg(v_pos_751_);
lean_dec(v_pos_751_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice(lean_object* v_s_753_, lean_object* v_pos_754_){
_start:
{
lean_inc(v_pos_754_);
return v_pos_754_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___boxed(lean_object* v_s_755_, lean_object* v_pos_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_String_Pos_toSlice(v_s_755_, v_pos_756_);
lean_dec(v_pos_756_);
lean_dec_ref(v_s_755_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg(lean_object* v_pos_758_){
_start:
{
lean_inc(v_pos_758_);
return v_pos_758_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg___boxed(lean_object* v_pos_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_String_Pos_ofToSlice___redArg(v_pos_759_);
lean_dec(v_pos_759_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice(lean_object* v_s_761_, lean_object* v_pos_762_){
_start:
{
lean_inc(v_pos_762_);
return v_pos_762_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___boxed(lean_object* v_s_763_, lean_object* v_pos_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_String_Pos_ofToSlice(v_s_763_, v_pos_764_);
lean_dec(v_pos_764_);
lean_dec_ref(v_s_763_);
return v_res_765_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get___redArg(lean_object* v_s_766_, lean_object* v_pos_767_){
_start:
{
uint32_t v___x_768_; 
v___x_768_ = lean_string_utf8_get_fast(v_s_766_, v_pos_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get___redArg___boxed(lean_object* v_s_769_, lean_object* v_pos_770_){
_start:
{
uint32_t v_res_771_; lean_object* v_r_772_; 
v_res_771_ = l_String_Pos_get___redArg(v_s_769_, v_pos_770_);
lean_dec(v_pos_770_);
lean_dec_ref(v_s_769_);
v_r_772_ = lean_box_uint32(v_res_771_);
return v_r_772_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get(lean_object* v_s_773_, lean_object* v_pos_774_, lean_object* v_h_775_){
_start:
{
uint32_t v___x_776_; 
v___x_776_ = lean_string_utf8_get_fast(v_s_773_, v_pos_774_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get___boxed(lean_object* v_s_777_, lean_object* v_pos_778_, lean_object* v_h_779_){
_start:
{
uint32_t v_res_780_; lean_object* v_r_781_; 
v_res_780_ = l_String_Pos_get(v_s_777_, v_pos_778_, v_h_779_);
lean_dec(v_pos_778_);
lean_dec_ref(v_s_777_);
v_r_781_ = lean_box_uint32(v_res_780_);
return v_r_781_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x3f(lean_object* v_s_782_, lean_object* v_pos_783_){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_784_ = lean_unsigned_to_nat(0u);
v___x_785_ = lean_string_utf8_byte_size(v_s_782_);
v___x_786_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_786_, 0, v_s_782_);
lean_ctor_set(v___x_786_, 1, v___x_784_);
lean_ctor_set(v___x_786_, 2, v___x_785_);
v___x_787_ = l_String_Slice_Pos_get_x3f(v___x_786_, v_pos_783_);
lean_dec_ref_known(v___x_786_, 3);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x3f___boxed(lean_object* v_s_788_, lean_object* v_pos_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_String_Pos_get_x3f(v_s_788_, v_pos_789_);
lean_dec(v_pos_789_);
return v_res_790_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get_x21(lean_object* v_s_791_, lean_object* v_pos_792_){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; uint32_t v___x_796_; 
v___x_793_ = lean_unsigned_to_nat(0u);
v___x_794_ = lean_string_utf8_byte_size(v_s_791_);
v___x_795_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_795_, 0, v_s_791_);
lean_ctor_set(v___x_795_, 1, v___x_793_);
lean_ctor_set(v___x_795_, 2, v___x_794_);
v___x_796_ = l_String_Slice_Pos_get_x21(v___x_795_, v_pos_792_);
lean_dec_ref_known(v___x_795_, 3);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x21___boxed(lean_object* v_s_797_, lean_object* v_pos_798_){
_start:
{
uint32_t v_res_799_; lean_object* v_r_800_; 
v_res_799_ = l_String_Pos_get_x21(v_s_797_, v_pos_798_);
lean_dec(v_pos_798_);
v_r_800_ = lean_box_uint32(v_res_799_);
return v_r_800_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_byte___redArg(lean_object* v_s_801_, lean_object* v_pos_802_){
_start:
{
uint8_t v___x_803_; 
v___x_803_ = lean_string_get_byte_fast(v_s_801_, v_pos_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_byte___redArg___boxed(lean_object* v_s_804_, lean_object* v_pos_805_){
_start:
{
uint8_t v_res_806_; lean_object* v_r_807_; 
v_res_806_ = l_String_Pos_byte___redArg(v_s_804_, v_pos_805_);
lean_dec_ref(v_s_804_);
v_r_807_ = lean_box(v_res_806_);
return v_r_807_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_byte(lean_object* v_s_808_, lean_object* v_pos_809_, lean_object* v_h_810_){
_start:
{
uint8_t v___x_811_; 
v___x_811_ = lean_string_get_byte_fast(v_s_808_, v_pos_809_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_byte___boxed(lean_object* v_s_812_, lean_object* v_pos_813_, lean_object* v_h_814_){
_start:
{
uint8_t v_res_815_; lean_object* v_r_816_; 
v_res_815_ = l_String_Pos_byte(v_s_812_, v_pos_813_, v_h_814_);
lean_dec_ref(v_s_812_);
v_r_816_ = lean_box(v_res_815_);
return v_r_816_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg(lean_object* v_pos_817_){
_start:
{
lean_inc(v_pos_817_);
return v_pos_817_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg___boxed(lean_object* v_pos_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_String_Pos_ofCopy___redArg(v_pos_818_);
lean_dec(v_pos_818_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy(lean_object* v_s_820_, lean_object* v_pos_821_){
_start:
{
lean_inc(v_pos_821_);
return v_pos_821_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___boxed(lean_object* v_s_822_, lean_object* v_pos_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_String_Pos_ofCopy(v_s_822_, v_pos_823_);
lean_dec(v_pos_823_);
lean_dec_ref(v_s_822_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg(lean_object* v_pos_825_){
_start:
{
lean_inc(v_pos_825_);
return v_pos_825_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg___boxed(lean_object* v_pos_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_String_Slice_Pos_copy___redArg(v_pos_826_);
lean_dec(v_pos_826_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy(lean_object* v_s_828_, lean_object* v_pos_829_){
_start:
{
lean_inc(v_pos_829_);
return v_pos_829_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___boxed(lean_object* v_s_830_, lean_object* v_pos_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_String_Slice_Pos_copy(v_s_830_, v_pos_831_);
lean_dec(v_pos_831_);
lean_dec_ref(v_s_830_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg(lean_object* v_pos_833_){
_start:
{
lean_inc(v_pos_833_);
return v_pos_833_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg___boxed(lean_object* v_pos_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_String_Slice_Pos_toCopy___redArg(v_pos_834_);
lean_dec(v_pos_834_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy(lean_object* v_s_836_, lean_object* v_pos_837_){
_start:
{
lean_inc(v_pos_837_);
return v_pos_837_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___boxed(lean_object* v_s_838_, lean_object* v_pos_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_String_Slice_Pos_toCopy(v_s_838_, v_pos_839_);
lean_dec(v_pos_839_);
lean_dec_ref(v_s_838_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg(lean_object* v_p_u2080_841_, lean_object* v_pos_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = lean_nat_add(v_p_u2080_841_, v_pos_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg___boxed(lean_object* v_p_u2080_844_, lean_object* v_pos_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_String_Slice_Pos_ofSliceFrom___redArg(v_p_u2080_844_, v_pos_845_);
lean_dec(v_pos_845_);
lean_dec(v_p_u2080_844_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom(lean_object* v_s_847_, lean_object* v_p_u2080_848_, lean_object* v_pos_849_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = lean_nat_add(v_p_u2080_848_, v_pos_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___boxed(lean_object* v_s_851_, lean_object* v_p_u2080_852_, lean_object* v_pos_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_String_Slice_Pos_ofSliceFrom(v_s_851_, v_p_u2080_852_, v_pos_853_);
lean_dec(v_pos_853_);
lean_dec(v_p_u2080_852_);
lean_dec_ref(v_s_851_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg(lean_object* v_p_u2080_855_, lean_object* v_pos_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = lean_nat_add(v_p_u2080_855_, v_pos_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg___boxed(lean_object* v_p_u2080_858_, lean_object* v_pos_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_String_Slice_Pos_ofReplaceStart___redArg(v_p_u2080_858_, v_pos_859_);
lean_dec(v_pos_859_);
lean_dec(v_p_u2080_858_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart(lean_object* v_s_861_, lean_object* v_p_u2080_862_, lean_object* v_pos_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = lean_nat_add(v_p_u2080_862_, v_pos_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___boxed(lean_object* v_s_865_, lean_object* v_p_u2080_866_, lean_object* v_pos_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_String_Slice_Pos_ofReplaceStart(v_s_865_, v_p_u2080_866_, v_pos_867_);
lean_dec(v_pos_867_);
lean_dec(v_p_u2080_866_);
lean_dec_ref(v_s_865_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg(lean_object* v_p_u2080_869_, lean_object* v_pos_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = lean_nat_sub(v_pos_870_, v_p_u2080_869_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg___boxed(lean_object* v_p_u2080_872_, lean_object* v_pos_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_String_Slice_Pos_sliceFrom___redArg(v_p_u2080_872_, v_pos_873_);
lean_dec(v_pos_873_);
lean_dec(v_p_u2080_872_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom(lean_object* v_s_875_, lean_object* v_p_u2080_876_, lean_object* v_pos_877_, lean_object* v_h_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = lean_nat_sub(v_pos_877_, v_p_u2080_876_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___boxed(lean_object* v_s_880_, lean_object* v_p_u2080_881_, lean_object* v_pos_882_, lean_object* v_h_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_String_Slice_Pos_sliceFrom(v_s_880_, v_p_u2080_881_, v_pos_882_, v_h_883_);
lean_dec(v_pos_882_);
lean_dec(v_p_u2080_881_);
lean_dec_ref(v_s_880_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg(lean_object* v_p_u2080_885_, lean_object* v_pos_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = lean_nat_sub(v_pos_886_, v_p_u2080_885_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg___boxed(lean_object* v_p_u2080_888_, lean_object* v_pos_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_String_Slice_Pos_toReplaceStart___redArg(v_p_u2080_888_, v_pos_889_);
lean_dec(v_pos_889_);
lean_dec(v_p_u2080_888_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart(lean_object* v_s_891_, lean_object* v_p_u2080_892_, lean_object* v_pos_893_, lean_object* v_h_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = lean_nat_sub(v_pos_893_, v_p_u2080_892_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___boxed(lean_object* v_s_896_, lean_object* v_p_u2080_897_, lean_object* v_pos_898_, lean_object* v_h_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_String_Slice_Pos_toReplaceStart(v_s_896_, v_p_u2080_897_, v_pos_898_, v_h_899_);
lean_dec(v_pos_898_);
lean_dec(v_p_u2080_897_);
lean_dec_ref(v_s_896_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg(lean_object* v_pos_901_){
_start:
{
lean_inc(v_pos_901_);
return v_pos_901_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg___boxed(lean_object* v_pos_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_String_Slice_Pos_ofSliceTo___redArg(v_pos_902_);
lean_dec(v_pos_902_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo(lean_object* v_s_904_, lean_object* v_p_u2080_905_, lean_object* v_pos_906_){
_start:
{
lean_inc(v_pos_906_);
return v_pos_906_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___boxed(lean_object* v_s_907_, lean_object* v_p_u2080_908_, lean_object* v_pos_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_String_Slice_Pos_ofSliceTo(v_s_907_, v_p_u2080_908_, v_pos_909_);
lean_dec(v_pos_909_);
lean_dec(v_p_u2080_908_);
lean_dec_ref(v_s_907_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg(lean_object* v_pos_911_){
_start:
{
lean_inc(v_pos_911_);
return v_pos_911_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg___boxed(lean_object* v_pos_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_String_Slice_Pos_ofReplaceEnd___redArg(v_pos_912_);
lean_dec(v_pos_912_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd(lean_object* v_s_914_, lean_object* v_p_u2080_915_, lean_object* v_pos_916_){
_start:
{
lean_inc(v_pos_916_);
return v_pos_916_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___boxed(lean_object* v_s_917_, lean_object* v_p_u2080_918_, lean_object* v_pos_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_String_Slice_Pos_ofReplaceEnd(v_s_917_, v_p_u2080_918_, v_pos_919_);
lean_dec(v_pos_919_);
lean_dec(v_p_u2080_918_);
lean_dec_ref(v_s_917_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg(lean_object* v_pos_921_){
_start:
{
lean_inc(v_pos_921_);
return v_pos_921_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg___boxed(lean_object* v_pos_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_String_Slice_Pos_sliceTo___redArg(v_pos_922_);
lean_dec(v_pos_922_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo(lean_object* v_s_924_, lean_object* v_p_u2080_925_, lean_object* v_pos_926_, lean_object* v_h_927_){
_start:
{
lean_inc(v_pos_926_);
return v_pos_926_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___boxed(lean_object* v_s_928_, lean_object* v_p_u2080_929_, lean_object* v_pos_930_, lean_object* v_h_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_String_Slice_Pos_sliceTo(v_s_928_, v_p_u2080_929_, v_pos_930_, v_h_931_);
lean_dec(v_pos_930_);
lean_dec(v_p_u2080_929_);
lean_dec_ref(v_s_928_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg(lean_object* v_pos_933_){
_start:
{
lean_inc(v_pos_933_);
return v_pos_933_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg___boxed(lean_object* v_pos_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_String_Slice_Pos_toReplaceEnd___redArg(v_pos_934_);
lean_dec(v_pos_934_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd(lean_object* v_s_936_, lean_object* v_p_u2080_937_, lean_object* v_pos_938_, lean_object* v_h_939_){
_start:
{
lean_inc(v_pos_938_);
return v_pos_938_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___boxed(lean_object* v_s_940_, lean_object* v_p_u2080_941_, lean_object* v_pos_942_, lean_object* v_h_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_String_Slice_Pos_toReplaceEnd(v_s_940_, v_p_u2080_941_, v_pos_942_, v_h_943_);
lean_dec(v_pos_942_);
lean_dec(v_p_u2080_941_);
lean_dec_ref(v_s_940_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg(lean_object* v_s_945_, lean_object* v_pos_946_){
_start:
{
lean_object* v_str_947_; lean_object* v_startInclusive_948_; lean_object* v___x_949_; uint8_t v___x_950_; uint8_t v___x_951_; uint8_t v___x_952_; uint8_t v___x_953_; uint8_t v___x_954_; 
v_str_947_ = lean_ctor_get(v_s_945_, 0);
v_startInclusive_948_ = lean_ctor_get(v_s_945_, 1);
v___x_949_ = lean_nat_add(v_startInclusive_948_, v_pos_946_);
v___x_950_ = lean_string_get_byte_fast(v_str_947_, v___x_949_);
v___x_951_ = 128;
v___x_952_ = lean_uint8_land(v___x_950_, v___x_951_);
v___x_953_ = 0;
v___x_954_ = lean_uint8_dec_eq(v___x_952_, v___x_953_);
if (v___x_954_ == 0)
{
uint8_t v___x_955_; uint8_t v___x_956_; uint8_t v___x_957_; uint8_t v___x_958_; 
v___x_955_ = 224;
v___x_956_ = lean_uint8_land(v___x_950_, v___x_955_);
v___x_957_ = 192;
v___x_958_ = lean_uint8_dec_eq(v___x_956_, v___x_957_);
if (v___x_958_ == 0)
{
uint8_t v___x_959_; uint8_t v___x_960_; uint8_t v___x_961_; 
v___x_959_ = 240;
v___x_960_ = lean_uint8_land(v___x_950_, v___x_959_);
v___x_961_ = lean_uint8_dec_eq(v___x_960_, v___x_955_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = lean_unsigned_to_nat(4u);
v___x_963_ = lean_nat_add(v_pos_946_, v___x_962_);
return v___x_963_;
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = lean_unsigned_to_nat(3u);
v___x_965_ = lean_nat_add(v_pos_946_, v___x_964_);
return v___x_965_;
}
}
else
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_unsigned_to_nat(2u);
v___x_967_ = lean_nat_add(v_pos_946_, v___x_966_);
return v___x_967_;
}
}
else
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_unsigned_to_nat(1u);
v___x_969_ = lean_nat_add(v_pos_946_, v___x_968_);
return v___x_969_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg___boxed(lean_object* v_s_970_, lean_object* v_pos_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_String_Slice_Pos_next___redArg(v_s_970_, v_pos_971_);
lean_dec(v_pos_971_);
lean_dec_ref(v_s_970_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next(lean_object* v_s_973_, lean_object* v_pos_974_, lean_object* v_h_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_String_Slice_Pos_next___redArg(v_s_973_, v_pos_974_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___boxed(lean_object* v_s_977_, lean_object* v_pos_978_, lean_object* v_h_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_String_Slice_Pos_next(v_s_977_, v_pos_978_, v_h_979_);
lean_dec(v_pos_978_);
lean_dec_ref(v_s_977_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f(lean_object* v_s_981_, lean_object* v_pos_982_){
_start:
{
lean_object* v_startInclusive_983_; lean_object* v_endExclusive_984_; lean_object* v___x_985_; uint8_t v_decide_986_; 
v_startInclusive_983_ = lean_ctor_get(v_s_981_, 1);
v_endExclusive_984_ = lean_ctor_get(v_s_981_, 2);
v___x_985_ = lean_nat_sub(v_endExclusive_984_, v_startInclusive_983_);
v_decide_986_ = lean_nat_dec_eq(v_pos_982_, v___x_985_);
lean_dec(v___x_985_);
if (v_decide_986_ == 0)
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = l_String_Slice_Pos_next___redArg(v_s_981_, v_pos_982_);
v___x_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
else
{
lean_object* v___x_989_; 
v___x_989_ = lean_box(0);
return v___x_989_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f___boxed(lean_object* v_s_990_, lean_object* v_pos_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_String_Slice_Pos_next_x3f(v_s_990_, v_pos_991_);
lean_dec(v_pos_991_);
lean_dec_ref(v_s_990_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(lean_object* v_msg_993_){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_unsigned_to_nat(0u);
v___x_995_ = lean_panic_fn_borrowed(v___x_994_, v_msg_993_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0(lean_object* v_s_996_, lean_object* v_msg_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v_msg_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___boxed(lean_object* v_s_999_, lean_object* v_msg_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0(v_s_999_, v_msg_1000_);
lean_dec_ref(v_s_999_);
return v_res_1001_;
}
}
static lean_object* _init_l_String_Slice_Pos_next_x21___closed__2(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1004_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__1));
v___x_1005_ = lean_unsigned_to_nat(29u);
v___x_1006_ = lean_unsigned_to_nat(1498u);
v___x_1007_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__0));
v___x_1008_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1009_ = l_mkPanicMessageWithDecl(v___x_1008_, v___x_1007_, v___x_1006_, v___x_1005_, v___x_1004_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21(lean_object* v_s_1010_, lean_object* v_pos_1011_){
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
lean_object* v___x_1016_; 
v___x_1016_ = l_String_Slice_Pos_next___redArg(v_s_1010_, v_pos_1011_);
return v___x_1016_;
}
else
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_obj_once(&l_String_Slice_Pos_next_x21___closed__2, &l_String_Slice_Pos_next_x21___closed__2_once, _init_l_String_Slice_Pos_next_x21___closed__2);
v___x_1018_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_1017_);
return v___x_1018_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21___boxed(lean_object* v_s_1019_, lean_object* v_pos_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_String_Slice_Pos_next_x21(v_s_1019_, v_pos_1020_);
lean_dec(v_pos_1020_);
lean_dec_ref(v_s_1019_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg(lean_object* v_s_1022_, lean_object* v_off_1023_){
_start:
{
lean_object* v_str_1024_; lean_object* v_startInclusive_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; uint8_t v___x_1028_; uint8_t v___x_1029_; uint8_t v___x_1030_; uint8_t v___x_1031_; 
v_str_1024_ = lean_ctor_get(v_s_1022_, 0);
v_startInclusive_1025_ = lean_ctor_get(v_s_1022_, 1);
v___x_1026_ = lean_nat_add(v_startInclusive_1025_, v_off_1023_);
v___x_1027_ = lean_string_get_byte_fast(v_str_1024_, v___x_1026_);
v___x_1028_ = 128;
v___x_1029_ = lean_uint8_land(v___x_1027_, v___x_1028_);
v___x_1030_ = 0;
v___x_1031_ = lean_uint8_dec_eq(v___x_1029_, v___x_1030_);
if (v___x_1031_ == 0)
{
uint8_t v___x_1032_; uint8_t v___x_1033_; uint8_t v___x_1034_; uint8_t v___x_1035_; 
v___x_1032_ = 224;
v___x_1033_ = lean_uint8_land(v___x_1027_, v___x_1032_);
v___x_1034_ = 192;
v___x_1035_ = lean_uint8_dec_eq(v___x_1033_, v___x_1034_);
if (v___x_1035_ == 0)
{
uint8_t v___x_1036_; uint8_t v___x_1037_; uint8_t v___x_1038_; 
v___x_1036_ = 240;
v___x_1037_ = lean_uint8_land(v___x_1027_, v___x_1036_);
v___x_1038_ = lean_uint8_dec_eq(v___x_1037_, v___x_1032_);
if (v___x_1038_ == 0)
{
uint8_t v___x_1039_; uint8_t v___x_1040_; uint8_t v___x_1041_; 
v___x_1039_ = 248;
v___x_1040_ = lean_uint8_land(v___x_1027_, v___x_1039_);
v___x_1041_ = lean_uint8_dec_eq(v___x_1040_, v___x_1036_);
if (v___x_1041_ == 0)
{
lean_object* v_zero_1042_; uint8_t v_isZero_1043_; lean_object* v_one_1044_; lean_object* v_n_1045_; 
v_zero_1042_ = lean_unsigned_to_nat(0u);
v_isZero_1043_ = lean_nat_dec_eq(v_off_1023_, v_zero_1042_);
v_one_1044_ = lean_unsigned_to_nat(1u);
v_n_1045_ = lean_nat_sub(v_off_1023_, v_one_1044_);
lean_dec(v_off_1023_);
v_off_1023_ = v_n_1045_;
goto _start;
}
else
{
return v_off_1023_;
}
}
else
{
return v_off_1023_;
}
}
else
{
return v_off_1023_;
}
}
else
{
return v_off_1023_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg___boxed(lean_object* v_s_1047_, lean_object* v_off_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1047_, v_off_1048_);
lean_dec_ref(v_s_1047_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go(lean_object* v_s_1050_, lean_object* v_off_1051_, lean_object* v_h_u2081_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1050_, v_off_1051_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___boxed(lean_object* v_s_1054_, lean_object* v_off_1055_, lean_object* v_h_u2081_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_String_Slice_Pos_prevAux_go(v_s_1054_, v_off_1055_, v_h_u2081_1056_);
lean_dec_ref(v_s_1054_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg(lean_object* v_s_1058_, lean_object* v_pos_1059_){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1060_ = lean_unsigned_to_nat(1u);
v___x_1061_ = lean_nat_sub(v_pos_1059_, v___x_1060_);
v___x_1062_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1058_, v___x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg___boxed(lean_object* v_s_1063_, lean_object* v_pos_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_String_Slice_Pos_prevAux___redArg(v_s_1063_, v_pos_1064_);
lean_dec(v_pos_1064_);
lean_dec_ref(v_s_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux(lean_object* v_s_1066_, lean_object* v_pos_1067_, lean_object* v_h_1068_){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1069_ = lean_unsigned_to_nat(1u);
v___x_1070_ = lean_nat_sub(v_pos_1067_, v___x_1069_);
v___x_1071_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1066_, v___x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___boxed(lean_object* v_s_1072_, lean_object* v_pos_1073_, lean_object* v_h_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_String_Slice_Pos_prevAux(v_s_1072_, v_pos_1073_, v_h_1074_);
lean_dec(v_pos_1073_);
lean_dec_ref(v_s_1072_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(lean_object* v_off_1076_, lean_object* v_h__1_1077_, lean_object* v_h__2_1078_){
_start:
{
lean_object* v_zero_1079_; uint8_t v_isZero_1080_; 
v_zero_1079_ = lean_unsigned_to_nat(0u);
v_isZero_1080_ = lean_nat_dec_eq(v_off_1076_, v_zero_1079_);
if (v_isZero_1080_ == 1)
{
lean_object* v___x_1081_; 
lean_dec(v_h__2_1078_);
v___x_1081_ = lean_apply_3(v_h__1_1077_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1081_;
}
else
{
lean_object* v_one_1082_; lean_object* v_n_1083_; lean_object* v___x_1084_; 
lean_dec(v_h__1_1077_);
v_one_1082_ = lean_unsigned_to_nat(1u);
v_n_1083_ = lean_nat_sub(v_off_1076_, v_one_1082_);
v___x_1084_ = lean_apply_4(v_h__2_1078_, v_n_1083_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg___boxed(lean_object* v_off_1085_, lean_object* v_h__1_1086_, lean_object* v_h__2_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(v_off_1085_, v_h__1_1086_, v_h__2_1087_);
lean_dec(v_off_1085_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(lean_object* v_s_1089_, lean_object* v_motive_1090_, lean_object* v_off_1091_, lean_object* v_h_u2081_1092_, lean_object* v_hbyte_1093_, lean_object* v_this_1094_, lean_object* v_h__1_1095_, lean_object* v_h__2_1096_){
_start:
{
lean_object* v_zero_1097_; uint8_t v_isZero_1098_; 
v_zero_1097_ = lean_unsigned_to_nat(0u);
v_isZero_1098_ = lean_nat_dec_eq(v_off_1091_, v_zero_1097_);
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
v_n_1101_ = lean_nat_sub(v_off_1091_, v_one_1100_);
v___x_1102_ = lean_apply_4(v_h__2_1096_, v_n_1101_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___boxed(lean_object* v_s_1103_, lean_object* v_motive_1104_, lean_object* v_off_1105_, lean_object* v_h_u2081_1106_, lean_object* v_hbyte_1107_, lean_object* v_this_1108_, lean_object* v_h__1_1109_, lean_object* v_h__2_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(v_s_1103_, v_motive_1104_, v_off_1105_, v_h_u2081_1106_, v_hbyte_1107_, v_this_1108_, v_h__1_1109_, v_h__2_1110_);
lean_dec(v_off_1105_);
lean_dec_ref(v_s_1103_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg(lean_object* v_off_1112_){
_start:
{
lean_inc(v_off_1112_);
return v_off_1112_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg___boxed(lean_object* v_off_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_String_Slice_pos___redArg(v_off_1113_);
lean_dec(v_off_1113_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos(lean_object* v_s_1115_, lean_object* v_off_1116_, lean_object* v_h_1117_){
_start:
{
lean_inc(v_off_1116_);
return v_off_1116_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___boxed(lean_object* v_s_1118_, lean_object* v_off_1119_, lean_object* v_h_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_String_Slice_pos(v_s_1118_, v_off_1119_, v_h_1120_);
lean_dec(v_off_1119_);
lean_dec_ref(v_s_1118_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f(lean_object* v_s_1122_, lean_object* v_off_1123_){
_start:
{
uint8_t v___x_1124_; 
v___x_1124_ = l_String_Pos_Raw_isValidForSlice(v_s_1122_, v_off_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; 
lean_dec(v_off_1123_);
v___x_1125_ = lean_box(0);
return v___x_1125_;
}
else
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1126_, 0, v_off_1123_);
return v___x_1126_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f___boxed(lean_object* v_s_1127_, lean_object* v_off_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_String_Slice_pos_x3f(v_s_1127_, v_off_1128_);
lean_dec_ref(v_s_1127_);
return v_res_1129_;
}
}
static lean_object* _init_l_String_Slice_pos_x21___closed__2(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1132_ = ((lean_object*)(l_String_Slice_pos_x21___closed__1));
v___x_1133_ = lean_unsigned_to_nat(4u);
v___x_1134_ = lean_unsigned_to_nat(1586u);
v___x_1135_ = ((lean_object*)(l_String_Slice_pos_x21___closed__0));
v___x_1136_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1137_ = l_mkPanicMessageWithDecl(v___x_1136_, v___x_1135_, v___x_1134_, v___x_1133_, v___x_1132_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21(lean_object* v_s_1138_, lean_object* v_off_1139_){
_start:
{
uint8_t v___x_1140_; 
v___x_1140_ = l_String_Pos_Raw_isValidForSlice(v_s_1138_, v_off_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = lean_obj_once(&l_String_Slice_pos_x21___closed__2, &l_String_Slice_pos_x21___closed__2_once, _init_l_String_Slice_pos_x21___closed__2);
v___x_1142_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_1141_);
return v___x_1142_;
}
else
{
lean_inc(v_off_1139_);
return v_off_1139_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21___boxed(lean_object* v_s_1143_, lean_object* v_off_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_String_Slice_pos_x21(v_s_1143_, v_off_1144_);
lean_dec(v_off_1144_);
lean_dec_ref(v_s_1143_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next___boxed(lean_object* v_s_1149_, lean_object* v_pos_1150_, lean_object* v_h_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = lean_string_utf8_next_fast(v_s_1149_, v_pos_1150_);
lean_dec(v_pos_1150_);
lean_dec_ref(v_s_1149_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x3f(lean_object* v_s_1153_, lean_object* v_pos_1154_){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1155_ = lean_unsigned_to_nat(0u);
v___x_1156_ = lean_string_utf8_byte_size(v_s_1153_);
v___x_1157_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1157_, 0, v_s_1153_);
lean_ctor_set(v___x_1157_, 1, v___x_1155_);
lean_ctor_set(v___x_1157_, 2, v___x_1156_);
v___x_1158_ = l_String_Slice_Pos_next_x3f(v___x_1157_, v_pos_1154_);
lean_dec_ref_known(v___x_1157_, 3);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_box(0);
return v___x_1159_;
}
else
{
lean_object* v_val_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
v_val_1160_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1158_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_val_1160_);
lean_dec(v___x_1158_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_val_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x3f___boxed(lean_object* v_s_1168_, lean_object* v_pos_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_String_Pos_next_x3f(v_s_1168_, v_pos_1169_);
lean_dec(v_pos_1169_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21(lean_object* v_s_1171_, lean_object* v_pos_1172_){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = lean_string_utf8_byte_size(v_s_1171_);
v___x_1175_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1175_, 0, v_s_1171_);
lean_ctor_set(v___x_1175_, 1, v___x_1173_);
lean_ctor_set(v___x_1175_, 2, v___x_1174_);
v___x_1176_ = l_String_Slice_Pos_next_x21(v___x_1175_, v_pos_1172_);
lean_dec_ref_known(v___x_1175_, 3);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21___boxed(lean_object* v_s_1177_, lean_object* v_pos_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_String_Pos_next_x21(v_s_1177_, v_pos_1178_);
lean_dec(v_pos_1178_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg(lean_object* v_off_1180_){
_start:
{
lean_inc(v_off_1180_);
return v_off_1180_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg___boxed(lean_object* v_off_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_String_pos___redArg(v_off_1181_);
lean_dec(v_off_1181_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_String_pos(lean_object* v_s_1183_, lean_object* v_off_1184_, lean_object* v_h_1185_){
_start:
{
lean_inc(v_off_1184_);
return v_off_1184_;
}
}
LEAN_EXPORT lean_object* l_String_pos___boxed(lean_object* v_s_1186_, lean_object* v_off_1187_, lean_object* v_h_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_String_pos(v_s_1186_, v_off_1187_, v_h_1188_);
lean_dec(v_off_1187_);
lean_dec_ref(v_s_1186_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x3f(lean_object* v_s_1190_, lean_object* v_off_1191_){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1192_ = lean_unsigned_to_nat(0u);
v___x_1193_ = lean_string_utf8_byte_size(v_s_1190_);
v___x_1194_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1194_, 0, v_s_1190_);
lean_ctor_set(v___x_1194_, 1, v___x_1192_);
lean_ctor_set(v___x_1194_, 2, v___x_1193_);
v___x_1195_ = l_String_Slice_pos_x3f(v___x_1194_, v_off_1191_);
lean_dec_ref_known(v___x_1194_, 3);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_box(0);
return v___x_1196_;
}
else
{
lean_object* v_val_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
v_val_1197_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1195_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_val_1197_);
lean_dec(v___x_1195_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_val_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_pos_x21(lean_object* v_s_1205_, lean_object* v_off_1206_){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = lean_string_utf8_byte_size(v_s_1205_);
v___x_1209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1209_, 0, v_s_1205_);
lean_ctor_set(v___x_1209_, 1, v___x_1207_);
lean_ctor_set(v___x_1209_, 2, v___x_1208_);
v___x_1210_ = l_String_Slice_pos_x21(v___x_1209_, v_off_1206_);
lean_dec_ref_known(v___x_1209_, 3);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x21___boxed(lean_object* v_s_1211_, lean_object* v_off_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_String_pos_x21(v_s_1211_, v_off_1212_);
lean_dec(v_off_1212_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg(lean_object* v_pos_1214_){
_start:
{
lean_inc(v_pos_1214_);
return v_pos_1214_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg___boxed(lean_object* v_pos_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_String_Slice_Pos_cast___redArg(v_pos_1215_);
lean_dec(v_pos_1215_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast(lean_object* v_s_1217_, lean_object* v_t_1218_, lean_object* v_pos_1219_, lean_object* v_h_1220_){
_start:
{
lean_inc(v_pos_1219_);
return v_pos_1219_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___boxed(lean_object* v_s_1221_, lean_object* v_t_1222_, lean_object* v_pos_1223_, lean_object* v_h_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_String_Slice_Pos_cast(v_s_1221_, v_t_1222_, v_pos_1223_, v_h_1224_);
lean_dec(v_pos_1223_);
lean_dec_ref(v_t_1222_);
lean_dec_ref(v_s_1221_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg(lean_object* v_pos_1226_){
_start:
{
lean_inc(v_pos_1226_);
return v_pos_1226_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg___boxed(lean_object* v_pos_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_String_Pos_cast___redArg(v_pos_1227_);
lean_dec(v_pos_1227_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast(lean_object* v_s_1229_, lean_object* v_t_1230_, lean_object* v_pos_1231_, lean_object* v_h_1232_){
_start:
{
lean_inc(v_pos_1231_);
return v_pos_1231_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___boxed(lean_object* v_s_1233_, lean_object* v_t_1234_, lean_object* v_pos_1235_, lean_object* v_h_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_String_Pos_cast(v_s_1233_, v_t_1234_, v_pos_1235_, v_h_1236_);
lean_dec(v_pos_1235_);
lean_dec_ref(v_t_1234_);
lean_dec_ref(v_s_1233_);
return v_res_1237_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_Raw_utf8GetAux(lean_object* v_x_1238_, lean_object* v_x_1239_, lean_object* v_x_1240_){
_start:
{
if (lean_obj_tag(v_x_1238_) == 0)
{
uint32_t v___x_1241_; 
lean_dec(v_x_1239_);
v___x_1241_ = 65;
return v___x_1241_;
}
else
{
lean_object* v_head_1242_; lean_object* v_tail_1243_; lean_object* v___y_1245_; uint8_t v_decide_1248_; 
v_head_1242_ = lean_ctor_get(v_x_1238_, 0);
v_tail_1243_ = lean_ctor_get(v_x_1238_, 1);
v_decide_1248_ = lean_nat_dec_eq(v_x_1239_, v_x_1240_);
if (v_decide_1248_ == 0)
{
uint32_t v___x_1249_; uint32_t v___x_1250_; uint8_t v___x_1251_; 
v___x_1249_ = 127;
v___x_1250_ = lean_unbox_uint32(v_head_1242_);
v___x_1251_ = lean_uint32_dec_le(v___x_1250_, v___x_1249_);
if (v___x_1251_ == 0)
{
uint32_t v___x_1252_; uint32_t v___x_1253_; uint8_t v___x_1254_; 
v___x_1252_ = 2047;
v___x_1253_ = lean_unbox_uint32(v_head_1242_);
v___x_1254_ = lean_uint32_dec_le(v___x_1253_, v___x_1252_);
if (v___x_1254_ == 0)
{
uint32_t v___x_1255_; uint32_t v___x_1256_; uint8_t v___x_1257_; 
v___x_1255_ = 65535;
v___x_1256_ = lean_unbox_uint32(v_head_1242_);
v___x_1257_ = lean_uint32_dec_le(v___x_1256_, v___x_1255_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; 
v___x_1258_ = lean_unsigned_to_nat(4u);
v___y_1245_ = v___x_1258_;
goto v___jp_1244_;
}
else
{
lean_object* v___x_1259_; 
v___x_1259_ = lean_unsigned_to_nat(3u);
v___y_1245_ = v___x_1259_;
goto v___jp_1244_;
}
}
else
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_unsigned_to_nat(2u);
v___y_1245_ = v___x_1260_;
goto v___jp_1244_;
}
}
else
{
lean_object* v___x_1261_; 
v___x_1261_ = lean_unsigned_to_nat(1u);
v___y_1245_ = v___x_1261_;
goto v___jp_1244_;
}
}
else
{
uint32_t v___x_1262_; 
lean_dec(v_x_1239_);
v___x_1262_ = lean_unbox_uint32(v_head_1242_);
return v___x_1262_;
}
v___jp_1244_:
{
lean_object* v___x_1246_; 
v___x_1246_ = lean_nat_add(v_x_1239_, v___y_1245_);
lean_dec(v_x_1239_);
v_x_1238_ = v_tail_1243_;
v_x_1239_ = v___x_1246_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux___boxed(lean_object* v_x_1263_, lean_object* v_x_1264_, lean_object* v_x_1265_){
_start:
{
uint32_t v_res_1266_; lean_object* v_r_1267_; 
v_res_1266_ = l_String_Pos_Raw_utf8GetAux(v_x_1263_, v_x_1264_, v_x_1265_);
lean_dec(v_x_1265_);
lean_dec(v_x_1263_);
v_r_1267_ = lean_box_uint32(v_res_1266_);
return v_r_1267_;
}
}
LEAN_EXPORT uint32_t l_String_utf8GetAux(lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
uint32_t v___x_1271_; 
v___x_1271_ = l_String_Pos_Raw_utf8GetAux(v_a_1268_, v_a_1269_, v_a_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux___boxed(lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_){
_start:
{
uint32_t v_res_1275_; lean_object* v_r_1276_; 
v_res_1275_ = l_String_utf8GetAux(v_a_1272_, v_a_1273_, v_a_1274_);
lean_dec(v_a_1274_);
lean_dec(v_a_1272_);
v_r_1276_ = lean_box_uint32(v_res_1275_);
return v_r_1276_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get___boxed(lean_object* v_s_1279_, lean_object* v_p_1280_){
_start:
{
uint32_t v_res_1281_; lean_object* v_r_1282_; 
v_res_1281_ = lean_string_utf8_get(v_s_1279_, v_p_1280_);
lean_dec(v_p_1280_);
lean_dec_ref(v_s_1279_);
v_r_1282_ = lean_box_uint32(v_res_1281_);
return v_r_1282_;
}
}
LEAN_EXPORT lean_object* l_String_get___boxed(lean_object* v_s_1285_, lean_object* v_p_1286_){
_start:
{
uint32_t v_res_1287_; lean_object* v_r_1288_; 
v_res_1287_ = lean_string_utf8_get(v_s_1285_, v_p_1286_);
lean_dec(v_p_1286_);
lean_dec_ref(v_s_1285_);
v_r_1288_ = lean_box_uint32(v_res_1287_);
return v_r_1288_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f(lean_object* v_x_1289_, lean_object* v_x_1290_, lean_object* v_x_1291_){
_start:
{
if (lean_obj_tag(v_x_1289_) == 0)
{
lean_object* v___x_1292_; 
lean_dec(v_x_1290_);
v___x_1292_ = lean_box(0);
return v___x_1292_;
}
else
{
lean_object* v_head_1293_; lean_object* v_tail_1294_; lean_object* v___y_1296_; uint8_t v_decide_1299_; 
v_head_1293_ = lean_ctor_get(v_x_1289_, 0);
v_tail_1294_ = lean_ctor_get(v_x_1289_, 1);
v_decide_1299_ = lean_nat_dec_eq(v_x_1290_, v_x_1291_);
if (v_decide_1299_ == 0)
{
uint32_t v___x_1300_; uint32_t v___x_1301_; uint8_t v___x_1302_; 
v___x_1300_ = 127;
v___x_1301_ = lean_unbox_uint32(v_head_1293_);
v___x_1302_ = lean_uint32_dec_le(v___x_1301_, v___x_1300_);
if (v___x_1302_ == 0)
{
uint32_t v___x_1303_; uint32_t v___x_1304_; uint8_t v___x_1305_; 
v___x_1303_ = 2047;
v___x_1304_ = lean_unbox_uint32(v_head_1293_);
v___x_1305_ = lean_uint32_dec_le(v___x_1304_, v___x_1303_);
if (v___x_1305_ == 0)
{
uint32_t v___x_1306_; uint32_t v___x_1307_; uint8_t v___x_1308_; 
v___x_1306_ = 65535;
v___x_1307_ = lean_unbox_uint32(v_head_1293_);
v___x_1308_ = lean_uint32_dec_le(v___x_1307_, v___x_1306_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; 
v___x_1309_ = lean_unsigned_to_nat(4u);
v___y_1296_ = v___x_1309_;
goto v___jp_1295_;
}
else
{
lean_object* v___x_1310_; 
v___x_1310_ = lean_unsigned_to_nat(3u);
v___y_1296_ = v___x_1310_;
goto v___jp_1295_;
}
}
else
{
lean_object* v___x_1311_; 
v___x_1311_ = lean_unsigned_to_nat(2u);
v___y_1296_ = v___x_1311_;
goto v___jp_1295_;
}
}
else
{
lean_object* v___x_1312_; 
v___x_1312_ = lean_unsigned_to_nat(1u);
v___y_1296_ = v___x_1312_;
goto v___jp_1295_;
}
}
else
{
lean_object* v___x_1313_; 
lean_dec(v_x_1290_);
lean_inc(v_head_1293_);
v___x_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1313_, 0, v_head_1293_);
return v___x_1313_;
}
v___jp_1295_:
{
lean_object* v___x_1297_; 
v___x_1297_ = lean_nat_add(v_x_1290_, v___y_1296_);
lean_dec(v_x_1290_);
v_x_1289_ = v_tail_1294_;
v_x_1290_ = v___x_1297_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f___boxed(lean_object* v_x_1314_, lean_object* v_x_1315_, lean_object* v_x_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_String_Pos_Raw_utf8GetAux_x3f(v_x_1314_, v_x_1315_, v_x_1316_);
lean_dec(v_x_1316_);
lean_dec(v_x_1314_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f(lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_String_Pos_Raw_utf8GetAux_x3f(v_a_1318_, v_a_1319_, v_a_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f___boxed(lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_String_utf8GetAux_x3f(v_a_1322_, v_a_1323_, v_a_1324_);
lean_dec(v_a_1324_);
lean_dec(v_a_1322_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1328_, lean_object* v_a_00___x40___internal___hyg_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1328_, v_a_00___x40___internal___hyg_1329_);
lean_dec(v_a_00___x40___internal___hyg_1329_);
lean_dec_ref(v_a_00___x40___internal___hyg_1328_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_String_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1333_, lean_object* v_a_00___x40___internal___hyg_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1333_, v_a_00___x40___internal___hyg_1334_);
lean_dec(v_a_00___x40___internal___hyg_1334_);
lean_dec_ref(v_a_00___x40___internal___hyg_1333_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x21___boxed(lean_object* v_s_1338_, lean_object* v_p_1339_){
_start:
{
uint32_t v_res_1340_; lean_object* v_r_1341_; 
v_res_1340_ = lean_string_utf8_get_bang(v_s_1338_, v_p_1339_);
lean_dec(v_p_1339_);
lean_dec_ref(v_s_1338_);
v_r_1341_ = lean_box_uint32(v_res_1340_);
return v_r_1341_;
}
}
LEAN_EXPORT lean_object* l_String_get_x21___boxed(lean_object* v_s_1344_, lean_object* v_p_1345_){
_start:
{
uint32_t v_res_1346_; lean_object* v_r_1347_; 
v_res_1346_ = lean_string_utf8_get_bang(v_s_1344_, v_p_1345_);
lean_dec(v_p_1345_);
lean_dec_ref(v_s_1344_);
v_r_1347_ = lean_box_uint32(v_res_1346_);
return v_r_1347_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux(uint32_t v_c_x27_1348_, lean_object* v_x_1349_, lean_object* v_x_1350_, lean_object* v_x_1351_){
_start:
{
if (lean_obj_tag(v_x_1349_) == 0)
{
return v_x_1349_;
}
else
{
lean_object* v_head_1352_; lean_object* v_tail_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1380_; 
v_head_1352_ = lean_ctor_get(v_x_1349_, 0);
v_tail_1353_ = lean_ctor_get(v_x_1349_, 1);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_x_1349_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1355_ = v_x_1349_;
v_isShared_1356_ = v_isSharedCheck_1380_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_tail_1353_);
lean_inc(v_head_1352_);
lean_dec(v_x_1349_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1380_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___y_1358_; uint8_t v_decide_1364_; 
v_decide_1364_ = lean_nat_dec_eq(v_x_1350_, v_x_1351_);
if (v_decide_1364_ == 0)
{
uint32_t v___x_1365_; uint32_t v___x_1366_; uint8_t v___x_1367_; 
v___x_1365_ = 127;
v___x_1366_ = lean_unbox_uint32(v_head_1352_);
v___x_1367_ = lean_uint32_dec_le(v___x_1366_, v___x_1365_);
if (v___x_1367_ == 0)
{
uint32_t v___x_1368_; uint32_t v___x_1369_; uint8_t v___x_1370_; 
v___x_1368_ = 2047;
v___x_1369_ = lean_unbox_uint32(v_head_1352_);
v___x_1370_ = lean_uint32_dec_le(v___x_1369_, v___x_1368_);
if (v___x_1370_ == 0)
{
uint32_t v___x_1371_; uint32_t v___x_1372_; uint8_t v___x_1373_; 
v___x_1371_ = 65535;
v___x_1372_ = lean_unbox_uint32(v_head_1352_);
v___x_1373_ = lean_uint32_dec_le(v___x_1372_, v___x_1371_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_unsigned_to_nat(4u);
v___y_1358_ = v___x_1374_;
goto v___jp_1357_;
}
else
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_unsigned_to_nat(3u);
v___y_1358_ = v___x_1375_;
goto v___jp_1357_;
}
}
else
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_unsigned_to_nat(2u);
v___y_1358_ = v___x_1376_;
goto v___jp_1357_;
}
}
else
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_unsigned_to_nat(1u);
v___y_1358_ = v___x_1377_;
goto v___jp_1357_;
}
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
lean_del_object(v___x_1355_);
lean_dec(v_head_1352_);
v___x_1378_ = lean_box_uint32(v_c_x27_1348_);
v___x_1379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
lean_ctor_set(v___x_1379_, 1, v_tail_1353_);
return v___x_1379_;
}
v___jp_1357_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1359_ = lean_nat_add(v_x_1350_, v___y_1358_);
v___x_1360_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1348_, v_tail_1353_, v___x_1359_, v_x_1351_);
lean_dec(v___x_1359_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 1, v___x_1360_);
v___x_1362_ = v___x_1355_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_head_1352_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux___boxed(lean_object* v_c_x27_1381_, lean_object* v_x_1382_, lean_object* v_x_1383_, lean_object* v_x_1384_){
_start:
{
uint32_t v_c_x27_boxed_1385_; lean_object* v_res_1386_; 
v_c_x27_boxed_1385_ = lean_unbox_uint32(v_c_x27_1381_);
lean_dec(v_c_x27_1381_);
v_res_1386_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_boxed_1385_, v_x_1382_, v_x_1383_, v_x_1384_);
lean_dec(v_x_1384_);
lean_dec(v_x_1383_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux(uint32_t v_c_x27_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1387_, v_a_1388_, v_a_1389_, v_a_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux___boxed(lean_object* v_c_x27_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
uint32_t v_c_x27_boxed_1396_; lean_object* v_res_1397_; 
v_c_x27_boxed_1396_ = lean_unbox_uint32(v_c_x27_1392_);
lean_dec(v_c_x27_1392_);
v_res_1397_ = l_String_utf8SetAux(v_c_x27_boxed_1396_, v_a_1393_, v_a_1394_, v_a_1395_);
lean_dec(v_a_1395_);
lean_dec(v_a_1394_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg(lean_object* v_s_1398_, lean_object* v_pos_1399_){
_start:
{
lean_object* v_str_1400_; lean_object* v_startInclusive_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v_str_1400_ = lean_ctor_get(v_s_1398_, 0);
v_startInclusive_1401_ = lean_ctor_get(v_s_1398_, 1);
v___x_1402_ = lean_nat_add(v_startInclusive_1401_, v_pos_1399_);
v___x_1403_ = lean_string_utf8_next_fast(v_str_1400_, v___x_1402_);
lean_dec(v___x_1402_);
v___x_1404_ = lean_nat_sub(v___x_1403_, v_startInclusive_1401_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg___boxed(lean_object* v_s_1405_, lean_object* v_pos_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_String_Slice_Pos_nextFast___redArg(v_s_1405_, v_pos_1406_);
lean_dec(v_pos_1406_);
lean_dec_ref(v_s_1405_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast(lean_object* v_s_1408_, lean_object* v_pos_1409_, lean_object* v_h_1410_){
_start:
{
lean_object* v_str_1411_; lean_object* v_startInclusive_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v_str_1411_ = lean_ctor_get(v_s_1408_, 0);
v_startInclusive_1412_ = lean_ctor_get(v_s_1408_, 1);
v___x_1413_ = lean_nat_add(v_startInclusive_1412_, v_pos_1409_);
v___x_1414_ = lean_string_utf8_next_fast(v_str_1411_, v___x_1413_);
lean_dec(v___x_1413_);
v___x_1415_ = lean_nat_sub(v___x_1414_, v_startInclusive_1412_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___boxed(lean_object* v_s_1416_, lean_object* v_pos_1417_, lean_object* v_h_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_String_Slice_Pos_nextFast(v_s_1416_, v_pos_1417_, v_h_1418_);
lean_dec(v_pos_1417_);
lean_dec_ref(v_s_1416_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_String_sliceTo(lean_object* v_s_1420_, lean_object* v_p_1421_){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = lean_unsigned_to_nat(0u);
v___x_1423_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1423_, 0, v_s_1420_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
lean_ctor_set(v___x_1423_, 2, v_p_1421_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_String_replaceEnd(lean_object* v_s_1424_, lean_object* v_p_1425_){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = lean_unsigned_to_nat(0u);
v___x_1427_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1427_, 0, v_s_1424_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
lean_ctor_set(v___x_1427_, 2, v_p_1425_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_String_sliceFrom(lean_object* v_s_1428_, lean_object* v_p_1429_){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = lean_string_utf8_byte_size(v_s_1428_);
v___x_1431_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1431_, 0, v_s_1428_);
lean_ctor_set(v___x_1431_, 1, v_p_1429_);
lean_ctor_set(v___x_1431_, 2, v___x_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStart(lean_object* v_s_1432_, lean_object* v_p_1433_){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_string_utf8_byte_size(v_s_1432_);
v___x_1435_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1435_, 0, v_s_1432_);
lean_ctor_set(v___x_1435_, 1, v_p_1433_);
lean_ctor_set(v___x_1435_, 2, v___x_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_String_slice___redArg(lean_object* v_s_1436_, lean_object* v_startInclusive_1437_, lean_object* v_endExclusive_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1439_, 0, v_s_1436_);
lean_ctor_set(v___x_1439_, 1, v_startInclusive_1437_);
lean_ctor_set(v___x_1439_, 2, v_endExclusive_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_String_slice(lean_object* v_s_1440_, lean_object* v_startInclusive_1441_, lean_object* v_endExclusive_1442_, lean_object* v_h_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1444_, 0, v_s_1440_);
lean_ctor_set(v___x_1444_, 1, v_startInclusive_1441_);
lean_ctor_set(v___x_1444_, 2, v_endExclusive_1442_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x3f(lean_object* v_s_1445_, lean_object* v_startInclusive_1446_, lean_object* v_endExclusive_1447_){
_start:
{
uint8_t v___x_1448_; 
v___x_1448_ = lean_nat_dec_le(v_startInclusive_1446_, v_endExclusive_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; 
lean_dec(v_endExclusive_1447_);
lean_dec(v_startInclusive_1446_);
lean_dec_ref(v_s_1445_);
v___x_1449_ = lean_box(0);
return v___x_1449_;
}
else
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1450_, 0, v_s_1445_);
lean_ctor_set(v___x_1450_, 1, v_startInclusive_1446_);
lean_ctor_set(v___x_1450_, 2, v_endExclusive_1447_);
v___x_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
return v___x_1451_;
}
}
}
LEAN_EXPORT lean_object* l_String_slice_x21(lean_object* v_s_1452_, lean_object* v_p_u2081_1453_, lean_object* v_p_u2082_1454_){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1455_ = lean_unsigned_to_nat(0u);
v___x_1456_ = lean_string_utf8_byte_size(v_s_1452_);
v___x_1457_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1457_, 0, v_s_1452_);
lean_ctor_set(v___x_1457_, 1, v___x_1455_);
lean_ctor_set(v___x_1457_, 2, v___x_1456_);
v___x_1458_ = l_String_Slice_slice_x21(v___x_1457_, v_p_u2081_1453_, v_p_u2082_1454_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x21___boxed(lean_object* v_s_1459_, lean_object* v_p_u2081_1460_, lean_object* v_p_u2082_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_String_slice_x21(v_s_1459_, v_p_u2081_1460_, v_p_u2082_1461_);
lean_dec(v_p_u2082_1461_);
lean_dec(v_p_u2081_1460_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21(lean_object* v_s_1463_, lean_object* v_p_u2081_1464_, lean_object* v_p_u2082_1465_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_String_slice_x21(v_s_1463_, v_p_u2081_1464_, v_p_u2082_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21___boxed(lean_object* v_s_1467_, lean_object* v_p_u2081_1468_, lean_object* v_p_u2082_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_String_replaceStartEnd_x21(v_s_1467_, v_p_u2081_1468_, v_p_u2082_1469_);
lean_dec(v_p_u2082_1469_);
lean_dec(v_p_u2081_1468_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg(lean_object* v_p_u2080_1471_, lean_object* v_pos_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = lean_nat_add(v_p_u2080_1471_, v_pos_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg___boxed(lean_object* v_p_u2080_1474_, lean_object* v_pos_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_String_Pos_ofSliceFrom___redArg(v_p_u2080_1474_, v_pos_1475_);
lean_dec(v_pos_1475_);
lean_dec(v_p_u2080_1474_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom(lean_object* v_s_1477_, lean_object* v_p_u2080_1478_, lean_object* v_pos_1479_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_nat_add(v_p_u2080_1478_, v_pos_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___boxed(lean_object* v_s_1481_, lean_object* v_p_u2080_1482_, lean_object* v_pos_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_String_Pos_ofSliceFrom(v_s_1481_, v_p_u2080_1482_, v_pos_1483_);
lean_dec(v_pos_1483_);
lean_dec(v_p_u2080_1482_);
lean_dec_ref(v_s_1481_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg(lean_object* v_p_u2080_1485_, lean_object* v_pos_1486_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = lean_nat_add(v_p_u2080_1485_, v_pos_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg___boxed(lean_object* v_p_u2080_1488_, lean_object* v_pos_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_String_Pos_ofReplaceStart___redArg(v_p_u2080_1488_, v_pos_1489_);
lean_dec(v_pos_1489_);
lean_dec(v_p_u2080_1488_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart(lean_object* v_s_1491_, lean_object* v_p_u2080_1492_, lean_object* v_pos_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_nat_add(v_p_u2080_1492_, v_pos_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___boxed(lean_object* v_s_1495_, lean_object* v_p_u2080_1496_, lean_object* v_pos_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_String_Pos_ofReplaceStart(v_s_1495_, v_p_u2080_1496_, v_pos_1497_);
lean_dec(v_pos_1497_);
lean_dec(v_p_u2080_1496_);
lean_dec_ref(v_s_1495_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg(lean_object* v_p_u2080_1499_, lean_object* v_pos_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_nat_sub(v_pos_1500_, v_p_u2080_1499_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg___boxed(lean_object* v_p_u2080_1502_, lean_object* v_pos_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_String_Pos_sliceFrom___redArg(v_p_u2080_1502_, v_pos_1503_);
lean_dec(v_pos_1503_);
lean_dec(v_p_u2080_1502_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom(lean_object* v_s_1505_, lean_object* v_p_u2080_1506_, lean_object* v_pos_1507_, lean_object* v_h_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_nat_sub(v_pos_1507_, v_p_u2080_1506_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___boxed(lean_object* v_s_1510_, lean_object* v_p_u2080_1511_, lean_object* v_pos_1512_, lean_object* v_h_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_String_Pos_sliceFrom(v_s_1510_, v_p_u2080_1511_, v_pos_1512_, v_h_1513_);
lean_dec(v_pos_1512_);
lean_dec(v_p_u2080_1511_);
lean_dec_ref(v_s_1510_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg(lean_object* v_p_u2080_1515_, lean_object* v_pos_1516_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_nat_sub(v_pos_1516_, v_p_u2080_1515_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg___boxed(lean_object* v_p_u2080_1518_, lean_object* v_pos_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_String_Pos_toReplaceStart___redArg(v_p_u2080_1518_, v_pos_1519_);
lean_dec(v_pos_1519_);
lean_dec(v_p_u2080_1518_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart(lean_object* v_s_1521_, lean_object* v_p_u2080_1522_, lean_object* v_pos_1523_, lean_object* v_h_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_nat_sub(v_pos_1523_, v_p_u2080_1522_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___boxed(lean_object* v_s_1526_, lean_object* v_p_u2080_1527_, lean_object* v_pos_1528_, lean_object* v_h_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_String_Pos_toReplaceStart(v_s_1526_, v_p_u2080_1527_, v_pos_1528_, v_h_1529_);
lean_dec(v_pos_1528_);
lean_dec(v_p_u2080_1527_);
lean_dec_ref(v_s_1526_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg(lean_object* v_pos_1531_){
_start:
{
lean_inc(v_pos_1531_);
return v_pos_1531_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg___boxed(lean_object* v_pos_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_String_Pos_ofSliceTo___redArg(v_pos_1532_);
lean_dec(v_pos_1532_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo(lean_object* v_s_1534_, lean_object* v_p_u2080_1535_, lean_object* v_pos_1536_){
_start:
{
lean_inc(v_pos_1536_);
return v_pos_1536_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___boxed(lean_object* v_s_1537_, lean_object* v_p_u2080_1538_, lean_object* v_pos_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_String_Pos_ofSliceTo(v_s_1537_, v_p_u2080_1538_, v_pos_1539_);
lean_dec(v_pos_1539_);
lean_dec(v_p_u2080_1538_);
lean_dec_ref(v_s_1537_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg(lean_object* v_pos_1541_){
_start:
{
lean_inc(v_pos_1541_);
return v_pos_1541_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg___boxed(lean_object* v_pos_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_String_Pos_ofReplaceEnd___redArg(v_pos_1542_);
lean_dec(v_pos_1542_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd(lean_object* v_s_1544_, lean_object* v_p_u2080_1545_, lean_object* v_pos_1546_){
_start:
{
lean_inc(v_pos_1546_);
return v_pos_1546_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___boxed(lean_object* v_s_1547_, lean_object* v_p_u2080_1548_, lean_object* v_pos_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_String_Pos_ofReplaceEnd(v_s_1547_, v_p_u2080_1548_, v_pos_1549_);
lean_dec(v_pos_1549_);
lean_dec(v_p_u2080_1548_);
lean_dec_ref(v_s_1547_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg(lean_object* v_pos_1551_){
_start:
{
lean_inc(v_pos_1551_);
return v_pos_1551_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg___boxed(lean_object* v_pos_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_String_Pos_sliceTo___redArg(v_pos_1552_);
lean_dec(v_pos_1552_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo(lean_object* v_s_1554_, lean_object* v_p_u2080_1555_, lean_object* v_pos_1556_, lean_object* v_h_1557_){
_start:
{
lean_inc(v_pos_1556_);
return v_pos_1556_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___boxed(lean_object* v_s_1558_, lean_object* v_p_u2080_1559_, lean_object* v_pos_1560_, lean_object* v_h_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_String_Pos_sliceTo(v_s_1558_, v_p_u2080_1559_, v_pos_1560_, v_h_1561_);
lean_dec(v_pos_1560_);
lean_dec(v_p_u2080_1559_);
lean_dec_ref(v_s_1558_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg(lean_object* v_pos_1563_){
_start:
{
lean_inc(v_pos_1563_);
return v_pos_1563_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg___boxed(lean_object* v_pos_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_String_Pos_toReplaceEnd___redArg(v_pos_1564_);
lean_dec(v_pos_1564_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd(lean_object* v_s_1566_, lean_object* v_p_u2080_1567_, lean_object* v_pos_1568_, lean_object* v_h_1569_){
_start:
{
lean_inc(v_pos_1568_);
return v_pos_1568_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___boxed(lean_object* v_s_1570_, lean_object* v_p_u2080_1571_, lean_object* v_pos_1572_, lean_object* v_h_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_String_Pos_toReplaceEnd(v_s_1570_, v_p_u2080_1571_, v_pos_1572_, v_h_1573_);
lean_dec(v_pos_1572_);
lean_dec(v_p_u2080_1571_);
lean_dec_ref(v_s_1570_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg(lean_object* v_p_u2080_1575_, lean_object* v_pos_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = lean_nat_add(v_p_u2080_1575_, v_pos_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1578_, lean_object* v_pos_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_String_Slice_Pos_ofSlice___redArg(v_p_u2080_1578_, v_pos_1579_);
lean_dec(v_pos_1579_);
lean_dec(v_p_u2080_1578_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice(lean_object* v_s_1581_, lean_object* v_p_u2080_1582_, lean_object* v_p_u2081_1583_, lean_object* v_h_1584_, lean_object* v_pos_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_nat_add(v_p_u2080_1582_, v_pos_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___boxed(lean_object* v_s_1587_, lean_object* v_p_u2080_1588_, lean_object* v_p_u2081_1589_, lean_object* v_h_1590_, lean_object* v_pos_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_String_Slice_Pos_ofSlice(v_s_1587_, v_p_u2080_1588_, v_p_u2081_1589_, v_h_1590_, v_pos_1591_);
lean_dec(v_pos_1591_);
lean_dec(v_p_u2081_1589_);
lean_dec(v_p_u2080_1588_);
lean_dec_ref(v_s_1587_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg(lean_object* v_p_u2080_1593_, lean_object* v_pos_1594_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = lean_nat_add(v_p_u2080_1593_, v_pos_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1596_, lean_object* v_pos_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_String_Pos_ofSlice___redArg(v_p_u2080_1596_, v_pos_1597_);
lean_dec(v_pos_1597_);
lean_dec(v_p_u2080_1596_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice(lean_object* v_s_1599_, lean_object* v_p_u2080_1600_, lean_object* v_p_u2081_1601_, lean_object* v_h_1602_, lean_object* v_pos_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = lean_nat_add(v_p_u2080_1600_, v_pos_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___boxed(lean_object* v_s_1605_, lean_object* v_p_u2080_1606_, lean_object* v_p_u2081_1607_, lean_object* v_h_1608_, lean_object* v_pos_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_String_Pos_ofSlice(v_s_1605_, v_p_u2080_1606_, v_p_u2081_1607_, v_h_1608_, v_pos_1609_);
lean_dec(v_pos_1609_);
lean_dec(v_p_u2081_1607_);
lean_dec(v_p_u2080_1606_);
lean_dec_ref(v_s_1605_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg(lean_object* v_pos_1611_, lean_object* v_p_u2080_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_nat_sub(v_pos_1611_, v_p_u2080_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg___boxed(lean_object* v_pos_1614_, lean_object* v_p_u2080_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_String_Slice_Pos_slice___redArg(v_pos_1614_, v_p_u2080_1615_);
lean_dec(v_p_u2080_1615_);
lean_dec(v_pos_1614_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice(lean_object* v_s_1617_, lean_object* v_pos_1618_, lean_object* v_p_u2080_1619_, lean_object* v_p_u2081_1620_, lean_object* v_h_u2081_1621_, lean_object* v_h_u2082_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_nat_sub(v_pos_1618_, v_p_u2080_1619_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___boxed(lean_object* v_s_1624_, lean_object* v_pos_1625_, lean_object* v_p_u2080_1626_, lean_object* v_p_u2081_1627_, lean_object* v_h_u2081_1628_, lean_object* v_h_u2082_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_String_Slice_Pos_slice(v_s_1624_, v_pos_1625_, v_p_u2080_1626_, v_p_u2081_1627_, v_h_u2081_1628_, v_h_u2082_1629_);
lean_dec(v_p_u2081_1627_);
lean_dec(v_p_u2080_1626_);
lean_dec(v_pos_1625_);
lean_dec_ref(v_s_1624_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg(lean_object* v_pos_1631_, lean_object* v_p_u2080_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = lean_nat_sub(v_pos_1631_, v_p_u2080_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg___boxed(lean_object* v_pos_1634_, lean_object* v_p_u2080_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_String_Pos_slice___redArg(v_pos_1634_, v_p_u2080_1635_);
lean_dec(v_p_u2080_1635_);
lean_dec(v_pos_1634_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice(lean_object* v_s_1637_, lean_object* v_pos_1638_, lean_object* v_p_u2080_1639_, lean_object* v_p_u2081_1640_, lean_object* v_h_u2081_1641_, lean_object* v_h_u2082_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = lean_nat_sub(v_pos_1638_, v_p_u2080_1639_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___boxed(lean_object* v_s_1644_, lean_object* v_pos_1645_, lean_object* v_p_u2080_1646_, lean_object* v_p_u2081_1647_, lean_object* v_h_u2081_1648_, lean_object* v_h_u2082_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_String_Pos_slice(v_s_1644_, v_pos_1645_, v_p_u2080_1646_, v_p_u2081_1647_, v_h_u2081_1648_, v_h_u2082_1649_);
lean_dec(v_p_u2081_1647_);
lean_dec(v_p_u2080_1646_);
lean_dec(v_pos_1645_);
lean_dec_ref(v_s_1644_);
return v_res_1650_;
}
}
static lean_object* _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2(void){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1653_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__1));
v___x_1654_ = lean_unsigned_to_nat(4u);
v___x_1655_ = lean_unsigned_to_nat(2601u);
v___x_1656_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__0));
v___x_1657_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1658_ = l_mkPanicMessageWithDecl(v___x_1657_, v___x_1656_, v___x_1655_, v___x_1654_, v___x_1653_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg(lean_object* v_pos_1659_, lean_object* v_p_u2080_1660_, lean_object* v_p_u2081_1661_){
_start:
{
uint8_t v___x_1666_; 
v___x_1666_ = lean_nat_dec_le(v_p_u2080_1660_, v_pos_1659_);
if (v___x_1666_ == 0)
{
goto v___jp_1662_;
}
else
{
uint8_t v___x_1667_; 
v___x_1667_ = lean_nat_dec_le(v_pos_1659_, v_p_u2081_1661_);
if (v___x_1667_ == 0)
{
goto v___jp_1662_;
}
else
{
lean_object* v___x_1668_; 
v___x_1668_ = lean_nat_sub(v_pos_1659_, v_p_u2080_1660_);
return v___x_1668_;
}
}
v___jp_1662_:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1663_ = lean_unsigned_to_nat(0u);
v___x_1664_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1665_ = l_panic___redArg(v___x_1663_, v___x_1664_);
return v___x_1665_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1669_, lean_object* v_p_u2080_1670_, lean_object* v_p_u2081_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_String_Slice_Pos_sliceOrPanic___redArg(v_pos_1669_, v_p_u2080_1670_, v_p_u2081_1671_);
lean_dec(v_p_u2081_1671_);
lean_dec(v_p_u2080_1670_);
lean_dec(v_pos_1669_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic(lean_object* v_s_1673_, lean_object* v_pos_1674_, lean_object* v_p_u2080_1675_, lean_object* v_p_u2081_1676_, lean_object* v_h_1677_){
_start:
{
uint8_t v___x_1682_; 
v___x_1682_ = lean_nat_dec_le(v_p_u2080_1675_, v_pos_1674_);
if (v___x_1682_ == 0)
{
goto v___jp_1678_;
}
else
{
uint8_t v___x_1683_; 
v___x_1683_ = lean_nat_dec_le(v_pos_1674_, v_p_u2081_1676_);
if (v___x_1683_ == 0)
{
goto v___jp_1678_;
}
else
{
lean_object* v___x_1684_; 
v___x_1684_ = lean_nat_sub(v_pos_1674_, v_p_u2080_1675_);
return v___x_1684_;
}
}
v___jp_1678_:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = lean_unsigned_to_nat(0u);
v___x_1680_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1681_ = l_panic___redArg(v___x_1679_, v___x_1680_);
return v___x_1681_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___boxed(lean_object* v_s_1685_, lean_object* v_pos_1686_, lean_object* v_p_u2080_1687_, lean_object* v_p_u2081_1688_, lean_object* v_h_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_String_Slice_Pos_sliceOrPanic(v_s_1685_, v_pos_1686_, v_p_u2080_1687_, v_p_u2081_1688_, v_h_1689_);
lean_dec(v_p_u2081_1688_);
lean_dec(v_p_u2080_1687_);
lean_dec(v_pos_1686_);
lean_dec_ref(v_s_1685_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg(lean_object* v_pos_1691_, lean_object* v_p_u2080_1692_, lean_object* v_p_u2081_1693_){
_start:
{
uint8_t v___x_1698_; 
v___x_1698_ = lean_nat_dec_le(v_p_u2080_1692_, v_pos_1691_);
if (v___x_1698_ == 0)
{
goto v___jp_1694_;
}
else
{
uint8_t v___x_1699_; 
v___x_1699_ = lean_nat_dec_le(v_pos_1691_, v_p_u2081_1693_);
if (v___x_1699_ == 0)
{
goto v___jp_1694_;
}
else
{
lean_object* v___x_1700_; 
v___x_1700_ = lean_nat_sub(v_pos_1691_, v_p_u2080_1692_);
return v___x_1700_;
}
}
v___jp_1694_:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1695_ = lean_unsigned_to_nat(0u);
v___x_1696_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1697_ = l_panic___redArg(v___x_1695_, v___x_1696_);
return v___x_1697_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1701_, lean_object* v_p_u2080_1702_, lean_object* v_p_u2081_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_String_Pos_sliceOrPanic___redArg(v_pos_1701_, v_p_u2080_1702_, v_p_u2081_1703_);
lean_dec(v_p_u2081_1703_);
lean_dec(v_p_u2080_1702_);
lean_dec(v_pos_1701_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic(lean_object* v_s_1705_, lean_object* v_pos_1706_, lean_object* v_p_u2080_1707_, lean_object* v_p_u2081_1708_, lean_object* v_h_1709_){
_start:
{
uint8_t v___x_1714_; 
v___x_1714_ = lean_nat_dec_le(v_p_u2080_1707_, v_pos_1706_);
if (v___x_1714_ == 0)
{
goto v___jp_1710_;
}
else
{
uint8_t v___x_1715_; 
v___x_1715_ = lean_nat_dec_le(v_pos_1706_, v_p_u2081_1708_);
if (v___x_1715_ == 0)
{
goto v___jp_1710_;
}
else
{
lean_object* v___x_1716_; 
v___x_1716_ = lean_nat_sub(v_pos_1706_, v_p_u2080_1707_);
return v___x_1716_;
}
}
v___jp_1710_:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1711_ = lean_unsigned_to_nat(0u);
v___x_1712_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1713_ = l_panic___redArg(v___x_1711_, v___x_1712_);
return v___x_1713_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___boxed(lean_object* v_s_1717_, lean_object* v_pos_1718_, lean_object* v_p_u2080_1719_, lean_object* v_p_u2081_1720_, lean_object* v_h_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_String_Pos_sliceOrPanic(v_s_1717_, v_pos_1718_, v_p_u2080_1719_, v_p_u2081_1720_, v_h_1721_);
lean_dec(v_p_u2081_1720_);
lean_dec(v_p_u2080_1719_);
lean_dec(v_pos_1718_);
lean_dec_ref(v_s_1717_);
return v_res_1722_;
}
}
static lean_object* _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1724_ = ((lean_object*)(l_String_Slice_slice_x21___closed__1));
v___x_1725_ = lean_unsigned_to_nat(4u);
v___x_1726_ = lean_unsigned_to_nat(2625u);
v___x_1727_ = ((lean_object*)(l_String_Slice_Pos_ofSlice_x21___redArg___closed__0));
v___x_1728_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1729_ = l_mkPanicMessageWithDecl(v___x_1728_, v___x_1727_, v___x_1726_, v___x_1725_, v___x_1724_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1730_, lean_object* v_p_u2081_1731_, lean_object* v_pos_1732_){
_start:
{
uint8_t v___x_1733_; 
v___x_1733_ = lean_nat_dec_le(v_p_u2080_1730_, v_p_u2081_1731_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1734_ = lean_unsigned_to_nat(0u);
v___x_1735_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1736_ = l_panic___redArg(v___x_1734_, v___x_1735_);
return v___x_1736_;
}
else
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_nat_add(v_p_u2080_1730_, v_pos_1732_);
return v___x_1737_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1738_, lean_object* v_p_u2081_1739_, lean_object* v_pos_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_String_Slice_Pos_ofSlice_x21___redArg(v_p_u2080_1738_, v_p_u2081_1739_, v_pos_1740_);
lean_dec(v_pos_1740_);
lean_dec(v_p_u2081_1739_);
lean_dec(v_p_u2080_1738_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21(lean_object* v_s_1742_, lean_object* v_p_u2080_1743_, lean_object* v_p_u2081_1744_, lean_object* v_pos_1745_){
_start:
{
uint8_t v___x_1746_; 
v___x_1746_ = lean_nat_dec_le(v_p_u2080_1743_, v_p_u2081_1744_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1747_ = lean_unsigned_to_nat(0u);
v___x_1748_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1749_ = l_panic___redArg(v___x_1747_, v___x_1748_);
return v___x_1749_;
}
else
{
lean_object* v___x_1750_; 
v___x_1750_ = lean_nat_add(v_p_u2080_1743_, v_pos_1745_);
return v___x_1750_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___boxed(lean_object* v_s_1751_, lean_object* v_p_u2080_1752_, lean_object* v_p_u2081_1753_, lean_object* v_pos_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_String_Slice_Pos_ofSlice_x21(v_s_1751_, v_p_u2080_1752_, v_p_u2081_1753_, v_pos_1754_);
lean_dec(v_pos_1754_);
lean_dec(v_p_u2081_1753_);
lean_dec(v_p_u2080_1752_);
lean_dec_ref(v_s_1751_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1756_, lean_object* v_p_u2081_1757_, lean_object* v_pos_1758_){
_start:
{
uint8_t v___x_1759_; 
v___x_1759_ = lean_nat_dec_le(v_p_u2080_1756_, v_p_u2081_1757_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1760_ = lean_unsigned_to_nat(0u);
v___x_1761_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1762_ = l_panic___redArg(v___x_1760_, v___x_1761_);
return v___x_1762_;
}
else
{
lean_object* v___x_1763_; 
v___x_1763_ = lean_nat_add(v_p_u2080_1756_, v_pos_1758_);
return v___x_1763_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1764_, lean_object* v_p_u2081_1765_, lean_object* v_pos_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_String_Pos_ofSlice_x21___redArg(v_p_u2080_1764_, v_p_u2081_1765_, v_pos_1766_);
lean_dec(v_pos_1766_);
lean_dec(v_p_u2081_1765_);
lean_dec(v_p_u2080_1764_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21(lean_object* v_s_1768_, lean_object* v_p_u2080_1769_, lean_object* v_p_u2081_1770_, lean_object* v_pos_1771_){
_start:
{
uint8_t v___x_1772_; 
v___x_1772_ = lean_nat_dec_le(v_p_u2080_1769_, v_p_u2081_1770_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = lean_unsigned_to_nat(0u);
v___x_1774_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1775_ = l_panic___redArg(v___x_1773_, v___x_1774_);
return v___x_1775_;
}
else
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_nat_add(v_p_u2080_1769_, v_pos_1771_);
return v___x_1776_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___boxed(lean_object* v_s_1777_, lean_object* v_p_u2080_1778_, lean_object* v_p_u2081_1779_, lean_object* v_pos_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_String_Pos_ofSlice_x21(v_s_1777_, v_p_u2080_1778_, v_p_u2081_1779_, v_pos_1780_);
lean_dec(v_pos_1780_);
lean_dec(v_p_u2081_1779_);
lean_dec(v_p_u2080_1778_);
lean_dec_ref(v_s_1777_);
return v_res_1781_;
}
}
static lean_object* _init_l_String_Slice_Pos_slice_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1784_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__1));
v___x_1785_ = lean_unsigned_to_nat(4u);
v___x_1786_ = lean_unsigned_to_nat(2643u);
v___x_1787_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__0));
v___x_1788_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1789_ = l_mkPanicMessageWithDecl(v___x_1788_, v___x_1787_, v___x_1786_, v___x_1785_, v___x_1784_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg(lean_object* v_pos_1790_, lean_object* v_p_u2080_1791_, lean_object* v_p_u2081_1792_){
_start:
{
uint8_t v___x_1797_; 
v___x_1797_ = lean_nat_dec_le(v_p_u2080_1791_, v_pos_1790_);
if (v___x_1797_ == 0)
{
goto v___jp_1793_;
}
else
{
uint8_t v___x_1798_; 
v___x_1798_ = lean_nat_dec_le(v_pos_1790_, v_p_u2081_1792_);
if (v___x_1798_ == 0)
{
goto v___jp_1793_;
}
else
{
lean_object* v___x_1799_; 
v___x_1799_ = lean_nat_sub(v_pos_1790_, v_p_u2080_1791_);
return v___x_1799_;
}
}
v___jp_1793_:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1794_ = lean_unsigned_to_nat(0u);
v___x_1795_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1796_ = l_panic___redArg(v___x_1794_, v___x_1795_);
return v___x_1796_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1800_, lean_object* v_p_u2080_1801_, lean_object* v_p_u2081_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_String_Slice_Pos_slice_x21___redArg(v_pos_1800_, v_p_u2080_1801_, v_p_u2081_1802_);
lean_dec(v_p_u2081_1802_);
lean_dec(v_p_u2080_1801_);
lean_dec(v_pos_1800_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21(lean_object* v_s_1804_, lean_object* v_pos_1805_, lean_object* v_p_u2080_1806_, lean_object* v_p_u2081_1807_){
_start:
{
uint8_t v___x_1812_; 
v___x_1812_ = lean_nat_dec_le(v_p_u2080_1806_, v_pos_1805_);
if (v___x_1812_ == 0)
{
goto v___jp_1808_;
}
else
{
uint8_t v___x_1813_; 
v___x_1813_ = lean_nat_dec_le(v_pos_1805_, v_p_u2081_1807_);
if (v___x_1813_ == 0)
{
goto v___jp_1808_;
}
else
{
lean_object* v___x_1814_; 
v___x_1814_ = lean_nat_sub(v_pos_1805_, v_p_u2080_1806_);
return v___x_1814_;
}
}
v___jp_1808_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = lean_unsigned_to_nat(0u);
v___x_1810_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1811_ = l_panic___redArg(v___x_1809_, v___x_1810_);
return v___x_1811_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___boxed(lean_object* v_s_1815_, lean_object* v_pos_1816_, lean_object* v_p_u2080_1817_, lean_object* v_p_u2081_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_String_Slice_Pos_slice_x21(v_s_1815_, v_pos_1816_, v_p_u2080_1817_, v_p_u2081_1818_);
lean_dec(v_p_u2081_1818_);
lean_dec(v_p_u2080_1817_);
lean_dec(v_pos_1816_);
lean_dec_ref(v_s_1815_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg(lean_object* v_pos_1820_, lean_object* v_p_u2080_1821_, lean_object* v_p_u2081_1822_){
_start:
{
uint8_t v___x_1827_; 
v___x_1827_ = lean_nat_dec_le(v_p_u2080_1821_, v_pos_1820_);
if (v___x_1827_ == 0)
{
goto v___jp_1823_;
}
else
{
uint8_t v___x_1828_; 
v___x_1828_ = lean_nat_dec_le(v_pos_1820_, v_p_u2081_1822_);
if (v___x_1828_ == 0)
{
goto v___jp_1823_;
}
else
{
lean_object* v___x_1829_; 
v___x_1829_ = lean_nat_sub(v_pos_1820_, v_p_u2080_1821_);
return v___x_1829_;
}
}
v___jp_1823_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1824_ = lean_unsigned_to_nat(0u);
v___x_1825_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1826_ = l_panic___redArg(v___x_1824_, v___x_1825_);
return v___x_1826_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1830_, lean_object* v_p_u2080_1831_, lean_object* v_p_u2081_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_String_Pos_slice_x21___redArg(v_pos_1830_, v_p_u2080_1831_, v_p_u2081_1832_);
lean_dec(v_p_u2081_1832_);
lean_dec(v_p_u2080_1831_);
lean_dec(v_pos_1830_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21(lean_object* v_s_1834_, lean_object* v_pos_1835_, lean_object* v_p_u2080_1836_, lean_object* v_p_u2081_1837_){
_start:
{
uint8_t v___x_1842_; 
v___x_1842_ = lean_nat_dec_le(v_p_u2080_1836_, v_pos_1835_);
if (v___x_1842_ == 0)
{
goto v___jp_1838_;
}
else
{
uint8_t v___x_1843_; 
v___x_1843_ = lean_nat_dec_le(v_pos_1835_, v_p_u2081_1837_);
if (v___x_1843_ == 0)
{
goto v___jp_1838_;
}
else
{
lean_object* v___x_1844_; 
v___x_1844_ = lean_nat_sub(v_pos_1835_, v_p_u2080_1836_);
return v___x_1844_;
}
}
v___jp_1838_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1839_ = lean_unsigned_to_nat(0u);
v___x_1840_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1841_ = l_panic___redArg(v___x_1839_, v___x_1840_);
return v___x_1841_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___boxed(lean_object* v_s_1845_, lean_object* v_pos_1846_, lean_object* v_p_u2080_1847_, lean_object* v_p_u2081_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_String_Pos_slice_x21(v_s_1845_, v_pos_1846_, v_p_u2080_1847_, v_p_u2081_1848_);
lean_dec(v_p_u2081_1848_);
lean_dec(v_p_u2080_1847_);
lean_dec(v_pos_1846_);
lean_dec_ref(v_s_1845_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract(lean_object* v_s_1850_, lean_object* v_p_u2080_1851_, lean_object* v_p_u2081_1852_){
_start:
{
lean_object* v_str_1853_; lean_object* v_startInclusive_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v_str_1853_ = lean_ctor_get(v_s_1850_, 0);
v_startInclusive_1854_ = lean_ctor_get(v_s_1850_, 1);
v___x_1855_ = lean_nat_add(v_startInclusive_1854_, v_p_u2080_1851_);
v___x_1856_ = lean_nat_add(v_startInclusive_1854_, v_p_u2081_1852_);
v___x_1857_ = lean_string_utf8_extract_fast(v_str_1853_, v___x_1855_, v___x_1856_);
lean_dec(v___x_1856_);
lean_dec(v___x_1855_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract___boxed(lean_object* v_s_1858_, lean_object* v_p_u2080_1859_, lean_object* v_p_u2081_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_String_Slice_extract(v_s_1858_, v_p_u2080_1859_, v_p_u2081_1860_);
lean_dec(v_p_u2081_1860_);
lean_dec(v_p_u2080_1859_);
lean_dec_ref(v_s_1858_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn(lean_object* v_s_1862_, lean_object* v_p_1863_, lean_object* v_n_1864_){
_start:
{
lean_object* v_zero_1865_; uint8_t v_isZero_1866_; 
v_zero_1865_ = lean_unsigned_to_nat(0u);
v_isZero_1866_ = lean_nat_dec_eq(v_n_1864_, v_zero_1865_);
if (v_isZero_1866_ == 1)
{
lean_dec(v_n_1864_);
return v_p_1863_;
}
else
{
lean_object* v_str_1867_; lean_object* v_startInclusive_1868_; lean_object* v_endExclusive_1869_; lean_object* v___x_1870_; uint8_t v_decide_1871_; 
v_str_1867_ = lean_ctor_get(v_s_1862_, 0);
v_startInclusive_1868_ = lean_ctor_get(v_s_1862_, 1);
v_endExclusive_1869_ = lean_ctor_get(v_s_1862_, 2);
v___x_1870_ = lean_nat_sub(v_endExclusive_1869_, v_startInclusive_1868_);
v_decide_1871_ = lean_nat_dec_eq(v_p_1863_, v___x_1870_);
lean_dec(v___x_1870_);
if (v_decide_1871_ == 0)
{
lean_object* v_one_1872_; lean_object* v_n_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v_one_1872_ = lean_unsigned_to_nat(1u);
v_n_1873_ = lean_nat_sub(v_n_1864_, v_one_1872_);
lean_dec(v_n_1864_);
v___x_1874_ = lean_nat_add(v_startInclusive_1868_, v_p_1863_);
lean_dec(v_p_1863_);
v___x_1875_ = lean_string_utf8_next_fast(v_str_1867_, v___x_1874_);
lean_dec(v___x_1874_);
v___x_1876_ = lean_nat_sub(v___x_1875_, v_startInclusive_1868_);
v_p_1863_ = v___x_1876_;
v_n_1864_ = v_n_1873_;
goto _start;
}
else
{
lean_dec(v_n_1864_);
return v_p_1863_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn___boxed(lean_object* v_s_1878_, lean_object* v_p_1879_, lean_object* v_n_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_String_Slice_Pos_nextn(v_s_1878_, v_p_1879_, v_n_1880_);
lean_dec_ref(v_s_1878_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_nextn(lean_object* v_s_1882_, lean_object* v_p_1883_, lean_object* v_n_1884_){
_start:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1885_ = lean_unsigned_to_nat(0u);
v___x_1886_ = lean_string_utf8_byte_size(v_s_1882_);
v___x_1887_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1887_, 0, v_s_1882_);
lean_ctor_set(v___x_1887_, 1, v___x_1885_);
lean_ctor_set(v___x_1887_, 2, v___x_1886_);
v___x_1888_ = l_String_Slice_Pos_nextn(v___x_1887_, v_p_1883_, v_n_1884_);
lean_dec_ref_known(v___x_1887_, 3);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(lean_object* v_n_1889_, lean_object* v_h__1_1890_, lean_object* v_h__2_1891_){
_start:
{
lean_object* v_zero_1892_; uint8_t v_isZero_1893_; 
v_zero_1892_ = lean_unsigned_to_nat(0u);
v_isZero_1893_ = lean_nat_dec_eq(v_n_1889_, v_zero_1892_);
if (v_isZero_1893_ == 1)
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
lean_dec(v_h__2_1891_);
v___x_1894_ = lean_box(0);
v___x_1895_ = lean_apply_1(v_h__1_1890_, v___x_1894_);
return v___x_1895_;
}
else
{
lean_object* v_one_1896_; lean_object* v_n_1897_; lean_object* v___x_1898_; 
lean_dec(v_h__1_1890_);
v_one_1896_ = lean_unsigned_to_nat(1u);
v_n_1897_ = lean_nat_sub(v_n_1889_, v_one_1896_);
v___x_1898_ = lean_apply_1(v_h__2_1891_, v_n_1897_);
return v___x_1898_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg___boxed(lean_object* v_n_1899_, lean_object* v_h__1_1900_, lean_object* v_h__2_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(v_n_1899_, v_h__1_1900_, v_h__2_1901_);
lean_dec(v_n_1899_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(lean_object* v_motive_1903_, lean_object* v_n_1904_, lean_object* v_h__1_1905_, lean_object* v_h__2_1906_){
_start:
{
lean_object* v_zero_1907_; uint8_t v_isZero_1908_; 
v_zero_1907_ = lean_unsigned_to_nat(0u);
v_isZero_1908_ = lean_nat_dec_eq(v_n_1904_, v_zero_1907_);
if (v_isZero_1908_ == 1)
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
lean_dec(v_h__2_1906_);
v___x_1909_ = lean_box(0);
v___x_1910_ = lean_apply_1(v_h__1_1905_, v___x_1909_);
return v___x_1910_;
}
else
{
lean_object* v_one_1911_; lean_object* v_n_1912_; lean_object* v___x_1913_; 
lean_dec(v_h__1_1905_);
v_one_1911_ = lean_unsigned_to_nat(1u);
v_n_1912_ = lean_nat_sub(v_n_1904_, v_one_1911_);
v___x_1913_ = lean_apply_1(v_h__2_1906_, v_n_1912_);
return v___x_1913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___boxed(lean_object* v_motive_1914_, lean_object* v_n_1915_, lean_object* v_h__1_1916_, lean_object* v_h__2_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(v_motive_1914_, v_n_1915_, v_h__1_1916_, v_h__2_1917_);
lean_dec(v_n_1915_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next___boxed(lean_object* v_s_1921_, lean_object* v_p_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = lean_string_utf8_next(v_s_1921_, v_p_1922_);
lean_dec(v_p_1922_);
lean_dec_ref(v_s_1921_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_String_next___boxed(lean_object* v_s_1926_, lean_object* v_p_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = lean_string_utf8_next(v_s_1926_, v_p_1927_);
lean_dec(v_p_1927_);
lean_dec_ref(v_s_1926_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux(lean_object* v_x_1929_, lean_object* v_x_1930_, lean_object* v_x_1931_){
_start:
{
if (lean_obj_tag(v_x_1929_) == 0)
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
lean_dec(v_x_1930_);
v___x_1932_ = lean_unsigned_to_nat(1u);
v___x_1933_ = lean_nat_sub(v_x_1931_, v___x_1932_);
return v___x_1933_;
}
else
{
lean_object* v_head_1934_; lean_object* v_tail_1935_; lean_object* v___y_1937_; uint32_t v___x_1941_; uint32_t v___x_1942_; uint8_t v___x_1943_; 
v_head_1934_ = lean_ctor_get(v_x_1929_, 0);
v_tail_1935_ = lean_ctor_get(v_x_1929_, 1);
v___x_1941_ = 127;
v___x_1942_ = lean_unbox_uint32(v_head_1934_);
v___x_1943_ = lean_uint32_dec_le(v___x_1942_, v___x_1941_);
if (v___x_1943_ == 0)
{
uint32_t v___x_1944_; uint32_t v___x_1945_; uint8_t v___x_1946_; 
v___x_1944_ = 2047;
v___x_1945_ = lean_unbox_uint32(v_head_1934_);
v___x_1946_ = lean_uint32_dec_le(v___x_1945_, v___x_1944_);
if (v___x_1946_ == 0)
{
uint32_t v___x_1947_; uint32_t v___x_1948_; uint8_t v___x_1949_; 
v___x_1947_ = 65535;
v___x_1948_ = lean_unbox_uint32(v_head_1934_);
v___x_1949_ = lean_uint32_dec_le(v___x_1948_, v___x_1947_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; 
v___x_1950_ = lean_unsigned_to_nat(4u);
v___y_1937_ = v___x_1950_;
goto v___jp_1936_;
}
else
{
lean_object* v___x_1951_; 
v___x_1951_ = lean_unsigned_to_nat(3u);
v___y_1937_ = v___x_1951_;
goto v___jp_1936_;
}
}
else
{
lean_object* v___x_1952_; 
v___x_1952_ = lean_unsigned_to_nat(2u);
v___y_1937_ = v___x_1952_;
goto v___jp_1936_;
}
}
else
{
lean_object* v___x_1953_; 
v___x_1953_ = lean_unsigned_to_nat(1u);
v___y_1937_ = v___x_1953_;
goto v___jp_1936_;
}
v___jp_1936_:
{
lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___x_1938_ = lean_nat_add(v_x_1930_, v___y_1937_);
v___x_1939_ = lean_nat_dec_le(v_x_1931_, v___x_1938_);
if (v___x_1939_ == 0)
{
lean_dec(v_x_1930_);
v_x_1929_ = v_tail_1935_;
v_x_1930_ = v___x_1938_;
goto _start;
}
else
{
lean_dec(v___x_1938_);
return v_x_1930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux___boxed(lean_object* v_x_1954_, lean_object* v_x_1955_, lean_object* v_x_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_String_Pos_Raw_utf8PrevAux(v_x_1954_, v_x_1955_, v_x_1956_);
lean_dec(v_x_1956_);
lean_dec(v_x_1954_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux(lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v___x_1961_; 
v___x_1961_ = l_String_Pos_Raw_utf8PrevAux(v_a_1958_, v_a_1959_, v_a_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux___boxed(lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_String_utf8PrevAux(v_a_1962_, v_a_1963_, v_a_1964_);
lean_dec(v_a_1964_);
lean_dec(v_a_1962_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_prev___boxed(lean_object* v_a_00___x40___internal___hyg_1968_, lean_object* v_a_00___x40___internal___hyg_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_1968_, v_a_00___x40___internal___hyg_1969_);
lean_dec(v_a_00___x40___internal___hyg_1969_);
lean_dec_ref(v_a_00___x40___internal___hyg_1968_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_String_prev___boxed(lean_object* v_a_00___x40___internal___hyg_1973_, lean_object* v_a_00___x40___internal___hyg_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_1973_, v_a_00___x40___internal___hyg_1974_);
lean_dec(v_a_00___x40___internal___hyg_1974_);
lean_dec_ref(v_a_00___x40___internal___hyg_1973_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_1978_, lean_object* v_a_00___x40___internal___hyg_1979_){
_start:
{
uint8_t v_res_1980_; lean_object* v_r_1981_; 
v_res_1980_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_1978_, v_a_00___x40___internal___hyg_1979_);
lean_dec(v_a_00___x40___internal___hyg_1979_);
lean_dec_ref(v_a_00___x40___internal___hyg_1978_);
v_r_1981_ = lean_box(v_res_1980_);
return v_r_1981_;
}
}
LEAN_EXPORT lean_object* l_String_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_1984_, lean_object* v_a_00___x40___internal___hyg_1985_){
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
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x27___boxed(lean_object* v_s_1991_, lean_object* v_p_1992_, lean_object* v_h_1993_){
_start:
{
uint32_t v_res_1994_; lean_object* v_r_1995_; 
v_res_1994_ = lean_string_utf8_get_fast(v_s_1991_, v_p_1992_);
lean_dec(v_p_1992_);
lean_dec_ref(v_s_1991_);
v_r_1995_ = lean_box_uint32(v_res_1994_);
return v_r_1995_;
}
}
LEAN_EXPORT lean_object* l_String_get_x27___boxed(lean_object* v_s_1999_, lean_object* v_p_2000_, lean_object* v_h_2001_){
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
LEAN_EXPORT lean_object* l_String_Pos_Raw_next_x27___boxed(lean_object* v_s_2007_, lean_object* v_p_2008_, lean_object* v_h_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = lean_string_utf8_next_fast(v_s_2007_, v_p_2008_);
lean_dec(v_p_2008_);
lean_dec_ref(v_s_2007_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_String_next_x27___boxed(lean_object* v_s_2014_, lean_object* v_p_2015_, lean_object* v_h_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = lean_string_utf8_next_fast(v_s_2014_, v_p_2015_);
lean_dec(v_p_2015_);
lean_dec_ref(v_s_2014_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop(lean_object* v_a_2018_, lean_object* v_b_2019_, lean_object* v_stopPos_2020_, lean_object* v_i_2021_){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2022_ = lean_unsigned_to_nat(1u);
v___x_2023_ = lean_nat_add(v_i_2021_, v___x_2022_);
v___x_2024_ = lean_nat_dec_le(v___x_2023_, v_stopPos_2020_);
lean_dec(v___x_2023_);
if (v___x_2024_ == 0)
{
return v_i_2021_;
}
else
{
uint32_t v___x_2025_; uint32_t v___x_2026_; uint8_t v___x_2027_; 
v___x_2025_ = lean_string_utf8_get(v_a_2018_, v_i_2021_);
v___x_2026_ = lean_string_utf8_get(v_b_2019_, v_i_2021_);
v___x_2027_ = lean_uint32_dec_eq(v___x_2025_, v___x_2026_);
if (v___x_2027_ == 0)
{
return v_i_2021_;
}
else
{
lean_object* v___x_2028_; 
v___x_2028_ = lean_string_utf8_next(v_a_2018_, v_i_2021_);
lean_dec(v_i_2021_);
v_i_2021_ = v___x_2028_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop___boxed(lean_object* v_a_2030_, lean_object* v_b_2031_, lean_object* v_stopPos_2032_, lean_object* v_i_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_String_firstDiffPos_loop(v_a_2030_, v_b_2031_, v_stopPos_2032_, v_i_2033_);
lean_dec(v_stopPos_2032_);
lean_dec_ref(v_b_2031_);
lean_dec_ref(v_a_2030_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos(lean_object* v_a_2035_, lean_object* v_b_2036_){
_start:
{
lean_object* v___y_2038_; lean_object* v___x_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; 
v___x_2041_ = lean_string_utf8_byte_size(v_a_2035_);
v___x_2042_ = lean_string_utf8_byte_size(v_b_2036_);
v___x_2043_ = lean_nat_dec_le(v___x_2041_, v___x_2042_);
if (v___x_2043_ == 0)
{
v___y_2038_ = v___x_2042_;
goto v___jp_2037_;
}
else
{
v___y_2038_ = v___x_2041_;
goto v___jp_2037_;
}
v___jp_2037_:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2039_ = lean_unsigned_to_nat(0u);
v___x_2040_ = l_String_firstDiffPos_loop(v_a_2035_, v_b_2036_, v___y_2038_, v___x_2039_);
lean_dec(v___y_2038_);
return v___x_2040_;
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos___boxed(lean_object* v_a_2044_, lean_object* v_b_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_String_firstDiffPos(v_a_2044_, v_b_2045_);
lean_dec_ref(v_b_2045_);
lean_dec_ref(v_a_2044_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082(lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_){
_start:
{
if (lean_obj_tag(v_a_2047_) == 0)
{
return v_a_2047_;
}
else
{
lean_object* v_head_2050_; lean_object* v_tail_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2077_; 
v_head_2050_ = lean_ctor_get(v_a_2047_, 0);
v_tail_2051_ = lean_ctor_get(v_a_2047_, 1);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_a_2047_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2053_ = v_a_2047_;
v_isShared_2054_ = v_isSharedCheck_2077_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_tail_2051_);
lean_inc(v_head_2050_);
lean_dec(v_a_2047_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2077_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___y_2056_; uint8_t v_decide_2062_; 
v_decide_2062_ = lean_nat_dec_eq(v_a_2048_, v_a_2049_);
if (v_decide_2062_ == 0)
{
uint32_t v___x_2063_; uint32_t v___x_2064_; uint8_t v___x_2065_; 
v___x_2063_ = 127;
v___x_2064_ = lean_unbox_uint32(v_head_2050_);
v___x_2065_ = lean_uint32_dec_le(v___x_2064_, v___x_2063_);
if (v___x_2065_ == 0)
{
uint32_t v___x_2066_; uint32_t v___x_2067_; uint8_t v___x_2068_; 
v___x_2066_ = 2047;
v___x_2067_ = lean_unbox_uint32(v_head_2050_);
v___x_2068_ = lean_uint32_dec_le(v___x_2067_, v___x_2066_);
if (v___x_2068_ == 0)
{
uint32_t v___x_2069_; uint32_t v___x_2070_; uint8_t v___x_2071_; 
v___x_2069_ = 65535;
v___x_2070_ = lean_unbox_uint32(v_head_2050_);
v___x_2071_ = lean_uint32_dec_le(v___x_2070_, v___x_2069_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2072_; 
v___x_2072_ = lean_unsigned_to_nat(4u);
v___y_2056_ = v___x_2072_;
goto v___jp_2055_;
}
else
{
lean_object* v___x_2073_; 
v___x_2073_ = lean_unsigned_to_nat(3u);
v___y_2056_ = v___x_2073_;
goto v___jp_2055_;
}
}
else
{
lean_object* v___x_2074_; 
v___x_2074_ = lean_unsigned_to_nat(2u);
v___y_2056_ = v___x_2074_;
goto v___jp_2055_;
}
}
else
{
lean_object* v___x_2075_; 
v___x_2075_ = lean_unsigned_to_nat(1u);
v___y_2056_ = v___x_2075_;
goto v___jp_2055_;
}
}
else
{
lean_object* v___x_2076_; 
lean_del_object(v___x_2053_);
lean_dec(v_tail_2051_);
lean_dec(v_head_2050_);
v___x_2076_ = lean_box(0);
return v___x_2076_;
}
v___jp_2055_:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2060_; 
v___x_2057_ = lean_nat_add(v_a_2048_, v___y_2056_);
v___x_2058_ = l_String_Pos_Raw_extract_go_u2082(v_tail_2051_, v___x_2057_, v_a_2049_);
lean_dec(v___x_2057_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 1, v___x_2058_);
v___x_2060_ = v___x_2053_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_head_2050_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082___boxed(lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_String_Pos_Raw_extract_go_u2082(v_a_2078_, v_a_2079_, v_a_2080_);
lean_dec(v_a_2080_);
lean_dec(v_a_2079_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081(lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
if (lean_obj_tag(v_a_2082_) == 0)
{
lean_dec(v_a_2083_);
return v_a_2082_;
}
else
{
lean_object* v_head_2086_; lean_object* v_tail_2087_; lean_object* v___y_2089_; uint8_t v_decide_2092_; 
v_head_2086_ = lean_ctor_get(v_a_2082_, 0);
v_tail_2087_ = lean_ctor_get(v_a_2082_, 1);
v_decide_2092_ = lean_nat_dec_eq(v_a_2083_, v_a_2084_);
if (v_decide_2092_ == 0)
{
uint32_t v___x_2093_; uint32_t v___x_2094_; uint8_t v___x_2095_; 
lean_inc(v_tail_2087_);
lean_inc(v_head_2086_);
lean_dec_ref_known(v_a_2082_, 2);
v___x_2093_ = 127;
v___x_2094_ = lean_unbox_uint32(v_head_2086_);
v___x_2095_ = lean_uint32_dec_le(v___x_2094_, v___x_2093_);
if (v___x_2095_ == 0)
{
uint32_t v___x_2096_; uint32_t v___x_2097_; uint8_t v___x_2098_; 
v___x_2096_ = 2047;
v___x_2097_ = lean_unbox_uint32(v_head_2086_);
v___x_2098_ = lean_uint32_dec_le(v___x_2097_, v___x_2096_);
if (v___x_2098_ == 0)
{
uint32_t v___x_2099_; uint32_t v___x_2100_; uint8_t v___x_2101_; 
v___x_2099_ = 65535;
v___x_2100_ = lean_unbox_uint32(v_head_2086_);
lean_dec(v_head_2086_);
v___x_2101_ = lean_uint32_dec_le(v___x_2100_, v___x_2099_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2102_; 
v___x_2102_ = lean_unsigned_to_nat(4u);
v___y_2089_ = v___x_2102_;
goto v___jp_2088_;
}
else
{
lean_object* v___x_2103_; 
v___x_2103_ = lean_unsigned_to_nat(3u);
v___y_2089_ = v___x_2103_;
goto v___jp_2088_;
}
}
else
{
lean_object* v___x_2104_; 
lean_dec(v_head_2086_);
v___x_2104_ = lean_unsigned_to_nat(2u);
v___y_2089_ = v___x_2104_;
goto v___jp_2088_;
}
}
else
{
lean_object* v___x_2105_; 
lean_dec(v_head_2086_);
v___x_2105_ = lean_unsigned_to_nat(1u);
v___y_2089_ = v___x_2105_;
goto v___jp_2088_;
}
}
else
{
lean_object* v___x_2106_; 
v___x_2106_ = l_String_Pos_Raw_extract_go_u2082(v_a_2082_, v_a_2083_, v_a_2085_);
lean_dec(v_a_2083_);
return v___x_2106_;
}
v___jp_2088_:
{
lean_object* v___x_2090_; 
v___x_2090_ = lean_nat_add(v_a_2083_, v___y_2089_);
lean_dec(v_a_2083_);
v_a_2082_ = v_tail_2087_;
v_a_2083_ = v___x_2090_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081___boxed(lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_String_Pos_Raw_extract_go_u2081(v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
lean_dec(v_a_2110_);
lean_dec(v_a_2109_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract___boxed(lean_object* v_a_00___x40___internal___hyg_2115_, lean_object* v_a_00___x40___internal___hyg_2116_, lean_object* v_a_00___x40___internal___hyg_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = lean_string_utf8_extract(v_a_00___x40___internal___hyg_2115_, v_a_00___x40___internal___hyg_2116_, v_a_00___x40___internal___hyg_2117_);
lean_dec(v_a_00___x40___internal___hyg_2117_);
lean_dec(v_a_00___x40___internal___hyg_2116_);
lean_dec_ref(v_a_00___x40___internal___hyg_2115_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux(lean_object* v_s_2119_, lean_object* v_pos_2120_, lean_object* v_i_2121_, lean_object* v_offset_2122_){
_start:
{
uint8_t v___x_2123_; 
v___x_2123_ = lean_nat_dec_le(v_pos_2120_, v_i_2121_);
if (v___x_2123_ == 0)
{
uint8_t v___x_2124_; 
v___x_2124_ = lean_string_utf8_at_end(v_s_2119_, v_i_2121_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2125_ = lean_string_utf8_next(v_s_2119_, v_i_2121_);
lean_dec(v_i_2121_);
v___x_2126_ = lean_unsigned_to_nat(1u);
v___x_2127_ = lean_nat_add(v_offset_2122_, v___x_2126_);
lean_dec(v_offset_2122_);
v_i_2121_ = v___x_2125_;
v_offset_2122_ = v___x_2127_;
goto _start;
}
else
{
lean_dec(v_i_2121_);
return v_offset_2122_;
}
}
else
{
lean_dec(v_i_2121_);
return v_offset_2122_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux___boxed(lean_object* v_s_2129_, lean_object* v_pos_2130_, lean_object* v_i_2131_, lean_object* v_offset_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2129_, v_pos_2130_, v_i_2131_, v_offset_2132_);
lean_dec(v_pos_2130_);
lean_dec_ref(v_s_2129_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos(lean_object* v_s_2134_, lean_object* v_pos_2135_){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = lean_unsigned_to_nat(0u);
v___x_2137_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2134_, v_pos_2135_, v___x_2136_, v___x_2136_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos___boxed(lean_object* v_s_2138_, lean_object* v_pos_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_String_Pos_Raw_offsetOfPos(v_s_2138_, v_pos_2139_);
lean_dec(v_pos_2139_);
lean_dec_ref(v_s_2138_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos(lean_object* v_s_2141_, lean_object* v_pos_2142_){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = lean_unsigned_to_nat(0u);
v___x_2144_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2141_, v_pos_2142_, v___x_2143_, v___x_2143_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos___boxed(lean_object* v_s_2145_, lean_object* v_pos_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_String_offsetOfPos(v_s_2145_, v_pos_2146_);
lean_dec(v_pos_2146_);
lean_dec_ref(v_s_2145_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* lean_string_offsetofpos(lean_object* v_s_2148_, lean_object* v_pos_2149_){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2150_ = lean_unsigned_to_nat(0u);
v___x_2151_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2148_, v_pos_2149_, v___x_2150_, v___x_2150_);
lean_dec(v_pos_2149_);
lean_dec_ref(v_s_2148_);
return v___x_2151_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(lean_object* v_s1_2152_, lean_object* v_s2_2153_, lean_object* v_off1_2154_, lean_object* v_off2_2155_, lean_object* v_stop1_2156_){
_start:
{
lean_object* v___y_2158_; lean_object* v___y_2159_; uint8_t v___x_2162_; 
v___x_2162_ = lean_nat_dec_lt(v_off1_2154_, v_stop1_2156_);
if (v___x_2162_ == 0)
{
uint8_t v___x_2163_; 
lean_dec(v_off2_2155_);
lean_dec(v_off1_2154_);
v___x_2163_ = 1;
return v___x_2163_;
}
else
{
uint32_t v_c_u2081_2164_; uint32_t v_c_u2082_2165_; lean_object* v___y_2167_; uint8_t v___x_2179_; 
v_c_u2081_2164_ = lean_string_utf8_get(v_s1_2152_, v_off1_2154_);
v_c_u2082_2165_ = lean_string_utf8_get(v_s2_2153_, v_off2_2155_);
v___x_2179_ = lean_uint32_dec_eq(v_c_u2081_2164_, v_c_u2082_2165_);
if (v___x_2179_ == 0)
{
lean_dec(v_off2_2155_);
lean_dec(v_off1_2154_);
return v___x_2179_;
}
else
{
uint32_t v___x_2180_; uint8_t v___x_2181_; 
v___x_2180_ = 127;
v___x_2181_ = lean_uint32_dec_le(v_c_u2081_2164_, v___x_2180_);
if (v___x_2181_ == 0)
{
uint32_t v___x_2182_; uint8_t v___x_2183_; 
v___x_2182_ = 2047;
v___x_2183_ = lean_uint32_dec_le(v_c_u2081_2164_, v___x_2182_);
if (v___x_2183_ == 0)
{
uint32_t v___x_2184_; uint8_t v___x_2185_; 
v___x_2184_ = 65535;
v___x_2185_ = lean_uint32_dec_le(v_c_u2081_2164_, v___x_2184_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; 
v___x_2186_ = lean_unsigned_to_nat(4u);
v___y_2167_ = v___x_2186_;
goto v___jp_2166_;
}
else
{
lean_object* v___x_2187_; 
v___x_2187_ = lean_unsigned_to_nat(3u);
v___y_2167_ = v___x_2187_;
goto v___jp_2166_;
}
}
else
{
lean_object* v___x_2188_; 
v___x_2188_ = lean_unsigned_to_nat(2u);
v___y_2167_ = v___x_2188_;
goto v___jp_2166_;
}
}
else
{
lean_object* v___x_2189_; 
v___x_2189_ = lean_unsigned_to_nat(1u);
v___y_2167_ = v___x_2189_;
goto v___jp_2166_;
}
}
v___jp_2166_:
{
lean_object* v___x_2168_; uint32_t v___x_2169_; uint8_t v___x_2170_; 
v___x_2168_ = lean_nat_add(v_off1_2154_, v___y_2167_);
lean_dec(v_off1_2154_);
v___x_2169_ = 127;
v___x_2170_ = lean_uint32_dec_le(v_c_u2082_2165_, v___x_2169_);
if (v___x_2170_ == 0)
{
uint32_t v___x_2171_; uint8_t v___x_2172_; 
v___x_2171_ = 2047;
v___x_2172_ = lean_uint32_dec_le(v_c_u2082_2165_, v___x_2171_);
if (v___x_2172_ == 0)
{
uint32_t v___x_2173_; uint8_t v___x_2174_; 
v___x_2173_ = 65535;
v___x_2174_ = lean_uint32_dec_le(v_c_u2082_2165_, v___x_2173_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2175_; 
v___x_2175_ = lean_unsigned_to_nat(4u);
v___y_2158_ = v___x_2168_;
v___y_2159_ = v___x_2175_;
goto v___jp_2157_;
}
else
{
lean_object* v___x_2176_; 
v___x_2176_ = lean_unsigned_to_nat(3u);
v___y_2158_ = v___x_2168_;
v___y_2159_ = v___x_2176_;
goto v___jp_2157_;
}
}
else
{
lean_object* v___x_2177_; 
v___x_2177_ = lean_unsigned_to_nat(2u);
v___y_2158_ = v___x_2168_;
v___y_2159_ = v___x_2177_;
goto v___jp_2157_;
}
}
else
{
lean_object* v___x_2178_; 
v___x_2178_ = lean_unsigned_to_nat(1u);
v___y_2158_ = v___x_2168_;
v___y_2159_ = v___x_2178_;
goto v___jp_2157_;
}
}
}
v___jp_2157_:
{
lean_object* v___x_2160_; 
v___x_2160_ = lean_nat_add(v_off2_2155_, v___y_2159_);
lean_dec(v_off2_2155_);
v_off1_2154_ = v___y_2158_;
v_off2_2155_ = v___x_2160_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop___boxed(lean_object* v_s1_2190_, lean_object* v_s2_2191_, lean_object* v_off1_2192_, lean_object* v_off2_2193_, lean_object* v_stop1_2194_){
_start:
{
uint8_t v_res_2195_; lean_object* v_r_2196_; 
v_res_2195_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2190_, v_s2_2191_, v_off1_2192_, v_off2_2193_, v_stop1_2194_);
lean_dec(v_stop1_2194_);
lean_dec_ref(v_s2_2191_);
lean_dec_ref(v_s1_2190_);
v_r_2196_ = lean_box(v_res_2195_);
return v_r_2196_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_substrEq(lean_object* v_s1_2197_, lean_object* v_pos1_2198_, lean_object* v_s2_2199_, lean_object* v_pos2_2200_, lean_object* v_sz_2201_){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v___x_2202_ = lean_nat_add(v_pos1_2198_, v_sz_2201_);
v___x_2203_ = lean_string_utf8_byte_size(v_s1_2197_);
v___x_2204_ = lean_nat_dec_le(v___x_2202_, v___x_2203_);
if (v___x_2204_ == 0)
{
lean_dec(v___x_2202_);
lean_dec(v_pos2_2200_);
lean_dec(v_pos1_2198_);
return v___x_2204_;
}
else
{
lean_object* v___x_2205_; lean_object* v___x_2206_; uint8_t v___x_2207_; 
v___x_2205_ = lean_nat_add(v_pos2_2200_, v_sz_2201_);
v___x_2206_ = lean_string_utf8_byte_size(v_s2_2199_);
v___x_2207_ = lean_nat_dec_le(v___x_2205_, v___x_2206_);
lean_dec(v___x_2205_);
if (v___x_2207_ == 0)
{
lean_dec(v___x_2202_);
lean_dec(v_pos2_2200_);
lean_dec(v_pos1_2198_);
return v___x_2207_;
}
else
{
uint8_t v___x_2208_; 
v___x_2208_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2197_, v_s2_2199_, v_pos1_2198_, v_pos2_2200_, v___x_2202_);
lean_dec(v___x_2202_);
return v___x_2208_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_substrEq___boxed(lean_object* v_s1_2209_, lean_object* v_pos1_2210_, lean_object* v_s2_2211_, lean_object* v_pos2_2212_, lean_object* v_sz_2213_){
_start:
{
uint8_t v_res_2214_; lean_object* v_r_2215_; 
v_res_2214_ = l_String_Pos_Raw_substrEq(v_s1_2209_, v_pos1_2210_, v_s2_2211_, v_pos2_2212_, v_sz_2213_);
lean_dec(v_sz_2213_);
lean_dec_ref(v_s2_2211_);
lean_dec_ref(v_s1_2209_);
v_r_2215_ = lean_box(v_res_2214_);
return v_r_2215_;
}
}
LEAN_EXPORT uint8_t l_String_substrEq(lean_object* v_s1_2216_, lean_object* v_pos1_2217_, lean_object* v_s2_2218_, lean_object* v_pos2_2219_, lean_object* v_sz_2220_){
_start:
{
uint8_t v___x_2221_; 
v___x_2221_ = l_String_Pos_Raw_substrEq(v_s1_2216_, v_pos1_2217_, v_s2_2218_, v_pos2_2219_, v_sz_2220_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_String_substrEq___boxed(lean_object* v_s1_2222_, lean_object* v_pos1_2223_, lean_object* v_s2_2224_, lean_object* v_pos2_2225_, lean_object* v_sz_2226_){
_start:
{
uint8_t v_res_2227_; lean_object* v_r_2228_; 
v_res_2227_ = l_String_substrEq(v_s1_2222_, v_pos1_2223_, v_s2_2224_, v_pos2_2225_, v_sz_2226_);
lean_dec(v_sz_2226_);
lean_dec_ref(v_s2_2224_);
lean_dec_ref(v_s1_2222_);
v_r_2228_ = lean_box(v_res_2227_);
return v_r_2228_;
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
