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
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_land(uint8_t, uint8_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
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
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_String_length___boxed(lean_object*);
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_x_147_);
v___x_152_ = lean_apply_2(v_h__2_149_, v_val_151_, lean_box(0));
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__1_splitter(lean_object* v_motive_153_, lean_object* v_x_154_, lean_object* v_h__1_155_, lean_object* v_h__2_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__1_splitter___redArg(v_x_154_, v_h__1_155_, v_h__2_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f(lean_object* v_b_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = ((lean_object*)(l_ByteArray_utf8Decode_x3f___closed__0));
v___x_163_ = l_ByteArray_utf8Decode_x3f_go___redArg(v_b_160_, v___x_161_, v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f___boxed(lean_object* v_b_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_ByteArray_utf8Decode_x3f(v_b_164_);
lean_dec_ref(v_b_164_);
return v_res_165_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8_go___redArg(lean_object* v_b_166_, lean_object* v_i_167_){
_start:
{
lean_object* v___y_169_; uint8_t v___y_173_; lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_190_ = lean_byte_array_size(v_b_166_);
v___x_191_ = lean_nat_dec_lt(v_i_167_, v___x_190_);
if (v___x_191_ == 0)
{
uint8_t v___x_192_; 
lean_dec(v_i_167_);
v___x_192_ = 1;
return v___x_192_;
}
else
{
if (v___x_191_ == 0)
{
lean_dec(v_i_167_);
return v___x_191_;
}
else
{
uint8_t v___x_193_; uint8_t v___x_194_; uint8_t v___x_195_; uint8_t v___x_196_; uint8_t v___x_197_; 
v___x_193_ = lean_byte_array_fget(v_b_166_, v_i_167_);
v___x_194_ = 128;
v___x_195_ = lean_uint8_land(v___x_193_, v___x_194_);
v___x_196_ = 0;
v___x_197_ = lean_uint8_dec_eq(v___x_195_, v___x_196_);
if (v___x_197_ == 0)
{
uint8_t v___x_198_; uint8_t v___x_199_; uint8_t v___x_200_; uint8_t v___x_201_; 
v___x_198_ = 224;
v___x_199_ = lean_uint8_land(v___x_193_, v___x_198_);
v___x_200_ = 192;
v___x_201_ = lean_uint8_dec_eq(v___x_199_, v___x_200_);
if (v___x_201_ == 0)
{
uint8_t v___x_202_; uint8_t v___x_203_; uint8_t v___x_204_; 
v___x_202_ = 240;
v___x_203_ = lean_uint8_land(v___x_193_, v___x_202_);
v___x_204_ = lean_uint8_dec_eq(v___x_203_, v___x_198_);
if (v___x_204_ == 0)
{
uint8_t v___x_205_; uint8_t v___x_206_; uint8_t v___x_207_; 
v___x_205_ = 248;
v___x_206_ = lean_uint8_land(v___x_193_, v___x_205_);
v___x_207_ = lean_uint8_dec_eq(v___x_206_, v___x_202_);
if (v___x_207_ == 0)
{
v___y_173_ = v___x_207_;
goto v___jp_172_;
}
else
{
lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_208_ = lean_unsigned_to_nat(3u);
v___x_209_ = lean_nat_add(v_i_167_, v___x_208_);
v___x_210_ = lean_nat_dec_lt(v___x_209_, v___x_190_);
if (v___x_210_ == 0)
{
lean_dec(v___x_209_);
v___y_173_ = v___x_204_;
goto v___jp_172_;
}
else
{
lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; uint8_t v___x_214_; uint8_t v___x_215_; 
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_add(v_i_167_, v___x_211_);
v___x_213_ = lean_byte_array_fget(v_b_166_, v___x_212_);
lean_dec(v___x_212_);
v___x_214_ = lean_uint8_land(v___x_213_, v___x_200_);
v___x_215_ = lean_uint8_dec_eq(v___x_214_, v___x_194_);
if (v___x_215_ == 0)
{
lean_dec(v___x_209_);
v___y_173_ = v___x_215_;
goto v___jp_172_;
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; uint8_t v___x_219_; uint8_t v___x_220_; 
v___x_216_ = lean_unsigned_to_nat(2u);
v___x_217_ = lean_nat_add(v_i_167_, v___x_216_);
v___x_218_ = lean_byte_array_fget(v_b_166_, v___x_217_);
lean_dec(v___x_217_);
v___x_219_ = lean_uint8_land(v___x_218_, v___x_200_);
v___x_220_ = lean_uint8_dec_eq(v___x_219_, v___x_194_);
if (v___x_220_ == 0)
{
lean_dec(v___x_209_);
v___y_173_ = v___x_220_;
goto v___jp_172_;
}
else
{
uint8_t v___x_221_; uint8_t v___x_222_; uint8_t v___x_223_; 
v___x_221_ = lean_byte_array_fget(v_b_166_, v___x_209_);
lean_dec(v___x_209_);
v___x_222_ = lean_uint8_land(v___x_221_, v___x_200_);
v___x_223_ = lean_uint8_dec_eq(v___x_222_, v___x_194_);
if (v___x_223_ == 0)
{
v___y_173_ = v___x_223_;
goto v___jp_172_;
}
else
{
uint8_t v___x_224_; uint8_t v_b_u2080_225_; uint8_t v___x_226_; uint8_t v_b_u2081_227_; uint8_t v_b_u2082_228_; uint8_t v_b_u2083_229_; uint32_t v___x_230_; uint32_t v___x_231_; uint32_t v___x_232_; uint32_t v___x_233_; uint32_t v___x_234_; uint32_t v___x_235_; uint32_t v___x_236_; uint32_t v___x_237_; uint32_t v___x_238_; uint32_t v___x_239_; uint32_t v___x_240_; uint32_t v___x_241_; uint32_t v_r_242_; uint32_t v___x_243_; uint8_t v___x_244_; 
v___x_224_ = 7;
v_b_u2080_225_ = lean_uint8_land(v___x_193_, v___x_224_);
v___x_226_ = 63;
v_b_u2081_227_ = lean_uint8_land(v___x_213_, v___x_226_);
v_b_u2082_228_ = lean_uint8_land(v___x_218_, v___x_226_);
v_b_u2083_229_ = lean_uint8_land(v___x_221_, v___x_226_);
v___x_230_ = lean_uint8_to_uint32(v_b_u2080_225_);
v___x_231_ = 18;
v___x_232_ = lean_uint32_shift_left(v___x_230_, v___x_231_);
v___x_233_ = lean_uint8_to_uint32(v_b_u2081_227_);
v___x_234_ = 12;
v___x_235_ = lean_uint32_shift_left(v___x_233_, v___x_234_);
v___x_236_ = lean_uint32_lor(v___x_232_, v___x_235_);
v___x_237_ = lean_uint8_to_uint32(v_b_u2082_228_);
v___x_238_ = 6;
v___x_239_ = lean_uint32_shift_left(v___x_237_, v___x_238_);
v___x_240_ = lean_uint32_lor(v___x_236_, v___x_239_);
v___x_241_ = lean_uint8_to_uint32(v_b_u2083_229_);
v_r_242_ = lean_uint32_lor(v___x_240_, v___x_241_);
v___x_243_ = 65536;
v___x_244_ = lean_uint32_dec_le(v___x_243_, v_r_242_);
if (v___x_244_ == 0)
{
v___y_173_ = v___x_204_;
goto v___jp_172_;
}
else
{
uint32_t v___x_245_; uint8_t v___x_246_; 
v___x_245_ = 1114111;
v___x_246_ = lean_uint32_dec_le(v_r_242_, v___x_245_);
if (v___x_246_ == 0)
{
v___y_173_ = v___x_204_;
goto v___jp_172_;
}
else
{
v___y_173_ = v___x_223_;
goto v___jp_172_;
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
lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_247_ = lean_unsigned_to_nat(2u);
v___x_248_ = lean_nat_add(v_i_167_, v___x_247_);
v___x_249_ = lean_nat_dec_lt(v___x_248_, v___x_190_);
if (v___x_249_ == 0)
{
lean_dec(v___x_248_);
v___y_173_ = v___x_201_;
goto v___jp_172_;
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; uint8_t v___x_253_; uint8_t v___x_254_; 
v___x_250_ = lean_unsigned_to_nat(1u);
v___x_251_ = lean_nat_add(v_i_167_, v___x_250_);
v___x_252_ = lean_byte_array_fget(v_b_166_, v___x_251_);
lean_dec(v___x_251_);
v___x_253_ = lean_uint8_land(v___x_252_, v___x_200_);
v___x_254_ = lean_uint8_dec_eq(v___x_253_, v___x_194_);
if (v___x_254_ == 0)
{
lean_dec(v___x_248_);
v___y_173_ = v___x_254_;
goto v___jp_172_;
}
else
{
uint8_t v___x_255_; uint8_t v___x_256_; uint8_t v___x_257_; 
v___x_255_ = lean_byte_array_fget(v_b_166_, v___x_248_);
lean_dec(v___x_248_);
v___x_256_ = lean_uint8_land(v___x_255_, v___x_200_);
v___x_257_ = lean_uint8_dec_eq(v___x_256_, v___x_194_);
if (v___x_257_ == 0)
{
v___y_173_ = v___x_257_;
goto v___jp_172_;
}
else
{
uint8_t v___x_258_; uint8_t v_b_u2080_259_; uint8_t v___x_260_; uint8_t v_b_u2081_261_; uint8_t v_b_u2082_262_; uint32_t v___x_263_; uint32_t v___x_264_; uint32_t v___x_265_; uint32_t v___x_266_; uint32_t v___x_267_; uint32_t v___x_268_; uint32_t v___x_269_; uint32_t v___x_270_; uint32_t v_r_271_; uint32_t v___x_272_; uint8_t v___x_273_; 
v___x_258_ = 15;
v_b_u2080_259_ = lean_uint8_land(v___x_193_, v___x_258_);
v___x_260_ = 63;
v_b_u2081_261_ = lean_uint8_land(v___x_252_, v___x_260_);
v_b_u2082_262_ = lean_uint8_land(v___x_255_, v___x_260_);
v___x_263_ = lean_uint8_to_uint32(v_b_u2080_259_);
v___x_264_ = 12;
v___x_265_ = lean_uint32_shift_left(v___x_263_, v___x_264_);
v___x_266_ = lean_uint8_to_uint32(v_b_u2081_261_);
v___x_267_ = 6;
v___x_268_ = lean_uint32_shift_left(v___x_266_, v___x_267_);
v___x_269_ = lean_uint32_lor(v___x_265_, v___x_268_);
v___x_270_ = lean_uint8_to_uint32(v_b_u2082_262_);
v_r_271_ = lean_uint32_lor(v___x_269_, v___x_270_);
v___x_272_ = 2048;
v___x_273_ = lean_uint32_dec_le(v___x_272_, v_r_271_);
if (v___x_273_ == 0)
{
v___y_173_ = v___x_201_;
goto v___jp_172_;
}
else
{
uint32_t v___x_274_; uint8_t v___x_275_; 
v___x_274_ = 55296;
v___x_275_ = lean_uint32_dec_lt(v_r_271_, v___x_274_);
if (v___x_275_ == 0)
{
uint32_t v___x_276_; uint8_t v___x_277_; 
v___x_276_ = 57343;
v___x_277_ = lean_uint32_dec_lt(v___x_276_, v_r_271_);
if (v___x_277_ == 0)
{
v___y_173_ = v___x_201_;
goto v___jp_172_;
}
else
{
v___y_173_ = v___x_257_;
goto v___jp_172_;
}
}
else
{
v___y_173_ = v___x_257_;
goto v___jp_172_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = lean_nat_add(v_i_167_, v___x_278_);
v___x_280_ = lean_nat_dec_lt(v___x_279_, v___x_190_);
if (v___x_280_ == 0)
{
lean_dec(v___x_279_);
v___y_173_ = v___x_197_;
goto v___jp_172_;
}
else
{
uint8_t v___x_281_; uint8_t v___x_282_; uint8_t v___x_283_; 
v___x_281_ = lean_byte_array_fget(v_b_166_, v___x_279_);
lean_dec(v___x_279_);
v___x_282_ = lean_uint8_land(v___x_281_, v___x_200_);
v___x_283_ = lean_uint8_dec_eq(v___x_282_, v___x_194_);
if (v___x_283_ == 0)
{
v___y_173_ = v___x_283_;
goto v___jp_172_;
}
else
{
uint8_t v___x_284_; uint8_t v_b_u2080_285_; uint8_t v___x_286_; uint8_t v_b_u2081_287_; uint32_t v___x_288_; uint32_t v___x_289_; uint32_t v___x_290_; uint32_t v___x_291_; uint32_t v_r_292_; uint32_t v___x_293_; uint8_t v___x_294_; 
v___x_284_ = 31;
v_b_u2080_285_ = lean_uint8_land(v___x_193_, v___x_284_);
v___x_286_ = 63;
v_b_u2081_287_ = lean_uint8_land(v___x_281_, v___x_286_);
v___x_288_ = lean_uint8_to_uint32(v_b_u2080_285_);
v___x_289_ = 6;
v___x_290_ = lean_uint32_shift_left(v___x_288_, v___x_289_);
v___x_291_ = lean_uint8_to_uint32(v_b_u2081_287_);
v_r_292_ = lean_uint32_lor(v___x_290_, v___x_291_);
v___x_293_ = 128;
v___x_294_ = lean_uint32_dec_le(v___x_293_, v_r_292_);
v___y_173_ = v___x_294_;
goto v___jp_172_;
}
}
}
}
else
{
v___y_173_ = v___x_197_;
goto v___jp_172_;
}
}
}
v___jp_168_:
{
lean_object* v___x_170_; 
v___x_170_ = lean_nat_add(v_i_167_, v___y_169_);
lean_dec(v_i_167_);
v_i_167_ = v___x_170_;
goto _start;
}
v___jp_172_:
{
if (v___y_173_ == 0)
{
lean_dec(v_i_167_);
return v___y_173_;
}
else
{
uint8_t v___x_174_; uint8_t v___x_175_; uint8_t v___x_176_; uint8_t v___x_177_; uint8_t v___x_178_; 
v___x_174_ = lean_byte_array_fget(v_b_166_, v_i_167_);
v___x_175_ = 128;
v___x_176_ = lean_uint8_land(v___x_174_, v___x_175_);
v___x_177_ = 0;
v___x_178_ = lean_uint8_dec_eq(v___x_176_, v___x_177_);
if (v___x_178_ == 0)
{
uint8_t v___x_179_; uint8_t v___x_180_; uint8_t v___x_181_; uint8_t v___x_182_; 
v___x_179_ = 224;
v___x_180_ = lean_uint8_land(v___x_174_, v___x_179_);
v___x_181_ = 192;
v___x_182_ = lean_uint8_dec_eq(v___x_180_, v___x_181_);
if (v___x_182_ == 0)
{
uint8_t v___x_183_; uint8_t v___x_184_; uint8_t v___x_185_; 
v___x_183_ = 240;
v___x_184_ = lean_uint8_land(v___x_174_, v___x_183_);
v___x_185_ = lean_uint8_dec_eq(v___x_184_, v___x_179_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; 
v___x_186_ = lean_unsigned_to_nat(4u);
v___y_169_ = v___x_186_;
goto v___jp_168_;
}
else
{
lean_object* v___x_187_; 
v___x_187_ = lean_unsigned_to_nat(3u);
v___y_169_ = v___x_187_;
goto v___jp_168_;
}
}
else
{
lean_object* v___x_188_; 
v___x_188_ = lean_unsigned_to_nat(2u);
v___y_169_ = v___x_188_;
goto v___jp_168_;
}
}
else
{
lean_object* v___x_189_; 
v___x_189_ = lean_unsigned_to_nat(1u);
v___y_169_ = v___x_189_;
goto v___jp_168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___redArg___boxed(lean_object* v_b_295_, lean_object* v_i_296_){
_start:
{
uint8_t v_res_297_; lean_object* v_r_298_; 
v_res_297_ = l_ByteArray_validateUTF8_go___redArg(v_b_295_, v_i_296_);
lean_dec_ref(v_b_295_);
v_r_298_ = lean_box(v_res_297_);
return v_r_298_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8_go(lean_object* v_b_299_, lean_object* v_i_300_, lean_object* v_hi_301_){
_start:
{
uint8_t v___x_302_; 
v___x_302_ = l_ByteArray_validateUTF8_go___redArg(v_b_299_, v_i_300_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___boxed(lean_object* v_b_303_, lean_object* v_i_304_, lean_object* v_hi_305_){
_start:
{
uint8_t v_res_306_; lean_object* v_r_307_; 
v_res_306_ = l_ByteArray_validateUTF8_go(v_b_303_, v_i_304_, v_hi_305_);
lean_dec_ref(v_b_303_);
v_r_307_ = lean_box(v_res_306_);
return v_r_307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(uint8_t v_x_308_, lean_object* v_h__1_309_, lean_object* v_h__2_310_){
_start:
{
if (v_x_308_ == 0)
{
lean_object* v___x_311_; 
lean_dec(v_h__2_310_);
v___x_311_ = lean_apply_1(v_h__1_309_, lean_box(0));
return v___x_311_;
}
else
{
lean_object* v___x_312_; 
lean_dec(v_h__1_309_);
v___x_312_ = lean_apply_1(v_h__2_310_, lean_box(0));
return v___x_312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg___boxed(lean_object* v_x_313_, lean_object* v_h__1_314_, lean_object* v_h__2_315_){
_start:
{
uint8_t v_x_24__boxed_316_; lean_object* v_res_317_; 
v_x_24__boxed_316_ = lean_unbox(v_x_313_);
v_res_317_ = l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(v_x_24__boxed_316_, v_h__1_314_, v_h__2_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(lean_object* v_motive_318_, uint8_t v_x_319_, lean_object* v_h__1_320_, lean_object* v_h__2_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(v_x_319_, v_h__1_320_, v_h__2_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___boxed(lean_object* v_motive_323_, lean_object* v_x_324_, lean_object* v_h__1_325_, lean_object* v_h__2_326_){
_start:
{
uint8_t v_x_31__boxed_327_; lean_object* v_res_328_; 
v_x_31__boxed_327_ = lean_unbox(v_x_324_);
v_res_328_ = l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(v_motive_323_, v_x_31__boxed_327_, v_h__1_325_, v_h__2_326_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8___boxed(lean_object* v_b_330_){
_start:
{
uint8_t v_res_331_; lean_object* v_r_332_; 
v_res_331_ = lean_string_validate_utf8(v_b_330_);
lean_dec_ref(v_b_330_);
v_r_332_ = lean_box(v_res_331_);
return v_r_332_;
}
}
LEAN_EXPORT uint8_t l_instDecidableIsValidUTF8(lean_object* v_b_333_){
_start:
{
uint8_t v___x_334_; 
v___x_334_ = lean_string_validate_utf8(v_b_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_instDecidableIsValidUTF8___boxed(lean_object* v_b_335_){
_start:
{
uint8_t v_res_336_; lean_object* v_r_337_; 
v_res_336_ = l_instDecidableIsValidUTF8(v_b_335_);
lean_dec_ref(v_b_335_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_x3f(lean_object* v_a_338_){
_start:
{
uint8_t v___x_339_; 
v___x_339_ = lean_string_validate_utf8(v_a_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; 
lean_dec_ref(v_a_338_);
v___x_340_ = lean_box(0);
return v___x_340_;
}
else
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_string_from_utf8_unchecked(v_a_338_);
v___x_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
return v___x_342_;
}
}
}
static lean_object* _init_l_String_fromUTF8_x21___closed__4(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_347_ = ((lean_object*)(l_String_fromUTF8_x21___closed__3));
v___x_348_ = lean_unsigned_to_nat(46u);
v___x_349_ = lean_unsigned_to_nat(193u);
v___x_350_ = ((lean_object*)(l_String_fromUTF8_x21___closed__2));
v___x_351_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_352_ = l_mkPanicMessageWithDecl(v___x_351_, v___x_350_, v___x_349_, v___x_348_, v___x_347_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_x21(lean_object* v_a_353_){
_start:
{
uint8_t v___x_354_; 
v___x_354_ = lean_string_validate_utf8(v_a_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
lean_dec_ref(v_a_353_);
v___x_355_ = ((lean_object*)(l_String_fromUTF8_x21___closed__0));
v___x_356_ = lean_obj_once(&l_String_fromUTF8_x21___closed__4, &l_String_fromUTF8_x21___closed__4_once, _init_l_String_fromUTF8_x21___closed__4);
v___x_357_ = l_panic___redArg(v___x_355_, v___x_356_);
return v___x_357_;
}
else
{
lean_object* v___x_358_; 
v___x_358_ = lean_string_from_utf8_unchecked(v_a_353_);
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l_String_Internal_toArray(lean_object* v_b_359_){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v_val_364_; 
v___x_360_ = lean_string_to_utf8(v_b_359_);
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_362_ = ((lean_object*)(l_ByteArray_utf8Decode_x3f___closed__0));
v___x_363_ = l_ByteArray_utf8Decode_x3f_go___redArg(v___x_360_, v___x_361_, v___x_362_);
lean_dec_ref(v___x_360_);
v_val_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_val_364_);
lean_dec(v___x_363_);
return v_val_364_;
}
}
LEAN_EXPORT lean_object* l_String_toList___boxed(lean_object* v_s_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = lean_string_data(v_s_366_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_String_data___boxed(lean_object* v_b_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = lean_string_data(v_b_369_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_String_length___boxed(lean_object* v_b_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = lean_string_length(v_b_372_);
lean_dec_ref(v_b_372_);
return v_res_373_;
}
}
static lean_object* _init_l_String_instLT(void){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = lean_box(0);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_String_decidableLT___boxed(lean_object* v_s_u2081_377_, lean_object* v_s_u2082_378_){
_start:
{
uint8_t v_res_379_; lean_object* v_r_380_; 
v_res_379_ = lean_string_dec_lt(v_s_u2081_377_, v_s_u2082_378_);
lean_dec_ref(v_s_u2082_378_);
lean_dec_ref(v_s_u2081_377_);
v_r_380_ = lean_box(v_res_379_);
return v_r_380_;
}
}
static lean_object* _init_l_String_instLE(void){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = lean_box(0);
return v___x_381_;
}
}
LEAN_EXPORT uint8_t l_String_decLE(lean_object* v_s_u2081_382_, lean_object* v_s_u2082_383_){
_start:
{
uint8_t v___x_384_; 
v___x_384_ = lean_string_dec_lt(v_s_u2082_383_, v_s_u2081_382_);
if (v___x_384_ == 0)
{
uint8_t v___x_385_; 
v___x_385_ = 1;
return v___x_385_;
}
else
{
uint8_t v___x_386_; 
v___x_386_ = 0;
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l_String_decLE___boxed(lean_object* v_s_u2081_387_, lean_object* v_s_u2082_388_){
_start:
{
uint8_t v_res_389_; lean_object* v_r_390_; 
v_res_389_ = l_String_decLE(v_s_u2081_387_, v_s_u2082_388_);
lean_dec_ref(v_s_u2082_388_);
lean_dec_ref(v_s_u2081_387_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValid___boxed(lean_object* v_s_393_, lean_object* v_p_394_){
_start:
{
uint8_t v_res_395_; lean_object* v_r_396_; 
v_res_395_ = lean_string_is_valid_pos(v_s_393_, v_p_394_);
lean_dec(v_p_394_);
lean_dec_ref(v_s_393_);
v_r_396_ = lean_box(v_res_395_);
return v_r_396_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsValid(lean_object* v_s_397_, lean_object* v_p_398_){
_start:
{
uint8_t v___x_399_; 
v___x_399_ = lean_string_is_valid_pos(v_s_397_, v_p_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsValid___boxed(lean_object* v_s_400_, lean_object* v_p_401_){
_start:
{
uint8_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = l_String_instDecidableIsValid(v_s_400_, v_p_401_);
lean_dec(v_p_401_);
lean_dec_ref(v_s_400_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT lean_object* l_String_extract___boxed(lean_object* v_s_407_, lean_object* v_b_408_, lean_object* v_e_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = lean_string_utf8_extract(v_s_407_, v_b_408_, v_e_409_);
lean_dec(v_e_409_);
lean_dec(v_b_408_);
lean_dec_ref(v_s_407_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_extract(lean_object* v_s_411_, lean_object* v_b_412_, lean_object* v_e_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = lean_string_utf8_extract(v_s_411_, v_b_412_, v_e_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_extract___boxed(lean_object* v_s_415_, lean_object* v_b_416_, lean_object* v_e_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_String_Pos_extract(v_s_415_, v_b_416_, v_e_417_);
lean_dec(v_e_417_);
lean_dec(v_b_416_);
lean_dec_ref(v_s_415_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_copy(lean_object* v_s_419_){
_start:
{
lean_object* v_str_420_; lean_object* v_startInclusive_421_; lean_object* v_endExclusive_422_; lean_object* v___x_423_; 
v_str_420_ = lean_ctor_get(v_s_419_, 0);
v_startInclusive_421_ = lean_ctor_get(v_s_419_, 1);
v_endExclusive_422_ = lean_ctor_get(v_s_419_, 2);
v___x_423_ = lean_string_utf8_extract(v_str_420_, v_startInclusive_421_, v_endExclusive_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_copy___boxed(lean_object* v_s_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_String_Slice_copy(v_s_424_);
lean_dec_ref(v_s_424_);
return v_res_425_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_isValidForSlice(lean_object* v_s_426_, lean_object* v_p_427_){
_start:
{
lean_object* v_str_428_; lean_object* v_startInclusive_429_; lean_object* v_endExclusive_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v_str_428_ = lean_ctor_get(v_s_426_, 0);
v_startInclusive_429_ = lean_ctor_get(v_s_426_, 1);
v_endExclusive_430_ = lean_ctor_get(v_s_426_, 2);
v___x_431_ = lean_nat_sub(v_endExclusive_430_, v_startInclusive_429_);
v___x_432_ = lean_nat_dec_lt(v_p_427_, v___x_431_);
if (v___x_432_ == 0)
{
uint8_t v___x_433_; 
v___x_433_ = lean_nat_dec_eq(v_p_427_, v___x_431_);
lean_dec(v___x_431_);
return v___x_433_;
}
else
{
lean_object* v___x_434_; uint8_t v___x_435_; uint8_t v___x_436_; uint8_t v___x_437_; uint8_t v___x_438_; uint8_t v___x_439_; 
lean_dec(v___x_431_);
v___x_434_ = lean_nat_add(v_startInclusive_429_, v_p_427_);
v___x_435_ = lean_string_get_byte_fast(v_str_428_, v___x_434_);
v___x_436_ = 128;
v___x_437_ = lean_uint8_land(v___x_435_, v___x_436_);
v___x_438_ = 0;
v___x_439_ = lean_uint8_dec_eq(v___x_437_, v___x_438_);
if (v___x_439_ == 0)
{
uint8_t v___x_440_; uint8_t v___x_441_; uint8_t v___x_442_; uint8_t v___x_443_; 
v___x_440_ = 224;
v___x_441_ = lean_uint8_land(v___x_435_, v___x_440_);
v___x_442_ = 192;
v___x_443_ = lean_uint8_dec_eq(v___x_441_, v___x_442_);
if (v___x_443_ == 0)
{
uint8_t v___x_444_; uint8_t v___x_445_; uint8_t v___x_446_; 
v___x_444_ = 240;
v___x_445_ = lean_uint8_land(v___x_435_, v___x_444_);
v___x_446_ = lean_uint8_dec_eq(v___x_445_, v___x_440_);
if (v___x_446_ == 0)
{
uint8_t v___x_447_; uint8_t v___x_448_; uint8_t v___x_449_; 
v___x_447_ = 248;
v___x_448_ = lean_uint8_land(v___x_435_, v___x_447_);
v___x_449_ = lean_uint8_dec_eq(v___x_448_, v___x_444_);
return v___x_449_;
}
else
{
return v___x_446_;
}
}
else
{
return v___x_443_;
}
}
else
{
return v___x_439_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValidForSlice___boxed(lean_object* v_s_450_, lean_object* v_p_451_){
_start:
{
uint8_t v_res_452_; lean_object* v_r_453_; 
v_res_452_ = l_String_Pos_Raw_isValidForSlice(v_s_450_, v_p_451_);
lean_dec(v_p_451_);
lean_dec_ref(v_s_450_);
v_r_453_ = lean_box(v_res_452_);
return v_r_453_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsValidForSlice(lean_object* v_s_454_, lean_object* v_p_455_){
_start:
{
uint8_t v___x_456_; 
v___x_456_ = l_String_Pos_Raw_isValidForSlice(v_s_454_, v_p_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsValidForSlice___boxed(lean_object* v_s_457_, lean_object* v_p_458_){
_start:
{
uint8_t v_res_459_; lean_object* v_r_460_; 
v_res_459_ = l_String_instDecidableIsValidForSlice(v_s_457_, v_p_458_);
lean_dec(v_p_458_);
lean_dec_ref(v_s_457_);
v_r_460_ = lean_box(v_res_459_);
return v_r_460_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str(lean_object* v_s_461_, lean_object* v_pos_462_){
_start:
{
lean_object* v_startInclusive_463_; lean_object* v___x_464_; 
v_startInclusive_463_ = lean_ctor_get(v_s_461_, 1);
v___x_464_ = lean_nat_add(v_startInclusive_463_, v_pos_462_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str___boxed(lean_object* v_s_465_, lean_object* v_pos_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_String_Slice_Pos_str(v_s_465_, v_pos_466_);
lean_dec(v_pos_466_);
lean_dec_ref(v_s_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg(lean_object* v_s_468_, lean_object* v_pos_469_){
_start:
{
lean_object* v_startInclusive_470_; lean_object* v___x_471_; 
v_startInclusive_470_ = lean_ctor_get(v_s_468_, 1);
v___x_471_ = lean_nat_sub(v_pos_469_, v_startInclusive_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg___boxed(lean_object* v_s_472_, lean_object* v_pos_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_String_Slice_Pos_ofStr___redArg(v_s_472_, v_pos_473_);
lean_dec(v_pos_473_);
lean_dec_ref(v_s_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr(lean_object* v_s_475_, lean_object* v_pos_476_, lean_object* v_h_u2081_477_, lean_object* v_h_u2082_478_){
_start:
{
lean_object* v_startInclusive_479_; lean_object* v___x_480_; 
v_startInclusive_479_ = lean_ctor_get(v_s_475_, 1);
v___x_480_ = lean_nat_sub(v_pos_476_, v_startInclusive_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___boxed(lean_object* v_s_481_, lean_object* v_pos_482_, lean_object* v_h_u2081_483_, lean_object* v_h_u2082_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_String_Slice_Pos_ofStr(v_s_481_, v_pos_482_, v_h_u2081_483_, v_h_u2082_484_);
lean_dec(v_pos_482_);
lean_dec_ref(v_s_481_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom(lean_object* v_s_486_, lean_object* v_pos_487_){
_start:
{
lean_object* v_str_488_; lean_object* v_startInclusive_489_; lean_object* v_endExclusive_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_498_; 
v_str_488_ = lean_ctor_get(v_s_486_, 0);
v_startInclusive_489_ = lean_ctor_get(v_s_486_, 1);
v_endExclusive_490_ = lean_ctor_get(v_s_486_, 2);
v_isSharedCheck_498_ = !lean_is_exclusive(v_s_486_);
if (v_isSharedCheck_498_ == 0)
{
v___x_492_ = v_s_486_;
v_isShared_493_ = v_isSharedCheck_498_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_endExclusive_490_);
lean_inc(v_startInclusive_489_);
lean_inc(v_str_488_);
lean_dec(v_s_486_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_498_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_494_ = lean_nat_add(v_startInclusive_489_, v_pos_487_);
lean_dec(v_startInclusive_489_);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 1, v___x_494_);
v___x_496_ = v___x_492_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_str_488_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v___x_494_);
lean_ctor_set(v_reuseFailAlloc_497_, 2, v_endExclusive_490_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom___boxed(lean_object* v_s_499_, lean_object* v_pos_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_String_Slice_sliceFrom(v_s_499_, v_pos_500_);
lean_dec(v_pos_500_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStart(lean_object* v_s_502_, lean_object* v_pos_503_){
_start:
{
lean_object* v_str_504_; lean_object* v_startInclusive_505_; lean_object* v_endExclusive_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_514_; 
v_str_504_ = lean_ctor_get(v_s_502_, 0);
v_startInclusive_505_ = lean_ctor_get(v_s_502_, 1);
v_endExclusive_506_ = lean_ctor_get(v_s_502_, 2);
v_isSharedCheck_514_ = !lean_is_exclusive(v_s_502_);
if (v_isSharedCheck_514_ == 0)
{
v___x_508_ = v_s_502_;
v_isShared_509_ = v_isSharedCheck_514_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_endExclusive_506_);
lean_inc(v_startInclusive_505_);
lean_inc(v_str_504_);
lean_dec(v_s_502_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_514_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_510_ = lean_nat_add(v_startInclusive_505_, v_pos_503_);
lean_dec(v_startInclusive_505_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v___x_510_);
v___x_512_ = v___x_508_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_str_504_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_513_, 2, v_endExclusive_506_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStart___boxed(lean_object* v_s_515_, lean_object* v_pos_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_String_Slice_replaceStart(v_s_515_, v_pos_516_);
lean_dec(v_pos_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceTo(lean_object* v_s_518_, lean_object* v_pos_519_){
_start:
{
lean_object* v_str_520_; lean_object* v_startInclusive_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_529_; 
v_str_520_ = lean_ctor_get(v_s_518_, 0);
v_startInclusive_521_ = lean_ctor_get(v_s_518_, 1);
v_isSharedCheck_529_ = !lean_is_exclusive(v_s_518_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; 
v_unused_530_ = lean_ctor_get(v_s_518_, 2);
lean_dec(v_unused_530_);
v___x_523_ = v_s_518_;
v_isShared_524_ = v_isSharedCheck_529_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_startInclusive_521_);
lean_inc(v_str_520_);
lean_dec(v_s_518_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_529_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_525_ = lean_nat_add(v_startInclusive_521_, v_pos_519_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 2, v___x_525_);
v___x_527_ = v___x_523_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_str_520_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_startInclusive_521_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceTo___boxed(lean_object* v_s_531_, lean_object* v_pos_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_String_Slice_sliceTo(v_s_531_, v_pos_532_);
lean_dec(v_pos_532_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd(lean_object* v_s_534_, lean_object* v_pos_535_){
_start:
{
lean_object* v_str_536_; lean_object* v_startInclusive_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_545_; 
v_str_536_ = lean_ctor_get(v_s_534_, 0);
v_startInclusive_537_ = lean_ctor_get(v_s_534_, 1);
v_isSharedCheck_545_ = !lean_is_exclusive(v_s_534_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; 
v_unused_546_ = lean_ctor_get(v_s_534_, 2);
lean_dec(v_unused_546_);
v___x_539_ = v_s_534_;
v_isShared_540_ = v_isSharedCheck_545_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_startInclusive_537_);
lean_inc(v_str_536_);
lean_dec(v_s_534_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_545_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_541_ = lean_nat_add(v_startInclusive_537_, v_pos_535_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 2, v___x_541_);
v___x_543_ = v___x_539_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_str_536_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_startInclusive_537_);
lean_ctor_set(v_reuseFailAlloc_544_, 2, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd___boxed(lean_object* v_s_547_, lean_object* v_pos_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_String_Slice_replaceEnd(v_s_547_, v_pos_548_);
lean_dec(v_pos_548_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg(lean_object* v_s_550_, lean_object* v_newStart_551_, lean_object* v_newEnd_552_){
_start:
{
lean_object* v_str_553_; lean_object* v_startInclusive_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_563_; 
v_str_553_ = lean_ctor_get(v_s_550_, 0);
v_startInclusive_554_ = lean_ctor_get(v_s_550_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v_s_550_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; 
v_unused_564_ = lean_ctor_get(v_s_550_, 2);
lean_dec(v_unused_564_);
v___x_556_ = v_s_550_;
v_isShared_557_ = v_isSharedCheck_563_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_startInclusive_554_);
lean_inc(v_str_553_);
lean_dec(v_s_550_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_563_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_558_ = lean_nat_add(v_startInclusive_554_, v_newStart_551_);
v___x_559_ = lean_nat_add(v_startInclusive_554_, v_newEnd_552_);
lean_dec(v_startInclusive_554_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 2, v___x_559_);
lean_ctor_set(v___x_556_, 1, v___x_558_);
v___x_561_ = v___x_556_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_str_553_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg___boxed(lean_object* v_s_565_, lean_object* v_newStart_566_, lean_object* v_newEnd_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_String_Slice_slice___redArg(v_s_565_, v_newStart_566_, v_newEnd_567_);
lean_dec(v_newEnd_567_);
lean_dec(v_newStart_566_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice(lean_object* v_s_569_, lean_object* v_newStart_570_, lean_object* v_newEnd_571_, lean_object* v_h_572_){
_start:
{
lean_object* v_str_573_; lean_object* v_startInclusive_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_583_; 
v_str_573_ = lean_ctor_get(v_s_569_, 0);
v_startInclusive_574_ = lean_ctor_get(v_s_569_, 1);
v_isSharedCheck_583_ = !lean_is_exclusive(v_s_569_);
if (v_isSharedCheck_583_ == 0)
{
lean_object* v_unused_584_; 
v_unused_584_ = lean_ctor_get(v_s_569_, 2);
lean_dec(v_unused_584_);
v___x_576_ = v_s_569_;
v_isShared_577_ = v_isSharedCheck_583_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_startInclusive_574_);
lean_inc(v_str_573_);
lean_dec(v_s_569_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_583_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_578_ = lean_nat_add(v_startInclusive_574_, v_newStart_570_);
v___x_579_ = lean_nat_add(v_startInclusive_574_, v_newEnd_571_);
lean_dec(v_startInclusive_574_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 2, v___x_579_);
lean_ctor_set(v___x_576_, 1, v___x_578_);
v___x_581_ = v___x_576_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_str_573_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_582_, 2, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___boxed(lean_object* v_s_585_, lean_object* v_newStart_586_, lean_object* v_newEnd_587_, lean_object* v_h_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_String_Slice_slice(v_s_585_, v_newStart_586_, v_newEnd_587_, v_h_588_);
lean_dec(v_newEnd_587_);
lean_dec(v_newStart_586_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg(lean_object* v_s_590_, lean_object* v_newStart_591_, lean_object* v_newEnd_592_){
_start:
{
lean_object* v_str_593_; lean_object* v_startInclusive_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_603_; 
v_str_593_ = lean_ctor_get(v_s_590_, 0);
v_startInclusive_594_ = lean_ctor_get(v_s_590_, 1);
v_isSharedCheck_603_ = !lean_is_exclusive(v_s_590_);
if (v_isSharedCheck_603_ == 0)
{
lean_object* v_unused_604_; 
v_unused_604_ = lean_ctor_get(v_s_590_, 2);
lean_dec(v_unused_604_);
v___x_596_ = v_s_590_;
v_isShared_597_ = v_isSharedCheck_603_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_startInclusive_594_);
lean_inc(v_str_593_);
lean_dec(v_s_590_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_603_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_598_ = lean_nat_add(v_startInclusive_594_, v_newStart_591_);
v___x_599_ = lean_nat_add(v_startInclusive_594_, v_newEnd_592_);
lean_dec(v_startInclusive_594_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 2, v___x_599_);
lean_ctor_set(v___x_596_, 1, v___x_598_);
v___x_601_ = v___x_596_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_str_593_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_602_, 2, v___x_599_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg___boxed(lean_object* v_s_605_, lean_object* v_newStart_606_, lean_object* v_newEnd_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_String_Slice_replaceStartEnd___redArg(v_s_605_, v_newStart_606_, v_newEnd_607_);
lean_dec(v_newEnd_607_);
lean_dec(v_newStart_606_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd(lean_object* v_s_609_, lean_object* v_newStart_610_, lean_object* v_newEnd_611_, lean_object* v_h_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_String_Slice_replaceStartEnd___redArg(v_s_609_, v_newStart_610_, v_newEnd_611_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___boxed(lean_object* v_s_614_, lean_object* v_newStart_615_, lean_object* v_newEnd_616_, lean_object* v_h_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_String_Slice_replaceStartEnd(v_s_614_, v_newStart_615_, v_newEnd_616_, v_h_617_);
lean_dec(v_newEnd_616_);
lean_dec(v_newStart_615_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f(lean_object* v_s_619_, lean_object* v_newStart_620_, lean_object* v_newEnd_621_){
_start:
{
uint8_t v___x_622_; 
v___x_622_ = lean_nat_dec_le(v_newStart_620_, v_newEnd_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
lean_dec_ref(v_s_619_);
v___x_623_ = lean_box(0);
return v___x_623_;
}
else
{
lean_object* v_str_624_; lean_object* v_startInclusive_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_635_; 
v_str_624_ = lean_ctor_get(v_s_619_, 0);
v_startInclusive_625_ = lean_ctor_get(v_s_619_, 1);
v_isSharedCheck_635_ = !lean_is_exclusive(v_s_619_);
if (v_isSharedCheck_635_ == 0)
{
lean_object* v_unused_636_; 
v_unused_636_ = lean_ctor_get(v_s_619_, 2);
lean_dec(v_unused_636_);
v___x_627_ = v_s_619_;
v_isShared_628_ = v_isSharedCheck_635_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_startInclusive_625_);
lean_inc(v_str_624_);
lean_dec(v_s_619_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_635_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_629_ = lean_nat_add(v_startInclusive_625_, v_newStart_620_);
v___x_630_ = lean_nat_add(v_startInclusive_625_, v_newEnd_621_);
lean_dec(v_startInclusive_625_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 2, v___x_630_);
lean_ctor_set(v___x_627_, 1, v___x_629_);
v___x_632_ = v___x_627_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_str_624_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v___x_630_);
v___x_632_ = v_reuseFailAlloc_634_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_633_; 
v___x_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
return v___x_633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f___boxed(lean_object* v_s_637_, lean_object* v_newStart_638_, lean_object* v_newEnd_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_String_Slice_slice_x3f(v_s_637_, v_newStart_638_, v_newEnd_639_);
lean_dec(v_newEnd_639_);
lean_dec(v_newStart_638_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_slice_x21_spec__0(lean_object* v_msg_641_){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = l_String_instInhabitedSlice;
v___x_643_ = lean_panic_fn(v___x_642_, v_msg_641_);
return v___x_643_;
}
}
static lean_object* _init_l_String_Slice_slice_x21___closed__2(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_646_ = ((lean_object*)(l_String_Slice_slice_x21___closed__1));
v___x_647_ = lean_unsigned_to_nat(4u);
v___x_648_ = lean_unsigned_to_nat(1122u);
v___x_649_ = ((lean_object*)(l_String_Slice_slice_x21___closed__0));
v___x_650_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_651_ = l_mkPanicMessageWithDecl(v___x_650_, v___x_649_, v___x_648_, v___x_647_, v___x_646_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x21(lean_object* v_s_652_, lean_object* v_newStart_653_, lean_object* v_newEnd_654_){
_start:
{
uint8_t v___x_655_; 
v___x_655_ = lean_nat_dec_le(v_newStart_653_, v_newEnd_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; 
lean_dec_ref(v_s_652_);
v___x_656_ = lean_obj_once(&l_String_Slice_slice_x21___closed__2, &l_String_Slice_slice_x21___closed__2_once, _init_l_String_Slice_slice_x21___closed__2);
v___x_657_ = l_panic___at___00String_Slice_slice_x21_spec__0(v___x_656_);
return v___x_657_;
}
else
{
lean_object* v_str_658_; lean_object* v_startInclusive_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_668_; 
v_str_658_ = lean_ctor_get(v_s_652_, 0);
v_startInclusive_659_ = lean_ctor_get(v_s_652_, 1);
v_isSharedCheck_668_ = !lean_is_exclusive(v_s_652_);
if (v_isSharedCheck_668_ == 0)
{
lean_object* v_unused_669_; 
v_unused_669_ = lean_ctor_get(v_s_652_, 2);
lean_dec(v_unused_669_);
v___x_661_ = v_s_652_;
v_isShared_662_ = v_isSharedCheck_668_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_startInclusive_659_);
lean_inc(v_str_658_);
lean_dec(v_s_652_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_668_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_663_ = lean_nat_add(v_startInclusive_659_, v_newStart_653_);
v___x_664_ = lean_nat_add(v_startInclusive_659_, v_newEnd_654_);
lean_dec(v_startInclusive_659_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 2, v___x_664_);
lean_ctor_set(v___x_661_, 1, v___x_663_);
v___x_666_ = v___x_661_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_str_658_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_667_, 2, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x21___boxed(lean_object* v_s_670_, lean_object* v_newStart_671_, lean_object* v_newEnd_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_String_Slice_slice_x21(v_s_670_, v_newStart_671_, v_newEnd_672_);
lean_dec(v_newEnd_672_);
lean_dec(v_newStart_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21(lean_object* v_s_674_, lean_object* v_newStart_675_, lean_object* v_newEnd_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_String_Slice_slice_x21(v_s_674_, v_newStart_675_, v_newEnd_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21___boxed(lean_object* v_s_678_, lean_object* v_newStart_679_, lean_object* v_newEnd_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_String_Slice_replaceStartEnd_x21(v_s_678_, v_newStart_679_, v_newEnd_680_);
lean_dec(v_newEnd_680_);
lean_dec(v_newStart_679_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_String_decodeChar___boxed(lean_object* v_s_685_, lean_object* v_byteIdx_686_, lean_object* v_h_687_){
_start:
{
uint32_t v_res_688_; lean_object* v_r_689_; 
v_res_688_ = lean_string_utf8_get_fast(v_s_685_, v_byteIdx_686_);
lean_dec(v_byteIdx_686_);
lean_dec_ref(v_s_685_);
v_r_689_ = lean_box_uint32(v_res_688_);
return v_r_689_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get___redArg(lean_object* v_s_690_, lean_object* v_pos_691_){
_start:
{
lean_object* v_str_692_; lean_object* v_startInclusive_693_; lean_object* v___x_694_; uint32_t v___x_695_; 
v_str_692_ = lean_ctor_get(v_s_690_, 0);
v_startInclusive_693_ = lean_ctor_get(v_s_690_, 1);
v___x_694_ = lean_nat_add(v_startInclusive_693_, v_pos_691_);
v___x_695_ = lean_string_utf8_get_fast(v_str_692_, v___x_694_);
lean_dec(v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___redArg___boxed(lean_object* v_s_696_, lean_object* v_pos_697_){
_start:
{
uint32_t v_res_698_; lean_object* v_r_699_; 
v_res_698_ = l_String_Slice_Pos_get___redArg(v_s_696_, v_pos_697_);
lean_dec(v_pos_697_);
lean_dec_ref(v_s_696_);
v_r_699_ = lean_box_uint32(v_res_698_);
return v_r_699_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get(lean_object* v_s_700_, lean_object* v_pos_701_, lean_object* v_h_702_){
_start:
{
lean_object* v_str_703_; lean_object* v_startInclusive_704_; lean_object* v___x_705_; uint32_t v___x_706_; 
v_str_703_ = lean_ctor_get(v_s_700_, 0);
v_startInclusive_704_ = lean_ctor_get(v_s_700_, 1);
v___x_705_ = lean_nat_add(v_startInclusive_704_, v_pos_701_);
v___x_706_ = lean_string_utf8_get_fast(v_str_703_, v___x_705_);
lean_dec(v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___boxed(lean_object* v_s_707_, lean_object* v_pos_708_, lean_object* v_h_709_){
_start:
{
uint32_t v_res_710_; lean_object* v_r_711_; 
v_res_710_ = l_String_Slice_Pos_get(v_s_707_, v_pos_708_, v_h_709_);
lean_dec(v_pos_708_);
lean_dec_ref(v_s_707_);
v_r_711_ = lean_box_uint32(v_res_710_);
return v_r_711_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f(lean_object* v_s_712_, lean_object* v_pos_713_){
_start:
{
lean_object* v_str_714_; lean_object* v_startInclusive_715_; lean_object* v_endExclusive_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v_str_714_ = lean_ctor_get(v_s_712_, 0);
v_startInclusive_715_ = lean_ctor_get(v_s_712_, 1);
v_endExclusive_716_ = lean_ctor_get(v_s_712_, 2);
v___x_717_ = lean_nat_sub(v_endExclusive_716_, v_startInclusive_715_);
v___x_718_ = lean_nat_dec_eq(v_pos_713_, v___x_717_);
lean_dec(v___x_717_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; uint32_t v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_719_ = lean_nat_add(v_startInclusive_715_, v_pos_713_);
v___x_720_ = lean_string_utf8_get_fast(v_str_714_, v___x_719_);
lean_dec(v___x_719_);
v___x_721_ = lean_box_uint32(v___x_720_);
v___x_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
else
{
lean_object* v___x_723_; 
v___x_723_ = lean_box(0);
return v___x_723_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f___boxed(lean_object* v_s_724_, lean_object* v_pos_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_String_Slice_Pos_get_x3f(v_s_724_, v_pos_725_);
lean_dec(v_pos_725_);
lean_dec_ref(v_s_724_);
return v_res_726_;
}
}
static lean_object* _init_l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1(void){
_start:
{
uint32_t v___x_727_; lean_object* v___x_728_; 
v___x_727_ = 65;
v___x_728_ = lean_box_uint32(v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT uint32_t l_panic___at___00String_Slice_Pos_get_x21_spec__0(lean_object* v_msg_729_){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; uint32_t v___x_732_; 
v___x_730_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1;
v___x_731_ = lean_panic_fn(v___x_730_, v_msg_729_);
v___x_732_ = lean_unbox_uint32(v___x_731_);
lean_dec(v___x_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed(lean_object* v_msg_733_){
_start:
{
uint32_t v_res_734_; lean_object* v_r_735_; 
v_res_734_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v_msg_733_);
v_r_735_ = lean_box_uint32(v_res_734_);
return v_r_735_;
}
}
static lean_object* _init_l_String_Slice_Pos_get_x21___closed__2(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_738_ = ((lean_object*)(l_String_Slice_Pos_get_x21___closed__1));
v___x_739_ = lean_unsigned_to_nat(29u);
v___x_740_ = lean_unsigned_to_nat(1207u);
v___x_741_ = ((lean_object*)(l_String_Slice_Pos_get_x21___closed__0));
v___x_742_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_743_ = l_mkPanicMessageWithDecl(v___x_742_, v___x_741_, v___x_740_, v___x_739_, v___x_738_);
return v___x_743_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get_x21(lean_object* v_s_744_, lean_object* v_pos_745_){
_start:
{
lean_object* v_str_746_; lean_object* v_startInclusive_747_; lean_object* v_endExclusive_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v_str_746_ = lean_ctor_get(v_s_744_, 0);
v_startInclusive_747_ = lean_ctor_get(v_s_744_, 1);
v_endExclusive_748_ = lean_ctor_get(v_s_744_, 2);
v___x_749_ = lean_nat_sub(v_endExclusive_748_, v_startInclusive_747_);
v___x_750_ = lean_nat_dec_eq(v_pos_745_, v___x_749_);
lean_dec(v___x_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; uint32_t v___x_752_; 
v___x_751_ = lean_nat_add(v_startInclusive_747_, v_pos_745_);
v___x_752_ = lean_string_utf8_get_fast(v_str_746_, v___x_751_);
lean_dec(v___x_751_);
return v___x_752_;
}
else
{
lean_object* v___x_753_; uint32_t v___x_754_; 
v___x_753_ = lean_obj_once(&l_String_Slice_Pos_get_x21___closed__2, &l_String_Slice_Pos_get_x21___closed__2_once, _init_l_String_Slice_Pos_get_x21___closed__2);
v___x_754_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v___x_753_);
return v___x_754_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x21___boxed(lean_object* v_s_755_, lean_object* v_pos_756_){
_start:
{
uint32_t v_res_757_; lean_object* v_r_758_; 
v_res_757_ = l_String_Slice_Pos_get_x21(v_s_755_, v_pos_756_);
lean_dec(v_pos_756_);
lean_dec_ref(v_s_755_);
v_r_758_ = lean_box_uint32(v_res_757_);
return v_r_758_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg(lean_object* v_pos_759_){
_start:
{
lean_inc(v_pos_759_);
return v_pos_759_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg___boxed(lean_object* v_pos_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_String_Pos_toSlice___redArg(v_pos_760_);
lean_dec(v_pos_760_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice(lean_object* v_s_762_, lean_object* v_pos_763_){
_start:
{
lean_inc(v_pos_763_);
return v_pos_763_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___boxed(lean_object* v_s_764_, lean_object* v_pos_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_String_Pos_toSlice(v_s_764_, v_pos_765_);
lean_dec(v_pos_765_);
lean_dec_ref(v_s_764_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg(lean_object* v_pos_767_){
_start:
{
lean_inc(v_pos_767_);
return v_pos_767_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg___boxed(lean_object* v_pos_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_String_Pos_ofToSlice___redArg(v_pos_768_);
lean_dec(v_pos_768_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice(lean_object* v_s_770_, lean_object* v_pos_771_){
_start:
{
lean_inc(v_pos_771_);
return v_pos_771_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___boxed(lean_object* v_s_772_, lean_object* v_pos_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_String_Pos_ofToSlice(v_s_772_, v_pos_773_);
lean_dec(v_pos_773_);
lean_dec_ref(v_s_772_);
return v_res_774_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get___redArg(lean_object* v_s_775_, lean_object* v_pos_776_){
_start:
{
uint32_t v___x_777_; 
v___x_777_ = lean_string_utf8_get_fast(v_s_775_, v_pos_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get___redArg___boxed(lean_object* v_s_778_, lean_object* v_pos_779_){
_start:
{
uint32_t v_res_780_; lean_object* v_r_781_; 
v_res_780_ = l_String_Pos_get___redArg(v_s_778_, v_pos_779_);
lean_dec(v_pos_779_);
lean_dec_ref(v_s_778_);
v_r_781_ = lean_box_uint32(v_res_780_);
return v_r_781_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get(lean_object* v_s_782_, lean_object* v_pos_783_, lean_object* v_h_784_){
_start:
{
uint32_t v___x_785_; 
v___x_785_ = lean_string_utf8_get_fast(v_s_782_, v_pos_783_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get___boxed(lean_object* v_s_786_, lean_object* v_pos_787_, lean_object* v_h_788_){
_start:
{
uint32_t v_res_789_; lean_object* v_r_790_; 
v_res_789_ = l_String_Pos_get(v_s_786_, v_pos_787_, v_h_788_);
lean_dec(v_pos_787_);
lean_dec_ref(v_s_786_);
v_r_790_ = lean_box_uint32(v_res_789_);
return v_r_790_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x3f(lean_object* v_s_791_, lean_object* v_pos_792_){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_793_ = lean_unsigned_to_nat(0u);
v___x_794_ = lean_string_utf8_byte_size(v_s_791_);
v___x_795_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_795_, 0, v_s_791_);
lean_ctor_set(v___x_795_, 1, v___x_793_);
lean_ctor_set(v___x_795_, 2, v___x_794_);
v___x_796_ = l_String_Slice_Pos_get_x3f(v___x_795_, v_pos_792_);
lean_dec_ref(v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x3f___boxed(lean_object* v_s_797_, lean_object* v_pos_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_String_Pos_get_x3f(v_s_797_, v_pos_798_);
lean_dec(v_pos_798_);
return v_res_799_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get_x21(lean_object* v_s_800_, lean_object* v_pos_801_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; uint32_t v___x_805_; 
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = lean_string_utf8_byte_size(v_s_800_);
v___x_804_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_804_, 0, v_s_800_);
lean_ctor_set(v___x_804_, 1, v___x_802_);
lean_ctor_set(v___x_804_, 2, v___x_803_);
v___x_805_ = l_String_Slice_Pos_get_x21(v___x_804_, v_pos_801_);
lean_dec_ref(v___x_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x21___boxed(lean_object* v_s_806_, lean_object* v_pos_807_){
_start:
{
uint32_t v_res_808_; lean_object* v_r_809_; 
v_res_808_ = l_String_Pos_get_x21(v_s_806_, v_pos_807_);
lean_dec(v_pos_807_);
v_r_809_ = lean_box_uint32(v_res_808_);
return v_r_809_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_byte___redArg(lean_object* v_s_810_, lean_object* v_pos_811_){
_start:
{
uint8_t v___x_812_; 
v___x_812_ = lean_string_get_byte_fast(v_s_810_, v_pos_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_byte___redArg___boxed(lean_object* v_s_813_, lean_object* v_pos_814_){
_start:
{
uint8_t v_res_815_; lean_object* v_r_816_; 
v_res_815_ = l_String_Pos_byte___redArg(v_s_813_, v_pos_814_);
lean_dec_ref(v_s_813_);
v_r_816_ = lean_box(v_res_815_);
return v_r_816_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_byte(lean_object* v_s_817_, lean_object* v_pos_818_, lean_object* v_h_819_){
_start:
{
uint8_t v___x_820_; 
v___x_820_ = lean_string_get_byte_fast(v_s_817_, v_pos_818_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_byte___boxed(lean_object* v_s_821_, lean_object* v_pos_822_, lean_object* v_h_823_){
_start:
{
uint8_t v_res_824_; lean_object* v_r_825_; 
v_res_824_ = l_String_Pos_byte(v_s_821_, v_pos_822_, v_h_823_);
lean_dec_ref(v_s_821_);
v_r_825_ = lean_box(v_res_824_);
return v_r_825_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg(lean_object* v_pos_826_){
_start:
{
lean_inc(v_pos_826_);
return v_pos_826_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg___boxed(lean_object* v_pos_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_String_Pos_ofCopy___redArg(v_pos_827_);
lean_dec(v_pos_827_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy(lean_object* v_s_829_, lean_object* v_pos_830_){
_start:
{
lean_inc(v_pos_830_);
return v_pos_830_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___boxed(lean_object* v_s_831_, lean_object* v_pos_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_String_Pos_ofCopy(v_s_831_, v_pos_832_);
lean_dec(v_pos_832_);
lean_dec_ref(v_s_831_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg(lean_object* v_pos_834_){
_start:
{
lean_inc(v_pos_834_);
return v_pos_834_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg___boxed(lean_object* v_pos_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_String_Slice_Pos_copy___redArg(v_pos_835_);
lean_dec(v_pos_835_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy(lean_object* v_s_837_, lean_object* v_pos_838_){
_start:
{
lean_inc(v_pos_838_);
return v_pos_838_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___boxed(lean_object* v_s_839_, lean_object* v_pos_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_String_Slice_Pos_copy(v_s_839_, v_pos_840_);
lean_dec(v_pos_840_);
lean_dec_ref(v_s_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg(lean_object* v_pos_842_){
_start:
{
lean_inc(v_pos_842_);
return v_pos_842_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg___boxed(lean_object* v_pos_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_String_Slice_Pos_toCopy___redArg(v_pos_843_);
lean_dec(v_pos_843_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy(lean_object* v_s_845_, lean_object* v_pos_846_){
_start:
{
lean_inc(v_pos_846_);
return v_pos_846_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___boxed(lean_object* v_s_847_, lean_object* v_pos_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_String_Slice_Pos_toCopy(v_s_847_, v_pos_848_);
lean_dec(v_pos_848_);
lean_dec_ref(v_s_847_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg(lean_object* v_p_u2080_850_, lean_object* v_pos_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = lean_nat_add(v_p_u2080_850_, v_pos_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg___boxed(lean_object* v_p_u2080_853_, lean_object* v_pos_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_String_Slice_Pos_ofSliceFrom___redArg(v_p_u2080_853_, v_pos_854_);
lean_dec(v_pos_854_);
lean_dec(v_p_u2080_853_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom(lean_object* v_s_856_, lean_object* v_p_u2080_857_, lean_object* v_pos_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = lean_nat_add(v_p_u2080_857_, v_pos_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___boxed(lean_object* v_s_860_, lean_object* v_p_u2080_861_, lean_object* v_pos_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_String_Slice_Pos_ofSliceFrom(v_s_860_, v_p_u2080_861_, v_pos_862_);
lean_dec(v_pos_862_);
lean_dec(v_p_u2080_861_);
lean_dec_ref(v_s_860_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg(lean_object* v_p_u2080_864_, lean_object* v_pos_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = lean_nat_add(v_p_u2080_864_, v_pos_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg___boxed(lean_object* v_p_u2080_867_, lean_object* v_pos_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_String_Slice_Pos_ofReplaceStart___redArg(v_p_u2080_867_, v_pos_868_);
lean_dec(v_pos_868_);
lean_dec(v_p_u2080_867_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart(lean_object* v_s_870_, lean_object* v_p_u2080_871_, lean_object* v_pos_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = lean_nat_add(v_p_u2080_871_, v_pos_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___boxed(lean_object* v_s_874_, lean_object* v_p_u2080_875_, lean_object* v_pos_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_String_Slice_Pos_ofReplaceStart(v_s_874_, v_p_u2080_875_, v_pos_876_);
lean_dec(v_pos_876_);
lean_dec(v_p_u2080_875_);
lean_dec_ref(v_s_874_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg(lean_object* v_p_u2080_878_, lean_object* v_pos_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = lean_nat_sub(v_pos_879_, v_p_u2080_878_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg___boxed(lean_object* v_p_u2080_881_, lean_object* v_pos_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_String_Slice_Pos_sliceFrom___redArg(v_p_u2080_881_, v_pos_882_);
lean_dec(v_pos_882_);
lean_dec(v_p_u2080_881_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom(lean_object* v_s_884_, lean_object* v_p_u2080_885_, lean_object* v_pos_886_, lean_object* v_h_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = lean_nat_sub(v_pos_886_, v_p_u2080_885_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___boxed(lean_object* v_s_889_, lean_object* v_p_u2080_890_, lean_object* v_pos_891_, lean_object* v_h_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_String_Slice_Pos_sliceFrom(v_s_889_, v_p_u2080_890_, v_pos_891_, v_h_892_);
lean_dec(v_pos_891_);
lean_dec(v_p_u2080_890_);
lean_dec_ref(v_s_889_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg(lean_object* v_p_u2080_894_, lean_object* v_pos_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = lean_nat_sub(v_pos_895_, v_p_u2080_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg___boxed(lean_object* v_p_u2080_897_, lean_object* v_pos_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_String_Slice_Pos_toReplaceStart___redArg(v_p_u2080_897_, v_pos_898_);
lean_dec(v_pos_898_);
lean_dec(v_p_u2080_897_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart(lean_object* v_s_900_, lean_object* v_p_u2080_901_, lean_object* v_pos_902_, lean_object* v_h_903_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = lean_nat_sub(v_pos_902_, v_p_u2080_901_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___boxed(lean_object* v_s_905_, lean_object* v_p_u2080_906_, lean_object* v_pos_907_, lean_object* v_h_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_String_Slice_Pos_toReplaceStart(v_s_905_, v_p_u2080_906_, v_pos_907_, v_h_908_);
lean_dec(v_pos_907_);
lean_dec(v_p_u2080_906_);
lean_dec_ref(v_s_905_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg(lean_object* v_pos_910_){
_start:
{
lean_inc(v_pos_910_);
return v_pos_910_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg___boxed(lean_object* v_pos_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_String_Slice_Pos_ofSliceTo___redArg(v_pos_911_);
lean_dec(v_pos_911_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo(lean_object* v_s_913_, lean_object* v_p_u2080_914_, lean_object* v_pos_915_){
_start:
{
lean_inc(v_pos_915_);
return v_pos_915_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___boxed(lean_object* v_s_916_, lean_object* v_p_u2080_917_, lean_object* v_pos_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_String_Slice_Pos_ofSliceTo(v_s_916_, v_p_u2080_917_, v_pos_918_);
lean_dec(v_pos_918_);
lean_dec(v_p_u2080_917_);
lean_dec_ref(v_s_916_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg(lean_object* v_pos_920_){
_start:
{
lean_inc(v_pos_920_);
return v_pos_920_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg___boxed(lean_object* v_pos_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_String_Slice_Pos_ofReplaceEnd___redArg(v_pos_921_);
lean_dec(v_pos_921_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd(lean_object* v_s_923_, lean_object* v_p_u2080_924_, lean_object* v_pos_925_){
_start:
{
lean_inc(v_pos_925_);
return v_pos_925_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___boxed(lean_object* v_s_926_, lean_object* v_p_u2080_927_, lean_object* v_pos_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_String_Slice_Pos_ofReplaceEnd(v_s_926_, v_p_u2080_927_, v_pos_928_);
lean_dec(v_pos_928_);
lean_dec(v_p_u2080_927_);
lean_dec_ref(v_s_926_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg(lean_object* v_pos_930_){
_start:
{
lean_inc(v_pos_930_);
return v_pos_930_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg___boxed(lean_object* v_pos_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_String_Slice_Pos_sliceTo___redArg(v_pos_931_);
lean_dec(v_pos_931_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo(lean_object* v_s_933_, lean_object* v_p_u2080_934_, lean_object* v_pos_935_, lean_object* v_h_936_){
_start:
{
lean_inc(v_pos_935_);
return v_pos_935_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___boxed(lean_object* v_s_937_, lean_object* v_p_u2080_938_, lean_object* v_pos_939_, lean_object* v_h_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_String_Slice_Pos_sliceTo(v_s_937_, v_p_u2080_938_, v_pos_939_, v_h_940_);
lean_dec(v_pos_939_);
lean_dec(v_p_u2080_938_);
lean_dec_ref(v_s_937_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg(lean_object* v_pos_942_){
_start:
{
lean_inc(v_pos_942_);
return v_pos_942_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg___boxed(lean_object* v_pos_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_String_Slice_Pos_toReplaceEnd___redArg(v_pos_943_);
lean_dec(v_pos_943_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd(lean_object* v_s_945_, lean_object* v_p_u2080_946_, lean_object* v_pos_947_, lean_object* v_h_948_){
_start:
{
lean_inc(v_pos_947_);
return v_pos_947_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___boxed(lean_object* v_s_949_, lean_object* v_p_u2080_950_, lean_object* v_pos_951_, lean_object* v_h_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_String_Slice_Pos_toReplaceEnd(v_s_949_, v_p_u2080_950_, v_pos_951_, v_h_952_);
lean_dec(v_pos_951_);
lean_dec(v_p_u2080_950_);
lean_dec_ref(v_s_949_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg(lean_object* v_s_954_, lean_object* v_pos_955_){
_start:
{
lean_object* v_str_956_; lean_object* v_startInclusive_957_; lean_object* v___x_958_; uint8_t v___x_959_; uint8_t v___x_960_; uint8_t v___x_961_; uint8_t v___x_962_; uint8_t v___x_963_; 
v_str_956_ = lean_ctor_get(v_s_954_, 0);
v_startInclusive_957_ = lean_ctor_get(v_s_954_, 1);
v___x_958_ = lean_nat_add(v_startInclusive_957_, v_pos_955_);
v___x_959_ = lean_string_get_byte_fast(v_str_956_, v___x_958_);
v___x_960_ = 128;
v___x_961_ = lean_uint8_land(v___x_959_, v___x_960_);
v___x_962_ = 0;
v___x_963_ = lean_uint8_dec_eq(v___x_961_, v___x_962_);
if (v___x_963_ == 0)
{
uint8_t v___x_964_; uint8_t v___x_965_; uint8_t v___x_966_; uint8_t v___x_967_; 
v___x_964_ = 224;
v___x_965_ = lean_uint8_land(v___x_959_, v___x_964_);
v___x_966_ = 192;
v___x_967_ = lean_uint8_dec_eq(v___x_965_, v___x_966_);
if (v___x_967_ == 0)
{
uint8_t v___x_968_; uint8_t v___x_969_; uint8_t v___x_970_; 
v___x_968_ = 240;
v___x_969_ = lean_uint8_land(v___x_959_, v___x_968_);
v___x_970_ = lean_uint8_dec_eq(v___x_969_, v___x_964_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = lean_unsigned_to_nat(4u);
v___x_972_ = lean_nat_add(v_pos_955_, v___x_971_);
return v___x_972_;
}
else
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = lean_unsigned_to_nat(3u);
v___x_974_ = lean_nat_add(v_pos_955_, v___x_973_);
return v___x_974_;
}
}
else
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_unsigned_to_nat(2u);
v___x_976_ = lean_nat_add(v_pos_955_, v___x_975_);
return v___x_976_;
}
}
else
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = lean_unsigned_to_nat(1u);
v___x_978_ = lean_nat_add(v_pos_955_, v___x_977_);
return v___x_978_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg___boxed(lean_object* v_s_979_, lean_object* v_pos_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_String_Slice_Pos_next___redArg(v_s_979_, v_pos_980_);
lean_dec(v_pos_980_);
lean_dec_ref(v_s_979_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next(lean_object* v_s_982_, lean_object* v_pos_983_, lean_object* v_h_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_String_Slice_Pos_next___redArg(v_s_982_, v_pos_983_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___boxed(lean_object* v_s_986_, lean_object* v_pos_987_, lean_object* v_h_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_String_Slice_Pos_next(v_s_986_, v_pos_987_, v_h_988_);
lean_dec(v_pos_987_);
lean_dec_ref(v_s_986_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f(lean_object* v_s_990_, lean_object* v_pos_991_){
_start:
{
lean_object* v_startInclusive_992_; lean_object* v_endExclusive_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v_startInclusive_992_ = lean_ctor_get(v_s_990_, 1);
v_endExclusive_993_ = lean_ctor_get(v_s_990_, 2);
v___x_994_ = lean_nat_sub(v_endExclusive_993_, v_startInclusive_992_);
v___x_995_ = lean_nat_dec_eq(v_pos_991_, v___x_994_);
lean_dec(v___x_994_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = l_String_Slice_Pos_next___redArg(v_s_990_, v_pos_991_);
v___x_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
return v___x_997_;
}
else
{
lean_object* v___x_998_; 
v___x_998_ = lean_box(0);
return v___x_998_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f___boxed(lean_object* v_s_999_, lean_object* v_pos_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_String_Slice_Pos_next_x3f(v_s_999_, v_pos_1000_);
lean_dec(v_pos_1000_);
lean_dec_ref(v_s_999_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(lean_object* v_msg_1002_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_unsigned_to_nat(0u);
v___x_1004_ = lean_panic_fn(v___x_1003_, v_msg_1002_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0(lean_object* v_s_1005_, lean_object* v_msg_1006_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v_msg_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___boxed(lean_object* v_s_1008_, lean_object* v_msg_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0(v_s_1008_, v_msg_1009_);
lean_dec_ref(v_s_1008_);
return v_res_1010_;
}
}
static lean_object* _init_l_String_Slice_Pos_next_x21___closed__2(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1013_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__1));
v___x_1014_ = lean_unsigned_to_nat(29u);
v___x_1015_ = lean_unsigned_to_nat(1594u);
v___x_1016_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__0));
v___x_1017_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1018_ = l_mkPanicMessageWithDecl(v___x_1017_, v___x_1016_, v___x_1015_, v___x_1014_, v___x_1013_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21(lean_object* v_s_1019_, lean_object* v_pos_1020_){
_start:
{
lean_object* v_startInclusive_1021_; lean_object* v_endExclusive_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v_startInclusive_1021_ = lean_ctor_get(v_s_1019_, 1);
v_endExclusive_1022_ = lean_ctor_get(v_s_1019_, 2);
v___x_1023_ = lean_nat_sub(v_endExclusive_1022_, v_startInclusive_1021_);
v___x_1024_ = lean_nat_dec_eq(v_pos_1020_, v___x_1023_);
lean_dec(v___x_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; 
v___x_1025_ = l_String_Slice_Pos_next___redArg(v_s_1019_, v_pos_1020_);
return v___x_1025_;
}
else
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = lean_obj_once(&l_String_Slice_Pos_next_x21___closed__2, &l_String_Slice_Pos_next_x21___closed__2_once, _init_l_String_Slice_Pos_next_x21___closed__2);
v___x_1027_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_1026_);
return v___x_1027_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21___boxed(lean_object* v_s_1028_, lean_object* v_pos_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_String_Slice_Pos_next_x21(v_s_1028_, v_pos_1029_);
lean_dec(v_pos_1029_);
lean_dec_ref(v_s_1028_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg(lean_object* v_s_1031_, lean_object* v_off_1032_){
_start:
{
uint8_t v___y_1034_; lean_object* v_str_1040_; lean_object* v_startInclusive_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; uint8_t v___x_1044_; uint8_t v___x_1045_; uint8_t v___x_1046_; uint8_t v___x_1047_; 
v_str_1040_ = lean_ctor_get(v_s_1031_, 0);
v_startInclusive_1041_ = lean_ctor_get(v_s_1031_, 1);
v___x_1042_ = lean_nat_add(v_startInclusive_1041_, v_off_1032_);
v___x_1043_ = lean_string_get_byte_fast(v_str_1040_, v___x_1042_);
v___x_1044_ = 128;
v___x_1045_ = lean_uint8_land(v___x_1043_, v___x_1044_);
v___x_1046_ = 0;
v___x_1047_ = lean_uint8_dec_eq(v___x_1045_, v___x_1046_);
if (v___x_1047_ == 0)
{
uint8_t v___x_1048_; uint8_t v___x_1049_; uint8_t v___x_1050_; uint8_t v___x_1051_; 
v___x_1048_ = 224;
v___x_1049_ = lean_uint8_land(v___x_1043_, v___x_1048_);
v___x_1050_ = 192;
v___x_1051_ = lean_uint8_dec_eq(v___x_1049_, v___x_1050_);
if (v___x_1051_ == 0)
{
uint8_t v___x_1052_; uint8_t v___x_1053_; uint8_t v___x_1054_; 
v___x_1052_ = 240;
v___x_1053_ = lean_uint8_land(v___x_1043_, v___x_1052_);
v___x_1054_ = lean_uint8_dec_eq(v___x_1053_, v___x_1048_);
if (v___x_1054_ == 0)
{
uint8_t v___x_1055_; uint8_t v___x_1056_; uint8_t v___x_1057_; 
v___x_1055_ = 248;
v___x_1056_ = lean_uint8_land(v___x_1043_, v___x_1055_);
v___x_1057_ = lean_uint8_dec_eq(v___x_1056_, v___x_1052_);
v___y_1034_ = v___x_1057_;
goto v___jp_1033_;
}
else
{
v___y_1034_ = v___x_1054_;
goto v___jp_1033_;
}
}
else
{
v___y_1034_ = v___x_1051_;
goto v___jp_1033_;
}
}
else
{
v___y_1034_ = v___x_1047_;
goto v___jp_1033_;
}
v___jp_1033_:
{
if (v___y_1034_ == 0)
{
lean_object* v_zero_1035_; uint8_t v_isZero_1036_; lean_object* v_one_1037_; lean_object* v_n_1038_; 
v_zero_1035_ = lean_unsigned_to_nat(0u);
v_isZero_1036_ = lean_nat_dec_eq(v_off_1032_, v_zero_1035_);
v_one_1037_ = lean_unsigned_to_nat(1u);
v_n_1038_ = lean_nat_sub(v_off_1032_, v_one_1037_);
lean_dec(v_off_1032_);
v_off_1032_ = v_n_1038_;
goto _start;
}
else
{
return v_off_1032_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg___boxed(lean_object* v_s_1058_, lean_object* v_off_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1058_, v_off_1059_);
lean_dec_ref(v_s_1058_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go(lean_object* v_s_1061_, lean_object* v_off_1062_, lean_object* v_h_u2081_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1061_, v_off_1062_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___boxed(lean_object* v_s_1065_, lean_object* v_off_1066_, lean_object* v_h_u2081_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_String_Slice_Pos_prevAux_go(v_s_1065_, v_off_1066_, v_h_u2081_1067_);
lean_dec_ref(v_s_1065_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg(lean_object* v_s_1069_, lean_object* v_pos_1070_){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1071_ = lean_unsigned_to_nat(1u);
v___x_1072_ = lean_nat_sub(v_pos_1070_, v___x_1071_);
v___x_1073_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1069_, v___x_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg___boxed(lean_object* v_s_1074_, lean_object* v_pos_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_String_Slice_Pos_prevAux___redArg(v_s_1074_, v_pos_1075_);
lean_dec(v_pos_1075_);
lean_dec_ref(v_s_1074_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux(lean_object* v_s_1077_, lean_object* v_pos_1078_, lean_object* v_h_1079_){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1080_ = lean_unsigned_to_nat(1u);
v___x_1081_ = lean_nat_sub(v_pos_1078_, v___x_1080_);
v___x_1082_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1077_, v___x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___boxed(lean_object* v_s_1083_, lean_object* v_pos_1084_, lean_object* v_h_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_String_Slice_Pos_prevAux(v_s_1083_, v_pos_1084_, v_h_1085_);
lean_dec(v_pos_1084_);
lean_dec_ref(v_s_1083_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(lean_object* v_off_1087_, lean_object* v_h__1_1088_, lean_object* v_h__2_1089_){
_start:
{
lean_object* v_zero_1090_; uint8_t v_isZero_1091_; 
v_zero_1090_ = lean_unsigned_to_nat(0u);
v_isZero_1091_ = lean_nat_dec_eq(v_off_1087_, v_zero_1090_);
if (v_isZero_1091_ == 1)
{
lean_object* v___x_1092_; 
lean_dec(v_h__2_1089_);
v___x_1092_ = lean_apply_3(v_h__1_1088_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1092_;
}
else
{
lean_object* v_one_1093_; lean_object* v_n_1094_; lean_object* v___x_1095_; 
lean_dec(v_h__1_1088_);
v_one_1093_ = lean_unsigned_to_nat(1u);
v_n_1094_ = lean_nat_sub(v_off_1087_, v_one_1093_);
v___x_1095_ = lean_apply_4(v_h__2_1089_, v_n_1094_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1095_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg___boxed(lean_object* v_off_1096_, lean_object* v_h__1_1097_, lean_object* v_h__2_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(v_off_1096_, v_h__1_1097_, v_h__2_1098_);
lean_dec(v_off_1096_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(lean_object* v_s_1100_, lean_object* v_motive_1101_, lean_object* v_off_1102_, lean_object* v_h_u2081_1103_, lean_object* v_hbyte_1104_, lean_object* v_this_1105_, lean_object* v_h__1_1106_, lean_object* v_h__2_1107_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(v_off_1102_, v_h__1_1106_, v_h__2_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___boxed(lean_object* v_s_1109_, lean_object* v_motive_1110_, lean_object* v_off_1111_, lean_object* v_h_u2081_1112_, lean_object* v_hbyte_1113_, lean_object* v_this_1114_, lean_object* v_h__1_1115_, lean_object* v_h__2_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(v_s_1109_, v_motive_1110_, v_off_1111_, v_h_u2081_1112_, v_hbyte_1113_, v_this_1114_, v_h__1_1115_, v_h__2_1116_);
lean_dec(v_off_1111_);
lean_dec_ref(v_s_1109_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg(lean_object* v_off_1118_){
_start:
{
lean_inc(v_off_1118_);
return v_off_1118_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg___boxed(lean_object* v_off_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_String_Slice_pos___redArg(v_off_1119_);
lean_dec(v_off_1119_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos(lean_object* v_s_1121_, lean_object* v_off_1122_, lean_object* v_h_1123_){
_start:
{
lean_inc(v_off_1122_);
return v_off_1122_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___boxed(lean_object* v_s_1124_, lean_object* v_off_1125_, lean_object* v_h_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_String_Slice_pos(v_s_1124_, v_off_1125_, v_h_1126_);
lean_dec(v_off_1125_);
lean_dec_ref(v_s_1124_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f(lean_object* v_s_1128_, lean_object* v_off_1129_){
_start:
{
uint8_t v___x_1130_; 
v___x_1130_ = l_String_Pos_Raw_isValidForSlice(v_s_1128_, v_off_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; 
lean_dec(v_off_1129_);
v___x_1131_ = lean_box(0);
return v___x_1131_;
}
else
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1132_, 0, v_off_1129_);
return v___x_1132_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f___boxed(lean_object* v_s_1133_, lean_object* v_off_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_String_Slice_pos_x3f(v_s_1133_, v_off_1134_);
lean_dec_ref(v_s_1133_);
return v_res_1135_;
}
}
static lean_object* _init_l_String_Slice_pos_x21___closed__2(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1138_ = ((lean_object*)(l_String_Slice_pos_x21___closed__1));
v___x_1139_ = lean_unsigned_to_nat(4u);
v___x_1140_ = lean_unsigned_to_nat(1682u);
v___x_1141_ = ((lean_object*)(l_String_Slice_pos_x21___closed__0));
v___x_1142_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1143_ = l_mkPanicMessageWithDecl(v___x_1142_, v___x_1141_, v___x_1140_, v___x_1139_, v___x_1138_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21(lean_object* v_s_1144_, lean_object* v_off_1145_){
_start:
{
uint8_t v___x_1146_; 
v___x_1146_ = l_String_Pos_Raw_isValidForSlice(v_s_1144_, v_off_1145_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = lean_obj_once(&l_String_Slice_pos_x21___closed__2, &l_String_Slice_pos_x21___closed__2_once, _init_l_String_Slice_pos_x21___closed__2);
v___x_1148_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_1147_);
return v___x_1148_;
}
else
{
lean_inc(v_off_1145_);
return v_off_1145_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21___boxed(lean_object* v_s_1149_, lean_object* v_off_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_String_Slice_pos_x21(v_s_1149_, v_off_1150_);
lean_dec(v_off_1150_);
lean_dec_ref(v_s_1149_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next___boxed(lean_object* v_s_1155_, lean_object* v_pos_1156_, lean_object* v_h_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = lean_string_utf8_next_fast(v_s_1155_, v_pos_1156_);
lean_dec(v_pos_1156_);
lean_dec_ref(v_s_1155_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x3f(lean_object* v_s_1159_, lean_object* v_pos_1160_){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1161_ = lean_unsigned_to_nat(0u);
v___x_1162_ = lean_string_utf8_byte_size(v_s_1159_);
v___x_1163_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1163_, 0, v_s_1159_);
lean_ctor_set(v___x_1163_, 1, v___x_1161_);
lean_ctor_set(v___x_1163_, 2, v___x_1162_);
v___x_1164_ = l_String_Slice_Pos_next_x3f(v___x_1163_, v_pos_1160_);
lean_dec_ref(v___x_1163_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_box(0);
return v___x_1165_;
}
else
{
lean_object* v_val_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
v_val_1166_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1164_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_val_1166_);
lean_dec(v___x_1164_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_val_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x3f___boxed(lean_object* v_s_1174_, lean_object* v_pos_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_String_Pos_next_x3f(v_s_1174_, v_pos_1175_);
lean_dec(v_pos_1175_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21(lean_object* v_s_1177_, lean_object* v_pos_1178_){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1179_ = lean_unsigned_to_nat(0u);
v___x_1180_ = lean_string_utf8_byte_size(v_s_1177_);
v___x_1181_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1181_, 0, v_s_1177_);
lean_ctor_set(v___x_1181_, 1, v___x_1179_);
lean_ctor_set(v___x_1181_, 2, v___x_1180_);
v___x_1182_ = l_String_Slice_Pos_next_x21(v___x_1181_, v_pos_1178_);
lean_dec_ref(v___x_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21___boxed(lean_object* v_s_1183_, lean_object* v_pos_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_String_Pos_next_x21(v_s_1183_, v_pos_1184_);
lean_dec(v_pos_1184_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg(lean_object* v_off_1186_){
_start:
{
lean_inc(v_off_1186_);
return v_off_1186_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg___boxed(lean_object* v_off_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_String_pos___redArg(v_off_1187_);
lean_dec(v_off_1187_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_String_pos(lean_object* v_s_1189_, lean_object* v_off_1190_, lean_object* v_h_1191_){
_start:
{
lean_inc(v_off_1190_);
return v_off_1190_;
}
}
LEAN_EXPORT lean_object* l_String_pos___boxed(lean_object* v_s_1192_, lean_object* v_off_1193_, lean_object* v_h_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_String_pos(v_s_1192_, v_off_1193_, v_h_1194_);
lean_dec(v_off_1193_);
lean_dec_ref(v_s_1192_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x3f(lean_object* v_s_1196_, lean_object* v_off_1197_){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = lean_string_utf8_byte_size(v_s_1196_);
v___x_1200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1200_, 0, v_s_1196_);
lean_ctor_set(v___x_1200_, 1, v___x_1198_);
lean_ctor_set(v___x_1200_, 2, v___x_1199_);
v___x_1201_ = l_String_Slice_pos_x3f(v___x_1200_, v_off_1197_);
lean_dec_ref(v___x_1200_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v___x_1202_; 
v___x_1202_ = lean_box(0);
return v___x_1202_;
}
else
{
lean_object* v_val_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
v_val_1203_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1201_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_val_1203_);
lean_dec(v___x_1201_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_val_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_pos_x21(lean_object* v_s_1211_, lean_object* v_off_1212_){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1214_ = lean_string_utf8_byte_size(v_s_1211_);
v___x_1215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1215_, 0, v_s_1211_);
lean_ctor_set(v___x_1215_, 1, v___x_1213_);
lean_ctor_set(v___x_1215_, 2, v___x_1214_);
v___x_1216_ = l_String_Slice_pos_x21(v___x_1215_, v_off_1212_);
lean_dec_ref(v___x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x21___boxed(lean_object* v_s_1217_, lean_object* v_off_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_String_pos_x21(v_s_1217_, v_off_1218_);
lean_dec(v_off_1218_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg(lean_object* v_pos_1220_){
_start:
{
lean_inc(v_pos_1220_);
return v_pos_1220_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg___boxed(lean_object* v_pos_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_String_Slice_Pos_cast___redArg(v_pos_1221_);
lean_dec(v_pos_1221_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast(lean_object* v_s_1223_, lean_object* v_t_1224_, lean_object* v_pos_1225_, lean_object* v_h_1226_){
_start:
{
lean_inc(v_pos_1225_);
return v_pos_1225_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___boxed(lean_object* v_s_1227_, lean_object* v_t_1228_, lean_object* v_pos_1229_, lean_object* v_h_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_String_Slice_Pos_cast(v_s_1227_, v_t_1228_, v_pos_1229_, v_h_1230_);
lean_dec(v_pos_1229_);
lean_dec_ref(v_t_1228_);
lean_dec_ref(v_s_1227_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg(lean_object* v_pos_1232_){
_start:
{
lean_inc(v_pos_1232_);
return v_pos_1232_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg___boxed(lean_object* v_pos_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_String_Pos_cast___redArg(v_pos_1233_);
lean_dec(v_pos_1233_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast(lean_object* v_s_1235_, lean_object* v_t_1236_, lean_object* v_pos_1237_, lean_object* v_h_1238_){
_start:
{
lean_inc(v_pos_1237_);
return v_pos_1237_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___boxed(lean_object* v_s_1239_, lean_object* v_t_1240_, lean_object* v_pos_1241_, lean_object* v_h_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_String_Pos_cast(v_s_1239_, v_t_1240_, v_pos_1241_, v_h_1242_);
lean_dec(v_pos_1241_);
lean_dec_ref(v_t_1240_);
lean_dec_ref(v_s_1239_);
return v_res_1243_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_Raw_utf8GetAux(lean_object* v_x_1244_, lean_object* v_x_1245_, lean_object* v_x_1246_){
_start:
{
if (lean_obj_tag(v_x_1244_) == 0)
{
uint32_t v___x_1247_; 
lean_dec(v_x_1245_);
v___x_1247_ = 65;
return v___x_1247_;
}
else
{
lean_object* v_head_1248_; lean_object* v_tail_1249_; uint8_t v___x_1250_; 
v_head_1248_ = lean_ctor_get(v_x_1244_, 0);
v_tail_1249_ = lean_ctor_get(v_x_1244_, 1);
v___x_1250_ = lean_nat_dec_eq(v_x_1245_, v_x_1246_);
if (v___x_1250_ == 0)
{
uint32_t v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = lean_unbox_uint32(v_head_1248_);
v___x_1252_ = l_Char_utf8Size(v___x_1251_);
v___x_1253_ = lean_nat_add(v_x_1245_, v___x_1252_);
lean_dec(v___x_1252_);
lean_dec(v_x_1245_);
v_x_1244_ = v_tail_1249_;
v_x_1245_ = v___x_1253_;
goto _start;
}
else
{
uint32_t v___x_1255_; 
lean_dec(v_x_1245_);
v___x_1255_ = lean_unbox_uint32(v_head_1248_);
return v___x_1255_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux___boxed(lean_object* v_x_1256_, lean_object* v_x_1257_, lean_object* v_x_1258_){
_start:
{
uint32_t v_res_1259_; lean_object* v_r_1260_; 
v_res_1259_ = l_String_Pos_Raw_utf8GetAux(v_x_1256_, v_x_1257_, v_x_1258_);
lean_dec(v_x_1258_);
lean_dec(v_x_1256_);
v_r_1260_ = lean_box_uint32(v_res_1259_);
return v_r_1260_;
}
}
LEAN_EXPORT uint32_t l_String_utf8GetAux(lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_){
_start:
{
uint32_t v___x_1264_; 
v___x_1264_ = l_String_Pos_Raw_utf8GetAux(v_a_1261_, v_a_1262_, v_a_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux___boxed(lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_){
_start:
{
uint32_t v_res_1268_; lean_object* v_r_1269_; 
v_res_1268_ = l_String_utf8GetAux(v_a_1265_, v_a_1266_, v_a_1267_);
lean_dec(v_a_1267_);
lean_dec(v_a_1265_);
v_r_1269_ = lean_box_uint32(v_res_1268_);
return v_r_1269_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get___boxed(lean_object* v_s_1272_, lean_object* v_p_1273_){
_start:
{
uint32_t v_res_1274_; lean_object* v_r_1275_; 
v_res_1274_ = lean_string_utf8_get(v_s_1272_, v_p_1273_);
lean_dec(v_p_1273_);
lean_dec_ref(v_s_1272_);
v_r_1275_ = lean_box_uint32(v_res_1274_);
return v_r_1275_;
}
}
LEAN_EXPORT lean_object* l_String_get___boxed(lean_object* v_s_1278_, lean_object* v_p_1279_){
_start:
{
uint32_t v_res_1280_; lean_object* v_r_1281_; 
v_res_1280_ = lean_string_utf8_get(v_s_1278_, v_p_1279_);
lean_dec(v_p_1279_);
lean_dec_ref(v_s_1278_);
v_r_1281_ = lean_box_uint32(v_res_1280_);
return v_r_1281_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f(lean_object* v_x_1282_, lean_object* v_x_1283_, lean_object* v_x_1284_){
_start:
{
if (lean_obj_tag(v_x_1282_) == 0)
{
lean_object* v___x_1285_; 
lean_dec(v_x_1283_);
v___x_1285_ = lean_box(0);
return v___x_1285_;
}
else
{
lean_object* v_head_1286_; lean_object* v_tail_1287_; uint8_t v___x_1288_; 
v_head_1286_ = lean_ctor_get(v_x_1282_, 0);
v_tail_1287_ = lean_ctor_get(v_x_1282_, 1);
v___x_1288_ = lean_nat_dec_eq(v_x_1283_, v_x_1284_);
if (v___x_1288_ == 0)
{
uint32_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1289_ = lean_unbox_uint32(v_head_1286_);
v___x_1290_ = l_Char_utf8Size(v___x_1289_);
v___x_1291_ = lean_nat_add(v_x_1283_, v___x_1290_);
lean_dec(v___x_1290_);
lean_dec(v_x_1283_);
v_x_1282_ = v_tail_1287_;
v_x_1283_ = v___x_1291_;
goto _start;
}
else
{
lean_object* v___x_1293_; 
lean_dec(v_x_1283_);
lean_inc(v_head_1286_);
v___x_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1293_, 0, v_head_1286_);
return v___x_1293_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f___boxed(lean_object* v_x_1294_, lean_object* v_x_1295_, lean_object* v_x_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_String_Pos_Raw_utf8GetAux_x3f(v_x_1294_, v_x_1295_, v_x_1296_);
lean_dec(v_x_1296_);
lean_dec(v_x_1294_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f(lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_String_Pos_Raw_utf8GetAux_x3f(v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f___boxed(lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_String_utf8GetAux_x3f(v_a_1302_, v_a_1303_, v_a_1304_);
lean_dec(v_a_1304_);
lean_dec(v_a_1302_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1308_, lean_object* v_a_00___x40___internal___hyg_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1308_, v_a_00___x40___internal___hyg_1309_);
lean_dec(v_a_00___x40___internal___hyg_1309_);
lean_dec_ref(v_a_00___x40___internal___hyg_1308_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_String_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1313_, lean_object* v_a_00___x40___internal___hyg_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1313_, v_a_00___x40___internal___hyg_1314_);
lean_dec(v_a_00___x40___internal___hyg_1314_);
lean_dec_ref(v_a_00___x40___internal___hyg_1313_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x21___boxed(lean_object* v_s_1318_, lean_object* v_p_1319_){
_start:
{
uint32_t v_res_1320_; lean_object* v_r_1321_; 
v_res_1320_ = lean_string_utf8_get_bang(v_s_1318_, v_p_1319_);
lean_dec(v_p_1319_);
lean_dec_ref(v_s_1318_);
v_r_1321_ = lean_box_uint32(v_res_1320_);
return v_r_1321_;
}
}
LEAN_EXPORT lean_object* l_String_get_x21___boxed(lean_object* v_s_1324_, lean_object* v_p_1325_){
_start:
{
uint32_t v_res_1326_; lean_object* v_r_1327_; 
v_res_1326_ = lean_string_utf8_get_bang(v_s_1324_, v_p_1325_);
lean_dec(v_p_1325_);
lean_dec_ref(v_s_1324_);
v_r_1327_ = lean_box_uint32(v_res_1326_);
return v_r_1327_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux(uint32_t v_c_x27_1328_, lean_object* v_x_1329_, lean_object* v_x_1330_, lean_object* v_x_1331_){
_start:
{
if (lean_obj_tag(v_x_1329_) == 0)
{
return v_x_1329_;
}
else
{
lean_object* v_head_1332_; lean_object* v_tail_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1349_; 
v_head_1332_ = lean_ctor_get(v_x_1329_, 0);
v_tail_1333_ = lean_ctor_get(v_x_1329_, 1);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_x_1329_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1335_ = v_x_1329_;
v_isShared_1336_ = v_isSharedCheck_1349_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_tail_1333_);
lean_inc(v_head_1332_);
lean_dec(v_x_1329_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1349_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
uint8_t v___x_1337_; 
v___x_1337_ = lean_nat_dec_eq(v_x_1330_, v_x_1331_);
if (v___x_1337_ == 0)
{
uint32_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1343_; 
v___x_1338_ = lean_unbox_uint32(v_head_1332_);
v___x_1339_ = l_Char_utf8Size(v___x_1338_);
v___x_1340_ = lean_nat_add(v_x_1330_, v___x_1339_);
lean_dec(v___x_1339_);
v___x_1341_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1328_, v_tail_1333_, v___x_1340_, v_x_1331_);
lean_dec(v___x_1340_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 1, v___x_1341_);
v___x_1343_ = v___x_1335_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_head_1332_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
else
{
lean_object* v___x_1345_; lean_object* v___x_1347_; 
lean_dec(v_head_1332_);
v___x_1345_ = lean_box_uint32(v_c_x27_1328_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1345_);
v___x_1347_ = v___x_1335_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_tail_1333_);
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
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux___boxed(lean_object* v_c_x27_1350_, lean_object* v_x_1351_, lean_object* v_x_1352_, lean_object* v_x_1353_){
_start:
{
uint32_t v_c_x27_boxed_1354_; lean_object* v_res_1355_; 
v_c_x27_boxed_1354_ = lean_unbox_uint32(v_c_x27_1350_);
lean_dec(v_c_x27_1350_);
v_res_1355_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_boxed_1354_, v_x_1351_, v_x_1352_, v_x_1353_);
lean_dec(v_x_1353_);
lean_dec(v_x_1352_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux(uint32_t v_c_x27_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux___boxed(lean_object* v_c_x27_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
uint32_t v_c_x27_boxed_1365_; lean_object* v_res_1366_; 
v_c_x27_boxed_1365_ = lean_unbox_uint32(v_c_x27_1361_);
lean_dec(v_c_x27_1361_);
v_res_1366_ = l_String_utf8SetAux(v_c_x27_boxed_1365_, v_a_1362_, v_a_1363_, v_a_1364_);
lean_dec(v_a_1364_);
lean_dec(v_a_1363_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg(lean_object* v_s_1367_, lean_object* v_pos_1368_){
_start:
{
lean_object* v_str_1369_; lean_object* v_startInclusive_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v_str_1369_ = lean_ctor_get(v_s_1367_, 0);
v_startInclusive_1370_ = lean_ctor_get(v_s_1367_, 1);
v___x_1371_ = lean_nat_add(v_startInclusive_1370_, v_pos_1368_);
v___x_1372_ = lean_string_utf8_next_fast(v_str_1369_, v___x_1371_);
lean_dec(v___x_1371_);
v___x_1373_ = lean_nat_sub(v___x_1372_, v_startInclusive_1370_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg___boxed(lean_object* v_s_1374_, lean_object* v_pos_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_String_Slice_Pos_nextFast___redArg(v_s_1374_, v_pos_1375_);
lean_dec(v_pos_1375_);
lean_dec_ref(v_s_1374_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast(lean_object* v_s_1377_, lean_object* v_pos_1378_, lean_object* v_h_1379_){
_start:
{
lean_object* v_str_1380_; lean_object* v_startInclusive_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_str_1380_ = lean_ctor_get(v_s_1377_, 0);
v_startInclusive_1381_ = lean_ctor_get(v_s_1377_, 1);
v___x_1382_ = lean_nat_add(v_startInclusive_1381_, v_pos_1378_);
v___x_1383_ = lean_string_utf8_next_fast(v_str_1380_, v___x_1382_);
lean_dec(v___x_1382_);
v___x_1384_ = lean_nat_sub(v___x_1383_, v_startInclusive_1381_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___boxed(lean_object* v_s_1385_, lean_object* v_pos_1386_, lean_object* v_h_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_String_Slice_Pos_nextFast(v_s_1385_, v_pos_1386_, v_h_1387_);
lean_dec(v_pos_1386_);
lean_dec_ref(v_s_1385_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_String_sliceTo(lean_object* v_s_1389_, lean_object* v_p_1390_){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = lean_unsigned_to_nat(0u);
v___x_1392_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1392_, 0, v_s_1389_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
lean_ctor_set(v___x_1392_, 2, v_p_1390_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_String_replaceEnd(lean_object* v_s_1393_, lean_object* v_p_1394_){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = lean_unsigned_to_nat(0u);
v___x_1396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1396_, 0, v_s_1393_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
lean_ctor_set(v___x_1396_, 2, v_p_1394_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_String_sliceFrom(lean_object* v_s_1397_, lean_object* v_p_1398_){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = lean_string_utf8_byte_size(v_s_1397_);
v___x_1400_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1400_, 0, v_s_1397_);
lean_ctor_set(v___x_1400_, 1, v_p_1398_);
lean_ctor_set(v___x_1400_, 2, v___x_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStart(lean_object* v_s_1401_, lean_object* v_p_1402_){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = lean_string_utf8_byte_size(v_s_1401_);
v___x_1404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1404_, 0, v_s_1401_);
lean_ctor_set(v___x_1404_, 1, v_p_1402_);
lean_ctor_set(v___x_1404_, 2, v___x_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_String_slice___redArg(lean_object* v_s_1405_, lean_object* v_startInclusive_1406_, lean_object* v_endExclusive_1407_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1408_, 0, v_s_1405_);
lean_ctor_set(v___x_1408_, 1, v_startInclusive_1406_);
lean_ctor_set(v___x_1408_, 2, v_endExclusive_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_String_slice(lean_object* v_s_1409_, lean_object* v_startInclusive_1410_, lean_object* v_endExclusive_1411_, lean_object* v_h_1412_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1413_, 0, v_s_1409_);
lean_ctor_set(v___x_1413_, 1, v_startInclusive_1410_);
lean_ctor_set(v___x_1413_, 2, v_endExclusive_1411_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x3f(lean_object* v_s_1414_, lean_object* v_startInclusive_1415_, lean_object* v_endExclusive_1416_){
_start:
{
uint8_t v___x_1417_; 
v___x_1417_ = lean_nat_dec_le(v_startInclusive_1415_, v_endExclusive_1416_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; 
lean_dec(v_endExclusive_1416_);
lean_dec(v_startInclusive_1415_);
lean_dec_ref(v_s_1414_);
v___x_1418_ = lean_box(0);
return v___x_1418_;
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1419_, 0, v_s_1414_);
lean_ctor_set(v___x_1419_, 1, v_startInclusive_1415_);
lean_ctor_set(v___x_1419_, 2, v_endExclusive_1416_);
v___x_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
return v___x_1420_;
}
}
}
LEAN_EXPORT lean_object* l_String_slice_x21(lean_object* v_s_1421_, lean_object* v_p_u2081_1422_, lean_object* v_p_u2082_1423_){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1424_ = lean_unsigned_to_nat(0u);
v___x_1425_ = lean_string_utf8_byte_size(v_s_1421_);
v___x_1426_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1426_, 0, v_s_1421_);
lean_ctor_set(v___x_1426_, 1, v___x_1424_);
lean_ctor_set(v___x_1426_, 2, v___x_1425_);
v___x_1427_ = l_String_Slice_slice_x21(v___x_1426_, v_p_u2081_1422_, v_p_u2082_1423_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x21___boxed(lean_object* v_s_1428_, lean_object* v_p_u2081_1429_, lean_object* v_p_u2082_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_String_slice_x21(v_s_1428_, v_p_u2081_1429_, v_p_u2082_1430_);
lean_dec(v_p_u2082_1430_);
lean_dec(v_p_u2081_1429_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21(lean_object* v_s_1432_, lean_object* v_p_u2081_1433_, lean_object* v_p_u2082_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_String_slice_x21(v_s_1432_, v_p_u2081_1433_, v_p_u2082_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21___boxed(lean_object* v_s_1436_, lean_object* v_p_u2081_1437_, lean_object* v_p_u2082_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_String_replaceStartEnd_x21(v_s_1436_, v_p_u2081_1437_, v_p_u2082_1438_);
lean_dec(v_p_u2082_1438_);
lean_dec(v_p_u2081_1437_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg(lean_object* v_p_u2080_1440_, lean_object* v_pos_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_nat_add(v_p_u2080_1440_, v_pos_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg___boxed(lean_object* v_p_u2080_1443_, lean_object* v_pos_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_String_Pos_ofSliceFrom___redArg(v_p_u2080_1443_, v_pos_1444_);
lean_dec(v_pos_1444_);
lean_dec(v_p_u2080_1443_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom(lean_object* v_s_1446_, lean_object* v_p_u2080_1447_, lean_object* v_pos_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_nat_add(v_p_u2080_1447_, v_pos_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___boxed(lean_object* v_s_1450_, lean_object* v_p_u2080_1451_, lean_object* v_pos_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_String_Pos_ofSliceFrom(v_s_1450_, v_p_u2080_1451_, v_pos_1452_);
lean_dec(v_pos_1452_);
lean_dec(v_p_u2080_1451_);
lean_dec_ref(v_s_1450_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg(lean_object* v_p_u2080_1454_, lean_object* v_pos_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = lean_nat_add(v_p_u2080_1454_, v_pos_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg___boxed(lean_object* v_p_u2080_1457_, lean_object* v_pos_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_String_Pos_ofReplaceStart___redArg(v_p_u2080_1457_, v_pos_1458_);
lean_dec(v_pos_1458_);
lean_dec(v_p_u2080_1457_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart(lean_object* v_s_1460_, lean_object* v_p_u2080_1461_, lean_object* v_pos_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_nat_add(v_p_u2080_1461_, v_pos_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___boxed(lean_object* v_s_1464_, lean_object* v_p_u2080_1465_, lean_object* v_pos_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_String_Pos_ofReplaceStart(v_s_1464_, v_p_u2080_1465_, v_pos_1466_);
lean_dec(v_pos_1466_);
lean_dec(v_p_u2080_1465_);
lean_dec_ref(v_s_1464_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg(lean_object* v_p_u2080_1468_, lean_object* v_pos_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = lean_nat_sub(v_pos_1469_, v_p_u2080_1468_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg___boxed(lean_object* v_p_u2080_1471_, lean_object* v_pos_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_String_Pos_sliceFrom___redArg(v_p_u2080_1471_, v_pos_1472_);
lean_dec(v_pos_1472_);
lean_dec(v_p_u2080_1471_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom(lean_object* v_s_1474_, lean_object* v_p_u2080_1475_, lean_object* v_pos_1476_, lean_object* v_h_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = lean_nat_sub(v_pos_1476_, v_p_u2080_1475_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___boxed(lean_object* v_s_1479_, lean_object* v_p_u2080_1480_, lean_object* v_pos_1481_, lean_object* v_h_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_String_Pos_sliceFrom(v_s_1479_, v_p_u2080_1480_, v_pos_1481_, v_h_1482_);
lean_dec(v_pos_1481_);
lean_dec(v_p_u2080_1480_);
lean_dec_ref(v_s_1479_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg(lean_object* v_p_u2080_1484_, lean_object* v_pos_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_nat_sub(v_pos_1485_, v_p_u2080_1484_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg___boxed(lean_object* v_p_u2080_1487_, lean_object* v_pos_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_String_Pos_toReplaceStart___redArg(v_p_u2080_1487_, v_pos_1488_);
lean_dec(v_pos_1488_);
lean_dec(v_p_u2080_1487_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart(lean_object* v_s_1490_, lean_object* v_p_u2080_1491_, lean_object* v_pos_1492_, lean_object* v_h_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_nat_sub(v_pos_1492_, v_p_u2080_1491_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___boxed(lean_object* v_s_1495_, lean_object* v_p_u2080_1496_, lean_object* v_pos_1497_, lean_object* v_h_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_String_Pos_toReplaceStart(v_s_1495_, v_p_u2080_1496_, v_pos_1497_, v_h_1498_);
lean_dec(v_pos_1497_);
lean_dec(v_p_u2080_1496_);
lean_dec_ref(v_s_1495_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg(lean_object* v_pos_1500_){
_start:
{
lean_inc(v_pos_1500_);
return v_pos_1500_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg___boxed(lean_object* v_pos_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_String_Pos_ofSliceTo___redArg(v_pos_1501_);
lean_dec(v_pos_1501_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo(lean_object* v_s_1503_, lean_object* v_p_u2080_1504_, lean_object* v_pos_1505_){
_start:
{
lean_inc(v_pos_1505_);
return v_pos_1505_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___boxed(lean_object* v_s_1506_, lean_object* v_p_u2080_1507_, lean_object* v_pos_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_String_Pos_ofSliceTo(v_s_1506_, v_p_u2080_1507_, v_pos_1508_);
lean_dec(v_pos_1508_);
lean_dec(v_p_u2080_1507_);
lean_dec_ref(v_s_1506_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg(lean_object* v_pos_1510_){
_start:
{
lean_inc(v_pos_1510_);
return v_pos_1510_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg___boxed(lean_object* v_pos_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_String_Pos_ofReplaceEnd___redArg(v_pos_1511_);
lean_dec(v_pos_1511_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd(lean_object* v_s_1513_, lean_object* v_p_u2080_1514_, lean_object* v_pos_1515_){
_start:
{
lean_inc(v_pos_1515_);
return v_pos_1515_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___boxed(lean_object* v_s_1516_, lean_object* v_p_u2080_1517_, lean_object* v_pos_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_String_Pos_ofReplaceEnd(v_s_1516_, v_p_u2080_1517_, v_pos_1518_);
lean_dec(v_pos_1518_);
lean_dec(v_p_u2080_1517_);
lean_dec_ref(v_s_1516_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg(lean_object* v_pos_1520_){
_start:
{
lean_inc(v_pos_1520_);
return v_pos_1520_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg___boxed(lean_object* v_pos_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_String_Pos_sliceTo___redArg(v_pos_1521_);
lean_dec(v_pos_1521_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo(lean_object* v_s_1523_, lean_object* v_p_u2080_1524_, lean_object* v_pos_1525_, lean_object* v_h_1526_){
_start:
{
lean_inc(v_pos_1525_);
return v_pos_1525_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___boxed(lean_object* v_s_1527_, lean_object* v_p_u2080_1528_, lean_object* v_pos_1529_, lean_object* v_h_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_String_Pos_sliceTo(v_s_1527_, v_p_u2080_1528_, v_pos_1529_, v_h_1530_);
lean_dec(v_pos_1529_);
lean_dec(v_p_u2080_1528_);
lean_dec_ref(v_s_1527_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg(lean_object* v_pos_1532_){
_start:
{
lean_inc(v_pos_1532_);
return v_pos_1532_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg___boxed(lean_object* v_pos_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_String_Pos_toReplaceEnd___redArg(v_pos_1533_);
lean_dec(v_pos_1533_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd(lean_object* v_s_1535_, lean_object* v_p_u2080_1536_, lean_object* v_pos_1537_, lean_object* v_h_1538_){
_start:
{
lean_inc(v_pos_1537_);
return v_pos_1537_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___boxed(lean_object* v_s_1539_, lean_object* v_p_u2080_1540_, lean_object* v_pos_1541_, lean_object* v_h_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_String_Pos_toReplaceEnd(v_s_1539_, v_p_u2080_1540_, v_pos_1541_, v_h_1542_);
lean_dec(v_pos_1541_);
lean_dec(v_p_u2080_1540_);
lean_dec_ref(v_s_1539_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg(lean_object* v_p_u2080_1544_, lean_object* v_pos_1545_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = lean_nat_add(v_p_u2080_1544_, v_pos_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1547_, lean_object* v_pos_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_String_Slice_Pos_ofSlice___redArg(v_p_u2080_1547_, v_pos_1548_);
lean_dec(v_pos_1548_);
lean_dec(v_p_u2080_1547_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice(lean_object* v_s_1550_, lean_object* v_p_u2080_1551_, lean_object* v_p_u2081_1552_, lean_object* v_h_1553_, lean_object* v_pos_1554_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = lean_nat_add(v_p_u2080_1551_, v_pos_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___boxed(lean_object* v_s_1556_, lean_object* v_p_u2080_1557_, lean_object* v_p_u2081_1558_, lean_object* v_h_1559_, lean_object* v_pos_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_String_Slice_Pos_ofSlice(v_s_1556_, v_p_u2080_1557_, v_p_u2081_1558_, v_h_1559_, v_pos_1560_);
lean_dec(v_pos_1560_);
lean_dec(v_p_u2081_1558_);
lean_dec(v_p_u2080_1557_);
lean_dec_ref(v_s_1556_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg(lean_object* v_p_u2080_1562_, lean_object* v_pos_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_nat_add(v_p_u2080_1562_, v_pos_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1565_, lean_object* v_pos_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_String_Pos_ofSlice___redArg(v_p_u2080_1565_, v_pos_1566_);
lean_dec(v_pos_1566_);
lean_dec(v_p_u2080_1565_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice(lean_object* v_s_1568_, lean_object* v_p_u2080_1569_, lean_object* v_p_u2081_1570_, lean_object* v_h_1571_, lean_object* v_pos_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = lean_nat_add(v_p_u2080_1569_, v_pos_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___boxed(lean_object* v_s_1574_, lean_object* v_p_u2080_1575_, lean_object* v_p_u2081_1576_, lean_object* v_h_1577_, lean_object* v_pos_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_String_Pos_ofSlice(v_s_1574_, v_p_u2080_1575_, v_p_u2081_1576_, v_h_1577_, v_pos_1578_);
lean_dec(v_pos_1578_);
lean_dec(v_p_u2081_1576_);
lean_dec(v_p_u2080_1575_);
lean_dec_ref(v_s_1574_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg(lean_object* v_pos_1580_, lean_object* v_p_u2080_1581_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_nat_sub(v_pos_1580_, v_p_u2080_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg___boxed(lean_object* v_pos_1583_, lean_object* v_p_u2080_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_String_Slice_Pos_slice___redArg(v_pos_1583_, v_p_u2080_1584_);
lean_dec(v_p_u2080_1584_);
lean_dec(v_pos_1583_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice(lean_object* v_s_1586_, lean_object* v_pos_1587_, lean_object* v_p_u2080_1588_, lean_object* v_p_u2081_1589_, lean_object* v_h_u2081_1590_, lean_object* v_h_u2082_1591_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = lean_nat_sub(v_pos_1587_, v_p_u2080_1588_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___boxed(lean_object* v_s_1593_, lean_object* v_pos_1594_, lean_object* v_p_u2080_1595_, lean_object* v_p_u2081_1596_, lean_object* v_h_u2081_1597_, lean_object* v_h_u2082_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_String_Slice_Pos_slice(v_s_1593_, v_pos_1594_, v_p_u2080_1595_, v_p_u2081_1596_, v_h_u2081_1597_, v_h_u2082_1598_);
lean_dec(v_p_u2081_1596_);
lean_dec(v_p_u2080_1595_);
lean_dec(v_pos_1594_);
lean_dec_ref(v_s_1593_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg(lean_object* v_pos_1600_, lean_object* v_p_u2080_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = lean_nat_sub(v_pos_1600_, v_p_u2080_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg___boxed(lean_object* v_pos_1603_, lean_object* v_p_u2080_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_String_Pos_slice___redArg(v_pos_1603_, v_p_u2080_1604_);
lean_dec(v_p_u2080_1604_);
lean_dec(v_pos_1603_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice(lean_object* v_s_1606_, lean_object* v_pos_1607_, lean_object* v_p_u2080_1608_, lean_object* v_p_u2081_1609_, lean_object* v_h_u2081_1610_, lean_object* v_h_u2082_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_nat_sub(v_pos_1607_, v_p_u2080_1608_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___boxed(lean_object* v_s_1613_, lean_object* v_pos_1614_, lean_object* v_p_u2080_1615_, lean_object* v_p_u2081_1616_, lean_object* v_h_u2081_1617_, lean_object* v_h_u2082_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_String_Pos_slice(v_s_1613_, v_pos_1614_, v_p_u2080_1615_, v_p_u2081_1616_, v_h_u2081_1617_, v_h_u2082_1618_);
lean_dec(v_p_u2081_1616_);
lean_dec(v_p_u2080_1615_);
lean_dec(v_pos_1614_);
lean_dec_ref(v_s_1613_);
return v_res_1619_;
}
}
static lean_object* _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1622_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__1));
v___x_1623_ = lean_unsigned_to_nat(4u);
v___x_1624_ = lean_unsigned_to_nat(2611u);
v___x_1625_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__0));
v___x_1626_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1627_ = l_mkPanicMessageWithDecl(v___x_1626_, v___x_1625_, v___x_1624_, v___x_1623_, v___x_1622_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg(lean_object* v_pos_1628_, lean_object* v_p_u2080_1629_, lean_object* v_p_u2081_1630_){
_start:
{
uint8_t v___x_1635_; 
v___x_1635_ = lean_nat_dec_le(v_p_u2080_1629_, v_pos_1628_);
if (v___x_1635_ == 0)
{
goto v___jp_1631_;
}
else
{
uint8_t v___x_1636_; 
v___x_1636_ = lean_nat_dec_le(v_pos_1628_, v_p_u2081_1630_);
if (v___x_1636_ == 0)
{
goto v___jp_1631_;
}
else
{
lean_object* v___x_1637_; 
v___x_1637_ = lean_nat_sub(v_pos_1628_, v_p_u2080_1629_);
return v___x_1637_;
}
}
v___jp_1631_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1632_ = lean_unsigned_to_nat(0u);
v___x_1633_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1634_ = l_panic___redArg(v___x_1632_, v___x_1633_);
return v___x_1634_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1638_, lean_object* v_p_u2080_1639_, lean_object* v_p_u2081_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_String_Slice_Pos_sliceOrPanic___redArg(v_pos_1638_, v_p_u2080_1639_, v_p_u2081_1640_);
lean_dec(v_p_u2081_1640_);
lean_dec(v_p_u2080_1639_);
lean_dec(v_pos_1638_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic(lean_object* v_s_1642_, lean_object* v_pos_1643_, lean_object* v_p_u2080_1644_, lean_object* v_p_u2081_1645_, lean_object* v_h_1646_){
_start:
{
uint8_t v___x_1651_; 
v___x_1651_ = lean_nat_dec_le(v_p_u2080_1644_, v_pos_1643_);
if (v___x_1651_ == 0)
{
goto v___jp_1647_;
}
else
{
uint8_t v___x_1652_; 
v___x_1652_ = lean_nat_dec_le(v_pos_1643_, v_p_u2081_1645_);
if (v___x_1652_ == 0)
{
goto v___jp_1647_;
}
else
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_nat_sub(v_pos_1643_, v_p_u2080_1644_);
return v___x_1653_;
}
}
v___jp_1647_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1648_ = lean_unsigned_to_nat(0u);
v___x_1649_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1650_ = l_panic___redArg(v___x_1648_, v___x_1649_);
return v___x_1650_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___boxed(lean_object* v_s_1654_, lean_object* v_pos_1655_, lean_object* v_p_u2080_1656_, lean_object* v_p_u2081_1657_, lean_object* v_h_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_String_Slice_Pos_sliceOrPanic(v_s_1654_, v_pos_1655_, v_p_u2080_1656_, v_p_u2081_1657_, v_h_1658_);
lean_dec(v_p_u2081_1657_);
lean_dec(v_p_u2080_1656_);
lean_dec(v_pos_1655_);
lean_dec_ref(v_s_1654_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg(lean_object* v_pos_1660_, lean_object* v_p_u2080_1661_, lean_object* v_p_u2081_1662_){
_start:
{
uint8_t v___x_1667_; 
v___x_1667_ = lean_nat_dec_le(v_p_u2080_1661_, v_pos_1660_);
if (v___x_1667_ == 0)
{
goto v___jp_1663_;
}
else
{
uint8_t v___x_1668_; 
v___x_1668_ = lean_nat_dec_le(v_pos_1660_, v_p_u2081_1662_);
if (v___x_1668_ == 0)
{
goto v___jp_1663_;
}
else
{
lean_object* v___x_1669_; 
v___x_1669_ = lean_nat_sub(v_pos_1660_, v_p_u2080_1661_);
return v___x_1669_;
}
}
v___jp_1663_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1664_ = lean_unsigned_to_nat(0u);
v___x_1665_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1666_ = l_panic___redArg(v___x_1664_, v___x_1665_);
return v___x_1666_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1670_, lean_object* v_p_u2080_1671_, lean_object* v_p_u2081_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_String_Pos_sliceOrPanic___redArg(v_pos_1670_, v_p_u2080_1671_, v_p_u2081_1672_);
lean_dec(v_p_u2081_1672_);
lean_dec(v_p_u2080_1671_);
lean_dec(v_pos_1670_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic(lean_object* v_s_1674_, lean_object* v_pos_1675_, lean_object* v_p_u2080_1676_, lean_object* v_p_u2081_1677_, lean_object* v_h_1678_){
_start:
{
uint8_t v___x_1683_; 
v___x_1683_ = lean_nat_dec_le(v_p_u2080_1676_, v_pos_1675_);
if (v___x_1683_ == 0)
{
goto v___jp_1679_;
}
else
{
uint8_t v___x_1684_; 
v___x_1684_ = lean_nat_dec_le(v_pos_1675_, v_p_u2081_1677_);
if (v___x_1684_ == 0)
{
goto v___jp_1679_;
}
else
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_nat_sub(v_pos_1675_, v_p_u2080_1676_);
return v___x_1685_;
}
}
v___jp_1679_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1680_ = lean_unsigned_to_nat(0u);
v___x_1681_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1682_ = l_panic___redArg(v___x_1680_, v___x_1681_);
return v___x_1682_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___boxed(lean_object* v_s_1686_, lean_object* v_pos_1687_, lean_object* v_p_u2080_1688_, lean_object* v_p_u2081_1689_, lean_object* v_h_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_String_Pos_sliceOrPanic(v_s_1686_, v_pos_1687_, v_p_u2080_1688_, v_p_u2081_1689_, v_h_1690_);
lean_dec(v_p_u2081_1689_);
lean_dec(v_p_u2080_1688_);
lean_dec(v_pos_1687_);
lean_dec_ref(v_s_1686_);
return v_res_1691_;
}
}
static lean_object* _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1693_ = ((lean_object*)(l_String_Slice_slice_x21___closed__1));
v___x_1694_ = lean_unsigned_to_nat(4u);
v___x_1695_ = lean_unsigned_to_nat(2635u);
v___x_1696_ = ((lean_object*)(l_String_Slice_Pos_ofSlice_x21___redArg___closed__0));
v___x_1697_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1698_ = l_mkPanicMessageWithDecl(v___x_1697_, v___x_1696_, v___x_1695_, v___x_1694_, v___x_1693_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1699_, lean_object* v_p_u2081_1700_, lean_object* v_pos_1701_){
_start:
{
uint8_t v___x_1702_; 
v___x_1702_ = lean_nat_dec_le(v_p_u2080_1699_, v_p_u2081_1700_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1703_ = lean_unsigned_to_nat(0u);
v___x_1704_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1705_ = l_panic___redArg(v___x_1703_, v___x_1704_);
return v___x_1705_;
}
else
{
lean_object* v___x_1706_; 
v___x_1706_ = lean_nat_add(v_p_u2080_1699_, v_pos_1701_);
return v___x_1706_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1707_, lean_object* v_p_u2081_1708_, lean_object* v_pos_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_String_Slice_Pos_ofSlice_x21___redArg(v_p_u2080_1707_, v_p_u2081_1708_, v_pos_1709_);
lean_dec(v_pos_1709_);
lean_dec(v_p_u2081_1708_);
lean_dec(v_p_u2080_1707_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21(lean_object* v_s_1711_, lean_object* v_p_u2080_1712_, lean_object* v_p_u2081_1713_, lean_object* v_pos_1714_){
_start:
{
uint8_t v___x_1715_; 
v___x_1715_ = lean_nat_dec_le(v_p_u2080_1712_, v_p_u2081_1713_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1716_ = lean_unsigned_to_nat(0u);
v___x_1717_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1718_ = l_panic___redArg(v___x_1716_, v___x_1717_);
return v___x_1718_;
}
else
{
lean_object* v___x_1719_; 
v___x_1719_ = lean_nat_add(v_p_u2080_1712_, v_pos_1714_);
return v___x_1719_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___boxed(lean_object* v_s_1720_, lean_object* v_p_u2080_1721_, lean_object* v_p_u2081_1722_, lean_object* v_pos_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_String_Slice_Pos_ofSlice_x21(v_s_1720_, v_p_u2080_1721_, v_p_u2081_1722_, v_pos_1723_);
lean_dec(v_pos_1723_);
lean_dec(v_p_u2081_1722_);
lean_dec(v_p_u2080_1721_);
lean_dec_ref(v_s_1720_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1725_, lean_object* v_p_u2081_1726_, lean_object* v_pos_1727_){
_start:
{
uint8_t v___x_1728_; 
v___x_1728_ = lean_nat_dec_le(v_p_u2080_1725_, v_p_u2081_1726_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1729_ = lean_unsigned_to_nat(0u);
v___x_1730_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1731_ = l_panic___redArg(v___x_1729_, v___x_1730_);
return v___x_1731_;
}
else
{
lean_object* v___x_1732_; 
v___x_1732_ = lean_nat_add(v_p_u2080_1725_, v_pos_1727_);
return v___x_1732_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1733_, lean_object* v_p_u2081_1734_, lean_object* v_pos_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_String_Pos_ofSlice_x21___redArg(v_p_u2080_1733_, v_p_u2081_1734_, v_pos_1735_);
lean_dec(v_pos_1735_);
lean_dec(v_p_u2081_1734_);
lean_dec(v_p_u2080_1733_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21(lean_object* v_s_1737_, lean_object* v_p_u2080_1738_, lean_object* v_p_u2081_1739_, lean_object* v_pos_1740_){
_start:
{
uint8_t v___x_1741_; 
v___x_1741_ = lean_nat_dec_le(v_p_u2080_1738_, v_p_u2081_1739_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1742_ = lean_unsigned_to_nat(0u);
v___x_1743_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1744_ = l_panic___redArg(v___x_1742_, v___x_1743_);
return v___x_1744_;
}
else
{
lean_object* v___x_1745_; 
v___x_1745_ = lean_nat_add(v_p_u2080_1738_, v_pos_1740_);
return v___x_1745_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___boxed(lean_object* v_s_1746_, lean_object* v_p_u2080_1747_, lean_object* v_p_u2081_1748_, lean_object* v_pos_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_String_Pos_ofSlice_x21(v_s_1746_, v_p_u2080_1747_, v_p_u2081_1748_, v_pos_1749_);
lean_dec(v_pos_1749_);
lean_dec(v_p_u2081_1748_);
lean_dec(v_p_u2080_1747_);
lean_dec_ref(v_s_1746_);
return v_res_1750_;
}
}
static lean_object* _init_l_String_Slice_Pos_slice_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1753_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__1));
v___x_1754_ = lean_unsigned_to_nat(4u);
v___x_1755_ = lean_unsigned_to_nat(2653u);
v___x_1756_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__0));
v___x_1757_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1758_ = l_mkPanicMessageWithDecl(v___x_1757_, v___x_1756_, v___x_1755_, v___x_1754_, v___x_1753_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg(lean_object* v_pos_1759_, lean_object* v_p_u2080_1760_, lean_object* v_p_u2081_1761_){
_start:
{
uint8_t v___x_1766_; 
v___x_1766_ = lean_nat_dec_le(v_p_u2080_1760_, v_pos_1759_);
if (v___x_1766_ == 0)
{
goto v___jp_1762_;
}
else
{
uint8_t v___x_1767_; 
v___x_1767_ = lean_nat_dec_le(v_pos_1759_, v_p_u2081_1761_);
if (v___x_1767_ == 0)
{
goto v___jp_1762_;
}
else
{
lean_object* v___x_1768_; 
v___x_1768_ = lean_nat_sub(v_pos_1759_, v_p_u2080_1760_);
return v___x_1768_;
}
}
v___jp_1762_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1763_ = lean_unsigned_to_nat(0u);
v___x_1764_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1765_ = l_panic___redArg(v___x_1763_, v___x_1764_);
return v___x_1765_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1769_, lean_object* v_p_u2080_1770_, lean_object* v_p_u2081_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_String_Slice_Pos_slice_x21___redArg(v_pos_1769_, v_p_u2080_1770_, v_p_u2081_1771_);
lean_dec(v_p_u2081_1771_);
lean_dec(v_p_u2080_1770_);
lean_dec(v_pos_1769_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21(lean_object* v_s_1773_, lean_object* v_pos_1774_, lean_object* v_p_u2080_1775_, lean_object* v_p_u2081_1776_){
_start:
{
uint8_t v___x_1781_; 
v___x_1781_ = lean_nat_dec_le(v_p_u2080_1775_, v_pos_1774_);
if (v___x_1781_ == 0)
{
goto v___jp_1777_;
}
else
{
uint8_t v___x_1782_; 
v___x_1782_ = lean_nat_dec_le(v_pos_1774_, v_p_u2081_1776_);
if (v___x_1782_ == 0)
{
goto v___jp_1777_;
}
else
{
lean_object* v___x_1783_; 
v___x_1783_ = lean_nat_sub(v_pos_1774_, v_p_u2080_1775_);
return v___x_1783_;
}
}
v___jp_1777_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1778_ = lean_unsigned_to_nat(0u);
v___x_1779_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1780_ = l_panic___redArg(v___x_1778_, v___x_1779_);
return v___x_1780_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___boxed(lean_object* v_s_1784_, lean_object* v_pos_1785_, lean_object* v_p_u2080_1786_, lean_object* v_p_u2081_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_String_Slice_Pos_slice_x21(v_s_1784_, v_pos_1785_, v_p_u2080_1786_, v_p_u2081_1787_);
lean_dec(v_p_u2081_1787_);
lean_dec(v_p_u2080_1786_);
lean_dec(v_pos_1785_);
lean_dec_ref(v_s_1784_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg(lean_object* v_pos_1789_, lean_object* v_p_u2080_1790_, lean_object* v_p_u2081_1791_){
_start:
{
uint8_t v___x_1796_; 
v___x_1796_ = lean_nat_dec_le(v_p_u2080_1790_, v_pos_1789_);
if (v___x_1796_ == 0)
{
goto v___jp_1792_;
}
else
{
uint8_t v___x_1797_; 
v___x_1797_ = lean_nat_dec_le(v_pos_1789_, v_p_u2081_1791_);
if (v___x_1797_ == 0)
{
goto v___jp_1792_;
}
else
{
lean_object* v___x_1798_; 
v___x_1798_ = lean_nat_sub(v_pos_1789_, v_p_u2080_1790_);
return v___x_1798_;
}
}
v___jp_1792_:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1795_ = l_panic___redArg(v___x_1793_, v___x_1794_);
return v___x_1795_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1799_, lean_object* v_p_u2080_1800_, lean_object* v_p_u2081_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_String_Pos_slice_x21___redArg(v_pos_1799_, v_p_u2080_1800_, v_p_u2081_1801_);
lean_dec(v_p_u2081_1801_);
lean_dec(v_p_u2080_1800_);
lean_dec(v_pos_1799_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21(lean_object* v_s_1803_, lean_object* v_pos_1804_, lean_object* v_p_u2080_1805_, lean_object* v_p_u2081_1806_){
_start:
{
uint8_t v___x_1811_; 
v___x_1811_ = lean_nat_dec_le(v_p_u2080_1805_, v_pos_1804_);
if (v___x_1811_ == 0)
{
goto v___jp_1807_;
}
else
{
uint8_t v___x_1812_; 
v___x_1812_ = lean_nat_dec_le(v_pos_1804_, v_p_u2081_1806_);
if (v___x_1812_ == 0)
{
goto v___jp_1807_;
}
else
{
lean_object* v___x_1813_; 
v___x_1813_ = lean_nat_sub(v_pos_1804_, v_p_u2080_1805_);
return v___x_1813_;
}
}
v___jp_1807_:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = lean_unsigned_to_nat(0u);
v___x_1809_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1810_ = l_panic___redArg(v___x_1808_, v___x_1809_);
return v___x_1810_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___boxed(lean_object* v_s_1814_, lean_object* v_pos_1815_, lean_object* v_p_u2080_1816_, lean_object* v_p_u2081_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_String_Pos_slice_x21(v_s_1814_, v_pos_1815_, v_p_u2080_1816_, v_p_u2081_1817_);
lean_dec(v_p_u2081_1817_);
lean_dec(v_p_u2080_1816_);
lean_dec(v_pos_1815_);
lean_dec_ref(v_s_1814_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract(lean_object* v_s_1819_, lean_object* v_p_u2080_1820_, lean_object* v_p_u2081_1821_){
_start:
{
lean_object* v_str_1822_; lean_object* v_startInclusive_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v_str_1822_ = lean_ctor_get(v_s_1819_, 0);
v_startInclusive_1823_ = lean_ctor_get(v_s_1819_, 1);
v___x_1824_ = lean_nat_add(v_startInclusive_1823_, v_p_u2080_1820_);
v___x_1825_ = lean_nat_add(v_startInclusive_1823_, v_p_u2081_1821_);
v___x_1826_ = lean_string_utf8_extract(v_str_1822_, v___x_1824_, v___x_1825_);
lean_dec(v___x_1825_);
lean_dec(v___x_1824_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract___boxed(lean_object* v_s_1827_, lean_object* v_p_u2080_1828_, lean_object* v_p_u2081_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_String_Slice_extract(v_s_1827_, v_p_u2080_1828_, v_p_u2081_1829_);
lean_dec(v_p_u2081_1829_);
lean_dec(v_p_u2080_1828_);
lean_dec_ref(v_s_1827_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn(lean_object* v_s_1831_, lean_object* v_p_1832_, lean_object* v_n_1833_){
_start:
{
lean_object* v_str_1834_; lean_object* v_startInclusive_1835_; lean_object* v_endExclusive_1836_; lean_object* v_zero_1837_; uint8_t v_isZero_1838_; 
v_str_1834_ = lean_ctor_get(v_s_1831_, 0);
v_startInclusive_1835_ = lean_ctor_get(v_s_1831_, 1);
v_endExclusive_1836_ = lean_ctor_get(v_s_1831_, 2);
v_zero_1837_ = lean_unsigned_to_nat(0u);
v_isZero_1838_ = lean_nat_dec_eq(v_n_1833_, v_zero_1837_);
if (v_isZero_1838_ == 1)
{
lean_dec(v_n_1833_);
return v_p_1832_;
}
else
{
lean_object* v___x_1839_; uint8_t v___x_1840_; lean_object* v_one_1841_; lean_object* v_n_1842_; 
v___x_1839_ = lean_nat_sub(v_endExclusive_1836_, v_startInclusive_1835_);
v___x_1840_ = lean_nat_dec_eq(v_p_1832_, v___x_1839_);
lean_dec(v___x_1839_);
v_one_1841_ = lean_unsigned_to_nat(1u);
v_n_1842_ = lean_nat_sub(v_n_1833_, v_one_1841_);
lean_dec(v_n_1833_);
if (v___x_1840_ == 0)
{
goto v___jp_1843_;
}
else
{
if (v_isZero_1838_ == 0)
{
lean_dec(v_n_1842_);
return v_p_1832_;
}
else
{
goto v___jp_1843_;
}
}
v___jp_1843_:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = lean_nat_add(v_startInclusive_1835_, v_p_1832_);
lean_dec(v_p_1832_);
v___x_1845_ = lean_string_utf8_next_fast(v_str_1834_, v___x_1844_);
lean_dec(v___x_1844_);
v___x_1846_ = lean_nat_sub(v___x_1845_, v_startInclusive_1835_);
v_p_1832_ = v___x_1846_;
v_n_1833_ = v_n_1842_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn___boxed(lean_object* v_s_1848_, lean_object* v_p_1849_, lean_object* v_n_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_String_Slice_Pos_nextn(v_s_1848_, v_p_1849_, v_n_1850_);
lean_dec_ref(v_s_1848_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_nextn(lean_object* v_s_1852_, lean_object* v_p_1853_, lean_object* v_n_1854_){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1855_ = lean_unsigned_to_nat(0u);
v___x_1856_ = lean_string_utf8_byte_size(v_s_1852_);
v___x_1857_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1857_, 0, v_s_1852_);
lean_ctor_set(v___x_1857_, 1, v___x_1855_);
lean_ctor_set(v___x_1857_, 2, v___x_1856_);
v___x_1858_ = l_String_Slice_Pos_nextn(v___x_1857_, v_p_1853_, v_n_1854_);
lean_dec_ref(v___x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(lean_object* v_n_1859_, lean_object* v_h__1_1860_, lean_object* v_h__2_1861_){
_start:
{
lean_object* v_zero_1862_; uint8_t v_isZero_1863_; 
v_zero_1862_ = lean_unsigned_to_nat(0u);
v_isZero_1863_ = lean_nat_dec_eq(v_n_1859_, v_zero_1862_);
if (v_isZero_1863_ == 1)
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
lean_dec(v_h__2_1861_);
v___x_1864_ = lean_box(0);
v___x_1865_ = lean_apply_1(v_h__1_1860_, v___x_1864_);
return v___x_1865_;
}
else
{
lean_object* v_one_1866_; lean_object* v_n_1867_; lean_object* v___x_1868_; 
lean_dec(v_h__1_1860_);
v_one_1866_ = lean_unsigned_to_nat(1u);
v_n_1867_ = lean_nat_sub(v_n_1859_, v_one_1866_);
v___x_1868_ = lean_apply_1(v_h__2_1861_, v_n_1867_);
return v___x_1868_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg___boxed(lean_object* v_n_1869_, lean_object* v_h__1_1870_, lean_object* v_h__2_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(v_n_1869_, v_h__1_1870_, v_h__2_1871_);
lean_dec(v_n_1869_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(lean_object* v_motive_1873_, lean_object* v_n_1874_, lean_object* v_h__1_1875_, lean_object* v_h__2_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(v_n_1874_, v_h__1_1875_, v_h__2_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___boxed(lean_object* v_motive_1878_, lean_object* v_n_1879_, lean_object* v_h__1_1880_, lean_object* v_h__2_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(v_motive_1878_, v_n_1879_, v_h__1_1880_, v_h__2_1881_);
lean_dec(v_n_1879_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next___boxed(lean_object* v_s_1885_, lean_object* v_p_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = lean_string_utf8_next(v_s_1885_, v_p_1886_);
lean_dec(v_p_1886_);
lean_dec_ref(v_s_1885_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_String_next___boxed(lean_object* v_s_1890_, lean_object* v_p_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = lean_string_utf8_next(v_s_1890_, v_p_1891_);
lean_dec(v_p_1891_);
lean_dec_ref(v_s_1890_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux(lean_object* v_x_1893_, lean_object* v_x_1894_, lean_object* v_x_1895_){
_start:
{
if (lean_obj_tag(v_x_1893_) == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_dec(v_x_1894_);
v___x_1896_ = lean_unsigned_to_nat(1u);
v___x_1897_ = lean_nat_sub(v_x_1895_, v___x_1896_);
return v___x_1897_;
}
else
{
lean_object* v_head_1898_; lean_object* v_tail_1899_; uint32_t v___x_1900_; lean_object* v___x_1901_; lean_object* v_i_x27_1902_; uint8_t v___x_1903_; 
v_head_1898_ = lean_ctor_get(v_x_1893_, 0);
v_tail_1899_ = lean_ctor_get(v_x_1893_, 1);
v___x_1900_ = lean_unbox_uint32(v_head_1898_);
v___x_1901_ = l_Char_utf8Size(v___x_1900_);
v_i_x27_1902_ = lean_nat_add(v_x_1894_, v___x_1901_);
lean_dec(v___x_1901_);
v___x_1903_ = lean_nat_dec_le(v_x_1895_, v_i_x27_1902_);
if (v___x_1903_ == 0)
{
lean_dec(v_x_1894_);
v_x_1893_ = v_tail_1899_;
v_x_1894_ = v_i_x27_1902_;
goto _start;
}
else
{
lean_dec(v_i_x27_1902_);
return v_x_1894_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux___boxed(lean_object* v_x_1905_, lean_object* v_x_1906_, lean_object* v_x_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_String_Pos_Raw_utf8PrevAux(v_x_1905_, v_x_1906_, v_x_1907_);
lean_dec(v_x_1907_);
lean_dec(v_x_1905_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux(lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_String_Pos_Raw_utf8PrevAux(v_a_1909_, v_a_1910_, v_a_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux___boxed(lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_String_utf8PrevAux(v_a_1913_, v_a_1914_, v_a_1915_);
lean_dec(v_a_1915_);
lean_dec(v_a_1913_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_prev___boxed(lean_object* v_a_00___x40___internal___hyg_1919_, lean_object* v_a_00___x40___internal___hyg_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_1919_, v_a_00___x40___internal___hyg_1920_);
lean_dec(v_a_00___x40___internal___hyg_1920_);
lean_dec_ref(v_a_00___x40___internal___hyg_1919_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_String_prev___boxed(lean_object* v_a_00___x40___internal___hyg_1924_, lean_object* v_a_00___x40___internal___hyg_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_1924_, v_a_00___x40___internal___hyg_1925_);
lean_dec(v_a_00___x40___internal___hyg_1925_);
lean_dec_ref(v_a_00___x40___internal___hyg_1924_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_1929_, lean_object* v_a_00___x40___internal___hyg_1930_){
_start:
{
uint8_t v_res_1931_; lean_object* v_r_1932_; 
v_res_1931_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_1929_, v_a_00___x40___internal___hyg_1930_);
lean_dec(v_a_00___x40___internal___hyg_1930_);
lean_dec_ref(v_a_00___x40___internal___hyg_1929_);
v_r_1932_ = lean_box(v_res_1931_);
return v_r_1932_;
}
}
LEAN_EXPORT lean_object* l_String_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_1935_, lean_object* v_a_00___x40___internal___hyg_1936_){
_start:
{
uint8_t v_res_1937_; lean_object* v_r_1938_; 
v_res_1937_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_1935_, v_a_00___x40___internal___hyg_1936_);
lean_dec(v_a_00___x40___internal___hyg_1936_);
lean_dec_ref(v_a_00___x40___internal___hyg_1935_);
v_r_1938_ = lean_box(v_res_1937_);
return v_r_1938_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x27___boxed(lean_object* v_s_1942_, lean_object* v_p_1943_, lean_object* v_h_1944_){
_start:
{
uint32_t v_res_1945_; lean_object* v_r_1946_; 
v_res_1945_ = lean_string_utf8_get_fast(v_s_1942_, v_p_1943_);
lean_dec(v_p_1943_);
lean_dec_ref(v_s_1942_);
v_r_1946_ = lean_box_uint32(v_res_1945_);
return v_r_1946_;
}
}
LEAN_EXPORT lean_object* l_String_get_x27___boxed(lean_object* v_s_1950_, lean_object* v_p_1951_, lean_object* v_h_1952_){
_start:
{
uint32_t v_res_1953_; lean_object* v_r_1954_; 
v_res_1953_ = lean_string_utf8_get_fast(v_s_1950_, v_p_1951_);
lean_dec(v_p_1951_);
lean_dec_ref(v_s_1950_);
v_r_1954_ = lean_box_uint32(v_res_1953_);
return v_r_1954_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next_x27___boxed(lean_object* v_s_1958_, lean_object* v_p_1959_, lean_object* v_h_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = lean_string_utf8_next_fast(v_s_1958_, v_p_1959_);
lean_dec(v_p_1959_);
lean_dec_ref(v_s_1958_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_String_next_x27___boxed(lean_object* v_s_1965_, lean_object* v_p_1966_, lean_object* v_h_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = lean_string_utf8_next_fast(v_s_1965_, v_p_1966_);
lean_dec(v_p_1966_);
lean_dec_ref(v_s_1965_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter___redArg(lean_object* v_x_1969_, lean_object* v_x_1970_, lean_object* v_x_1971_, lean_object* v_h__1_1972_, lean_object* v_h__2_1973_){
_start:
{
if (lean_obj_tag(v_x_1969_) == 0)
{
lean_object* v___x_1974_; 
lean_dec(v_h__2_1973_);
v___x_1974_ = lean_apply_2(v_h__1_1972_, v_x_1970_, v_x_1971_);
return v___x_1974_;
}
else
{
lean_object* v_head_1975_; lean_object* v_tail_1976_; lean_object* v___x_1977_; 
lean_dec(v_h__1_1972_);
v_head_1975_ = lean_ctor_get(v_x_1969_, 0);
lean_inc(v_head_1975_);
v_tail_1976_ = lean_ctor_get(v_x_1969_, 1);
lean_inc(v_tail_1976_);
lean_dec_ref(v_x_1969_);
v___x_1977_ = lean_apply_4(v_h__2_1973_, v_head_1975_, v_tail_1976_, v_x_1970_, v_x_1971_);
return v___x_1977_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter(lean_object* v_motive_1978_, lean_object* v_x_1979_, lean_object* v_x_1980_, lean_object* v_x_1981_, lean_object* v_h__1_1982_, lean_object* v_h__2_1983_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter___redArg(v_x_1979_, v_x_1980_, v_x_1981_, v_h__1_1982_, v_h__2_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop(lean_object* v_a_1985_, lean_object* v_b_1986_, lean_object* v_stopPos_1987_, lean_object* v_i_1988_){
_start:
{
uint8_t v___x_1989_; 
v___x_1989_ = lean_nat_dec_lt(v_i_1988_, v_stopPos_1987_);
if (v___x_1989_ == 0)
{
return v_i_1988_;
}
else
{
uint32_t v___x_1990_; uint32_t v___x_1991_; uint8_t v___x_1992_; 
v___x_1990_ = lean_string_utf8_get(v_a_1985_, v_i_1988_);
v___x_1991_ = lean_string_utf8_get(v_b_1986_, v_i_1988_);
v___x_1992_ = lean_uint32_dec_eq(v___x_1990_, v___x_1991_);
if (v___x_1992_ == 0)
{
return v_i_1988_;
}
else
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_string_utf8_next(v_a_1985_, v_i_1988_);
lean_dec(v_i_1988_);
v_i_1988_ = v___x_1993_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop___boxed(lean_object* v_a_1995_, lean_object* v_b_1996_, lean_object* v_stopPos_1997_, lean_object* v_i_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l_String_firstDiffPos_loop(v_a_1995_, v_b_1996_, v_stopPos_1997_, v_i_1998_);
lean_dec(v_stopPos_1997_);
lean_dec_ref(v_b_1996_);
lean_dec_ref(v_a_1995_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos(lean_object* v_a_2000_, lean_object* v_b_2001_){
_start:
{
lean_object* v___y_2003_; lean_object* v___x_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; 
v___x_2006_ = lean_string_utf8_byte_size(v_a_2000_);
v___x_2007_ = lean_string_utf8_byte_size(v_b_2001_);
v___x_2008_ = lean_nat_dec_le(v___x_2006_, v___x_2007_);
if (v___x_2008_ == 0)
{
v___y_2003_ = v___x_2007_;
goto v___jp_2002_;
}
else
{
v___y_2003_ = v___x_2006_;
goto v___jp_2002_;
}
v___jp_2002_:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = lean_unsigned_to_nat(0u);
v___x_2005_ = l_String_firstDiffPos_loop(v_a_2000_, v_b_2001_, v___y_2003_, v___x_2004_);
lean_dec(v___y_2003_);
return v___x_2005_;
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos___boxed(lean_object* v_a_2009_, lean_object* v_b_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_String_firstDiffPos(v_a_2009_, v_b_2010_);
lean_dec_ref(v_b_2010_);
lean_dec_ref(v_a_2009_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082(lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
if (lean_obj_tag(v_a_2012_) == 0)
{
return v_a_2012_;
}
else
{
lean_object* v_head_2015_; lean_object* v_tail_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2029_; 
v_head_2015_ = lean_ctor_get(v_a_2012_, 0);
v_tail_2016_ = lean_ctor_get(v_a_2012_, 1);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_a_2012_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2018_ = v_a_2012_;
v_isShared_2019_ = v_isSharedCheck_2029_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_tail_2016_);
lean_inc(v_head_2015_);
lean_dec(v_a_2012_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2029_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
uint8_t v___x_2020_; 
v___x_2020_ = lean_nat_dec_eq(v_a_2013_, v_a_2014_);
if (v___x_2020_ == 0)
{
uint32_t v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2021_ = lean_unbox_uint32(v_head_2015_);
v___x_2022_ = l_Char_utf8Size(v___x_2021_);
v___x_2023_ = lean_nat_add(v_a_2013_, v___x_2022_);
lean_dec(v___x_2022_);
v___x_2024_ = l_String_Pos_Raw_extract_go_u2082(v_tail_2016_, v___x_2023_, v_a_2014_);
lean_dec(v___x_2023_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 1, v___x_2024_);
v___x_2026_ = v___x_2018_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_head_2015_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
else
{
lean_object* v___x_2028_; 
lean_del_object(v___x_2018_);
lean_dec(v_tail_2016_);
lean_dec(v_head_2015_);
v___x_2028_ = lean_box(0);
return v___x_2028_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082___boxed(lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_String_Pos_Raw_extract_go_u2082(v_a_2030_, v_a_2031_, v_a_2032_);
lean_dec(v_a_2032_);
lean_dec(v_a_2031_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081(lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_){
_start:
{
if (lean_obj_tag(v_a_2034_) == 0)
{
lean_dec(v_a_2035_);
return v_a_2034_;
}
else
{
lean_object* v_head_2038_; lean_object* v_tail_2039_; uint8_t v___x_2040_; 
v_head_2038_ = lean_ctor_get(v_a_2034_, 0);
v_tail_2039_ = lean_ctor_get(v_a_2034_, 1);
v___x_2040_ = lean_nat_dec_eq(v_a_2035_, v_a_2036_);
if (v___x_2040_ == 0)
{
uint32_t v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
lean_inc(v_tail_2039_);
lean_inc(v_head_2038_);
lean_dec_ref(v_a_2034_);
v___x_2041_ = lean_unbox_uint32(v_head_2038_);
lean_dec(v_head_2038_);
v___x_2042_ = l_Char_utf8Size(v___x_2041_);
v___x_2043_ = lean_nat_add(v_a_2035_, v___x_2042_);
lean_dec(v___x_2042_);
lean_dec(v_a_2035_);
v_a_2034_ = v_tail_2039_;
v_a_2035_ = v___x_2043_;
goto _start;
}
else
{
lean_object* v___x_2045_; 
v___x_2045_ = l_String_Pos_Raw_extract_go_u2082(v_a_2034_, v_a_2035_, v_a_2037_);
lean_dec(v_a_2035_);
return v___x_2045_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081___boxed(lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_String_Pos_Raw_extract_go_u2081(v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_);
lean_dec(v_a_2049_);
lean_dec(v_a_2048_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract___boxed(lean_object* v_a_00___x40___internal___hyg_2054_, lean_object* v_a_00___x40___internal___hyg_2055_, lean_object* v_a_00___x40___internal___hyg_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = lean_string_utf8_extract(v_a_00___x40___internal___hyg_2054_, v_a_00___x40___internal___hyg_2055_, v_a_00___x40___internal___hyg_2056_);
lean_dec(v_a_00___x40___internal___hyg_2056_);
lean_dec(v_a_00___x40___internal___hyg_2055_);
lean_dec_ref(v_a_00___x40___internal___hyg_2054_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux(lean_object* v_s_2058_, lean_object* v_pos_2059_, lean_object* v_i_2060_, lean_object* v_offset_2061_){
_start:
{
uint8_t v___x_2062_; 
v___x_2062_ = lean_nat_dec_le(v_pos_2059_, v_i_2060_);
if (v___x_2062_ == 0)
{
uint8_t v___x_2063_; 
v___x_2063_ = lean_string_utf8_at_end(v_s_2058_, v_i_2060_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2064_ = lean_string_utf8_next(v_s_2058_, v_i_2060_);
lean_dec(v_i_2060_);
v___x_2065_ = lean_unsigned_to_nat(1u);
v___x_2066_ = lean_nat_add(v_offset_2061_, v___x_2065_);
lean_dec(v_offset_2061_);
v_i_2060_ = v___x_2064_;
v_offset_2061_ = v___x_2066_;
goto _start;
}
else
{
lean_dec(v_i_2060_);
return v_offset_2061_;
}
}
else
{
lean_dec(v_i_2060_);
return v_offset_2061_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux___boxed(lean_object* v_s_2068_, lean_object* v_pos_2069_, lean_object* v_i_2070_, lean_object* v_offset_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2068_, v_pos_2069_, v_i_2070_, v_offset_2071_);
lean_dec(v_pos_2069_);
lean_dec_ref(v_s_2068_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos(lean_object* v_s_2073_, lean_object* v_pos_2074_){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = lean_unsigned_to_nat(0u);
v___x_2076_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2073_, v_pos_2074_, v___x_2075_, v___x_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos___boxed(lean_object* v_s_2077_, lean_object* v_pos_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_String_Pos_Raw_offsetOfPos(v_s_2077_, v_pos_2078_);
lean_dec(v_pos_2078_);
lean_dec_ref(v_s_2077_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos(lean_object* v_s_2080_, lean_object* v_pos_2081_){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = lean_unsigned_to_nat(0u);
v___x_2083_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2080_, v_pos_2081_, v___x_2082_, v___x_2082_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos___boxed(lean_object* v_s_2084_, lean_object* v_pos_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_String_offsetOfPos(v_s_2084_, v_pos_2085_);
lean_dec(v_pos_2085_);
lean_dec_ref(v_s_2084_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* lean_string_offsetofpos(lean_object* v_s_2087_, lean_object* v_pos_2088_){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = lean_unsigned_to_nat(0u);
v___x_2090_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2087_, v_pos_2088_, v___x_2089_, v___x_2089_);
lean_dec(v_pos_2088_);
lean_dec_ref(v_s_2087_);
return v___x_2090_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(lean_object* v_s1_2091_, lean_object* v_s2_2092_, lean_object* v_off1_2093_, lean_object* v_off2_2094_, lean_object* v_stop1_2095_){
_start:
{
uint8_t v___x_2096_; 
v___x_2096_ = lean_nat_dec_lt(v_off1_2093_, v_stop1_2095_);
if (v___x_2096_ == 0)
{
uint8_t v___x_2097_; 
lean_dec(v_off2_2094_);
lean_dec(v_off1_2093_);
v___x_2097_ = 1;
return v___x_2097_;
}
else
{
uint32_t v_c_u2081_2098_; uint32_t v_c_u2082_2099_; uint8_t v___x_2100_; 
v_c_u2081_2098_ = lean_string_utf8_get(v_s1_2091_, v_off1_2093_);
v_c_u2082_2099_ = lean_string_utf8_get(v_s2_2092_, v_off2_2094_);
v___x_2100_ = lean_uint32_dec_eq(v_c_u2081_2098_, v_c_u2082_2099_);
if (v___x_2100_ == 0)
{
lean_dec(v_off2_2094_);
lean_dec(v_off1_2093_);
return v___x_2100_;
}
else
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2101_ = l_Char_utf8Size(v_c_u2081_2098_);
v___x_2102_ = lean_nat_add(v_off1_2093_, v___x_2101_);
lean_dec(v___x_2101_);
lean_dec(v_off1_2093_);
v___x_2103_ = l_Char_utf8Size(v_c_u2082_2099_);
v___x_2104_ = lean_nat_add(v_off2_2094_, v___x_2103_);
lean_dec(v___x_2103_);
lean_dec(v_off2_2094_);
v_off1_2093_ = v___x_2102_;
v_off2_2094_ = v___x_2104_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop___boxed(lean_object* v_s1_2106_, lean_object* v_s2_2107_, lean_object* v_off1_2108_, lean_object* v_off2_2109_, lean_object* v_stop1_2110_){
_start:
{
uint8_t v_res_2111_; lean_object* v_r_2112_; 
v_res_2111_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2106_, v_s2_2107_, v_off1_2108_, v_off2_2109_, v_stop1_2110_);
lean_dec(v_stop1_2110_);
lean_dec_ref(v_s2_2107_);
lean_dec_ref(v_s1_2106_);
v_r_2112_ = lean_box(v_res_2111_);
return v_r_2112_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_substrEq(lean_object* v_s1_2113_, lean_object* v_pos1_2114_, lean_object* v_s2_2115_, lean_object* v_pos2_2116_, lean_object* v_sz_2117_){
_start:
{
uint8_t v___y_2119_; lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
v___x_2122_ = lean_nat_add(v_pos1_2114_, v_sz_2117_);
v___x_2123_ = lean_string_utf8_byte_size(v_s1_2113_);
v___x_2124_ = lean_nat_dec_le(v___x_2122_, v___x_2123_);
lean_dec(v___x_2122_);
if (v___x_2124_ == 0)
{
v___y_2119_ = v___x_2124_;
goto v___jp_2118_;
}
else
{
lean_object* v___x_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; 
v___x_2125_ = lean_nat_add(v_pos2_2116_, v_sz_2117_);
v___x_2126_ = lean_string_utf8_byte_size(v_s2_2115_);
v___x_2127_ = lean_nat_dec_le(v___x_2125_, v___x_2126_);
lean_dec(v___x_2125_);
v___y_2119_ = v___x_2127_;
goto v___jp_2118_;
}
v___jp_2118_:
{
if (v___y_2119_ == 0)
{
lean_dec(v_pos2_2116_);
lean_dec(v_pos1_2114_);
return v___y_2119_;
}
else
{
lean_object* v___x_2120_; uint8_t v___x_2121_; 
v___x_2120_ = lean_nat_add(v_pos1_2114_, v_sz_2117_);
v___x_2121_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2113_, v_s2_2115_, v_pos1_2114_, v_pos2_2116_, v___x_2120_);
lean_dec(v___x_2120_);
return v___x_2121_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_substrEq___boxed(lean_object* v_s1_2128_, lean_object* v_pos1_2129_, lean_object* v_s2_2130_, lean_object* v_pos2_2131_, lean_object* v_sz_2132_){
_start:
{
uint8_t v_res_2133_; lean_object* v_r_2134_; 
v_res_2133_ = l_String_Pos_Raw_substrEq(v_s1_2128_, v_pos1_2129_, v_s2_2130_, v_pos2_2131_, v_sz_2132_);
lean_dec(v_sz_2132_);
lean_dec_ref(v_s2_2130_);
lean_dec_ref(v_s1_2128_);
v_r_2134_ = lean_box(v_res_2133_);
return v_r_2134_;
}
}
LEAN_EXPORT uint8_t l_String_substrEq(lean_object* v_s1_2135_, lean_object* v_pos1_2136_, lean_object* v_s2_2137_, lean_object* v_pos2_2138_, lean_object* v_sz_2139_){
_start:
{
uint8_t v___x_2140_; 
v___x_2140_ = l_String_Pos_Raw_substrEq(v_s1_2135_, v_pos1_2136_, v_s2_2137_, v_pos2_2138_, v_sz_2139_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l_String_substrEq___boxed(lean_object* v_s1_2141_, lean_object* v_pos1_2142_, lean_object* v_s2_2143_, lean_object* v_pos2_2144_, lean_object* v_sz_2145_){
_start:
{
uint8_t v_res_2146_; lean_object* v_r_2147_; 
v_res_2146_ = l_String_substrEq(v_s1_2141_, v_pos1_2142_, v_s2_2143_, v_pos2_2144_, v_sz_2145_);
lean_dec(v_sz_2145_);
lean_dec_ref(v_s2_2143_);
lean_dec_ref(v_s1_2141_);
v_r_2147_ = lean_box(v_res_2146_);
return v_r_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter___redArg(lean_object* v_x_2148_, lean_object* v_x_2149_, lean_object* v_h__1_2150_, lean_object* v_h__2_2151_){
_start:
{
lean_object* v_zero_2152_; uint8_t v_isZero_2153_; 
v_zero_2152_ = lean_unsigned_to_nat(0u);
v_isZero_2153_ = lean_nat_dec_eq(v_x_2148_, v_zero_2152_);
if (v_isZero_2153_ == 1)
{
lean_object* v___x_2154_; 
lean_dec(v_h__2_2151_);
v___x_2154_ = lean_apply_1(v_h__1_2150_, v_x_2149_);
return v___x_2154_;
}
else
{
lean_object* v_one_2155_; lean_object* v_n_2156_; lean_object* v___x_2157_; 
lean_dec(v_h__1_2150_);
v_one_2155_ = lean_unsigned_to_nat(1u);
v_n_2156_ = lean_nat_sub(v_x_2148_, v_one_2155_);
v___x_2157_ = lean_apply_2(v_h__2_2151_, v_n_2156_, v_x_2149_);
return v___x_2157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter___redArg___boxed(lean_object* v_x_2158_, lean_object* v_x_2159_, lean_object* v_h__1_2160_, lean_object* v_h__2_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter___redArg(v_x_2158_, v_x_2159_, v_h__1_2160_, v_h__2_2161_);
lean_dec(v_x_2158_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter(lean_object* v_00_u03b1_2163_, lean_object* v_motive_2164_, lean_object* v_x_2165_, lean_object* v_x_2166_, lean_object* v_h__1_2167_, lean_object* v_h__2_2168_){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter___redArg(v_x_2165_, v_x_2166_, v_h__1_2167_, v_h__2_2168_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter___boxed(lean_object* v_00_u03b1_2170_, lean_object* v_motive_2171_, lean_object* v_x_2172_, lean_object* v_x_2173_, lean_object* v_h__1_2174_, lean_object* v_h__2_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter(v_00_u03b1_2170_, v_motive_2171_, v_x_2172_, v_x_2173_, v_h__1_2174_, v_h__2_2175_);
lean_dec(v_x_2172_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object* v_x_2177_, lean_object* v_x_2178_, lean_object* v_h__1_2179_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = lean_apply_2(v_h__1_2179_, v_x_2177_, v_x_2178_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object* v_motive_2181_, lean_object* v_x_2182_, lean_object* v_x_2183_, lean_object* v_h__1_2184_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = lean_apply_2(v_h__1_2184_, v_x_2182_, v_x_2183_);
return v___x_2185_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
