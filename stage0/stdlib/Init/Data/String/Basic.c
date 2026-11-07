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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__6_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__6_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__8_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__8_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(uint8_t v_x_380_, lean_object* v_h__1_381_, lean_object* v_h__2_382_, lean_object* v_h__3_383_, lean_object* v_h__4_384_, lean_object* v_h__5_385_){
_start:
{
switch(v_x_380_)
{
case 0:
{
lean_object* v___x_386_; 
lean_dec(v_h__5_385_);
lean_dec(v_h__4_384_);
lean_dec(v_h__3_383_);
lean_dec(v_h__2_382_);
v___x_386_ = lean_apply_1(v_h__1_381_, lean_box(0));
return v___x_386_;
}
case 1:
{
lean_object* v___x_387_; 
lean_dec(v_h__5_385_);
lean_dec(v_h__4_384_);
lean_dec(v_h__3_383_);
lean_dec(v_h__1_381_);
v___x_387_ = lean_apply_1(v_h__2_382_, lean_box(0));
return v___x_387_;
}
case 2:
{
lean_object* v___x_388_; 
lean_dec(v_h__5_385_);
lean_dec(v_h__4_384_);
lean_dec(v_h__2_382_);
lean_dec(v_h__1_381_);
v___x_388_ = lean_apply_1(v_h__3_383_, lean_box(0));
return v___x_388_;
}
case 3:
{
lean_object* v___x_389_; 
lean_dec(v_h__5_385_);
lean_dec(v_h__3_383_);
lean_dec(v_h__2_382_);
lean_dec(v_h__1_381_);
v___x_389_ = lean_apply_1(v_h__4_384_, lean_box(0));
return v___x_389_;
}
default: 
{
lean_object* v___x_390_; 
lean_dec(v_h__4_384_);
lean_dec(v_h__3_383_);
lean_dec(v_h__2_382_);
lean_dec(v_h__1_381_);
v___x_390_ = lean_apply_1(v_h__5_385_, lean_box(0));
return v___x_390_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_391_, lean_object* v_h__1_392_, lean_object* v_h__2_393_, lean_object* v_h__3_394_, lean_object* v_h__4_395_, lean_object* v_h__5_396_){
_start:
{
uint8_t v_x_47__boxed_397_; lean_object* v_res_398_; 
v_x_47__boxed_397_ = lean_unbox(v_x_391_);
v_res_398_ = l___private_Init_Data_String_Basic_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(v_x_47__boxed_397_, v_h__1_392_, v_h__2_393_, v_h__3_394_, v_h__4_395_, v_h__5_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(lean_object* v_motive_399_, uint8_t v_x_400_, lean_object* v_h__1_401_, lean_object* v_h__2_402_, lean_object* v_h__3_403_, lean_object* v_h__4_404_, lean_object* v_h__5_405_){
_start:
{
switch(v_x_400_)
{
case 0:
{
lean_object* v___x_406_; 
lean_dec(v_h__5_405_);
lean_dec(v_h__4_404_);
lean_dec(v_h__3_403_);
lean_dec(v_h__2_402_);
v___x_406_ = lean_apply_1(v_h__1_401_, lean_box(0));
return v___x_406_;
}
case 1:
{
lean_object* v___x_407_; 
lean_dec(v_h__5_405_);
lean_dec(v_h__4_404_);
lean_dec(v_h__3_403_);
lean_dec(v_h__1_401_);
v___x_407_ = lean_apply_1(v_h__2_402_, lean_box(0));
return v___x_407_;
}
case 2:
{
lean_object* v___x_408_; 
lean_dec(v_h__5_405_);
lean_dec(v_h__4_404_);
lean_dec(v_h__2_402_);
lean_dec(v_h__1_401_);
v___x_408_ = lean_apply_1(v_h__3_403_, lean_box(0));
return v___x_408_;
}
case 3:
{
lean_object* v___x_409_; 
lean_dec(v_h__5_405_);
lean_dec(v_h__3_403_);
lean_dec(v_h__2_402_);
lean_dec(v_h__1_401_);
v___x_409_ = lean_apply_1(v_h__4_404_, lean_box(0));
return v___x_409_;
}
default: 
{
lean_object* v___x_410_; 
lean_dec(v_h__4_404_);
lean_dec(v_h__3_403_);
lean_dec(v_h__2_402_);
lean_dec(v_h__1_401_);
v___x_410_ = lean_apply_1(v_h__5_405_, lean_box(0));
return v___x_410_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___boxed(lean_object* v_motive_411_, lean_object* v_x_412_, lean_object* v_h__1_413_, lean_object* v_h__2_414_, lean_object* v_h__3_415_, lean_object* v_h__4_416_, lean_object* v_h__5_417_){
_start:
{
uint8_t v_x_60__boxed_418_; lean_object* v_res_419_; 
v_x_60__boxed_418_ = lean_unbox(v_x_412_);
v_res_419_ = l___private_Init_Data_String_Basic_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(v_motive_411_, v_x_60__boxed_418_, v_h__1_413_, v_h__2_414_, v_h__3_415_, v_h__4_416_, v_h__5_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__1_splitter___redArg(lean_object* v_x_420_, lean_object* v_h__1_421_, lean_object* v_h__2_422_){
_start:
{
if (lean_obj_tag(v_x_420_) == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec(v_h__1_421_);
v___x_423_ = lean_box(0);
v___x_424_ = lean_apply_1(v_h__2_422_, v___x_423_);
return v___x_424_;
}
else
{
lean_object* v_val_425_; lean_object* v___x_426_; 
lean_dec(v_h__2_422_);
v_val_425_ = lean_ctor_get(v_x_420_, 0);
lean_inc(v_val_425_);
lean_dec_ref_known(v_x_420_, 1);
v___x_426_ = lean_apply_1(v_h__1_421_, v_val_425_);
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__1_splitter(lean_object* v_motive_427_, lean_object* v_x_428_, lean_object* v_h__1_429_, lean_object* v_h__2_430_){
_start:
{
if (lean_obj_tag(v_x_428_) == 0)
{
lean_object* v___x_431_; lean_object* v___x_432_; 
lean_dec(v_h__1_429_);
v___x_431_ = lean_box(0);
v___x_432_ = lean_apply_1(v_h__2_430_, v___x_431_);
return v___x_432_;
}
else
{
lean_object* v_val_433_; lean_object* v___x_434_; 
lean_dec(v_h__2_430_);
v_val_433_ = lean_ctor_get(v_x_428_, 0);
lean_inc(v_val_433_);
lean_dec_ref_known(v_x_428_, 1);
v___x_434_ = lean_apply_1(v_h__1_429_, v_val_433_);
return v___x_434_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__3_splitter___redArg(lean_object* v_ws_435_, lean_object* v_h__1_436_, lean_object* v_h__2_437_){
_start:
{
if (lean_obj_tag(v_ws_435_) == 1)
{
lean_object* v_head_438_; lean_object* v_tail_439_; lean_object* v___x_440_; 
lean_dec(v_h__2_437_);
v_head_438_ = lean_ctor_get(v_ws_435_, 0);
lean_inc(v_head_438_);
v_tail_439_ = lean_ctor_get(v_ws_435_, 1);
lean_inc(v_tail_439_);
lean_dec_ref_known(v_ws_435_, 2);
v___x_440_ = lean_apply_2(v_h__1_436_, v_head_438_, v_tail_439_);
return v___x_440_;
}
else
{
lean_object* v___x_441_; 
lean_dec(v_h__1_436_);
v___x_441_ = lean_apply_2(v_h__2_437_, v_ws_435_, lean_box(0));
return v___x_441_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__3_splitter(lean_object* v_motive_442_, lean_object* v_ws_443_, lean_object* v_h__1_444_, lean_object* v_h__2_445_){
_start:
{
if (lean_obj_tag(v_ws_443_) == 1)
{
lean_object* v_head_446_; lean_object* v_tail_447_; lean_object* v___x_448_; 
lean_dec(v_h__2_445_);
v_head_446_ = lean_ctor_get(v_ws_443_, 0);
lean_inc(v_head_446_);
v_tail_447_ = lean_ctor_get(v_ws_443_, 1);
lean_inc(v_tail_447_);
lean_dec_ref_known(v_ws_443_, 2);
v___x_448_ = lean_apply_2(v_h__1_444_, v_head_446_, v_tail_447_);
return v___x_448_;
}
else
{
lean_object* v___x_449_; 
lean_dec(v_h__1_444_);
v___x_449_ = lean_apply_2(v_h__2_445_, v_ws_443_, lean_box(0));
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__6_splitter___redArg(lean_object* v_ws_450_, lean_object* v_h__1_451_, lean_object* v_h__2_452_){
_start:
{
if (lean_obj_tag(v_ws_450_) == 1)
{
lean_object* v_tail_453_; 
v_tail_453_ = lean_ctor_get(v_ws_450_, 1);
if (lean_obj_tag(v_tail_453_) == 1)
{
lean_object* v_head_454_; lean_object* v_head_455_; lean_object* v_tail_456_; lean_object* v___x_457_; 
lean_inc_ref(v_tail_453_);
lean_dec(v_h__2_452_);
v_head_454_ = lean_ctor_get(v_ws_450_, 0);
lean_inc(v_head_454_);
lean_dec_ref_known(v_ws_450_, 2);
v_head_455_ = lean_ctor_get(v_tail_453_, 0);
lean_inc(v_head_455_);
v_tail_456_ = lean_ctor_get(v_tail_453_, 1);
lean_inc(v_tail_456_);
lean_dec_ref_known(v_tail_453_, 2);
v___x_457_ = lean_apply_3(v_h__1_451_, v_head_454_, v_head_455_, v_tail_456_);
return v___x_457_;
}
else
{
lean_object* v___x_458_; 
lean_dec(v_h__1_451_);
v___x_458_ = lean_apply_2(v_h__2_452_, v_ws_450_, lean_box(0));
return v___x_458_;
}
}
else
{
lean_object* v___x_459_; 
lean_dec(v_h__1_451_);
v___x_459_ = lean_apply_2(v_h__2_452_, v_ws_450_, lean_box(0));
return v___x_459_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__6_splitter(lean_object* v_motive_460_, lean_object* v_ws_461_, lean_object* v_h__1_462_, lean_object* v_h__2_463_){
_start:
{
if (lean_obj_tag(v_ws_461_) == 1)
{
lean_object* v_tail_464_; 
v_tail_464_ = lean_ctor_get(v_ws_461_, 1);
if (lean_obj_tag(v_tail_464_) == 1)
{
lean_object* v_head_465_; lean_object* v_head_466_; lean_object* v_tail_467_; lean_object* v___x_468_; 
lean_inc_ref(v_tail_464_);
lean_dec(v_h__2_463_);
v_head_465_ = lean_ctor_get(v_ws_461_, 0);
lean_inc(v_head_465_);
lean_dec_ref_known(v_ws_461_, 2);
v_head_466_ = lean_ctor_get(v_tail_464_, 0);
lean_inc(v_head_466_);
v_tail_467_ = lean_ctor_get(v_tail_464_, 1);
lean_inc(v_tail_467_);
lean_dec_ref_known(v_tail_464_, 2);
v___x_468_ = lean_apply_3(v_h__1_462_, v_head_465_, v_head_466_, v_tail_467_);
return v___x_468_;
}
else
{
lean_object* v___x_469_; 
lean_dec(v_h__1_462_);
v___x_469_ = lean_apply_2(v_h__2_463_, v_ws_461_, lean_box(0));
return v___x_469_;
}
}
else
{
lean_object* v___x_470_; 
lean_dec(v_h__1_462_);
v___x_470_ = lean_apply_2(v_h__2_463_, v_ws_461_, lean_box(0));
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__8_splitter___redArg(lean_object* v_ws_471_, lean_object* v_h__1_472_, lean_object* v_h__2_473_){
_start:
{
if (lean_obj_tag(v_ws_471_) == 1)
{
lean_object* v_tail_474_; 
v_tail_474_ = lean_ctor_get(v_ws_471_, 1);
if (lean_obj_tag(v_tail_474_) == 1)
{
lean_object* v_tail_475_; 
v_tail_475_ = lean_ctor_get(v_tail_474_, 1);
if (lean_obj_tag(v_tail_475_) == 1)
{
lean_object* v_head_476_; lean_object* v_head_477_; lean_object* v_head_478_; lean_object* v_tail_479_; lean_object* v___x_480_; 
lean_inc_ref(v_tail_475_);
lean_inc_ref(v_tail_474_);
lean_dec(v_h__2_473_);
v_head_476_ = lean_ctor_get(v_ws_471_, 0);
lean_inc(v_head_476_);
lean_dec_ref_known(v_ws_471_, 2);
v_head_477_ = lean_ctor_get(v_tail_474_, 0);
lean_inc(v_head_477_);
lean_dec_ref_known(v_tail_474_, 2);
v_head_478_ = lean_ctor_get(v_tail_475_, 0);
lean_inc(v_head_478_);
v_tail_479_ = lean_ctor_get(v_tail_475_, 1);
lean_inc(v_tail_479_);
lean_dec_ref_known(v_tail_475_, 2);
v___x_480_ = lean_apply_4(v_h__1_472_, v_head_476_, v_head_477_, v_head_478_, v_tail_479_);
return v___x_480_;
}
else
{
lean_object* v___x_481_; 
lean_dec(v_h__1_472_);
v___x_481_ = lean_apply_2(v_h__2_473_, v_ws_471_, lean_box(0));
return v___x_481_;
}
}
else
{
lean_object* v___x_482_; 
lean_dec(v_h__1_472_);
v___x_482_ = lean_apply_2(v_h__2_473_, v_ws_471_, lean_box(0));
return v___x_482_;
}
}
else
{
lean_object* v___x_483_; 
lean_dec(v_h__1_472_);
v___x_483_ = lean_apply_2(v_h__2_473_, v_ws_471_, lean_box(0));
return v___x_483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__8_splitter(lean_object* v_motive_484_, lean_object* v_ws_485_, lean_object* v_h__1_486_, lean_object* v_h__2_487_){
_start:
{
if (lean_obj_tag(v_ws_485_) == 1)
{
lean_object* v_tail_488_; 
v_tail_488_ = lean_ctor_get(v_ws_485_, 1);
if (lean_obj_tag(v_tail_488_) == 1)
{
lean_object* v_tail_489_; 
v_tail_489_ = lean_ctor_get(v_tail_488_, 1);
if (lean_obj_tag(v_tail_489_) == 1)
{
lean_object* v_head_490_; lean_object* v_head_491_; lean_object* v_head_492_; lean_object* v_tail_493_; lean_object* v___x_494_; 
lean_inc_ref(v_tail_489_);
lean_inc_ref(v_tail_488_);
lean_dec(v_h__2_487_);
v_head_490_ = lean_ctor_get(v_ws_485_, 0);
lean_inc(v_head_490_);
lean_dec_ref_known(v_ws_485_, 2);
v_head_491_ = lean_ctor_get(v_tail_488_, 0);
lean_inc(v_head_491_);
lean_dec_ref_known(v_tail_488_, 2);
v_head_492_ = lean_ctor_get(v_tail_489_, 0);
lean_inc(v_head_492_);
v_tail_493_ = lean_ctor_get(v_tail_489_, 1);
lean_inc(v_tail_493_);
lean_dec_ref_known(v_tail_489_, 2);
v___x_494_ = lean_apply_4(v_h__1_486_, v_head_490_, v_head_491_, v_head_492_, v_tail_493_);
return v___x_494_;
}
else
{
lean_object* v___x_495_; 
lean_dec(v_h__1_486_);
v___x_495_ = lean_apply_2(v_h__2_487_, v_ws_485_, lean_box(0));
return v___x_495_;
}
}
else
{
lean_object* v___x_496_; 
lean_dec(v_h__1_486_);
v___x_496_ = lean_apply_2(v_h__2_487_, v_ws_485_, lean_box(0));
return v___x_496_;
}
}
else
{
lean_object* v___x_497_; 
lean_dec(v_h__1_486_);
v___x_497_ = lean_apply_2(v_h__2_487_, v_ws_485_, lean_box(0));
return v___x_497_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValid___boxed(lean_object* v_s_500_, lean_object* v_p_501_){
_start:
{
uint8_t v_res_502_; lean_object* v_r_503_; 
v_res_502_ = lean_string_is_valid_pos(v_s_500_, v_p_501_);
lean_dec(v_p_501_);
lean_dec_ref(v_s_500_);
v_r_503_ = lean_box(v_res_502_);
return v_r_503_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsValid(lean_object* v_s_504_, lean_object* v_p_505_){
_start:
{
uint8_t v___x_506_; 
v___x_506_ = lean_string_is_valid_pos(v_s_504_, v_p_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsValid___boxed(lean_object* v_s_507_, lean_object* v_p_508_){
_start:
{
uint8_t v_res_509_; lean_object* v_r_510_; 
v_res_509_ = l_String_instDecidableIsValid(v_s_507_, v_p_508_);
lean_dec(v_p_508_);
lean_dec_ref(v_s_507_);
v_r_510_ = lean_box(v_res_509_);
return v_r_510_;
}
}
LEAN_EXPORT lean_object* l_String_extract___boxed(lean_object* v_s_514_, lean_object* v_b_515_, lean_object* v_e_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = lean_string_utf8_extract_fast(v_s_514_, v_b_515_, v_e_516_);
lean_dec(v_e_516_);
lean_dec(v_b_515_);
lean_dec_ref(v_s_514_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_extract(lean_object* v_s_518_, lean_object* v_b_519_, lean_object* v_e_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = lean_string_utf8_extract_fast(v_s_518_, v_b_519_, v_e_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_extract___boxed(lean_object* v_s_522_, lean_object* v_b_523_, lean_object* v_e_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_String_Pos_extract(v_s_522_, v_b_523_, v_e_524_);
lean_dec(v_e_524_);
lean_dec(v_b_523_);
lean_dec_ref(v_s_522_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_copy(lean_object* v_s_526_){
_start:
{
lean_object* v_str_527_; lean_object* v_startInclusive_528_; lean_object* v_endExclusive_529_; lean_object* v___x_530_; 
v_str_527_ = lean_ctor_get(v_s_526_, 0);
v_startInclusive_528_ = lean_ctor_get(v_s_526_, 1);
v_endExclusive_529_ = lean_ctor_get(v_s_526_, 2);
v___x_530_ = lean_string_utf8_extract_fast(v_str_527_, v_startInclusive_528_, v_endExclusive_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_copy___boxed(lean_object* v_s_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_String_Slice_copy(v_s_531_);
lean_dec_ref(v_s_531_);
return v_res_532_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_isValidForSlice(lean_object* v_s_533_, lean_object* v_p_534_){
_start:
{
lean_object* v_str_535_; lean_object* v_startInclusive_536_; lean_object* v_endExclusive_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v_str_535_ = lean_ctor_get(v_s_533_, 0);
v_startInclusive_536_ = lean_ctor_get(v_s_533_, 1);
v_endExclusive_537_ = lean_ctor_get(v_s_533_, 2);
v___x_538_ = lean_nat_sub(v_endExclusive_537_, v_startInclusive_536_);
v___x_539_ = lean_unsigned_to_nat(1u);
v___x_540_ = lean_nat_add(v_p_534_, v___x_539_);
v___x_541_ = lean_nat_dec_le(v___x_540_, v___x_538_);
lean_dec(v___x_540_);
if (v___x_541_ == 0)
{
uint8_t v_decide_542_; 
v_decide_542_ = lean_nat_dec_eq(v_p_534_, v___x_538_);
lean_dec(v___x_538_);
return v_decide_542_;
}
else
{
lean_object* v___x_543_; uint8_t v___x_544_; uint8_t v___x_545_; uint8_t v___x_546_; uint8_t v___x_547_; uint8_t v___x_548_; 
lean_dec(v___x_538_);
v___x_543_ = lean_nat_add(v_startInclusive_536_, v_p_534_);
v___x_544_ = lean_string_get_byte_fast(v_str_535_, v___x_543_);
v___x_545_ = 128;
v___x_546_ = lean_uint8_land(v___x_544_, v___x_545_);
v___x_547_ = 0;
v___x_548_ = lean_uint8_dec_eq(v___x_546_, v___x_547_);
if (v___x_548_ == 0)
{
uint8_t v___x_549_; uint8_t v___x_550_; uint8_t v___x_551_; uint8_t v___x_552_; 
v___x_549_ = 224;
v___x_550_ = lean_uint8_land(v___x_544_, v___x_549_);
v___x_551_ = 192;
v___x_552_ = lean_uint8_dec_eq(v___x_550_, v___x_551_);
if (v___x_552_ == 0)
{
uint8_t v___x_553_; uint8_t v___x_554_; uint8_t v___x_555_; 
v___x_553_ = 240;
v___x_554_ = lean_uint8_land(v___x_544_, v___x_553_);
v___x_555_ = lean_uint8_dec_eq(v___x_554_, v___x_549_);
if (v___x_555_ == 0)
{
uint8_t v___x_556_; uint8_t v___x_557_; uint8_t v___x_558_; 
v___x_556_ = 248;
v___x_557_ = lean_uint8_land(v___x_544_, v___x_556_);
v___x_558_ = lean_uint8_dec_eq(v___x_557_, v___x_553_);
return v___x_558_;
}
else
{
return v___x_555_;
}
}
else
{
return v___x_552_;
}
}
else
{
return v___x_548_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValidForSlice___boxed(lean_object* v_s_559_, lean_object* v_p_560_){
_start:
{
uint8_t v_res_561_; lean_object* v_r_562_; 
v_res_561_ = l_String_Pos_Raw_isValidForSlice(v_s_559_, v_p_560_);
lean_dec(v_p_560_);
lean_dec_ref(v_s_559_);
v_r_562_ = lean_box(v_res_561_);
return v_r_562_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsValidForSlice(lean_object* v_s_563_, lean_object* v_p_564_){
_start:
{
uint8_t v___x_565_; 
v___x_565_ = l_String_Pos_Raw_isValidForSlice(v_s_563_, v_p_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsValidForSlice___boxed(lean_object* v_s_566_, lean_object* v_p_567_){
_start:
{
uint8_t v_res_568_; lean_object* v_r_569_; 
v_res_568_ = l_String_instDecidableIsValidForSlice(v_s_566_, v_p_567_);
lean_dec(v_p_567_);
lean_dec_ref(v_s_566_);
v_r_569_ = lean_box(v_res_568_);
return v_r_569_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str(lean_object* v_s_570_, lean_object* v_pos_571_){
_start:
{
lean_object* v_startInclusive_572_; lean_object* v___x_573_; 
v_startInclusive_572_ = lean_ctor_get(v_s_570_, 1);
v___x_573_ = lean_nat_add(v_startInclusive_572_, v_pos_571_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str___boxed(lean_object* v_s_574_, lean_object* v_pos_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_String_Slice_Pos_str(v_s_574_, v_pos_575_);
lean_dec(v_pos_575_);
lean_dec_ref(v_s_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg(lean_object* v_s_577_, lean_object* v_pos_578_){
_start:
{
lean_object* v_startInclusive_579_; lean_object* v___x_580_; 
v_startInclusive_579_ = lean_ctor_get(v_s_577_, 1);
v___x_580_ = lean_nat_sub(v_pos_578_, v_startInclusive_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg___boxed(lean_object* v_s_581_, lean_object* v_pos_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_String_Slice_Pos_ofStr___redArg(v_s_581_, v_pos_582_);
lean_dec(v_pos_582_);
lean_dec_ref(v_s_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr(lean_object* v_s_584_, lean_object* v_pos_585_, lean_object* v_h_u2081_586_, lean_object* v_h_u2082_587_){
_start:
{
lean_object* v_startInclusive_588_; lean_object* v___x_589_; 
v_startInclusive_588_ = lean_ctor_get(v_s_584_, 1);
v___x_589_ = lean_nat_sub(v_pos_585_, v_startInclusive_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___boxed(lean_object* v_s_590_, lean_object* v_pos_591_, lean_object* v_h_u2081_592_, lean_object* v_h_u2082_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_String_Slice_Pos_ofStr(v_s_590_, v_pos_591_, v_h_u2081_592_, v_h_u2082_593_);
lean_dec(v_pos_591_);
lean_dec_ref(v_s_590_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom(lean_object* v_s_595_, lean_object* v_pos_596_){
_start:
{
lean_object* v_str_597_; lean_object* v_startInclusive_598_; lean_object* v_endExclusive_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_607_; 
v_str_597_ = lean_ctor_get(v_s_595_, 0);
v_startInclusive_598_ = lean_ctor_get(v_s_595_, 1);
v_endExclusive_599_ = lean_ctor_get(v_s_595_, 2);
v_isSharedCheck_607_ = !lean_is_exclusive(v_s_595_);
if (v_isSharedCheck_607_ == 0)
{
v___x_601_ = v_s_595_;
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_endExclusive_599_);
lean_inc(v_startInclusive_598_);
lean_inc(v_str_597_);
lean_dec(v_s_595_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_603_ = lean_nat_add(v_startInclusive_598_, v_pos_596_);
lean_dec(v_startInclusive_598_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 1, v___x_603_);
v___x_605_ = v___x_601_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_str_597_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_606_, 2, v_endExclusive_599_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom___boxed(lean_object* v_s_608_, lean_object* v_pos_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_String_Slice_sliceFrom(v_s_608_, v_pos_609_);
lean_dec(v_pos_609_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStart(lean_object* v_s_611_, lean_object* v_pos_612_){
_start:
{
lean_object* v_str_613_; lean_object* v_startInclusive_614_; lean_object* v_endExclusive_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_623_; 
v_str_613_ = lean_ctor_get(v_s_611_, 0);
v_startInclusive_614_ = lean_ctor_get(v_s_611_, 1);
v_endExclusive_615_ = lean_ctor_get(v_s_611_, 2);
v_isSharedCheck_623_ = !lean_is_exclusive(v_s_611_);
if (v_isSharedCheck_623_ == 0)
{
v___x_617_ = v_s_611_;
v_isShared_618_ = v_isSharedCheck_623_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_endExclusive_615_);
lean_inc(v_startInclusive_614_);
lean_inc(v_str_613_);
lean_dec(v_s_611_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_623_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v___x_621_; 
v___x_619_ = lean_nat_add(v_startInclusive_614_, v_pos_612_);
lean_dec(v_startInclusive_614_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v___x_619_);
v___x_621_ = v___x_617_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_str_613_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_622_, 2, v_endExclusive_615_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStart___boxed(lean_object* v_s_624_, lean_object* v_pos_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_String_Slice_replaceStart(v_s_624_, v_pos_625_);
lean_dec(v_pos_625_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceTo(lean_object* v_s_627_, lean_object* v_pos_628_){
_start:
{
lean_object* v_str_629_; lean_object* v_startInclusive_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_638_; 
v_str_629_ = lean_ctor_get(v_s_627_, 0);
v_startInclusive_630_ = lean_ctor_get(v_s_627_, 1);
v_isSharedCheck_638_ = !lean_is_exclusive(v_s_627_);
if (v_isSharedCheck_638_ == 0)
{
lean_object* v_unused_639_; 
v_unused_639_ = lean_ctor_get(v_s_627_, 2);
lean_dec(v_unused_639_);
v___x_632_ = v_s_627_;
v_isShared_633_ = v_isSharedCheck_638_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_startInclusive_630_);
lean_inc(v_str_629_);
lean_dec(v_s_627_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_638_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_634_ = lean_nat_add(v_startInclusive_630_, v_pos_628_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 2, v___x_634_);
v___x_636_ = v___x_632_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_str_629_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_startInclusive_630_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceTo___boxed(lean_object* v_s_640_, lean_object* v_pos_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_String_Slice_sliceTo(v_s_640_, v_pos_641_);
lean_dec(v_pos_641_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd(lean_object* v_s_643_, lean_object* v_pos_644_){
_start:
{
lean_object* v_str_645_; lean_object* v_startInclusive_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_654_; 
v_str_645_ = lean_ctor_get(v_s_643_, 0);
v_startInclusive_646_ = lean_ctor_get(v_s_643_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_s_643_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; 
v_unused_655_ = lean_ctor_get(v_s_643_, 2);
lean_dec(v_unused_655_);
v___x_648_ = v_s_643_;
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_startInclusive_646_);
lean_inc(v_str_645_);
lean_dec(v_s_643_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = lean_nat_add(v_startInclusive_646_, v_pos_644_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 2, v___x_650_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_str_645_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_startInclusive_646_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd___boxed(lean_object* v_s_656_, lean_object* v_pos_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_String_Slice_replaceEnd(v_s_656_, v_pos_657_);
lean_dec(v_pos_657_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg(lean_object* v_s_659_, lean_object* v_newStart_660_, lean_object* v_newEnd_661_){
_start:
{
lean_object* v_str_662_; lean_object* v_startInclusive_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_672_; 
v_str_662_ = lean_ctor_get(v_s_659_, 0);
v_startInclusive_663_ = lean_ctor_get(v_s_659_, 1);
v_isSharedCheck_672_ = !lean_is_exclusive(v_s_659_);
if (v_isSharedCheck_672_ == 0)
{
lean_object* v_unused_673_; 
v_unused_673_ = lean_ctor_get(v_s_659_, 2);
lean_dec(v_unused_673_);
v___x_665_ = v_s_659_;
v_isShared_666_ = v_isSharedCheck_672_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_startInclusive_663_);
lean_inc(v_str_662_);
lean_dec(v_s_659_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_672_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_667_ = lean_nat_add(v_startInclusive_663_, v_newStart_660_);
v___x_668_ = lean_nat_add(v_startInclusive_663_, v_newEnd_661_);
lean_dec(v_startInclusive_663_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 2, v___x_668_);
lean_ctor_set(v___x_665_, 1, v___x_667_);
v___x_670_ = v___x_665_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_str_662_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v___x_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg___boxed(lean_object* v_s_674_, lean_object* v_newStart_675_, lean_object* v_newEnd_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_String_Slice_slice___redArg(v_s_674_, v_newStart_675_, v_newEnd_676_);
lean_dec(v_newEnd_676_);
lean_dec(v_newStart_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice(lean_object* v_s_678_, lean_object* v_newStart_679_, lean_object* v_newEnd_680_, lean_object* v_h_681_){
_start:
{
lean_object* v_str_682_; lean_object* v_startInclusive_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_692_; 
v_str_682_ = lean_ctor_get(v_s_678_, 0);
v_startInclusive_683_ = lean_ctor_get(v_s_678_, 1);
v_isSharedCheck_692_ = !lean_is_exclusive(v_s_678_);
if (v_isSharedCheck_692_ == 0)
{
lean_object* v_unused_693_; 
v_unused_693_ = lean_ctor_get(v_s_678_, 2);
lean_dec(v_unused_693_);
v___x_685_ = v_s_678_;
v_isShared_686_ = v_isSharedCheck_692_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_startInclusive_683_);
lean_inc(v_str_682_);
lean_dec(v_s_678_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_692_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_687_ = lean_nat_add(v_startInclusive_683_, v_newStart_679_);
v___x_688_ = lean_nat_add(v_startInclusive_683_, v_newEnd_680_);
lean_dec(v_startInclusive_683_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 2, v___x_688_);
lean_ctor_set(v___x_685_, 1, v___x_687_);
v___x_690_ = v___x_685_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_str_682_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_691_, 2, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___boxed(lean_object* v_s_694_, lean_object* v_newStart_695_, lean_object* v_newEnd_696_, lean_object* v_h_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_String_Slice_slice(v_s_694_, v_newStart_695_, v_newEnd_696_, v_h_697_);
lean_dec(v_newEnd_696_);
lean_dec(v_newStart_695_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg(lean_object* v_s_699_, lean_object* v_newStart_700_, lean_object* v_newEnd_701_){
_start:
{
lean_object* v_str_702_; lean_object* v_startInclusive_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_712_; 
v_str_702_ = lean_ctor_get(v_s_699_, 0);
v_startInclusive_703_ = lean_ctor_get(v_s_699_, 1);
v_isSharedCheck_712_ = !lean_is_exclusive(v_s_699_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; 
v_unused_713_ = lean_ctor_get(v_s_699_, 2);
lean_dec(v_unused_713_);
v___x_705_ = v_s_699_;
v_isShared_706_ = v_isSharedCheck_712_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_startInclusive_703_);
lean_inc(v_str_702_);
lean_dec(v_s_699_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_712_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_707_ = lean_nat_add(v_startInclusive_703_, v_newStart_700_);
v___x_708_ = lean_nat_add(v_startInclusive_703_, v_newEnd_701_);
lean_dec(v_startInclusive_703_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 2, v___x_708_);
lean_ctor_set(v___x_705_, 1, v___x_707_);
v___x_710_ = v___x_705_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_str_702_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_711_, 2, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg___boxed(lean_object* v_s_714_, lean_object* v_newStart_715_, lean_object* v_newEnd_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_String_Slice_replaceStartEnd___redArg(v_s_714_, v_newStart_715_, v_newEnd_716_);
lean_dec(v_newEnd_716_);
lean_dec(v_newStart_715_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd(lean_object* v_s_718_, lean_object* v_newStart_719_, lean_object* v_newEnd_720_, lean_object* v_h_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_String_Slice_replaceStartEnd___redArg(v_s_718_, v_newStart_719_, v_newEnd_720_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___boxed(lean_object* v_s_723_, lean_object* v_newStart_724_, lean_object* v_newEnd_725_, lean_object* v_h_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_String_Slice_replaceStartEnd(v_s_723_, v_newStart_724_, v_newEnd_725_, v_h_726_);
lean_dec(v_newEnd_725_);
lean_dec(v_newStart_724_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f(lean_object* v_s_728_, lean_object* v_newStart_729_, lean_object* v_newEnd_730_){
_start:
{
uint8_t v___x_731_; 
v___x_731_ = lean_nat_dec_le(v_newStart_729_, v_newEnd_730_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; 
lean_dec_ref(v_s_728_);
v___x_732_ = lean_box(0);
return v___x_732_;
}
else
{
lean_object* v_str_733_; lean_object* v_startInclusive_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_744_; 
v_str_733_ = lean_ctor_get(v_s_728_, 0);
v_startInclusive_734_ = lean_ctor_get(v_s_728_, 1);
v_isSharedCheck_744_ = !lean_is_exclusive(v_s_728_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; 
v_unused_745_ = lean_ctor_get(v_s_728_, 2);
lean_dec(v_unused_745_);
v___x_736_ = v_s_728_;
v_isShared_737_ = v_isSharedCheck_744_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_startInclusive_734_);
lean_inc(v_str_733_);
lean_dec(v_s_728_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_744_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_738_ = lean_nat_add(v_startInclusive_734_, v_newStart_729_);
v___x_739_ = lean_nat_add(v_startInclusive_734_, v_newEnd_730_);
lean_dec(v_startInclusive_734_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 2, v___x_739_);
lean_ctor_set(v___x_736_, 1, v___x_738_);
v___x_741_ = v___x_736_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_str_733_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_743_, 2, v___x_739_);
v___x_741_ = v_reuseFailAlloc_743_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_742_; 
v___x_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
return v___x_742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f___boxed(lean_object* v_s_746_, lean_object* v_newStart_747_, lean_object* v_newEnd_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_String_Slice_slice_x3f(v_s_746_, v_newStart_747_, v_newEnd_748_);
lean_dec(v_newEnd_748_);
lean_dec(v_newStart_747_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_slice_x21_spec__0(lean_object* v_msg_750_){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = l_String_instInhabitedSlice;
v___x_752_ = lean_panic_fn_borrowed(v___x_751_, v_msg_750_);
return v___x_752_;
}
}
static lean_object* _init_l_String_Slice_slice_x21___closed__2(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_755_ = ((lean_object*)(l_String_Slice_slice_x21___closed__1));
v___x_756_ = lean_unsigned_to_nat(4u);
v___x_757_ = lean_unsigned_to_nat(1038u);
v___x_758_ = ((lean_object*)(l_String_Slice_slice_x21___closed__0));
v___x_759_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_760_ = l_mkPanicMessageWithDecl(v___x_759_, v___x_758_, v___x_757_, v___x_756_, v___x_755_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x21(lean_object* v_s_761_, lean_object* v_newStart_762_, lean_object* v_newEnd_763_){
_start:
{
uint8_t v___x_764_; 
v___x_764_ = lean_nat_dec_le(v_newStart_762_, v_newEnd_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_766_; 
lean_dec_ref(v_s_761_);
v___x_765_ = lean_obj_once(&l_String_Slice_slice_x21___closed__2, &l_String_Slice_slice_x21___closed__2_once, _init_l_String_Slice_slice_x21___closed__2);
v___x_766_ = l_panic___at___00String_Slice_slice_x21_spec__0(v___x_765_);
return v___x_766_;
}
else
{
lean_object* v_str_767_; lean_object* v_startInclusive_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_777_; 
v_str_767_ = lean_ctor_get(v_s_761_, 0);
v_startInclusive_768_ = lean_ctor_get(v_s_761_, 1);
v_isSharedCheck_777_ = !lean_is_exclusive(v_s_761_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; 
v_unused_778_ = lean_ctor_get(v_s_761_, 2);
lean_dec(v_unused_778_);
v___x_770_ = v_s_761_;
v_isShared_771_ = v_isSharedCheck_777_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_startInclusive_768_);
lean_inc(v_str_767_);
lean_dec(v_s_761_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_777_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_772_ = lean_nat_add(v_startInclusive_768_, v_newStart_762_);
v___x_773_ = lean_nat_add(v_startInclusive_768_, v_newEnd_763_);
lean_dec(v_startInclusive_768_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 2, v___x_773_);
lean_ctor_set(v___x_770_, 1, v___x_772_);
v___x_775_ = v___x_770_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_str_767_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x21___boxed(lean_object* v_s_779_, lean_object* v_newStart_780_, lean_object* v_newEnd_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_String_Slice_slice_x21(v_s_779_, v_newStart_780_, v_newEnd_781_);
lean_dec(v_newEnd_781_);
lean_dec(v_newStart_780_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21(lean_object* v_s_783_, lean_object* v_newStart_784_, lean_object* v_newEnd_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_String_Slice_slice_x21(v_s_783_, v_newStart_784_, v_newEnd_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21___boxed(lean_object* v_s_787_, lean_object* v_newStart_788_, lean_object* v_newEnd_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_String_Slice_replaceStartEnd_x21(v_s_787_, v_newStart_788_, v_newEnd_789_);
lean_dec(v_newEnd_789_);
lean_dec(v_newStart_788_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_String_decodeChar___boxed(lean_object* v_s_794_, lean_object* v_byteIdx_795_, lean_object* v_h_796_){
_start:
{
uint32_t v_res_797_; lean_object* v_r_798_; 
v_res_797_ = lean_string_utf8_get_fast(v_s_794_, v_byteIdx_795_);
lean_dec(v_byteIdx_795_);
lean_dec_ref(v_s_794_);
v_r_798_ = lean_box_uint32(v_res_797_);
return v_r_798_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get___redArg(lean_object* v_s_799_, lean_object* v_pos_800_){
_start:
{
lean_object* v_str_801_; lean_object* v_startInclusive_802_; lean_object* v___x_803_; uint32_t v___x_804_; 
v_str_801_ = lean_ctor_get(v_s_799_, 0);
v_startInclusive_802_ = lean_ctor_get(v_s_799_, 1);
v___x_803_ = lean_nat_add(v_startInclusive_802_, v_pos_800_);
v___x_804_ = lean_string_utf8_get_fast(v_str_801_, v___x_803_);
lean_dec(v___x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___redArg___boxed(lean_object* v_s_805_, lean_object* v_pos_806_){
_start:
{
uint32_t v_res_807_; lean_object* v_r_808_; 
v_res_807_ = l_String_Slice_Pos_get___redArg(v_s_805_, v_pos_806_);
lean_dec(v_pos_806_);
lean_dec_ref(v_s_805_);
v_r_808_ = lean_box_uint32(v_res_807_);
return v_r_808_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get(lean_object* v_s_809_, lean_object* v_pos_810_, lean_object* v_h_811_){
_start:
{
lean_object* v_str_812_; lean_object* v_startInclusive_813_; lean_object* v___x_814_; uint32_t v___x_815_; 
v_str_812_ = lean_ctor_get(v_s_809_, 0);
v_startInclusive_813_ = lean_ctor_get(v_s_809_, 1);
v___x_814_ = lean_nat_add(v_startInclusive_813_, v_pos_810_);
v___x_815_ = lean_string_utf8_get_fast(v_str_812_, v___x_814_);
lean_dec(v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___boxed(lean_object* v_s_816_, lean_object* v_pos_817_, lean_object* v_h_818_){
_start:
{
uint32_t v_res_819_; lean_object* v_r_820_; 
v_res_819_ = l_String_Slice_Pos_get(v_s_816_, v_pos_817_, v_h_818_);
lean_dec(v_pos_817_);
lean_dec_ref(v_s_816_);
v_r_820_ = lean_box_uint32(v_res_819_);
return v_r_820_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f(lean_object* v_s_821_, lean_object* v_pos_822_){
_start:
{
lean_object* v_str_823_; lean_object* v_startInclusive_824_; lean_object* v_endExclusive_825_; lean_object* v___x_826_; uint8_t v_decide_827_; 
v_str_823_ = lean_ctor_get(v_s_821_, 0);
v_startInclusive_824_ = lean_ctor_get(v_s_821_, 1);
v_endExclusive_825_ = lean_ctor_get(v_s_821_, 2);
v___x_826_ = lean_nat_sub(v_endExclusive_825_, v_startInclusive_824_);
v_decide_827_ = lean_nat_dec_eq(v_pos_822_, v___x_826_);
lean_dec(v___x_826_);
if (v_decide_827_ == 0)
{
lean_object* v___x_828_; uint32_t v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_828_ = lean_nat_add(v_startInclusive_824_, v_pos_822_);
v___x_829_ = lean_string_utf8_get_fast(v_str_823_, v___x_828_);
lean_dec(v___x_828_);
v___x_830_ = lean_box_uint32(v___x_829_);
v___x_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
return v___x_831_;
}
else
{
lean_object* v___x_832_; 
v___x_832_ = lean_box(0);
return v___x_832_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f___boxed(lean_object* v_s_833_, lean_object* v_pos_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_String_Slice_Pos_get_x3f(v_s_833_, v_pos_834_);
lean_dec(v_pos_834_);
lean_dec_ref(v_s_833_);
return v_res_835_;
}
}
static lean_object* _init_l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1(void){
_start:
{
uint32_t v___x_836_; lean_object* v___x_837_; 
v___x_836_ = 65;
v___x_837_ = lean_box_uint32(v___x_836_);
return v___x_837_;
}
}
LEAN_EXPORT uint32_t l_panic___at___00String_Slice_Pos_get_x21_spec__0(lean_object* v_msg_838_){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; uint32_t v___x_841_; 
v___x_839_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1;
v___x_840_ = lean_panic_fn_borrowed(v___x_839_, v_msg_838_);
v___x_841_ = lean_unbox_uint32(v___x_840_);
lean_dec(v___x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed(lean_object* v_msg_842_){
_start:
{
uint32_t v_res_843_; lean_object* v_r_844_; 
v_res_843_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v_msg_842_);
v_r_844_ = lean_box_uint32(v_res_843_);
return v_r_844_;
}
}
static lean_object* _init_l_String_Slice_Pos_get_x21___closed__2(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_847_ = ((lean_object*)(l_String_Slice_Pos_get_x21___closed__1));
v___x_848_ = lean_unsigned_to_nat(29u);
v___x_849_ = lean_unsigned_to_nat(1123u);
v___x_850_ = ((lean_object*)(l_String_Slice_Pos_get_x21___closed__0));
v___x_851_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_852_ = l_mkPanicMessageWithDecl(v___x_851_, v___x_850_, v___x_849_, v___x_848_, v___x_847_);
return v___x_852_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get_x21(lean_object* v_s_853_, lean_object* v_pos_854_){
_start:
{
lean_object* v_str_855_; lean_object* v_startInclusive_856_; lean_object* v_endExclusive_857_; lean_object* v___x_858_; uint8_t v_decide_859_; 
v_str_855_ = lean_ctor_get(v_s_853_, 0);
v_startInclusive_856_ = lean_ctor_get(v_s_853_, 1);
v_endExclusive_857_ = lean_ctor_get(v_s_853_, 2);
v___x_858_ = lean_nat_sub(v_endExclusive_857_, v_startInclusive_856_);
v_decide_859_ = lean_nat_dec_eq(v_pos_854_, v___x_858_);
lean_dec(v___x_858_);
if (v_decide_859_ == 0)
{
lean_object* v___x_860_; uint32_t v___x_861_; 
v___x_860_ = lean_nat_add(v_startInclusive_856_, v_pos_854_);
v___x_861_ = lean_string_utf8_get_fast(v_str_855_, v___x_860_);
lean_dec(v___x_860_);
return v___x_861_;
}
else
{
lean_object* v___x_862_; uint32_t v___x_863_; 
v___x_862_ = lean_obj_once(&l_String_Slice_Pos_get_x21___closed__2, &l_String_Slice_Pos_get_x21___closed__2_once, _init_l_String_Slice_Pos_get_x21___closed__2);
v___x_863_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v___x_862_);
return v___x_863_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x21___boxed(lean_object* v_s_864_, lean_object* v_pos_865_){
_start:
{
uint32_t v_res_866_; lean_object* v_r_867_; 
v_res_866_ = l_String_Slice_Pos_get_x21(v_s_864_, v_pos_865_);
lean_dec(v_pos_865_);
lean_dec_ref(v_s_864_);
v_r_867_ = lean_box_uint32(v_res_866_);
return v_r_867_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg(lean_object* v_pos_868_){
_start:
{
lean_inc(v_pos_868_);
return v_pos_868_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg___boxed(lean_object* v_pos_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_String_Pos_toSlice___redArg(v_pos_869_);
lean_dec(v_pos_869_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice(lean_object* v_s_871_, lean_object* v_pos_872_){
_start:
{
lean_inc(v_pos_872_);
return v_pos_872_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___boxed(lean_object* v_s_873_, lean_object* v_pos_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_String_Pos_toSlice(v_s_873_, v_pos_874_);
lean_dec(v_pos_874_);
lean_dec_ref(v_s_873_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg(lean_object* v_pos_876_){
_start:
{
lean_inc(v_pos_876_);
return v_pos_876_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg___boxed(lean_object* v_pos_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_String_Pos_ofToSlice___redArg(v_pos_877_);
lean_dec(v_pos_877_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice(lean_object* v_s_879_, lean_object* v_pos_880_){
_start:
{
lean_inc(v_pos_880_);
return v_pos_880_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___boxed(lean_object* v_s_881_, lean_object* v_pos_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_String_Pos_ofToSlice(v_s_881_, v_pos_882_);
lean_dec(v_pos_882_);
lean_dec_ref(v_s_881_);
return v_res_883_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get___redArg(lean_object* v_s_884_, lean_object* v_pos_885_){
_start:
{
uint32_t v___x_886_; 
v___x_886_ = lean_string_utf8_get_fast(v_s_884_, v_pos_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get___redArg___boxed(lean_object* v_s_887_, lean_object* v_pos_888_){
_start:
{
uint32_t v_res_889_; lean_object* v_r_890_; 
v_res_889_ = l_String_Pos_get___redArg(v_s_887_, v_pos_888_);
lean_dec(v_pos_888_);
lean_dec_ref(v_s_887_);
v_r_890_ = lean_box_uint32(v_res_889_);
return v_r_890_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get(lean_object* v_s_891_, lean_object* v_pos_892_, lean_object* v_h_893_){
_start:
{
uint32_t v___x_894_; 
v___x_894_ = lean_string_utf8_get_fast(v_s_891_, v_pos_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get___boxed(lean_object* v_s_895_, lean_object* v_pos_896_, lean_object* v_h_897_){
_start:
{
uint32_t v_res_898_; lean_object* v_r_899_; 
v_res_898_ = l_String_Pos_get(v_s_895_, v_pos_896_, v_h_897_);
lean_dec(v_pos_896_);
lean_dec_ref(v_s_895_);
v_r_899_ = lean_box_uint32(v_res_898_);
return v_r_899_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x3f(lean_object* v_s_900_, lean_object* v_pos_901_){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_902_ = lean_unsigned_to_nat(0u);
v___x_903_ = lean_string_utf8_byte_size(v_s_900_);
v___x_904_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_904_, 0, v_s_900_);
lean_ctor_set(v___x_904_, 1, v___x_902_);
lean_ctor_set(v___x_904_, 2, v___x_903_);
v___x_905_ = l_String_Slice_Pos_get_x3f(v___x_904_, v_pos_901_);
lean_dec_ref_known(v___x_904_, 3);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x3f___boxed(lean_object* v_s_906_, lean_object* v_pos_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_String_Pos_get_x3f(v_s_906_, v_pos_907_);
lean_dec(v_pos_907_);
return v_res_908_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get_x21(lean_object* v_s_909_, lean_object* v_pos_910_){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; uint32_t v___x_914_; 
v___x_911_ = lean_unsigned_to_nat(0u);
v___x_912_ = lean_string_utf8_byte_size(v_s_909_);
v___x_913_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_913_, 0, v_s_909_);
lean_ctor_set(v___x_913_, 1, v___x_911_);
lean_ctor_set(v___x_913_, 2, v___x_912_);
v___x_914_ = l_String_Slice_Pos_get_x21(v___x_913_, v_pos_910_);
lean_dec_ref_known(v___x_913_, 3);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x21___boxed(lean_object* v_s_915_, lean_object* v_pos_916_){
_start:
{
uint32_t v_res_917_; lean_object* v_r_918_; 
v_res_917_ = l_String_Pos_get_x21(v_s_915_, v_pos_916_);
lean_dec(v_pos_916_);
v_r_918_ = lean_box_uint32(v_res_917_);
return v_r_918_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_byte___redArg(lean_object* v_s_919_, lean_object* v_pos_920_){
_start:
{
uint8_t v___x_921_; 
v___x_921_ = lean_string_get_byte_fast(v_s_919_, v_pos_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_byte___redArg___boxed(lean_object* v_s_922_, lean_object* v_pos_923_){
_start:
{
uint8_t v_res_924_; lean_object* v_r_925_; 
v_res_924_ = l_String_Pos_byte___redArg(v_s_922_, v_pos_923_);
lean_dec_ref(v_s_922_);
v_r_925_ = lean_box(v_res_924_);
return v_r_925_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_byte(lean_object* v_s_926_, lean_object* v_pos_927_, lean_object* v_h_928_){
_start:
{
uint8_t v___x_929_; 
v___x_929_ = lean_string_get_byte_fast(v_s_926_, v_pos_927_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_byte___boxed(lean_object* v_s_930_, lean_object* v_pos_931_, lean_object* v_h_932_){
_start:
{
uint8_t v_res_933_; lean_object* v_r_934_; 
v_res_933_ = l_String_Pos_byte(v_s_930_, v_pos_931_, v_h_932_);
lean_dec_ref(v_s_930_);
v_r_934_ = lean_box(v_res_933_);
return v_r_934_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg(lean_object* v_pos_935_){
_start:
{
lean_inc(v_pos_935_);
return v_pos_935_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg___boxed(lean_object* v_pos_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_String_Pos_ofCopy___redArg(v_pos_936_);
lean_dec(v_pos_936_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy(lean_object* v_s_938_, lean_object* v_pos_939_){
_start:
{
lean_inc(v_pos_939_);
return v_pos_939_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___boxed(lean_object* v_s_940_, lean_object* v_pos_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_String_Pos_ofCopy(v_s_940_, v_pos_941_);
lean_dec(v_pos_941_);
lean_dec_ref(v_s_940_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg(lean_object* v_pos_943_){
_start:
{
lean_inc(v_pos_943_);
return v_pos_943_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg___boxed(lean_object* v_pos_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_String_Slice_Pos_copy___redArg(v_pos_944_);
lean_dec(v_pos_944_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy(lean_object* v_s_946_, lean_object* v_pos_947_){
_start:
{
lean_inc(v_pos_947_);
return v_pos_947_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___boxed(lean_object* v_s_948_, lean_object* v_pos_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_String_Slice_Pos_copy(v_s_948_, v_pos_949_);
lean_dec(v_pos_949_);
lean_dec_ref(v_s_948_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg(lean_object* v_pos_951_){
_start:
{
lean_inc(v_pos_951_);
return v_pos_951_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg___boxed(lean_object* v_pos_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_String_Slice_Pos_toCopy___redArg(v_pos_952_);
lean_dec(v_pos_952_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy(lean_object* v_s_954_, lean_object* v_pos_955_){
_start:
{
lean_inc(v_pos_955_);
return v_pos_955_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___boxed(lean_object* v_s_956_, lean_object* v_pos_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_String_Slice_Pos_toCopy(v_s_956_, v_pos_957_);
lean_dec(v_pos_957_);
lean_dec_ref(v_s_956_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg(lean_object* v_p_u2080_959_, lean_object* v_pos_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = lean_nat_add(v_p_u2080_959_, v_pos_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg___boxed(lean_object* v_p_u2080_962_, lean_object* v_pos_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_String_Slice_Pos_ofSliceFrom___redArg(v_p_u2080_962_, v_pos_963_);
lean_dec(v_pos_963_);
lean_dec(v_p_u2080_962_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom(lean_object* v_s_965_, lean_object* v_p_u2080_966_, lean_object* v_pos_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = lean_nat_add(v_p_u2080_966_, v_pos_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___boxed(lean_object* v_s_969_, lean_object* v_p_u2080_970_, lean_object* v_pos_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_String_Slice_Pos_ofSliceFrom(v_s_969_, v_p_u2080_970_, v_pos_971_);
lean_dec(v_pos_971_);
lean_dec(v_p_u2080_970_);
lean_dec_ref(v_s_969_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg(lean_object* v_p_u2080_973_, lean_object* v_pos_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = lean_nat_add(v_p_u2080_973_, v_pos_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg___boxed(lean_object* v_p_u2080_976_, lean_object* v_pos_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_String_Slice_Pos_ofReplaceStart___redArg(v_p_u2080_976_, v_pos_977_);
lean_dec(v_pos_977_);
lean_dec(v_p_u2080_976_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart(lean_object* v_s_979_, lean_object* v_p_u2080_980_, lean_object* v_pos_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = lean_nat_add(v_p_u2080_980_, v_pos_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___boxed(lean_object* v_s_983_, lean_object* v_p_u2080_984_, lean_object* v_pos_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_String_Slice_Pos_ofReplaceStart(v_s_983_, v_p_u2080_984_, v_pos_985_);
lean_dec(v_pos_985_);
lean_dec(v_p_u2080_984_);
lean_dec_ref(v_s_983_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg(lean_object* v_p_u2080_987_, lean_object* v_pos_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = lean_nat_sub(v_pos_988_, v_p_u2080_987_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg___boxed(lean_object* v_p_u2080_990_, lean_object* v_pos_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_String_Slice_Pos_sliceFrom___redArg(v_p_u2080_990_, v_pos_991_);
lean_dec(v_pos_991_);
lean_dec(v_p_u2080_990_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom(lean_object* v_s_993_, lean_object* v_p_u2080_994_, lean_object* v_pos_995_, lean_object* v_h_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = lean_nat_sub(v_pos_995_, v_p_u2080_994_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___boxed(lean_object* v_s_998_, lean_object* v_p_u2080_999_, lean_object* v_pos_1000_, lean_object* v_h_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_String_Slice_Pos_sliceFrom(v_s_998_, v_p_u2080_999_, v_pos_1000_, v_h_1001_);
lean_dec(v_pos_1000_);
lean_dec(v_p_u2080_999_);
lean_dec_ref(v_s_998_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg(lean_object* v_p_u2080_1003_, lean_object* v_pos_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_nat_sub(v_pos_1004_, v_p_u2080_1003_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg___boxed(lean_object* v_p_u2080_1006_, lean_object* v_pos_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_String_Slice_Pos_toReplaceStart___redArg(v_p_u2080_1006_, v_pos_1007_);
lean_dec(v_pos_1007_);
lean_dec(v_p_u2080_1006_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart(lean_object* v_s_1009_, lean_object* v_p_u2080_1010_, lean_object* v_pos_1011_, lean_object* v_h_1012_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_nat_sub(v_pos_1011_, v_p_u2080_1010_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___boxed(lean_object* v_s_1014_, lean_object* v_p_u2080_1015_, lean_object* v_pos_1016_, lean_object* v_h_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_String_Slice_Pos_toReplaceStart(v_s_1014_, v_p_u2080_1015_, v_pos_1016_, v_h_1017_);
lean_dec(v_pos_1016_);
lean_dec(v_p_u2080_1015_);
lean_dec_ref(v_s_1014_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg(lean_object* v_pos_1019_){
_start:
{
lean_inc(v_pos_1019_);
return v_pos_1019_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg___boxed(lean_object* v_pos_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_String_Slice_Pos_ofSliceTo___redArg(v_pos_1020_);
lean_dec(v_pos_1020_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo(lean_object* v_s_1022_, lean_object* v_p_u2080_1023_, lean_object* v_pos_1024_){
_start:
{
lean_inc(v_pos_1024_);
return v_pos_1024_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___boxed(lean_object* v_s_1025_, lean_object* v_p_u2080_1026_, lean_object* v_pos_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_String_Slice_Pos_ofSliceTo(v_s_1025_, v_p_u2080_1026_, v_pos_1027_);
lean_dec(v_pos_1027_);
lean_dec(v_p_u2080_1026_);
lean_dec_ref(v_s_1025_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg(lean_object* v_pos_1029_){
_start:
{
lean_inc(v_pos_1029_);
return v_pos_1029_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg___boxed(lean_object* v_pos_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_String_Slice_Pos_ofReplaceEnd___redArg(v_pos_1030_);
lean_dec(v_pos_1030_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd(lean_object* v_s_1032_, lean_object* v_p_u2080_1033_, lean_object* v_pos_1034_){
_start:
{
lean_inc(v_pos_1034_);
return v_pos_1034_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___boxed(lean_object* v_s_1035_, lean_object* v_p_u2080_1036_, lean_object* v_pos_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_String_Slice_Pos_ofReplaceEnd(v_s_1035_, v_p_u2080_1036_, v_pos_1037_);
lean_dec(v_pos_1037_);
lean_dec(v_p_u2080_1036_);
lean_dec_ref(v_s_1035_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg(lean_object* v_pos_1039_){
_start:
{
lean_inc(v_pos_1039_);
return v_pos_1039_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg___boxed(lean_object* v_pos_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_String_Slice_Pos_sliceTo___redArg(v_pos_1040_);
lean_dec(v_pos_1040_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo(lean_object* v_s_1042_, lean_object* v_p_u2080_1043_, lean_object* v_pos_1044_, lean_object* v_h_1045_){
_start:
{
lean_inc(v_pos_1044_);
return v_pos_1044_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___boxed(lean_object* v_s_1046_, lean_object* v_p_u2080_1047_, lean_object* v_pos_1048_, lean_object* v_h_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_String_Slice_Pos_sliceTo(v_s_1046_, v_p_u2080_1047_, v_pos_1048_, v_h_1049_);
lean_dec(v_pos_1048_);
lean_dec(v_p_u2080_1047_);
lean_dec_ref(v_s_1046_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg(lean_object* v_pos_1051_){
_start:
{
lean_inc(v_pos_1051_);
return v_pos_1051_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg___boxed(lean_object* v_pos_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_String_Slice_Pos_toReplaceEnd___redArg(v_pos_1052_);
lean_dec(v_pos_1052_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd(lean_object* v_s_1054_, lean_object* v_p_u2080_1055_, lean_object* v_pos_1056_, lean_object* v_h_1057_){
_start:
{
lean_inc(v_pos_1056_);
return v_pos_1056_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___boxed(lean_object* v_s_1058_, lean_object* v_p_u2080_1059_, lean_object* v_pos_1060_, lean_object* v_h_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_String_Slice_Pos_toReplaceEnd(v_s_1058_, v_p_u2080_1059_, v_pos_1060_, v_h_1061_);
lean_dec(v_pos_1060_);
lean_dec(v_p_u2080_1059_);
lean_dec_ref(v_s_1058_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg(lean_object* v_s_1063_, lean_object* v_pos_1064_){
_start:
{
lean_object* v_str_1065_; lean_object* v_startInclusive_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; uint8_t v___x_1069_; uint8_t v___x_1070_; uint8_t v___x_1071_; uint8_t v___x_1072_; 
v_str_1065_ = lean_ctor_get(v_s_1063_, 0);
v_startInclusive_1066_ = lean_ctor_get(v_s_1063_, 1);
v___x_1067_ = lean_nat_add(v_startInclusive_1066_, v_pos_1064_);
v___x_1068_ = lean_string_get_byte_fast(v_str_1065_, v___x_1067_);
v___x_1069_ = 128;
v___x_1070_ = lean_uint8_land(v___x_1068_, v___x_1069_);
v___x_1071_ = 0;
v___x_1072_ = lean_uint8_dec_eq(v___x_1070_, v___x_1071_);
if (v___x_1072_ == 0)
{
uint8_t v___x_1073_; uint8_t v___x_1074_; uint8_t v___x_1075_; uint8_t v___x_1076_; 
v___x_1073_ = 224;
v___x_1074_ = lean_uint8_land(v___x_1068_, v___x_1073_);
v___x_1075_ = 192;
v___x_1076_ = lean_uint8_dec_eq(v___x_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
uint8_t v___x_1077_; uint8_t v___x_1078_; uint8_t v___x_1079_; 
v___x_1077_ = 240;
v___x_1078_ = lean_uint8_land(v___x_1068_, v___x_1077_);
v___x_1079_ = lean_uint8_dec_eq(v___x_1078_, v___x_1073_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_unsigned_to_nat(4u);
v___x_1081_ = lean_nat_add(v_pos_1064_, v___x_1080_);
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = lean_unsigned_to_nat(3u);
v___x_1083_ = lean_nat_add(v_pos_1064_, v___x_1082_);
return v___x_1083_;
}
}
else
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_unsigned_to_nat(2u);
v___x_1085_ = lean_nat_add(v_pos_1064_, v___x_1084_);
return v___x_1085_;
}
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_unsigned_to_nat(1u);
v___x_1087_ = lean_nat_add(v_pos_1064_, v___x_1086_);
return v___x_1087_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg___boxed(lean_object* v_s_1088_, lean_object* v_pos_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_String_Slice_Pos_next___redArg(v_s_1088_, v_pos_1089_);
lean_dec(v_pos_1089_);
lean_dec_ref(v_s_1088_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next(lean_object* v_s_1091_, lean_object* v_pos_1092_, lean_object* v_h_1093_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_String_Slice_Pos_next___redArg(v_s_1091_, v_pos_1092_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___boxed(lean_object* v_s_1095_, lean_object* v_pos_1096_, lean_object* v_h_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_String_Slice_Pos_next(v_s_1095_, v_pos_1096_, v_h_1097_);
lean_dec(v_pos_1096_);
lean_dec_ref(v_s_1095_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f(lean_object* v_s_1099_, lean_object* v_pos_1100_){
_start:
{
lean_object* v_startInclusive_1101_; lean_object* v_endExclusive_1102_; lean_object* v___x_1103_; uint8_t v_decide_1104_; 
v_startInclusive_1101_ = lean_ctor_get(v_s_1099_, 1);
v_endExclusive_1102_ = lean_ctor_get(v_s_1099_, 2);
v___x_1103_ = lean_nat_sub(v_endExclusive_1102_, v_startInclusive_1101_);
v_decide_1104_ = lean_nat_dec_eq(v_pos_1100_, v___x_1103_);
lean_dec(v___x_1103_);
if (v_decide_1104_ == 0)
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = l_String_Slice_Pos_next___redArg(v_s_1099_, v_pos_1100_);
v___x_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
return v___x_1106_;
}
else
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_box(0);
return v___x_1107_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f___boxed(lean_object* v_s_1108_, lean_object* v_pos_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_String_Slice_Pos_next_x3f(v_s_1108_, v_pos_1109_);
lean_dec(v_pos_1109_);
lean_dec_ref(v_s_1108_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(lean_object* v_msg_1111_){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = lean_unsigned_to_nat(0u);
v___x_1113_ = lean_panic_fn_borrowed(v___x_1112_, v_msg_1111_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0(lean_object* v_s_1114_, lean_object* v_msg_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v_msg_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___boxed(lean_object* v_s_1117_, lean_object* v_msg_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0(v_s_1117_, v_msg_1118_);
lean_dec_ref(v_s_1117_);
return v_res_1119_;
}
}
static lean_object* _init_l_String_Slice_Pos_next_x21___closed__2(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1122_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__1));
v___x_1123_ = lean_unsigned_to_nat(29u);
v___x_1124_ = lean_unsigned_to_nat(1510u);
v___x_1125_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__0));
v___x_1126_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1127_ = l_mkPanicMessageWithDecl(v___x_1126_, v___x_1125_, v___x_1124_, v___x_1123_, v___x_1122_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21(lean_object* v_s_1128_, lean_object* v_pos_1129_){
_start:
{
lean_object* v_startInclusive_1130_; lean_object* v_endExclusive_1131_; lean_object* v___x_1132_; uint8_t v_decide_1133_; 
v_startInclusive_1130_ = lean_ctor_get(v_s_1128_, 1);
v_endExclusive_1131_ = lean_ctor_get(v_s_1128_, 2);
v___x_1132_ = lean_nat_sub(v_endExclusive_1131_, v_startInclusive_1130_);
v_decide_1133_ = lean_nat_dec_eq(v_pos_1129_, v___x_1132_);
lean_dec(v___x_1132_);
if (v_decide_1133_ == 0)
{
lean_object* v___x_1134_; 
v___x_1134_ = l_String_Slice_Pos_next___redArg(v_s_1128_, v_pos_1129_);
return v___x_1134_;
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_obj_once(&l_String_Slice_Pos_next_x21___closed__2, &l_String_Slice_Pos_next_x21___closed__2_once, _init_l_String_Slice_Pos_next_x21___closed__2);
v___x_1136_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_1135_);
return v___x_1136_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21___boxed(lean_object* v_s_1137_, lean_object* v_pos_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_String_Slice_Pos_next_x21(v_s_1137_, v_pos_1138_);
lean_dec(v_pos_1138_);
lean_dec_ref(v_s_1137_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg(lean_object* v_s_1140_, lean_object* v_off_1141_){
_start:
{
lean_object* v_str_1142_; lean_object* v_startInclusive_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; uint8_t v___x_1146_; uint8_t v___x_1147_; uint8_t v___x_1148_; uint8_t v___x_1149_; 
v_str_1142_ = lean_ctor_get(v_s_1140_, 0);
v_startInclusive_1143_ = lean_ctor_get(v_s_1140_, 1);
v___x_1144_ = lean_nat_add(v_startInclusive_1143_, v_off_1141_);
v___x_1145_ = lean_string_get_byte_fast(v_str_1142_, v___x_1144_);
v___x_1146_ = 128;
v___x_1147_ = lean_uint8_land(v___x_1145_, v___x_1146_);
v___x_1148_ = 0;
v___x_1149_ = lean_uint8_dec_eq(v___x_1147_, v___x_1148_);
if (v___x_1149_ == 0)
{
uint8_t v___x_1150_; uint8_t v___x_1151_; uint8_t v___x_1152_; uint8_t v___x_1153_; 
v___x_1150_ = 224;
v___x_1151_ = lean_uint8_land(v___x_1145_, v___x_1150_);
v___x_1152_ = 192;
v___x_1153_ = lean_uint8_dec_eq(v___x_1151_, v___x_1152_);
if (v___x_1153_ == 0)
{
uint8_t v___x_1154_; uint8_t v___x_1155_; uint8_t v___x_1156_; 
v___x_1154_ = 240;
v___x_1155_ = lean_uint8_land(v___x_1145_, v___x_1154_);
v___x_1156_ = lean_uint8_dec_eq(v___x_1155_, v___x_1150_);
if (v___x_1156_ == 0)
{
uint8_t v___x_1157_; uint8_t v___x_1158_; uint8_t v___x_1159_; 
v___x_1157_ = 248;
v___x_1158_ = lean_uint8_land(v___x_1145_, v___x_1157_);
v___x_1159_ = lean_uint8_dec_eq(v___x_1158_, v___x_1154_);
if (v___x_1159_ == 0)
{
lean_object* v_zero_1160_; uint8_t v_isZero_1161_; lean_object* v_one_1162_; lean_object* v_n_1163_; 
v_zero_1160_ = lean_unsigned_to_nat(0u);
v_isZero_1161_ = lean_nat_dec_eq(v_off_1141_, v_zero_1160_);
v_one_1162_ = lean_unsigned_to_nat(1u);
v_n_1163_ = lean_nat_sub(v_off_1141_, v_one_1162_);
lean_dec(v_off_1141_);
v_off_1141_ = v_n_1163_;
goto _start;
}
else
{
return v_off_1141_;
}
}
else
{
return v_off_1141_;
}
}
else
{
return v_off_1141_;
}
}
else
{
return v_off_1141_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg___boxed(lean_object* v_s_1165_, lean_object* v_off_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1165_, v_off_1166_);
lean_dec_ref(v_s_1165_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go(lean_object* v_s_1168_, lean_object* v_off_1169_, lean_object* v_h_u2081_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1168_, v_off_1169_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___boxed(lean_object* v_s_1172_, lean_object* v_off_1173_, lean_object* v_h_u2081_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_String_Slice_Pos_prevAux_go(v_s_1172_, v_off_1173_, v_h_u2081_1174_);
lean_dec_ref(v_s_1172_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg(lean_object* v_s_1176_, lean_object* v_pos_1177_){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1178_ = lean_unsigned_to_nat(1u);
v___x_1179_ = lean_nat_sub(v_pos_1177_, v___x_1178_);
v___x_1180_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1176_, v___x_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg___boxed(lean_object* v_s_1181_, lean_object* v_pos_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_String_Slice_Pos_prevAux___redArg(v_s_1181_, v_pos_1182_);
lean_dec(v_pos_1182_);
lean_dec_ref(v_s_1181_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux(lean_object* v_s_1184_, lean_object* v_pos_1185_, lean_object* v_h_1186_){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1187_ = lean_unsigned_to_nat(1u);
v___x_1188_ = lean_nat_sub(v_pos_1185_, v___x_1187_);
v___x_1189_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1184_, v___x_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___boxed(lean_object* v_s_1190_, lean_object* v_pos_1191_, lean_object* v_h_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_String_Slice_Pos_prevAux(v_s_1190_, v_pos_1191_, v_h_1192_);
lean_dec(v_pos_1191_);
lean_dec_ref(v_s_1190_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(lean_object* v_off_1194_, lean_object* v_h__1_1195_, lean_object* v_h__2_1196_){
_start:
{
lean_object* v_zero_1197_; uint8_t v_isZero_1198_; 
v_zero_1197_ = lean_unsigned_to_nat(0u);
v_isZero_1198_ = lean_nat_dec_eq(v_off_1194_, v_zero_1197_);
if (v_isZero_1198_ == 1)
{
lean_object* v___x_1199_; 
lean_dec(v_h__2_1196_);
v___x_1199_ = lean_apply_3(v_h__1_1195_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1199_;
}
else
{
lean_object* v_one_1200_; lean_object* v_n_1201_; lean_object* v___x_1202_; 
lean_dec(v_h__1_1195_);
v_one_1200_ = lean_unsigned_to_nat(1u);
v_n_1201_ = lean_nat_sub(v_off_1194_, v_one_1200_);
v___x_1202_ = lean_apply_4(v_h__2_1196_, v_n_1201_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg___boxed(lean_object* v_off_1203_, lean_object* v_h__1_1204_, lean_object* v_h__2_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(v_off_1203_, v_h__1_1204_, v_h__2_1205_);
lean_dec(v_off_1203_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(lean_object* v_s_1207_, lean_object* v_motive_1208_, lean_object* v_off_1209_, lean_object* v_h_u2081_1210_, lean_object* v_hbyte_1211_, lean_object* v_this_1212_, lean_object* v_h__1_1213_, lean_object* v_h__2_1214_){
_start:
{
lean_object* v_zero_1215_; uint8_t v_isZero_1216_; 
v_zero_1215_ = lean_unsigned_to_nat(0u);
v_isZero_1216_ = lean_nat_dec_eq(v_off_1209_, v_zero_1215_);
if (v_isZero_1216_ == 1)
{
lean_object* v___x_1217_; 
lean_dec(v_h__2_1214_);
v___x_1217_ = lean_apply_3(v_h__1_1213_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1217_;
}
else
{
lean_object* v_one_1218_; lean_object* v_n_1219_; lean_object* v___x_1220_; 
lean_dec(v_h__1_1213_);
v_one_1218_ = lean_unsigned_to_nat(1u);
v_n_1219_ = lean_nat_sub(v_off_1209_, v_one_1218_);
v___x_1220_ = lean_apply_4(v_h__2_1214_, v_n_1219_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___boxed(lean_object* v_s_1221_, lean_object* v_motive_1222_, lean_object* v_off_1223_, lean_object* v_h_u2081_1224_, lean_object* v_hbyte_1225_, lean_object* v_this_1226_, lean_object* v_h__1_1227_, lean_object* v_h__2_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(v_s_1221_, v_motive_1222_, v_off_1223_, v_h_u2081_1224_, v_hbyte_1225_, v_this_1226_, v_h__1_1227_, v_h__2_1228_);
lean_dec(v_off_1223_);
lean_dec_ref(v_s_1221_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg(lean_object* v_off_1230_){
_start:
{
lean_inc(v_off_1230_);
return v_off_1230_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg___boxed(lean_object* v_off_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_String_Slice_pos___redArg(v_off_1231_);
lean_dec(v_off_1231_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos(lean_object* v_s_1233_, lean_object* v_off_1234_, lean_object* v_h_1235_){
_start:
{
lean_inc(v_off_1234_);
return v_off_1234_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___boxed(lean_object* v_s_1236_, lean_object* v_off_1237_, lean_object* v_h_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_String_Slice_pos(v_s_1236_, v_off_1237_, v_h_1238_);
lean_dec(v_off_1237_);
lean_dec_ref(v_s_1236_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f(lean_object* v_s_1240_, lean_object* v_off_1241_){
_start:
{
uint8_t v___x_1242_; 
v___x_1242_ = l_String_Pos_Raw_isValidForSlice(v_s_1240_, v_off_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; 
lean_dec(v_off_1241_);
v___x_1243_ = lean_box(0);
return v___x_1243_;
}
else
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1244_, 0, v_off_1241_);
return v___x_1244_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f___boxed(lean_object* v_s_1245_, lean_object* v_off_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_String_Slice_pos_x3f(v_s_1245_, v_off_1246_);
lean_dec_ref(v_s_1245_);
return v_res_1247_;
}
}
static lean_object* _init_l_String_Slice_pos_x21___closed__2(void){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1250_ = ((lean_object*)(l_String_Slice_pos_x21___closed__1));
v___x_1251_ = lean_unsigned_to_nat(4u);
v___x_1252_ = lean_unsigned_to_nat(1598u);
v___x_1253_ = ((lean_object*)(l_String_Slice_pos_x21___closed__0));
v___x_1254_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1255_ = l_mkPanicMessageWithDecl(v___x_1254_, v___x_1253_, v___x_1252_, v___x_1251_, v___x_1250_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21(lean_object* v_s_1256_, lean_object* v_off_1257_){
_start:
{
uint8_t v___x_1258_; 
v___x_1258_ = l_String_Pos_Raw_isValidForSlice(v_s_1256_, v_off_1257_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = lean_obj_once(&l_String_Slice_pos_x21___closed__2, &l_String_Slice_pos_x21___closed__2_once, _init_l_String_Slice_pos_x21___closed__2);
v___x_1260_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_1259_);
return v___x_1260_;
}
else
{
lean_inc(v_off_1257_);
return v_off_1257_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21___boxed(lean_object* v_s_1261_, lean_object* v_off_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_String_Slice_pos_x21(v_s_1261_, v_off_1262_);
lean_dec(v_off_1262_);
lean_dec_ref(v_s_1261_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next___boxed(lean_object* v_s_1267_, lean_object* v_pos_1268_, lean_object* v_h_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = lean_string_utf8_next_fast(v_s_1267_, v_pos_1268_);
lean_dec(v_pos_1268_);
lean_dec_ref(v_s_1267_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x3f(lean_object* v_s_1271_, lean_object* v_pos_1272_){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1273_ = lean_unsigned_to_nat(0u);
v___x_1274_ = lean_string_utf8_byte_size(v_s_1271_);
v___x_1275_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1275_, 0, v_s_1271_);
lean_ctor_set(v___x_1275_, 1, v___x_1273_);
lean_ctor_set(v___x_1275_, 2, v___x_1274_);
v___x_1276_ = l_String_Slice_Pos_next_x3f(v___x_1275_, v_pos_1272_);
lean_dec_ref_known(v___x_1275_, 3);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v___x_1277_; 
v___x_1277_ = lean_box(0);
return v___x_1277_;
}
else
{
lean_object* v_val_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
v_val_1278_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1276_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_val_1278_);
lean_dec(v___x_1276_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_val_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x3f___boxed(lean_object* v_s_1286_, lean_object* v_pos_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_String_Pos_next_x3f(v_s_1286_, v_pos_1287_);
lean_dec(v_pos_1287_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21(lean_object* v_s_1289_, lean_object* v_pos_1290_){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1291_ = lean_unsigned_to_nat(0u);
v___x_1292_ = lean_string_utf8_byte_size(v_s_1289_);
v___x_1293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1293_, 0, v_s_1289_);
lean_ctor_set(v___x_1293_, 1, v___x_1291_);
lean_ctor_set(v___x_1293_, 2, v___x_1292_);
v___x_1294_ = l_String_Slice_Pos_next_x21(v___x_1293_, v_pos_1290_);
lean_dec_ref_known(v___x_1293_, 3);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21___boxed(lean_object* v_s_1295_, lean_object* v_pos_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_String_Pos_next_x21(v_s_1295_, v_pos_1296_);
lean_dec(v_pos_1296_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg(lean_object* v_off_1298_){
_start:
{
lean_inc(v_off_1298_);
return v_off_1298_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg___boxed(lean_object* v_off_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_String_pos___redArg(v_off_1299_);
lean_dec(v_off_1299_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_String_pos(lean_object* v_s_1301_, lean_object* v_off_1302_, lean_object* v_h_1303_){
_start:
{
lean_inc(v_off_1302_);
return v_off_1302_;
}
}
LEAN_EXPORT lean_object* l_String_pos___boxed(lean_object* v_s_1304_, lean_object* v_off_1305_, lean_object* v_h_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_String_pos(v_s_1304_, v_off_1305_, v_h_1306_);
lean_dec(v_off_1305_);
lean_dec_ref(v_s_1304_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x3f(lean_object* v_s_1308_, lean_object* v_off_1309_){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1310_ = lean_unsigned_to_nat(0u);
v___x_1311_ = lean_string_utf8_byte_size(v_s_1308_);
v___x_1312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1312_, 0, v_s_1308_);
lean_ctor_set(v___x_1312_, 1, v___x_1310_);
lean_ctor_set(v___x_1312_, 2, v___x_1311_);
v___x_1313_ = l_String_Slice_pos_x3f(v___x_1312_, v_off_1309_);
lean_dec_ref_known(v___x_1312_, 3);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v___x_1314_; 
v___x_1314_ = lean_box(0);
return v___x_1314_;
}
else
{
lean_object* v_val_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
v_val_1315_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1313_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_val_1315_);
lean_dec(v___x_1313_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_val_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_pos_x21(lean_object* v_s_1323_, lean_object* v_off_1324_){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1325_ = lean_unsigned_to_nat(0u);
v___x_1326_ = lean_string_utf8_byte_size(v_s_1323_);
v___x_1327_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1327_, 0, v_s_1323_);
lean_ctor_set(v___x_1327_, 1, v___x_1325_);
lean_ctor_set(v___x_1327_, 2, v___x_1326_);
v___x_1328_ = l_String_Slice_pos_x21(v___x_1327_, v_off_1324_);
lean_dec_ref_known(v___x_1327_, 3);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x21___boxed(lean_object* v_s_1329_, lean_object* v_off_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_String_pos_x21(v_s_1329_, v_off_1330_);
lean_dec(v_off_1330_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg(lean_object* v_pos_1332_){
_start:
{
lean_inc(v_pos_1332_);
return v_pos_1332_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg___boxed(lean_object* v_pos_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_String_Slice_Pos_cast___redArg(v_pos_1333_);
lean_dec(v_pos_1333_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast(lean_object* v_s_1335_, lean_object* v_t_1336_, lean_object* v_pos_1337_, lean_object* v_h_1338_){
_start:
{
lean_inc(v_pos_1337_);
return v_pos_1337_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___boxed(lean_object* v_s_1339_, lean_object* v_t_1340_, lean_object* v_pos_1341_, lean_object* v_h_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_String_Slice_Pos_cast(v_s_1339_, v_t_1340_, v_pos_1341_, v_h_1342_);
lean_dec(v_pos_1341_);
lean_dec_ref(v_t_1340_);
lean_dec_ref(v_s_1339_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg(lean_object* v_pos_1344_){
_start:
{
lean_inc(v_pos_1344_);
return v_pos_1344_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg___boxed(lean_object* v_pos_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_String_Pos_cast___redArg(v_pos_1345_);
lean_dec(v_pos_1345_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast(lean_object* v_s_1347_, lean_object* v_t_1348_, lean_object* v_pos_1349_, lean_object* v_h_1350_){
_start:
{
lean_inc(v_pos_1349_);
return v_pos_1349_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___boxed(lean_object* v_s_1351_, lean_object* v_t_1352_, lean_object* v_pos_1353_, lean_object* v_h_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_String_Pos_cast(v_s_1351_, v_t_1352_, v_pos_1353_, v_h_1354_);
lean_dec(v_pos_1353_);
lean_dec_ref(v_t_1352_);
lean_dec_ref(v_s_1351_);
return v_res_1355_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_Raw_utf8GetAux(lean_object* v_x_1356_, lean_object* v_x_1357_, lean_object* v_x_1358_){
_start:
{
if (lean_obj_tag(v_x_1356_) == 0)
{
uint32_t v___x_1359_; 
lean_dec(v_x_1357_);
v___x_1359_ = 65;
return v___x_1359_;
}
else
{
lean_object* v_head_1360_; lean_object* v_tail_1361_; lean_object* v___y_1363_; uint8_t v_decide_1366_; 
v_head_1360_ = lean_ctor_get(v_x_1356_, 0);
v_tail_1361_ = lean_ctor_get(v_x_1356_, 1);
v_decide_1366_ = lean_nat_dec_eq(v_x_1357_, v_x_1358_);
if (v_decide_1366_ == 0)
{
uint32_t v___x_1367_; uint32_t v___x_1368_; uint8_t v___x_1369_; 
v___x_1367_ = 127;
v___x_1368_ = lean_unbox_uint32(v_head_1360_);
v___x_1369_ = lean_uint32_dec_le(v___x_1368_, v___x_1367_);
if (v___x_1369_ == 0)
{
uint32_t v___x_1370_; uint32_t v___x_1371_; uint8_t v___x_1372_; 
v___x_1370_ = 2047;
v___x_1371_ = lean_unbox_uint32(v_head_1360_);
v___x_1372_ = lean_uint32_dec_le(v___x_1371_, v___x_1370_);
if (v___x_1372_ == 0)
{
uint32_t v___x_1373_; uint32_t v___x_1374_; uint8_t v___x_1375_; 
v___x_1373_ = 65535;
v___x_1374_ = lean_unbox_uint32(v_head_1360_);
v___x_1375_ = lean_uint32_dec_le(v___x_1374_, v___x_1373_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_unsigned_to_nat(4u);
v___y_1363_ = v___x_1376_;
goto v___jp_1362_;
}
else
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_unsigned_to_nat(3u);
v___y_1363_ = v___x_1377_;
goto v___jp_1362_;
}
}
else
{
lean_object* v___x_1378_; 
v___x_1378_ = lean_unsigned_to_nat(2u);
v___y_1363_ = v___x_1378_;
goto v___jp_1362_;
}
}
else
{
lean_object* v___x_1379_; 
v___x_1379_ = lean_unsigned_to_nat(1u);
v___y_1363_ = v___x_1379_;
goto v___jp_1362_;
}
}
else
{
uint32_t v___x_1380_; 
lean_dec(v_x_1357_);
v___x_1380_ = lean_unbox_uint32(v_head_1360_);
return v___x_1380_;
}
v___jp_1362_:
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_nat_add(v_x_1357_, v___y_1363_);
lean_dec(v_x_1357_);
v_x_1356_ = v_tail_1361_;
v_x_1357_ = v___x_1364_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux___boxed(lean_object* v_x_1381_, lean_object* v_x_1382_, lean_object* v_x_1383_){
_start:
{
uint32_t v_res_1384_; lean_object* v_r_1385_; 
v_res_1384_ = l_String_Pos_Raw_utf8GetAux(v_x_1381_, v_x_1382_, v_x_1383_);
lean_dec(v_x_1383_);
lean_dec(v_x_1381_);
v_r_1385_ = lean_box_uint32(v_res_1384_);
return v_r_1385_;
}
}
LEAN_EXPORT uint32_t l_String_utf8GetAux(lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_){
_start:
{
uint32_t v___x_1389_; 
v___x_1389_ = l_String_Pos_Raw_utf8GetAux(v_a_1386_, v_a_1387_, v_a_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux___boxed(lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
uint32_t v_res_1393_; lean_object* v_r_1394_; 
v_res_1393_ = l_String_utf8GetAux(v_a_1390_, v_a_1391_, v_a_1392_);
lean_dec(v_a_1392_);
lean_dec(v_a_1390_);
v_r_1394_ = lean_box_uint32(v_res_1393_);
return v_r_1394_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get___boxed(lean_object* v_s_1397_, lean_object* v_p_1398_){
_start:
{
uint32_t v_res_1399_; lean_object* v_r_1400_; 
v_res_1399_ = lean_string_utf8_get(v_s_1397_, v_p_1398_);
lean_dec(v_p_1398_);
lean_dec_ref(v_s_1397_);
v_r_1400_ = lean_box_uint32(v_res_1399_);
return v_r_1400_;
}
}
LEAN_EXPORT lean_object* l_String_get___boxed(lean_object* v_s_1403_, lean_object* v_p_1404_){
_start:
{
uint32_t v_res_1405_; lean_object* v_r_1406_; 
v_res_1405_ = lean_string_utf8_get(v_s_1403_, v_p_1404_);
lean_dec(v_p_1404_);
lean_dec_ref(v_s_1403_);
v_r_1406_ = lean_box_uint32(v_res_1405_);
return v_r_1406_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f(lean_object* v_x_1407_, lean_object* v_x_1408_, lean_object* v_x_1409_){
_start:
{
if (lean_obj_tag(v_x_1407_) == 0)
{
lean_object* v___x_1410_; 
lean_dec(v_x_1408_);
v___x_1410_ = lean_box(0);
return v___x_1410_;
}
else
{
lean_object* v_head_1411_; lean_object* v_tail_1412_; lean_object* v___y_1414_; uint8_t v_decide_1417_; 
v_head_1411_ = lean_ctor_get(v_x_1407_, 0);
v_tail_1412_ = lean_ctor_get(v_x_1407_, 1);
v_decide_1417_ = lean_nat_dec_eq(v_x_1408_, v_x_1409_);
if (v_decide_1417_ == 0)
{
uint32_t v___x_1418_; uint32_t v___x_1419_; uint8_t v___x_1420_; 
v___x_1418_ = 127;
v___x_1419_ = lean_unbox_uint32(v_head_1411_);
v___x_1420_ = lean_uint32_dec_le(v___x_1419_, v___x_1418_);
if (v___x_1420_ == 0)
{
uint32_t v___x_1421_; uint32_t v___x_1422_; uint8_t v___x_1423_; 
v___x_1421_ = 2047;
v___x_1422_ = lean_unbox_uint32(v_head_1411_);
v___x_1423_ = lean_uint32_dec_le(v___x_1422_, v___x_1421_);
if (v___x_1423_ == 0)
{
uint32_t v___x_1424_; uint32_t v___x_1425_; uint8_t v___x_1426_; 
v___x_1424_ = 65535;
v___x_1425_ = lean_unbox_uint32(v_head_1411_);
v___x_1426_ = lean_uint32_dec_le(v___x_1425_, v___x_1424_);
if (v___x_1426_ == 0)
{
lean_object* v___x_1427_; 
v___x_1427_ = lean_unsigned_to_nat(4u);
v___y_1414_ = v___x_1427_;
goto v___jp_1413_;
}
else
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_unsigned_to_nat(3u);
v___y_1414_ = v___x_1428_;
goto v___jp_1413_;
}
}
else
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_unsigned_to_nat(2u);
v___y_1414_ = v___x_1429_;
goto v___jp_1413_;
}
}
else
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_unsigned_to_nat(1u);
v___y_1414_ = v___x_1430_;
goto v___jp_1413_;
}
}
else
{
lean_object* v___x_1431_; 
lean_dec(v_x_1408_);
lean_inc(v_head_1411_);
v___x_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1431_, 0, v_head_1411_);
return v___x_1431_;
}
v___jp_1413_:
{
lean_object* v___x_1415_; 
v___x_1415_ = lean_nat_add(v_x_1408_, v___y_1414_);
lean_dec(v_x_1408_);
v_x_1407_ = v_tail_1412_;
v_x_1408_ = v___x_1415_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f___boxed(lean_object* v_x_1432_, lean_object* v_x_1433_, lean_object* v_x_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_String_Pos_Raw_utf8GetAux_x3f(v_x_1432_, v_x_1433_, v_x_1434_);
lean_dec(v_x_1434_);
lean_dec(v_x_1432_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f(lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_String_Pos_Raw_utf8GetAux_x3f(v_a_1436_, v_a_1437_, v_a_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f___boxed(lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_String_utf8GetAux_x3f(v_a_1440_, v_a_1441_, v_a_1442_);
lean_dec(v_a_1442_);
lean_dec(v_a_1440_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1446_, lean_object* v_a_00___x40___internal___hyg_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1446_, v_a_00___x40___internal___hyg_1447_);
lean_dec(v_a_00___x40___internal___hyg_1447_);
lean_dec_ref(v_a_00___x40___internal___hyg_1446_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_String_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1451_, lean_object* v_a_00___x40___internal___hyg_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1451_, v_a_00___x40___internal___hyg_1452_);
lean_dec(v_a_00___x40___internal___hyg_1452_);
lean_dec_ref(v_a_00___x40___internal___hyg_1451_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x21___boxed(lean_object* v_s_1456_, lean_object* v_p_1457_){
_start:
{
uint32_t v_res_1458_; lean_object* v_r_1459_; 
v_res_1458_ = lean_string_utf8_get_bang(v_s_1456_, v_p_1457_);
lean_dec(v_p_1457_);
lean_dec_ref(v_s_1456_);
v_r_1459_ = lean_box_uint32(v_res_1458_);
return v_r_1459_;
}
}
LEAN_EXPORT lean_object* l_String_get_x21___boxed(lean_object* v_s_1462_, lean_object* v_p_1463_){
_start:
{
uint32_t v_res_1464_; lean_object* v_r_1465_; 
v_res_1464_ = lean_string_utf8_get_bang(v_s_1462_, v_p_1463_);
lean_dec(v_p_1463_);
lean_dec_ref(v_s_1462_);
v_r_1465_ = lean_box_uint32(v_res_1464_);
return v_r_1465_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux(uint32_t v_c_x27_1466_, lean_object* v_x_1467_, lean_object* v_x_1468_, lean_object* v_x_1469_){
_start:
{
if (lean_obj_tag(v_x_1467_) == 0)
{
return v_x_1467_;
}
else
{
lean_object* v_head_1470_; lean_object* v_tail_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1498_; 
v_head_1470_ = lean_ctor_get(v_x_1467_, 0);
v_tail_1471_ = lean_ctor_get(v_x_1467_, 1);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_x_1467_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1473_ = v_x_1467_;
v_isShared_1474_ = v_isSharedCheck_1498_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_tail_1471_);
lean_inc(v_head_1470_);
lean_dec(v_x_1467_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1498_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___y_1476_; uint8_t v_decide_1482_; 
v_decide_1482_ = lean_nat_dec_eq(v_x_1468_, v_x_1469_);
if (v_decide_1482_ == 0)
{
uint32_t v___x_1483_; uint32_t v___x_1484_; uint8_t v___x_1485_; 
v___x_1483_ = 127;
v___x_1484_ = lean_unbox_uint32(v_head_1470_);
v___x_1485_ = lean_uint32_dec_le(v___x_1484_, v___x_1483_);
if (v___x_1485_ == 0)
{
uint32_t v___x_1486_; uint32_t v___x_1487_; uint8_t v___x_1488_; 
v___x_1486_ = 2047;
v___x_1487_ = lean_unbox_uint32(v_head_1470_);
v___x_1488_ = lean_uint32_dec_le(v___x_1487_, v___x_1486_);
if (v___x_1488_ == 0)
{
uint32_t v___x_1489_; uint32_t v___x_1490_; uint8_t v___x_1491_; 
v___x_1489_ = 65535;
v___x_1490_ = lean_unbox_uint32(v_head_1470_);
v___x_1491_ = lean_uint32_dec_le(v___x_1490_, v___x_1489_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; 
v___x_1492_ = lean_unsigned_to_nat(4u);
v___y_1476_ = v___x_1492_;
goto v___jp_1475_;
}
else
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_unsigned_to_nat(3u);
v___y_1476_ = v___x_1493_;
goto v___jp_1475_;
}
}
else
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_unsigned_to_nat(2u);
v___y_1476_ = v___x_1494_;
goto v___jp_1475_;
}
}
else
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_unsigned_to_nat(1u);
v___y_1476_ = v___x_1495_;
goto v___jp_1475_;
}
}
else
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
lean_del_object(v___x_1473_);
lean_dec(v_head_1470_);
v___x_1496_ = lean_box_uint32(v_c_x27_1466_);
v___x_1497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
lean_ctor_set(v___x_1497_, 1, v_tail_1471_);
return v___x_1497_;
}
v___jp_1475_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
v___x_1477_ = lean_nat_add(v_x_1468_, v___y_1476_);
v___x_1478_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1466_, v_tail_1471_, v___x_1477_, v_x_1469_);
lean_dec(v___x_1477_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 1, v___x_1478_);
v___x_1480_ = v___x_1473_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_head_1470_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux___boxed(lean_object* v_c_x27_1499_, lean_object* v_x_1500_, lean_object* v_x_1501_, lean_object* v_x_1502_){
_start:
{
uint32_t v_c_x27_boxed_1503_; lean_object* v_res_1504_; 
v_c_x27_boxed_1503_ = lean_unbox_uint32(v_c_x27_1499_);
lean_dec(v_c_x27_1499_);
v_res_1504_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_boxed_1503_, v_x_1500_, v_x_1501_, v_x_1502_);
lean_dec(v_x_1502_);
lean_dec(v_x_1501_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux(uint32_t v_c_x27_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux___boxed(lean_object* v_c_x27_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_){
_start:
{
uint32_t v_c_x27_boxed_1514_; lean_object* v_res_1515_; 
v_c_x27_boxed_1514_ = lean_unbox_uint32(v_c_x27_1510_);
lean_dec(v_c_x27_1510_);
v_res_1515_ = l_String_utf8SetAux(v_c_x27_boxed_1514_, v_a_1511_, v_a_1512_, v_a_1513_);
lean_dec(v_a_1513_);
lean_dec(v_a_1512_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg(lean_object* v_s_1516_, lean_object* v_pos_1517_){
_start:
{
lean_object* v_str_1518_; lean_object* v_startInclusive_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v_str_1518_ = lean_ctor_get(v_s_1516_, 0);
v_startInclusive_1519_ = lean_ctor_get(v_s_1516_, 1);
v___x_1520_ = lean_nat_add(v_startInclusive_1519_, v_pos_1517_);
v___x_1521_ = lean_string_utf8_next_fast(v_str_1518_, v___x_1520_);
lean_dec(v___x_1520_);
v___x_1522_ = lean_nat_sub(v___x_1521_, v_startInclusive_1519_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg___boxed(lean_object* v_s_1523_, lean_object* v_pos_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_String_Slice_Pos_nextFast___redArg(v_s_1523_, v_pos_1524_);
lean_dec(v_pos_1524_);
lean_dec_ref(v_s_1523_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast(lean_object* v_s_1526_, lean_object* v_pos_1527_, lean_object* v_h_1528_){
_start:
{
lean_object* v_str_1529_; lean_object* v_startInclusive_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v_str_1529_ = lean_ctor_get(v_s_1526_, 0);
v_startInclusive_1530_ = lean_ctor_get(v_s_1526_, 1);
v___x_1531_ = lean_nat_add(v_startInclusive_1530_, v_pos_1527_);
v___x_1532_ = lean_string_utf8_next_fast(v_str_1529_, v___x_1531_);
lean_dec(v___x_1531_);
v___x_1533_ = lean_nat_sub(v___x_1532_, v_startInclusive_1530_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___boxed(lean_object* v_s_1534_, lean_object* v_pos_1535_, lean_object* v_h_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_String_Slice_Pos_nextFast(v_s_1534_, v_pos_1535_, v_h_1536_);
lean_dec(v_pos_1535_);
lean_dec_ref(v_s_1534_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_String_sliceTo(lean_object* v_s_1538_, lean_object* v_p_1539_){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = lean_unsigned_to_nat(0u);
v___x_1541_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1541_, 0, v_s_1538_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
lean_ctor_set(v___x_1541_, 2, v_p_1539_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_String_replaceEnd(lean_object* v_s_1542_, lean_object* v_p_1543_){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = lean_unsigned_to_nat(0u);
v___x_1545_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1545_, 0, v_s_1542_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
lean_ctor_set(v___x_1545_, 2, v_p_1543_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_String_sliceFrom(lean_object* v_s_1546_, lean_object* v_p_1547_){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_string_utf8_byte_size(v_s_1546_);
v___x_1549_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1549_, 0, v_s_1546_);
lean_ctor_set(v___x_1549_, 1, v_p_1547_);
lean_ctor_set(v___x_1549_, 2, v___x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStart(lean_object* v_s_1550_, lean_object* v_p_1551_){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = lean_string_utf8_byte_size(v_s_1550_);
v___x_1553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1553_, 0, v_s_1550_);
lean_ctor_set(v___x_1553_, 1, v_p_1551_);
lean_ctor_set(v___x_1553_, 2, v___x_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_String_slice___redArg(lean_object* v_s_1554_, lean_object* v_startInclusive_1555_, lean_object* v_endExclusive_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1557_, 0, v_s_1554_);
lean_ctor_set(v___x_1557_, 1, v_startInclusive_1555_);
lean_ctor_set(v___x_1557_, 2, v_endExclusive_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_String_slice(lean_object* v_s_1558_, lean_object* v_startInclusive_1559_, lean_object* v_endExclusive_1560_, lean_object* v_h_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1562_, 0, v_s_1558_);
lean_ctor_set(v___x_1562_, 1, v_startInclusive_1559_);
lean_ctor_set(v___x_1562_, 2, v_endExclusive_1560_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x3f(lean_object* v_s_1563_, lean_object* v_startInclusive_1564_, lean_object* v_endExclusive_1565_){
_start:
{
uint8_t v___x_1566_; 
v___x_1566_ = lean_nat_dec_le(v_startInclusive_1564_, v_endExclusive_1565_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; 
lean_dec(v_endExclusive_1565_);
lean_dec(v_startInclusive_1564_);
lean_dec_ref(v_s_1563_);
v___x_1567_ = lean_box(0);
return v___x_1567_;
}
else
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1568_, 0, v_s_1563_);
lean_ctor_set(v___x_1568_, 1, v_startInclusive_1564_);
lean_ctor_set(v___x_1568_, 2, v_endExclusive_1565_);
v___x_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
return v___x_1569_;
}
}
}
LEAN_EXPORT lean_object* l_String_slice_x21(lean_object* v_s_1570_, lean_object* v_p_u2081_1571_, lean_object* v_p_u2082_1572_){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1573_ = lean_unsigned_to_nat(0u);
v___x_1574_ = lean_string_utf8_byte_size(v_s_1570_);
v___x_1575_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1575_, 0, v_s_1570_);
lean_ctor_set(v___x_1575_, 1, v___x_1573_);
lean_ctor_set(v___x_1575_, 2, v___x_1574_);
v___x_1576_ = l_String_Slice_slice_x21(v___x_1575_, v_p_u2081_1571_, v_p_u2082_1572_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x21___boxed(lean_object* v_s_1577_, lean_object* v_p_u2081_1578_, lean_object* v_p_u2082_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_String_slice_x21(v_s_1577_, v_p_u2081_1578_, v_p_u2082_1579_);
lean_dec(v_p_u2082_1579_);
lean_dec(v_p_u2081_1578_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21(lean_object* v_s_1581_, lean_object* v_p_u2081_1582_, lean_object* v_p_u2082_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_String_slice_x21(v_s_1581_, v_p_u2081_1582_, v_p_u2082_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21___boxed(lean_object* v_s_1585_, lean_object* v_p_u2081_1586_, lean_object* v_p_u2082_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_String_replaceStartEnd_x21(v_s_1585_, v_p_u2081_1586_, v_p_u2082_1587_);
lean_dec(v_p_u2082_1587_);
lean_dec(v_p_u2081_1586_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg(lean_object* v_p_u2080_1589_, lean_object* v_pos_1590_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = lean_nat_add(v_p_u2080_1589_, v_pos_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg___boxed(lean_object* v_p_u2080_1592_, lean_object* v_pos_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_String_Pos_ofSliceFrom___redArg(v_p_u2080_1592_, v_pos_1593_);
lean_dec(v_pos_1593_);
lean_dec(v_p_u2080_1592_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom(lean_object* v_s_1595_, lean_object* v_p_u2080_1596_, lean_object* v_pos_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_nat_add(v_p_u2080_1596_, v_pos_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___boxed(lean_object* v_s_1599_, lean_object* v_p_u2080_1600_, lean_object* v_pos_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_String_Pos_ofSliceFrom(v_s_1599_, v_p_u2080_1600_, v_pos_1601_);
lean_dec(v_pos_1601_);
lean_dec(v_p_u2080_1600_);
lean_dec_ref(v_s_1599_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg(lean_object* v_p_u2080_1603_, lean_object* v_pos_1604_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = lean_nat_add(v_p_u2080_1603_, v_pos_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg___boxed(lean_object* v_p_u2080_1606_, lean_object* v_pos_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_String_Pos_ofReplaceStart___redArg(v_p_u2080_1606_, v_pos_1607_);
lean_dec(v_pos_1607_);
lean_dec(v_p_u2080_1606_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart(lean_object* v_s_1609_, lean_object* v_p_u2080_1610_, lean_object* v_pos_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_nat_add(v_p_u2080_1610_, v_pos_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___boxed(lean_object* v_s_1613_, lean_object* v_p_u2080_1614_, lean_object* v_pos_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_String_Pos_ofReplaceStart(v_s_1613_, v_p_u2080_1614_, v_pos_1615_);
lean_dec(v_pos_1615_);
lean_dec(v_p_u2080_1614_);
lean_dec_ref(v_s_1613_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg(lean_object* v_p_u2080_1617_, lean_object* v_pos_1618_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_nat_sub(v_pos_1618_, v_p_u2080_1617_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg___boxed(lean_object* v_p_u2080_1620_, lean_object* v_pos_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_String_Pos_sliceFrom___redArg(v_p_u2080_1620_, v_pos_1621_);
lean_dec(v_pos_1621_);
lean_dec(v_p_u2080_1620_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom(lean_object* v_s_1623_, lean_object* v_p_u2080_1624_, lean_object* v_pos_1625_, lean_object* v_h_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = lean_nat_sub(v_pos_1625_, v_p_u2080_1624_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___boxed(lean_object* v_s_1628_, lean_object* v_p_u2080_1629_, lean_object* v_pos_1630_, lean_object* v_h_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_String_Pos_sliceFrom(v_s_1628_, v_p_u2080_1629_, v_pos_1630_, v_h_1631_);
lean_dec(v_pos_1630_);
lean_dec(v_p_u2080_1629_);
lean_dec_ref(v_s_1628_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg(lean_object* v_p_u2080_1633_, lean_object* v_pos_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = lean_nat_sub(v_pos_1634_, v_p_u2080_1633_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg___boxed(lean_object* v_p_u2080_1636_, lean_object* v_pos_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_String_Pos_toReplaceStart___redArg(v_p_u2080_1636_, v_pos_1637_);
lean_dec(v_pos_1637_);
lean_dec(v_p_u2080_1636_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart(lean_object* v_s_1639_, lean_object* v_p_u2080_1640_, lean_object* v_pos_1641_, lean_object* v_h_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = lean_nat_sub(v_pos_1641_, v_p_u2080_1640_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___boxed(lean_object* v_s_1644_, lean_object* v_p_u2080_1645_, lean_object* v_pos_1646_, lean_object* v_h_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_String_Pos_toReplaceStart(v_s_1644_, v_p_u2080_1645_, v_pos_1646_, v_h_1647_);
lean_dec(v_pos_1646_);
lean_dec(v_p_u2080_1645_);
lean_dec_ref(v_s_1644_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg(lean_object* v_pos_1649_){
_start:
{
lean_inc(v_pos_1649_);
return v_pos_1649_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg___boxed(lean_object* v_pos_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_String_Pos_ofSliceTo___redArg(v_pos_1650_);
lean_dec(v_pos_1650_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo(lean_object* v_s_1652_, lean_object* v_p_u2080_1653_, lean_object* v_pos_1654_){
_start:
{
lean_inc(v_pos_1654_);
return v_pos_1654_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___boxed(lean_object* v_s_1655_, lean_object* v_p_u2080_1656_, lean_object* v_pos_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_String_Pos_ofSliceTo(v_s_1655_, v_p_u2080_1656_, v_pos_1657_);
lean_dec(v_pos_1657_);
lean_dec(v_p_u2080_1656_);
lean_dec_ref(v_s_1655_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg(lean_object* v_pos_1659_){
_start:
{
lean_inc(v_pos_1659_);
return v_pos_1659_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg___boxed(lean_object* v_pos_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_String_Pos_ofReplaceEnd___redArg(v_pos_1660_);
lean_dec(v_pos_1660_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd(lean_object* v_s_1662_, lean_object* v_p_u2080_1663_, lean_object* v_pos_1664_){
_start:
{
lean_inc(v_pos_1664_);
return v_pos_1664_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___boxed(lean_object* v_s_1665_, lean_object* v_p_u2080_1666_, lean_object* v_pos_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_String_Pos_ofReplaceEnd(v_s_1665_, v_p_u2080_1666_, v_pos_1667_);
lean_dec(v_pos_1667_);
lean_dec(v_p_u2080_1666_);
lean_dec_ref(v_s_1665_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg(lean_object* v_pos_1669_){
_start:
{
lean_inc(v_pos_1669_);
return v_pos_1669_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg___boxed(lean_object* v_pos_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_String_Pos_sliceTo___redArg(v_pos_1670_);
lean_dec(v_pos_1670_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo(lean_object* v_s_1672_, lean_object* v_p_u2080_1673_, lean_object* v_pos_1674_, lean_object* v_h_1675_){
_start:
{
lean_inc(v_pos_1674_);
return v_pos_1674_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___boxed(lean_object* v_s_1676_, lean_object* v_p_u2080_1677_, lean_object* v_pos_1678_, lean_object* v_h_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_String_Pos_sliceTo(v_s_1676_, v_p_u2080_1677_, v_pos_1678_, v_h_1679_);
lean_dec(v_pos_1678_);
lean_dec(v_p_u2080_1677_);
lean_dec_ref(v_s_1676_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg(lean_object* v_pos_1681_){
_start:
{
lean_inc(v_pos_1681_);
return v_pos_1681_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg___boxed(lean_object* v_pos_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_String_Pos_toReplaceEnd___redArg(v_pos_1682_);
lean_dec(v_pos_1682_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd(lean_object* v_s_1684_, lean_object* v_p_u2080_1685_, lean_object* v_pos_1686_, lean_object* v_h_1687_){
_start:
{
lean_inc(v_pos_1686_);
return v_pos_1686_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___boxed(lean_object* v_s_1688_, lean_object* v_p_u2080_1689_, lean_object* v_pos_1690_, lean_object* v_h_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_String_Pos_toReplaceEnd(v_s_1688_, v_p_u2080_1689_, v_pos_1690_, v_h_1691_);
lean_dec(v_pos_1690_);
lean_dec(v_p_u2080_1689_);
lean_dec_ref(v_s_1688_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg(lean_object* v_p_u2080_1693_, lean_object* v_pos_1694_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_nat_add(v_p_u2080_1693_, v_pos_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1696_, lean_object* v_pos_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_String_Slice_Pos_ofSlice___redArg(v_p_u2080_1696_, v_pos_1697_);
lean_dec(v_pos_1697_);
lean_dec(v_p_u2080_1696_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice(lean_object* v_s_1699_, lean_object* v_p_u2080_1700_, lean_object* v_p_u2081_1701_, lean_object* v_h_1702_, lean_object* v_pos_1703_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_nat_add(v_p_u2080_1700_, v_pos_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___boxed(lean_object* v_s_1705_, lean_object* v_p_u2080_1706_, lean_object* v_p_u2081_1707_, lean_object* v_h_1708_, lean_object* v_pos_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_String_Slice_Pos_ofSlice(v_s_1705_, v_p_u2080_1706_, v_p_u2081_1707_, v_h_1708_, v_pos_1709_);
lean_dec(v_pos_1709_);
lean_dec(v_p_u2081_1707_);
lean_dec(v_p_u2080_1706_);
lean_dec_ref(v_s_1705_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg(lean_object* v_p_u2080_1711_, lean_object* v_pos_1712_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = lean_nat_add(v_p_u2080_1711_, v_pos_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1714_, lean_object* v_pos_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_String_Pos_ofSlice___redArg(v_p_u2080_1714_, v_pos_1715_);
lean_dec(v_pos_1715_);
lean_dec(v_p_u2080_1714_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice(lean_object* v_s_1717_, lean_object* v_p_u2080_1718_, lean_object* v_p_u2081_1719_, lean_object* v_h_1720_, lean_object* v_pos_1721_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = lean_nat_add(v_p_u2080_1718_, v_pos_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___boxed(lean_object* v_s_1723_, lean_object* v_p_u2080_1724_, lean_object* v_p_u2081_1725_, lean_object* v_h_1726_, lean_object* v_pos_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_String_Pos_ofSlice(v_s_1723_, v_p_u2080_1724_, v_p_u2081_1725_, v_h_1726_, v_pos_1727_);
lean_dec(v_pos_1727_);
lean_dec(v_p_u2081_1725_);
lean_dec(v_p_u2080_1724_);
lean_dec_ref(v_s_1723_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg(lean_object* v_pos_1729_, lean_object* v_p_u2080_1730_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_nat_sub(v_pos_1729_, v_p_u2080_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg___boxed(lean_object* v_pos_1732_, lean_object* v_p_u2080_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_String_Slice_Pos_slice___redArg(v_pos_1732_, v_p_u2080_1733_);
lean_dec(v_p_u2080_1733_);
lean_dec(v_pos_1732_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice(lean_object* v_s_1735_, lean_object* v_pos_1736_, lean_object* v_p_u2080_1737_, lean_object* v_p_u2081_1738_, lean_object* v_h_u2081_1739_, lean_object* v_h_u2082_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = lean_nat_sub(v_pos_1736_, v_p_u2080_1737_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___boxed(lean_object* v_s_1742_, lean_object* v_pos_1743_, lean_object* v_p_u2080_1744_, lean_object* v_p_u2081_1745_, lean_object* v_h_u2081_1746_, lean_object* v_h_u2082_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_String_Slice_Pos_slice(v_s_1742_, v_pos_1743_, v_p_u2080_1744_, v_p_u2081_1745_, v_h_u2081_1746_, v_h_u2082_1747_);
lean_dec(v_p_u2081_1745_);
lean_dec(v_p_u2080_1744_);
lean_dec(v_pos_1743_);
lean_dec_ref(v_s_1742_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg(lean_object* v_pos_1749_, lean_object* v_p_u2080_1750_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = lean_nat_sub(v_pos_1749_, v_p_u2080_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg___boxed(lean_object* v_pos_1752_, lean_object* v_p_u2080_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_String_Pos_slice___redArg(v_pos_1752_, v_p_u2080_1753_);
lean_dec(v_p_u2080_1753_);
lean_dec(v_pos_1752_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice(lean_object* v_s_1755_, lean_object* v_pos_1756_, lean_object* v_p_u2080_1757_, lean_object* v_p_u2081_1758_, lean_object* v_h_u2081_1759_, lean_object* v_h_u2082_1760_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = lean_nat_sub(v_pos_1756_, v_p_u2080_1757_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___boxed(lean_object* v_s_1762_, lean_object* v_pos_1763_, lean_object* v_p_u2080_1764_, lean_object* v_p_u2081_1765_, lean_object* v_h_u2081_1766_, lean_object* v_h_u2082_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_String_Pos_slice(v_s_1762_, v_pos_1763_, v_p_u2080_1764_, v_p_u2081_1765_, v_h_u2081_1766_, v_h_u2082_1767_);
lean_dec(v_p_u2081_1765_);
lean_dec(v_p_u2080_1764_);
lean_dec(v_pos_1763_);
lean_dec_ref(v_s_1762_);
return v_res_1768_;
}
}
static lean_object* _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1771_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__1));
v___x_1772_ = lean_unsigned_to_nat(4u);
v___x_1773_ = lean_unsigned_to_nat(2613u);
v___x_1774_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__0));
v___x_1775_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1776_ = l_mkPanicMessageWithDecl(v___x_1775_, v___x_1774_, v___x_1773_, v___x_1772_, v___x_1771_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg(lean_object* v_pos_1777_, lean_object* v_p_u2080_1778_, lean_object* v_p_u2081_1779_){
_start:
{
uint8_t v___x_1784_; 
v___x_1784_ = lean_nat_dec_le(v_p_u2080_1778_, v_pos_1777_);
if (v___x_1784_ == 0)
{
goto v___jp_1780_;
}
else
{
uint8_t v___x_1785_; 
v___x_1785_ = lean_nat_dec_le(v_pos_1777_, v_p_u2081_1779_);
if (v___x_1785_ == 0)
{
goto v___jp_1780_;
}
else
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_nat_sub(v_pos_1777_, v_p_u2080_1778_);
return v___x_1786_;
}
}
v___jp_1780_:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = lean_unsigned_to_nat(0u);
v___x_1782_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1783_ = l_panic___redArg(v___x_1781_, v___x_1782_);
return v___x_1783_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1787_, lean_object* v_p_u2080_1788_, lean_object* v_p_u2081_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_String_Slice_Pos_sliceOrPanic___redArg(v_pos_1787_, v_p_u2080_1788_, v_p_u2081_1789_);
lean_dec(v_p_u2081_1789_);
lean_dec(v_p_u2080_1788_);
lean_dec(v_pos_1787_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic(lean_object* v_s_1791_, lean_object* v_pos_1792_, lean_object* v_p_u2080_1793_, lean_object* v_p_u2081_1794_, lean_object* v_h_1795_){
_start:
{
uint8_t v___x_1800_; 
v___x_1800_ = lean_nat_dec_le(v_p_u2080_1793_, v_pos_1792_);
if (v___x_1800_ == 0)
{
goto v___jp_1796_;
}
else
{
uint8_t v___x_1801_; 
v___x_1801_ = lean_nat_dec_le(v_pos_1792_, v_p_u2081_1794_);
if (v___x_1801_ == 0)
{
goto v___jp_1796_;
}
else
{
lean_object* v___x_1802_; 
v___x_1802_ = lean_nat_sub(v_pos_1792_, v_p_u2080_1793_);
return v___x_1802_;
}
}
v___jp_1796_:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = lean_unsigned_to_nat(0u);
v___x_1798_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1799_ = l_panic___redArg(v___x_1797_, v___x_1798_);
return v___x_1799_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___boxed(lean_object* v_s_1803_, lean_object* v_pos_1804_, lean_object* v_p_u2080_1805_, lean_object* v_p_u2081_1806_, lean_object* v_h_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_String_Slice_Pos_sliceOrPanic(v_s_1803_, v_pos_1804_, v_p_u2080_1805_, v_p_u2081_1806_, v_h_1807_);
lean_dec(v_p_u2081_1806_);
lean_dec(v_p_u2080_1805_);
lean_dec(v_pos_1804_);
lean_dec_ref(v_s_1803_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg(lean_object* v_pos_1809_, lean_object* v_p_u2080_1810_, lean_object* v_p_u2081_1811_){
_start:
{
uint8_t v___x_1816_; 
v___x_1816_ = lean_nat_dec_le(v_p_u2080_1810_, v_pos_1809_);
if (v___x_1816_ == 0)
{
goto v___jp_1812_;
}
else
{
uint8_t v___x_1817_; 
v___x_1817_ = lean_nat_dec_le(v_pos_1809_, v_p_u2081_1811_);
if (v___x_1817_ == 0)
{
goto v___jp_1812_;
}
else
{
lean_object* v___x_1818_; 
v___x_1818_ = lean_nat_sub(v_pos_1809_, v_p_u2080_1810_);
return v___x_1818_;
}
}
v___jp_1812_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1813_ = lean_unsigned_to_nat(0u);
v___x_1814_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1815_ = l_panic___redArg(v___x_1813_, v___x_1814_);
return v___x_1815_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1819_, lean_object* v_p_u2080_1820_, lean_object* v_p_u2081_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_String_Pos_sliceOrPanic___redArg(v_pos_1819_, v_p_u2080_1820_, v_p_u2081_1821_);
lean_dec(v_p_u2081_1821_);
lean_dec(v_p_u2080_1820_);
lean_dec(v_pos_1819_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic(lean_object* v_s_1823_, lean_object* v_pos_1824_, lean_object* v_p_u2080_1825_, lean_object* v_p_u2081_1826_, lean_object* v_h_1827_){
_start:
{
uint8_t v___x_1832_; 
v___x_1832_ = lean_nat_dec_le(v_p_u2080_1825_, v_pos_1824_);
if (v___x_1832_ == 0)
{
goto v___jp_1828_;
}
else
{
uint8_t v___x_1833_; 
v___x_1833_ = lean_nat_dec_le(v_pos_1824_, v_p_u2081_1826_);
if (v___x_1833_ == 0)
{
goto v___jp_1828_;
}
else
{
lean_object* v___x_1834_; 
v___x_1834_ = lean_nat_sub(v_pos_1824_, v_p_u2080_1825_);
return v___x_1834_;
}
}
v___jp_1828_:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1829_ = lean_unsigned_to_nat(0u);
v___x_1830_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1831_ = l_panic___redArg(v___x_1829_, v___x_1830_);
return v___x_1831_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___boxed(lean_object* v_s_1835_, lean_object* v_pos_1836_, lean_object* v_p_u2080_1837_, lean_object* v_p_u2081_1838_, lean_object* v_h_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_String_Pos_sliceOrPanic(v_s_1835_, v_pos_1836_, v_p_u2080_1837_, v_p_u2081_1838_, v_h_1839_);
lean_dec(v_p_u2081_1838_);
lean_dec(v_p_u2080_1837_);
lean_dec(v_pos_1836_);
lean_dec_ref(v_s_1835_);
return v_res_1840_;
}
}
static lean_object* _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1842_ = ((lean_object*)(l_String_Slice_slice_x21___closed__1));
v___x_1843_ = lean_unsigned_to_nat(4u);
v___x_1844_ = lean_unsigned_to_nat(2637u);
v___x_1845_ = ((lean_object*)(l_String_Slice_Pos_ofSlice_x21___redArg___closed__0));
v___x_1846_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1847_ = l_mkPanicMessageWithDecl(v___x_1846_, v___x_1845_, v___x_1844_, v___x_1843_, v___x_1842_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1848_, lean_object* v_p_u2081_1849_, lean_object* v_pos_1850_){
_start:
{
uint8_t v___x_1851_; 
v___x_1851_ = lean_nat_dec_le(v_p_u2080_1848_, v_p_u2081_1849_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = lean_unsigned_to_nat(0u);
v___x_1853_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1854_ = l_panic___redArg(v___x_1852_, v___x_1853_);
return v___x_1854_;
}
else
{
lean_object* v___x_1855_; 
v___x_1855_ = lean_nat_add(v_p_u2080_1848_, v_pos_1850_);
return v___x_1855_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1856_, lean_object* v_p_u2081_1857_, lean_object* v_pos_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_String_Slice_Pos_ofSlice_x21___redArg(v_p_u2080_1856_, v_p_u2081_1857_, v_pos_1858_);
lean_dec(v_pos_1858_);
lean_dec(v_p_u2081_1857_);
lean_dec(v_p_u2080_1856_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21(lean_object* v_s_1860_, lean_object* v_p_u2080_1861_, lean_object* v_p_u2081_1862_, lean_object* v_pos_1863_){
_start:
{
uint8_t v___x_1864_; 
v___x_1864_ = lean_nat_dec_le(v_p_u2080_1861_, v_p_u2081_1862_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1865_ = lean_unsigned_to_nat(0u);
v___x_1866_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1867_ = l_panic___redArg(v___x_1865_, v___x_1866_);
return v___x_1867_;
}
else
{
lean_object* v___x_1868_; 
v___x_1868_ = lean_nat_add(v_p_u2080_1861_, v_pos_1863_);
return v___x_1868_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___boxed(lean_object* v_s_1869_, lean_object* v_p_u2080_1870_, lean_object* v_p_u2081_1871_, lean_object* v_pos_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_String_Slice_Pos_ofSlice_x21(v_s_1869_, v_p_u2080_1870_, v_p_u2081_1871_, v_pos_1872_);
lean_dec(v_pos_1872_);
lean_dec(v_p_u2081_1871_);
lean_dec(v_p_u2080_1870_);
lean_dec_ref(v_s_1869_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1874_, lean_object* v_p_u2081_1875_, lean_object* v_pos_1876_){
_start:
{
uint8_t v___x_1877_; 
v___x_1877_ = lean_nat_dec_le(v_p_u2080_1874_, v_p_u2081_1875_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1878_ = lean_unsigned_to_nat(0u);
v___x_1879_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1880_ = l_panic___redArg(v___x_1878_, v___x_1879_);
return v___x_1880_;
}
else
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_nat_add(v_p_u2080_1874_, v_pos_1876_);
return v___x_1881_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1882_, lean_object* v_p_u2081_1883_, lean_object* v_pos_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_String_Pos_ofSlice_x21___redArg(v_p_u2080_1882_, v_p_u2081_1883_, v_pos_1884_);
lean_dec(v_pos_1884_);
lean_dec(v_p_u2081_1883_);
lean_dec(v_p_u2080_1882_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21(lean_object* v_s_1886_, lean_object* v_p_u2080_1887_, lean_object* v_p_u2081_1888_, lean_object* v_pos_1889_){
_start:
{
uint8_t v___x_1890_; 
v___x_1890_ = lean_nat_dec_le(v_p_u2080_1887_, v_p_u2081_1888_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = lean_unsigned_to_nat(0u);
v___x_1892_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1893_ = l_panic___redArg(v___x_1891_, v___x_1892_);
return v___x_1893_;
}
else
{
lean_object* v___x_1894_; 
v___x_1894_ = lean_nat_add(v_p_u2080_1887_, v_pos_1889_);
return v___x_1894_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___boxed(lean_object* v_s_1895_, lean_object* v_p_u2080_1896_, lean_object* v_p_u2081_1897_, lean_object* v_pos_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_String_Pos_ofSlice_x21(v_s_1895_, v_p_u2080_1896_, v_p_u2081_1897_, v_pos_1898_);
lean_dec(v_pos_1898_);
lean_dec(v_p_u2081_1897_);
lean_dec(v_p_u2080_1896_);
lean_dec_ref(v_s_1895_);
return v_res_1899_;
}
}
static lean_object* _init_l_String_Slice_Pos_slice_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1902_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__1));
v___x_1903_ = lean_unsigned_to_nat(4u);
v___x_1904_ = lean_unsigned_to_nat(2655u);
v___x_1905_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__0));
v___x_1906_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1907_ = l_mkPanicMessageWithDecl(v___x_1906_, v___x_1905_, v___x_1904_, v___x_1903_, v___x_1902_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg(lean_object* v_pos_1908_, lean_object* v_p_u2080_1909_, lean_object* v_p_u2081_1910_){
_start:
{
uint8_t v___x_1915_; 
v___x_1915_ = lean_nat_dec_le(v_p_u2080_1909_, v_pos_1908_);
if (v___x_1915_ == 0)
{
goto v___jp_1911_;
}
else
{
uint8_t v___x_1916_; 
v___x_1916_ = lean_nat_dec_le(v_pos_1908_, v_p_u2081_1910_);
if (v___x_1916_ == 0)
{
goto v___jp_1911_;
}
else
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_nat_sub(v_pos_1908_, v_p_u2080_1909_);
return v___x_1917_;
}
}
v___jp_1911_:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1912_ = lean_unsigned_to_nat(0u);
v___x_1913_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1914_ = l_panic___redArg(v___x_1912_, v___x_1913_);
return v___x_1914_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1918_, lean_object* v_p_u2080_1919_, lean_object* v_p_u2081_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_String_Slice_Pos_slice_x21___redArg(v_pos_1918_, v_p_u2080_1919_, v_p_u2081_1920_);
lean_dec(v_p_u2081_1920_);
lean_dec(v_p_u2080_1919_);
lean_dec(v_pos_1918_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21(lean_object* v_s_1922_, lean_object* v_pos_1923_, lean_object* v_p_u2080_1924_, lean_object* v_p_u2081_1925_){
_start:
{
uint8_t v___x_1930_; 
v___x_1930_ = lean_nat_dec_le(v_p_u2080_1924_, v_pos_1923_);
if (v___x_1930_ == 0)
{
goto v___jp_1926_;
}
else
{
uint8_t v___x_1931_; 
v___x_1931_ = lean_nat_dec_le(v_pos_1923_, v_p_u2081_1925_);
if (v___x_1931_ == 0)
{
goto v___jp_1926_;
}
else
{
lean_object* v___x_1932_; 
v___x_1932_ = lean_nat_sub(v_pos_1923_, v_p_u2080_1924_);
return v___x_1932_;
}
}
v___jp_1926_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1927_ = lean_unsigned_to_nat(0u);
v___x_1928_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1929_ = l_panic___redArg(v___x_1927_, v___x_1928_);
return v___x_1929_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___boxed(lean_object* v_s_1933_, lean_object* v_pos_1934_, lean_object* v_p_u2080_1935_, lean_object* v_p_u2081_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_String_Slice_Pos_slice_x21(v_s_1933_, v_pos_1934_, v_p_u2080_1935_, v_p_u2081_1936_);
lean_dec(v_p_u2081_1936_);
lean_dec(v_p_u2080_1935_);
lean_dec(v_pos_1934_);
lean_dec_ref(v_s_1933_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg(lean_object* v_pos_1938_, lean_object* v_p_u2080_1939_, lean_object* v_p_u2081_1940_){
_start:
{
uint8_t v___x_1945_; 
v___x_1945_ = lean_nat_dec_le(v_p_u2080_1939_, v_pos_1938_);
if (v___x_1945_ == 0)
{
goto v___jp_1941_;
}
else
{
uint8_t v___x_1946_; 
v___x_1946_ = lean_nat_dec_le(v_pos_1938_, v_p_u2081_1940_);
if (v___x_1946_ == 0)
{
goto v___jp_1941_;
}
else
{
lean_object* v___x_1947_; 
v___x_1947_ = lean_nat_sub(v_pos_1938_, v_p_u2080_1939_);
return v___x_1947_;
}
}
v___jp_1941_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1942_ = lean_unsigned_to_nat(0u);
v___x_1943_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1944_ = l_panic___redArg(v___x_1942_, v___x_1943_);
return v___x_1944_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1948_, lean_object* v_p_u2080_1949_, lean_object* v_p_u2081_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_String_Pos_slice_x21___redArg(v_pos_1948_, v_p_u2080_1949_, v_p_u2081_1950_);
lean_dec(v_p_u2081_1950_);
lean_dec(v_p_u2080_1949_);
lean_dec(v_pos_1948_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21(lean_object* v_s_1952_, lean_object* v_pos_1953_, lean_object* v_p_u2080_1954_, lean_object* v_p_u2081_1955_){
_start:
{
uint8_t v___x_1960_; 
v___x_1960_ = lean_nat_dec_le(v_p_u2080_1954_, v_pos_1953_);
if (v___x_1960_ == 0)
{
goto v___jp_1956_;
}
else
{
uint8_t v___x_1961_; 
v___x_1961_ = lean_nat_dec_le(v_pos_1953_, v_p_u2081_1955_);
if (v___x_1961_ == 0)
{
goto v___jp_1956_;
}
else
{
lean_object* v___x_1962_; 
v___x_1962_ = lean_nat_sub(v_pos_1953_, v_p_u2080_1954_);
return v___x_1962_;
}
}
v___jp_1956_:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1957_ = lean_unsigned_to_nat(0u);
v___x_1958_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1959_ = l_panic___redArg(v___x_1957_, v___x_1958_);
return v___x_1959_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___boxed(lean_object* v_s_1963_, lean_object* v_pos_1964_, lean_object* v_p_u2080_1965_, lean_object* v_p_u2081_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_String_Pos_slice_x21(v_s_1963_, v_pos_1964_, v_p_u2080_1965_, v_p_u2081_1966_);
lean_dec(v_p_u2081_1966_);
lean_dec(v_p_u2080_1965_);
lean_dec(v_pos_1964_);
lean_dec_ref(v_s_1963_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract(lean_object* v_s_1968_, lean_object* v_p_u2080_1969_, lean_object* v_p_u2081_1970_){
_start:
{
lean_object* v_str_1971_; lean_object* v_startInclusive_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v_str_1971_ = lean_ctor_get(v_s_1968_, 0);
v_startInclusive_1972_ = lean_ctor_get(v_s_1968_, 1);
v___x_1973_ = lean_nat_add(v_startInclusive_1972_, v_p_u2080_1969_);
v___x_1974_ = lean_nat_add(v_startInclusive_1972_, v_p_u2081_1970_);
v___x_1975_ = lean_string_utf8_extract_fast(v_str_1971_, v___x_1973_, v___x_1974_);
lean_dec(v___x_1974_);
lean_dec(v___x_1973_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract___boxed(lean_object* v_s_1976_, lean_object* v_p_u2080_1977_, lean_object* v_p_u2081_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_String_Slice_extract(v_s_1976_, v_p_u2080_1977_, v_p_u2081_1978_);
lean_dec(v_p_u2081_1978_);
lean_dec(v_p_u2080_1977_);
lean_dec_ref(v_s_1976_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn(lean_object* v_s_1980_, lean_object* v_p_1981_, lean_object* v_n_1982_){
_start:
{
lean_object* v_zero_1983_; uint8_t v_isZero_1984_; 
v_zero_1983_ = lean_unsigned_to_nat(0u);
v_isZero_1984_ = lean_nat_dec_eq(v_n_1982_, v_zero_1983_);
if (v_isZero_1984_ == 1)
{
lean_dec(v_n_1982_);
return v_p_1981_;
}
else
{
lean_object* v_str_1985_; lean_object* v_startInclusive_1986_; lean_object* v_endExclusive_1987_; lean_object* v___x_1988_; uint8_t v_decide_1989_; 
v_str_1985_ = lean_ctor_get(v_s_1980_, 0);
v_startInclusive_1986_ = lean_ctor_get(v_s_1980_, 1);
v_endExclusive_1987_ = lean_ctor_get(v_s_1980_, 2);
v___x_1988_ = lean_nat_sub(v_endExclusive_1987_, v_startInclusive_1986_);
v_decide_1989_ = lean_nat_dec_eq(v_p_1981_, v___x_1988_);
lean_dec(v___x_1988_);
if (v_decide_1989_ == 0)
{
lean_object* v_one_1990_; lean_object* v_n_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v_one_1990_ = lean_unsigned_to_nat(1u);
v_n_1991_ = lean_nat_sub(v_n_1982_, v_one_1990_);
lean_dec(v_n_1982_);
v___x_1992_ = lean_nat_add(v_startInclusive_1986_, v_p_1981_);
lean_dec(v_p_1981_);
v___x_1993_ = lean_string_utf8_next_fast(v_str_1985_, v___x_1992_);
lean_dec(v___x_1992_);
v___x_1994_ = lean_nat_sub(v___x_1993_, v_startInclusive_1986_);
v_p_1981_ = v___x_1994_;
v_n_1982_ = v_n_1991_;
goto _start;
}
else
{
lean_dec(v_n_1982_);
return v_p_1981_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn___boxed(lean_object* v_s_1996_, lean_object* v_p_1997_, lean_object* v_n_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l_String_Slice_Pos_nextn(v_s_1996_, v_p_1997_, v_n_1998_);
lean_dec_ref(v_s_1996_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_nextn(lean_object* v_s_2000_, lean_object* v_p_2001_, lean_object* v_n_2002_){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2003_ = lean_unsigned_to_nat(0u);
v___x_2004_ = lean_string_utf8_byte_size(v_s_2000_);
v___x_2005_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2005_, 0, v_s_2000_);
lean_ctor_set(v___x_2005_, 1, v___x_2003_);
lean_ctor_set(v___x_2005_, 2, v___x_2004_);
v___x_2006_ = l_String_Slice_Pos_nextn(v___x_2005_, v_p_2001_, v_n_2002_);
lean_dec_ref_known(v___x_2005_, 3);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(lean_object* v_n_2007_, lean_object* v_h__1_2008_, lean_object* v_h__2_2009_){
_start:
{
lean_object* v_zero_2010_; uint8_t v_isZero_2011_; 
v_zero_2010_ = lean_unsigned_to_nat(0u);
v_isZero_2011_ = lean_nat_dec_eq(v_n_2007_, v_zero_2010_);
if (v_isZero_2011_ == 1)
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
lean_dec(v_h__2_2009_);
v___x_2012_ = lean_box(0);
v___x_2013_ = lean_apply_1(v_h__1_2008_, v___x_2012_);
return v___x_2013_;
}
else
{
lean_object* v_one_2014_; lean_object* v_n_2015_; lean_object* v___x_2016_; 
lean_dec(v_h__1_2008_);
v_one_2014_ = lean_unsigned_to_nat(1u);
v_n_2015_ = lean_nat_sub(v_n_2007_, v_one_2014_);
v___x_2016_ = lean_apply_1(v_h__2_2009_, v_n_2015_);
return v___x_2016_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg___boxed(lean_object* v_n_2017_, lean_object* v_h__1_2018_, lean_object* v_h__2_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(v_n_2017_, v_h__1_2018_, v_h__2_2019_);
lean_dec(v_n_2017_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(lean_object* v_motive_2021_, lean_object* v_n_2022_, lean_object* v_h__1_2023_, lean_object* v_h__2_2024_){
_start:
{
lean_object* v_zero_2025_; uint8_t v_isZero_2026_; 
v_zero_2025_ = lean_unsigned_to_nat(0u);
v_isZero_2026_ = lean_nat_dec_eq(v_n_2022_, v_zero_2025_);
if (v_isZero_2026_ == 1)
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
lean_dec(v_h__2_2024_);
v___x_2027_ = lean_box(0);
v___x_2028_ = lean_apply_1(v_h__1_2023_, v___x_2027_);
return v___x_2028_;
}
else
{
lean_object* v_one_2029_; lean_object* v_n_2030_; lean_object* v___x_2031_; 
lean_dec(v_h__1_2023_);
v_one_2029_ = lean_unsigned_to_nat(1u);
v_n_2030_ = lean_nat_sub(v_n_2022_, v_one_2029_);
v___x_2031_ = lean_apply_1(v_h__2_2024_, v_n_2030_);
return v___x_2031_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___boxed(lean_object* v_motive_2032_, lean_object* v_n_2033_, lean_object* v_h__1_2034_, lean_object* v_h__2_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(v_motive_2032_, v_n_2033_, v_h__1_2034_, v_h__2_2035_);
lean_dec(v_n_2033_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next___boxed(lean_object* v_s_2039_, lean_object* v_p_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = lean_string_utf8_next(v_s_2039_, v_p_2040_);
lean_dec(v_p_2040_);
lean_dec_ref(v_s_2039_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_String_next___boxed(lean_object* v_s_2044_, lean_object* v_p_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = lean_string_utf8_next(v_s_2044_, v_p_2045_);
lean_dec(v_p_2045_);
lean_dec_ref(v_s_2044_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux(lean_object* v_x_2047_, lean_object* v_x_2048_, lean_object* v_x_2049_){
_start:
{
if (lean_obj_tag(v_x_2047_) == 0)
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
lean_dec(v_x_2048_);
v___x_2050_ = lean_unsigned_to_nat(1u);
v___x_2051_ = lean_nat_sub(v_x_2049_, v___x_2050_);
return v___x_2051_;
}
else
{
lean_object* v_head_2052_; lean_object* v_tail_2053_; lean_object* v___y_2055_; uint32_t v___x_2059_; uint32_t v___x_2060_; uint8_t v___x_2061_; 
v_head_2052_ = lean_ctor_get(v_x_2047_, 0);
v_tail_2053_ = lean_ctor_get(v_x_2047_, 1);
v___x_2059_ = 127;
v___x_2060_ = lean_unbox_uint32(v_head_2052_);
v___x_2061_ = lean_uint32_dec_le(v___x_2060_, v___x_2059_);
if (v___x_2061_ == 0)
{
uint32_t v___x_2062_; uint32_t v___x_2063_; uint8_t v___x_2064_; 
v___x_2062_ = 2047;
v___x_2063_ = lean_unbox_uint32(v_head_2052_);
v___x_2064_ = lean_uint32_dec_le(v___x_2063_, v___x_2062_);
if (v___x_2064_ == 0)
{
uint32_t v___x_2065_; uint32_t v___x_2066_; uint8_t v___x_2067_; 
v___x_2065_ = 65535;
v___x_2066_ = lean_unbox_uint32(v_head_2052_);
v___x_2067_ = lean_uint32_dec_le(v___x_2066_, v___x_2065_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2068_; 
v___x_2068_ = lean_unsigned_to_nat(4u);
v___y_2055_ = v___x_2068_;
goto v___jp_2054_;
}
else
{
lean_object* v___x_2069_; 
v___x_2069_ = lean_unsigned_to_nat(3u);
v___y_2055_ = v___x_2069_;
goto v___jp_2054_;
}
}
else
{
lean_object* v___x_2070_; 
v___x_2070_ = lean_unsigned_to_nat(2u);
v___y_2055_ = v___x_2070_;
goto v___jp_2054_;
}
}
else
{
lean_object* v___x_2071_; 
v___x_2071_ = lean_unsigned_to_nat(1u);
v___y_2055_ = v___x_2071_;
goto v___jp_2054_;
}
v___jp_2054_:
{
lean_object* v___x_2056_; uint8_t v___x_2057_; 
v___x_2056_ = lean_nat_add(v_x_2048_, v___y_2055_);
v___x_2057_ = lean_nat_dec_le(v_x_2049_, v___x_2056_);
if (v___x_2057_ == 0)
{
lean_dec(v_x_2048_);
v_x_2047_ = v_tail_2053_;
v_x_2048_ = v___x_2056_;
goto _start;
}
else
{
lean_dec(v___x_2056_);
return v_x_2048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux___boxed(lean_object* v_x_2072_, lean_object* v_x_2073_, lean_object* v_x_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_String_Pos_Raw_utf8PrevAux(v_x_2072_, v_x_2073_, v_x_2074_);
lean_dec(v_x_2074_);
lean_dec(v_x_2072_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux(lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_){
_start:
{
lean_object* v___x_2079_; 
v___x_2079_ = l_String_Pos_Raw_utf8PrevAux(v_a_2076_, v_a_2077_, v_a_2078_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux___boxed(lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_String_utf8PrevAux(v_a_2080_, v_a_2081_, v_a_2082_);
lean_dec(v_a_2082_);
lean_dec(v_a_2080_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_prev___boxed(lean_object* v_a_00___x40___internal___hyg_2086_, lean_object* v_a_00___x40___internal___hyg_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_2086_, v_a_00___x40___internal___hyg_2087_);
lean_dec(v_a_00___x40___internal___hyg_2087_);
lean_dec_ref(v_a_00___x40___internal___hyg_2086_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_String_prev___boxed(lean_object* v_a_00___x40___internal___hyg_2091_, lean_object* v_a_00___x40___internal___hyg_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_2091_, v_a_00___x40___internal___hyg_2092_);
lean_dec(v_a_00___x40___internal___hyg_2092_);
lean_dec_ref(v_a_00___x40___internal___hyg_2091_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_2096_, lean_object* v_a_00___x40___internal___hyg_2097_){
_start:
{
uint8_t v_res_2098_; lean_object* v_r_2099_; 
v_res_2098_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_2096_, v_a_00___x40___internal___hyg_2097_);
lean_dec(v_a_00___x40___internal___hyg_2097_);
lean_dec_ref(v_a_00___x40___internal___hyg_2096_);
v_r_2099_ = lean_box(v_res_2098_);
return v_r_2099_;
}
}
LEAN_EXPORT lean_object* l_String_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_2102_, lean_object* v_a_00___x40___internal___hyg_2103_){
_start:
{
uint8_t v_res_2104_; lean_object* v_r_2105_; 
v_res_2104_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_2102_, v_a_00___x40___internal___hyg_2103_);
lean_dec(v_a_00___x40___internal___hyg_2103_);
lean_dec_ref(v_a_00___x40___internal___hyg_2102_);
v_r_2105_ = lean_box(v_res_2104_);
return v_r_2105_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x27___boxed(lean_object* v_s_2109_, lean_object* v_p_2110_, lean_object* v_h_2111_){
_start:
{
uint32_t v_res_2112_; lean_object* v_r_2113_; 
v_res_2112_ = lean_string_utf8_get_fast(v_s_2109_, v_p_2110_);
lean_dec(v_p_2110_);
lean_dec_ref(v_s_2109_);
v_r_2113_ = lean_box_uint32(v_res_2112_);
return v_r_2113_;
}
}
LEAN_EXPORT lean_object* l_String_get_x27___boxed(lean_object* v_s_2117_, lean_object* v_p_2118_, lean_object* v_h_2119_){
_start:
{
uint32_t v_res_2120_; lean_object* v_r_2121_; 
v_res_2120_ = lean_string_utf8_get_fast(v_s_2117_, v_p_2118_);
lean_dec(v_p_2118_);
lean_dec_ref(v_s_2117_);
v_r_2121_ = lean_box_uint32(v_res_2120_);
return v_r_2121_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next_x27___boxed(lean_object* v_s_2125_, lean_object* v_p_2126_, lean_object* v_h_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = lean_string_utf8_next_fast(v_s_2125_, v_p_2126_);
lean_dec(v_p_2126_);
lean_dec_ref(v_s_2125_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_String_next_x27___boxed(lean_object* v_s_2132_, lean_object* v_p_2133_, lean_object* v_h_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = lean_string_utf8_next_fast(v_s_2132_, v_p_2133_);
lean_dec(v_p_2133_);
lean_dec_ref(v_s_2132_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop(lean_object* v_a_2136_, lean_object* v_b_2137_, lean_object* v_stopPos_2138_, lean_object* v_i_2139_){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2140_ = lean_unsigned_to_nat(1u);
v___x_2141_ = lean_nat_add(v_i_2139_, v___x_2140_);
v___x_2142_ = lean_nat_dec_le(v___x_2141_, v_stopPos_2138_);
lean_dec(v___x_2141_);
if (v___x_2142_ == 0)
{
return v_i_2139_;
}
else
{
uint32_t v___x_2143_; uint32_t v___x_2144_; uint8_t v___x_2145_; 
v___x_2143_ = lean_string_utf8_get(v_a_2136_, v_i_2139_);
v___x_2144_ = lean_string_utf8_get(v_b_2137_, v_i_2139_);
v___x_2145_ = lean_uint32_dec_eq(v___x_2143_, v___x_2144_);
if (v___x_2145_ == 0)
{
return v_i_2139_;
}
else
{
lean_object* v___x_2146_; 
v___x_2146_ = lean_string_utf8_next(v_a_2136_, v_i_2139_);
lean_dec(v_i_2139_);
v_i_2139_ = v___x_2146_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop___boxed(lean_object* v_a_2148_, lean_object* v_b_2149_, lean_object* v_stopPos_2150_, lean_object* v_i_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_String_firstDiffPos_loop(v_a_2148_, v_b_2149_, v_stopPos_2150_, v_i_2151_);
lean_dec(v_stopPos_2150_);
lean_dec_ref(v_b_2149_);
lean_dec_ref(v_a_2148_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos(lean_object* v_a_2153_, lean_object* v_b_2154_){
_start:
{
lean_object* v___y_2156_; lean_object* v___x_2159_; lean_object* v___x_2160_; uint8_t v___x_2161_; 
v___x_2159_ = lean_string_utf8_byte_size(v_a_2153_);
v___x_2160_ = lean_string_utf8_byte_size(v_b_2154_);
v___x_2161_ = lean_nat_dec_le(v___x_2159_, v___x_2160_);
if (v___x_2161_ == 0)
{
v___y_2156_ = v___x_2160_;
goto v___jp_2155_;
}
else
{
v___y_2156_ = v___x_2159_;
goto v___jp_2155_;
}
v___jp_2155_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = lean_unsigned_to_nat(0u);
v___x_2158_ = l_String_firstDiffPos_loop(v_a_2153_, v_b_2154_, v___y_2156_, v___x_2157_);
lean_dec(v___y_2156_);
return v___x_2158_;
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos___boxed(lean_object* v_a_2162_, lean_object* v_b_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_String_firstDiffPos(v_a_2162_, v_b_2163_);
lean_dec_ref(v_b_2163_);
lean_dec_ref(v_a_2162_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082(lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_){
_start:
{
if (lean_obj_tag(v_a_2165_) == 0)
{
return v_a_2165_;
}
else
{
lean_object* v_head_2168_; lean_object* v_tail_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2195_; 
v_head_2168_ = lean_ctor_get(v_a_2165_, 0);
v_tail_2169_ = lean_ctor_get(v_a_2165_, 1);
v_isSharedCheck_2195_ = !lean_is_exclusive(v_a_2165_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2171_ = v_a_2165_;
v_isShared_2172_ = v_isSharedCheck_2195_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_tail_2169_);
lean_inc(v_head_2168_);
lean_dec(v_a_2165_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2195_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___y_2174_; uint8_t v_decide_2180_; 
v_decide_2180_ = lean_nat_dec_eq(v_a_2166_, v_a_2167_);
if (v_decide_2180_ == 0)
{
uint32_t v___x_2181_; uint32_t v___x_2182_; uint8_t v___x_2183_; 
v___x_2181_ = 127;
v___x_2182_ = lean_unbox_uint32(v_head_2168_);
v___x_2183_ = lean_uint32_dec_le(v___x_2182_, v___x_2181_);
if (v___x_2183_ == 0)
{
uint32_t v___x_2184_; uint32_t v___x_2185_; uint8_t v___x_2186_; 
v___x_2184_ = 2047;
v___x_2185_ = lean_unbox_uint32(v_head_2168_);
v___x_2186_ = lean_uint32_dec_le(v___x_2185_, v___x_2184_);
if (v___x_2186_ == 0)
{
uint32_t v___x_2187_; uint32_t v___x_2188_; uint8_t v___x_2189_; 
v___x_2187_ = 65535;
v___x_2188_ = lean_unbox_uint32(v_head_2168_);
v___x_2189_ = lean_uint32_dec_le(v___x_2188_, v___x_2187_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; 
v___x_2190_ = lean_unsigned_to_nat(4u);
v___y_2174_ = v___x_2190_;
goto v___jp_2173_;
}
else
{
lean_object* v___x_2191_; 
v___x_2191_ = lean_unsigned_to_nat(3u);
v___y_2174_ = v___x_2191_;
goto v___jp_2173_;
}
}
else
{
lean_object* v___x_2192_; 
v___x_2192_ = lean_unsigned_to_nat(2u);
v___y_2174_ = v___x_2192_;
goto v___jp_2173_;
}
}
else
{
lean_object* v___x_2193_; 
v___x_2193_ = lean_unsigned_to_nat(1u);
v___y_2174_ = v___x_2193_;
goto v___jp_2173_;
}
}
else
{
lean_object* v___x_2194_; 
lean_del_object(v___x_2171_);
lean_dec(v_tail_2169_);
lean_dec(v_head_2168_);
v___x_2194_ = lean_box(0);
return v___x_2194_;
}
v___jp_2173_:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2178_; 
v___x_2175_ = lean_nat_add(v_a_2166_, v___y_2174_);
v___x_2176_ = l_String_Pos_Raw_extract_go_u2082(v_tail_2169_, v___x_2175_, v_a_2167_);
lean_dec(v___x_2175_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 1, v___x_2176_);
v___x_2178_ = v___x_2171_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_head_2168_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v___x_2176_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082___boxed(lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_String_Pos_Raw_extract_go_u2082(v_a_2196_, v_a_2197_, v_a_2198_);
lean_dec(v_a_2198_);
lean_dec(v_a_2197_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081(lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_){
_start:
{
if (lean_obj_tag(v_a_2200_) == 0)
{
lean_dec(v_a_2201_);
return v_a_2200_;
}
else
{
lean_object* v_head_2204_; lean_object* v_tail_2205_; lean_object* v___y_2207_; uint8_t v_decide_2210_; 
v_head_2204_ = lean_ctor_get(v_a_2200_, 0);
v_tail_2205_ = lean_ctor_get(v_a_2200_, 1);
v_decide_2210_ = lean_nat_dec_eq(v_a_2201_, v_a_2202_);
if (v_decide_2210_ == 0)
{
uint32_t v___x_2211_; uint32_t v___x_2212_; uint8_t v___x_2213_; 
lean_inc(v_tail_2205_);
lean_inc(v_head_2204_);
lean_dec_ref_known(v_a_2200_, 2);
v___x_2211_ = 127;
v___x_2212_ = lean_unbox_uint32(v_head_2204_);
v___x_2213_ = lean_uint32_dec_le(v___x_2212_, v___x_2211_);
if (v___x_2213_ == 0)
{
uint32_t v___x_2214_; uint32_t v___x_2215_; uint8_t v___x_2216_; 
v___x_2214_ = 2047;
v___x_2215_ = lean_unbox_uint32(v_head_2204_);
v___x_2216_ = lean_uint32_dec_le(v___x_2215_, v___x_2214_);
if (v___x_2216_ == 0)
{
uint32_t v___x_2217_; uint32_t v___x_2218_; uint8_t v___x_2219_; 
v___x_2217_ = 65535;
v___x_2218_ = lean_unbox_uint32(v_head_2204_);
lean_dec(v_head_2204_);
v___x_2219_ = lean_uint32_dec_le(v___x_2218_, v___x_2217_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2220_; 
v___x_2220_ = lean_unsigned_to_nat(4u);
v___y_2207_ = v___x_2220_;
goto v___jp_2206_;
}
else
{
lean_object* v___x_2221_; 
v___x_2221_ = lean_unsigned_to_nat(3u);
v___y_2207_ = v___x_2221_;
goto v___jp_2206_;
}
}
else
{
lean_object* v___x_2222_; 
lean_dec(v_head_2204_);
v___x_2222_ = lean_unsigned_to_nat(2u);
v___y_2207_ = v___x_2222_;
goto v___jp_2206_;
}
}
else
{
lean_object* v___x_2223_; 
lean_dec(v_head_2204_);
v___x_2223_ = lean_unsigned_to_nat(1u);
v___y_2207_ = v___x_2223_;
goto v___jp_2206_;
}
}
else
{
lean_object* v___x_2224_; 
v___x_2224_ = l_String_Pos_Raw_extract_go_u2082(v_a_2200_, v_a_2201_, v_a_2203_);
lean_dec(v_a_2201_);
return v___x_2224_;
}
v___jp_2206_:
{
lean_object* v___x_2208_; 
v___x_2208_ = lean_nat_add(v_a_2201_, v___y_2207_);
lean_dec(v_a_2201_);
v_a_2200_ = v_tail_2205_;
v_a_2201_ = v___x_2208_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081___boxed(lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_String_Pos_Raw_extract_go_u2081(v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
lean_dec(v_a_2228_);
lean_dec(v_a_2227_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract___boxed(lean_object* v_a_00___x40___internal___hyg_2233_, lean_object* v_a_00___x40___internal___hyg_2234_, lean_object* v_a_00___x40___internal___hyg_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = lean_string_utf8_extract(v_a_00___x40___internal___hyg_2233_, v_a_00___x40___internal___hyg_2234_, v_a_00___x40___internal___hyg_2235_);
lean_dec(v_a_00___x40___internal___hyg_2235_);
lean_dec(v_a_00___x40___internal___hyg_2234_);
lean_dec_ref(v_a_00___x40___internal___hyg_2233_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux(lean_object* v_s_2237_, lean_object* v_pos_2238_, lean_object* v_i_2239_, lean_object* v_offset_2240_){
_start:
{
uint8_t v___x_2241_; 
v___x_2241_ = lean_nat_dec_le(v_pos_2238_, v_i_2239_);
if (v___x_2241_ == 0)
{
uint8_t v___x_2242_; 
v___x_2242_ = lean_string_utf8_at_end(v_s_2237_, v_i_2239_);
if (v___x_2242_ == 0)
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2243_ = lean_string_utf8_next(v_s_2237_, v_i_2239_);
lean_dec(v_i_2239_);
v___x_2244_ = lean_unsigned_to_nat(1u);
v___x_2245_ = lean_nat_add(v_offset_2240_, v___x_2244_);
lean_dec(v_offset_2240_);
v_i_2239_ = v___x_2243_;
v_offset_2240_ = v___x_2245_;
goto _start;
}
else
{
lean_dec(v_i_2239_);
return v_offset_2240_;
}
}
else
{
lean_dec(v_i_2239_);
return v_offset_2240_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux___boxed(lean_object* v_s_2247_, lean_object* v_pos_2248_, lean_object* v_i_2249_, lean_object* v_offset_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2247_, v_pos_2248_, v_i_2249_, v_offset_2250_);
lean_dec(v_pos_2248_);
lean_dec_ref(v_s_2247_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos(lean_object* v_s_2252_, lean_object* v_pos_2253_){
_start:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = lean_unsigned_to_nat(0u);
v___x_2255_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2252_, v_pos_2253_, v___x_2254_, v___x_2254_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos___boxed(lean_object* v_s_2256_, lean_object* v_pos_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_String_Pos_Raw_offsetOfPos(v_s_2256_, v_pos_2257_);
lean_dec(v_pos_2257_);
lean_dec_ref(v_s_2256_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos(lean_object* v_s_2259_, lean_object* v_pos_2260_){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = lean_unsigned_to_nat(0u);
v___x_2262_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2259_, v_pos_2260_, v___x_2261_, v___x_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos___boxed(lean_object* v_s_2263_, lean_object* v_pos_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l_String_offsetOfPos(v_s_2263_, v_pos_2264_);
lean_dec(v_pos_2264_);
lean_dec_ref(v_s_2263_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* lean_string_offsetofpos(lean_object* v_s_2266_, lean_object* v_pos_2267_){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = lean_unsigned_to_nat(0u);
v___x_2269_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2266_, v_pos_2267_, v___x_2268_, v___x_2268_);
lean_dec(v_pos_2267_);
lean_dec_ref(v_s_2266_);
return v___x_2269_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(lean_object* v_s1_2270_, lean_object* v_s2_2271_, lean_object* v_off1_2272_, lean_object* v_off2_2273_, lean_object* v_stop1_2274_){
_start:
{
lean_object* v___y_2276_; lean_object* v___y_2277_; uint8_t v___x_2280_; 
v___x_2280_ = lean_nat_dec_lt(v_off1_2272_, v_stop1_2274_);
if (v___x_2280_ == 0)
{
uint8_t v___x_2281_; 
lean_dec(v_off2_2273_);
lean_dec(v_off1_2272_);
v___x_2281_ = 1;
return v___x_2281_;
}
else
{
uint32_t v_c_u2081_2282_; uint32_t v_c_u2082_2283_; lean_object* v___y_2285_; uint8_t v___x_2297_; 
v_c_u2081_2282_ = lean_string_utf8_get(v_s1_2270_, v_off1_2272_);
v_c_u2082_2283_ = lean_string_utf8_get(v_s2_2271_, v_off2_2273_);
v___x_2297_ = lean_uint32_dec_eq(v_c_u2081_2282_, v_c_u2082_2283_);
if (v___x_2297_ == 0)
{
lean_dec(v_off2_2273_);
lean_dec(v_off1_2272_);
return v___x_2297_;
}
else
{
uint32_t v___x_2298_; uint8_t v___x_2299_; 
v___x_2298_ = 127;
v___x_2299_ = lean_uint32_dec_le(v_c_u2081_2282_, v___x_2298_);
if (v___x_2299_ == 0)
{
uint32_t v___x_2300_; uint8_t v___x_2301_; 
v___x_2300_ = 2047;
v___x_2301_ = lean_uint32_dec_le(v_c_u2081_2282_, v___x_2300_);
if (v___x_2301_ == 0)
{
uint32_t v___x_2302_; uint8_t v___x_2303_; 
v___x_2302_ = 65535;
v___x_2303_ = lean_uint32_dec_le(v_c_u2081_2282_, v___x_2302_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; 
v___x_2304_ = lean_unsigned_to_nat(4u);
v___y_2285_ = v___x_2304_;
goto v___jp_2284_;
}
else
{
lean_object* v___x_2305_; 
v___x_2305_ = lean_unsigned_to_nat(3u);
v___y_2285_ = v___x_2305_;
goto v___jp_2284_;
}
}
else
{
lean_object* v___x_2306_; 
v___x_2306_ = lean_unsigned_to_nat(2u);
v___y_2285_ = v___x_2306_;
goto v___jp_2284_;
}
}
else
{
lean_object* v___x_2307_; 
v___x_2307_ = lean_unsigned_to_nat(1u);
v___y_2285_ = v___x_2307_;
goto v___jp_2284_;
}
}
v___jp_2284_:
{
lean_object* v___x_2286_; uint32_t v___x_2287_; uint8_t v___x_2288_; 
v___x_2286_ = lean_nat_add(v_off1_2272_, v___y_2285_);
lean_dec(v_off1_2272_);
v___x_2287_ = 127;
v___x_2288_ = lean_uint32_dec_le(v_c_u2082_2283_, v___x_2287_);
if (v___x_2288_ == 0)
{
uint32_t v___x_2289_; uint8_t v___x_2290_; 
v___x_2289_ = 2047;
v___x_2290_ = lean_uint32_dec_le(v_c_u2082_2283_, v___x_2289_);
if (v___x_2290_ == 0)
{
uint32_t v___x_2291_; uint8_t v___x_2292_; 
v___x_2291_ = 65535;
v___x_2292_ = lean_uint32_dec_le(v_c_u2082_2283_, v___x_2291_);
if (v___x_2292_ == 0)
{
lean_object* v___x_2293_; 
v___x_2293_ = lean_unsigned_to_nat(4u);
v___y_2276_ = v___x_2286_;
v___y_2277_ = v___x_2293_;
goto v___jp_2275_;
}
else
{
lean_object* v___x_2294_; 
v___x_2294_ = lean_unsigned_to_nat(3u);
v___y_2276_ = v___x_2286_;
v___y_2277_ = v___x_2294_;
goto v___jp_2275_;
}
}
else
{
lean_object* v___x_2295_; 
v___x_2295_ = lean_unsigned_to_nat(2u);
v___y_2276_ = v___x_2286_;
v___y_2277_ = v___x_2295_;
goto v___jp_2275_;
}
}
else
{
lean_object* v___x_2296_; 
v___x_2296_ = lean_unsigned_to_nat(1u);
v___y_2276_ = v___x_2286_;
v___y_2277_ = v___x_2296_;
goto v___jp_2275_;
}
}
}
v___jp_2275_:
{
lean_object* v___x_2278_; 
v___x_2278_ = lean_nat_add(v_off2_2273_, v___y_2277_);
lean_dec(v_off2_2273_);
v_off1_2272_ = v___y_2276_;
v_off2_2273_ = v___x_2278_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop___boxed(lean_object* v_s1_2308_, lean_object* v_s2_2309_, lean_object* v_off1_2310_, lean_object* v_off2_2311_, lean_object* v_stop1_2312_){
_start:
{
uint8_t v_res_2313_; lean_object* v_r_2314_; 
v_res_2313_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2308_, v_s2_2309_, v_off1_2310_, v_off2_2311_, v_stop1_2312_);
lean_dec(v_stop1_2312_);
lean_dec_ref(v_s2_2309_);
lean_dec_ref(v_s1_2308_);
v_r_2314_ = lean_box(v_res_2313_);
return v_r_2314_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_substrEq(lean_object* v_s1_2315_, lean_object* v_pos1_2316_, lean_object* v_s2_2317_, lean_object* v_pos2_2318_, lean_object* v_sz_2319_){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; uint8_t v___x_2322_; 
v___x_2320_ = lean_nat_add(v_pos1_2316_, v_sz_2319_);
v___x_2321_ = lean_string_utf8_byte_size(v_s1_2315_);
v___x_2322_ = lean_nat_dec_le(v___x_2320_, v___x_2321_);
if (v___x_2322_ == 0)
{
lean_dec(v___x_2320_);
lean_dec(v_pos2_2318_);
lean_dec(v_pos1_2316_);
return v___x_2322_;
}
else
{
lean_object* v___x_2323_; lean_object* v___x_2324_; uint8_t v___x_2325_; 
v___x_2323_ = lean_nat_add(v_pos2_2318_, v_sz_2319_);
v___x_2324_ = lean_string_utf8_byte_size(v_s2_2317_);
v___x_2325_ = lean_nat_dec_le(v___x_2323_, v___x_2324_);
lean_dec(v___x_2323_);
if (v___x_2325_ == 0)
{
lean_dec(v___x_2320_);
lean_dec(v_pos2_2318_);
lean_dec(v_pos1_2316_);
return v___x_2325_;
}
else
{
uint8_t v___x_2326_; 
v___x_2326_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2315_, v_s2_2317_, v_pos1_2316_, v_pos2_2318_, v___x_2320_);
lean_dec(v___x_2320_);
return v___x_2326_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_substrEq___boxed(lean_object* v_s1_2327_, lean_object* v_pos1_2328_, lean_object* v_s2_2329_, lean_object* v_pos2_2330_, lean_object* v_sz_2331_){
_start:
{
uint8_t v_res_2332_; lean_object* v_r_2333_; 
v_res_2332_ = l_String_Pos_Raw_substrEq(v_s1_2327_, v_pos1_2328_, v_s2_2329_, v_pos2_2330_, v_sz_2331_);
lean_dec(v_sz_2331_);
lean_dec_ref(v_s2_2329_);
lean_dec_ref(v_s1_2327_);
v_r_2333_ = lean_box(v_res_2332_);
return v_r_2333_;
}
}
LEAN_EXPORT uint8_t l_String_substrEq(lean_object* v_s1_2334_, lean_object* v_pos1_2335_, lean_object* v_s2_2336_, lean_object* v_pos2_2337_, lean_object* v_sz_2338_){
_start:
{
uint8_t v___x_2339_; 
v___x_2339_ = l_String_Pos_Raw_substrEq(v_s1_2334_, v_pos1_2335_, v_s2_2336_, v_pos2_2337_, v_sz_2338_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_String_substrEq___boxed(lean_object* v_s1_2340_, lean_object* v_pos1_2341_, lean_object* v_s2_2342_, lean_object* v_pos2_2343_, lean_object* v_sz_2344_){
_start:
{
uint8_t v_res_2345_; lean_object* v_r_2346_; 
v_res_2345_ = l_String_substrEq(v_s1_2340_, v_pos1_2341_, v_s2_2342_, v_pos2_2343_, v_sz_2344_);
lean_dec(v_sz_2344_);
lean_dec_ref(v_s2_2342_);
lean_dec_ref(v_s1_2340_);
v_r_2346_ = lean_box(v_res_2345_);
return v_r_2346_;
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
