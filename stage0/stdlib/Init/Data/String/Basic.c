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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__10_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__10_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__6_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__6_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__8_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__8_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__10_splitter___redArg(lean_object* v_x_380_, lean_object* v_h__1_381_, lean_object* v_h__2_382_){
_start:
{
if (lean_obj_tag(v_x_380_) == 0)
{
lean_object* v___x_383_; lean_object* v___x_384_; 
lean_dec(v_h__2_382_);
v___x_383_ = lean_box(0);
v___x_384_ = lean_apply_1(v_h__1_381_, v___x_383_);
return v___x_384_;
}
else
{
lean_object* v_head_385_; lean_object* v_tail_386_; lean_object* v___x_387_; 
lean_dec(v_h__1_381_);
v_head_385_ = lean_ctor_get(v_x_380_, 0);
lean_inc(v_head_385_);
v_tail_386_ = lean_ctor_get(v_x_380_, 1);
lean_inc(v_tail_386_);
lean_dec_ref_known(v_x_380_, 2);
v___x_387_ = lean_apply_2(v_h__2_382_, v_head_385_, v_tail_386_);
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__10_splitter(lean_object* v_motive_388_, lean_object* v_x_389_, lean_object* v_h__1_390_, lean_object* v_h__2_391_){
_start:
{
if (lean_obj_tag(v_x_389_) == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; 
lean_dec(v_h__2_391_);
v___x_392_ = lean_box(0);
v___x_393_ = lean_apply_1(v_h__1_390_, v___x_392_);
return v___x_393_;
}
else
{
lean_object* v_head_394_; lean_object* v_tail_395_; lean_object* v___x_396_; 
lean_dec(v_h__1_390_);
v_head_394_ = lean_ctor_get(v_x_389_, 0);
lean_inc(v_head_394_);
v_tail_395_ = lean_ctor_get(v_x_389_, 1);
lean_inc(v_tail_395_);
lean_dec_ref_known(v_x_389_, 2);
v___x_396_ = lean_apply_2(v_h__2_391_, v_head_394_, v_tail_395_);
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__3_splitter___redArg(lean_object* v_ws_397_, lean_object* v_h__1_398_, lean_object* v_h__2_399_){
_start:
{
if (lean_obj_tag(v_ws_397_) == 1)
{
lean_object* v_head_400_; lean_object* v_tail_401_; lean_object* v___x_402_; 
lean_dec(v_h__2_399_);
v_head_400_ = lean_ctor_get(v_ws_397_, 0);
lean_inc(v_head_400_);
v_tail_401_ = lean_ctor_get(v_ws_397_, 1);
lean_inc(v_tail_401_);
lean_dec_ref_known(v_ws_397_, 2);
v___x_402_ = lean_apply_2(v_h__1_398_, v_head_400_, v_tail_401_);
return v___x_402_;
}
else
{
lean_object* v___x_403_; 
lean_dec(v_h__1_398_);
v___x_403_ = lean_apply_2(v_h__2_399_, v_ws_397_, lean_box(0));
return v___x_403_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__3_splitter(lean_object* v_motive_404_, lean_object* v_ws_405_, lean_object* v_h__1_406_, lean_object* v_h__2_407_){
_start:
{
if (lean_obj_tag(v_ws_405_) == 1)
{
lean_object* v_head_408_; lean_object* v_tail_409_; lean_object* v___x_410_; 
lean_dec(v_h__2_407_);
v_head_408_ = lean_ctor_get(v_ws_405_, 0);
lean_inc(v_head_408_);
v_tail_409_ = lean_ctor_get(v_ws_405_, 1);
lean_inc(v_tail_409_);
lean_dec_ref_known(v_ws_405_, 2);
v___x_410_ = lean_apply_2(v_h__1_406_, v_head_408_, v_tail_409_);
return v___x_410_;
}
else
{
lean_object* v___x_411_; 
lean_dec(v_h__1_406_);
v___x_411_ = lean_apply_2(v_h__2_407_, v_ws_405_, lean_box(0));
return v___x_411_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__6_splitter___redArg(lean_object* v_ws_412_, lean_object* v_h__1_413_, lean_object* v_h__2_414_){
_start:
{
if (lean_obj_tag(v_ws_412_) == 1)
{
lean_object* v_tail_415_; 
v_tail_415_ = lean_ctor_get(v_ws_412_, 1);
if (lean_obj_tag(v_tail_415_) == 1)
{
lean_object* v_head_416_; lean_object* v_head_417_; lean_object* v_tail_418_; lean_object* v___x_419_; 
lean_inc_ref(v_tail_415_);
lean_dec(v_h__2_414_);
v_head_416_ = lean_ctor_get(v_ws_412_, 0);
lean_inc(v_head_416_);
lean_dec_ref_known(v_ws_412_, 2);
v_head_417_ = lean_ctor_get(v_tail_415_, 0);
lean_inc(v_head_417_);
v_tail_418_ = lean_ctor_get(v_tail_415_, 1);
lean_inc(v_tail_418_);
lean_dec_ref_known(v_tail_415_, 2);
v___x_419_ = lean_apply_3(v_h__1_413_, v_head_416_, v_head_417_, v_tail_418_);
return v___x_419_;
}
else
{
lean_object* v___x_420_; 
lean_dec(v_h__1_413_);
v___x_420_ = lean_apply_2(v_h__2_414_, v_ws_412_, lean_box(0));
return v___x_420_;
}
}
else
{
lean_object* v___x_421_; 
lean_dec(v_h__1_413_);
v___x_421_ = lean_apply_2(v_h__2_414_, v_ws_412_, lean_box(0));
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__6_splitter(lean_object* v_motive_422_, lean_object* v_ws_423_, lean_object* v_h__1_424_, lean_object* v_h__2_425_){
_start:
{
if (lean_obj_tag(v_ws_423_) == 1)
{
lean_object* v_tail_426_; 
v_tail_426_ = lean_ctor_get(v_ws_423_, 1);
if (lean_obj_tag(v_tail_426_) == 1)
{
lean_object* v_head_427_; lean_object* v_head_428_; lean_object* v_tail_429_; lean_object* v___x_430_; 
lean_inc_ref(v_tail_426_);
lean_dec(v_h__2_425_);
v_head_427_ = lean_ctor_get(v_ws_423_, 0);
lean_inc(v_head_427_);
lean_dec_ref_known(v_ws_423_, 2);
v_head_428_ = lean_ctor_get(v_tail_426_, 0);
lean_inc(v_head_428_);
v_tail_429_ = lean_ctor_get(v_tail_426_, 1);
lean_inc(v_tail_429_);
lean_dec_ref_known(v_tail_426_, 2);
v___x_430_ = lean_apply_3(v_h__1_424_, v_head_427_, v_head_428_, v_tail_429_);
return v___x_430_;
}
else
{
lean_object* v___x_431_; 
lean_dec(v_h__1_424_);
v___x_431_ = lean_apply_2(v_h__2_425_, v_ws_423_, lean_box(0));
return v___x_431_;
}
}
else
{
lean_object* v___x_432_; 
lean_dec(v_h__1_424_);
v___x_432_ = lean_apply_2(v_h__2_425_, v_ws_423_, lean_box(0));
return v___x_432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__8_splitter___redArg(lean_object* v_ws_433_, lean_object* v_h__1_434_, lean_object* v_h__2_435_){
_start:
{
if (lean_obj_tag(v_ws_433_) == 1)
{
lean_object* v_tail_436_; 
v_tail_436_ = lean_ctor_get(v_ws_433_, 1);
if (lean_obj_tag(v_tail_436_) == 1)
{
lean_object* v_tail_437_; 
v_tail_437_ = lean_ctor_get(v_tail_436_, 1);
if (lean_obj_tag(v_tail_437_) == 1)
{
lean_object* v_head_438_; lean_object* v_head_439_; lean_object* v_head_440_; lean_object* v_tail_441_; lean_object* v___x_442_; 
lean_inc_ref(v_tail_437_);
lean_inc_ref(v_tail_436_);
lean_dec(v_h__2_435_);
v_head_438_ = lean_ctor_get(v_ws_433_, 0);
lean_inc(v_head_438_);
lean_dec_ref_known(v_ws_433_, 2);
v_head_439_ = lean_ctor_get(v_tail_436_, 0);
lean_inc(v_head_439_);
lean_dec_ref_known(v_tail_436_, 2);
v_head_440_ = lean_ctor_get(v_tail_437_, 0);
lean_inc(v_head_440_);
v_tail_441_ = lean_ctor_get(v_tail_437_, 1);
lean_inc(v_tail_441_);
lean_dec_ref_known(v_tail_437_, 2);
v___x_442_ = lean_apply_4(v_h__1_434_, v_head_438_, v_head_439_, v_head_440_, v_tail_441_);
return v___x_442_;
}
else
{
lean_object* v___x_443_; 
lean_dec(v_h__1_434_);
v___x_443_ = lean_apply_2(v_h__2_435_, v_ws_433_, lean_box(0));
return v___x_443_;
}
}
else
{
lean_object* v___x_444_; 
lean_dec(v_h__1_434_);
v___x_444_ = lean_apply_2(v_h__2_435_, v_ws_433_, lean_box(0));
return v___x_444_;
}
}
else
{
lean_object* v___x_445_; 
lean_dec(v_h__1_434_);
v___x_445_ = lean_apply_2(v_h__2_435_, v_ws_433_, lean_box(0));
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__8_splitter(lean_object* v_motive_446_, lean_object* v_ws_447_, lean_object* v_h__1_448_, lean_object* v_h__2_449_){
_start:
{
if (lean_obj_tag(v_ws_447_) == 1)
{
lean_object* v_tail_450_; 
v_tail_450_ = lean_ctor_get(v_ws_447_, 1);
if (lean_obj_tag(v_tail_450_) == 1)
{
lean_object* v_tail_451_; 
v_tail_451_ = lean_ctor_get(v_tail_450_, 1);
if (lean_obj_tag(v_tail_451_) == 1)
{
lean_object* v_head_452_; lean_object* v_head_453_; lean_object* v_head_454_; lean_object* v_tail_455_; lean_object* v___x_456_; 
lean_inc_ref(v_tail_451_);
lean_inc_ref(v_tail_450_);
lean_dec(v_h__2_449_);
v_head_452_ = lean_ctor_get(v_ws_447_, 0);
lean_inc(v_head_452_);
lean_dec_ref_known(v_ws_447_, 2);
v_head_453_ = lean_ctor_get(v_tail_450_, 0);
lean_inc(v_head_453_);
lean_dec_ref_known(v_tail_450_, 2);
v_head_454_ = lean_ctor_get(v_tail_451_, 0);
lean_inc(v_head_454_);
v_tail_455_ = lean_ctor_get(v_tail_451_, 1);
lean_inc(v_tail_455_);
lean_dec_ref_known(v_tail_451_, 2);
v___x_456_ = lean_apply_4(v_h__1_448_, v_head_452_, v_head_453_, v_head_454_, v_tail_455_);
return v___x_456_;
}
else
{
lean_object* v___x_457_; 
lean_dec(v_h__1_448_);
v___x_457_ = lean_apply_2(v_h__2_449_, v_ws_447_, lean_box(0));
return v___x_457_;
}
}
else
{
lean_object* v___x_458_; 
lean_dec(v_h__1_448_);
v___x_458_ = lean_apply_2(v_h__2_449_, v_ws_447_, lean_box(0));
return v___x_458_;
}
}
else
{
lean_object* v___x_459_; 
lean_dec(v_h__1_448_);
v___x_459_ = lean_apply_2(v_h__2_449_, v_ws_447_, lean_box(0));
return v___x_459_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(uint8_t v_x_460_, lean_object* v_h__1_461_, lean_object* v_h__2_462_, lean_object* v_h__3_463_, lean_object* v_h__4_464_, lean_object* v_h__5_465_){
_start:
{
switch(v_x_460_)
{
case 0:
{
lean_object* v___x_466_; 
lean_dec(v_h__5_465_);
lean_dec(v_h__4_464_);
lean_dec(v_h__3_463_);
lean_dec(v_h__2_462_);
v___x_466_ = lean_apply_1(v_h__1_461_, lean_box(0));
return v___x_466_;
}
case 1:
{
lean_object* v___x_467_; 
lean_dec(v_h__5_465_);
lean_dec(v_h__4_464_);
lean_dec(v_h__3_463_);
lean_dec(v_h__1_461_);
v___x_467_ = lean_apply_1(v_h__2_462_, lean_box(0));
return v___x_467_;
}
case 2:
{
lean_object* v___x_468_; 
lean_dec(v_h__5_465_);
lean_dec(v_h__4_464_);
lean_dec(v_h__2_462_);
lean_dec(v_h__1_461_);
v___x_468_ = lean_apply_1(v_h__3_463_, lean_box(0));
return v___x_468_;
}
case 3:
{
lean_object* v___x_469_; 
lean_dec(v_h__5_465_);
lean_dec(v_h__3_463_);
lean_dec(v_h__2_462_);
lean_dec(v_h__1_461_);
v___x_469_ = lean_apply_1(v_h__4_464_, lean_box(0));
return v___x_469_;
}
default: 
{
lean_object* v___x_470_; 
lean_dec(v_h__4_464_);
lean_dec(v_h__3_463_);
lean_dec(v_h__2_462_);
lean_dec(v_h__1_461_);
v___x_470_ = lean_apply_1(v_h__5_465_, lean_box(0));
return v___x_470_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg___boxed(lean_object* v_x_471_, lean_object* v_h__1_472_, lean_object* v_h__2_473_, lean_object* v_h__3_474_, lean_object* v_h__4_475_, lean_object* v_h__5_476_){
_start:
{
uint8_t v_x_47__boxed_477_; lean_object* v_res_478_; 
v_x_47__boxed_477_ = lean_unbox(v_x_471_);
v_res_478_ = l___private_Init_Data_String_Basic_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(v_x_47__boxed_477_, v_h__1_472_, v_h__2_473_, v_h__3_474_, v_h__4_475_, v_h__5_476_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(lean_object* v_motive_479_, uint8_t v_x_480_, lean_object* v_h__1_481_, lean_object* v_h__2_482_, lean_object* v_h__3_483_, lean_object* v_h__4_484_, lean_object* v_h__5_485_){
_start:
{
switch(v_x_480_)
{
case 0:
{
lean_object* v___x_486_; 
lean_dec(v_h__5_485_);
lean_dec(v_h__4_484_);
lean_dec(v_h__3_483_);
lean_dec(v_h__2_482_);
v___x_486_ = lean_apply_1(v_h__1_481_, lean_box(0));
return v___x_486_;
}
case 1:
{
lean_object* v___x_487_; 
lean_dec(v_h__5_485_);
lean_dec(v_h__4_484_);
lean_dec(v_h__3_483_);
lean_dec(v_h__1_481_);
v___x_487_ = lean_apply_1(v_h__2_482_, lean_box(0));
return v___x_487_;
}
case 2:
{
lean_object* v___x_488_; 
lean_dec(v_h__5_485_);
lean_dec(v_h__4_484_);
lean_dec(v_h__2_482_);
lean_dec(v_h__1_481_);
v___x_488_ = lean_apply_1(v_h__3_483_, lean_box(0));
return v___x_488_;
}
case 3:
{
lean_object* v___x_489_; 
lean_dec(v_h__5_485_);
lean_dec(v_h__3_483_);
lean_dec(v_h__2_482_);
lean_dec(v_h__1_481_);
v___x_489_ = lean_apply_1(v_h__4_484_, lean_box(0));
return v___x_489_;
}
default: 
{
lean_object* v___x_490_; 
lean_dec(v_h__4_484_);
lean_dec(v_h__3_483_);
lean_dec(v_h__2_482_);
lean_dec(v_h__1_481_);
v___x_490_ = lean_apply_1(v_h__5_485_, lean_box(0));
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___boxed(lean_object* v_motive_491_, lean_object* v_x_492_, lean_object* v_h__1_493_, lean_object* v_h__2_494_, lean_object* v_h__3_495_, lean_object* v_h__4_496_, lean_object* v_h__5_497_){
_start:
{
uint8_t v_x_60__boxed_498_; lean_object* v_res_499_; 
v_x_60__boxed_498_ = lean_unbox(v_x_492_);
v_res_499_ = l___private_Init_Data_String_Basic_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(v_motive_491_, v_x_60__boxed_498_, v_h__1_493_, v_h__2_494_, v_h__3_495_, v_h__4_496_, v_h__5_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__1_splitter___redArg(lean_object* v_x_500_, lean_object* v_h__1_501_, lean_object* v_h__2_502_){
_start:
{
if (lean_obj_tag(v_x_500_) == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec(v_h__1_501_);
v___x_503_ = lean_box(0);
v___x_504_ = lean_apply_1(v_h__2_502_, v___x_503_);
return v___x_504_;
}
else
{
lean_object* v_val_505_; lean_object* v___x_506_; 
lean_dec(v_h__2_502_);
v_val_505_ = lean_ctor_get(v_x_500_, 0);
lean_inc(v_val_505_);
lean_dec_ref_known(v_x_500_, 1);
v___x_506_ = lean_apply_1(v_h__1_501_, v_val_505_);
return v___x_506_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Internal_utf8DecodeList_match__1_splitter(lean_object* v_motive_507_, lean_object* v_x_508_, lean_object* v_h__1_509_, lean_object* v_h__2_510_){
_start:
{
if (lean_obj_tag(v_x_508_) == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec(v_h__1_509_);
v___x_511_ = lean_box(0);
v___x_512_ = lean_apply_1(v_h__2_510_, v___x_511_);
return v___x_512_;
}
else
{
lean_object* v_val_513_; lean_object* v___x_514_; 
lean_dec(v_h__2_510_);
v_val_513_ = lean_ctor_get(v_x_508_, 0);
lean_inc(v_val_513_);
lean_dec_ref_known(v_x_508_, 1);
v___x_514_ = lean_apply_1(v_h__1_509_, v_val_513_);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValid___boxed(lean_object* v_s_517_, lean_object* v_p_518_){
_start:
{
uint8_t v_res_519_; lean_object* v_r_520_; 
v_res_519_ = lean_string_is_valid_pos(v_s_517_, v_p_518_);
lean_dec(v_p_518_);
lean_dec_ref(v_s_517_);
v_r_520_ = lean_box(v_res_519_);
return v_r_520_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsValid(lean_object* v_s_521_, lean_object* v_p_522_){
_start:
{
uint8_t v___x_523_; 
v___x_523_ = lean_string_is_valid_pos(v_s_521_, v_p_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsValid___boxed(lean_object* v_s_524_, lean_object* v_p_525_){
_start:
{
uint8_t v_res_526_; lean_object* v_r_527_; 
v_res_526_ = l_String_instDecidableIsValid(v_s_524_, v_p_525_);
lean_dec(v_p_525_);
lean_dec_ref(v_s_524_);
v_r_527_ = lean_box(v_res_526_);
return v_r_527_;
}
}
LEAN_EXPORT lean_object* l_String_extract___boxed(lean_object* v_s_531_, lean_object* v_b_532_, lean_object* v_e_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = lean_string_utf8_extract_fast(v_s_531_, v_b_532_, v_e_533_);
lean_dec(v_e_533_);
lean_dec(v_b_532_);
lean_dec_ref(v_s_531_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_extract(lean_object* v_s_535_, lean_object* v_b_536_, lean_object* v_e_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = lean_string_utf8_extract_fast(v_s_535_, v_b_536_, v_e_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_extract___boxed(lean_object* v_s_539_, lean_object* v_b_540_, lean_object* v_e_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_String_Pos_extract(v_s_539_, v_b_540_, v_e_541_);
lean_dec(v_e_541_);
lean_dec(v_b_540_);
lean_dec_ref(v_s_539_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_copy(lean_object* v_s_543_){
_start:
{
lean_object* v_str_544_; lean_object* v_startInclusive_545_; lean_object* v_endExclusive_546_; lean_object* v___x_547_; 
v_str_544_ = lean_ctor_get(v_s_543_, 0);
v_startInclusive_545_ = lean_ctor_get(v_s_543_, 1);
v_endExclusive_546_ = lean_ctor_get(v_s_543_, 2);
v___x_547_ = lean_string_utf8_extract_fast(v_str_544_, v_startInclusive_545_, v_endExclusive_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_copy___boxed(lean_object* v_s_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_String_Slice_copy(v_s_548_);
lean_dec_ref(v_s_548_);
return v_res_549_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_isValidForSlice(lean_object* v_s_550_, lean_object* v_p_551_){
_start:
{
lean_object* v_str_552_; lean_object* v_startInclusive_553_; lean_object* v_endExclusive_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_str_552_ = lean_ctor_get(v_s_550_, 0);
v_startInclusive_553_ = lean_ctor_get(v_s_550_, 1);
v_endExclusive_554_ = lean_ctor_get(v_s_550_, 2);
v___x_555_ = lean_nat_sub(v_endExclusive_554_, v_startInclusive_553_);
v___x_556_ = lean_unsigned_to_nat(1u);
v___x_557_ = lean_nat_add(v_p_551_, v___x_556_);
v___x_558_ = lean_nat_dec_le(v___x_557_, v___x_555_);
lean_dec(v___x_557_);
if (v___x_558_ == 0)
{
uint8_t v_decide_559_; 
v_decide_559_ = lean_nat_dec_eq(v_p_551_, v___x_555_);
lean_dec(v___x_555_);
return v_decide_559_;
}
else
{
lean_object* v___x_560_; uint8_t v___x_561_; uint8_t v___x_562_; uint8_t v___x_563_; uint8_t v___x_564_; uint8_t v___x_565_; 
lean_dec(v___x_555_);
v___x_560_ = lean_nat_add(v_startInclusive_553_, v_p_551_);
v___x_561_ = lean_string_get_byte_fast(v_str_552_, v___x_560_);
v___x_562_ = 128;
v___x_563_ = lean_uint8_land(v___x_561_, v___x_562_);
v___x_564_ = 0;
v___x_565_ = lean_uint8_dec_eq(v___x_563_, v___x_564_);
if (v___x_565_ == 0)
{
uint8_t v___x_566_; uint8_t v___x_567_; uint8_t v___x_568_; uint8_t v___x_569_; 
v___x_566_ = 224;
v___x_567_ = lean_uint8_land(v___x_561_, v___x_566_);
v___x_568_ = 192;
v___x_569_ = lean_uint8_dec_eq(v___x_567_, v___x_568_);
if (v___x_569_ == 0)
{
uint8_t v___x_570_; uint8_t v___x_571_; uint8_t v___x_572_; 
v___x_570_ = 240;
v___x_571_ = lean_uint8_land(v___x_561_, v___x_570_);
v___x_572_ = lean_uint8_dec_eq(v___x_571_, v___x_566_);
if (v___x_572_ == 0)
{
uint8_t v___x_573_; uint8_t v___x_574_; uint8_t v___x_575_; 
v___x_573_ = 248;
v___x_574_ = lean_uint8_land(v___x_561_, v___x_573_);
v___x_575_ = lean_uint8_dec_eq(v___x_574_, v___x_570_);
return v___x_575_;
}
else
{
return v___x_572_;
}
}
else
{
return v___x_569_;
}
}
else
{
return v___x_565_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValidForSlice___boxed(lean_object* v_s_576_, lean_object* v_p_577_){
_start:
{
uint8_t v_res_578_; lean_object* v_r_579_; 
v_res_578_ = l_String_Pos_Raw_isValidForSlice(v_s_576_, v_p_577_);
lean_dec(v_p_577_);
lean_dec_ref(v_s_576_);
v_r_579_ = lean_box(v_res_578_);
return v_r_579_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsValidForSlice(lean_object* v_s_580_, lean_object* v_p_581_){
_start:
{
uint8_t v___x_582_; 
v___x_582_ = l_String_Pos_Raw_isValidForSlice(v_s_580_, v_p_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsValidForSlice___boxed(lean_object* v_s_583_, lean_object* v_p_584_){
_start:
{
uint8_t v_res_585_; lean_object* v_r_586_; 
v_res_585_ = l_String_instDecidableIsValidForSlice(v_s_583_, v_p_584_);
lean_dec(v_p_584_);
lean_dec_ref(v_s_583_);
v_r_586_ = lean_box(v_res_585_);
return v_r_586_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str(lean_object* v_s_587_, lean_object* v_pos_588_){
_start:
{
lean_object* v_startInclusive_589_; lean_object* v___x_590_; 
v_startInclusive_589_ = lean_ctor_get(v_s_587_, 1);
v___x_590_ = lean_nat_add(v_startInclusive_589_, v_pos_588_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str___boxed(lean_object* v_s_591_, lean_object* v_pos_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_String_Slice_Pos_str(v_s_591_, v_pos_592_);
lean_dec(v_pos_592_);
lean_dec_ref(v_s_591_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg(lean_object* v_s_594_, lean_object* v_pos_595_){
_start:
{
lean_object* v_startInclusive_596_; lean_object* v___x_597_; 
v_startInclusive_596_ = lean_ctor_get(v_s_594_, 1);
v___x_597_ = lean_nat_sub(v_pos_595_, v_startInclusive_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg___boxed(lean_object* v_s_598_, lean_object* v_pos_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_String_Slice_Pos_ofStr___redArg(v_s_598_, v_pos_599_);
lean_dec(v_pos_599_);
lean_dec_ref(v_s_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr(lean_object* v_s_601_, lean_object* v_pos_602_, lean_object* v_h_u2081_603_, lean_object* v_h_u2082_604_){
_start:
{
lean_object* v_startInclusive_605_; lean_object* v___x_606_; 
v_startInclusive_605_ = lean_ctor_get(v_s_601_, 1);
v___x_606_ = lean_nat_sub(v_pos_602_, v_startInclusive_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___boxed(lean_object* v_s_607_, lean_object* v_pos_608_, lean_object* v_h_u2081_609_, lean_object* v_h_u2082_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_String_Slice_Pos_ofStr(v_s_607_, v_pos_608_, v_h_u2081_609_, v_h_u2082_610_);
lean_dec(v_pos_608_);
lean_dec_ref(v_s_607_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom(lean_object* v_s_612_, lean_object* v_pos_613_){
_start:
{
lean_object* v_str_614_; lean_object* v_startInclusive_615_; lean_object* v_endExclusive_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_624_; 
v_str_614_ = lean_ctor_get(v_s_612_, 0);
v_startInclusive_615_ = lean_ctor_get(v_s_612_, 1);
v_endExclusive_616_ = lean_ctor_get(v_s_612_, 2);
v_isSharedCheck_624_ = !lean_is_exclusive(v_s_612_);
if (v_isSharedCheck_624_ == 0)
{
v___x_618_ = v_s_612_;
v_isShared_619_ = v_isSharedCheck_624_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_endExclusive_616_);
lean_inc(v_startInclusive_615_);
lean_inc(v_str_614_);
lean_dec(v_s_612_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_624_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_620_ = lean_nat_add(v_startInclusive_615_, v_pos_613_);
lean_dec(v_startInclusive_615_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 1, v___x_620_);
v___x_622_ = v___x_618_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_str_614_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_623_, 2, v_endExclusive_616_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom___boxed(lean_object* v_s_625_, lean_object* v_pos_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_String_Slice_sliceFrom(v_s_625_, v_pos_626_);
lean_dec(v_pos_626_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStart(lean_object* v_s_628_, lean_object* v_pos_629_){
_start:
{
lean_object* v_str_630_; lean_object* v_startInclusive_631_; lean_object* v_endExclusive_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_640_; 
v_str_630_ = lean_ctor_get(v_s_628_, 0);
v_startInclusive_631_ = lean_ctor_get(v_s_628_, 1);
v_endExclusive_632_ = lean_ctor_get(v_s_628_, 2);
v_isSharedCheck_640_ = !lean_is_exclusive(v_s_628_);
if (v_isSharedCheck_640_ == 0)
{
v___x_634_ = v_s_628_;
v_isShared_635_ = v_isSharedCheck_640_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_endExclusive_632_);
lean_inc(v_startInclusive_631_);
lean_inc(v_str_630_);
lean_dec(v_s_628_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_640_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_636_ = lean_nat_add(v_startInclusive_631_, v_pos_629_);
lean_dec(v_startInclusive_631_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 1, v___x_636_);
v___x_638_ = v___x_634_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_str_630_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_639_, 2, v_endExclusive_632_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStart___boxed(lean_object* v_s_641_, lean_object* v_pos_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_String_Slice_replaceStart(v_s_641_, v_pos_642_);
lean_dec(v_pos_642_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceTo(lean_object* v_s_644_, lean_object* v_pos_645_){
_start:
{
lean_object* v_str_646_; lean_object* v_startInclusive_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_655_; 
v_str_646_ = lean_ctor_get(v_s_644_, 0);
v_startInclusive_647_ = lean_ctor_get(v_s_644_, 1);
v_isSharedCheck_655_ = !lean_is_exclusive(v_s_644_);
if (v_isSharedCheck_655_ == 0)
{
lean_object* v_unused_656_; 
v_unused_656_ = lean_ctor_get(v_s_644_, 2);
lean_dec(v_unused_656_);
v___x_649_ = v_s_644_;
v_isShared_650_ = v_isSharedCheck_655_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_startInclusive_647_);
lean_inc(v_str_646_);
lean_dec(v_s_644_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_655_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_653_; 
v___x_651_ = lean_nat_add(v_startInclusive_647_, v_pos_645_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 2, v___x_651_);
v___x_653_ = v___x_649_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_str_646_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_startInclusive_647_);
lean_ctor_set(v_reuseFailAlloc_654_, 2, v___x_651_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceTo___boxed(lean_object* v_s_657_, lean_object* v_pos_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_String_Slice_sliceTo(v_s_657_, v_pos_658_);
lean_dec(v_pos_658_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd(lean_object* v_s_660_, lean_object* v_pos_661_){
_start:
{
lean_object* v_str_662_; lean_object* v_startInclusive_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_671_; 
v_str_662_ = lean_ctor_get(v_s_660_, 0);
v_startInclusive_663_ = lean_ctor_get(v_s_660_, 1);
v_isSharedCheck_671_ = !lean_is_exclusive(v_s_660_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; 
v_unused_672_ = lean_ctor_get(v_s_660_, 2);
lean_dec(v_unused_672_);
v___x_665_ = v_s_660_;
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_startInclusive_663_);
lean_inc(v_str_662_);
lean_dec(v_s_660_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_667_ = lean_nat_add(v_startInclusive_663_, v_pos_661_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 2, v___x_667_);
v___x_669_ = v___x_665_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_str_662_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_startInclusive_663_);
lean_ctor_set(v_reuseFailAlloc_670_, 2, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd___boxed(lean_object* v_s_673_, lean_object* v_pos_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_String_Slice_replaceEnd(v_s_673_, v_pos_674_);
lean_dec(v_pos_674_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg(lean_object* v_s_676_, lean_object* v_newStart_677_, lean_object* v_newEnd_678_){
_start:
{
lean_object* v_str_679_; lean_object* v_startInclusive_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_689_; 
v_str_679_ = lean_ctor_get(v_s_676_, 0);
v_startInclusive_680_ = lean_ctor_get(v_s_676_, 1);
v_isSharedCheck_689_ = !lean_is_exclusive(v_s_676_);
if (v_isSharedCheck_689_ == 0)
{
lean_object* v_unused_690_; 
v_unused_690_ = lean_ctor_get(v_s_676_, 2);
lean_dec(v_unused_690_);
v___x_682_ = v_s_676_;
v_isShared_683_ = v_isSharedCheck_689_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_startInclusive_680_);
lean_inc(v_str_679_);
lean_dec(v_s_676_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_689_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_684_ = lean_nat_add(v_startInclusive_680_, v_newStart_677_);
v___x_685_ = lean_nat_add(v_startInclusive_680_, v_newEnd_678_);
lean_dec(v_startInclusive_680_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 2, v___x_685_);
lean_ctor_set(v___x_682_, 1, v___x_684_);
v___x_687_ = v___x_682_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_str_679_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg___boxed(lean_object* v_s_691_, lean_object* v_newStart_692_, lean_object* v_newEnd_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_String_Slice_slice___redArg(v_s_691_, v_newStart_692_, v_newEnd_693_);
lean_dec(v_newEnd_693_);
lean_dec(v_newStart_692_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice(lean_object* v_s_695_, lean_object* v_newStart_696_, lean_object* v_newEnd_697_, lean_object* v_h_698_){
_start:
{
lean_object* v_str_699_; lean_object* v_startInclusive_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_709_; 
v_str_699_ = lean_ctor_get(v_s_695_, 0);
v_startInclusive_700_ = lean_ctor_get(v_s_695_, 1);
v_isSharedCheck_709_ = !lean_is_exclusive(v_s_695_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; 
v_unused_710_ = lean_ctor_get(v_s_695_, 2);
lean_dec(v_unused_710_);
v___x_702_ = v_s_695_;
v_isShared_703_ = v_isSharedCheck_709_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_startInclusive_700_);
lean_inc(v_str_699_);
lean_dec(v_s_695_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_709_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_707_; 
v___x_704_ = lean_nat_add(v_startInclusive_700_, v_newStart_696_);
v___x_705_ = lean_nat_add(v_startInclusive_700_, v_newEnd_697_);
lean_dec(v_startInclusive_700_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 2, v___x_705_);
lean_ctor_set(v___x_702_, 1, v___x_704_);
v___x_707_ = v___x_702_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_str_699_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_708_, 2, v___x_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___boxed(lean_object* v_s_711_, lean_object* v_newStart_712_, lean_object* v_newEnd_713_, lean_object* v_h_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_String_Slice_slice(v_s_711_, v_newStart_712_, v_newEnd_713_, v_h_714_);
lean_dec(v_newEnd_713_);
lean_dec(v_newStart_712_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg(lean_object* v_s_716_, lean_object* v_newStart_717_, lean_object* v_newEnd_718_){
_start:
{
lean_object* v_str_719_; lean_object* v_startInclusive_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_729_; 
v_str_719_ = lean_ctor_get(v_s_716_, 0);
v_startInclusive_720_ = lean_ctor_get(v_s_716_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v_s_716_);
if (v_isSharedCheck_729_ == 0)
{
lean_object* v_unused_730_; 
v_unused_730_ = lean_ctor_get(v_s_716_, 2);
lean_dec(v_unused_730_);
v___x_722_ = v_s_716_;
v_isShared_723_ = v_isSharedCheck_729_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_startInclusive_720_);
lean_inc(v_str_719_);
lean_dec(v_s_716_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_729_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_724_ = lean_nat_add(v_startInclusive_720_, v_newStart_717_);
v___x_725_ = lean_nat_add(v_startInclusive_720_, v_newEnd_718_);
lean_dec(v_startInclusive_720_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 2, v___x_725_);
lean_ctor_set(v___x_722_, 1, v___x_724_);
v___x_727_ = v___x_722_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_str_719_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_728_, 2, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg___boxed(lean_object* v_s_731_, lean_object* v_newStart_732_, lean_object* v_newEnd_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_String_Slice_replaceStartEnd___redArg(v_s_731_, v_newStart_732_, v_newEnd_733_);
lean_dec(v_newEnd_733_);
lean_dec(v_newStart_732_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd(lean_object* v_s_735_, lean_object* v_newStart_736_, lean_object* v_newEnd_737_, lean_object* v_h_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_String_Slice_replaceStartEnd___redArg(v_s_735_, v_newStart_736_, v_newEnd_737_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___boxed(lean_object* v_s_740_, lean_object* v_newStart_741_, lean_object* v_newEnd_742_, lean_object* v_h_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_String_Slice_replaceStartEnd(v_s_740_, v_newStart_741_, v_newEnd_742_, v_h_743_);
lean_dec(v_newEnd_742_);
lean_dec(v_newStart_741_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f(lean_object* v_s_745_, lean_object* v_newStart_746_, lean_object* v_newEnd_747_){
_start:
{
uint8_t v___x_748_; 
v___x_748_ = lean_nat_dec_le(v_newStart_746_, v_newEnd_747_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; 
lean_dec_ref(v_s_745_);
v___x_749_ = lean_box(0);
return v___x_749_;
}
else
{
lean_object* v_str_750_; lean_object* v_startInclusive_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_761_; 
v_str_750_ = lean_ctor_get(v_s_745_, 0);
v_startInclusive_751_ = lean_ctor_get(v_s_745_, 1);
v_isSharedCheck_761_ = !lean_is_exclusive(v_s_745_);
if (v_isSharedCheck_761_ == 0)
{
lean_object* v_unused_762_; 
v_unused_762_ = lean_ctor_get(v_s_745_, 2);
lean_dec(v_unused_762_);
v___x_753_ = v_s_745_;
v_isShared_754_ = v_isSharedCheck_761_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_startInclusive_751_);
lean_inc(v_str_750_);
lean_dec(v_s_745_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_761_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
v___x_755_ = lean_nat_add(v_startInclusive_751_, v_newStart_746_);
v___x_756_ = lean_nat_add(v_startInclusive_751_, v_newEnd_747_);
lean_dec(v_startInclusive_751_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 2, v___x_756_);
lean_ctor_set(v___x_753_, 1, v___x_755_);
v___x_758_ = v___x_753_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_str_750_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_760_, 2, v___x_756_);
v___x_758_ = v_reuseFailAlloc_760_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_759_; 
v___x_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
return v___x_759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f___boxed(lean_object* v_s_763_, lean_object* v_newStart_764_, lean_object* v_newEnd_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_String_Slice_slice_x3f(v_s_763_, v_newStart_764_, v_newEnd_765_);
lean_dec(v_newEnd_765_);
lean_dec(v_newStart_764_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_slice_x21_spec__0(lean_object* v_msg_767_){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = l_String_instInhabitedSlice;
v___x_769_ = lean_panic_fn_borrowed(v___x_768_, v_msg_767_);
return v___x_769_;
}
}
static lean_object* _init_l_String_Slice_slice_x21___closed__2(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_772_ = ((lean_object*)(l_String_Slice_slice_x21___closed__1));
v___x_773_ = lean_unsigned_to_nat(4u);
v___x_774_ = lean_unsigned_to_nat(1038u);
v___x_775_ = ((lean_object*)(l_String_Slice_slice_x21___closed__0));
v___x_776_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_777_ = l_mkPanicMessageWithDecl(v___x_776_, v___x_775_, v___x_774_, v___x_773_, v___x_772_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x21(lean_object* v_s_778_, lean_object* v_newStart_779_, lean_object* v_newEnd_780_){
_start:
{
uint8_t v___x_781_; 
v___x_781_ = lean_nat_dec_le(v_newStart_779_, v_newEnd_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; 
lean_dec_ref(v_s_778_);
v___x_782_ = lean_obj_once(&l_String_Slice_slice_x21___closed__2, &l_String_Slice_slice_x21___closed__2_once, _init_l_String_Slice_slice_x21___closed__2);
v___x_783_ = l_panic___at___00String_Slice_slice_x21_spec__0(v___x_782_);
return v___x_783_;
}
else
{
lean_object* v_str_784_; lean_object* v_startInclusive_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_794_; 
v_str_784_ = lean_ctor_get(v_s_778_, 0);
v_startInclusive_785_ = lean_ctor_get(v_s_778_, 1);
v_isSharedCheck_794_ = !lean_is_exclusive(v_s_778_);
if (v_isSharedCheck_794_ == 0)
{
lean_object* v_unused_795_; 
v_unused_795_ = lean_ctor_get(v_s_778_, 2);
lean_dec(v_unused_795_);
v___x_787_ = v_s_778_;
v_isShared_788_ = v_isSharedCheck_794_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_startInclusive_785_);
lean_inc(v_str_784_);
lean_dec(v_s_778_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_794_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_789_ = lean_nat_add(v_startInclusive_785_, v_newStart_779_);
v___x_790_ = lean_nat_add(v_startInclusive_785_, v_newEnd_780_);
lean_dec(v_startInclusive_785_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 2, v___x_790_);
lean_ctor_set(v___x_787_, 1, v___x_789_);
v___x_792_ = v___x_787_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_str_784_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x21___boxed(lean_object* v_s_796_, lean_object* v_newStart_797_, lean_object* v_newEnd_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_String_Slice_slice_x21(v_s_796_, v_newStart_797_, v_newEnd_798_);
lean_dec(v_newEnd_798_);
lean_dec(v_newStart_797_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21(lean_object* v_s_800_, lean_object* v_newStart_801_, lean_object* v_newEnd_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_String_Slice_slice_x21(v_s_800_, v_newStart_801_, v_newEnd_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21___boxed(lean_object* v_s_804_, lean_object* v_newStart_805_, lean_object* v_newEnd_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_String_Slice_replaceStartEnd_x21(v_s_804_, v_newStart_805_, v_newEnd_806_);
lean_dec(v_newEnd_806_);
lean_dec(v_newStart_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_String_decodeChar___boxed(lean_object* v_s_811_, lean_object* v_byteIdx_812_, lean_object* v_h_813_){
_start:
{
uint32_t v_res_814_; lean_object* v_r_815_; 
v_res_814_ = lean_string_utf8_get_fast(v_s_811_, v_byteIdx_812_);
lean_dec(v_byteIdx_812_);
lean_dec_ref(v_s_811_);
v_r_815_ = lean_box_uint32(v_res_814_);
return v_r_815_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get___redArg(lean_object* v_s_816_, lean_object* v_pos_817_){
_start:
{
lean_object* v_str_818_; lean_object* v_startInclusive_819_; lean_object* v___x_820_; uint32_t v___x_821_; 
v_str_818_ = lean_ctor_get(v_s_816_, 0);
v_startInclusive_819_ = lean_ctor_get(v_s_816_, 1);
v___x_820_ = lean_nat_add(v_startInclusive_819_, v_pos_817_);
v___x_821_ = lean_string_utf8_get_fast(v_str_818_, v___x_820_);
lean_dec(v___x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___redArg___boxed(lean_object* v_s_822_, lean_object* v_pos_823_){
_start:
{
uint32_t v_res_824_; lean_object* v_r_825_; 
v_res_824_ = l_String_Slice_Pos_get___redArg(v_s_822_, v_pos_823_);
lean_dec(v_pos_823_);
lean_dec_ref(v_s_822_);
v_r_825_ = lean_box_uint32(v_res_824_);
return v_r_825_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get(lean_object* v_s_826_, lean_object* v_pos_827_, lean_object* v_h_828_){
_start:
{
lean_object* v_str_829_; lean_object* v_startInclusive_830_; lean_object* v___x_831_; uint32_t v___x_832_; 
v_str_829_ = lean_ctor_get(v_s_826_, 0);
v_startInclusive_830_ = lean_ctor_get(v_s_826_, 1);
v___x_831_ = lean_nat_add(v_startInclusive_830_, v_pos_827_);
v___x_832_ = lean_string_utf8_get_fast(v_str_829_, v___x_831_);
lean_dec(v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___boxed(lean_object* v_s_833_, lean_object* v_pos_834_, lean_object* v_h_835_){
_start:
{
uint32_t v_res_836_; lean_object* v_r_837_; 
v_res_836_ = l_String_Slice_Pos_get(v_s_833_, v_pos_834_, v_h_835_);
lean_dec(v_pos_834_);
lean_dec_ref(v_s_833_);
v_r_837_ = lean_box_uint32(v_res_836_);
return v_r_837_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f(lean_object* v_s_838_, lean_object* v_pos_839_){
_start:
{
lean_object* v_str_840_; lean_object* v_startInclusive_841_; lean_object* v_endExclusive_842_; lean_object* v___x_843_; uint8_t v_decide_844_; 
v_str_840_ = lean_ctor_get(v_s_838_, 0);
v_startInclusive_841_ = lean_ctor_get(v_s_838_, 1);
v_endExclusive_842_ = lean_ctor_get(v_s_838_, 2);
v___x_843_ = lean_nat_sub(v_endExclusive_842_, v_startInclusive_841_);
v_decide_844_ = lean_nat_dec_eq(v_pos_839_, v___x_843_);
lean_dec(v___x_843_);
if (v_decide_844_ == 0)
{
lean_object* v___x_845_; uint32_t v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_845_ = lean_nat_add(v_startInclusive_841_, v_pos_839_);
v___x_846_ = lean_string_utf8_get_fast(v_str_840_, v___x_845_);
lean_dec(v___x_845_);
v___x_847_ = lean_box_uint32(v___x_846_);
v___x_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
else
{
lean_object* v___x_849_; 
v___x_849_ = lean_box(0);
return v___x_849_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f___boxed(lean_object* v_s_850_, lean_object* v_pos_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_String_Slice_Pos_get_x3f(v_s_850_, v_pos_851_);
lean_dec(v_pos_851_);
lean_dec_ref(v_s_850_);
return v_res_852_;
}
}
static lean_object* _init_l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1(void){
_start:
{
uint32_t v___x_853_; lean_object* v___x_854_; 
v___x_853_ = 65;
v___x_854_ = lean_box_uint32(v___x_853_);
return v___x_854_;
}
}
LEAN_EXPORT uint32_t l_panic___at___00String_Slice_Pos_get_x21_spec__0(lean_object* v_msg_855_){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; uint32_t v___x_858_; 
v___x_856_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1;
v___x_857_ = lean_panic_fn_borrowed(v___x_856_, v_msg_855_);
v___x_858_ = lean_unbox_uint32(v___x_857_);
lean_dec(v___x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed(lean_object* v_msg_859_){
_start:
{
uint32_t v_res_860_; lean_object* v_r_861_; 
v_res_860_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v_msg_859_);
v_r_861_ = lean_box_uint32(v_res_860_);
return v_r_861_;
}
}
static lean_object* _init_l_String_Slice_Pos_get_x21___closed__2(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_864_ = ((lean_object*)(l_String_Slice_Pos_get_x21___closed__1));
v___x_865_ = lean_unsigned_to_nat(29u);
v___x_866_ = lean_unsigned_to_nat(1123u);
v___x_867_ = ((lean_object*)(l_String_Slice_Pos_get_x21___closed__0));
v___x_868_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_869_ = l_mkPanicMessageWithDecl(v___x_868_, v___x_867_, v___x_866_, v___x_865_, v___x_864_);
return v___x_869_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get_x21(lean_object* v_s_870_, lean_object* v_pos_871_){
_start:
{
lean_object* v_str_872_; lean_object* v_startInclusive_873_; lean_object* v_endExclusive_874_; lean_object* v___x_875_; uint8_t v_decide_876_; 
v_str_872_ = lean_ctor_get(v_s_870_, 0);
v_startInclusive_873_ = lean_ctor_get(v_s_870_, 1);
v_endExclusive_874_ = lean_ctor_get(v_s_870_, 2);
v___x_875_ = lean_nat_sub(v_endExclusive_874_, v_startInclusive_873_);
v_decide_876_ = lean_nat_dec_eq(v_pos_871_, v___x_875_);
lean_dec(v___x_875_);
if (v_decide_876_ == 0)
{
lean_object* v___x_877_; uint32_t v___x_878_; 
v___x_877_ = lean_nat_add(v_startInclusive_873_, v_pos_871_);
v___x_878_ = lean_string_utf8_get_fast(v_str_872_, v___x_877_);
lean_dec(v___x_877_);
return v___x_878_;
}
else
{
lean_object* v___x_879_; uint32_t v___x_880_; 
v___x_879_ = lean_obj_once(&l_String_Slice_Pos_get_x21___closed__2, &l_String_Slice_Pos_get_x21___closed__2_once, _init_l_String_Slice_Pos_get_x21___closed__2);
v___x_880_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v___x_879_);
return v___x_880_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x21___boxed(lean_object* v_s_881_, lean_object* v_pos_882_){
_start:
{
uint32_t v_res_883_; lean_object* v_r_884_; 
v_res_883_ = l_String_Slice_Pos_get_x21(v_s_881_, v_pos_882_);
lean_dec(v_pos_882_);
lean_dec_ref(v_s_881_);
v_r_884_ = lean_box_uint32(v_res_883_);
return v_r_884_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg(lean_object* v_pos_885_){
_start:
{
lean_inc(v_pos_885_);
return v_pos_885_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg___boxed(lean_object* v_pos_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_String_Pos_toSlice___redArg(v_pos_886_);
lean_dec(v_pos_886_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice(lean_object* v_s_888_, lean_object* v_pos_889_){
_start:
{
lean_inc(v_pos_889_);
return v_pos_889_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___boxed(lean_object* v_s_890_, lean_object* v_pos_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_String_Pos_toSlice(v_s_890_, v_pos_891_);
lean_dec(v_pos_891_);
lean_dec_ref(v_s_890_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg(lean_object* v_pos_893_){
_start:
{
lean_inc(v_pos_893_);
return v_pos_893_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg___boxed(lean_object* v_pos_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_String_Pos_ofToSlice___redArg(v_pos_894_);
lean_dec(v_pos_894_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice(lean_object* v_s_896_, lean_object* v_pos_897_){
_start:
{
lean_inc(v_pos_897_);
return v_pos_897_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___boxed(lean_object* v_s_898_, lean_object* v_pos_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_String_Pos_ofToSlice(v_s_898_, v_pos_899_);
lean_dec(v_pos_899_);
lean_dec_ref(v_s_898_);
return v_res_900_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get___redArg(lean_object* v_s_901_, lean_object* v_pos_902_){
_start:
{
uint32_t v___x_903_; 
v___x_903_ = lean_string_utf8_get_fast(v_s_901_, v_pos_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get___redArg___boxed(lean_object* v_s_904_, lean_object* v_pos_905_){
_start:
{
uint32_t v_res_906_; lean_object* v_r_907_; 
v_res_906_ = l_String_Pos_get___redArg(v_s_904_, v_pos_905_);
lean_dec(v_pos_905_);
lean_dec_ref(v_s_904_);
v_r_907_ = lean_box_uint32(v_res_906_);
return v_r_907_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get(lean_object* v_s_908_, lean_object* v_pos_909_, lean_object* v_h_910_){
_start:
{
uint32_t v___x_911_; 
v___x_911_ = lean_string_utf8_get_fast(v_s_908_, v_pos_909_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get___boxed(lean_object* v_s_912_, lean_object* v_pos_913_, lean_object* v_h_914_){
_start:
{
uint32_t v_res_915_; lean_object* v_r_916_; 
v_res_915_ = l_String_Pos_get(v_s_912_, v_pos_913_, v_h_914_);
lean_dec(v_pos_913_);
lean_dec_ref(v_s_912_);
v_r_916_ = lean_box_uint32(v_res_915_);
return v_r_916_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x3f(lean_object* v_s_917_, lean_object* v_pos_918_){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_919_ = lean_unsigned_to_nat(0u);
v___x_920_ = lean_string_utf8_byte_size(v_s_917_);
v___x_921_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_921_, 0, v_s_917_);
lean_ctor_set(v___x_921_, 1, v___x_919_);
lean_ctor_set(v___x_921_, 2, v___x_920_);
v___x_922_ = l_String_Slice_Pos_get_x3f(v___x_921_, v_pos_918_);
lean_dec_ref_known(v___x_921_, 3);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x3f___boxed(lean_object* v_s_923_, lean_object* v_pos_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_String_Pos_get_x3f(v_s_923_, v_pos_924_);
lean_dec(v_pos_924_);
return v_res_925_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get_x21(lean_object* v_s_926_, lean_object* v_pos_927_){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; uint32_t v___x_931_; 
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = lean_string_utf8_byte_size(v_s_926_);
v___x_930_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_930_, 0, v_s_926_);
lean_ctor_set(v___x_930_, 1, v___x_928_);
lean_ctor_set(v___x_930_, 2, v___x_929_);
v___x_931_ = l_String_Slice_Pos_get_x21(v___x_930_, v_pos_927_);
lean_dec_ref_known(v___x_930_, 3);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x21___boxed(lean_object* v_s_932_, lean_object* v_pos_933_){
_start:
{
uint32_t v_res_934_; lean_object* v_r_935_; 
v_res_934_ = l_String_Pos_get_x21(v_s_932_, v_pos_933_);
lean_dec(v_pos_933_);
v_r_935_ = lean_box_uint32(v_res_934_);
return v_r_935_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_byte___redArg(lean_object* v_s_936_, lean_object* v_pos_937_){
_start:
{
uint8_t v___x_938_; 
v___x_938_ = lean_string_get_byte_fast(v_s_936_, v_pos_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_byte___redArg___boxed(lean_object* v_s_939_, lean_object* v_pos_940_){
_start:
{
uint8_t v_res_941_; lean_object* v_r_942_; 
v_res_941_ = l_String_Pos_byte___redArg(v_s_939_, v_pos_940_);
lean_dec_ref(v_s_939_);
v_r_942_ = lean_box(v_res_941_);
return v_r_942_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_byte(lean_object* v_s_943_, lean_object* v_pos_944_, lean_object* v_h_945_){
_start:
{
uint8_t v___x_946_; 
v___x_946_ = lean_string_get_byte_fast(v_s_943_, v_pos_944_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_byte___boxed(lean_object* v_s_947_, lean_object* v_pos_948_, lean_object* v_h_949_){
_start:
{
uint8_t v_res_950_; lean_object* v_r_951_; 
v_res_950_ = l_String_Pos_byte(v_s_947_, v_pos_948_, v_h_949_);
lean_dec_ref(v_s_947_);
v_r_951_ = lean_box(v_res_950_);
return v_r_951_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg(lean_object* v_pos_952_){
_start:
{
lean_inc(v_pos_952_);
return v_pos_952_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg___boxed(lean_object* v_pos_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_String_Pos_ofCopy___redArg(v_pos_953_);
lean_dec(v_pos_953_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy(lean_object* v_s_955_, lean_object* v_pos_956_){
_start:
{
lean_inc(v_pos_956_);
return v_pos_956_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___boxed(lean_object* v_s_957_, lean_object* v_pos_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_String_Pos_ofCopy(v_s_957_, v_pos_958_);
lean_dec(v_pos_958_);
lean_dec_ref(v_s_957_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg(lean_object* v_pos_960_){
_start:
{
lean_inc(v_pos_960_);
return v_pos_960_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg___boxed(lean_object* v_pos_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_String_Slice_Pos_copy___redArg(v_pos_961_);
lean_dec(v_pos_961_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy(lean_object* v_s_963_, lean_object* v_pos_964_){
_start:
{
lean_inc(v_pos_964_);
return v_pos_964_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___boxed(lean_object* v_s_965_, lean_object* v_pos_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_String_Slice_Pos_copy(v_s_965_, v_pos_966_);
lean_dec(v_pos_966_);
lean_dec_ref(v_s_965_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg(lean_object* v_pos_968_){
_start:
{
lean_inc(v_pos_968_);
return v_pos_968_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg___boxed(lean_object* v_pos_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_String_Slice_Pos_toCopy___redArg(v_pos_969_);
lean_dec(v_pos_969_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy(lean_object* v_s_971_, lean_object* v_pos_972_){
_start:
{
lean_inc(v_pos_972_);
return v_pos_972_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___boxed(lean_object* v_s_973_, lean_object* v_pos_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_String_Slice_Pos_toCopy(v_s_973_, v_pos_974_);
lean_dec(v_pos_974_);
lean_dec_ref(v_s_973_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg(lean_object* v_p_u2080_976_, lean_object* v_pos_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = lean_nat_add(v_p_u2080_976_, v_pos_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg___boxed(lean_object* v_p_u2080_979_, lean_object* v_pos_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_String_Slice_Pos_ofSliceFrom___redArg(v_p_u2080_979_, v_pos_980_);
lean_dec(v_pos_980_);
lean_dec(v_p_u2080_979_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom(lean_object* v_s_982_, lean_object* v_p_u2080_983_, lean_object* v_pos_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = lean_nat_add(v_p_u2080_983_, v_pos_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___boxed(lean_object* v_s_986_, lean_object* v_p_u2080_987_, lean_object* v_pos_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_String_Slice_Pos_ofSliceFrom(v_s_986_, v_p_u2080_987_, v_pos_988_);
lean_dec(v_pos_988_);
lean_dec(v_p_u2080_987_);
lean_dec_ref(v_s_986_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg(lean_object* v_p_u2080_990_, lean_object* v_pos_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = lean_nat_add(v_p_u2080_990_, v_pos_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg___boxed(lean_object* v_p_u2080_993_, lean_object* v_pos_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_String_Slice_Pos_ofReplaceStart___redArg(v_p_u2080_993_, v_pos_994_);
lean_dec(v_pos_994_);
lean_dec(v_p_u2080_993_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart(lean_object* v_s_996_, lean_object* v_p_u2080_997_, lean_object* v_pos_998_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = lean_nat_add(v_p_u2080_997_, v_pos_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___boxed(lean_object* v_s_1000_, lean_object* v_p_u2080_1001_, lean_object* v_pos_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_String_Slice_Pos_ofReplaceStart(v_s_1000_, v_p_u2080_1001_, v_pos_1002_);
lean_dec(v_pos_1002_);
lean_dec(v_p_u2080_1001_);
lean_dec_ref(v_s_1000_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg(lean_object* v_p_u2080_1004_, lean_object* v_pos_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_nat_sub(v_pos_1005_, v_p_u2080_1004_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg___boxed(lean_object* v_p_u2080_1007_, lean_object* v_pos_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_String_Slice_Pos_sliceFrom___redArg(v_p_u2080_1007_, v_pos_1008_);
lean_dec(v_pos_1008_);
lean_dec(v_p_u2080_1007_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom(lean_object* v_s_1010_, lean_object* v_p_u2080_1011_, lean_object* v_pos_1012_, lean_object* v_h_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_nat_sub(v_pos_1012_, v_p_u2080_1011_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___boxed(lean_object* v_s_1015_, lean_object* v_p_u2080_1016_, lean_object* v_pos_1017_, lean_object* v_h_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_String_Slice_Pos_sliceFrom(v_s_1015_, v_p_u2080_1016_, v_pos_1017_, v_h_1018_);
lean_dec(v_pos_1017_);
lean_dec(v_p_u2080_1016_);
lean_dec_ref(v_s_1015_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg(lean_object* v_p_u2080_1020_, lean_object* v_pos_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_nat_sub(v_pos_1021_, v_p_u2080_1020_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg___boxed(lean_object* v_p_u2080_1023_, lean_object* v_pos_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_String_Slice_Pos_toReplaceStart___redArg(v_p_u2080_1023_, v_pos_1024_);
lean_dec(v_pos_1024_);
lean_dec(v_p_u2080_1023_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart(lean_object* v_s_1026_, lean_object* v_p_u2080_1027_, lean_object* v_pos_1028_, lean_object* v_h_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_nat_sub(v_pos_1028_, v_p_u2080_1027_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___boxed(lean_object* v_s_1031_, lean_object* v_p_u2080_1032_, lean_object* v_pos_1033_, lean_object* v_h_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_String_Slice_Pos_toReplaceStart(v_s_1031_, v_p_u2080_1032_, v_pos_1033_, v_h_1034_);
lean_dec(v_pos_1033_);
lean_dec(v_p_u2080_1032_);
lean_dec_ref(v_s_1031_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg(lean_object* v_pos_1036_){
_start:
{
lean_inc(v_pos_1036_);
return v_pos_1036_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg___boxed(lean_object* v_pos_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_String_Slice_Pos_ofSliceTo___redArg(v_pos_1037_);
lean_dec(v_pos_1037_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo(lean_object* v_s_1039_, lean_object* v_p_u2080_1040_, lean_object* v_pos_1041_){
_start:
{
lean_inc(v_pos_1041_);
return v_pos_1041_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___boxed(lean_object* v_s_1042_, lean_object* v_p_u2080_1043_, lean_object* v_pos_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_String_Slice_Pos_ofSliceTo(v_s_1042_, v_p_u2080_1043_, v_pos_1044_);
lean_dec(v_pos_1044_);
lean_dec(v_p_u2080_1043_);
lean_dec_ref(v_s_1042_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg(lean_object* v_pos_1046_){
_start:
{
lean_inc(v_pos_1046_);
return v_pos_1046_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg___boxed(lean_object* v_pos_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_String_Slice_Pos_ofReplaceEnd___redArg(v_pos_1047_);
lean_dec(v_pos_1047_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd(lean_object* v_s_1049_, lean_object* v_p_u2080_1050_, lean_object* v_pos_1051_){
_start:
{
lean_inc(v_pos_1051_);
return v_pos_1051_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___boxed(lean_object* v_s_1052_, lean_object* v_p_u2080_1053_, lean_object* v_pos_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_String_Slice_Pos_ofReplaceEnd(v_s_1052_, v_p_u2080_1053_, v_pos_1054_);
lean_dec(v_pos_1054_);
lean_dec(v_p_u2080_1053_);
lean_dec_ref(v_s_1052_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg(lean_object* v_pos_1056_){
_start:
{
lean_inc(v_pos_1056_);
return v_pos_1056_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg___boxed(lean_object* v_pos_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_String_Slice_Pos_sliceTo___redArg(v_pos_1057_);
lean_dec(v_pos_1057_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo(lean_object* v_s_1059_, lean_object* v_p_u2080_1060_, lean_object* v_pos_1061_, lean_object* v_h_1062_){
_start:
{
lean_inc(v_pos_1061_);
return v_pos_1061_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___boxed(lean_object* v_s_1063_, lean_object* v_p_u2080_1064_, lean_object* v_pos_1065_, lean_object* v_h_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_String_Slice_Pos_sliceTo(v_s_1063_, v_p_u2080_1064_, v_pos_1065_, v_h_1066_);
lean_dec(v_pos_1065_);
lean_dec(v_p_u2080_1064_);
lean_dec_ref(v_s_1063_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg(lean_object* v_pos_1068_){
_start:
{
lean_inc(v_pos_1068_);
return v_pos_1068_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg___boxed(lean_object* v_pos_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_String_Slice_Pos_toReplaceEnd___redArg(v_pos_1069_);
lean_dec(v_pos_1069_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd(lean_object* v_s_1071_, lean_object* v_p_u2080_1072_, lean_object* v_pos_1073_, lean_object* v_h_1074_){
_start:
{
lean_inc(v_pos_1073_);
return v_pos_1073_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___boxed(lean_object* v_s_1075_, lean_object* v_p_u2080_1076_, lean_object* v_pos_1077_, lean_object* v_h_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_String_Slice_Pos_toReplaceEnd(v_s_1075_, v_p_u2080_1076_, v_pos_1077_, v_h_1078_);
lean_dec(v_pos_1077_);
lean_dec(v_p_u2080_1076_);
lean_dec_ref(v_s_1075_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg(lean_object* v_s_1080_, lean_object* v_pos_1081_){
_start:
{
lean_object* v_str_1082_; lean_object* v_startInclusive_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; uint8_t v___x_1086_; uint8_t v___x_1087_; uint8_t v___x_1088_; uint8_t v___x_1089_; 
v_str_1082_ = lean_ctor_get(v_s_1080_, 0);
v_startInclusive_1083_ = lean_ctor_get(v_s_1080_, 1);
v___x_1084_ = lean_nat_add(v_startInclusive_1083_, v_pos_1081_);
v___x_1085_ = lean_string_get_byte_fast(v_str_1082_, v___x_1084_);
v___x_1086_ = 128;
v___x_1087_ = lean_uint8_land(v___x_1085_, v___x_1086_);
v___x_1088_ = 0;
v___x_1089_ = lean_uint8_dec_eq(v___x_1087_, v___x_1088_);
if (v___x_1089_ == 0)
{
uint8_t v___x_1090_; uint8_t v___x_1091_; uint8_t v___x_1092_; uint8_t v___x_1093_; 
v___x_1090_ = 224;
v___x_1091_ = lean_uint8_land(v___x_1085_, v___x_1090_);
v___x_1092_ = 192;
v___x_1093_ = lean_uint8_dec_eq(v___x_1091_, v___x_1092_);
if (v___x_1093_ == 0)
{
uint8_t v___x_1094_; uint8_t v___x_1095_; uint8_t v___x_1096_; 
v___x_1094_ = 240;
v___x_1095_ = lean_uint8_land(v___x_1085_, v___x_1094_);
v___x_1096_ = lean_uint8_dec_eq(v___x_1095_, v___x_1090_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = lean_unsigned_to_nat(4u);
v___x_1098_ = lean_nat_add(v_pos_1081_, v___x_1097_);
return v___x_1098_;
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = lean_unsigned_to_nat(3u);
v___x_1100_ = lean_nat_add(v_pos_1081_, v___x_1099_);
return v___x_1100_;
}
}
else
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_unsigned_to_nat(2u);
v___x_1102_ = lean_nat_add(v_pos_1081_, v___x_1101_);
return v___x_1102_;
}
}
else
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = lean_unsigned_to_nat(1u);
v___x_1104_ = lean_nat_add(v_pos_1081_, v___x_1103_);
return v___x_1104_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg___boxed(lean_object* v_s_1105_, lean_object* v_pos_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_String_Slice_Pos_next___redArg(v_s_1105_, v_pos_1106_);
lean_dec(v_pos_1106_);
lean_dec_ref(v_s_1105_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next(lean_object* v_s_1108_, lean_object* v_pos_1109_, lean_object* v_h_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_String_Slice_Pos_next___redArg(v_s_1108_, v_pos_1109_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___boxed(lean_object* v_s_1112_, lean_object* v_pos_1113_, lean_object* v_h_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_String_Slice_Pos_next(v_s_1112_, v_pos_1113_, v_h_1114_);
lean_dec(v_pos_1113_);
lean_dec_ref(v_s_1112_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f(lean_object* v_s_1116_, lean_object* v_pos_1117_){
_start:
{
lean_object* v_startInclusive_1118_; lean_object* v_endExclusive_1119_; lean_object* v___x_1120_; uint8_t v_decide_1121_; 
v_startInclusive_1118_ = lean_ctor_get(v_s_1116_, 1);
v_endExclusive_1119_ = lean_ctor_get(v_s_1116_, 2);
v___x_1120_ = lean_nat_sub(v_endExclusive_1119_, v_startInclusive_1118_);
v_decide_1121_ = lean_nat_dec_eq(v_pos_1117_, v___x_1120_);
lean_dec(v___x_1120_);
if (v_decide_1121_ == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = l_String_Slice_Pos_next___redArg(v_s_1116_, v_pos_1117_);
v___x_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
return v___x_1123_;
}
else
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_box(0);
return v___x_1124_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f___boxed(lean_object* v_s_1125_, lean_object* v_pos_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_String_Slice_Pos_next_x3f(v_s_1125_, v_pos_1126_);
lean_dec(v_pos_1126_);
lean_dec_ref(v_s_1125_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(lean_object* v_msg_1128_){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_unsigned_to_nat(0u);
v___x_1130_ = lean_panic_fn_borrowed(v___x_1129_, v_msg_1128_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0(lean_object* v_s_1131_, lean_object* v_msg_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v_msg_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___boxed(lean_object* v_s_1134_, lean_object* v_msg_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0(v_s_1134_, v_msg_1135_);
lean_dec_ref(v_s_1134_);
return v_res_1136_;
}
}
static lean_object* _init_l_String_Slice_Pos_next_x21___closed__2(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1139_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__1));
v___x_1140_ = lean_unsigned_to_nat(29u);
v___x_1141_ = lean_unsigned_to_nat(1510u);
v___x_1142_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__0));
v___x_1143_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1144_ = l_mkPanicMessageWithDecl(v___x_1143_, v___x_1142_, v___x_1141_, v___x_1140_, v___x_1139_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21(lean_object* v_s_1145_, lean_object* v_pos_1146_){
_start:
{
lean_object* v_startInclusive_1147_; lean_object* v_endExclusive_1148_; lean_object* v___x_1149_; uint8_t v_decide_1150_; 
v_startInclusive_1147_ = lean_ctor_get(v_s_1145_, 1);
v_endExclusive_1148_ = lean_ctor_get(v_s_1145_, 2);
v___x_1149_ = lean_nat_sub(v_endExclusive_1148_, v_startInclusive_1147_);
v_decide_1150_ = lean_nat_dec_eq(v_pos_1146_, v___x_1149_);
lean_dec(v___x_1149_);
if (v_decide_1150_ == 0)
{
lean_object* v___x_1151_; 
v___x_1151_ = l_String_Slice_Pos_next___redArg(v_s_1145_, v_pos_1146_);
return v___x_1151_;
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_obj_once(&l_String_Slice_Pos_next_x21___closed__2, &l_String_Slice_Pos_next_x21___closed__2_once, _init_l_String_Slice_Pos_next_x21___closed__2);
v___x_1153_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_1152_);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21___boxed(lean_object* v_s_1154_, lean_object* v_pos_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_String_Slice_Pos_next_x21(v_s_1154_, v_pos_1155_);
lean_dec(v_pos_1155_);
lean_dec_ref(v_s_1154_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg(lean_object* v_s_1157_, lean_object* v_off_1158_){
_start:
{
lean_object* v_str_1159_; lean_object* v_startInclusive_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; uint8_t v___x_1163_; uint8_t v___x_1164_; uint8_t v___x_1165_; uint8_t v___x_1166_; 
v_str_1159_ = lean_ctor_get(v_s_1157_, 0);
v_startInclusive_1160_ = lean_ctor_get(v_s_1157_, 1);
v___x_1161_ = lean_nat_add(v_startInclusive_1160_, v_off_1158_);
v___x_1162_ = lean_string_get_byte_fast(v_str_1159_, v___x_1161_);
v___x_1163_ = 128;
v___x_1164_ = lean_uint8_land(v___x_1162_, v___x_1163_);
v___x_1165_ = 0;
v___x_1166_ = lean_uint8_dec_eq(v___x_1164_, v___x_1165_);
if (v___x_1166_ == 0)
{
uint8_t v___x_1167_; uint8_t v___x_1168_; uint8_t v___x_1169_; uint8_t v___x_1170_; 
v___x_1167_ = 224;
v___x_1168_ = lean_uint8_land(v___x_1162_, v___x_1167_);
v___x_1169_ = 192;
v___x_1170_ = lean_uint8_dec_eq(v___x_1168_, v___x_1169_);
if (v___x_1170_ == 0)
{
uint8_t v___x_1171_; uint8_t v___x_1172_; uint8_t v___x_1173_; 
v___x_1171_ = 240;
v___x_1172_ = lean_uint8_land(v___x_1162_, v___x_1171_);
v___x_1173_ = lean_uint8_dec_eq(v___x_1172_, v___x_1167_);
if (v___x_1173_ == 0)
{
uint8_t v___x_1174_; uint8_t v___x_1175_; uint8_t v___x_1176_; 
v___x_1174_ = 248;
v___x_1175_ = lean_uint8_land(v___x_1162_, v___x_1174_);
v___x_1176_ = lean_uint8_dec_eq(v___x_1175_, v___x_1171_);
if (v___x_1176_ == 0)
{
lean_object* v_zero_1177_; uint8_t v_isZero_1178_; lean_object* v_one_1179_; lean_object* v_n_1180_; 
v_zero_1177_ = lean_unsigned_to_nat(0u);
v_isZero_1178_ = lean_nat_dec_eq(v_off_1158_, v_zero_1177_);
v_one_1179_ = lean_unsigned_to_nat(1u);
v_n_1180_ = lean_nat_sub(v_off_1158_, v_one_1179_);
lean_dec(v_off_1158_);
v_off_1158_ = v_n_1180_;
goto _start;
}
else
{
return v_off_1158_;
}
}
else
{
return v_off_1158_;
}
}
else
{
return v_off_1158_;
}
}
else
{
return v_off_1158_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg___boxed(lean_object* v_s_1182_, lean_object* v_off_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1182_, v_off_1183_);
lean_dec_ref(v_s_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go(lean_object* v_s_1185_, lean_object* v_off_1186_, lean_object* v_h_u2081_1187_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1185_, v_off_1186_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___boxed(lean_object* v_s_1189_, lean_object* v_off_1190_, lean_object* v_h_u2081_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_String_Slice_Pos_prevAux_go(v_s_1189_, v_off_1190_, v_h_u2081_1191_);
lean_dec_ref(v_s_1189_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg(lean_object* v_s_1193_, lean_object* v_pos_1194_){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = lean_unsigned_to_nat(1u);
v___x_1196_ = lean_nat_sub(v_pos_1194_, v___x_1195_);
v___x_1197_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1193_, v___x_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg___boxed(lean_object* v_s_1198_, lean_object* v_pos_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_String_Slice_Pos_prevAux___redArg(v_s_1198_, v_pos_1199_);
lean_dec(v_pos_1199_);
lean_dec_ref(v_s_1198_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux(lean_object* v_s_1201_, lean_object* v_pos_1202_, lean_object* v_h_1203_){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1204_ = lean_unsigned_to_nat(1u);
v___x_1205_ = lean_nat_sub(v_pos_1202_, v___x_1204_);
v___x_1206_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1201_, v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___boxed(lean_object* v_s_1207_, lean_object* v_pos_1208_, lean_object* v_h_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_String_Slice_Pos_prevAux(v_s_1207_, v_pos_1208_, v_h_1209_);
lean_dec(v_pos_1208_);
lean_dec_ref(v_s_1207_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(lean_object* v_off_1211_, lean_object* v_h__1_1212_, lean_object* v_h__2_1213_){
_start:
{
lean_object* v_zero_1214_; uint8_t v_isZero_1215_; 
v_zero_1214_ = lean_unsigned_to_nat(0u);
v_isZero_1215_ = lean_nat_dec_eq(v_off_1211_, v_zero_1214_);
if (v_isZero_1215_ == 1)
{
lean_object* v___x_1216_; 
lean_dec(v_h__2_1213_);
v___x_1216_ = lean_apply_3(v_h__1_1212_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1216_;
}
else
{
lean_object* v_one_1217_; lean_object* v_n_1218_; lean_object* v___x_1219_; 
lean_dec(v_h__1_1212_);
v_one_1217_ = lean_unsigned_to_nat(1u);
v_n_1218_ = lean_nat_sub(v_off_1211_, v_one_1217_);
v___x_1219_ = lean_apply_4(v_h__2_1213_, v_n_1218_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1219_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg___boxed(lean_object* v_off_1220_, lean_object* v_h__1_1221_, lean_object* v_h__2_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(v_off_1220_, v_h__1_1221_, v_h__2_1222_);
lean_dec(v_off_1220_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(lean_object* v_s_1224_, lean_object* v_motive_1225_, lean_object* v_off_1226_, lean_object* v_h_u2081_1227_, lean_object* v_hbyte_1228_, lean_object* v_this_1229_, lean_object* v_h__1_1230_, lean_object* v_h__2_1231_){
_start:
{
lean_object* v_zero_1232_; uint8_t v_isZero_1233_; 
v_zero_1232_ = lean_unsigned_to_nat(0u);
v_isZero_1233_ = lean_nat_dec_eq(v_off_1226_, v_zero_1232_);
if (v_isZero_1233_ == 1)
{
lean_object* v___x_1234_; 
lean_dec(v_h__2_1231_);
v___x_1234_ = lean_apply_3(v_h__1_1230_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1234_;
}
else
{
lean_object* v_one_1235_; lean_object* v_n_1236_; lean_object* v___x_1237_; 
lean_dec(v_h__1_1230_);
v_one_1235_ = lean_unsigned_to_nat(1u);
v_n_1236_ = lean_nat_sub(v_off_1226_, v_one_1235_);
v___x_1237_ = lean_apply_4(v_h__2_1231_, v_n_1236_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___boxed(lean_object* v_s_1238_, lean_object* v_motive_1239_, lean_object* v_off_1240_, lean_object* v_h_u2081_1241_, lean_object* v_hbyte_1242_, lean_object* v_this_1243_, lean_object* v_h__1_1244_, lean_object* v_h__2_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(v_s_1238_, v_motive_1239_, v_off_1240_, v_h_u2081_1241_, v_hbyte_1242_, v_this_1243_, v_h__1_1244_, v_h__2_1245_);
lean_dec(v_off_1240_);
lean_dec_ref(v_s_1238_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg(lean_object* v_off_1247_){
_start:
{
lean_inc(v_off_1247_);
return v_off_1247_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg___boxed(lean_object* v_off_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_String_Slice_pos___redArg(v_off_1248_);
lean_dec(v_off_1248_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos(lean_object* v_s_1250_, lean_object* v_off_1251_, lean_object* v_h_1252_){
_start:
{
lean_inc(v_off_1251_);
return v_off_1251_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___boxed(lean_object* v_s_1253_, lean_object* v_off_1254_, lean_object* v_h_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_String_Slice_pos(v_s_1253_, v_off_1254_, v_h_1255_);
lean_dec(v_off_1254_);
lean_dec_ref(v_s_1253_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f(lean_object* v_s_1257_, lean_object* v_off_1258_){
_start:
{
uint8_t v___x_1259_; 
v___x_1259_ = l_String_Pos_Raw_isValidForSlice(v_s_1257_, v_off_1258_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; 
lean_dec(v_off_1258_);
v___x_1260_ = lean_box(0);
return v___x_1260_;
}
else
{
lean_object* v___x_1261_; 
v___x_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1261_, 0, v_off_1258_);
return v___x_1261_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f___boxed(lean_object* v_s_1262_, lean_object* v_off_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_String_Slice_pos_x3f(v_s_1262_, v_off_1263_);
lean_dec_ref(v_s_1262_);
return v_res_1264_;
}
}
static lean_object* _init_l_String_Slice_pos_x21___closed__2(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1267_ = ((lean_object*)(l_String_Slice_pos_x21___closed__1));
v___x_1268_ = lean_unsigned_to_nat(4u);
v___x_1269_ = lean_unsigned_to_nat(1598u);
v___x_1270_ = ((lean_object*)(l_String_Slice_pos_x21___closed__0));
v___x_1271_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1272_ = l_mkPanicMessageWithDecl(v___x_1271_, v___x_1270_, v___x_1269_, v___x_1268_, v___x_1267_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21(lean_object* v_s_1273_, lean_object* v_off_1274_){
_start:
{
uint8_t v___x_1275_; 
v___x_1275_ = l_String_Pos_Raw_isValidForSlice(v_s_1273_, v_off_1274_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = lean_obj_once(&l_String_Slice_pos_x21___closed__2, &l_String_Slice_pos_x21___closed__2_once, _init_l_String_Slice_pos_x21___closed__2);
v___x_1277_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_1276_);
return v___x_1277_;
}
else
{
lean_inc(v_off_1274_);
return v_off_1274_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21___boxed(lean_object* v_s_1278_, lean_object* v_off_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_String_Slice_pos_x21(v_s_1278_, v_off_1279_);
lean_dec(v_off_1279_);
lean_dec_ref(v_s_1278_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next___boxed(lean_object* v_s_1284_, lean_object* v_pos_1285_, lean_object* v_h_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = lean_string_utf8_next_fast(v_s_1284_, v_pos_1285_);
lean_dec(v_pos_1285_);
lean_dec_ref(v_s_1284_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x3f(lean_object* v_s_1288_, lean_object* v_pos_1289_){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1290_ = lean_unsigned_to_nat(0u);
v___x_1291_ = lean_string_utf8_byte_size(v_s_1288_);
v___x_1292_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1292_, 0, v_s_1288_);
lean_ctor_set(v___x_1292_, 1, v___x_1290_);
lean_ctor_set(v___x_1292_, 2, v___x_1291_);
v___x_1293_ = l_String_Slice_Pos_next_x3f(v___x_1292_, v_pos_1289_);
lean_dec_ref_known(v___x_1292_, 3);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_box(0);
return v___x_1294_;
}
else
{
lean_object* v_val_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
v_val_1295_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1293_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_val_1295_);
lean_dec(v___x_1293_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_val_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x3f___boxed(lean_object* v_s_1303_, lean_object* v_pos_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_String_Pos_next_x3f(v_s_1303_, v_pos_1304_);
lean_dec(v_pos_1304_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21(lean_object* v_s_1306_, lean_object* v_pos_1307_){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = lean_string_utf8_byte_size(v_s_1306_);
v___x_1310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1310_, 0, v_s_1306_);
lean_ctor_set(v___x_1310_, 1, v___x_1308_);
lean_ctor_set(v___x_1310_, 2, v___x_1309_);
v___x_1311_ = l_String_Slice_Pos_next_x21(v___x_1310_, v_pos_1307_);
lean_dec_ref_known(v___x_1310_, 3);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21___boxed(lean_object* v_s_1312_, lean_object* v_pos_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_String_Pos_next_x21(v_s_1312_, v_pos_1313_);
lean_dec(v_pos_1313_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg(lean_object* v_off_1315_){
_start:
{
lean_inc(v_off_1315_);
return v_off_1315_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg___boxed(lean_object* v_off_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_String_pos___redArg(v_off_1316_);
lean_dec(v_off_1316_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_String_pos(lean_object* v_s_1318_, lean_object* v_off_1319_, lean_object* v_h_1320_){
_start:
{
lean_inc(v_off_1319_);
return v_off_1319_;
}
}
LEAN_EXPORT lean_object* l_String_pos___boxed(lean_object* v_s_1321_, lean_object* v_off_1322_, lean_object* v_h_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_String_pos(v_s_1321_, v_off_1322_, v_h_1323_);
lean_dec(v_off_1322_);
lean_dec_ref(v_s_1321_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x3f(lean_object* v_s_1325_, lean_object* v_off_1326_){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1327_ = lean_unsigned_to_nat(0u);
v___x_1328_ = lean_string_utf8_byte_size(v_s_1325_);
v___x_1329_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1329_, 0, v_s_1325_);
lean_ctor_set(v___x_1329_, 1, v___x_1327_);
lean_ctor_set(v___x_1329_, 2, v___x_1328_);
v___x_1330_ = l_String_Slice_pos_x3f(v___x_1329_, v_off_1326_);
lean_dec_ref_known(v___x_1329_, 3);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v___x_1331_; 
v___x_1331_ = lean_box(0);
return v___x_1331_;
}
else
{
lean_object* v_val_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
v_val_1332_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1330_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_val_1332_);
lean_dec(v___x_1330_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_val_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_pos_x21(lean_object* v_s_1340_, lean_object* v_off_1341_){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1342_ = lean_unsigned_to_nat(0u);
v___x_1343_ = lean_string_utf8_byte_size(v_s_1340_);
v___x_1344_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1344_, 0, v_s_1340_);
lean_ctor_set(v___x_1344_, 1, v___x_1342_);
lean_ctor_set(v___x_1344_, 2, v___x_1343_);
v___x_1345_ = l_String_Slice_pos_x21(v___x_1344_, v_off_1341_);
lean_dec_ref_known(v___x_1344_, 3);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x21___boxed(lean_object* v_s_1346_, lean_object* v_off_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_String_pos_x21(v_s_1346_, v_off_1347_);
lean_dec(v_off_1347_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg(lean_object* v_pos_1349_){
_start:
{
lean_inc(v_pos_1349_);
return v_pos_1349_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg___boxed(lean_object* v_pos_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_String_Slice_Pos_cast___redArg(v_pos_1350_);
lean_dec(v_pos_1350_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast(lean_object* v_s_1352_, lean_object* v_t_1353_, lean_object* v_pos_1354_, lean_object* v_h_1355_){
_start:
{
lean_inc(v_pos_1354_);
return v_pos_1354_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___boxed(lean_object* v_s_1356_, lean_object* v_t_1357_, lean_object* v_pos_1358_, lean_object* v_h_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_String_Slice_Pos_cast(v_s_1356_, v_t_1357_, v_pos_1358_, v_h_1359_);
lean_dec(v_pos_1358_);
lean_dec_ref(v_t_1357_);
lean_dec_ref(v_s_1356_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg(lean_object* v_pos_1361_){
_start:
{
lean_inc(v_pos_1361_);
return v_pos_1361_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg___boxed(lean_object* v_pos_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_String_Pos_cast___redArg(v_pos_1362_);
lean_dec(v_pos_1362_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast(lean_object* v_s_1364_, lean_object* v_t_1365_, lean_object* v_pos_1366_, lean_object* v_h_1367_){
_start:
{
lean_inc(v_pos_1366_);
return v_pos_1366_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___boxed(lean_object* v_s_1368_, lean_object* v_t_1369_, lean_object* v_pos_1370_, lean_object* v_h_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_String_Pos_cast(v_s_1368_, v_t_1369_, v_pos_1370_, v_h_1371_);
lean_dec(v_pos_1370_);
lean_dec_ref(v_t_1369_);
lean_dec_ref(v_s_1368_);
return v_res_1372_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_Raw_utf8GetAux(lean_object* v_x_1373_, lean_object* v_x_1374_, lean_object* v_x_1375_){
_start:
{
if (lean_obj_tag(v_x_1373_) == 0)
{
uint32_t v___x_1376_; 
lean_dec(v_x_1374_);
v___x_1376_ = 65;
return v___x_1376_;
}
else
{
lean_object* v_head_1377_; lean_object* v_tail_1378_; lean_object* v___y_1380_; uint8_t v_decide_1383_; 
v_head_1377_ = lean_ctor_get(v_x_1373_, 0);
v_tail_1378_ = lean_ctor_get(v_x_1373_, 1);
v_decide_1383_ = lean_nat_dec_eq(v_x_1374_, v_x_1375_);
if (v_decide_1383_ == 0)
{
uint32_t v___x_1384_; uint32_t v___x_1385_; uint8_t v___x_1386_; 
v___x_1384_ = 127;
v___x_1385_ = lean_unbox_uint32(v_head_1377_);
v___x_1386_ = lean_uint32_dec_le(v___x_1385_, v___x_1384_);
if (v___x_1386_ == 0)
{
uint32_t v___x_1387_; uint32_t v___x_1388_; uint8_t v___x_1389_; 
v___x_1387_ = 2047;
v___x_1388_ = lean_unbox_uint32(v_head_1377_);
v___x_1389_ = lean_uint32_dec_le(v___x_1388_, v___x_1387_);
if (v___x_1389_ == 0)
{
uint32_t v___x_1390_; uint32_t v___x_1391_; uint8_t v___x_1392_; 
v___x_1390_ = 65535;
v___x_1391_ = lean_unbox_uint32(v_head_1377_);
v___x_1392_ = lean_uint32_dec_le(v___x_1391_, v___x_1390_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_unsigned_to_nat(4u);
v___y_1380_ = v___x_1393_;
goto v___jp_1379_;
}
else
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_unsigned_to_nat(3u);
v___y_1380_ = v___x_1394_;
goto v___jp_1379_;
}
}
else
{
lean_object* v___x_1395_; 
v___x_1395_ = lean_unsigned_to_nat(2u);
v___y_1380_ = v___x_1395_;
goto v___jp_1379_;
}
}
else
{
lean_object* v___x_1396_; 
v___x_1396_ = lean_unsigned_to_nat(1u);
v___y_1380_ = v___x_1396_;
goto v___jp_1379_;
}
}
else
{
uint32_t v___x_1397_; 
lean_dec(v_x_1374_);
v___x_1397_ = lean_unbox_uint32(v_head_1377_);
return v___x_1397_;
}
v___jp_1379_:
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_nat_add(v_x_1374_, v___y_1380_);
lean_dec(v_x_1374_);
v_x_1373_ = v_tail_1378_;
v_x_1374_ = v___x_1381_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux___boxed(lean_object* v_x_1398_, lean_object* v_x_1399_, lean_object* v_x_1400_){
_start:
{
uint32_t v_res_1401_; lean_object* v_r_1402_; 
v_res_1401_ = l_String_Pos_Raw_utf8GetAux(v_x_1398_, v_x_1399_, v_x_1400_);
lean_dec(v_x_1400_);
lean_dec(v_x_1398_);
v_r_1402_ = lean_box_uint32(v_res_1401_);
return v_r_1402_;
}
}
LEAN_EXPORT uint32_t l_String_utf8GetAux(lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_){
_start:
{
uint32_t v___x_1406_; 
v___x_1406_ = l_String_Pos_Raw_utf8GetAux(v_a_1403_, v_a_1404_, v_a_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux___boxed(lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
uint32_t v_res_1410_; lean_object* v_r_1411_; 
v_res_1410_ = l_String_utf8GetAux(v_a_1407_, v_a_1408_, v_a_1409_);
lean_dec(v_a_1409_);
lean_dec(v_a_1407_);
v_r_1411_ = lean_box_uint32(v_res_1410_);
return v_r_1411_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get___boxed(lean_object* v_s_1414_, lean_object* v_p_1415_){
_start:
{
uint32_t v_res_1416_; lean_object* v_r_1417_; 
v_res_1416_ = lean_string_utf8_get(v_s_1414_, v_p_1415_);
lean_dec(v_p_1415_);
lean_dec_ref(v_s_1414_);
v_r_1417_ = lean_box_uint32(v_res_1416_);
return v_r_1417_;
}
}
LEAN_EXPORT lean_object* l_String_get___boxed(lean_object* v_s_1420_, lean_object* v_p_1421_){
_start:
{
uint32_t v_res_1422_; lean_object* v_r_1423_; 
v_res_1422_ = lean_string_utf8_get(v_s_1420_, v_p_1421_);
lean_dec(v_p_1421_);
lean_dec_ref(v_s_1420_);
v_r_1423_ = lean_box_uint32(v_res_1422_);
return v_r_1423_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f(lean_object* v_x_1424_, lean_object* v_x_1425_, lean_object* v_x_1426_){
_start:
{
if (lean_obj_tag(v_x_1424_) == 0)
{
lean_object* v___x_1427_; 
lean_dec(v_x_1425_);
v___x_1427_ = lean_box(0);
return v___x_1427_;
}
else
{
lean_object* v_head_1428_; lean_object* v_tail_1429_; lean_object* v___y_1431_; uint8_t v_decide_1434_; 
v_head_1428_ = lean_ctor_get(v_x_1424_, 0);
v_tail_1429_ = lean_ctor_get(v_x_1424_, 1);
v_decide_1434_ = lean_nat_dec_eq(v_x_1425_, v_x_1426_);
if (v_decide_1434_ == 0)
{
uint32_t v___x_1435_; uint32_t v___x_1436_; uint8_t v___x_1437_; 
v___x_1435_ = 127;
v___x_1436_ = lean_unbox_uint32(v_head_1428_);
v___x_1437_ = lean_uint32_dec_le(v___x_1436_, v___x_1435_);
if (v___x_1437_ == 0)
{
uint32_t v___x_1438_; uint32_t v___x_1439_; uint8_t v___x_1440_; 
v___x_1438_ = 2047;
v___x_1439_ = lean_unbox_uint32(v_head_1428_);
v___x_1440_ = lean_uint32_dec_le(v___x_1439_, v___x_1438_);
if (v___x_1440_ == 0)
{
uint32_t v___x_1441_; uint32_t v___x_1442_; uint8_t v___x_1443_; 
v___x_1441_ = 65535;
v___x_1442_ = lean_unbox_uint32(v_head_1428_);
v___x_1443_ = lean_uint32_dec_le(v___x_1442_, v___x_1441_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_unsigned_to_nat(4u);
v___y_1431_ = v___x_1444_;
goto v___jp_1430_;
}
else
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_unsigned_to_nat(3u);
v___y_1431_ = v___x_1445_;
goto v___jp_1430_;
}
}
else
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_unsigned_to_nat(2u);
v___y_1431_ = v___x_1446_;
goto v___jp_1430_;
}
}
else
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_unsigned_to_nat(1u);
v___y_1431_ = v___x_1447_;
goto v___jp_1430_;
}
}
else
{
lean_object* v___x_1448_; 
lean_dec(v_x_1425_);
lean_inc(v_head_1428_);
v___x_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1448_, 0, v_head_1428_);
return v___x_1448_;
}
v___jp_1430_:
{
lean_object* v___x_1432_; 
v___x_1432_ = lean_nat_add(v_x_1425_, v___y_1431_);
lean_dec(v_x_1425_);
v_x_1424_ = v_tail_1429_;
v_x_1425_ = v___x_1432_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f___boxed(lean_object* v_x_1449_, lean_object* v_x_1450_, lean_object* v_x_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_String_Pos_Raw_utf8GetAux_x3f(v_x_1449_, v_x_1450_, v_x_1451_);
lean_dec(v_x_1451_);
lean_dec(v_x_1449_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f(lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_String_Pos_Raw_utf8GetAux_x3f(v_a_1453_, v_a_1454_, v_a_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f___boxed(lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_String_utf8GetAux_x3f(v_a_1457_, v_a_1458_, v_a_1459_);
lean_dec(v_a_1459_);
lean_dec(v_a_1457_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1463_, lean_object* v_a_00___x40___internal___hyg_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1463_, v_a_00___x40___internal___hyg_1464_);
lean_dec(v_a_00___x40___internal___hyg_1464_);
lean_dec_ref(v_a_00___x40___internal___hyg_1463_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_String_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1468_, lean_object* v_a_00___x40___internal___hyg_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1468_, v_a_00___x40___internal___hyg_1469_);
lean_dec(v_a_00___x40___internal___hyg_1469_);
lean_dec_ref(v_a_00___x40___internal___hyg_1468_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x21___boxed(lean_object* v_s_1473_, lean_object* v_p_1474_){
_start:
{
uint32_t v_res_1475_; lean_object* v_r_1476_; 
v_res_1475_ = lean_string_utf8_get_bang(v_s_1473_, v_p_1474_);
lean_dec(v_p_1474_);
lean_dec_ref(v_s_1473_);
v_r_1476_ = lean_box_uint32(v_res_1475_);
return v_r_1476_;
}
}
LEAN_EXPORT lean_object* l_String_get_x21___boxed(lean_object* v_s_1479_, lean_object* v_p_1480_){
_start:
{
uint32_t v_res_1481_; lean_object* v_r_1482_; 
v_res_1481_ = lean_string_utf8_get_bang(v_s_1479_, v_p_1480_);
lean_dec(v_p_1480_);
lean_dec_ref(v_s_1479_);
v_r_1482_ = lean_box_uint32(v_res_1481_);
return v_r_1482_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux(uint32_t v_c_x27_1483_, lean_object* v_x_1484_, lean_object* v_x_1485_, lean_object* v_x_1486_){
_start:
{
if (lean_obj_tag(v_x_1484_) == 0)
{
return v_x_1484_;
}
else
{
lean_object* v_head_1487_; lean_object* v_tail_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1515_; 
v_head_1487_ = lean_ctor_get(v_x_1484_, 0);
v_tail_1488_ = lean_ctor_get(v_x_1484_, 1);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_x_1484_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1490_ = v_x_1484_;
v_isShared_1491_ = v_isSharedCheck_1515_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_tail_1488_);
lean_inc(v_head_1487_);
lean_dec(v_x_1484_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1515_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___y_1493_; uint8_t v_decide_1499_; 
v_decide_1499_ = lean_nat_dec_eq(v_x_1485_, v_x_1486_);
if (v_decide_1499_ == 0)
{
uint32_t v___x_1500_; uint32_t v___x_1501_; uint8_t v___x_1502_; 
v___x_1500_ = 127;
v___x_1501_ = lean_unbox_uint32(v_head_1487_);
v___x_1502_ = lean_uint32_dec_le(v___x_1501_, v___x_1500_);
if (v___x_1502_ == 0)
{
uint32_t v___x_1503_; uint32_t v___x_1504_; uint8_t v___x_1505_; 
v___x_1503_ = 2047;
v___x_1504_ = lean_unbox_uint32(v_head_1487_);
v___x_1505_ = lean_uint32_dec_le(v___x_1504_, v___x_1503_);
if (v___x_1505_ == 0)
{
uint32_t v___x_1506_; uint32_t v___x_1507_; uint8_t v___x_1508_; 
v___x_1506_ = 65535;
v___x_1507_ = lean_unbox_uint32(v_head_1487_);
v___x_1508_ = lean_uint32_dec_le(v___x_1507_, v___x_1506_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_unsigned_to_nat(4u);
v___y_1493_ = v___x_1509_;
goto v___jp_1492_;
}
else
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_unsigned_to_nat(3u);
v___y_1493_ = v___x_1510_;
goto v___jp_1492_;
}
}
else
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_unsigned_to_nat(2u);
v___y_1493_ = v___x_1511_;
goto v___jp_1492_;
}
}
else
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_unsigned_to_nat(1u);
v___y_1493_ = v___x_1512_;
goto v___jp_1492_;
}
}
else
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_del_object(v___x_1490_);
lean_dec(v_head_1487_);
v___x_1513_ = lean_box_uint32(v_c_x27_1483_);
v___x_1514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
lean_ctor_set(v___x_1514_, 1, v_tail_1488_);
return v___x_1514_;
}
v___jp_1492_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1494_ = lean_nat_add(v_x_1485_, v___y_1493_);
v___x_1495_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1483_, v_tail_1488_, v___x_1494_, v_x_1486_);
lean_dec(v___x_1494_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v___x_1495_);
v___x_1497_ = v___x_1490_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_head_1487_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux___boxed(lean_object* v_c_x27_1516_, lean_object* v_x_1517_, lean_object* v_x_1518_, lean_object* v_x_1519_){
_start:
{
uint32_t v_c_x27_boxed_1520_; lean_object* v_res_1521_; 
v_c_x27_boxed_1520_ = lean_unbox_uint32(v_c_x27_1516_);
lean_dec(v_c_x27_1516_);
v_res_1521_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_boxed_1520_, v_x_1517_, v_x_1518_, v_x_1519_);
lean_dec(v_x_1519_);
lean_dec(v_x_1518_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux(uint32_t v_c_x27_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux___boxed(lean_object* v_c_x27_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
uint32_t v_c_x27_boxed_1531_; lean_object* v_res_1532_; 
v_c_x27_boxed_1531_ = lean_unbox_uint32(v_c_x27_1527_);
lean_dec(v_c_x27_1527_);
v_res_1532_ = l_String_utf8SetAux(v_c_x27_boxed_1531_, v_a_1528_, v_a_1529_, v_a_1530_);
lean_dec(v_a_1530_);
lean_dec(v_a_1529_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg(lean_object* v_s_1533_, lean_object* v_pos_1534_){
_start:
{
lean_object* v_str_1535_; lean_object* v_startInclusive_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v_str_1535_ = lean_ctor_get(v_s_1533_, 0);
v_startInclusive_1536_ = lean_ctor_get(v_s_1533_, 1);
v___x_1537_ = lean_nat_add(v_startInclusive_1536_, v_pos_1534_);
v___x_1538_ = lean_string_utf8_next_fast(v_str_1535_, v___x_1537_);
lean_dec(v___x_1537_);
v___x_1539_ = lean_nat_sub(v___x_1538_, v_startInclusive_1536_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg___boxed(lean_object* v_s_1540_, lean_object* v_pos_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_String_Slice_Pos_nextFast___redArg(v_s_1540_, v_pos_1541_);
lean_dec(v_pos_1541_);
lean_dec_ref(v_s_1540_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast(lean_object* v_s_1543_, lean_object* v_pos_1544_, lean_object* v_h_1545_){
_start:
{
lean_object* v_str_1546_; lean_object* v_startInclusive_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v_str_1546_ = lean_ctor_get(v_s_1543_, 0);
v_startInclusive_1547_ = lean_ctor_get(v_s_1543_, 1);
v___x_1548_ = lean_nat_add(v_startInclusive_1547_, v_pos_1544_);
v___x_1549_ = lean_string_utf8_next_fast(v_str_1546_, v___x_1548_);
lean_dec(v___x_1548_);
v___x_1550_ = lean_nat_sub(v___x_1549_, v_startInclusive_1547_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___boxed(lean_object* v_s_1551_, lean_object* v_pos_1552_, lean_object* v_h_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_String_Slice_Pos_nextFast(v_s_1551_, v_pos_1552_, v_h_1553_);
lean_dec(v_pos_1552_);
lean_dec_ref(v_s_1551_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_String_sliceTo(lean_object* v_s_1555_, lean_object* v_p_1556_){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = lean_unsigned_to_nat(0u);
v___x_1558_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1558_, 0, v_s_1555_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
lean_ctor_set(v___x_1558_, 2, v_p_1556_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_String_replaceEnd(lean_object* v_s_1559_, lean_object* v_p_1560_){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = lean_unsigned_to_nat(0u);
v___x_1562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1562_, 0, v_s_1559_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
lean_ctor_set(v___x_1562_, 2, v_p_1560_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_String_sliceFrom(lean_object* v_s_1563_, lean_object* v_p_1564_){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = lean_string_utf8_byte_size(v_s_1563_);
v___x_1566_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1566_, 0, v_s_1563_);
lean_ctor_set(v___x_1566_, 1, v_p_1564_);
lean_ctor_set(v___x_1566_, 2, v___x_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStart(lean_object* v_s_1567_, lean_object* v_p_1568_){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = lean_string_utf8_byte_size(v_s_1567_);
v___x_1570_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1570_, 0, v_s_1567_);
lean_ctor_set(v___x_1570_, 1, v_p_1568_);
lean_ctor_set(v___x_1570_, 2, v___x_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_String_slice___redArg(lean_object* v_s_1571_, lean_object* v_startInclusive_1572_, lean_object* v_endExclusive_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1574_, 0, v_s_1571_);
lean_ctor_set(v___x_1574_, 1, v_startInclusive_1572_);
lean_ctor_set(v___x_1574_, 2, v_endExclusive_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_String_slice(lean_object* v_s_1575_, lean_object* v_startInclusive_1576_, lean_object* v_endExclusive_1577_, lean_object* v_h_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1579_, 0, v_s_1575_);
lean_ctor_set(v___x_1579_, 1, v_startInclusive_1576_);
lean_ctor_set(v___x_1579_, 2, v_endExclusive_1577_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x3f(lean_object* v_s_1580_, lean_object* v_startInclusive_1581_, lean_object* v_endExclusive_1582_){
_start:
{
uint8_t v___x_1583_; 
v___x_1583_ = lean_nat_dec_le(v_startInclusive_1581_, v_endExclusive_1582_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; 
lean_dec(v_endExclusive_1582_);
lean_dec(v_startInclusive_1581_);
lean_dec_ref(v_s_1580_);
v___x_1584_ = lean_box(0);
return v___x_1584_;
}
else
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1585_, 0, v_s_1580_);
lean_ctor_set(v___x_1585_, 1, v_startInclusive_1581_);
lean_ctor_set(v___x_1585_, 2, v_endExclusive_1582_);
v___x_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
return v___x_1586_;
}
}
}
LEAN_EXPORT lean_object* l_String_slice_x21(lean_object* v_s_1587_, lean_object* v_p_u2081_1588_, lean_object* v_p_u2082_1589_){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1590_ = lean_unsigned_to_nat(0u);
v___x_1591_ = lean_string_utf8_byte_size(v_s_1587_);
v___x_1592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1592_, 0, v_s_1587_);
lean_ctor_set(v___x_1592_, 1, v___x_1590_);
lean_ctor_set(v___x_1592_, 2, v___x_1591_);
v___x_1593_ = l_String_Slice_slice_x21(v___x_1592_, v_p_u2081_1588_, v_p_u2082_1589_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x21___boxed(lean_object* v_s_1594_, lean_object* v_p_u2081_1595_, lean_object* v_p_u2082_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_String_slice_x21(v_s_1594_, v_p_u2081_1595_, v_p_u2082_1596_);
lean_dec(v_p_u2082_1596_);
lean_dec(v_p_u2081_1595_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21(lean_object* v_s_1598_, lean_object* v_p_u2081_1599_, lean_object* v_p_u2082_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_String_slice_x21(v_s_1598_, v_p_u2081_1599_, v_p_u2082_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21___boxed(lean_object* v_s_1602_, lean_object* v_p_u2081_1603_, lean_object* v_p_u2082_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_String_replaceStartEnd_x21(v_s_1602_, v_p_u2081_1603_, v_p_u2082_1604_);
lean_dec(v_p_u2082_1604_);
lean_dec(v_p_u2081_1603_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg(lean_object* v_p_u2080_1606_, lean_object* v_pos_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = lean_nat_add(v_p_u2080_1606_, v_pos_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg___boxed(lean_object* v_p_u2080_1609_, lean_object* v_pos_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_String_Pos_ofSliceFrom___redArg(v_p_u2080_1609_, v_pos_1610_);
lean_dec(v_pos_1610_);
lean_dec(v_p_u2080_1609_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom(lean_object* v_s_1612_, lean_object* v_p_u2080_1613_, lean_object* v_pos_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = lean_nat_add(v_p_u2080_1613_, v_pos_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___boxed(lean_object* v_s_1616_, lean_object* v_p_u2080_1617_, lean_object* v_pos_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_String_Pos_ofSliceFrom(v_s_1616_, v_p_u2080_1617_, v_pos_1618_);
lean_dec(v_pos_1618_);
lean_dec(v_p_u2080_1617_);
lean_dec_ref(v_s_1616_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg(lean_object* v_p_u2080_1620_, lean_object* v_pos_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_nat_add(v_p_u2080_1620_, v_pos_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg___boxed(lean_object* v_p_u2080_1623_, lean_object* v_pos_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_String_Pos_ofReplaceStart___redArg(v_p_u2080_1623_, v_pos_1624_);
lean_dec(v_pos_1624_);
lean_dec(v_p_u2080_1623_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart(lean_object* v_s_1626_, lean_object* v_p_u2080_1627_, lean_object* v_pos_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_nat_add(v_p_u2080_1627_, v_pos_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___boxed(lean_object* v_s_1630_, lean_object* v_p_u2080_1631_, lean_object* v_pos_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_String_Pos_ofReplaceStart(v_s_1630_, v_p_u2080_1631_, v_pos_1632_);
lean_dec(v_pos_1632_);
lean_dec(v_p_u2080_1631_);
lean_dec_ref(v_s_1630_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg(lean_object* v_p_u2080_1634_, lean_object* v_pos_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_nat_sub(v_pos_1635_, v_p_u2080_1634_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg___boxed(lean_object* v_p_u2080_1637_, lean_object* v_pos_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_String_Pos_sliceFrom___redArg(v_p_u2080_1637_, v_pos_1638_);
lean_dec(v_pos_1638_);
lean_dec(v_p_u2080_1637_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom(lean_object* v_s_1640_, lean_object* v_p_u2080_1641_, lean_object* v_pos_1642_, lean_object* v_h_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = lean_nat_sub(v_pos_1642_, v_p_u2080_1641_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___boxed(lean_object* v_s_1645_, lean_object* v_p_u2080_1646_, lean_object* v_pos_1647_, lean_object* v_h_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_String_Pos_sliceFrom(v_s_1645_, v_p_u2080_1646_, v_pos_1647_, v_h_1648_);
lean_dec(v_pos_1647_);
lean_dec(v_p_u2080_1646_);
lean_dec_ref(v_s_1645_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg(lean_object* v_p_u2080_1650_, lean_object* v_pos_1651_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = lean_nat_sub(v_pos_1651_, v_p_u2080_1650_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg___boxed(lean_object* v_p_u2080_1653_, lean_object* v_pos_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_String_Pos_toReplaceStart___redArg(v_p_u2080_1653_, v_pos_1654_);
lean_dec(v_pos_1654_);
lean_dec(v_p_u2080_1653_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart(lean_object* v_s_1656_, lean_object* v_p_u2080_1657_, lean_object* v_pos_1658_, lean_object* v_h_1659_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_nat_sub(v_pos_1658_, v_p_u2080_1657_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___boxed(lean_object* v_s_1661_, lean_object* v_p_u2080_1662_, lean_object* v_pos_1663_, lean_object* v_h_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_String_Pos_toReplaceStart(v_s_1661_, v_p_u2080_1662_, v_pos_1663_, v_h_1664_);
lean_dec(v_pos_1663_);
lean_dec(v_p_u2080_1662_);
lean_dec_ref(v_s_1661_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg(lean_object* v_pos_1666_){
_start:
{
lean_inc(v_pos_1666_);
return v_pos_1666_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg___boxed(lean_object* v_pos_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_String_Pos_ofSliceTo___redArg(v_pos_1667_);
lean_dec(v_pos_1667_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo(lean_object* v_s_1669_, lean_object* v_p_u2080_1670_, lean_object* v_pos_1671_){
_start:
{
lean_inc(v_pos_1671_);
return v_pos_1671_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___boxed(lean_object* v_s_1672_, lean_object* v_p_u2080_1673_, lean_object* v_pos_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_String_Pos_ofSliceTo(v_s_1672_, v_p_u2080_1673_, v_pos_1674_);
lean_dec(v_pos_1674_);
lean_dec(v_p_u2080_1673_);
lean_dec_ref(v_s_1672_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg(lean_object* v_pos_1676_){
_start:
{
lean_inc(v_pos_1676_);
return v_pos_1676_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg___boxed(lean_object* v_pos_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_String_Pos_ofReplaceEnd___redArg(v_pos_1677_);
lean_dec(v_pos_1677_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd(lean_object* v_s_1679_, lean_object* v_p_u2080_1680_, lean_object* v_pos_1681_){
_start:
{
lean_inc(v_pos_1681_);
return v_pos_1681_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___boxed(lean_object* v_s_1682_, lean_object* v_p_u2080_1683_, lean_object* v_pos_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_String_Pos_ofReplaceEnd(v_s_1682_, v_p_u2080_1683_, v_pos_1684_);
lean_dec(v_pos_1684_);
lean_dec(v_p_u2080_1683_);
lean_dec_ref(v_s_1682_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg(lean_object* v_pos_1686_){
_start:
{
lean_inc(v_pos_1686_);
return v_pos_1686_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg___boxed(lean_object* v_pos_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_String_Pos_sliceTo___redArg(v_pos_1687_);
lean_dec(v_pos_1687_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo(lean_object* v_s_1689_, lean_object* v_p_u2080_1690_, lean_object* v_pos_1691_, lean_object* v_h_1692_){
_start:
{
lean_inc(v_pos_1691_);
return v_pos_1691_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___boxed(lean_object* v_s_1693_, lean_object* v_p_u2080_1694_, lean_object* v_pos_1695_, lean_object* v_h_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_String_Pos_sliceTo(v_s_1693_, v_p_u2080_1694_, v_pos_1695_, v_h_1696_);
lean_dec(v_pos_1695_);
lean_dec(v_p_u2080_1694_);
lean_dec_ref(v_s_1693_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg(lean_object* v_pos_1698_){
_start:
{
lean_inc(v_pos_1698_);
return v_pos_1698_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg___boxed(lean_object* v_pos_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_String_Pos_toReplaceEnd___redArg(v_pos_1699_);
lean_dec(v_pos_1699_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd(lean_object* v_s_1701_, lean_object* v_p_u2080_1702_, lean_object* v_pos_1703_, lean_object* v_h_1704_){
_start:
{
lean_inc(v_pos_1703_);
return v_pos_1703_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___boxed(lean_object* v_s_1705_, lean_object* v_p_u2080_1706_, lean_object* v_pos_1707_, lean_object* v_h_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_String_Pos_toReplaceEnd(v_s_1705_, v_p_u2080_1706_, v_pos_1707_, v_h_1708_);
lean_dec(v_pos_1707_);
lean_dec(v_p_u2080_1706_);
lean_dec_ref(v_s_1705_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg(lean_object* v_p_u2080_1710_, lean_object* v_pos_1711_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = lean_nat_add(v_p_u2080_1710_, v_pos_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1713_, lean_object* v_pos_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_String_Slice_Pos_ofSlice___redArg(v_p_u2080_1713_, v_pos_1714_);
lean_dec(v_pos_1714_);
lean_dec(v_p_u2080_1713_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice(lean_object* v_s_1716_, lean_object* v_p_u2080_1717_, lean_object* v_p_u2081_1718_, lean_object* v_h_1719_, lean_object* v_pos_1720_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_nat_add(v_p_u2080_1717_, v_pos_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___boxed(lean_object* v_s_1722_, lean_object* v_p_u2080_1723_, lean_object* v_p_u2081_1724_, lean_object* v_h_1725_, lean_object* v_pos_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_String_Slice_Pos_ofSlice(v_s_1722_, v_p_u2080_1723_, v_p_u2081_1724_, v_h_1725_, v_pos_1726_);
lean_dec(v_pos_1726_);
lean_dec(v_p_u2081_1724_);
lean_dec(v_p_u2080_1723_);
lean_dec_ref(v_s_1722_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg(lean_object* v_p_u2080_1728_, lean_object* v_pos_1729_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = lean_nat_add(v_p_u2080_1728_, v_pos_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1731_, lean_object* v_pos_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_String_Pos_ofSlice___redArg(v_p_u2080_1731_, v_pos_1732_);
lean_dec(v_pos_1732_);
lean_dec(v_p_u2080_1731_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice(lean_object* v_s_1734_, lean_object* v_p_u2080_1735_, lean_object* v_p_u2081_1736_, lean_object* v_h_1737_, lean_object* v_pos_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_nat_add(v_p_u2080_1735_, v_pos_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___boxed(lean_object* v_s_1740_, lean_object* v_p_u2080_1741_, lean_object* v_p_u2081_1742_, lean_object* v_h_1743_, lean_object* v_pos_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_String_Pos_ofSlice(v_s_1740_, v_p_u2080_1741_, v_p_u2081_1742_, v_h_1743_, v_pos_1744_);
lean_dec(v_pos_1744_);
lean_dec(v_p_u2081_1742_);
lean_dec(v_p_u2080_1741_);
lean_dec_ref(v_s_1740_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg(lean_object* v_pos_1746_, lean_object* v_p_u2080_1747_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = lean_nat_sub(v_pos_1746_, v_p_u2080_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg___boxed(lean_object* v_pos_1749_, lean_object* v_p_u2080_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_String_Slice_Pos_slice___redArg(v_pos_1749_, v_p_u2080_1750_);
lean_dec(v_p_u2080_1750_);
lean_dec(v_pos_1749_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice(lean_object* v_s_1752_, lean_object* v_pos_1753_, lean_object* v_p_u2080_1754_, lean_object* v_p_u2081_1755_, lean_object* v_h_u2081_1756_, lean_object* v_h_u2082_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_nat_sub(v_pos_1753_, v_p_u2080_1754_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___boxed(lean_object* v_s_1759_, lean_object* v_pos_1760_, lean_object* v_p_u2080_1761_, lean_object* v_p_u2081_1762_, lean_object* v_h_u2081_1763_, lean_object* v_h_u2082_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_String_Slice_Pos_slice(v_s_1759_, v_pos_1760_, v_p_u2080_1761_, v_p_u2081_1762_, v_h_u2081_1763_, v_h_u2082_1764_);
lean_dec(v_p_u2081_1762_);
lean_dec(v_p_u2080_1761_);
lean_dec(v_pos_1760_);
lean_dec_ref(v_s_1759_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg(lean_object* v_pos_1766_, lean_object* v_p_u2080_1767_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = lean_nat_sub(v_pos_1766_, v_p_u2080_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg___boxed(lean_object* v_pos_1769_, lean_object* v_p_u2080_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_String_Pos_slice___redArg(v_pos_1769_, v_p_u2080_1770_);
lean_dec(v_p_u2080_1770_);
lean_dec(v_pos_1769_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice(lean_object* v_s_1772_, lean_object* v_pos_1773_, lean_object* v_p_u2080_1774_, lean_object* v_p_u2081_1775_, lean_object* v_h_u2081_1776_, lean_object* v_h_u2082_1777_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = lean_nat_sub(v_pos_1773_, v_p_u2080_1774_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___boxed(lean_object* v_s_1779_, lean_object* v_pos_1780_, lean_object* v_p_u2080_1781_, lean_object* v_p_u2081_1782_, lean_object* v_h_u2081_1783_, lean_object* v_h_u2082_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_String_Pos_slice(v_s_1779_, v_pos_1780_, v_p_u2080_1781_, v_p_u2081_1782_, v_h_u2081_1783_, v_h_u2082_1784_);
lean_dec(v_p_u2081_1782_);
lean_dec(v_p_u2080_1781_);
lean_dec(v_pos_1780_);
lean_dec_ref(v_s_1779_);
return v_res_1785_;
}
}
static lean_object* _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1788_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__1));
v___x_1789_ = lean_unsigned_to_nat(4u);
v___x_1790_ = lean_unsigned_to_nat(2613u);
v___x_1791_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__0));
v___x_1792_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1793_ = l_mkPanicMessageWithDecl(v___x_1792_, v___x_1791_, v___x_1790_, v___x_1789_, v___x_1788_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg(lean_object* v_pos_1794_, lean_object* v_p_u2080_1795_, lean_object* v_p_u2081_1796_){
_start:
{
uint8_t v___x_1801_; 
v___x_1801_ = lean_nat_dec_le(v_p_u2080_1795_, v_pos_1794_);
if (v___x_1801_ == 0)
{
goto v___jp_1797_;
}
else
{
uint8_t v___x_1802_; 
v___x_1802_ = lean_nat_dec_le(v_pos_1794_, v_p_u2081_1796_);
if (v___x_1802_ == 0)
{
goto v___jp_1797_;
}
else
{
lean_object* v___x_1803_; 
v___x_1803_ = lean_nat_sub(v_pos_1794_, v_p_u2080_1795_);
return v___x_1803_;
}
}
v___jp_1797_:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1798_ = lean_unsigned_to_nat(0u);
v___x_1799_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1800_ = l_panic___redArg(v___x_1798_, v___x_1799_);
return v___x_1800_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1804_, lean_object* v_p_u2080_1805_, lean_object* v_p_u2081_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_String_Slice_Pos_sliceOrPanic___redArg(v_pos_1804_, v_p_u2080_1805_, v_p_u2081_1806_);
lean_dec(v_p_u2081_1806_);
lean_dec(v_p_u2080_1805_);
lean_dec(v_pos_1804_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic(lean_object* v_s_1808_, lean_object* v_pos_1809_, lean_object* v_p_u2080_1810_, lean_object* v_p_u2081_1811_, lean_object* v_h_1812_){
_start:
{
uint8_t v___x_1817_; 
v___x_1817_ = lean_nat_dec_le(v_p_u2080_1810_, v_pos_1809_);
if (v___x_1817_ == 0)
{
goto v___jp_1813_;
}
else
{
uint8_t v___x_1818_; 
v___x_1818_ = lean_nat_dec_le(v_pos_1809_, v_p_u2081_1811_);
if (v___x_1818_ == 0)
{
goto v___jp_1813_;
}
else
{
lean_object* v___x_1819_; 
v___x_1819_ = lean_nat_sub(v_pos_1809_, v_p_u2080_1810_);
return v___x_1819_;
}
}
v___jp_1813_:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1814_ = lean_unsigned_to_nat(0u);
v___x_1815_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1816_ = l_panic___redArg(v___x_1814_, v___x_1815_);
return v___x_1816_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___boxed(lean_object* v_s_1820_, lean_object* v_pos_1821_, lean_object* v_p_u2080_1822_, lean_object* v_p_u2081_1823_, lean_object* v_h_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_String_Slice_Pos_sliceOrPanic(v_s_1820_, v_pos_1821_, v_p_u2080_1822_, v_p_u2081_1823_, v_h_1824_);
lean_dec(v_p_u2081_1823_);
lean_dec(v_p_u2080_1822_);
lean_dec(v_pos_1821_);
lean_dec_ref(v_s_1820_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg(lean_object* v_pos_1826_, lean_object* v_p_u2080_1827_, lean_object* v_p_u2081_1828_){
_start:
{
uint8_t v___x_1833_; 
v___x_1833_ = lean_nat_dec_le(v_p_u2080_1827_, v_pos_1826_);
if (v___x_1833_ == 0)
{
goto v___jp_1829_;
}
else
{
uint8_t v___x_1834_; 
v___x_1834_ = lean_nat_dec_le(v_pos_1826_, v_p_u2081_1828_);
if (v___x_1834_ == 0)
{
goto v___jp_1829_;
}
else
{
lean_object* v___x_1835_; 
v___x_1835_ = lean_nat_sub(v_pos_1826_, v_p_u2080_1827_);
return v___x_1835_;
}
}
v___jp_1829_:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1830_ = lean_unsigned_to_nat(0u);
v___x_1831_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1832_ = l_panic___redArg(v___x_1830_, v___x_1831_);
return v___x_1832_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1836_, lean_object* v_p_u2080_1837_, lean_object* v_p_u2081_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_String_Pos_sliceOrPanic___redArg(v_pos_1836_, v_p_u2080_1837_, v_p_u2081_1838_);
lean_dec(v_p_u2081_1838_);
lean_dec(v_p_u2080_1837_);
lean_dec(v_pos_1836_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic(lean_object* v_s_1840_, lean_object* v_pos_1841_, lean_object* v_p_u2080_1842_, lean_object* v_p_u2081_1843_, lean_object* v_h_1844_){
_start:
{
uint8_t v___x_1849_; 
v___x_1849_ = lean_nat_dec_le(v_p_u2080_1842_, v_pos_1841_);
if (v___x_1849_ == 0)
{
goto v___jp_1845_;
}
else
{
uint8_t v___x_1850_; 
v___x_1850_ = lean_nat_dec_le(v_pos_1841_, v_p_u2081_1843_);
if (v___x_1850_ == 0)
{
goto v___jp_1845_;
}
else
{
lean_object* v___x_1851_; 
v___x_1851_ = lean_nat_sub(v_pos_1841_, v_p_u2080_1842_);
return v___x_1851_;
}
}
v___jp_1845_:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1846_ = lean_unsigned_to_nat(0u);
v___x_1847_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1848_ = l_panic___redArg(v___x_1846_, v___x_1847_);
return v___x_1848_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___boxed(lean_object* v_s_1852_, lean_object* v_pos_1853_, lean_object* v_p_u2080_1854_, lean_object* v_p_u2081_1855_, lean_object* v_h_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_String_Pos_sliceOrPanic(v_s_1852_, v_pos_1853_, v_p_u2080_1854_, v_p_u2081_1855_, v_h_1856_);
lean_dec(v_p_u2081_1855_);
lean_dec(v_p_u2080_1854_);
lean_dec(v_pos_1853_);
lean_dec_ref(v_s_1852_);
return v_res_1857_;
}
}
static lean_object* _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1859_ = ((lean_object*)(l_String_Slice_slice_x21___closed__1));
v___x_1860_ = lean_unsigned_to_nat(4u);
v___x_1861_ = lean_unsigned_to_nat(2637u);
v___x_1862_ = ((lean_object*)(l_String_Slice_Pos_ofSlice_x21___redArg___closed__0));
v___x_1863_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1864_ = l_mkPanicMessageWithDecl(v___x_1863_, v___x_1862_, v___x_1861_, v___x_1860_, v___x_1859_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1865_, lean_object* v_p_u2081_1866_, lean_object* v_pos_1867_){
_start:
{
uint8_t v___x_1868_; 
v___x_1868_ = lean_nat_dec_le(v_p_u2080_1865_, v_p_u2081_1866_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1869_ = lean_unsigned_to_nat(0u);
v___x_1870_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1871_ = l_panic___redArg(v___x_1869_, v___x_1870_);
return v___x_1871_;
}
else
{
lean_object* v___x_1872_; 
v___x_1872_ = lean_nat_add(v_p_u2080_1865_, v_pos_1867_);
return v___x_1872_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1873_, lean_object* v_p_u2081_1874_, lean_object* v_pos_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_String_Slice_Pos_ofSlice_x21___redArg(v_p_u2080_1873_, v_p_u2081_1874_, v_pos_1875_);
lean_dec(v_pos_1875_);
lean_dec(v_p_u2081_1874_);
lean_dec(v_p_u2080_1873_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21(lean_object* v_s_1877_, lean_object* v_p_u2080_1878_, lean_object* v_p_u2081_1879_, lean_object* v_pos_1880_){
_start:
{
uint8_t v___x_1881_; 
v___x_1881_ = lean_nat_dec_le(v_p_u2080_1878_, v_p_u2081_1879_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1882_ = lean_unsigned_to_nat(0u);
v___x_1883_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1884_ = l_panic___redArg(v___x_1882_, v___x_1883_);
return v___x_1884_;
}
else
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_nat_add(v_p_u2080_1878_, v_pos_1880_);
return v___x_1885_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___boxed(lean_object* v_s_1886_, lean_object* v_p_u2080_1887_, lean_object* v_p_u2081_1888_, lean_object* v_pos_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_String_Slice_Pos_ofSlice_x21(v_s_1886_, v_p_u2080_1887_, v_p_u2081_1888_, v_pos_1889_);
lean_dec(v_pos_1889_);
lean_dec(v_p_u2081_1888_);
lean_dec(v_p_u2080_1887_);
lean_dec_ref(v_s_1886_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1891_, lean_object* v_p_u2081_1892_, lean_object* v_pos_1893_){
_start:
{
uint8_t v___x_1894_; 
v___x_1894_ = lean_nat_dec_le(v_p_u2080_1891_, v_p_u2081_1892_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1895_ = lean_unsigned_to_nat(0u);
v___x_1896_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1897_ = l_panic___redArg(v___x_1895_, v___x_1896_);
return v___x_1897_;
}
else
{
lean_object* v___x_1898_; 
v___x_1898_ = lean_nat_add(v_p_u2080_1891_, v_pos_1893_);
return v___x_1898_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1899_, lean_object* v_p_u2081_1900_, lean_object* v_pos_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_String_Pos_ofSlice_x21___redArg(v_p_u2080_1899_, v_p_u2081_1900_, v_pos_1901_);
lean_dec(v_pos_1901_);
lean_dec(v_p_u2081_1900_);
lean_dec(v_p_u2080_1899_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21(lean_object* v_s_1903_, lean_object* v_p_u2080_1904_, lean_object* v_p_u2081_1905_, lean_object* v_pos_1906_){
_start:
{
uint8_t v___x_1907_; 
v___x_1907_ = lean_nat_dec_le(v_p_u2080_1904_, v_p_u2081_1905_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1908_ = lean_unsigned_to_nat(0u);
v___x_1909_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1910_ = l_panic___redArg(v___x_1908_, v___x_1909_);
return v___x_1910_;
}
else
{
lean_object* v___x_1911_; 
v___x_1911_ = lean_nat_add(v_p_u2080_1904_, v_pos_1906_);
return v___x_1911_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___boxed(lean_object* v_s_1912_, lean_object* v_p_u2080_1913_, lean_object* v_p_u2081_1914_, lean_object* v_pos_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_String_Pos_ofSlice_x21(v_s_1912_, v_p_u2080_1913_, v_p_u2081_1914_, v_pos_1915_);
lean_dec(v_pos_1915_);
lean_dec(v_p_u2081_1914_);
lean_dec(v_p_u2080_1913_);
lean_dec_ref(v_s_1912_);
return v_res_1916_;
}
}
static lean_object* _init_l_String_Slice_Pos_slice_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1919_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__1));
v___x_1920_ = lean_unsigned_to_nat(4u);
v___x_1921_ = lean_unsigned_to_nat(2655u);
v___x_1922_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__0));
v___x_1923_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1924_ = l_mkPanicMessageWithDecl(v___x_1923_, v___x_1922_, v___x_1921_, v___x_1920_, v___x_1919_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg(lean_object* v_pos_1925_, lean_object* v_p_u2080_1926_, lean_object* v_p_u2081_1927_){
_start:
{
uint8_t v___x_1932_; 
v___x_1932_ = lean_nat_dec_le(v_p_u2080_1926_, v_pos_1925_);
if (v___x_1932_ == 0)
{
goto v___jp_1928_;
}
else
{
uint8_t v___x_1933_; 
v___x_1933_ = lean_nat_dec_le(v_pos_1925_, v_p_u2081_1927_);
if (v___x_1933_ == 0)
{
goto v___jp_1928_;
}
else
{
lean_object* v___x_1934_; 
v___x_1934_ = lean_nat_sub(v_pos_1925_, v_p_u2080_1926_);
return v___x_1934_;
}
}
v___jp_1928_:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1929_ = lean_unsigned_to_nat(0u);
v___x_1930_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1931_ = l_panic___redArg(v___x_1929_, v___x_1930_);
return v___x_1931_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1935_, lean_object* v_p_u2080_1936_, lean_object* v_p_u2081_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_String_Slice_Pos_slice_x21___redArg(v_pos_1935_, v_p_u2080_1936_, v_p_u2081_1937_);
lean_dec(v_p_u2081_1937_);
lean_dec(v_p_u2080_1936_);
lean_dec(v_pos_1935_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21(lean_object* v_s_1939_, lean_object* v_pos_1940_, lean_object* v_p_u2080_1941_, lean_object* v_p_u2081_1942_){
_start:
{
uint8_t v___x_1947_; 
v___x_1947_ = lean_nat_dec_le(v_p_u2080_1941_, v_pos_1940_);
if (v___x_1947_ == 0)
{
goto v___jp_1943_;
}
else
{
uint8_t v___x_1948_; 
v___x_1948_ = lean_nat_dec_le(v_pos_1940_, v_p_u2081_1942_);
if (v___x_1948_ == 0)
{
goto v___jp_1943_;
}
else
{
lean_object* v___x_1949_; 
v___x_1949_ = lean_nat_sub(v_pos_1940_, v_p_u2080_1941_);
return v___x_1949_;
}
}
v___jp_1943_:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1944_ = lean_unsigned_to_nat(0u);
v___x_1945_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1946_ = l_panic___redArg(v___x_1944_, v___x_1945_);
return v___x_1946_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___boxed(lean_object* v_s_1950_, lean_object* v_pos_1951_, lean_object* v_p_u2080_1952_, lean_object* v_p_u2081_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_String_Slice_Pos_slice_x21(v_s_1950_, v_pos_1951_, v_p_u2080_1952_, v_p_u2081_1953_);
lean_dec(v_p_u2081_1953_);
lean_dec(v_p_u2080_1952_);
lean_dec(v_pos_1951_);
lean_dec_ref(v_s_1950_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg(lean_object* v_pos_1955_, lean_object* v_p_u2080_1956_, lean_object* v_p_u2081_1957_){
_start:
{
uint8_t v___x_1962_; 
v___x_1962_ = lean_nat_dec_le(v_p_u2080_1956_, v_pos_1955_);
if (v___x_1962_ == 0)
{
goto v___jp_1958_;
}
else
{
uint8_t v___x_1963_; 
v___x_1963_ = lean_nat_dec_le(v_pos_1955_, v_p_u2081_1957_);
if (v___x_1963_ == 0)
{
goto v___jp_1958_;
}
else
{
lean_object* v___x_1964_; 
v___x_1964_ = lean_nat_sub(v_pos_1955_, v_p_u2080_1956_);
return v___x_1964_;
}
}
v___jp_1958_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1959_ = lean_unsigned_to_nat(0u);
v___x_1960_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1961_ = l_panic___redArg(v___x_1959_, v___x_1960_);
return v___x_1961_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1965_, lean_object* v_p_u2080_1966_, lean_object* v_p_u2081_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_String_Pos_slice_x21___redArg(v_pos_1965_, v_p_u2080_1966_, v_p_u2081_1967_);
lean_dec(v_p_u2081_1967_);
lean_dec(v_p_u2080_1966_);
lean_dec(v_pos_1965_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21(lean_object* v_s_1969_, lean_object* v_pos_1970_, lean_object* v_p_u2080_1971_, lean_object* v_p_u2081_1972_){
_start:
{
uint8_t v___x_1977_; 
v___x_1977_ = lean_nat_dec_le(v_p_u2080_1971_, v_pos_1970_);
if (v___x_1977_ == 0)
{
goto v___jp_1973_;
}
else
{
uint8_t v___x_1978_; 
v___x_1978_ = lean_nat_dec_le(v_pos_1970_, v_p_u2081_1972_);
if (v___x_1978_ == 0)
{
goto v___jp_1973_;
}
else
{
lean_object* v___x_1979_; 
v___x_1979_ = lean_nat_sub(v_pos_1970_, v_p_u2080_1971_);
return v___x_1979_;
}
}
v___jp_1973_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1974_ = lean_unsigned_to_nat(0u);
v___x_1975_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1976_ = l_panic___redArg(v___x_1974_, v___x_1975_);
return v___x_1976_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___boxed(lean_object* v_s_1980_, lean_object* v_pos_1981_, lean_object* v_p_u2080_1982_, lean_object* v_p_u2081_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_String_Pos_slice_x21(v_s_1980_, v_pos_1981_, v_p_u2080_1982_, v_p_u2081_1983_);
lean_dec(v_p_u2081_1983_);
lean_dec(v_p_u2080_1982_);
lean_dec(v_pos_1981_);
lean_dec_ref(v_s_1980_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract(lean_object* v_s_1985_, lean_object* v_p_u2080_1986_, lean_object* v_p_u2081_1987_){
_start:
{
lean_object* v_str_1988_; lean_object* v_startInclusive_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v_str_1988_ = lean_ctor_get(v_s_1985_, 0);
v_startInclusive_1989_ = lean_ctor_get(v_s_1985_, 1);
v___x_1990_ = lean_nat_add(v_startInclusive_1989_, v_p_u2080_1986_);
v___x_1991_ = lean_nat_add(v_startInclusive_1989_, v_p_u2081_1987_);
v___x_1992_ = lean_string_utf8_extract_fast(v_str_1988_, v___x_1990_, v___x_1991_);
lean_dec(v___x_1991_);
lean_dec(v___x_1990_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract___boxed(lean_object* v_s_1993_, lean_object* v_p_u2080_1994_, lean_object* v_p_u2081_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_String_Slice_extract(v_s_1993_, v_p_u2080_1994_, v_p_u2081_1995_);
lean_dec(v_p_u2081_1995_);
lean_dec(v_p_u2080_1994_);
lean_dec_ref(v_s_1993_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn(lean_object* v_s_1997_, lean_object* v_p_1998_, lean_object* v_n_1999_){
_start:
{
lean_object* v_zero_2000_; uint8_t v_isZero_2001_; 
v_zero_2000_ = lean_unsigned_to_nat(0u);
v_isZero_2001_ = lean_nat_dec_eq(v_n_1999_, v_zero_2000_);
if (v_isZero_2001_ == 1)
{
lean_dec(v_n_1999_);
return v_p_1998_;
}
else
{
lean_object* v_str_2002_; lean_object* v_startInclusive_2003_; lean_object* v_endExclusive_2004_; lean_object* v___x_2005_; uint8_t v_decide_2006_; 
v_str_2002_ = lean_ctor_get(v_s_1997_, 0);
v_startInclusive_2003_ = lean_ctor_get(v_s_1997_, 1);
v_endExclusive_2004_ = lean_ctor_get(v_s_1997_, 2);
v___x_2005_ = lean_nat_sub(v_endExclusive_2004_, v_startInclusive_2003_);
v_decide_2006_ = lean_nat_dec_eq(v_p_1998_, v___x_2005_);
lean_dec(v___x_2005_);
if (v_decide_2006_ == 0)
{
lean_object* v_one_2007_; lean_object* v_n_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v_one_2007_ = lean_unsigned_to_nat(1u);
v_n_2008_ = lean_nat_sub(v_n_1999_, v_one_2007_);
lean_dec(v_n_1999_);
v___x_2009_ = lean_nat_add(v_startInclusive_2003_, v_p_1998_);
lean_dec(v_p_1998_);
v___x_2010_ = lean_string_utf8_next_fast(v_str_2002_, v___x_2009_);
lean_dec(v___x_2009_);
v___x_2011_ = lean_nat_sub(v___x_2010_, v_startInclusive_2003_);
v_p_1998_ = v___x_2011_;
v_n_1999_ = v_n_2008_;
goto _start;
}
else
{
lean_dec(v_n_1999_);
return v_p_1998_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn___boxed(lean_object* v_s_2013_, lean_object* v_p_2014_, lean_object* v_n_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_String_Slice_Pos_nextn(v_s_2013_, v_p_2014_, v_n_2015_);
lean_dec_ref(v_s_2013_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_nextn(lean_object* v_s_2017_, lean_object* v_p_2018_, lean_object* v_n_2019_){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2020_ = lean_unsigned_to_nat(0u);
v___x_2021_ = lean_string_utf8_byte_size(v_s_2017_);
v___x_2022_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2022_, 0, v_s_2017_);
lean_ctor_set(v___x_2022_, 1, v___x_2020_);
lean_ctor_set(v___x_2022_, 2, v___x_2021_);
v___x_2023_ = l_String_Slice_Pos_nextn(v___x_2022_, v_p_2018_, v_n_2019_);
lean_dec_ref_known(v___x_2022_, 3);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(lean_object* v_n_2024_, lean_object* v_h__1_2025_, lean_object* v_h__2_2026_){
_start:
{
lean_object* v_zero_2027_; uint8_t v_isZero_2028_; 
v_zero_2027_ = lean_unsigned_to_nat(0u);
v_isZero_2028_ = lean_nat_dec_eq(v_n_2024_, v_zero_2027_);
if (v_isZero_2028_ == 1)
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
lean_dec(v_h__2_2026_);
v___x_2029_ = lean_box(0);
v___x_2030_ = lean_apply_1(v_h__1_2025_, v___x_2029_);
return v___x_2030_;
}
else
{
lean_object* v_one_2031_; lean_object* v_n_2032_; lean_object* v___x_2033_; 
lean_dec(v_h__1_2025_);
v_one_2031_ = lean_unsigned_to_nat(1u);
v_n_2032_ = lean_nat_sub(v_n_2024_, v_one_2031_);
v___x_2033_ = lean_apply_1(v_h__2_2026_, v_n_2032_);
return v___x_2033_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg___boxed(lean_object* v_n_2034_, lean_object* v_h__1_2035_, lean_object* v_h__2_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(v_n_2034_, v_h__1_2035_, v_h__2_2036_);
lean_dec(v_n_2034_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(lean_object* v_motive_2038_, lean_object* v_n_2039_, lean_object* v_h__1_2040_, lean_object* v_h__2_2041_){
_start:
{
lean_object* v_zero_2042_; uint8_t v_isZero_2043_; 
v_zero_2042_ = lean_unsigned_to_nat(0u);
v_isZero_2043_ = lean_nat_dec_eq(v_n_2039_, v_zero_2042_);
if (v_isZero_2043_ == 1)
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
lean_dec(v_h__2_2041_);
v___x_2044_ = lean_box(0);
v___x_2045_ = lean_apply_1(v_h__1_2040_, v___x_2044_);
return v___x_2045_;
}
else
{
lean_object* v_one_2046_; lean_object* v_n_2047_; lean_object* v___x_2048_; 
lean_dec(v_h__1_2040_);
v_one_2046_ = lean_unsigned_to_nat(1u);
v_n_2047_ = lean_nat_sub(v_n_2039_, v_one_2046_);
v___x_2048_ = lean_apply_1(v_h__2_2041_, v_n_2047_);
return v___x_2048_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___boxed(lean_object* v_motive_2049_, lean_object* v_n_2050_, lean_object* v_h__1_2051_, lean_object* v_h__2_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(v_motive_2049_, v_n_2050_, v_h__1_2051_, v_h__2_2052_);
lean_dec(v_n_2050_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next___boxed(lean_object* v_s_2056_, lean_object* v_p_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = lean_string_utf8_next(v_s_2056_, v_p_2057_);
lean_dec(v_p_2057_);
lean_dec_ref(v_s_2056_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_String_next___boxed(lean_object* v_s_2061_, lean_object* v_p_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = lean_string_utf8_next(v_s_2061_, v_p_2062_);
lean_dec(v_p_2062_);
lean_dec_ref(v_s_2061_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux(lean_object* v_x_2064_, lean_object* v_x_2065_, lean_object* v_x_2066_){
_start:
{
if (lean_obj_tag(v_x_2064_) == 0)
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
lean_dec(v_x_2065_);
v___x_2067_ = lean_unsigned_to_nat(1u);
v___x_2068_ = lean_nat_sub(v_x_2066_, v___x_2067_);
return v___x_2068_;
}
else
{
lean_object* v_head_2069_; lean_object* v_tail_2070_; lean_object* v___y_2072_; uint32_t v___x_2076_; uint32_t v___x_2077_; uint8_t v___x_2078_; 
v_head_2069_ = lean_ctor_get(v_x_2064_, 0);
v_tail_2070_ = lean_ctor_get(v_x_2064_, 1);
v___x_2076_ = 127;
v___x_2077_ = lean_unbox_uint32(v_head_2069_);
v___x_2078_ = lean_uint32_dec_le(v___x_2077_, v___x_2076_);
if (v___x_2078_ == 0)
{
uint32_t v___x_2079_; uint32_t v___x_2080_; uint8_t v___x_2081_; 
v___x_2079_ = 2047;
v___x_2080_ = lean_unbox_uint32(v_head_2069_);
v___x_2081_ = lean_uint32_dec_le(v___x_2080_, v___x_2079_);
if (v___x_2081_ == 0)
{
uint32_t v___x_2082_; uint32_t v___x_2083_; uint8_t v___x_2084_; 
v___x_2082_ = 65535;
v___x_2083_ = lean_unbox_uint32(v_head_2069_);
v___x_2084_ = lean_uint32_dec_le(v___x_2083_, v___x_2082_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; 
v___x_2085_ = lean_unsigned_to_nat(4u);
v___y_2072_ = v___x_2085_;
goto v___jp_2071_;
}
else
{
lean_object* v___x_2086_; 
v___x_2086_ = lean_unsigned_to_nat(3u);
v___y_2072_ = v___x_2086_;
goto v___jp_2071_;
}
}
else
{
lean_object* v___x_2087_; 
v___x_2087_ = lean_unsigned_to_nat(2u);
v___y_2072_ = v___x_2087_;
goto v___jp_2071_;
}
}
else
{
lean_object* v___x_2088_; 
v___x_2088_ = lean_unsigned_to_nat(1u);
v___y_2072_ = v___x_2088_;
goto v___jp_2071_;
}
v___jp_2071_:
{
lean_object* v___x_2073_; uint8_t v___x_2074_; 
v___x_2073_ = lean_nat_add(v_x_2065_, v___y_2072_);
v___x_2074_ = lean_nat_dec_le(v_x_2066_, v___x_2073_);
if (v___x_2074_ == 0)
{
lean_dec(v_x_2065_);
v_x_2064_ = v_tail_2070_;
v_x_2065_ = v___x_2073_;
goto _start;
}
else
{
lean_dec(v___x_2073_);
return v_x_2065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux___boxed(lean_object* v_x_2089_, lean_object* v_x_2090_, lean_object* v_x_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_String_Pos_Raw_utf8PrevAux(v_x_2089_, v_x_2090_, v_x_2091_);
lean_dec(v_x_2091_);
lean_dec(v_x_2089_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux(lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = l_String_Pos_Raw_utf8PrevAux(v_a_2093_, v_a_2094_, v_a_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux___boxed(lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_String_utf8PrevAux(v_a_2097_, v_a_2098_, v_a_2099_);
lean_dec(v_a_2099_);
lean_dec(v_a_2097_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_prev___boxed(lean_object* v_a_00___x40___internal___hyg_2103_, lean_object* v_a_00___x40___internal___hyg_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_2103_, v_a_00___x40___internal___hyg_2104_);
lean_dec(v_a_00___x40___internal___hyg_2104_);
lean_dec_ref(v_a_00___x40___internal___hyg_2103_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_String_prev___boxed(lean_object* v_a_00___x40___internal___hyg_2108_, lean_object* v_a_00___x40___internal___hyg_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_2108_, v_a_00___x40___internal___hyg_2109_);
lean_dec(v_a_00___x40___internal___hyg_2109_);
lean_dec_ref(v_a_00___x40___internal___hyg_2108_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_2113_, lean_object* v_a_00___x40___internal___hyg_2114_){
_start:
{
uint8_t v_res_2115_; lean_object* v_r_2116_; 
v_res_2115_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_2113_, v_a_00___x40___internal___hyg_2114_);
lean_dec(v_a_00___x40___internal___hyg_2114_);
lean_dec_ref(v_a_00___x40___internal___hyg_2113_);
v_r_2116_ = lean_box(v_res_2115_);
return v_r_2116_;
}
}
LEAN_EXPORT lean_object* l_String_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_2119_, lean_object* v_a_00___x40___internal___hyg_2120_){
_start:
{
uint8_t v_res_2121_; lean_object* v_r_2122_; 
v_res_2121_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_2119_, v_a_00___x40___internal___hyg_2120_);
lean_dec(v_a_00___x40___internal___hyg_2120_);
lean_dec_ref(v_a_00___x40___internal___hyg_2119_);
v_r_2122_ = lean_box(v_res_2121_);
return v_r_2122_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x27___boxed(lean_object* v_s_2126_, lean_object* v_p_2127_, lean_object* v_h_2128_){
_start:
{
uint32_t v_res_2129_; lean_object* v_r_2130_; 
v_res_2129_ = lean_string_utf8_get_fast(v_s_2126_, v_p_2127_);
lean_dec(v_p_2127_);
lean_dec_ref(v_s_2126_);
v_r_2130_ = lean_box_uint32(v_res_2129_);
return v_r_2130_;
}
}
LEAN_EXPORT lean_object* l_String_get_x27___boxed(lean_object* v_s_2134_, lean_object* v_p_2135_, lean_object* v_h_2136_){
_start:
{
uint32_t v_res_2137_; lean_object* v_r_2138_; 
v_res_2137_ = lean_string_utf8_get_fast(v_s_2134_, v_p_2135_);
lean_dec(v_p_2135_);
lean_dec_ref(v_s_2134_);
v_r_2138_ = lean_box_uint32(v_res_2137_);
return v_r_2138_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next_x27___boxed(lean_object* v_s_2142_, lean_object* v_p_2143_, lean_object* v_h_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = lean_string_utf8_next_fast(v_s_2142_, v_p_2143_);
lean_dec(v_p_2143_);
lean_dec_ref(v_s_2142_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_String_next_x27___boxed(lean_object* v_s_2149_, lean_object* v_p_2150_, lean_object* v_h_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = lean_string_utf8_next_fast(v_s_2149_, v_p_2150_);
lean_dec(v_p_2150_);
lean_dec_ref(v_s_2149_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter___redArg(lean_object* v_x_2153_, lean_object* v_x_2154_, lean_object* v_x_2155_, lean_object* v_h__1_2156_, lean_object* v_h__2_2157_){
_start:
{
if (lean_obj_tag(v_x_2153_) == 0)
{
lean_object* v___x_2158_; 
lean_dec(v_h__2_2157_);
v___x_2158_ = lean_apply_2(v_h__1_2156_, v_x_2154_, v_x_2155_);
return v___x_2158_;
}
else
{
lean_object* v_head_2159_; lean_object* v_tail_2160_; lean_object* v___x_2161_; 
lean_dec(v_h__1_2156_);
v_head_2159_ = lean_ctor_get(v_x_2153_, 0);
lean_inc(v_head_2159_);
v_tail_2160_ = lean_ctor_get(v_x_2153_, 1);
lean_inc(v_tail_2160_);
lean_dec_ref_known(v_x_2153_, 2);
v___x_2161_ = lean_apply_4(v_h__2_2157_, v_head_2159_, v_tail_2160_, v_x_2154_, v_x_2155_);
return v___x_2161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter(lean_object* v_motive_2162_, lean_object* v_x_2163_, lean_object* v_x_2164_, lean_object* v_x_2165_, lean_object* v_h__1_2166_, lean_object* v_h__2_2167_){
_start:
{
if (lean_obj_tag(v_x_2163_) == 0)
{
lean_object* v___x_2168_; 
lean_dec(v_h__2_2167_);
v___x_2168_ = lean_apply_2(v_h__1_2166_, v_x_2164_, v_x_2165_);
return v___x_2168_;
}
else
{
lean_object* v_head_2169_; lean_object* v_tail_2170_; lean_object* v___x_2171_; 
lean_dec(v_h__1_2166_);
v_head_2169_ = lean_ctor_get(v_x_2163_, 0);
lean_inc(v_head_2169_);
v_tail_2170_ = lean_ctor_get(v_x_2163_, 1);
lean_inc(v_tail_2170_);
lean_dec_ref_known(v_x_2163_, 2);
v___x_2171_ = lean_apply_4(v_h__2_2167_, v_head_2169_, v_tail_2170_, v_x_2164_, v_x_2165_);
return v___x_2171_;
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop(lean_object* v_a_2172_, lean_object* v_b_2173_, lean_object* v_stopPos_2174_, lean_object* v_i_2175_){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; 
v___x_2176_ = lean_unsigned_to_nat(1u);
v___x_2177_ = lean_nat_add(v_i_2175_, v___x_2176_);
v___x_2178_ = lean_nat_dec_le(v___x_2177_, v_stopPos_2174_);
lean_dec(v___x_2177_);
if (v___x_2178_ == 0)
{
return v_i_2175_;
}
else
{
uint32_t v___x_2179_; uint32_t v___x_2180_; uint8_t v___x_2181_; 
v___x_2179_ = lean_string_utf8_get(v_a_2172_, v_i_2175_);
v___x_2180_ = lean_string_utf8_get(v_b_2173_, v_i_2175_);
v___x_2181_ = lean_uint32_dec_eq(v___x_2179_, v___x_2180_);
if (v___x_2181_ == 0)
{
return v_i_2175_;
}
else
{
lean_object* v___x_2182_; 
v___x_2182_ = lean_string_utf8_next(v_a_2172_, v_i_2175_);
lean_dec(v_i_2175_);
v_i_2175_ = v___x_2182_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop___boxed(lean_object* v_a_2184_, lean_object* v_b_2185_, lean_object* v_stopPos_2186_, lean_object* v_i_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_String_firstDiffPos_loop(v_a_2184_, v_b_2185_, v_stopPos_2186_, v_i_2187_);
lean_dec(v_stopPos_2186_);
lean_dec_ref(v_b_2185_);
lean_dec_ref(v_a_2184_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos(lean_object* v_a_2189_, lean_object* v_b_2190_){
_start:
{
lean_object* v___y_2192_; lean_object* v___x_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v___x_2195_ = lean_string_utf8_byte_size(v_a_2189_);
v___x_2196_ = lean_string_utf8_byte_size(v_b_2190_);
v___x_2197_ = lean_nat_dec_le(v___x_2195_, v___x_2196_);
if (v___x_2197_ == 0)
{
v___y_2192_ = v___x_2196_;
goto v___jp_2191_;
}
else
{
v___y_2192_ = v___x_2195_;
goto v___jp_2191_;
}
v___jp_2191_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = lean_unsigned_to_nat(0u);
v___x_2194_ = l_String_firstDiffPos_loop(v_a_2189_, v_b_2190_, v___y_2192_, v___x_2193_);
lean_dec(v___y_2192_);
return v___x_2194_;
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos___boxed(lean_object* v_a_2198_, lean_object* v_b_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_String_firstDiffPos(v_a_2198_, v_b_2199_);
lean_dec_ref(v_b_2199_);
lean_dec_ref(v_a_2198_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082(lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_){
_start:
{
if (lean_obj_tag(v_a_2201_) == 0)
{
return v_a_2201_;
}
else
{
lean_object* v_head_2204_; lean_object* v_tail_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2231_; 
v_head_2204_ = lean_ctor_get(v_a_2201_, 0);
v_tail_2205_ = lean_ctor_get(v_a_2201_, 1);
v_isSharedCheck_2231_ = !lean_is_exclusive(v_a_2201_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2207_ = v_a_2201_;
v_isShared_2208_ = v_isSharedCheck_2231_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_tail_2205_);
lean_inc(v_head_2204_);
lean_dec(v_a_2201_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2231_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___y_2210_; uint8_t v_decide_2216_; 
v_decide_2216_ = lean_nat_dec_eq(v_a_2202_, v_a_2203_);
if (v_decide_2216_ == 0)
{
uint32_t v___x_2217_; uint32_t v___x_2218_; uint8_t v___x_2219_; 
v___x_2217_ = 127;
v___x_2218_ = lean_unbox_uint32(v_head_2204_);
v___x_2219_ = lean_uint32_dec_le(v___x_2218_, v___x_2217_);
if (v___x_2219_ == 0)
{
uint32_t v___x_2220_; uint32_t v___x_2221_; uint8_t v___x_2222_; 
v___x_2220_ = 2047;
v___x_2221_ = lean_unbox_uint32(v_head_2204_);
v___x_2222_ = lean_uint32_dec_le(v___x_2221_, v___x_2220_);
if (v___x_2222_ == 0)
{
uint32_t v___x_2223_; uint32_t v___x_2224_; uint8_t v___x_2225_; 
v___x_2223_ = 65535;
v___x_2224_ = lean_unbox_uint32(v_head_2204_);
v___x_2225_ = lean_uint32_dec_le(v___x_2224_, v___x_2223_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_unsigned_to_nat(4u);
v___y_2210_ = v___x_2226_;
goto v___jp_2209_;
}
else
{
lean_object* v___x_2227_; 
v___x_2227_ = lean_unsigned_to_nat(3u);
v___y_2210_ = v___x_2227_;
goto v___jp_2209_;
}
}
else
{
lean_object* v___x_2228_; 
v___x_2228_ = lean_unsigned_to_nat(2u);
v___y_2210_ = v___x_2228_;
goto v___jp_2209_;
}
}
else
{
lean_object* v___x_2229_; 
v___x_2229_ = lean_unsigned_to_nat(1u);
v___y_2210_ = v___x_2229_;
goto v___jp_2209_;
}
}
else
{
lean_object* v___x_2230_; 
lean_del_object(v___x_2207_);
lean_dec(v_tail_2205_);
lean_dec(v_head_2204_);
v___x_2230_ = lean_box(0);
return v___x_2230_;
}
v___jp_2209_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2214_; 
v___x_2211_ = lean_nat_add(v_a_2202_, v___y_2210_);
v___x_2212_ = l_String_Pos_Raw_extract_go_u2082(v_tail_2205_, v___x_2211_, v_a_2203_);
lean_dec(v___x_2211_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 1, v___x_2212_);
v___x_2214_ = v___x_2207_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_head_2204_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082___boxed(lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_String_Pos_Raw_extract_go_u2082(v_a_2232_, v_a_2233_, v_a_2234_);
lean_dec(v_a_2234_);
lean_dec(v_a_2233_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081(lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_){
_start:
{
if (lean_obj_tag(v_a_2236_) == 0)
{
lean_dec(v_a_2237_);
return v_a_2236_;
}
else
{
lean_object* v_head_2240_; lean_object* v_tail_2241_; lean_object* v___y_2243_; uint8_t v_decide_2246_; 
v_head_2240_ = lean_ctor_get(v_a_2236_, 0);
v_tail_2241_ = lean_ctor_get(v_a_2236_, 1);
v_decide_2246_ = lean_nat_dec_eq(v_a_2237_, v_a_2238_);
if (v_decide_2246_ == 0)
{
uint32_t v___x_2247_; uint32_t v___x_2248_; uint8_t v___x_2249_; 
lean_inc(v_tail_2241_);
lean_inc(v_head_2240_);
lean_dec_ref_known(v_a_2236_, 2);
v___x_2247_ = 127;
v___x_2248_ = lean_unbox_uint32(v_head_2240_);
v___x_2249_ = lean_uint32_dec_le(v___x_2248_, v___x_2247_);
if (v___x_2249_ == 0)
{
uint32_t v___x_2250_; uint32_t v___x_2251_; uint8_t v___x_2252_; 
v___x_2250_ = 2047;
v___x_2251_ = lean_unbox_uint32(v_head_2240_);
v___x_2252_ = lean_uint32_dec_le(v___x_2251_, v___x_2250_);
if (v___x_2252_ == 0)
{
uint32_t v___x_2253_; uint32_t v___x_2254_; uint8_t v___x_2255_; 
v___x_2253_ = 65535;
v___x_2254_ = lean_unbox_uint32(v_head_2240_);
lean_dec(v_head_2240_);
v___x_2255_ = lean_uint32_dec_le(v___x_2254_, v___x_2253_);
if (v___x_2255_ == 0)
{
lean_object* v___x_2256_; 
v___x_2256_ = lean_unsigned_to_nat(4u);
v___y_2243_ = v___x_2256_;
goto v___jp_2242_;
}
else
{
lean_object* v___x_2257_; 
v___x_2257_ = lean_unsigned_to_nat(3u);
v___y_2243_ = v___x_2257_;
goto v___jp_2242_;
}
}
else
{
lean_object* v___x_2258_; 
lean_dec(v_head_2240_);
v___x_2258_ = lean_unsigned_to_nat(2u);
v___y_2243_ = v___x_2258_;
goto v___jp_2242_;
}
}
else
{
lean_object* v___x_2259_; 
lean_dec(v_head_2240_);
v___x_2259_ = lean_unsigned_to_nat(1u);
v___y_2243_ = v___x_2259_;
goto v___jp_2242_;
}
}
else
{
lean_object* v___x_2260_; 
v___x_2260_ = l_String_Pos_Raw_extract_go_u2082(v_a_2236_, v_a_2237_, v_a_2239_);
lean_dec(v_a_2237_);
return v___x_2260_;
}
v___jp_2242_:
{
lean_object* v___x_2244_; 
v___x_2244_ = lean_nat_add(v_a_2237_, v___y_2243_);
lean_dec(v_a_2237_);
v_a_2236_ = v_tail_2241_;
v_a_2237_ = v___x_2244_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081___boxed(lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l_String_Pos_Raw_extract_go_u2081(v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_);
lean_dec(v_a_2264_);
lean_dec(v_a_2263_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract___boxed(lean_object* v_a_00___x40___internal___hyg_2269_, lean_object* v_a_00___x40___internal___hyg_2270_, lean_object* v_a_00___x40___internal___hyg_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = lean_string_utf8_extract(v_a_00___x40___internal___hyg_2269_, v_a_00___x40___internal___hyg_2270_, v_a_00___x40___internal___hyg_2271_);
lean_dec(v_a_00___x40___internal___hyg_2271_);
lean_dec(v_a_00___x40___internal___hyg_2270_);
lean_dec_ref(v_a_00___x40___internal___hyg_2269_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux(lean_object* v_s_2273_, lean_object* v_pos_2274_, lean_object* v_i_2275_, lean_object* v_offset_2276_){
_start:
{
uint8_t v___x_2277_; 
v___x_2277_ = lean_nat_dec_le(v_pos_2274_, v_i_2275_);
if (v___x_2277_ == 0)
{
uint8_t v___x_2278_; 
v___x_2278_ = lean_string_utf8_at_end(v_s_2273_, v_i_2275_);
if (v___x_2278_ == 0)
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = lean_string_utf8_next(v_s_2273_, v_i_2275_);
lean_dec(v_i_2275_);
v___x_2280_ = lean_unsigned_to_nat(1u);
v___x_2281_ = lean_nat_add(v_offset_2276_, v___x_2280_);
lean_dec(v_offset_2276_);
v_i_2275_ = v___x_2279_;
v_offset_2276_ = v___x_2281_;
goto _start;
}
else
{
lean_dec(v_i_2275_);
return v_offset_2276_;
}
}
else
{
lean_dec(v_i_2275_);
return v_offset_2276_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux___boxed(lean_object* v_s_2283_, lean_object* v_pos_2284_, lean_object* v_i_2285_, lean_object* v_offset_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2283_, v_pos_2284_, v_i_2285_, v_offset_2286_);
lean_dec(v_pos_2284_);
lean_dec_ref(v_s_2283_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos(lean_object* v_s_2288_, lean_object* v_pos_2289_){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = lean_unsigned_to_nat(0u);
v___x_2291_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2288_, v_pos_2289_, v___x_2290_, v___x_2290_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos___boxed(lean_object* v_s_2292_, lean_object* v_pos_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_String_Pos_Raw_offsetOfPos(v_s_2292_, v_pos_2293_);
lean_dec(v_pos_2293_);
lean_dec_ref(v_s_2292_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos(lean_object* v_s_2295_, lean_object* v_pos_2296_){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2297_ = lean_unsigned_to_nat(0u);
v___x_2298_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2295_, v_pos_2296_, v___x_2297_, v___x_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos___boxed(lean_object* v_s_2299_, lean_object* v_pos_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_String_offsetOfPos(v_s_2299_, v_pos_2300_);
lean_dec(v_pos_2300_);
lean_dec_ref(v_s_2299_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* lean_string_offsetofpos(lean_object* v_s_2302_, lean_object* v_pos_2303_){
_start:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2304_ = lean_unsigned_to_nat(0u);
v___x_2305_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2302_, v_pos_2303_, v___x_2304_, v___x_2304_);
lean_dec(v_pos_2303_);
lean_dec_ref(v_s_2302_);
return v___x_2305_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(lean_object* v_s1_2306_, lean_object* v_s2_2307_, lean_object* v_off1_2308_, lean_object* v_off2_2309_, lean_object* v_stop1_2310_){
_start:
{
lean_object* v___y_2312_; lean_object* v___y_2313_; uint8_t v___x_2316_; 
v___x_2316_ = lean_nat_dec_lt(v_off1_2308_, v_stop1_2310_);
if (v___x_2316_ == 0)
{
uint8_t v___x_2317_; 
lean_dec(v_off2_2309_);
lean_dec(v_off1_2308_);
v___x_2317_ = 1;
return v___x_2317_;
}
else
{
uint32_t v_c_u2081_2318_; uint32_t v_c_u2082_2319_; lean_object* v___y_2321_; uint8_t v___x_2333_; 
v_c_u2081_2318_ = lean_string_utf8_get(v_s1_2306_, v_off1_2308_);
v_c_u2082_2319_ = lean_string_utf8_get(v_s2_2307_, v_off2_2309_);
v___x_2333_ = lean_uint32_dec_eq(v_c_u2081_2318_, v_c_u2082_2319_);
if (v___x_2333_ == 0)
{
lean_dec(v_off2_2309_);
lean_dec(v_off1_2308_);
return v___x_2333_;
}
else
{
uint32_t v___x_2334_; uint8_t v___x_2335_; 
v___x_2334_ = 127;
v___x_2335_ = lean_uint32_dec_le(v_c_u2081_2318_, v___x_2334_);
if (v___x_2335_ == 0)
{
uint32_t v___x_2336_; uint8_t v___x_2337_; 
v___x_2336_ = 2047;
v___x_2337_ = lean_uint32_dec_le(v_c_u2081_2318_, v___x_2336_);
if (v___x_2337_ == 0)
{
uint32_t v___x_2338_; uint8_t v___x_2339_; 
v___x_2338_ = 65535;
v___x_2339_ = lean_uint32_dec_le(v_c_u2081_2318_, v___x_2338_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2340_; 
v___x_2340_ = lean_unsigned_to_nat(4u);
v___y_2321_ = v___x_2340_;
goto v___jp_2320_;
}
else
{
lean_object* v___x_2341_; 
v___x_2341_ = lean_unsigned_to_nat(3u);
v___y_2321_ = v___x_2341_;
goto v___jp_2320_;
}
}
else
{
lean_object* v___x_2342_; 
v___x_2342_ = lean_unsigned_to_nat(2u);
v___y_2321_ = v___x_2342_;
goto v___jp_2320_;
}
}
else
{
lean_object* v___x_2343_; 
v___x_2343_ = lean_unsigned_to_nat(1u);
v___y_2321_ = v___x_2343_;
goto v___jp_2320_;
}
}
v___jp_2320_:
{
lean_object* v___x_2322_; uint32_t v___x_2323_; uint8_t v___x_2324_; 
v___x_2322_ = lean_nat_add(v_off1_2308_, v___y_2321_);
lean_dec(v_off1_2308_);
v___x_2323_ = 127;
v___x_2324_ = lean_uint32_dec_le(v_c_u2082_2319_, v___x_2323_);
if (v___x_2324_ == 0)
{
uint32_t v___x_2325_; uint8_t v___x_2326_; 
v___x_2325_ = 2047;
v___x_2326_ = lean_uint32_dec_le(v_c_u2082_2319_, v___x_2325_);
if (v___x_2326_ == 0)
{
uint32_t v___x_2327_; uint8_t v___x_2328_; 
v___x_2327_ = 65535;
v___x_2328_ = lean_uint32_dec_le(v_c_u2082_2319_, v___x_2327_);
if (v___x_2328_ == 0)
{
lean_object* v___x_2329_; 
v___x_2329_ = lean_unsigned_to_nat(4u);
v___y_2312_ = v___x_2322_;
v___y_2313_ = v___x_2329_;
goto v___jp_2311_;
}
else
{
lean_object* v___x_2330_; 
v___x_2330_ = lean_unsigned_to_nat(3u);
v___y_2312_ = v___x_2322_;
v___y_2313_ = v___x_2330_;
goto v___jp_2311_;
}
}
else
{
lean_object* v___x_2331_; 
v___x_2331_ = lean_unsigned_to_nat(2u);
v___y_2312_ = v___x_2322_;
v___y_2313_ = v___x_2331_;
goto v___jp_2311_;
}
}
else
{
lean_object* v___x_2332_; 
v___x_2332_ = lean_unsigned_to_nat(1u);
v___y_2312_ = v___x_2322_;
v___y_2313_ = v___x_2332_;
goto v___jp_2311_;
}
}
}
v___jp_2311_:
{
lean_object* v___x_2314_; 
v___x_2314_ = lean_nat_add(v_off2_2309_, v___y_2313_);
lean_dec(v_off2_2309_);
v_off1_2308_ = v___y_2312_;
v_off2_2309_ = v___x_2314_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop___boxed(lean_object* v_s1_2344_, lean_object* v_s2_2345_, lean_object* v_off1_2346_, lean_object* v_off2_2347_, lean_object* v_stop1_2348_){
_start:
{
uint8_t v_res_2349_; lean_object* v_r_2350_; 
v_res_2349_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2344_, v_s2_2345_, v_off1_2346_, v_off2_2347_, v_stop1_2348_);
lean_dec(v_stop1_2348_);
lean_dec_ref(v_s2_2345_);
lean_dec_ref(v_s1_2344_);
v_r_2350_ = lean_box(v_res_2349_);
return v_r_2350_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_substrEq(lean_object* v_s1_2351_, lean_object* v_pos1_2352_, lean_object* v_s2_2353_, lean_object* v_pos2_2354_, lean_object* v_sz_2355_){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; uint8_t v___x_2358_; 
v___x_2356_ = lean_nat_add(v_pos1_2352_, v_sz_2355_);
v___x_2357_ = lean_string_utf8_byte_size(v_s1_2351_);
v___x_2358_ = lean_nat_dec_le(v___x_2356_, v___x_2357_);
if (v___x_2358_ == 0)
{
lean_dec(v___x_2356_);
lean_dec(v_pos2_2354_);
lean_dec(v_pos1_2352_);
return v___x_2358_;
}
else
{
lean_object* v___x_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; 
v___x_2359_ = lean_nat_add(v_pos2_2354_, v_sz_2355_);
v___x_2360_ = lean_string_utf8_byte_size(v_s2_2353_);
v___x_2361_ = lean_nat_dec_le(v___x_2359_, v___x_2360_);
lean_dec(v___x_2359_);
if (v___x_2361_ == 0)
{
lean_dec(v___x_2356_);
lean_dec(v_pos2_2354_);
lean_dec(v_pos1_2352_);
return v___x_2361_;
}
else
{
uint8_t v___x_2362_; 
v___x_2362_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2351_, v_s2_2353_, v_pos1_2352_, v_pos2_2354_, v___x_2356_);
lean_dec(v___x_2356_);
return v___x_2362_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_substrEq___boxed(lean_object* v_s1_2363_, lean_object* v_pos1_2364_, lean_object* v_s2_2365_, lean_object* v_pos2_2366_, lean_object* v_sz_2367_){
_start:
{
uint8_t v_res_2368_; lean_object* v_r_2369_; 
v_res_2368_ = l_String_Pos_Raw_substrEq(v_s1_2363_, v_pos1_2364_, v_s2_2365_, v_pos2_2366_, v_sz_2367_);
lean_dec(v_sz_2367_);
lean_dec_ref(v_s2_2365_);
lean_dec_ref(v_s1_2363_);
v_r_2369_ = lean_box(v_res_2368_);
return v_r_2369_;
}
}
LEAN_EXPORT uint8_t l_String_substrEq(lean_object* v_s1_2370_, lean_object* v_pos1_2371_, lean_object* v_s2_2372_, lean_object* v_pos2_2373_, lean_object* v_sz_2374_){
_start:
{
uint8_t v___x_2375_; 
v___x_2375_ = l_String_Pos_Raw_substrEq(v_s1_2370_, v_pos1_2371_, v_s2_2372_, v_pos2_2373_, v_sz_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_String_substrEq___boxed(lean_object* v_s1_2376_, lean_object* v_pos1_2377_, lean_object* v_s2_2378_, lean_object* v_pos2_2379_, lean_object* v_sz_2380_){
_start:
{
uint8_t v_res_2381_; lean_object* v_r_2382_; 
v_res_2381_ = l_String_substrEq(v_s1_2376_, v_pos1_2377_, v_s2_2378_, v_pos2_2379_, v_sz_2380_);
lean_dec(v_sz_2380_);
lean_dec_ref(v_s2_2378_);
lean_dec_ref(v_s1_2376_);
v_r_2382_ = lean_box(v_res_2381_);
return v_r_2382_;
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
