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
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_pos_x21_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_pos_x21_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_pos_x21_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_String_Slice_Pos_next_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "String.Slice.Pos.next!"};
static const lean_object* l_String_Slice_Pos_next_x21___closed__0 = (const lean_object*)&l_String_Slice_Pos_next_x21___closed__0_value;
static const lean_string_object l_String_Slice_Pos_next_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Cannot advance the end position"};
static const lean_object* l_String_Slice_Pos_next_x21___closed__1 = (const lean_object*)&l_String_Slice_Pos_next_x21___closed__1_value;
static lean_once_cell_t l_String_Slice_Pos_next_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_Pos_next_x21___closed__2;
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_next_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_next_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_next_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_next_x21___boxed(lean_object*, lean_object*);
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
v___x_774_ = lean_unsigned_to_nat(1080u);
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
v___x_866_ = lean_unsigned_to_nat(1165u);
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
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg(lean_object* v_s_1080_, lean_object* v_off_1081_){
_start:
{
lean_object* v_str_1082_; lean_object* v_startInclusive_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; uint8_t v___x_1086_; uint8_t v___x_1087_; uint8_t v___x_1088_; uint8_t v___x_1089_; 
v_str_1082_ = lean_ctor_get(v_s_1080_, 0);
v_startInclusive_1083_ = lean_ctor_get(v_s_1080_, 1);
v___x_1084_ = lean_nat_add(v_startInclusive_1083_, v_off_1081_);
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
uint8_t v___x_1097_; uint8_t v___x_1098_; uint8_t v___x_1099_; 
v___x_1097_ = 248;
v___x_1098_ = lean_uint8_land(v___x_1085_, v___x_1097_);
v___x_1099_ = lean_uint8_dec_eq(v___x_1098_, v___x_1094_);
if (v___x_1099_ == 0)
{
lean_object* v_zero_1100_; uint8_t v_isZero_1101_; lean_object* v_one_1102_; lean_object* v_n_1103_; 
v_zero_1100_ = lean_unsigned_to_nat(0u);
v_isZero_1101_ = lean_nat_dec_eq(v_off_1081_, v_zero_1100_);
v_one_1102_ = lean_unsigned_to_nat(1u);
v_n_1103_ = lean_nat_sub(v_off_1081_, v_one_1102_);
lean_dec(v_off_1081_);
v_off_1081_ = v_n_1103_;
goto _start;
}
else
{
return v_off_1081_;
}
}
else
{
return v_off_1081_;
}
}
else
{
return v_off_1081_;
}
}
else
{
return v_off_1081_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg___boxed(lean_object* v_s_1105_, lean_object* v_off_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1105_, v_off_1106_);
lean_dec_ref(v_s_1105_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go(lean_object* v_s_1108_, lean_object* v_off_1109_, lean_object* v_h_u2081_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1108_, v_off_1109_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___boxed(lean_object* v_s_1112_, lean_object* v_off_1113_, lean_object* v_h_u2081_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_String_Slice_Pos_prevAux_go(v_s_1112_, v_off_1113_, v_h_u2081_1114_);
lean_dec_ref(v_s_1112_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg(lean_object* v_s_1116_, lean_object* v_pos_1117_){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = lean_unsigned_to_nat(1u);
v___x_1119_ = lean_nat_sub(v_pos_1117_, v___x_1118_);
v___x_1120_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1116_, v___x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg___boxed(lean_object* v_s_1121_, lean_object* v_pos_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_String_Slice_Pos_prevAux___redArg(v_s_1121_, v_pos_1122_);
lean_dec(v_pos_1122_);
lean_dec_ref(v_s_1121_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux(lean_object* v_s_1124_, lean_object* v_pos_1125_, lean_object* v_h_1126_){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = lean_unsigned_to_nat(1u);
v___x_1128_ = lean_nat_sub(v_pos_1125_, v___x_1127_);
v___x_1129_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1124_, v___x_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___boxed(lean_object* v_s_1130_, lean_object* v_pos_1131_, lean_object* v_h_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_String_Slice_Pos_prevAux(v_s_1130_, v_pos_1131_, v_h_1132_);
lean_dec(v_pos_1131_);
lean_dec_ref(v_s_1130_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(lean_object* v_off_1134_, lean_object* v_h__1_1135_, lean_object* v_h__2_1136_){
_start:
{
lean_object* v_zero_1137_; uint8_t v_isZero_1138_; 
v_zero_1137_ = lean_unsigned_to_nat(0u);
v_isZero_1138_ = lean_nat_dec_eq(v_off_1134_, v_zero_1137_);
if (v_isZero_1138_ == 1)
{
lean_object* v___x_1139_; 
lean_dec(v_h__2_1136_);
v___x_1139_ = lean_apply_3(v_h__1_1135_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1139_;
}
else
{
lean_object* v_one_1140_; lean_object* v_n_1141_; lean_object* v___x_1142_; 
lean_dec(v_h__1_1135_);
v_one_1140_ = lean_unsigned_to_nat(1u);
v_n_1141_ = lean_nat_sub(v_off_1134_, v_one_1140_);
v___x_1142_ = lean_apply_4(v_h__2_1136_, v_n_1141_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg___boxed(lean_object* v_off_1143_, lean_object* v_h__1_1144_, lean_object* v_h__2_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(v_off_1143_, v_h__1_1144_, v_h__2_1145_);
lean_dec(v_off_1143_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(lean_object* v_s_1147_, lean_object* v_motive_1148_, lean_object* v_off_1149_, lean_object* v_h_u2081_1150_, lean_object* v_hbyte_1151_, lean_object* v_this_1152_, lean_object* v_h__1_1153_, lean_object* v_h__2_1154_){
_start:
{
lean_object* v_zero_1155_; uint8_t v_isZero_1156_; 
v_zero_1155_ = lean_unsigned_to_nat(0u);
v_isZero_1156_ = lean_nat_dec_eq(v_off_1149_, v_zero_1155_);
if (v_isZero_1156_ == 1)
{
lean_object* v___x_1157_; 
lean_dec(v_h__2_1154_);
v___x_1157_ = lean_apply_3(v_h__1_1153_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1157_;
}
else
{
lean_object* v_one_1158_; lean_object* v_n_1159_; lean_object* v___x_1160_; 
lean_dec(v_h__1_1153_);
v_one_1158_ = lean_unsigned_to_nat(1u);
v_n_1159_ = lean_nat_sub(v_off_1149_, v_one_1158_);
v___x_1160_ = lean_apply_4(v_h__2_1154_, v_n_1159_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___boxed(lean_object* v_s_1161_, lean_object* v_motive_1162_, lean_object* v_off_1163_, lean_object* v_h_u2081_1164_, lean_object* v_hbyte_1165_, lean_object* v_this_1166_, lean_object* v_h__1_1167_, lean_object* v_h__2_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(v_s_1161_, v_motive_1162_, v_off_1163_, v_h_u2081_1164_, v_hbyte_1165_, v_this_1166_, v_h__1_1167_, v_h__2_1168_);
lean_dec(v_off_1163_);
lean_dec_ref(v_s_1161_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg(lean_object* v_off_1170_){
_start:
{
lean_inc(v_off_1170_);
return v_off_1170_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg___boxed(lean_object* v_off_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_String_Slice_pos___redArg(v_off_1171_);
lean_dec(v_off_1171_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos(lean_object* v_s_1173_, lean_object* v_off_1174_, lean_object* v_h_1175_){
_start:
{
lean_inc(v_off_1174_);
return v_off_1174_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___boxed(lean_object* v_s_1176_, lean_object* v_off_1177_, lean_object* v_h_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_String_Slice_pos(v_s_1176_, v_off_1177_, v_h_1178_);
lean_dec(v_off_1177_);
lean_dec_ref(v_s_1176_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f(lean_object* v_s_1180_, lean_object* v_off_1181_){
_start:
{
uint8_t v___x_1182_; 
v___x_1182_ = l_String_Pos_Raw_isValidForSlice(v_s_1180_, v_off_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; 
lean_dec(v_off_1181_);
v___x_1183_ = lean_box(0);
return v___x_1183_;
}
else
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1184_, 0, v_off_1181_);
return v___x_1184_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f___boxed(lean_object* v_s_1185_, lean_object* v_off_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_String_Slice_pos_x3f(v_s_1185_, v_off_1186_);
lean_dec_ref(v_s_1185_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_pos_x21_spec__0___redArg(lean_object* v_msg_1188_){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = lean_unsigned_to_nat(0u);
v___x_1190_ = lean_panic_fn_borrowed(v___x_1189_, v_msg_1188_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_pos_x21_spec__0(lean_object* v_s_1191_, lean_object* v_msg_1192_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_panic___at___00String_Slice_pos_x21_spec__0___redArg(v_msg_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_pos_x21_spec__0___boxed(lean_object* v_s_1194_, lean_object* v_msg_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_panic___at___00String_Slice_pos_x21_spec__0(v_s_1194_, v_msg_1195_);
lean_dec_ref(v_s_1194_);
return v_res_1196_;
}
}
static lean_object* _init_l_String_Slice_pos_x21___closed__2(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1199_ = ((lean_object*)(l_String_Slice_pos_x21___closed__1));
v___x_1200_ = lean_unsigned_to_nat(4u);
v___x_1201_ = lean_unsigned_to_nat(1628u);
v___x_1202_ = ((lean_object*)(l_String_Slice_pos_x21___closed__0));
v___x_1203_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1204_ = l_mkPanicMessageWithDecl(v___x_1203_, v___x_1202_, v___x_1201_, v___x_1200_, v___x_1199_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21(lean_object* v_s_1205_, lean_object* v_off_1206_){
_start:
{
uint8_t v___x_1207_; 
v___x_1207_ = l_String_Pos_Raw_isValidForSlice(v_s_1205_, v_off_1206_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = lean_obj_once(&l_String_Slice_pos_x21___closed__2, &l_String_Slice_pos_x21___closed__2_once, _init_l_String_Slice_pos_x21___closed__2);
v___x_1209_ = l_panic___at___00String_Slice_pos_x21_spec__0___redArg(v___x_1208_);
return v___x_1209_;
}
else
{
lean_inc(v_off_1206_);
return v_off_1206_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21___boxed(lean_object* v_s_1210_, lean_object* v_off_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_String_Slice_pos_x21(v_s_1210_, v_off_1211_);
lean_dec(v_off_1211_);
lean_dec_ref(v_s_1210_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next___boxed(lean_object* v_s_1216_, lean_object* v_pos_1217_, lean_object* v_h_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = lean_string_utf8_next_fast(v_s_1216_, v_pos_1217_);
lean_dec(v_pos_1217_);
lean_dec_ref(v_s_1216_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg(lean_object* v_off_1220_){
_start:
{
lean_inc(v_off_1220_);
return v_off_1220_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg___boxed(lean_object* v_off_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_String_pos___redArg(v_off_1221_);
lean_dec(v_off_1221_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_String_pos(lean_object* v_s_1223_, lean_object* v_off_1224_, lean_object* v_h_1225_){
_start:
{
lean_inc(v_off_1224_);
return v_off_1224_;
}
}
LEAN_EXPORT lean_object* l_String_pos___boxed(lean_object* v_s_1226_, lean_object* v_off_1227_, lean_object* v_h_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_String_pos(v_s_1226_, v_off_1227_, v_h_1228_);
lean_dec(v_off_1227_);
lean_dec_ref(v_s_1226_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x3f(lean_object* v_s_1230_, lean_object* v_off_1231_){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1232_ = lean_unsigned_to_nat(0u);
v___x_1233_ = lean_string_utf8_byte_size(v_s_1230_);
v___x_1234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1234_, 0, v_s_1230_);
lean_ctor_set(v___x_1234_, 1, v___x_1232_);
lean_ctor_set(v___x_1234_, 2, v___x_1233_);
v___x_1235_ = l_String_Slice_pos_x3f(v___x_1234_, v_off_1231_);
lean_dec_ref_known(v___x_1234_, 3);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v___x_1236_; 
v___x_1236_ = lean_box(0);
return v___x_1236_;
}
else
{
lean_object* v_val_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
v_val_1237_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1235_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_val_1237_);
lean_dec(v___x_1235_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_val_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_pos_x21(lean_object* v_s_1245_, lean_object* v_off_1246_){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1247_ = lean_unsigned_to_nat(0u);
v___x_1248_ = lean_string_utf8_byte_size(v_s_1245_);
v___x_1249_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1249_, 0, v_s_1245_);
lean_ctor_set(v___x_1249_, 1, v___x_1247_);
lean_ctor_set(v___x_1249_, 2, v___x_1248_);
v___x_1250_ = l_String_Slice_pos_x21(v___x_1249_, v_off_1246_);
lean_dec_ref_known(v___x_1249_, 3);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x21___boxed(lean_object* v_s_1251_, lean_object* v_off_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_String_pos_x21(v_s_1251_, v_off_1252_);
lean_dec(v_off_1252_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg(lean_object* v_pos_1254_){
_start:
{
lean_inc(v_pos_1254_);
return v_pos_1254_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg___boxed(lean_object* v_pos_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_String_Slice_Pos_cast___redArg(v_pos_1255_);
lean_dec(v_pos_1255_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast(lean_object* v_s_1257_, lean_object* v_t_1258_, lean_object* v_pos_1259_, lean_object* v_h_1260_){
_start:
{
lean_inc(v_pos_1259_);
return v_pos_1259_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___boxed(lean_object* v_s_1261_, lean_object* v_t_1262_, lean_object* v_pos_1263_, lean_object* v_h_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_String_Slice_Pos_cast(v_s_1261_, v_t_1262_, v_pos_1263_, v_h_1264_);
lean_dec(v_pos_1263_);
lean_dec_ref(v_t_1262_);
lean_dec_ref(v_s_1261_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg(lean_object* v_pos_1266_){
_start:
{
lean_inc(v_pos_1266_);
return v_pos_1266_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg___boxed(lean_object* v_pos_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_String_Pos_cast___redArg(v_pos_1267_);
lean_dec(v_pos_1267_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast(lean_object* v_s_1269_, lean_object* v_t_1270_, lean_object* v_pos_1271_, lean_object* v_h_1272_){
_start:
{
lean_inc(v_pos_1271_);
return v_pos_1271_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___boxed(lean_object* v_s_1273_, lean_object* v_t_1274_, lean_object* v_pos_1275_, lean_object* v_h_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_String_Pos_cast(v_s_1273_, v_t_1274_, v_pos_1275_, v_h_1276_);
lean_dec(v_pos_1275_);
lean_dec_ref(v_t_1274_);
lean_dec_ref(v_s_1273_);
return v_res_1277_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_Raw_utf8GetAux(lean_object* v_x_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_){
_start:
{
if (lean_obj_tag(v_x_1278_) == 0)
{
uint32_t v___x_1281_; 
lean_dec(v_x_1279_);
v___x_1281_ = 65;
return v___x_1281_;
}
else
{
lean_object* v_head_1282_; lean_object* v_tail_1283_; lean_object* v___y_1285_; uint8_t v_decide_1288_; 
v_head_1282_ = lean_ctor_get(v_x_1278_, 0);
v_tail_1283_ = lean_ctor_get(v_x_1278_, 1);
v_decide_1288_ = lean_nat_dec_eq(v_x_1279_, v_x_1280_);
if (v_decide_1288_ == 0)
{
uint32_t v___x_1289_; uint32_t v___x_1290_; uint8_t v___x_1291_; 
v___x_1289_ = 127;
v___x_1290_ = lean_unbox_uint32(v_head_1282_);
v___x_1291_ = lean_uint32_dec_le(v___x_1290_, v___x_1289_);
if (v___x_1291_ == 0)
{
uint32_t v___x_1292_; uint32_t v___x_1293_; uint8_t v___x_1294_; 
v___x_1292_ = 2047;
v___x_1293_ = lean_unbox_uint32(v_head_1282_);
v___x_1294_ = lean_uint32_dec_le(v___x_1293_, v___x_1292_);
if (v___x_1294_ == 0)
{
uint32_t v___x_1295_; uint32_t v___x_1296_; uint8_t v___x_1297_; 
v___x_1295_ = 65535;
v___x_1296_ = lean_unbox_uint32(v_head_1282_);
v___x_1297_ = lean_uint32_dec_le(v___x_1296_, v___x_1295_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; 
v___x_1298_ = lean_unsigned_to_nat(4u);
v___y_1285_ = v___x_1298_;
goto v___jp_1284_;
}
else
{
lean_object* v___x_1299_; 
v___x_1299_ = lean_unsigned_to_nat(3u);
v___y_1285_ = v___x_1299_;
goto v___jp_1284_;
}
}
else
{
lean_object* v___x_1300_; 
v___x_1300_ = lean_unsigned_to_nat(2u);
v___y_1285_ = v___x_1300_;
goto v___jp_1284_;
}
}
else
{
lean_object* v___x_1301_; 
v___x_1301_ = lean_unsigned_to_nat(1u);
v___y_1285_ = v___x_1301_;
goto v___jp_1284_;
}
}
else
{
uint32_t v___x_1302_; 
lean_dec(v_x_1279_);
v___x_1302_ = lean_unbox_uint32(v_head_1282_);
return v___x_1302_;
}
v___jp_1284_:
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_nat_add(v_x_1279_, v___y_1285_);
lean_dec(v_x_1279_);
v_x_1278_ = v_tail_1283_;
v_x_1279_ = v___x_1286_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux___boxed(lean_object* v_x_1303_, lean_object* v_x_1304_, lean_object* v_x_1305_){
_start:
{
uint32_t v_res_1306_; lean_object* v_r_1307_; 
v_res_1306_ = l_String_Pos_Raw_utf8GetAux(v_x_1303_, v_x_1304_, v_x_1305_);
lean_dec(v_x_1305_);
lean_dec(v_x_1303_);
v_r_1307_ = lean_box_uint32(v_res_1306_);
return v_r_1307_;
}
}
LEAN_EXPORT uint32_t l_String_utf8GetAux(lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
uint32_t v___x_1311_; 
v___x_1311_ = l_String_Pos_Raw_utf8GetAux(v_a_1308_, v_a_1309_, v_a_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux___boxed(lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
uint32_t v_res_1315_; lean_object* v_r_1316_; 
v_res_1315_ = l_String_utf8GetAux(v_a_1312_, v_a_1313_, v_a_1314_);
lean_dec(v_a_1314_);
lean_dec(v_a_1312_);
v_r_1316_ = lean_box_uint32(v_res_1315_);
return v_r_1316_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get___boxed(lean_object* v_s_1319_, lean_object* v_p_1320_){
_start:
{
uint32_t v_res_1321_; lean_object* v_r_1322_; 
v_res_1321_ = lean_string_utf8_get(v_s_1319_, v_p_1320_);
lean_dec(v_p_1320_);
lean_dec_ref(v_s_1319_);
v_r_1322_ = lean_box_uint32(v_res_1321_);
return v_r_1322_;
}
}
LEAN_EXPORT lean_object* l_String_get___boxed(lean_object* v_s_1325_, lean_object* v_p_1326_){
_start:
{
uint32_t v_res_1327_; lean_object* v_r_1328_; 
v_res_1327_ = lean_string_utf8_get(v_s_1325_, v_p_1326_);
lean_dec(v_p_1326_);
lean_dec_ref(v_s_1325_);
v_r_1328_ = lean_box_uint32(v_res_1327_);
return v_r_1328_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f(lean_object* v_x_1329_, lean_object* v_x_1330_, lean_object* v_x_1331_){
_start:
{
if (lean_obj_tag(v_x_1329_) == 0)
{
lean_object* v___x_1332_; 
lean_dec(v_x_1330_);
v___x_1332_ = lean_box(0);
return v___x_1332_;
}
else
{
lean_object* v_head_1333_; lean_object* v_tail_1334_; lean_object* v___y_1336_; uint8_t v_decide_1339_; 
v_head_1333_ = lean_ctor_get(v_x_1329_, 0);
v_tail_1334_ = lean_ctor_get(v_x_1329_, 1);
v_decide_1339_ = lean_nat_dec_eq(v_x_1330_, v_x_1331_);
if (v_decide_1339_ == 0)
{
uint32_t v___x_1340_; uint32_t v___x_1341_; uint8_t v___x_1342_; 
v___x_1340_ = 127;
v___x_1341_ = lean_unbox_uint32(v_head_1333_);
v___x_1342_ = lean_uint32_dec_le(v___x_1341_, v___x_1340_);
if (v___x_1342_ == 0)
{
uint32_t v___x_1343_; uint32_t v___x_1344_; uint8_t v___x_1345_; 
v___x_1343_ = 2047;
v___x_1344_ = lean_unbox_uint32(v_head_1333_);
v___x_1345_ = lean_uint32_dec_le(v___x_1344_, v___x_1343_);
if (v___x_1345_ == 0)
{
uint32_t v___x_1346_; uint32_t v___x_1347_; uint8_t v___x_1348_; 
v___x_1346_ = 65535;
v___x_1347_ = lean_unbox_uint32(v_head_1333_);
v___x_1348_ = lean_uint32_dec_le(v___x_1347_, v___x_1346_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_unsigned_to_nat(4u);
v___y_1336_ = v___x_1349_;
goto v___jp_1335_;
}
else
{
lean_object* v___x_1350_; 
v___x_1350_ = lean_unsigned_to_nat(3u);
v___y_1336_ = v___x_1350_;
goto v___jp_1335_;
}
}
else
{
lean_object* v___x_1351_; 
v___x_1351_ = lean_unsigned_to_nat(2u);
v___y_1336_ = v___x_1351_;
goto v___jp_1335_;
}
}
else
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_unsigned_to_nat(1u);
v___y_1336_ = v___x_1352_;
goto v___jp_1335_;
}
}
else
{
lean_object* v___x_1353_; 
lean_dec(v_x_1330_);
lean_inc(v_head_1333_);
v___x_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1353_, 0, v_head_1333_);
return v___x_1353_;
}
v___jp_1335_:
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_nat_add(v_x_1330_, v___y_1336_);
lean_dec(v_x_1330_);
v_x_1329_ = v_tail_1334_;
v_x_1330_ = v___x_1337_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f___boxed(lean_object* v_x_1354_, lean_object* v_x_1355_, lean_object* v_x_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_String_Pos_Raw_utf8GetAux_x3f(v_x_1354_, v_x_1355_, v_x_1356_);
lean_dec(v_x_1356_);
lean_dec(v_x_1354_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f(lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_String_Pos_Raw_utf8GetAux_x3f(v_a_1358_, v_a_1359_, v_a_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f___boxed(lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_String_utf8GetAux_x3f(v_a_1362_, v_a_1363_, v_a_1364_);
lean_dec(v_a_1364_);
lean_dec(v_a_1362_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1368_, lean_object* v_a_00___x40___internal___hyg_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1368_, v_a_00___x40___internal___hyg_1369_);
lean_dec(v_a_00___x40___internal___hyg_1369_);
lean_dec_ref(v_a_00___x40___internal___hyg_1368_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_String_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1373_, lean_object* v_a_00___x40___internal___hyg_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1373_, v_a_00___x40___internal___hyg_1374_);
lean_dec(v_a_00___x40___internal___hyg_1374_);
lean_dec_ref(v_a_00___x40___internal___hyg_1373_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x21___boxed(lean_object* v_s_1378_, lean_object* v_p_1379_){
_start:
{
uint32_t v_res_1380_; lean_object* v_r_1381_; 
v_res_1380_ = lean_string_utf8_get_bang(v_s_1378_, v_p_1379_);
lean_dec(v_p_1379_);
lean_dec_ref(v_s_1378_);
v_r_1381_ = lean_box_uint32(v_res_1380_);
return v_r_1381_;
}
}
LEAN_EXPORT lean_object* l_String_get_x21___boxed(lean_object* v_s_1384_, lean_object* v_p_1385_){
_start:
{
uint32_t v_res_1386_; lean_object* v_r_1387_; 
v_res_1386_ = lean_string_utf8_get_bang(v_s_1384_, v_p_1385_);
lean_dec(v_p_1385_);
lean_dec_ref(v_s_1384_);
v_r_1387_ = lean_box_uint32(v_res_1386_);
return v_r_1387_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux(uint32_t v_c_x27_1388_, lean_object* v_x_1389_, lean_object* v_x_1390_, lean_object* v_x_1391_){
_start:
{
if (lean_obj_tag(v_x_1389_) == 0)
{
return v_x_1389_;
}
else
{
lean_object* v_head_1392_; lean_object* v_tail_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1420_; 
v_head_1392_ = lean_ctor_get(v_x_1389_, 0);
v_tail_1393_ = lean_ctor_get(v_x_1389_, 1);
v_isSharedCheck_1420_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1395_ = v_x_1389_;
v_isShared_1396_ = v_isSharedCheck_1420_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_tail_1393_);
lean_inc(v_head_1392_);
lean_dec(v_x_1389_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1420_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___y_1398_; uint8_t v_decide_1404_; 
v_decide_1404_ = lean_nat_dec_eq(v_x_1390_, v_x_1391_);
if (v_decide_1404_ == 0)
{
uint32_t v___x_1405_; uint32_t v___x_1406_; uint8_t v___x_1407_; 
v___x_1405_ = 127;
v___x_1406_ = lean_unbox_uint32(v_head_1392_);
v___x_1407_ = lean_uint32_dec_le(v___x_1406_, v___x_1405_);
if (v___x_1407_ == 0)
{
uint32_t v___x_1408_; uint32_t v___x_1409_; uint8_t v___x_1410_; 
v___x_1408_ = 2047;
v___x_1409_ = lean_unbox_uint32(v_head_1392_);
v___x_1410_ = lean_uint32_dec_le(v___x_1409_, v___x_1408_);
if (v___x_1410_ == 0)
{
uint32_t v___x_1411_; uint32_t v___x_1412_; uint8_t v___x_1413_; 
v___x_1411_ = 65535;
v___x_1412_ = lean_unbox_uint32(v_head_1392_);
v___x_1413_ = lean_uint32_dec_le(v___x_1412_, v___x_1411_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; 
v___x_1414_ = lean_unsigned_to_nat(4u);
v___y_1398_ = v___x_1414_;
goto v___jp_1397_;
}
else
{
lean_object* v___x_1415_; 
v___x_1415_ = lean_unsigned_to_nat(3u);
v___y_1398_ = v___x_1415_;
goto v___jp_1397_;
}
}
else
{
lean_object* v___x_1416_; 
v___x_1416_ = lean_unsigned_to_nat(2u);
v___y_1398_ = v___x_1416_;
goto v___jp_1397_;
}
}
else
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_unsigned_to_nat(1u);
v___y_1398_ = v___x_1417_;
goto v___jp_1397_;
}
}
else
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
lean_del_object(v___x_1395_);
lean_dec(v_head_1392_);
v___x_1418_ = lean_box_uint32(v_c_x27_1388_);
v___x_1419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
lean_ctor_set(v___x_1419_, 1, v_tail_1393_);
return v___x_1419_;
}
v___jp_1397_:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1399_ = lean_nat_add(v_x_1390_, v___y_1398_);
v___x_1400_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1388_, v_tail_1393_, v___x_1399_, v_x_1391_);
lean_dec(v___x_1399_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 1, v___x_1400_);
v___x_1402_ = v___x_1395_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_head_1392_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux___boxed(lean_object* v_c_x27_1421_, lean_object* v_x_1422_, lean_object* v_x_1423_, lean_object* v_x_1424_){
_start:
{
uint32_t v_c_x27_boxed_1425_; lean_object* v_res_1426_; 
v_c_x27_boxed_1425_ = lean_unbox_uint32(v_c_x27_1421_);
lean_dec(v_c_x27_1421_);
v_res_1426_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_boxed_1425_, v_x_1422_, v_x_1423_, v_x_1424_);
lean_dec(v_x_1424_);
lean_dec(v_x_1423_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux(uint32_t v_c_x27_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux___boxed(lean_object* v_c_x27_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_){
_start:
{
uint32_t v_c_x27_boxed_1436_; lean_object* v_res_1437_; 
v_c_x27_boxed_1436_ = lean_unbox_uint32(v_c_x27_1432_);
lean_dec(v_c_x27_1432_);
v_res_1437_ = l_String_utf8SetAux(v_c_x27_boxed_1436_, v_a_1433_, v_a_1434_, v_a_1435_);
lean_dec(v_a_1435_);
lean_dec(v_a_1434_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg(lean_object* v_s_1438_, lean_object* v_pos_1439_){
_start:
{
lean_object* v_str_1440_; lean_object* v_startInclusive_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v_str_1440_ = lean_ctor_get(v_s_1438_, 0);
v_startInclusive_1441_ = lean_ctor_get(v_s_1438_, 1);
v___x_1442_ = lean_nat_add(v_startInclusive_1441_, v_pos_1439_);
v___x_1443_ = lean_string_utf8_next_fast(v_str_1440_, v___x_1442_);
lean_dec(v___x_1442_);
v___x_1444_ = lean_nat_sub(v___x_1443_, v_startInclusive_1441_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg___boxed(lean_object* v_s_1445_, lean_object* v_pos_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_String_Slice_Pos_nextFast___redArg(v_s_1445_, v_pos_1446_);
lean_dec(v_pos_1446_);
lean_dec_ref(v_s_1445_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast(lean_object* v_s_1448_, lean_object* v_pos_1449_, lean_object* v_h_1450_){
_start:
{
lean_object* v_str_1451_; lean_object* v_startInclusive_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v_str_1451_ = lean_ctor_get(v_s_1448_, 0);
v_startInclusive_1452_ = lean_ctor_get(v_s_1448_, 1);
v___x_1453_ = lean_nat_add(v_startInclusive_1452_, v_pos_1449_);
v___x_1454_ = lean_string_utf8_next_fast(v_str_1451_, v___x_1453_);
lean_dec(v___x_1453_);
v___x_1455_ = lean_nat_sub(v___x_1454_, v_startInclusive_1452_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___boxed(lean_object* v_s_1456_, lean_object* v_pos_1457_, lean_object* v_h_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_String_Slice_Pos_nextFast(v_s_1456_, v_pos_1457_, v_h_1458_);
lean_dec(v_pos_1457_);
lean_dec_ref(v_s_1456_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f(lean_object* v_s_1460_, lean_object* v_pos_1461_){
_start:
{
lean_object* v_str_1462_; lean_object* v_startInclusive_1463_; lean_object* v_endExclusive_1464_; lean_object* v___x_1465_; uint8_t v_decide_1466_; 
v_str_1462_ = lean_ctor_get(v_s_1460_, 0);
v_startInclusive_1463_ = lean_ctor_get(v_s_1460_, 1);
v_endExclusive_1464_ = lean_ctor_get(v_s_1460_, 2);
v___x_1465_ = lean_nat_sub(v_endExclusive_1464_, v_startInclusive_1463_);
v_decide_1466_ = lean_nat_dec_eq(v_pos_1461_, v___x_1465_);
lean_dec(v___x_1465_);
if (v_decide_1466_ == 0)
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1467_ = lean_nat_add(v_startInclusive_1463_, v_pos_1461_);
v___x_1468_ = lean_string_utf8_next_fast(v_str_1462_, v___x_1467_);
lean_dec(v___x_1467_);
v___x_1469_ = lean_nat_sub(v___x_1468_, v_startInclusive_1463_);
v___x_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
return v___x_1470_;
}
else
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_box(0);
return v___x_1471_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f___boxed(lean_object* v_s_1472_, lean_object* v_pos_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_String_Slice_Pos_next_x3f(v_s_1472_, v_pos_1473_);
lean_dec(v_pos_1473_);
lean_dec_ref(v_s_1472_);
return v_res_1474_;
}
}
static lean_object* _init_l_String_Slice_Pos_next_x21___closed__2(void){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1477_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__1));
v___x_1478_ = lean_unsigned_to_nat(29u);
v___x_1479_ = lean_unsigned_to_nat(2103u);
v___x_1480_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__0));
v___x_1481_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1482_ = l_mkPanicMessageWithDecl(v___x_1481_, v___x_1480_, v___x_1479_, v___x_1478_, v___x_1477_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21(lean_object* v_s_1483_, lean_object* v_pos_1484_){
_start:
{
lean_object* v_str_1485_; lean_object* v_startInclusive_1486_; lean_object* v_endExclusive_1487_; lean_object* v___x_1488_; uint8_t v_decide_1489_; 
v_str_1485_ = lean_ctor_get(v_s_1483_, 0);
v_startInclusive_1486_ = lean_ctor_get(v_s_1483_, 1);
v_endExclusive_1487_ = lean_ctor_get(v_s_1483_, 2);
v___x_1488_ = lean_nat_sub(v_endExclusive_1487_, v_startInclusive_1486_);
v_decide_1489_ = lean_nat_dec_eq(v_pos_1484_, v___x_1488_);
lean_dec(v___x_1488_);
if (v_decide_1489_ == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1490_ = lean_nat_add(v_startInclusive_1486_, v_pos_1484_);
v___x_1491_ = lean_string_utf8_next_fast(v_str_1485_, v___x_1490_);
lean_dec(v___x_1490_);
v___x_1492_ = lean_nat_sub(v___x_1491_, v_startInclusive_1486_);
return v___x_1492_;
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = lean_obj_once(&l_String_Slice_Pos_next_x21___closed__2, &l_String_Slice_Pos_next_x21___closed__2_once, _init_l_String_Slice_Pos_next_x21___closed__2);
v___x_1494_ = l_panic___at___00String_Slice_pos_x21_spec__0___redArg(v___x_1493_);
return v___x_1494_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21___boxed(lean_object* v_s_1495_, lean_object* v_pos_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_String_Slice_Pos_next_x21(v_s_1495_, v_pos_1496_);
lean_dec(v_pos_1496_);
lean_dec_ref(v_s_1495_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x3f(lean_object* v_s_1498_, lean_object* v_pos_1499_){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1500_ = lean_unsigned_to_nat(0u);
v___x_1501_ = lean_string_utf8_byte_size(v_s_1498_);
v___x_1502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1502_, 0, v_s_1498_);
lean_ctor_set(v___x_1502_, 1, v___x_1500_);
lean_ctor_set(v___x_1502_, 2, v___x_1501_);
v___x_1503_ = l_String_Slice_Pos_next_x3f(v___x_1502_, v_pos_1499_);
lean_dec_ref_known(v___x_1502_, 3);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_box(0);
return v___x_1504_;
}
else
{
lean_object* v_val_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
v_val_1505_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1503_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_val_1505_);
lean_dec(v___x_1503_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_val_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x3f___boxed(lean_object* v_s_1513_, lean_object* v_pos_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_String_Pos_next_x3f(v_s_1513_, v_pos_1514_);
lean_dec(v_pos_1514_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21(lean_object* v_s_1516_, lean_object* v_pos_1517_){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1518_ = lean_unsigned_to_nat(0u);
v___x_1519_ = lean_string_utf8_byte_size(v_s_1516_);
v___x_1520_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1520_, 0, v_s_1516_);
lean_ctor_set(v___x_1520_, 1, v___x_1518_);
lean_ctor_set(v___x_1520_, 2, v___x_1519_);
v___x_1521_ = l_String_Slice_Pos_next_x21(v___x_1520_, v_pos_1517_);
lean_dec_ref_known(v___x_1520_, 3);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21___boxed(lean_object* v_s_1522_, lean_object* v_pos_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_String_Pos_next_x21(v_s_1522_, v_pos_1523_);
lean_dec(v_pos_1523_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_String_sliceTo(lean_object* v_s_1525_, lean_object* v_p_1526_){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = lean_unsigned_to_nat(0u);
v___x_1528_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1528_, 0, v_s_1525_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
lean_ctor_set(v___x_1528_, 2, v_p_1526_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_String_replaceEnd(lean_object* v_s_1529_, lean_object* v_p_1530_){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = lean_unsigned_to_nat(0u);
v___x_1532_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1532_, 0, v_s_1529_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
lean_ctor_set(v___x_1532_, 2, v_p_1530_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_String_sliceFrom(lean_object* v_s_1533_, lean_object* v_p_1534_){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = lean_string_utf8_byte_size(v_s_1533_);
v___x_1536_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1536_, 0, v_s_1533_);
lean_ctor_set(v___x_1536_, 1, v_p_1534_);
lean_ctor_set(v___x_1536_, 2, v___x_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStart(lean_object* v_s_1537_, lean_object* v_p_1538_){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_string_utf8_byte_size(v_s_1537_);
v___x_1540_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1540_, 0, v_s_1537_);
lean_ctor_set(v___x_1540_, 1, v_p_1538_);
lean_ctor_set(v___x_1540_, 2, v___x_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_String_slice___redArg(lean_object* v_s_1541_, lean_object* v_startInclusive_1542_, lean_object* v_endExclusive_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1544_, 0, v_s_1541_);
lean_ctor_set(v___x_1544_, 1, v_startInclusive_1542_);
lean_ctor_set(v___x_1544_, 2, v_endExclusive_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_String_slice(lean_object* v_s_1545_, lean_object* v_startInclusive_1546_, lean_object* v_endExclusive_1547_, lean_object* v_h_1548_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1549_, 0, v_s_1545_);
lean_ctor_set(v___x_1549_, 1, v_startInclusive_1546_);
lean_ctor_set(v___x_1549_, 2, v_endExclusive_1547_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x3f(lean_object* v_s_1550_, lean_object* v_startInclusive_1551_, lean_object* v_endExclusive_1552_){
_start:
{
uint8_t v___x_1553_; 
v___x_1553_ = lean_nat_dec_le(v_startInclusive_1551_, v_endExclusive_1552_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; 
lean_dec(v_endExclusive_1552_);
lean_dec(v_startInclusive_1551_);
lean_dec_ref(v_s_1550_);
v___x_1554_ = lean_box(0);
return v___x_1554_;
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1555_, 0, v_s_1550_);
lean_ctor_set(v___x_1555_, 1, v_startInclusive_1551_);
lean_ctor_set(v___x_1555_, 2, v_endExclusive_1552_);
v___x_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
return v___x_1556_;
}
}
}
LEAN_EXPORT lean_object* l_String_slice_x21(lean_object* v_s_1557_, lean_object* v_p_u2081_1558_, lean_object* v_p_u2082_1559_){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1560_ = lean_unsigned_to_nat(0u);
v___x_1561_ = lean_string_utf8_byte_size(v_s_1557_);
v___x_1562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1562_, 0, v_s_1557_);
lean_ctor_set(v___x_1562_, 1, v___x_1560_);
lean_ctor_set(v___x_1562_, 2, v___x_1561_);
v___x_1563_ = l_String_Slice_slice_x21(v___x_1562_, v_p_u2081_1558_, v_p_u2082_1559_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x21___boxed(lean_object* v_s_1564_, lean_object* v_p_u2081_1565_, lean_object* v_p_u2082_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_String_slice_x21(v_s_1564_, v_p_u2081_1565_, v_p_u2082_1566_);
lean_dec(v_p_u2082_1566_);
lean_dec(v_p_u2081_1565_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21(lean_object* v_s_1568_, lean_object* v_p_u2081_1569_, lean_object* v_p_u2082_1570_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_String_slice_x21(v_s_1568_, v_p_u2081_1569_, v_p_u2082_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21___boxed(lean_object* v_s_1572_, lean_object* v_p_u2081_1573_, lean_object* v_p_u2082_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_String_replaceStartEnd_x21(v_s_1572_, v_p_u2081_1573_, v_p_u2082_1574_);
lean_dec(v_p_u2082_1574_);
lean_dec(v_p_u2081_1573_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg(lean_object* v_p_u2080_1576_, lean_object* v_pos_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = lean_nat_add(v_p_u2080_1576_, v_pos_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg___boxed(lean_object* v_p_u2080_1579_, lean_object* v_pos_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_String_Pos_ofSliceFrom___redArg(v_p_u2080_1579_, v_pos_1580_);
lean_dec(v_pos_1580_);
lean_dec(v_p_u2080_1579_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom(lean_object* v_s_1582_, lean_object* v_p_u2080_1583_, lean_object* v_pos_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_nat_add(v_p_u2080_1583_, v_pos_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___boxed(lean_object* v_s_1586_, lean_object* v_p_u2080_1587_, lean_object* v_pos_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_String_Pos_ofSliceFrom(v_s_1586_, v_p_u2080_1587_, v_pos_1588_);
lean_dec(v_pos_1588_);
lean_dec(v_p_u2080_1587_);
lean_dec_ref(v_s_1586_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg(lean_object* v_p_u2080_1590_, lean_object* v_pos_1591_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = lean_nat_add(v_p_u2080_1590_, v_pos_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg___boxed(lean_object* v_p_u2080_1593_, lean_object* v_pos_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_String_Pos_ofReplaceStart___redArg(v_p_u2080_1593_, v_pos_1594_);
lean_dec(v_pos_1594_);
lean_dec(v_p_u2080_1593_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart(lean_object* v_s_1596_, lean_object* v_p_u2080_1597_, lean_object* v_pos_1598_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_nat_add(v_p_u2080_1597_, v_pos_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___boxed(lean_object* v_s_1600_, lean_object* v_p_u2080_1601_, lean_object* v_pos_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_String_Pos_ofReplaceStart(v_s_1600_, v_p_u2080_1601_, v_pos_1602_);
lean_dec(v_pos_1602_);
lean_dec(v_p_u2080_1601_);
lean_dec_ref(v_s_1600_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg(lean_object* v_p_u2080_1604_, lean_object* v_pos_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = lean_nat_sub(v_pos_1605_, v_p_u2080_1604_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg___boxed(lean_object* v_p_u2080_1607_, lean_object* v_pos_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_String_Pos_sliceFrom___redArg(v_p_u2080_1607_, v_pos_1608_);
lean_dec(v_pos_1608_);
lean_dec(v_p_u2080_1607_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom(lean_object* v_s_1610_, lean_object* v_p_u2080_1611_, lean_object* v_pos_1612_, lean_object* v_h_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_nat_sub(v_pos_1612_, v_p_u2080_1611_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___boxed(lean_object* v_s_1615_, lean_object* v_p_u2080_1616_, lean_object* v_pos_1617_, lean_object* v_h_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_String_Pos_sliceFrom(v_s_1615_, v_p_u2080_1616_, v_pos_1617_, v_h_1618_);
lean_dec(v_pos_1617_);
lean_dec(v_p_u2080_1616_);
lean_dec_ref(v_s_1615_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg(lean_object* v_p_u2080_1620_, lean_object* v_pos_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_nat_sub(v_pos_1621_, v_p_u2080_1620_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg___boxed(lean_object* v_p_u2080_1623_, lean_object* v_pos_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_String_Pos_toReplaceStart___redArg(v_p_u2080_1623_, v_pos_1624_);
lean_dec(v_pos_1624_);
lean_dec(v_p_u2080_1623_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart(lean_object* v_s_1626_, lean_object* v_p_u2080_1627_, lean_object* v_pos_1628_, lean_object* v_h_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_nat_sub(v_pos_1628_, v_p_u2080_1627_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___boxed(lean_object* v_s_1631_, lean_object* v_p_u2080_1632_, lean_object* v_pos_1633_, lean_object* v_h_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_String_Pos_toReplaceStart(v_s_1631_, v_p_u2080_1632_, v_pos_1633_, v_h_1634_);
lean_dec(v_pos_1633_);
lean_dec(v_p_u2080_1632_);
lean_dec_ref(v_s_1631_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg(lean_object* v_pos_1636_){
_start:
{
lean_inc(v_pos_1636_);
return v_pos_1636_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg___boxed(lean_object* v_pos_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_String_Pos_ofSliceTo___redArg(v_pos_1637_);
lean_dec(v_pos_1637_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo(lean_object* v_s_1639_, lean_object* v_p_u2080_1640_, lean_object* v_pos_1641_){
_start:
{
lean_inc(v_pos_1641_);
return v_pos_1641_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___boxed(lean_object* v_s_1642_, lean_object* v_p_u2080_1643_, lean_object* v_pos_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_String_Pos_ofSliceTo(v_s_1642_, v_p_u2080_1643_, v_pos_1644_);
lean_dec(v_pos_1644_);
lean_dec(v_p_u2080_1643_);
lean_dec_ref(v_s_1642_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg(lean_object* v_pos_1646_){
_start:
{
lean_inc(v_pos_1646_);
return v_pos_1646_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg___boxed(lean_object* v_pos_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_String_Pos_ofReplaceEnd___redArg(v_pos_1647_);
lean_dec(v_pos_1647_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd(lean_object* v_s_1649_, lean_object* v_p_u2080_1650_, lean_object* v_pos_1651_){
_start:
{
lean_inc(v_pos_1651_);
return v_pos_1651_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___boxed(lean_object* v_s_1652_, lean_object* v_p_u2080_1653_, lean_object* v_pos_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_String_Pos_ofReplaceEnd(v_s_1652_, v_p_u2080_1653_, v_pos_1654_);
lean_dec(v_pos_1654_);
lean_dec(v_p_u2080_1653_);
lean_dec_ref(v_s_1652_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg(lean_object* v_pos_1656_){
_start:
{
lean_inc(v_pos_1656_);
return v_pos_1656_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg___boxed(lean_object* v_pos_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_String_Pos_sliceTo___redArg(v_pos_1657_);
lean_dec(v_pos_1657_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo(lean_object* v_s_1659_, lean_object* v_p_u2080_1660_, lean_object* v_pos_1661_, lean_object* v_h_1662_){
_start:
{
lean_inc(v_pos_1661_);
return v_pos_1661_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___boxed(lean_object* v_s_1663_, lean_object* v_p_u2080_1664_, lean_object* v_pos_1665_, lean_object* v_h_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_String_Pos_sliceTo(v_s_1663_, v_p_u2080_1664_, v_pos_1665_, v_h_1666_);
lean_dec(v_pos_1665_);
lean_dec(v_p_u2080_1664_);
lean_dec_ref(v_s_1663_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg(lean_object* v_pos_1668_){
_start:
{
lean_inc(v_pos_1668_);
return v_pos_1668_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg___boxed(lean_object* v_pos_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_String_Pos_toReplaceEnd___redArg(v_pos_1669_);
lean_dec(v_pos_1669_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd(lean_object* v_s_1671_, lean_object* v_p_u2080_1672_, lean_object* v_pos_1673_, lean_object* v_h_1674_){
_start:
{
lean_inc(v_pos_1673_);
return v_pos_1673_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___boxed(lean_object* v_s_1675_, lean_object* v_p_u2080_1676_, lean_object* v_pos_1677_, lean_object* v_h_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_String_Pos_toReplaceEnd(v_s_1675_, v_p_u2080_1676_, v_pos_1677_, v_h_1678_);
lean_dec(v_pos_1677_);
lean_dec(v_p_u2080_1676_);
lean_dec_ref(v_s_1675_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg(lean_object* v_p_u2080_1680_, lean_object* v_pos_1681_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_nat_add(v_p_u2080_1680_, v_pos_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1683_, lean_object* v_pos_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_String_Slice_Pos_ofSlice___redArg(v_p_u2080_1683_, v_pos_1684_);
lean_dec(v_pos_1684_);
lean_dec(v_p_u2080_1683_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice(lean_object* v_s_1686_, lean_object* v_p_u2080_1687_, lean_object* v_p_u2081_1688_, lean_object* v_h_1689_, lean_object* v_pos_1690_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_nat_add(v_p_u2080_1687_, v_pos_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___boxed(lean_object* v_s_1692_, lean_object* v_p_u2080_1693_, lean_object* v_p_u2081_1694_, lean_object* v_h_1695_, lean_object* v_pos_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_String_Slice_Pos_ofSlice(v_s_1692_, v_p_u2080_1693_, v_p_u2081_1694_, v_h_1695_, v_pos_1696_);
lean_dec(v_pos_1696_);
lean_dec(v_p_u2081_1694_);
lean_dec(v_p_u2080_1693_);
lean_dec_ref(v_s_1692_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg(lean_object* v_p_u2080_1698_, lean_object* v_pos_1699_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = lean_nat_add(v_p_u2080_1698_, v_pos_1699_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1701_, lean_object* v_pos_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_String_Pos_ofSlice___redArg(v_p_u2080_1701_, v_pos_1702_);
lean_dec(v_pos_1702_);
lean_dec(v_p_u2080_1701_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice(lean_object* v_s_1704_, lean_object* v_p_u2080_1705_, lean_object* v_p_u2081_1706_, lean_object* v_h_1707_, lean_object* v_pos_1708_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = lean_nat_add(v_p_u2080_1705_, v_pos_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___boxed(lean_object* v_s_1710_, lean_object* v_p_u2080_1711_, lean_object* v_p_u2081_1712_, lean_object* v_h_1713_, lean_object* v_pos_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_String_Pos_ofSlice(v_s_1710_, v_p_u2080_1711_, v_p_u2081_1712_, v_h_1713_, v_pos_1714_);
lean_dec(v_pos_1714_);
lean_dec(v_p_u2081_1712_);
lean_dec(v_p_u2080_1711_);
lean_dec_ref(v_s_1710_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg(lean_object* v_pos_1716_, lean_object* v_p_u2080_1717_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = lean_nat_sub(v_pos_1716_, v_p_u2080_1717_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg___boxed(lean_object* v_pos_1719_, lean_object* v_p_u2080_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_String_Slice_Pos_slice___redArg(v_pos_1719_, v_p_u2080_1720_);
lean_dec(v_p_u2080_1720_);
lean_dec(v_pos_1719_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice(lean_object* v_s_1722_, lean_object* v_pos_1723_, lean_object* v_p_u2080_1724_, lean_object* v_p_u2081_1725_, lean_object* v_h_u2081_1726_, lean_object* v_h_u2082_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_nat_sub(v_pos_1723_, v_p_u2080_1724_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___boxed(lean_object* v_s_1729_, lean_object* v_pos_1730_, lean_object* v_p_u2080_1731_, lean_object* v_p_u2081_1732_, lean_object* v_h_u2081_1733_, lean_object* v_h_u2082_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_String_Slice_Pos_slice(v_s_1729_, v_pos_1730_, v_p_u2080_1731_, v_p_u2081_1732_, v_h_u2081_1733_, v_h_u2082_1734_);
lean_dec(v_p_u2081_1732_);
lean_dec(v_p_u2080_1731_);
lean_dec(v_pos_1730_);
lean_dec_ref(v_s_1729_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg(lean_object* v_pos_1736_, lean_object* v_p_u2080_1737_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = lean_nat_sub(v_pos_1736_, v_p_u2080_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg___boxed(lean_object* v_pos_1739_, lean_object* v_p_u2080_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_String_Pos_slice___redArg(v_pos_1739_, v_p_u2080_1740_);
lean_dec(v_p_u2080_1740_);
lean_dec(v_pos_1739_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice(lean_object* v_s_1742_, lean_object* v_pos_1743_, lean_object* v_p_u2080_1744_, lean_object* v_p_u2081_1745_, lean_object* v_h_u2081_1746_, lean_object* v_h_u2082_1747_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = lean_nat_sub(v_pos_1743_, v_p_u2080_1744_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___boxed(lean_object* v_s_1749_, lean_object* v_pos_1750_, lean_object* v_p_u2080_1751_, lean_object* v_p_u2081_1752_, lean_object* v_h_u2081_1753_, lean_object* v_h_u2082_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_String_Pos_slice(v_s_1749_, v_pos_1750_, v_p_u2080_1751_, v_p_u2081_1752_, v_h_u2081_1753_, v_h_u2082_1754_);
lean_dec(v_p_u2081_1752_);
lean_dec(v_p_u2080_1751_);
lean_dec(v_pos_1750_);
lean_dec_ref(v_s_1749_);
return v_res_1755_;
}
}
static lean_object* _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1758_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__1));
v___x_1759_ = lean_unsigned_to_nat(4u);
v___x_1760_ = lean_unsigned_to_nat(2655u);
v___x_1761_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__0));
v___x_1762_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1763_ = l_mkPanicMessageWithDecl(v___x_1762_, v___x_1761_, v___x_1760_, v___x_1759_, v___x_1758_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg(lean_object* v_pos_1764_, lean_object* v_p_u2080_1765_, lean_object* v_p_u2081_1766_){
_start:
{
uint8_t v___x_1771_; 
v___x_1771_ = lean_nat_dec_le(v_p_u2080_1765_, v_pos_1764_);
if (v___x_1771_ == 0)
{
goto v___jp_1767_;
}
else
{
uint8_t v___x_1772_; 
v___x_1772_ = lean_nat_dec_le(v_pos_1764_, v_p_u2081_1766_);
if (v___x_1772_ == 0)
{
goto v___jp_1767_;
}
else
{
lean_object* v___x_1773_; 
v___x_1773_ = lean_nat_sub(v_pos_1764_, v_p_u2080_1765_);
return v___x_1773_;
}
}
v___jp_1767_:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1768_ = lean_unsigned_to_nat(0u);
v___x_1769_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1770_ = l_panic___redArg(v___x_1768_, v___x_1769_);
return v___x_1770_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1774_, lean_object* v_p_u2080_1775_, lean_object* v_p_u2081_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_String_Slice_Pos_sliceOrPanic___redArg(v_pos_1774_, v_p_u2080_1775_, v_p_u2081_1776_);
lean_dec(v_p_u2081_1776_);
lean_dec(v_p_u2080_1775_);
lean_dec(v_pos_1774_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic(lean_object* v_s_1778_, lean_object* v_pos_1779_, lean_object* v_p_u2080_1780_, lean_object* v_p_u2081_1781_, lean_object* v_h_1782_){
_start:
{
uint8_t v___x_1787_; 
v___x_1787_ = lean_nat_dec_le(v_p_u2080_1780_, v_pos_1779_);
if (v___x_1787_ == 0)
{
goto v___jp_1783_;
}
else
{
uint8_t v___x_1788_; 
v___x_1788_ = lean_nat_dec_le(v_pos_1779_, v_p_u2081_1781_);
if (v___x_1788_ == 0)
{
goto v___jp_1783_;
}
else
{
lean_object* v___x_1789_; 
v___x_1789_ = lean_nat_sub(v_pos_1779_, v_p_u2080_1780_);
return v___x_1789_;
}
}
v___jp_1783_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1784_ = lean_unsigned_to_nat(0u);
v___x_1785_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1786_ = l_panic___redArg(v___x_1784_, v___x_1785_);
return v___x_1786_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___boxed(lean_object* v_s_1790_, lean_object* v_pos_1791_, lean_object* v_p_u2080_1792_, lean_object* v_p_u2081_1793_, lean_object* v_h_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_String_Slice_Pos_sliceOrPanic(v_s_1790_, v_pos_1791_, v_p_u2080_1792_, v_p_u2081_1793_, v_h_1794_);
lean_dec(v_p_u2081_1793_);
lean_dec(v_p_u2080_1792_);
lean_dec(v_pos_1791_);
lean_dec_ref(v_s_1790_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg(lean_object* v_pos_1796_, lean_object* v_p_u2080_1797_, lean_object* v_p_u2081_1798_){
_start:
{
uint8_t v___x_1803_; 
v___x_1803_ = lean_nat_dec_le(v_p_u2080_1797_, v_pos_1796_);
if (v___x_1803_ == 0)
{
goto v___jp_1799_;
}
else
{
uint8_t v___x_1804_; 
v___x_1804_ = lean_nat_dec_le(v_pos_1796_, v_p_u2081_1798_);
if (v___x_1804_ == 0)
{
goto v___jp_1799_;
}
else
{
lean_object* v___x_1805_; 
v___x_1805_ = lean_nat_sub(v_pos_1796_, v_p_u2080_1797_);
return v___x_1805_;
}
}
v___jp_1799_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = lean_unsigned_to_nat(0u);
v___x_1801_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1802_ = l_panic___redArg(v___x_1800_, v___x_1801_);
return v___x_1802_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1806_, lean_object* v_p_u2080_1807_, lean_object* v_p_u2081_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_String_Pos_sliceOrPanic___redArg(v_pos_1806_, v_p_u2080_1807_, v_p_u2081_1808_);
lean_dec(v_p_u2081_1808_);
lean_dec(v_p_u2080_1807_);
lean_dec(v_pos_1806_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic(lean_object* v_s_1810_, lean_object* v_pos_1811_, lean_object* v_p_u2080_1812_, lean_object* v_p_u2081_1813_, lean_object* v_h_1814_){
_start:
{
uint8_t v___x_1819_; 
v___x_1819_ = lean_nat_dec_le(v_p_u2080_1812_, v_pos_1811_);
if (v___x_1819_ == 0)
{
goto v___jp_1815_;
}
else
{
uint8_t v___x_1820_; 
v___x_1820_ = lean_nat_dec_le(v_pos_1811_, v_p_u2081_1813_);
if (v___x_1820_ == 0)
{
goto v___jp_1815_;
}
else
{
lean_object* v___x_1821_; 
v___x_1821_ = lean_nat_sub(v_pos_1811_, v_p_u2080_1812_);
return v___x_1821_;
}
}
v___jp_1815_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = lean_unsigned_to_nat(0u);
v___x_1817_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1818_ = l_panic___redArg(v___x_1816_, v___x_1817_);
return v___x_1818_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___boxed(lean_object* v_s_1822_, lean_object* v_pos_1823_, lean_object* v_p_u2080_1824_, lean_object* v_p_u2081_1825_, lean_object* v_h_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_String_Pos_sliceOrPanic(v_s_1822_, v_pos_1823_, v_p_u2080_1824_, v_p_u2081_1825_, v_h_1826_);
lean_dec(v_p_u2081_1825_);
lean_dec(v_p_u2080_1824_);
lean_dec(v_pos_1823_);
lean_dec_ref(v_s_1822_);
return v_res_1827_;
}
}
static lean_object* _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1829_ = ((lean_object*)(l_String_Slice_slice_x21___closed__1));
v___x_1830_ = lean_unsigned_to_nat(4u);
v___x_1831_ = lean_unsigned_to_nat(2679u);
v___x_1832_ = ((lean_object*)(l_String_Slice_Pos_ofSlice_x21___redArg___closed__0));
v___x_1833_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1834_ = l_mkPanicMessageWithDecl(v___x_1833_, v___x_1832_, v___x_1831_, v___x_1830_, v___x_1829_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1835_, lean_object* v_p_u2081_1836_, lean_object* v_pos_1837_){
_start:
{
uint8_t v___x_1838_; 
v___x_1838_ = lean_nat_dec_le(v_p_u2080_1835_, v_p_u2081_1836_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1839_ = lean_unsigned_to_nat(0u);
v___x_1840_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1841_ = l_panic___redArg(v___x_1839_, v___x_1840_);
return v___x_1841_;
}
else
{
lean_object* v___x_1842_; 
v___x_1842_ = lean_nat_add(v_p_u2080_1835_, v_pos_1837_);
return v___x_1842_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1843_, lean_object* v_p_u2081_1844_, lean_object* v_pos_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_String_Slice_Pos_ofSlice_x21___redArg(v_p_u2080_1843_, v_p_u2081_1844_, v_pos_1845_);
lean_dec(v_pos_1845_);
lean_dec(v_p_u2081_1844_);
lean_dec(v_p_u2080_1843_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21(lean_object* v_s_1847_, lean_object* v_p_u2080_1848_, lean_object* v_p_u2081_1849_, lean_object* v_pos_1850_){
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
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___boxed(lean_object* v_s_1856_, lean_object* v_p_u2080_1857_, lean_object* v_p_u2081_1858_, lean_object* v_pos_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_String_Slice_Pos_ofSlice_x21(v_s_1856_, v_p_u2080_1857_, v_p_u2081_1858_, v_pos_1859_);
lean_dec(v_pos_1859_);
lean_dec(v_p_u2081_1858_);
lean_dec(v_p_u2080_1857_);
lean_dec_ref(v_s_1856_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1861_, lean_object* v_p_u2081_1862_, lean_object* v_pos_1863_){
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
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1869_, lean_object* v_p_u2081_1870_, lean_object* v_pos_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_String_Pos_ofSlice_x21___redArg(v_p_u2080_1869_, v_p_u2081_1870_, v_pos_1871_);
lean_dec(v_pos_1871_);
lean_dec(v_p_u2081_1870_);
lean_dec(v_p_u2080_1869_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21(lean_object* v_s_1873_, lean_object* v_p_u2080_1874_, lean_object* v_p_u2081_1875_, lean_object* v_pos_1876_){
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
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___boxed(lean_object* v_s_1882_, lean_object* v_p_u2080_1883_, lean_object* v_p_u2081_1884_, lean_object* v_pos_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_String_Pos_ofSlice_x21(v_s_1882_, v_p_u2080_1883_, v_p_u2081_1884_, v_pos_1885_);
lean_dec(v_pos_1885_);
lean_dec(v_p_u2081_1884_);
lean_dec(v_p_u2080_1883_);
lean_dec_ref(v_s_1882_);
return v_res_1886_;
}
}
static lean_object* _init_l_String_Slice_Pos_slice_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1889_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__1));
v___x_1890_ = lean_unsigned_to_nat(4u);
v___x_1891_ = lean_unsigned_to_nat(2697u);
v___x_1892_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__0));
v___x_1893_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1894_ = l_mkPanicMessageWithDecl(v___x_1893_, v___x_1892_, v___x_1891_, v___x_1890_, v___x_1889_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg(lean_object* v_pos_1895_, lean_object* v_p_u2080_1896_, lean_object* v_p_u2081_1897_){
_start:
{
uint8_t v___x_1902_; 
v___x_1902_ = lean_nat_dec_le(v_p_u2080_1896_, v_pos_1895_);
if (v___x_1902_ == 0)
{
goto v___jp_1898_;
}
else
{
uint8_t v___x_1903_; 
v___x_1903_ = lean_nat_dec_le(v_pos_1895_, v_p_u2081_1897_);
if (v___x_1903_ == 0)
{
goto v___jp_1898_;
}
else
{
lean_object* v___x_1904_; 
v___x_1904_ = lean_nat_sub(v_pos_1895_, v_p_u2080_1896_);
return v___x_1904_;
}
}
v___jp_1898_:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1899_ = lean_unsigned_to_nat(0u);
v___x_1900_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1901_ = l_panic___redArg(v___x_1899_, v___x_1900_);
return v___x_1901_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1905_, lean_object* v_p_u2080_1906_, lean_object* v_p_u2081_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_String_Slice_Pos_slice_x21___redArg(v_pos_1905_, v_p_u2080_1906_, v_p_u2081_1907_);
lean_dec(v_p_u2081_1907_);
lean_dec(v_p_u2080_1906_);
lean_dec(v_pos_1905_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21(lean_object* v_s_1909_, lean_object* v_pos_1910_, lean_object* v_p_u2080_1911_, lean_object* v_p_u2081_1912_){
_start:
{
uint8_t v___x_1917_; 
v___x_1917_ = lean_nat_dec_le(v_p_u2080_1911_, v_pos_1910_);
if (v___x_1917_ == 0)
{
goto v___jp_1913_;
}
else
{
uint8_t v___x_1918_; 
v___x_1918_ = lean_nat_dec_le(v_pos_1910_, v_p_u2081_1912_);
if (v___x_1918_ == 0)
{
goto v___jp_1913_;
}
else
{
lean_object* v___x_1919_; 
v___x_1919_ = lean_nat_sub(v_pos_1910_, v_p_u2080_1911_);
return v___x_1919_;
}
}
v___jp_1913_:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = lean_unsigned_to_nat(0u);
v___x_1915_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1916_ = l_panic___redArg(v___x_1914_, v___x_1915_);
return v___x_1916_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___boxed(lean_object* v_s_1920_, lean_object* v_pos_1921_, lean_object* v_p_u2080_1922_, lean_object* v_p_u2081_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_String_Slice_Pos_slice_x21(v_s_1920_, v_pos_1921_, v_p_u2080_1922_, v_p_u2081_1923_);
lean_dec(v_p_u2081_1923_);
lean_dec(v_p_u2080_1922_);
lean_dec(v_pos_1921_);
lean_dec_ref(v_s_1920_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg(lean_object* v_pos_1925_, lean_object* v_p_u2080_1926_, lean_object* v_p_u2081_1927_){
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
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1935_, lean_object* v_p_u2080_1936_, lean_object* v_p_u2081_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_String_Pos_slice_x21___redArg(v_pos_1935_, v_p_u2080_1936_, v_p_u2081_1937_);
lean_dec(v_p_u2081_1937_);
lean_dec(v_p_u2080_1936_);
lean_dec(v_pos_1935_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21(lean_object* v_s_1939_, lean_object* v_pos_1940_, lean_object* v_p_u2080_1941_, lean_object* v_p_u2081_1942_){
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
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___boxed(lean_object* v_s_1950_, lean_object* v_pos_1951_, lean_object* v_p_u2080_1952_, lean_object* v_p_u2081_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_String_Pos_slice_x21(v_s_1950_, v_pos_1951_, v_p_u2080_1952_, v_p_u2081_1953_);
lean_dec(v_p_u2081_1953_);
lean_dec(v_p_u2080_1952_);
lean_dec(v_pos_1951_);
lean_dec_ref(v_s_1950_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract(lean_object* v_s_1955_, lean_object* v_p_u2080_1956_, lean_object* v_p_u2081_1957_){
_start:
{
lean_object* v_str_1958_; lean_object* v_startInclusive_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v_str_1958_ = lean_ctor_get(v_s_1955_, 0);
v_startInclusive_1959_ = lean_ctor_get(v_s_1955_, 1);
v___x_1960_ = lean_nat_add(v_startInclusive_1959_, v_p_u2080_1956_);
v___x_1961_ = lean_nat_add(v_startInclusive_1959_, v_p_u2081_1957_);
v___x_1962_ = lean_string_utf8_extract_fast(v_str_1958_, v___x_1960_, v___x_1961_);
lean_dec(v___x_1961_);
lean_dec(v___x_1960_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract___boxed(lean_object* v_s_1963_, lean_object* v_p_u2080_1964_, lean_object* v_p_u2081_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_String_Slice_extract(v_s_1963_, v_p_u2080_1964_, v_p_u2081_1965_);
lean_dec(v_p_u2081_1965_);
lean_dec(v_p_u2080_1964_);
lean_dec_ref(v_s_1963_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn(lean_object* v_s_1967_, lean_object* v_p_1968_, lean_object* v_n_1969_){
_start:
{
lean_object* v_zero_1970_; uint8_t v_isZero_1971_; 
v_zero_1970_ = lean_unsigned_to_nat(0u);
v_isZero_1971_ = lean_nat_dec_eq(v_n_1969_, v_zero_1970_);
if (v_isZero_1971_ == 1)
{
lean_dec(v_n_1969_);
return v_p_1968_;
}
else
{
lean_object* v_str_1972_; lean_object* v_startInclusive_1973_; lean_object* v_endExclusive_1974_; lean_object* v___x_1975_; uint8_t v_decide_1976_; 
v_str_1972_ = lean_ctor_get(v_s_1967_, 0);
v_startInclusive_1973_ = lean_ctor_get(v_s_1967_, 1);
v_endExclusive_1974_ = lean_ctor_get(v_s_1967_, 2);
v___x_1975_ = lean_nat_sub(v_endExclusive_1974_, v_startInclusive_1973_);
v_decide_1976_ = lean_nat_dec_eq(v_p_1968_, v___x_1975_);
lean_dec(v___x_1975_);
if (v_decide_1976_ == 0)
{
lean_object* v_one_1977_; lean_object* v_n_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v_one_1977_ = lean_unsigned_to_nat(1u);
v_n_1978_ = lean_nat_sub(v_n_1969_, v_one_1977_);
lean_dec(v_n_1969_);
v___x_1979_ = lean_nat_add(v_startInclusive_1973_, v_p_1968_);
lean_dec(v_p_1968_);
v___x_1980_ = lean_string_utf8_next_fast(v_str_1972_, v___x_1979_);
lean_dec(v___x_1979_);
v___x_1981_ = lean_nat_sub(v___x_1980_, v_startInclusive_1973_);
v_p_1968_ = v___x_1981_;
v_n_1969_ = v_n_1978_;
goto _start;
}
else
{
lean_dec(v_n_1969_);
return v_p_1968_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn___boxed(lean_object* v_s_1983_, lean_object* v_p_1984_, lean_object* v_n_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_String_Slice_Pos_nextn(v_s_1983_, v_p_1984_, v_n_1985_);
lean_dec_ref(v_s_1983_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_nextn(lean_object* v_s_1987_, lean_object* v_p_1988_, lean_object* v_n_1989_){
_start:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1990_ = lean_unsigned_to_nat(0u);
v___x_1991_ = lean_string_utf8_byte_size(v_s_1987_);
v___x_1992_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1992_, 0, v_s_1987_);
lean_ctor_set(v___x_1992_, 1, v___x_1990_);
lean_ctor_set(v___x_1992_, 2, v___x_1991_);
v___x_1993_ = l_String_Slice_Pos_nextn(v___x_1992_, v_p_1988_, v_n_1989_);
lean_dec_ref_known(v___x_1992_, 3);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(lean_object* v_n_1994_, lean_object* v_h__1_1995_, lean_object* v_h__2_1996_){
_start:
{
lean_object* v_zero_1997_; uint8_t v_isZero_1998_; 
v_zero_1997_ = lean_unsigned_to_nat(0u);
v_isZero_1998_ = lean_nat_dec_eq(v_n_1994_, v_zero_1997_);
if (v_isZero_1998_ == 1)
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
lean_dec(v_h__2_1996_);
v___x_1999_ = lean_box(0);
v___x_2000_ = lean_apply_1(v_h__1_1995_, v___x_1999_);
return v___x_2000_;
}
else
{
lean_object* v_one_2001_; lean_object* v_n_2002_; lean_object* v___x_2003_; 
lean_dec(v_h__1_1995_);
v_one_2001_ = lean_unsigned_to_nat(1u);
v_n_2002_ = lean_nat_sub(v_n_1994_, v_one_2001_);
v___x_2003_ = lean_apply_1(v_h__2_1996_, v_n_2002_);
return v___x_2003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg___boxed(lean_object* v_n_2004_, lean_object* v_h__1_2005_, lean_object* v_h__2_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(v_n_2004_, v_h__1_2005_, v_h__2_2006_);
lean_dec(v_n_2004_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(lean_object* v_motive_2008_, lean_object* v_n_2009_, lean_object* v_h__1_2010_, lean_object* v_h__2_2011_){
_start:
{
lean_object* v_zero_2012_; uint8_t v_isZero_2013_; 
v_zero_2012_ = lean_unsigned_to_nat(0u);
v_isZero_2013_ = lean_nat_dec_eq(v_n_2009_, v_zero_2012_);
if (v_isZero_2013_ == 1)
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
lean_dec(v_h__2_2011_);
v___x_2014_ = lean_box(0);
v___x_2015_ = lean_apply_1(v_h__1_2010_, v___x_2014_);
return v___x_2015_;
}
else
{
lean_object* v_one_2016_; lean_object* v_n_2017_; lean_object* v___x_2018_; 
lean_dec(v_h__1_2010_);
v_one_2016_ = lean_unsigned_to_nat(1u);
v_n_2017_ = lean_nat_sub(v_n_2009_, v_one_2016_);
v___x_2018_ = lean_apply_1(v_h__2_2011_, v_n_2017_);
return v___x_2018_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___boxed(lean_object* v_motive_2019_, lean_object* v_n_2020_, lean_object* v_h__1_2021_, lean_object* v_h__2_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(v_motive_2019_, v_n_2020_, v_h__1_2021_, v_h__2_2022_);
lean_dec(v_n_2020_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next___boxed(lean_object* v_s_2026_, lean_object* v_p_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = lean_string_utf8_next(v_s_2026_, v_p_2027_);
lean_dec(v_p_2027_);
lean_dec_ref(v_s_2026_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_String_next___boxed(lean_object* v_s_2031_, lean_object* v_p_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = lean_string_utf8_next(v_s_2031_, v_p_2032_);
lean_dec(v_p_2032_);
lean_dec_ref(v_s_2031_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux(lean_object* v_x_2034_, lean_object* v_x_2035_, lean_object* v_x_2036_){
_start:
{
if (lean_obj_tag(v_x_2034_) == 0)
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
lean_dec(v_x_2035_);
v___x_2037_ = lean_unsigned_to_nat(1u);
v___x_2038_ = lean_nat_sub(v_x_2036_, v___x_2037_);
return v___x_2038_;
}
else
{
lean_object* v_head_2039_; lean_object* v_tail_2040_; lean_object* v___y_2042_; uint32_t v___x_2046_; uint32_t v___x_2047_; uint8_t v___x_2048_; 
v_head_2039_ = lean_ctor_get(v_x_2034_, 0);
v_tail_2040_ = lean_ctor_get(v_x_2034_, 1);
v___x_2046_ = 127;
v___x_2047_ = lean_unbox_uint32(v_head_2039_);
v___x_2048_ = lean_uint32_dec_le(v___x_2047_, v___x_2046_);
if (v___x_2048_ == 0)
{
uint32_t v___x_2049_; uint32_t v___x_2050_; uint8_t v___x_2051_; 
v___x_2049_ = 2047;
v___x_2050_ = lean_unbox_uint32(v_head_2039_);
v___x_2051_ = lean_uint32_dec_le(v___x_2050_, v___x_2049_);
if (v___x_2051_ == 0)
{
uint32_t v___x_2052_; uint32_t v___x_2053_; uint8_t v___x_2054_; 
v___x_2052_ = 65535;
v___x_2053_ = lean_unbox_uint32(v_head_2039_);
v___x_2054_ = lean_uint32_dec_le(v___x_2053_, v___x_2052_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; 
v___x_2055_ = lean_unsigned_to_nat(4u);
v___y_2042_ = v___x_2055_;
goto v___jp_2041_;
}
else
{
lean_object* v___x_2056_; 
v___x_2056_ = lean_unsigned_to_nat(3u);
v___y_2042_ = v___x_2056_;
goto v___jp_2041_;
}
}
else
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_unsigned_to_nat(2u);
v___y_2042_ = v___x_2057_;
goto v___jp_2041_;
}
}
else
{
lean_object* v___x_2058_; 
v___x_2058_ = lean_unsigned_to_nat(1u);
v___y_2042_ = v___x_2058_;
goto v___jp_2041_;
}
v___jp_2041_:
{
lean_object* v___x_2043_; uint8_t v___x_2044_; 
v___x_2043_ = lean_nat_add(v_x_2035_, v___y_2042_);
v___x_2044_ = lean_nat_dec_le(v_x_2036_, v___x_2043_);
if (v___x_2044_ == 0)
{
lean_dec(v_x_2035_);
v_x_2034_ = v_tail_2040_;
v_x_2035_ = v___x_2043_;
goto _start;
}
else
{
lean_dec(v___x_2043_);
return v_x_2035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux___boxed(lean_object* v_x_2059_, lean_object* v_x_2060_, lean_object* v_x_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_String_Pos_Raw_utf8PrevAux(v_x_2059_, v_x_2060_, v_x_2061_);
lean_dec(v_x_2061_);
lean_dec(v_x_2059_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux(lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l_String_Pos_Raw_utf8PrevAux(v_a_2063_, v_a_2064_, v_a_2065_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux___boxed(lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_String_utf8PrevAux(v_a_2067_, v_a_2068_, v_a_2069_);
lean_dec(v_a_2069_);
lean_dec(v_a_2067_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_prev___boxed(lean_object* v_a_00___x40___internal___hyg_2073_, lean_object* v_a_00___x40___internal___hyg_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_2073_, v_a_00___x40___internal___hyg_2074_);
lean_dec(v_a_00___x40___internal___hyg_2074_);
lean_dec_ref(v_a_00___x40___internal___hyg_2073_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_String_prev___boxed(lean_object* v_a_00___x40___internal___hyg_2078_, lean_object* v_a_00___x40___internal___hyg_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_2078_, v_a_00___x40___internal___hyg_2079_);
lean_dec(v_a_00___x40___internal___hyg_2079_);
lean_dec_ref(v_a_00___x40___internal___hyg_2078_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_2083_, lean_object* v_a_00___x40___internal___hyg_2084_){
_start:
{
uint8_t v_res_2085_; lean_object* v_r_2086_; 
v_res_2085_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_2083_, v_a_00___x40___internal___hyg_2084_);
lean_dec(v_a_00___x40___internal___hyg_2084_);
lean_dec_ref(v_a_00___x40___internal___hyg_2083_);
v_r_2086_ = lean_box(v_res_2085_);
return v_r_2086_;
}
}
LEAN_EXPORT lean_object* l_String_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_2089_, lean_object* v_a_00___x40___internal___hyg_2090_){
_start:
{
uint8_t v_res_2091_; lean_object* v_r_2092_; 
v_res_2091_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_2089_, v_a_00___x40___internal___hyg_2090_);
lean_dec(v_a_00___x40___internal___hyg_2090_);
lean_dec_ref(v_a_00___x40___internal___hyg_2089_);
v_r_2092_ = lean_box(v_res_2091_);
return v_r_2092_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x27___boxed(lean_object* v_s_2096_, lean_object* v_p_2097_, lean_object* v_h_2098_){
_start:
{
uint32_t v_res_2099_; lean_object* v_r_2100_; 
v_res_2099_ = lean_string_utf8_get_fast(v_s_2096_, v_p_2097_);
lean_dec(v_p_2097_);
lean_dec_ref(v_s_2096_);
v_r_2100_ = lean_box_uint32(v_res_2099_);
return v_r_2100_;
}
}
LEAN_EXPORT lean_object* l_String_get_x27___boxed(lean_object* v_s_2104_, lean_object* v_p_2105_, lean_object* v_h_2106_){
_start:
{
uint32_t v_res_2107_; lean_object* v_r_2108_; 
v_res_2107_ = lean_string_utf8_get_fast(v_s_2104_, v_p_2105_);
lean_dec(v_p_2105_);
lean_dec_ref(v_s_2104_);
v_r_2108_ = lean_box_uint32(v_res_2107_);
return v_r_2108_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next_x27___boxed(lean_object* v_s_2112_, lean_object* v_p_2113_, lean_object* v_h_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = lean_string_utf8_next_fast(v_s_2112_, v_p_2113_);
lean_dec(v_p_2113_);
lean_dec_ref(v_s_2112_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l_String_next_x27___boxed(lean_object* v_s_2119_, lean_object* v_p_2120_, lean_object* v_h_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = lean_string_utf8_next_fast(v_s_2119_, v_p_2120_);
lean_dec(v_p_2120_);
lean_dec_ref(v_s_2119_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter___redArg(lean_object* v_x_2123_, lean_object* v_x_2124_, lean_object* v_x_2125_, lean_object* v_h__1_2126_, lean_object* v_h__2_2127_){
_start:
{
if (lean_obj_tag(v_x_2123_) == 0)
{
lean_object* v___x_2128_; 
lean_dec(v_h__2_2127_);
v___x_2128_ = lean_apply_2(v_h__1_2126_, v_x_2124_, v_x_2125_);
return v___x_2128_;
}
else
{
lean_object* v_head_2129_; lean_object* v_tail_2130_; lean_object* v___x_2131_; 
lean_dec(v_h__1_2126_);
v_head_2129_ = lean_ctor_get(v_x_2123_, 0);
lean_inc(v_head_2129_);
v_tail_2130_ = lean_ctor_get(v_x_2123_, 1);
lean_inc(v_tail_2130_);
lean_dec_ref_known(v_x_2123_, 2);
v___x_2131_ = lean_apply_4(v_h__2_2127_, v_head_2129_, v_tail_2130_, v_x_2124_, v_x_2125_);
return v___x_2131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter(lean_object* v_motive_2132_, lean_object* v_x_2133_, lean_object* v_x_2134_, lean_object* v_x_2135_, lean_object* v_h__1_2136_, lean_object* v_h__2_2137_){
_start:
{
if (lean_obj_tag(v_x_2133_) == 0)
{
lean_object* v___x_2138_; 
lean_dec(v_h__2_2137_);
v___x_2138_ = lean_apply_2(v_h__1_2136_, v_x_2134_, v_x_2135_);
return v___x_2138_;
}
else
{
lean_object* v_head_2139_; lean_object* v_tail_2140_; lean_object* v___x_2141_; 
lean_dec(v_h__1_2136_);
v_head_2139_ = lean_ctor_get(v_x_2133_, 0);
lean_inc(v_head_2139_);
v_tail_2140_ = lean_ctor_get(v_x_2133_, 1);
lean_inc(v_tail_2140_);
lean_dec_ref_known(v_x_2133_, 2);
v___x_2141_ = lean_apply_4(v_h__2_2137_, v_head_2139_, v_tail_2140_, v_x_2134_, v_x_2135_);
return v___x_2141_;
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop(lean_object* v_a_2142_, lean_object* v_b_2143_, lean_object* v_stopPos_2144_, lean_object* v_i_2145_){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; uint8_t v___x_2148_; 
v___x_2146_ = lean_unsigned_to_nat(1u);
v___x_2147_ = lean_nat_add(v_i_2145_, v___x_2146_);
v___x_2148_ = lean_nat_dec_le(v___x_2147_, v_stopPos_2144_);
lean_dec(v___x_2147_);
if (v___x_2148_ == 0)
{
return v_i_2145_;
}
else
{
uint32_t v___x_2149_; uint32_t v___x_2150_; uint8_t v___x_2151_; 
v___x_2149_ = lean_string_utf8_get(v_a_2142_, v_i_2145_);
v___x_2150_ = lean_string_utf8_get(v_b_2143_, v_i_2145_);
v___x_2151_ = lean_uint32_dec_eq(v___x_2149_, v___x_2150_);
if (v___x_2151_ == 0)
{
return v_i_2145_;
}
else
{
lean_object* v___x_2152_; 
v___x_2152_ = lean_string_utf8_next(v_a_2142_, v_i_2145_);
lean_dec(v_i_2145_);
v_i_2145_ = v___x_2152_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop___boxed(lean_object* v_a_2154_, lean_object* v_b_2155_, lean_object* v_stopPos_2156_, lean_object* v_i_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_String_firstDiffPos_loop(v_a_2154_, v_b_2155_, v_stopPos_2156_, v_i_2157_);
lean_dec(v_stopPos_2156_);
lean_dec_ref(v_b_2155_);
lean_dec_ref(v_a_2154_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos(lean_object* v_a_2159_, lean_object* v_b_2160_){
_start:
{
lean_object* v___y_2162_; lean_object* v___x_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; 
v___x_2165_ = lean_string_utf8_byte_size(v_a_2159_);
v___x_2166_ = lean_string_utf8_byte_size(v_b_2160_);
v___x_2167_ = lean_nat_dec_le(v___x_2165_, v___x_2166_);
if (v___x_2167_ == 0)
{
v___y_2162_ = v___x_2166_;
goto v___jp_2161_;
}
else
{
v___y_2162_ = v___x_2165_;
goto v___jp_2161_;
}
v___jp_2161_:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2163_ = lean_unsigned_to_nat(0u);
v___x_2164_ = l_String_firstDiffPos_loop(v_a_2159_, v_b_2160_, v___y_2162_, v___x_2163_);
lean_dec(v___y_2162_);
return v___x_2164_;
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos___boxed(lean_object* v_a_2168_, lean_object* v_b_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_String_firstDiffPos(v_a_2168_, v_b_2169_);
lean_dec_ref(v_b_2169_);
lean_dec_ref(v_a_2168_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082(lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_){
_start:
{
if (lean_obj_tag(v_a_2171_) == 0)
{
return v_a_2171_;
}
else
{
lean_object* v_head_2174_; lean_object* v_tail_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2201_; 
v_head_2174_ = lean_ctor_get(v_a_2171_, 0);
v_tail_2175_ = lean_ctor_get(v_a_2171_, 1);
v_isSharedCheck_2201_ = !lean_is_exclusive(v_a_2171_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2177_ = v_a_2171_;
v_isShared_2178_ = v_isSharedCheck_2201_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_tail_2175_);
lean_inc(v_head_2174_);
lean_dec(v_a_2171_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2201_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___y_2180_; uint8_t v_decide_2186_; 
v_decide_2186_ = lean_nat_dec_eq(v_a_2172_, v_a_2173_);
if (v_decide_2186_ == 0)
{
uint32_t v___x_2187_; uint32_t v___x_2188_; uint8_t v___x_2189_; 
v___x_2187_ = 127;
v___x_2188_ = lean_unbox_uint32(v_head_2174_);
v___x_2189_ = lean_uint32_dec_le(v___x_2188_, v___x_2187_);
if (v___x_2189_ == 0)
{
uint32_t v___x_2190_; uint32_t v___x_2191_; uint8_t v___x_2192_; 
v___x_2190_ = 2047;
v___x_2191_ = lean_unbox_uint32(v_head_2174_);
v___x_2192_ = lean_uint32_dec_le(v___x_2191_, v___x_2190_);
if (v___x_2192_ == 0)
{
uint32_t v___x_2193_; uint32_t v___x_2194_; uint8_t v___x_2195_; 
v___x_2193_ = 65535;
v___x_2194_ = lean_unbox_uint32(v_head_2174_);
v___x_2195_ = lean_uint32_dec_le(v___x_2194_, v___x_2193_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; 
v___x_2196_ = lean_unsigned_to_nat(4u);
v___y_2180_ = v___x_2196_;
goto v___jp_2179_;
}
else
{
lean_object* v___x_2197_; 
v___x_2197_ = lean_unsigned_to_nat(3u);
v___y_2180_ = v___x_2197_;
goto v___jp_2179_;
}
}
else
{
lean_object* v___x_2198_; 
v___x_2198_ = lean_unsigned_to_nat(2u);
v___y_2180_ = v___x_2198_;
goto v___jp_2179_;
}
}
else
{
lean_object* v___x_2199_; 
v___x_2199_ = lean_unsigned_to_nat(1u);
v___y_2180_ = v___x_2199_;
goto v___jp_2179_;
}
}
else
{
lean_object* v___x_2200_; 
lean_del_object(v___x_2177_);
lean_dec(v_tail_2175_);
lean_dec(v_head_2174_);
v___x_2200_ = lean_box(0);
return v___x_2200_;
}
v___jp_2179_:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2184_; 
v___x_2181_ = lean_nat_add(v_a_2172_, v___y_2180_);
v___x_2182_ = l_String_Pos_Raw_extract_go_u2082(v_tail_2175_, v___x_2181_, v_a_2173_);
lean_dec(v___x_2181_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 1, v___x_2182_);
v___x_2184_ = v___x_2177_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_head_2174_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082___boxed(lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_String_Pos_Raw_extract_go_u2082(v_a_2202_, v_a_2203_, v_a_2204_);
lean_dec(v_a_2204_);
lean_dec(v_a_2203_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081(lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_){
_start:
{
if (lean_obj_tag(v_a_2206_) == 0)
{
lean_dec(v_a_2207_);
return v_a_2206_;
}
else
{
lean_object* v_head_2210_; lean_object* v_tail_2211_; lean_object* v___y_2213_; uint8_t v_decide_2216_; 
v_head_2210_ = lean_ctor_get(v_a_2206_, 0);
v_tail_2211_ = lean_ctor_get(v_a_2206_, 1);
v_decide_2216_ = lean_nat_dec_eq(v_a_2207_, v_a_2208_);
if (v_decide_2216_ == 0)
{
uint32_t v___x_2217_; uint32_t v___x_2218_; uint8_t v___x_2219_; 
lean_inc(v_tail_2211_);
lean_inc(v_head_2210_);
lean_dec_ref_known(v_a_2206_, 2);
v___x_2217_ = 127;
v___x_2218_ = lean_unbox_uint32(v_head_2210_);
v___x_2219_ = lean_uint32_dec_le(v___x_2218_, v___x_2217_);
if (v___x_2219_ == 0)
{
uint32_t v___x_2220_; uint32_t v___x_2221_; uint8_t v___x_2222_; 
v___x_2220_ = 2047;
v___x_2221_ = lean_unbox_uint32(v_head_2210_);
v___x_2222_ = lean_uint32_dec_le(v___x_2221_, v___x_2220_);
if (v___x_2222_ == 0)
{
uint32_t v___x_2223_; uint32_t v___x_2224_; uint8_t v___x_2225_; 
v___x_2223_ = 65535;
v___x_2224_ = lean_unbox_uint32(v_head_2210_);
lean_dec(v_head_2210_);
v___x_2225_ = lean_uint32_dec_le(v___x_2224_, v___x_2223_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_unsigned_to_nat(4u);
v___y_2213_ = v___x_2226_;
goto v___jp_2212_;
}
else
{
lean_object* v___x_2227_; 
v___x_2227_ = lean_unsigned_to_nat(3u);
v___y_2213_ = v___x_2227_;
goto v___jp_2212_;
}
}
else
{
lean_object* v___x_2228_; 
lean_dec(v_head_2210_);
v___x_2228_ = lean_unsigned_to_nat(2u);
v___y_2213_ = v___x_2228_;
goto v___jp_2212_;
}
}
else
{
lean_object* v___x_2229_; 
lean_dec(v_head_2210_);
v___x_2229_ = lean_unsigned_to_nat(1u);
v___y_2213_ = v___x_2229_;
goto v___jp_2212_;
}
}
else
{
lean_object* v___x_2230_; 
v___x_2230_ = l_String_Pos_Raw_extract_go_u2082(v_a_2206_, v_a_2207_, v_a_2209_);
lean_dec(v_a_2207_);
return v___x_2230_;
}
v___jp_2212_:
{
lean_object* v___x_2214_; 
v___x_2214_ = lean_nat_add(v_a_2207_, v___y_2213_);
lean_dec(v_a_2207_);
v_a_2206_ = v_tail_2211_;
v_a_2207_ = v___x_2214_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081___boxed(lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_String_Pos_Raw_extract_go_u2081(v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
lean_dec(v_a_2234_);
lean_dec(v_a_2233_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract___boxed(lean_object* v_a_00___x40___internal___hyg_2239_, lean_object* v_a_00___x40___internal___hyg_2240_, lean_object* v_a_00___x40___internal___hyg_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = lean_string_utf8_extract(v_a_00___x40___internal___hyg_2239_, v_a_00___x40___internal___hyg_2240_, v_a_00___x40___internal___hyg_2241_);
lean_dec(v_a_00___x40___internal___hyg_2241_);
lean_dec(v_a_00___x40___internal___hyg_2240_);
lean_dec_ref(v_a_00___x40___internal___hyg_2239_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux(lean_object* v_s_2243_, lean_object* v_pos_2244_, lean_object* v_i_2245_, lean_object* v_offset_2246_){
_start:
{
uint8_t v___x_2247_; 
v___x_2247_ = lean_nat_dec_le(v_pos_2244_, v_i_2245_);
if (v___x_2247_ == 0)
{
uint8_t v___x_2248_; 
v___x_2248_ = lean_string_utf8_at_end(v_s_2243_, v_i_2245_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2249_ = lean_string_utf8_next(v_s_2243_, v_i_2245_);
lean_dec(v_i_2245_);
v___x_2250_ = lean_unsigned_to_nat(1u);
v___x_2251_ = lean_nat_add(v_offset_2246_, v___x_2250_);
lean_dec(v_offset_2246_);
v_i_2245_ = v___x_2249_;
v_offset_2246_ = v___x_2251_;
goto _start;
}
else
{
lean_dec(v_i_2245_);
return v_offset_2246_;
}
}
else
{
lean_dec(v_i_2245_);
return v_offset_2246_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux___boxed(lean_object* v_s_2253_, lean_object* v_pos_2254_, lean_object* v_i_2255_, lean_object* v_offset_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2253_, v_pos_2254_, v_i_2255_, v_offset_2256_);
lean_dec(v_pos_2254_);
lean_dec_ref(v_s_2253_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos(lean_object* v_s_2258_, lean_object* v_pos_2259_){
_start:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = lean_unsigned_to_nat(0u);
v___x_2261_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2258_, v_pos_2259_, v___x_2260_, v___x_2260_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos___boxed(lean_object* v_s_2262_, lean_object* v_pos_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_String_Pos_Raw_offsetOfPos(v_s_2262_, v_pos_2263_);
lean_dec(v_pos_2263_);
lean_dec_ref(v_s_2262_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos(lean_object* v_s_2265_, lean_object* v_pos_2266_){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = lean_unsigned_to_nat(0u);
v___x_2268_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2265_, v_pos_2266_, v___x_2267_, v___x_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos___boxed(lean_object* v_s_2269_, lean_object* v_pos_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_String_offsetOfPos(v_s_2269_, v_pos_2270_);
lean_dec(v_pos_2270_);
lean_dec_ref(v_s_2269_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* lean_string_offsetofpos(lean_object* v_s_2272_, lean_object* v_pos_2273_){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = lean_unsigned_to_nat(0u);
v___x_2275_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2272_, v_pos_2273_, v___x_2274_, v___x_2274_);
lean_dec(v_pos_2273_);
lean_dec_ref(v_s_2272_);
return v___x_2275_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(lean_object* v_s1_2276_, lean_object* v_s2_2277_, lean_object* v_off1_2278_, lean_object* v_off2_2279_, lean_object* v_stop1_2280_){
_start:
{
lean_object* v___y_2282_; lean_object* v___y_2283_; uint8_t v___x_2286_; 
v___x_2286_ = lean_nat_dec_lt(v_off1_2278_, v_stop1_2280_);
if (v___x_2286_ == 0)
{
uint8_t v___x_2287_; 
lean_dec(v_off2_2279_);
lean_dec(v_off1_2278_);
v___x_2287_ = 1;
return v___x_2287_;
}
else
{
uint32_t v_c_u2081_2288_; uint32_t v_c_u2082_2289_; lean_object* v___y_2291_; uint8_t v___x_2303_; 
v_c_u2081_2288_ = lean_string_utf8_get(v_s1_2276_, v_off1_2278_);
v_c_u2082_2289_ = lean_string_utf8_get(v_s2_2277_, v_off2_2279_);
v___x_2303_ = lean_uint32_dec_eq(v_c_u2081_2288_, v_c_u2082_2289_);
if (v___x_2303_ == 0)
{
lean_dec(v_off2_2279_);
lean_dec(v_off1_2278_);
return v___x_2303_;
}
else
{
uint32_t v___x_2304_; uint8_t v___x_2305_; 
v___x_2304_ = 127;
v___x_2305_ = lean_uint32_dec_le(v_c_u2081_2288_, v___x_2304_);
if (v___x_2305_ == 0)
{
uint32_t v___x_2306_; uint8_t v___x_2307_; 
v___x_2306_ = 2047;
v___x_2307_ = lean_uint32_dec_le(v_c_u2081_2288_, v___x_2306_);
if (v___x_2307_ == 0)
{
uint32_t v___x_2308_; uint8_t v___x_2309_; 
v___x_2308_ = 65535;
v___x_2309_ = lean_uint32_dec_le(v_c_u2081_2288_, v___x_2308_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2310_; 
v___x_2310_ = lean_unsigned_to_nat(4u);
v___y_2291_ = v___x_2310_;
goto v___jp_2290_;
}
else
{
lean_object* v___x_2311_; 
v___x_2311_ = lean_unsigned_to_nat(3u);
v___y_2291_ = v___x_2311_;
goto v___jp_2290_;
}
}
else
{
lean_object* v___x_2312_; 
v___x_2312_ = lean_unsigned_to_nat(2u);
v___y_2291_ = v___x_2312_;
goto v___jp_2290_;
}
}
else
{
lean_object* v___x_2313_; 
v___x_2313_ = lean_unsigned_to_nat(1u);
v___y_2291_ = v___x_2313_;
goto v___jp_2290_;
}
}
v___jp_2290_:
{
lean_object* v___x_2292_; uint32_t v___x_2293_; uint8_t v___x_2294_; 
v___x_2292_ = lean_nat_add(v_off1_2278_, v___y_2291_);
lean_dec(v_off1_2278_);
v___x_2293_ = 127;
v___x_2294_ = lean_uint32_dec_le(v_c_u2082_2289_, v___x_2293_);
if (v___x_2294_ == 0)
{
uint32_t v___x_2295_; uint8_t v___x_2296_; 
v___x_2295_ = 2047;
v___x_2296_ = lean_uint32_dec_le(v_c_u2082_2289_, v___x_2295_);
if (v___x_2296_ == 0)
{
uint32_t v___x_2297_; uint8_t v___x_2298_; 
v___x_2297_ = 65535;
v___x_2298_ = lean_uint32_dec_le(v_c_u2082_2289_, v___x_2297_);
if (v___x_2298_ == 0)
{
lean_object* v___x_2299_; 
v___x_2299_ = lean_unsigned_to_nat(4u);
v___y_2282_ = v___x_2292_;
v___y_2283_ = v___x_2299_;
goto v___jp_2281_;
}
else
{
lean_object* v___x_2300_; 
v___x_2300_ = lean_unsigned_to_nat(3u);
v___y_2282_ = v___x_2292_;
v___y_2283_ = v___x_2300_;
goto v___jp_2281_;
}
}
else
{
lean_object* v___x_2301_; 
v___x_2301_ = lean_unsigned_to_nat(2u);
v___y_2282_ = v___x_2292_;
v___y_2283_ = v___x_2301_;
goto v___jp_2281_;
}
}
else
{
lean_object* v___x_2302_; 
v___x_2302_ = lean_unsigned_to_nat(1u);
v___y_2282_ = v___x_2292_;
v___y_2283_ = v___x_2302_;
goto v___jp_2281_;
}
}
}
v___jp_2281_:
{
lean_object* v___x_2284_; 
v___x_2284_ = lean_nat_add(v_off2_2279_, v___y_2283_);
lean_dec(v_off2_2279_);
v_off1_2278_ = v___y_2282_;
v_off2_2279_ = v___x_2284_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop___boxed(lean_object* v_s1_2314_, lean_object* v_s2_2315_, lean_object* v_off1_2316_, lean_object* v_off2_2317_, lean_object* v_stop1_2318_){
_start:
{
uint8_t v_res_2319_; lean_object* v_r_2320_; 
v_res_2319_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2314_, v_s2_2315_, v_off1_2316_, v_off2_2317_, v_stop1_2318_);
lean_dec(v_stop1_2318_);
lean_dec_ref(v_s2_2315_);
lean_dec_ref(v_s1_2314_);
v_r_2320_ = lean_box(v_res_2319_);
return v_r_2320_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_substrEq(lean_object* v_s1_2321_, lean_object* v_pos1_2322_, lean_object* v_s2_2323_, lean_object* v_pos2_2324_, lean_object* v_sz_2325_){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; uint8_t v___x_2328_; 
v___x_2326_ = lean_nat_add(v_pos1_2322_, v_sz_2325_);
v___x_2327_ = lean_string_utf8_byte_size(v_s1_2321_);
v___x_2328_ = lean_nat_dec_le(v___x_2326_, v___x_2327_);
if (v___x_2328_ == 0)
{
lean_dec(v___x_2326_);
lean_dec(v_pos2_2324_);
lean_dec(v_pos1_2322_);
return v___x_2328_;
}
else
{
lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v___x_2329_ = lean_nat_add(v_pos2_2324_, v_sz_2325_);
v___x_2330_ = lean_string_utf8_byte_size(v_s2_2323_);
v___x_2331_ = lean_nat_dec_le(v___x_2329_, v___x_2330_);
lean_dec(v___x_2329_);
if (v___x_2331_ == 0)
{
lean_dec(v___x_2326_);
lean_dec(v_pos2_2324_);
lean_dec(v_pos1_2322_);
return v___x_2331_;
}
else
{
uint8_t v___x_2332_; 
v___x_2332_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2321_, v_s2_2323_, v_pos1_2322_, v_pos2_2324_, v___x_2326_);
lean_dec(v___x_2326_);
return v___x_2332_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_substrEq___boxed(lean_object* v_s1_2333_, lean_object* v_pos1_2334_, lean_object* v_s2_2335_, lean_object* v_pos2_2336_, lean_object* v_sz_2337_){
_start:
{
uint8_t v_res_2338_; lean_object* v_r_2339_; 
v_res_2338_ = l_String_Pos_Raw_substrEq(v_s1_2333_, v_pos1_2334_, v_s2_2335_, v_pos2_2336_, v_sz_2337_);
lean_dec(v_sz_2337_);
lean_dec_ref(v_s2_2335_);
lean_dec_ref(v_s1_2333_);
v_r_2339_ = lean_box(v_res_2338_);
return v_r_2339_;
}
}
LEAN_EXPORT uint8_t l_String_substrEq(lean_object* v_s1_2340_, lean_object* v_pos1_2341_, lean_object* v_s2_2342_, lean_object* v_pos2_2343_, lean_object* v_sz_2344_){
_start:
{
uint8_t v___x_2345_; 
v___x_2345_ = l_String_Pos_Raw_substrEq(v_s1_2340_, v_pos1_2341_, v_s2_2342_, v_pos2_2343_, v_sz_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_String_substrEq___boxed(lean_object* v_s1_2346_, lean_object* v_pos1_2347_, lean_object* v_s2_2348_, lean_object* v_pos2_2349_, lean_object* v_sz_2350_){
_start:
{
uint8_t v_res_2351_; lean_object* v_r_2352_; 
v_res_2351_ = l_String_substrEq(v_s1_2346_, v_pos1_2347_, v_s2_2348_, v_pos2_2349_, v_sz_2350_);
lean_dec(v_sz_2350_);
lean_dec_ref(v_s2_2348_);
lean_dec_ref(v_s1_2346_);
v_r_2352_ = lean_box(v_res_2351_);
return v_r_2352_;
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
