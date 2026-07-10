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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t l_UInt8_instDecidableIsUTF8FirstByte___aux__1(uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_uint8_land(uint8_t, uint8_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* v___x_35_; lean_object* v___x_36_; uint8_t v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; uint8_t v___x_40_; uint8_t v___x_41_; uint8_t v___y_43_; uint8_t v___x_74_; uint8_t v___x_75_; uint8_t v___x_76_; 
v___x_35_ = lean_unsigned_to_nat(1u);
v___x_36_ = lean_nat_add(v_i_2_, v___x_35_);
v___x_37_ = lean_byte_array_fget(v_b_1_, v___x_36_);
lean_dec(v___x_36_);
v___x_38_ = lean_unsigned_to_nat(2u);
v___x_39_ = lean_nat_add(v_i_2_, v___x_38_);
v___x_40_ = lean_byte_array_fget(v_b_1_, v___x_39_);
lean_dec(v___x_39_);
v___x_41_ = lean_byte_array_fget(v_b_1_, v___x_32_);
lean_dec(v___x_32_);
v___x_74_ = lean_uint8_land(v___x_37_, v___x_22_);
v___x_75_ = lean_uint8_dec_eq(v___x_74_, v___x_16_);
v___x_76_ = lean_bool_not(v___x_75_);
if (v___x_76_ == 0)
{
uint8_t v___x_77_; uint8_t v___x_78_; uint8_t v___x_79_; 
v___x_77_ = lean_uint8_land(v___x_40_, v___x_22_);
v___x_78_ = lean_uint8_dec_eq(v___x_77_, v___x_16_);
v___x_79_ = lean_bool_not(v___x_78_);
v___y_43_ = v___x_79_;
goto v___jp_42_;
}
else
{
v___y_43_ = v___x_76_;
goto v___jp_42_;
}
v___jp_42_:
{
if (v___y_43_ == 0)
{
uint8_t v___x_44_; uint8_t v___x_45_; uint8_t v___x_46_; 
v___x_44_ = lean_uint8_land(v___x_41_, v___x_22_);
v___x_45_ = lean_uint8_dec_eq(v___x_44_, v___x_16_);
v___x_46_ = lean_bool_not(v___x_45_);
if (v___x_46_ == 0)
{
uint8_t v___x_47_; uint8_t v_b_u2080_48_; uint8_t v___x_49_; uint8_t v_b_u2081_50_; uint8_t v_b_u2082_51_; uint8_t v_b_u2083_52_; uint32_t v___x_53_; uint32_t v___x_54_; uint32_t v___x_55_; uint32_t v___x_56_; uint32_t v___x_57_; uint32_t v___x_58_; uint32_t v___x_59_; uint32_t v___x_60_; uint32_t v___x_61_; uint32_t v___x_62_; uint32_t v___x_63_; uint32_t v___x_64_; uint32_t v_r_65_; uint32_t v___x_66_; uint8_t v___x_67_; 
v___x_47_ = 7;
v_b_u2080_48_ = lean_uint8_land(v___x_15_, v___x_47_);
v___x_49_ = 63;
v_b_u2081_50_ = lean_uint8_land(v___x_37_, v___x_49_);
v_b_u2082_51_ = lean_uint8_land(v___x_40_, v___x_49_);
v_b_u2083_52_ = lean_uint8_land(v___x_41_, v___x_49_);
v___x_53_ = lean_uint8_to_uint32(v_b_u2080_48_);
v___x_54_ = 18;
v___x_55_ = lean_uint32_shift_left(v___x_53_, v___x_54_);
v___x_56_ = lean_uint8_to_uint32(v_b_u2081_50_);
v___x_57_ = 12;
v___x_58_ = lean_uint32_shift_left(v___x_56_, v___x_57_);
v___x_59_ = lean_uint32_lor(v___x_55_, v___x_58_);
v___x_60_ = lean_uint8_to_uint32(v_b_u2082_51_);
v___x_61_ = 6;
v___x_62_ = lean_uint32_shift_left(v___x_60_, v___x_61_);
v___x_63_ = lean_uint32_lor(v___x_59_, v___x_62_);
v___x_64_ = lean_uint8_to_uint32(v_b_u2083_52_);
v_r_65_ = lean_uint32_lor(v___x_63_, v___x_64_);
v___x_66_ = 65536;
v___x_67_ = lean_uint32_dec_lt(v_r_65_, v___x_66_);
if (v___x_67_ == 0)
{
uint32_t v___x_68_; uint8_t v___x_69_; 
v___x_68_ = 1114111;
v___x_69_ = lean_uint32_dec_lt(v___x_68_, v_r_65_);
if (v___x_69_ == 0)
{
v_val_5_ = v_r_65_;
goto v___jp_4_;
}
else
{
lean_object* v___x_70_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_70_ = lean_box(0);
return v___x_70_;
}
}
else
{
lean_object* v___x_71_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_71_ = lean_box(0);
return v___x_71_;
}
}
else
{
lean_object* v___x_72_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_72_ = lean_box(0);
return v___x_72_;
}
}
else
{
lean_object* v___x_73_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_73_ = lean_box(0);
return v___x_73_;
}
}
}
}
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_80_ = lean_unsigned_to_nat(2u);
v___x_81_ = lean_nat_add(v_i_2_, v___x_80_);
v___x_82_ = lean_nat_dec_lt(v___x_81_, v___x_11_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; 
lean_dec(v___x_81_);
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_83_ = lean_box(0);
return v___x_83_;
}
else
{
lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; uint8_t v___x_87_; uint8_t v___y_89_; uint8_t v___x_113_; uint8_t v___x_114_; uint8_t v___x_115_; 
v___x_84_ = lean_unsigned_to_nat(1u);
v___x_85_ = lean_nat_add(v_i_2_, v___x_84_);
v___x_86_ = lean_byte_array_fget(v_b_1_, v___x_85_);
lean_dec(v___x_85_);
v___x_87_ = lean_byte_array_fget(v_b_1_, v___x_81_);
lean_dec(v___x_81_);
v___x_113_ = lean_uint8_land(v___x_86_, v___x_22_);
v___x_114_ = lean_uint8_dec_eq(v___x_113_, v___x_16_);
v___x_115_ = lean_bool_not(v___x_114_);
if (v___x_115_ == 0)
{
uint8_t v___x_116_; uint8_t v___x_117_; uint8_t v___x_118_; 
v___x_116_ = lean_uint8_land(v___x_87_, v___x_22_);
v___x_117_ = lean_uint8_dec_eq(v___x_116_, v___x_16_);
v___x_118_ = lean_bool_not(v___x_117_);
v___y_89_ = v___x_118_;
goto v___jp_88_;
}
else
{
v___y_89_ = v___x_115_;
goto v___jp_88_;
}
v___jp_88_:
{
if (v___y_89_ == 0)
{
uint8_t v___x_90_; uint8_t v_b_u2080_91_; uint8_t v___x_92_; uint8_t v_b_u2081_93_; uint8_t v_b_u2082_94_; uint32_t v___x_95_; uint32_t v___x_96_; uint32_t v___x_97_; uint32_t v___x_98_; uint32_t v___x_99_; uint32_t v___x_100_; uint32_t v___x_101_; uint32_t v___x_102_; uint32_t v_r_103_; uint32_t v___x_104_; uint8_t v___x_105_; 
v___x_90_ = 15;
v_b_u2080_91_ = lean_uint8_land(v___x_15_, v___x_90_);
v___x_92_ = 63;
v_b_u2081_93_ = lean_uint8_land(v___x_86_, v___x_92_);
v_b_u2082_94_ = lean_uint8_land(v___x_87_, v___x_92_);
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
else
{
lean_object* v___x_112_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_112_ = lean_box(0);
return v___x_112_;
}
}
}
}
}
else
{
lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_119_ = lean_unsigned_to_nat(1u);
v___x_120_ = lean_nat_add(v_i_2_, v___x_119_);
v___x_121_ = lean_nat_dec_lt(v___x_120_, v___x_11_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; 
lean_dec(v___x_120_);
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_122_ = lean_box(0);
return v___x_122_;
}
else
{
uint8_t v___x_123_; uint8_t v___x_124_; uint8_t v___x_125_; uint8_t v___x_126_; 
v___x_123_ = lean_byte_array_fget(v_b_1_, v___x_120_);
lean_dec(v___x_120_);
v___x_124_ = lean_uint8_land(v___x_123_, v___x_22_);
v___x_125_ = lean_uint8_dec_eq(v___x_124_, v___x_16_);
v___x_126_ = lean_bool_not(v___x_125_);
if (v___x_126_ == 0)
{
uint8_t v___x_127_; uint8_t v_b_u2080_128_; uint8_t v___x_129_; uint8_t v_b_u2081_130_; uint32_t v___x_131_; uint32_t v___x_132_; uint32_t v___x_133_; uint32_t v___x_134_; uint32_t v_r_135_; uint32_t v___x_136_; uint8_t v___x_137_; 
v___x_127_ = 31;
v_b_u2080_128_ = lean_uint8_land(v___x_15_, v___x_127_);
v___x_129_ = 63;
v_b_u2081_130_ = lean_uint8_land(v___x_123_, v___x_129_);
v___x_131_ = lean_uint8_to_uint32(v_b_u2080_128_);
v___x_132_ = 6;
v___x_133_ = lean_uint32_shift_left(v___x_131_, v___x_132_);
v___x_134_ = lean_uint8_to_uint32(v_b_u2081_130_);
v_r_135_ = lean_uint32_lor(v___x_133_, v___x_134_);
v___x_136_ = 128;
v___x_137_ = lean_uint32_dec_lt(v_r_135_, v___x_136_);
if (v___x_137_ == 0)
{
v_val_5_ = v_r_135_;
goto v___jp_4_;
}
else
{
lean_object* v___x_138_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_138_ = lean_box(0);
return v___x_138_;
}
}
else
{
lean_object* v___x_139_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_139_ = lean_box(0);
return v___x_139_;
}
}
}
}
else
{
uint32_t v___x_140_; 
v___x_140_ = lean_uint8_to_uint32(v___x_15_);
v_val_5_ = v___x_140_;
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
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go___redArg___boxed(lean_object* v_b_141_, lean_object* v_i_142_, lean_object* v_acc_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_ByteArray_utf8Decode_x3f_go___redArg(v_b_141_, v_i_142_, v_acc_143_);
lean_dec_ref(v_b_141_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go(lean_object* v_b_145_, lean_object* v_i_146_, lean_object* v_acc_147_, lean_object* v_hi_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_ByteArray_utf8Decode_x3f_go___redArg(v_b_145_, v_i_146_, v_acc_147_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go___boxed(lean_object* v_b_150_, lean_object* v_i_151_, lean_object* v_acc_152_, lean_object* v_hi_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_ByteArray_utf8Decode_x3f_go(v_b_150_, v_i_151_, v_acc_152_, v_hi_153_);
lean_dec_ref(v_b_150_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__1_splitter___redArg(lean_object* v_x_155_, lean_object* v_h__1_156_, lean_object* v_h__2_157_){
_start:
{
if (lean_obj_tag(v_x_155_) == 0)
{
lean_object* v___x_158_; 
lean_dec(v_h__2_157_);
v___x_158_ = lean_apply_1(v_h__1_156_, lean_box(0));
return v___x_158_;
}
else
{
lean_object* v_val_159_; lean_object* v___x_160_; 
lean_dec(v_h__1_156_);
v_val_159_ = lean_ctor_get(v_x_155_, 0);
lean_inc(v_val_159_);
lean_dec_ref_known(v_x_155_, 1);
v___x_160_ = lean_apply_2(v_h__2_157_, v_val_159_, lean_box(0));
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__1_splitter(lean_object* v_motive_161_, lean_object* v_x_162_, lean_object* v_h__1_163_, lean_object* v_h__2_164_){
_start:
{
if (lean_obj_tag(v_x_162_) == 0)
{
lean_object* v___x_165_; 
lean_dec(v_h__2_164_);
v___x_165_ = lean_apply_1(v_h__1_163_, lean_box(0));
return v___x_165_;
}
else
{
lean_object* v_val_166_; lean_object* v___x_167_; 
lean_dec(v_h__1_163_);
v_val_166_ = lean_ctor_get(v_x_162_, 0);
lean_inc(v_val_166_);
lean_dec_ref_known(v_x_162_, 1);
v___x_167_ = lean_apply_2(v_h__2_164_, v_val_166_, lean_box(0));
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f(lean_object* v_b_170_){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = ((lean_object*)(l_ByteArray_utf8Decode_x3f___closed__0));
v___x_173_ = l_ByteArray_utf8Decode_x3f_go___redArg(v_b_170_, v___x_171_, v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f___boxed(lean_object* v_b_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_ByteArray_utf8Decode_x3f(v_b_174_);
lean_dec_ref(v_b_174_);
return v_res_175_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8_go___redArg(lean_object* v_b_176_, lean_object* v_i_177_){
_start:
{
lean_object* v___y_179_; uint8_t v___y_183_; lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_200_ = lean_byte_array_size(v_b_176_);
v___x_201_ = lean_nat_dec_lt(v_i_177_, v___x_200_);
if (v___x_201_ == 0)
{
uint8_t v___x_202_; 
lean_dec(v_i_177_);
v___x_202_ = 1;
return v___x_202_;
}
else
{
if (v___x_201_ == 0)
{
lean_dec(v_i_177_);
return v___x_201_;
}
else
{
uint8_t v___x_203_; uint8_t v___x_204_; uint8_t v___x_205_; uint8_t v___x_206_; uint8_t v___x_207_; 
v___x_203_ = lean_byte_array_fget(v_b_176_, v_i_177_);
v___x_204_ = 128;
v___x_205_ = lean_uint8_land(v___x_203_, v___x_204_);
v___x_206_ = 0;
v___x_207_ = lean_uint8_dec_eq(v___x_205_, v___x_206_);
if (v___x_207_ == 0)
{
uint8_t v___x_208_; uint8_t v___x_209_; uint8_t v___x_210_; uint8_t v___x_211_; 
v___x_208_ = 224;
v___x_209_ = lean_uint8_land(v___x_203_, v___x_208_);
v___x_210_ = 192;
v___x_211_ = lean_uint8_dec_eq(v___x_209_, v___x_210_);
if (v___x_211_ == 0)
{
uint8_t v___x_212_; uint8_t v___x_213_; uint8_t v___x_214_; 
v___x_212_ = 240;
v___x_213_ = lean_uint8_land(v___x_203_, v___x_212_);
v___x_214_ = lean_uint8_dec_eq(v___x_213_, v___x_208_);
if (v___x_214_ == 0)
{
uint8_t v___x_215_; uint8_t v___x_216_; uint8_t v___x_217_; 
v___x_215_ = 248;
v___x_216_ = lean_uint8_land(v___x_203_, v___x_215_);
v___x_217_ = lean_uint8_dec_eq(v___x_216_, v___x_212_);
if (v___x_217_ == 0)
{
v___y_183_ = v___x_217_;
goto v___jp_182_;
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_218_ = lean_unsigned_to_nat(3u);
v___x_219_ = lean_nat_add(v_i_177_, v___x_218_);
v___x_220_ = lean_nat_dec_lt(v___x_219_, v___x_200_);
if (v___x_220_ == 0)
{
lean_dec(v___x_219_);
v___y_183_ = v___x_214_;
goto v___jp_182_;
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; uint8_t v___x_227_; uint8_t v___y_229_; uint8_t v___x_256_; uint8_t v___x_257_; uint8_t v___x_258_; 
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = lean_nat_add(v_i_177_, v___x_221_);
v___x_223_ = lean_byte_array_fget(v_b_176_, v___x_222_);
lean_dec(v___x_222_);
v___x_224_ = lean_unsigned_to_nat(2u);
v___x_225_ = lean_nat_add(v_i_177_, v___x_224_);
v___x_226_ = lean_byte_array_fget(v_b_176_, v___x_225_);
lean_dec(v___x_225_);
v___x_227_ = lean_byte_array_fget(v_b_176_, v___x_219_);
lean_dec(v___x_219_);
v___x_256_ = lean_uint8_land(v___x_223_, v___x_210_);
v___x_257_ = lean_uint8_dec_eq(v___x_256_, v___x_204_);
v___x_258_ = lean_bool_not(v___x_257_);
if (v___x_258_ == 0)
{
uint8_t v___x_259_; uint8_t v___x_260_; uint8_t v___x_261_; 
v___x_259_ = lean_uint8_land(v___x_226_, v___x_210_);
v___x_260_ = lean_uint8_dec_eq(v___x_259_, v___x_204_);
v___x_261_ = lean_bool_not(v___x_260_);
v___y_229_ = v___x_261_;
goto v___jp_228_;
}
else
{
v___y_229_ = v___x_258_;
goto v___jp_228_;
}
v___jp_228_:
{
if (v___y_229_ == 0)
{
uint8_t v___x_230_; uint8_t v___x_231_; uint8_t v___x_232_; 
v___x_230_ = lean_uint8_land(v___x_227_, v___x_210_);
v___x_231_ = lean_uint8_dec_eq(v___x_230_, v___x_204_);
v___x_232_ = lean_bool_not(v___x_231_);
if (v___x_232_ == 0)
{
uint8_t v___x_233_; uint8_t v_b_u2080_234_; uint8_t v___x_235_; uint8_t v_b_u2081_236_; uint8_t v_b_u2082_237_; uint8_t v_b_u2083_238_; uint32_t v___x_239_; uint32_t v___x_240_; uint32_t v___x_241_; uint32_t v___x_242_; uint32_t v___x_243_; uint32_t v___x_244_; uint32_t v___x_245_; uint32_t v___x_246_; uint32_t v___x_247_; uint32_t v___x_248_; uint32_t v___x_249_; uint32_t v___x_250_; uint32_t v_r_251_; uint32_t v___x_252_; uint8_t v___x_253_; 
v___x_233_ = 7;
v_b_u2080_234_ = lean_uint8_land(v___x_203_, v___x_233_);
v___x_235_ = 63;
v_b_u2081_236_ = lean_uint8_land(v___x_223_, v___x_235_);
v_b_u2082_237_ = lean_uint8_land(v___x_226_, v___x_235_);
v_b_u2083_238_ = lean_uint8_land(v___x_227_, v___x_235_);
v___x_239_ = lean_uint8_to_uint32(v_b_u2080_234_);
v___x_240_ = 18;
v___x_241_ = lean_uint32_shift_left(v___x_239_, v___x_240_);
v___x_242_ = lean_uint8_to_uint32(v_b_u2081_236_);
v___x_243_ = 12;
v___x_244_ = lean_uint32_shift_left(v___x_242_, v___x_243_);
v___x_245_ = lean_uint32_lor(v___x_241_, v___x_244_);
v___x_246_ = lean_uint8_to_uint32(v_b_u2082_237_);
v___x_247_ = 6;
v___x_248_ = lean_uint32_shift_left(v___x_246_, v___x_247_);
v___x_249_ = lean_uint32_lor(v___x_245_, v___x_248_);
v___x_250_ = lean_uint8_to_uint32(v_b_u2083_238_);
v_r_251_ = lean_uint32_lor(v___x_249_, v___x_250_);
v___x_252_ = 65536;
v___x_253_ = lean_uint32_dec_le(v___x_252_, v_r_251_);
if (v___x_253_ == 0)
{
v___y_183_ = v___x_232_;
goto v___jp_182_;
}
else
{
uint32_t v___x_254_; uint8_t v___x_255_; 
v___x_254_ = 1114111;
v___x_255_ = lean_uint32_dec_le(v_r_251_, v___x_254_);
if (v___x_255_ == 0)
{
v___y_183_ = v___x_232_;
goto v___jp_182_;
}
else
{
v___y_183_ = v___x_217_;
goto v___jp_182_;
}
}
}
else
{
lean_dec(v_i_177_);
return v___y_229_;
}
}
else
{
v___y_183_ = v___x_214_;
goto v___jp_182_;
}
}
}
}
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_262_ = lean_unsigned_to_nat(2u);
v___x_263_ = lean_nat_add(v_i_177_, v___x_262_);
v___x_264_ = lean_nat_dec_lt(v___x_263_, v___x_200_);
if (v___x_264_ == 0)
{
lean_dec(v___x_263_);
v___y_183_ = v___x_211_;
goto v___jp_182_;
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; uint8_t v___x_268_; uint8_t v___y_270_; uint8_t v___x_291_; uint8_t v___x_292_; uint8_t v___x_293_; 
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = lean_nat_add(v_i_177_, v___x_265_);
v___x_267_ = lean_byte_array_fget(v_b_176_, v___x_266_);
lean_dec(v___x_266_);
v___x_268_ = lean_byte_array_fget(v_b_176_, v___x_263_);
lean_dec(v___x_263_);
v___x_291_ = lean_uint8_land(v___x_267_, v___x_210_);
v___x_292_ = lean_uint8_dec_eq(v___x_291_, v___x_204_);
v___x_293_ = lean_bool_not(v___x_292_);
if (v___x_293_ == 0)
{
uint8_t v___x_294_; uint8_t v___x_295_; uint8_t v___x_296_; 
v___x_294_ = lean_uint8_land(v___x_268_, v___x_210_);
v___x_295_ = lean_uint8_dec_eq(v___x_294_, v___x_204_);
v___x_296_ = lean_bool_not(v___x_295_);
v___y_270_ = v___x_296_;
goto v___jp_269_;
}
else
{
v___y_270_ = v___x_293_;
goto v___jp_269_;
}
v___jp_269_:
{
if (v___y_270_ == 0)
{
uint8_t v___x_271_; uint8_t v_b_u2080_272_; uint8_t v___x_273_; uint8_t v_b_u2081_274_; uint8_t v_b_u2082_275_; uint32_t v___x_276_; uint32_t v___x_277_; uint32_t v___x_278_; uint32_t v___x_279_; uint32_t v___x_280_; uint32_t v___x_281_; uint32_t v___x_282_; uint32_t v___x_283_; uint32_t v_r_284_; uint32_t v___x_285_; uint8_t v___x_286_; 
v___x_271_ = 15;
v_b_u2080_272_ = lean_uint8_land(v___x_203_, v___x_271_);
v___x_273_ = 63;
v_b_u2081_274_ = lean_uint8_land(v___x_267_, v___x_273_);
v_b_u2082_275_ = lean_uint8_land(v___x_268_, v___x_273_);
v___x_276_ = lean_uint8_to_uint32(v_b_u2080_272_);
v___x_277_ = 12;
v___x_278_ = lean_uint32_shift_left(v___x_276_, v___x_277_);
v___x_279_ = lean_uint8_to_uint32(v_b_u2081_274_);
v___x_280_ = 6;
v___x_281_ = lean_uint32_shift_left(v___x_279_, v___x_280_);
v___x_282_ = lean_uint32_lor(v___x_278_, v___x_281_);
v___x_283_ = lean_uint8_to_uint32(v_b_u2082_275_);
v_r_284_ = lean_uint32_lor(v___x_282_, v___x_283_);
v___x_285_ = 2048;
v___x_286_ = lean_uint32_dec_le(v___x_285_, v_r_284_);
if (v___x_286_ == 0)
{
lean_dec(v_i_177_);
return v___y_270_;
}
else
{
uint32_t v___x_287_; uint8_t v___x_288_; 
v___x_287_ = 55296;
v___x_288_ = lean_uint32_dec_lt(v_r_284_, v___x_287_);
if (v___x_288_ == 0)
{
uint32_t v___x_289_; uint8_t v___x_290_; 
v___x_289_ = 57343;
v___x_290_ = lean_uint32_dec_lt(v___x_289_, v_r_284_);
if (v___x_290_ == 0)
{
lean_dec(v_i_177_);
return v___y_270_;
}
else
{
v___y_183_ = v___x_214_;
goto v___jp_182_;
}
}
else
{
v___y_183_ = v___x_214_;
goto v___jp_182_;
}
}
}
else
{
v___y_183_ = v___x_211_;
goto v___jp_182_;
}
}
}
}
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_297_ = lean_unsigned_to_nat(1u);
v___x_298_ = lean_nat_add(v_i_177_, v___x_297_);
v___x_299_ = lean_nat_dec_lt(v___x_298_, v___x_200_);
if (v___x_299_ == 0)
{
lean_dec(v___x_298_);
v___y_183_ = v___x_207_;
goto v___jp_182_;
}
else
{
uint8_t v___x_300_; uint8_t v___x_301_; uint8_t v___x_302_; uint8_t v___x_303_; 
v___x_300_ = lean_byte_array_fget(v_b_176_, v___x_298_);
lean_dec(v___x_298_);
v___x_301_ = lean_uint8_land(v___x_300_, v___x_210_);
v___x_302_ = lean_uint8_dec_eq(v___x_301_, v___x_204_);
v___x_303_ = lean_bool_not(v___x_302_);
if (v___x_303_ == 0)
{
uint8_t v___x_304_; uint8_t v_b_u2080_305_; uint8_t v___x_306_; uint8_t v_b_u2081_307_; uint32_t v___x_308_; uint32_t v___x_309_; uint32_t v___x_310_; uint32_t v___x_311_; uint32_t v_r_312_; uint32_t v___x_313_; uint8_t v___x_314_; 
v___x_304_ = 31;
v_b_u2080_305_ = lean_uint8_land(v___x_203_, v___x_304_);
v___x_306_ = 63;
v_b_u2081_307_ = lean_uint8_land(v___x_300_, v___x_306_);
v___x_308_ = lean_uint8_to_uint32(v_b_u2080_305_);
v___x_309_ = 6;
v___x_310_ = lean_uint32_shift_left(v___x_308_, v___x_309_);
v___x_311_ = lean_uint8_to_uint32(v_b_u2081_307_);
v_r_312_ = lean_uint32_lor(v___x_310_, v___x_311_);
v___x_313_ = 128;
v___x_314_ = lean_uint32_dec_le(v___x_313_, v_r_312_);
v___y_183_ = v___x_314_;
goto v___jp_182_;
}
else
{
v___y_183_ = v___x_207_;
goto v___jp_182_;
}
}
}
}
else
{
v___y_183_ = v___x_207_;
goto v___jp_182_;
}
}
}
v___jp_178_:
{
lean_object* v___x_180_; 
v___x_180_ = lean_nat_add(v_i_177_, v___y_179_);
lean_dec(v_i_177_);
v_i_177_ = v___x_180_;
goto _start;
}
v___jp_182_:
{
if (v___y_183_ == 0)
{
lean_dec(v_i_177_);
return v___y_183_;
}
else
{
uint8_t v___x_184_; uint8_t v___x_185_; uint8_t v___x_186_; uint8_t v___x_187_; uint8_t v___x_188_; 
v___x_184_ = lean_byte_array_fget(v_b_176_, v_i_177_);
v___x_185_ = 128;
v___x_186_ = lean_uint8_land(v___x_184_, v___x_185_);
v___x_187_ = 0;
v___x_188_ = lean_uint8_dec_eq(v___x_186_, v___x_187_);
if (v___x_188_ == 0)
{
uint8_t v___x_189_; uint8_t v___x_190_; uint8_t v___x_191_; uint8_t v___x_192_; 
v___x_189_ = 224;
v___x_190_ = lean_uint8_land(v___x_184_, v___x_189_);
v___x_191_ = 192;
v___x_192_ = lean_uint8_dec_eq(v___x_190_, v___x_191_);
if (v___x_192_ == 0)
{
uint8_t v___x_193_; uint8_t v___x_194_; uint8_t v___x_195_; 
v___x_193_ = 240;
v___x_194_ = lean_uint8_land(v___x_184_, v___x_193_);
v___x_195_ = lean_uint8_dec_eq(v___x_194_, v___x_189_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; 
v___x_196_ = lean_unsigned_to_nat(4u);
v___y_179_ = v___x_196_;
goto v___jp_178_;
}
else
{
lean_object* v___x_197_; 
v___x_197_ = lean_unsigned_to_nat(3u);
v___y_179_ = v___x_197_;
goto v___jp_178_;
}
}
else
{
lean_object* v___x_198_; 
v___x_198_ = lean_unsigned_to_nat(2u);
v___y_179_ = v___x_198_;
goto v___jp_178_;
}
}
else
{
lean_object* v___x_199_; 
v___x_199_ = lean_unsigned_to_nat(1u);
v___y_179_ = v___x_199_;
goto v___jp_178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___redArg___boxed(lean_object* v_b_315_, lean_object* v_i_316_){
_start:
{
uint8_t v_res_317_; lean_object* v_r_318_; 
v_res_317_ = l_ByteArray_validateUTF8_go___redArg(v_b_315_, v_i_316_);
lean_dec_ref(v_b_315_);
v_r_318_ = lean_box(v_res_317_);
return v_r_318_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8_go(lean_object* v_b_319_, lean_object* v_i_320_, lean_object* v_hi_321_){
_start:
{
uint8_t v___x_322_; 
v___x_322_ = l_ByteArray_validateUTF8_go___redArg(v_b_319_, v_i_320_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___boxed(lean_object* v_b_323_, lean_object* v_i_324_, lean_object* v_hi_325_){
_start:
{
uint8_t v_res_326_; lean_object* v_r_327_; 
v_res_326_ = l_ByteArray_validateUTF8_go(v_b_323_, v_i_324_, v_hi_325_);
lean_dec_ref(v_b_323_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(uint8_t v_x_328_, lean_object* v_h__1_329_, lean_object* v_h__2_330_){
_start:
{
if (v_x_328_ == 0)
{
lean_object* v___x_331_; 
lean_dec(v_h__2_330_);
v___x_331_ = lean_apply_1(v_h__1_329_, lean_box(0));
return v___x_331_;
}
else
{
lean_object* v___x_332_; 
lean_dec(v_h__1_329_);
v___x_332_ = lean_apply_1(v_h__2_330_, lean_box(0));
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg___boxed(lean_object* v_x_333_, lean_object* v_h__1_334_, lean_object* v_h__2_335_){
_start:
{
uint8_t v_x_26__boxed_336_; lean_object* v_res_337_; 
v_x_26__boxed_336_ = lean_unbox(v_x_333_);
v_res_337_ = l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(v_x_26__boxed_336_, v_h__1_334_, v_h__2_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(lean_object* v_motive_338_, uint8_t v_x_339_, lean_object* v_h__1_340_, lean_object* v_h__2_341_){
_start:
{
if (v_x_339_ == 0)
{
lean_object* v___x_342_; 
lean_dec(v_h__2_341_);
v___x_342_ = lean_apply_1(v_h__1_340_, lean_box(0));
return v___x_342_;
}
else
{
lean_object* v___x_343_; 
lean_dec(v_h__1_340_);
v___x_343_ = lean_apply_1(v_h__2_341_, lean_box(0));
return v___x_343_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___boxed(lean_object* v_motive_344_, lean_object* v_x_345_, lean_object* v_h__1_346_, lean_object* v_h__2_347_){
_start:
{
uint8_t v_x_33__boxed_348_; lean_object* v_res_349_; 
v_x_33__boxed_348_ = lean_unbox(v_x_345_);
v_res_349_ = l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(v_motive_344_, v_x_33__boxed_348_, v_h__1_346_, v_h__2_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8___boxed(lean_object* v_b_351_){
_start:
{
uint8_t v_res_352_; lean_object* v_r_353_; 
v_res_352_ = lean_string_validate_utf8(v_b_351_);
lean_dec_ref(v_b_351_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT uint8_t l_instDecidableIsValidUTF8(lean_object* v_b_354_){
_start:
{
uint8_t v___x_355_; 
v___x_355_ = lean_string_validate_utf8(v_b_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_instDecidableIsValidUTF8___boxed(lean_object* v_b_356_){
_start:
{
uint8_t v_res_357_; lean_object* v_r_358_; 
v_res_357_ = l_instDecidableIsValidUTF8(v_b_356_);
lean_dec_ref(v_b_356_);
v_r_358_ = lean_box(v_res_357_);
return v_r_358_;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_x3f(lean_object* v_a_359_){
_start:
{
uint8_t v___x_360_; 
v___x_360_ = lean_string_validate_utf8(v_a_359_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; 
lean_dec_ref(v_a_359_);
v___x_361_ = lean_box(0);
return v___x_361_;
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_string_from_utf8_unchecked(v_a_359_);
v___x_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
return v___x_363_;
}
}
}
static lean_object* _init_l_String_fromUTF8_x21___closed__4(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_368_ = ((lean_object*)(l_String_fromUTF8_x21___closed__3));
v___x_369_ = lean_unsigned_to_nat(46u);
v___x_370_ = lean_unsigned_to_nat(193u);
v___x_371_ = ((lean_object*)(l_String_fromUTF8_x21___closed__2));
v___x_372_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_373_ = l_mkPanicMessageWithDecl(v___x_372_, v___x_371_, v___x_370_, v___x_369_, v___x_368_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_x21(lean_object* v_a_374_){
_start:
{
uint8_t v___x_375_; 
v___x_375_ = lean_string_validate_utf8(v_a_374_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
lean_dec_ref(v_a_374_);
v___x_376_ = ((lean_object*)(l_String_fromUTF8_x21___closed__0));
v___x_377_ = lean_obj_once(&l_String_fromUTF8_x21___closed__4, &l_String_fromUTF8_x21___closed__4_once, _init_l_String_fromUTF8_x21___closed__4);
v___x_378_ = l_panic___redArg(v___x_376_, v___x_377_);
return v___x_378_;
}
else
{
lean_object* v___x_379_; 
v___x_379_ = lean_string_from_utf8_unchecked(v_a_374_);
return v___x_379_;
}
}
}
LEAN_EXPORT lean_object* l_String_Internal_toArray(lean_object* v_b_380_){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v_val_385_; 
v___x_381_ = lean_string_to_utf8(v_b_380_);
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = ((lean_object*)(l_ByteArray_utf8Decode_x3f___closed__0));
v___x_384_ = l_ByteArray_utf8Decode_x3f_go___redArg(v___x_381_, v___x_382_, v___x_383_);
lean_dec_ref(v___x_381_);
v_val_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_val_385_);
lean_dec(v___x_384_);
return v_val_385_;
}
}
LEAN_EXPORT lean_object* l_String_toList___boxed(lean_object* v_s_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = lean_string_data(v_s_387_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_String_data___boxed(lean_object* v_b_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = lean_string_data(v_b_390_);
return v_res_391_;
}
}
static lean_object* _init_l_String_instLT(void){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = lean_box(0);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_String_decidableLT___boxed(lean_object* v_s_u2081_395_, lean_object* v_s_u2082_396_){
_start:
{
uint8_t v_res_397_; lean_object* v_r_398_; 
v_res_397_ = lean_string_dec_lt(v_s_u2081_395_, v_s_u2082_396_);
lean_dec_ref(v_s_u2082_396_);
lean_dec_ref(v_s_u2081_395_);
v_r_398_ = lean_box(v_res_397_);
return v_r_398_;
}
}
static lean_object* _init_l_String_instLE(void){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = lean_box(0);
return v___x_399_;
}
}
LEAN_EXPORT uint8_t l_String_decLE(lean_object* v_s_u2081_400_, lean_object* v_s_u2082_401_){
_start:
{
uint8_t v___x_402_; 
v___x_402_ = lean_string_dec_lt(v_s_u2082_401_, v_s_u2081_400_);
if (v___x_402_ == 0)
{
uint8_t v___x_403_; 
v___x_403_ = 1;
return v___x_403_;
}
else
{
uint8_t v___x_404_; 
v___x_404_ = 0;
return v___x_404_;
}
}
}
LEAN_EXPORT lean_object* l_String_decLE___boxed(lean_object* v_s_u2081_405_, lean_object* v_s_u2082_406_){
_start:
{
uint8_t v_res_407_; lean_object* v_r_408_; 
v_res_407_ = l_String_decLE(v_s_u2081_405_, v_s_u2082_406_);
lean_dec_ref(v_s_u2082_406_);
lean_dec_ref(v_s_u2081_405_);
v_r_408_ = lean_box(v_res_407_);
return v_r_408_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValid___boxed(lean_object* v_s_411_, lean_object* v_p_412_){
_start:
{
uint8_t v_res_413_; lean_object* v_r_414_; 
v_res_413_ = lean_string_is_valid_pos(v_s_411_, v_p_412_);
lean_dec(v_p_412_);
lean_dec_ref(v_s_411_);
v_r_414_ = lean_box(v_res_413_);
return v_r_414_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsValid(lean_object* v_s_415_, lean_object* v_p_416_){
_start:
{
uint8_t v___x_417_; 
v___x_417_ = lean_string_is_valid_pos(v_s_415_, v_p_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsValid___boxed(lean_object* v_s_418_, lean_object* v_p_419_){
_start:
{
uint8_t v_res_420_; lean_object* v_r_421_; 
v_res_420_ = l_String_instDecidableIsValid(v_s_418_, v_p_419_);
lean_dec(v_p_419_);
lean_dec_ref(v_s_418_);
v_r_421_ = lean_box(v_res_420_);
return v_r_421_;
}
}
LEAN_EXPORT lean_object* l_String_extract___boxed(lean_object* v_s_425_, lean_object* v_b_426_, lean_object* v_e_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = lean_string_utf8_extract(v_s_425_, v_b_426_, v_e_427_);
lean_dec(v_e_427_);
lean_dec(v_b_426_);
lean_dec_ref(v_s_425_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_extract(lean_object* v_s_429_, lean_object* v_b_430_, lean_object* v_e_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = lean_string_utf8_extract(v_s_429_, v_b_430_, v_e_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_extract___boxed(lean_object* v_s_433_, lean_object* v_b_434_, lean_object* v_e_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_String_Pos_extract(v_s_433_, v_b_434_, v_e_435_);
lean_dec(v_e_435_);
lean_dec(v_b_434_);
lean_dec_ref(v_s_433_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_copy(lean_object* v_s_437_){
_start:
{
lean_object* v_str_438_; lean_object* v_startInclusive_439_; lean_object* v_endExclusive_440_; lean_object* v___x_441_; 
v_str_438_ = lean_ctor_get(v_s_437_, 0);
v_startInclusive_439_ = lean_ctor_get(v_s_437_, 1);
v_endExclusive_440_ = lean_ctor_get(v_s_437_, 2);
v___x_441_ = lean_string_utf8_extract(v_str_438_, v_startInclusive_439_, v_endExclusive_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_copy___boxed(lean_object* v_s_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_String_Slice_copy(v_s_442_);
lean_dec_ref(v_s_442_);
return v_res_443_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_isValidForSlice(lean_object* v_s_444_, lean_object* v_p_445_){
_start:
{
lean_object* v_str_446_; lean_object* v_startInclusive_447_; lean_object* v_endExclusive_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v_str_446_ = lean_ctor_get(v_s_444_, 0);
v_startInclusive_447_ = lean_ctor_get(v_s_444_, 1);
v_endExclusive_448_ = lean_ctor_get(v_s_444_, 2);
v___x_449_ = lean_nat_sub(v_endExclusive_448_, v_startInclusive_447_);
v___x_450_ = lean_nat_dec_lt(v_p_445_, v___x_449_);
if (v___x_450_ == 0)
{
uint8_t v___x_451_; 
v___x_451_ = lean_nat_dec_eq(v_p_445_, v___x_449_);
lean_dec(v___x_449_);
return v___x_451_;
}
else
{
lean_object* v___x_452_; uint8_t v___x_453_; uint8_t v___x_454_; 
lean_dec(v___x_449_);
v___x_452_ = lean_nat_add(v_startInclusive_447_, v_p_445_);
v___x_453_ = lean_string_get_byte_fast(v_str_446_, v___x_452_);
v___x_454_ = l_UInt8_instDecidableIsUTF8FirstByte___aux__1(v___x_453_);
return v___x_454_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValidForSlice___boxed(lean_object* v_s_455_, lean_object* v_p_456_){
_start:
{
uint8_t v_res_457_; lean_object* v_r_458_; 
v_res_457_ = l_String_Pos_Raw_isValidForSlice(v_s_455_, v_p_456_);
lean_dec(v_p_456_);
lean_dec_ref(v_s_455_);
v_r_458_ = lean_box(v_res_457_);
return v_r_458_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsValidForSlice(lean_object* v_s_459_, lean_object* v_p_460_){
_start:
{
uint8_t v___x_461_; 
v___x_461_ = l_String_Pos_Raw_isValidForSlice(v_s_459_, v_p_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsValidForSlice___boxed(lean_object* v_s_462_, lean_object* v_p_463_){
_start:
{
uint8_t v_res_464_; lean_object* v_r_465_; 
v_res_464_ = l_String_instDecidableIsValidForSlice(v_s_462_, v_p_463_);
lean_dec(v_p_463_);
lean_dec_ref(v_s_462_);
v_r_465_ = lean_box(v_res_464_);
return v_r_465_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str(lean_object* v_s_466_, lean_object* v_pos_467_){
_start:
{
lean_object* v_startInclusive_468_; lean_object* v___x_469_; 
v_startInclusive_468_ = lean_ctor_get(v_s_466_, 1);
v___x_469_ = lean_nat_add(v_startInclusive_468_, v_pos_467_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str___boxed(lean_object* v_s_470_, lean_object* v_pos_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_String_Slice_Pos_str(v_s_470_, v_pos_471_);
lean_dec(v_pos_471_);
lean_dec_ref(v_s_470_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg(lean_object* v_s_473_, lean_object* v_pos_474_){
_start:
{
lean_object* v_startInclusive_475_; lean_object* v___x_476_; 
v_startInclusive_475_ = lean_ctor_get(v_s_473_, 1);
v___x_476_ = lean_nat_sub(v_pos_474_, v_startInclusive_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg___boxed(lean_object* v_s_477_, lean_object* v_pos_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_String_Slice_Pos_ofStr___redArg(v_s_477_, v_pos_478_);
lean_dec(v_pos_478_);
lean_dec_ref(v_s_477_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr(lean_object* v_s_480_, lean_object* v_pos_481_, lean_object* v_h_u2081_482_, lean_object* v_h_u2082_483_){
_start:
{
lean_object* v_startInclusive_484_; lean_object* v___x_485_; 
v_startInclusive_484_ = lean_ctor_get(v_s_480_, 1);
v___x_485_ = lean_nat_sub(v_pos_481_, v_startInclusive_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___boxed(lean_object* v_s_486_, lean_object* v_pos_487_, lean_object* v_h_u2081_488_, lean_object* v_h_u2082_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_String_Slice_Pos_ofStr(v_s_486_, v_pos_487_, v_h_u2081_488_, v_h_u2082_489_);
lean_dec(v_pos_487_);
lean_dec_ref(v_s_486_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom(lean_object* v_s_491_, lean_object* v_pos_492_){
_start:
{
lean_object* v_str_493_; lean_object* v_startInclusive_494_; lean_object* v_endExclusive_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_503_; 
v_str_493_ = lean_ctor_get(v_s_491_, 0);
v_startInclusive_494_ = lean_ctor_get(v_s_491_, 1);
v_endExclusive_495_ = lean_ctor_get(v_s_491_, 2);
v_isSharedCheck_503_ = !lean_is_exclusive(v_s_491_);
if (v_isSharedCheck_503_ == 0)
{
v___x_497_ = v_s_491_;
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_endExclusive_495_);
lean_inc(v_startInclusive_494_);
lean_inc(v_str_493_);
lean_dec(v_s_491_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_499_ = lean_nat_add(v_startInclusive_494_, v_pos_492_);
lean_dec(v_startInclusive_494_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 1, v___x_499_);
v___x_501_ = v___x_497_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_str_493_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v___x_499_);
lean_ctor_set(v_reuseFailAlloc_502_, 2, v_endExclusive_495_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom___boxed(lean_object* v_s_504_, lean_object* v_pos_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_String_Slice_sliceFrom(v_s_504_, v_pos_505_);
lean_dec(v_pos_505_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStart(lean_object* v_s_507_, lean_object* v_pos_508_){
_start:
{
lean_object* v_str_509_; lean_object* v_startInclusive_510_; lean_object* v_endExclusive_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_519_; 
v_str_509_ = lean_ctor_get(v_s_507_, 0);
v_startInclusive_510_ = lean_ctor_get(v_s_507_, 1);
v_endExclusive_511_ = lean_ctor_get(v_s_507_, 2);
v_isSharedCheck_519_ = !lean_is_exclusive(v_s_507_);
if (v_isSharedCheck_519_ == 0)
{
v___x_513_ = v_s_507_;
v_isShared_514_ = v_isSharedCheck_519_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_endExclusive_511_);
lean_inc(v_startInclusive_510_);
lean_inc(v_str_509_);
lean_dec(v_s_507_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_519_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_515_ = lean_nat_add(v_startInclusive_510_, v_pos_508_);
lean_dec(v_startInclusive_510_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 1, v___x_515_);
v___x_517_ = v___x_513_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_str_509_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_518_, 2, v_endExclusive_511_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStart___boxed(lean_object* v_s_520_, lean_object* v_pos_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_String_Slice_replaceStart(v_s_520_, v_pos_521_);
lean_dec(v_pos_521_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceTo(lean_object* v_s_523_, lean_object* v_pos_524_){
_start:
{
lean_object* v_str_525_; lean_object* v_startInclusive_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_534_; 
v_str_525_ = lean_ctor_get(v_s_523_, 0);
v_startInclusive_526_ = lean_ctor_get(v_s_523_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v_s_523_);
if (v_isSharedCheck_534_ == 0)
{
lean_object* v_unused_535_; 
v_unused_535_ = lean_ctor_get(v_s_523_, 2);
lean_dec(v_unused_535_);
v___x_528_ = v_s_523_;
v_isShared_529_ = v_isSharedCheck_534_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_startInclusive_526_);
lean_inc(v_str_525_);
lean_dec(v_s_523_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_534_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_530_ = lean_nat_add(v_startInclusive_526_, v_pos_524_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 2, v___x_530_);
v___x_532_ = v___x_528_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_str_525_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_startInclusive_526_);
lean_ctor_set(v_reuseFailAlloc_533_, 2, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceTo___boxed(lean_object* v_s_536_, lean_object* v_pos_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_String_Slice_sliceTo(v_s_536_, v_pos_537_);
lean_dec(v_pos_537_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd(lean_object* v_s_539_, lean_object* v_pos_540_){
_start:
{
lean_object* v_str_541_; lean_object* v_startInclusive_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_550_; 
v_str_541_ = lean_ctor_get(v_s_539_, 0);
v_startInclusive_542_ = lean_ctor_get(v_s_539_, 1);
v_isSharedCheck_550_ = !lean_is_exclusive(v_s_539_);
if (v_isSharedCheck_550_ == 0)
{
lean_object* v_unused_551_; 
v_unused_551_ = lean_ctor_get(v_s_539_, 2);
lean_dec(v_unused_551_);
v___x_544_ = v_s_539_;
v_isShared_545_ = v_isSharedCheck_550_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_startInclusive_542_);
lean_inc(v_str_541_);
lean_dec(v_s_539_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_550_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_546_ = lean_nat_add(v_startInclusive_542_, v_pos_540_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 2, v___x_546_);
v___x_548_ = v___x_544_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_str_541_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_startInclusive_542_);
lean_ctor_set(v_reuseFailAlloc_549_, 2, v___x_546_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd___boxed(lean_object* v_s_552_, lean_object* v_pos_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_String_Slice_replaceEnd(v_s_552_, v_pos_553_);
lean_dec(v_pos_553_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg(lean_object* v_s_555_, lean_object* v_newStart_556_, lean_object* v_newEnd_557_){
_start:
{
lean_object* v_str_558_; lean_object* v_startInclusive_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_568_; 
v_str_558_ = lean_ctor_get(v_s_555_, 0);
v_startInclusive_559_ = lean_ctor_get(v_s_555_, 1);
v_isSharedCheck_568_ = !lean_is_exclusive(v_s_555_);
if (v_isSharedCheck_568_ == 0)
{
lean_object* v_unused_569_; 
v_unused_569_ = lean_ctor_get(v_s_555_, 2);
lean_dec(v_unused_569_);
v___x_561_ = v_s_555_;
v_isShared_562_ = v_isSharedCheck_568_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_startInclusive_559_);
lean_inc(v_str_558_);
lean_dec(v_s_555_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_568_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_566_; 
v___x_563_ = lean_nat_add(v_startInclusive_559_, v_newStart_556_);
v___x_564_ = lean_nat_add(v_startInclusive_559_, v_newEnd_557_);
lean_dec(v_startInclusive_559_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 2, v___x_564_);
lean_ctor_set(v___x_561_, 1, v___x_563_);
v___x_566_ = v___x_561_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_str_558_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_567_, 2, v___x_564_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg___boxed(lean_object* v_s_570_, lean_object* v_newStart_571_, lean_object* v_newEnd_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_String_Slice_slice___redArg(v_s_570_, v_newStart_571_, v_newEnd_572_);
lean_dec(v_newEnd_572_);
lean_dec(v_newStart_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice(lean_object* v_s_574_, lean_object* v_newStart_575_, lean_object* v_newEnd_576_, lean_object* v_h_577_){
_start:
{
lean_object* v_str_578_; lean_object* v_startInclusive_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_588_; 
v_str_578_ = lean_ctor_get(v_s_574_, 0);
v_startInclusive_579_ = lean_ctor_get(v_s_574_, 1);
v_isSharedCheck_588_ = !lean_is_exclusive(v_s_574_);
if (v_isSharedCheck_588_ == 0)
{
lean_object* v_unused_589_; 
v_unused_589_ = lean_ctor_get(v_s_574_, 2);
lean_dec(v_unused_589_);
v___x_581_ = v_s_574_;
v_isShared_582_ = v_isSharedCheck_588_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_startInclusive_579_);
lean_inc(v_str_578_);
lean_dec(v_s_574_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_588_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_583_ = lean_nat_add(v_startInclusive_579_, v_newStart_575_);
v___x_584_ = lean_nat_add(v_startInclusive_579_, v_newEnd_576_);
lean_dec(v_startInclusive_579_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 2, v___x_584_);
lean_ctor_set(v___x_581_, 1, v___x_583_);
v___x_586_ = v___x_581_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_str_578_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_587_, 2, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___boxed(lean_object* v_s_590_, lean_object* v_newStart_591_, lean_object* v_newEnd_592_, lean_object* v_h_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_String_Slice_slice(v_s_590_, v_newStart_591_, v_newEnd_592_, v_h_593_);
lean_dec(v_newEnd_592_);
lean_dec(v_newStart_591_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg(lean_object* v_s_595_, lean_object* v_newStart_596_, lean_object* v_newEnd_597_){
_start:
{
lean_object* v_str_598_; lean_object* v_startInclusive_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_608_; 
v_str_598_ = lean_ctor_get(v_s_595_, 0);
v_startInclusive_599_ = lean_ctor_get(v_s_595_, 1);
v_isSharedCheck_608_ = !lean_is_exclusive(v_s_595_);
if (v_isSharedCheck_608_ == 0)
{
lean_object* v_unused_609_; 
v_unused_609_ = lean_ctor_get(v_s_595_, 2);
lean_dec(v_unused_609_);
v___x_601_ = v_s_595_;
v_isShared_602_ = v_isSharedCheck_608_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_startInclusive_599_);
lean_inc(v_str_598_);
lean_dec(v_s_595_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_608_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_603_ = lean_nat_add(v_startInclusive_599_, v_newStart_596_);
v___x_604_ = lean_nat_add(v_startInclusive_599_, v_newEnd_597_);
lean_dec(v_startInclusive_599_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 2, v___x_604_);
lean_ctor_set(v___x_601_, 1, v___x_603_);
v___x_606_ = v___x_601_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_str_598_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_607_, 2, v___x_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg___boxed(lean_object* v_s_610_, lean_object* v_newStart_611_, lean_object* v_newEnd_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_String_Slice_replaceStartEnd___redArg(v_s_610_, v_newStart_611_, v_newEnd_612_);
lean_dec(v_newEnd_612_);
lean_dec(v_newStart_611_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd(lean_object* v_s_614_, lean_object* v_newStart_615_, lean_object* v_newEnd_616_, lean_object* v_h_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_String_Slice_replaceStartEnd___redArg(v_s_614_, v_newStart_615_, v_newEnd_616_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___boxed(lean_object* v_s_619_, lean_object* v_newStart_620_, lean_object* v_newEnd_621_, lean_object* v_h_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_String_Slice_replaceStartEnd(v_s_619_, v_newStart_620_, v_newEnd_621_, v_h_622_);
lean_dec(v_newEnd_621_);
lean_dec(v_newStart_620_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f(lean_object* v_s_624_, lean_object* v_newStart_625_, lean_object* v_newEnd_626_){
_start:
{
uint8_t v___x_627_; 
v___x_627_ = lean_nat_dec_le(v_newStart_625_, v_newEnd_626_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; 
lean_dec_ref(v_s_624_);
v___x_628_ = lean_box(0);
return v___x_628_;
}
else
{
lean_object* v_str_629_; lean_object* v_startInclusive_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_640_; 
v_str_629_ = lean_ctor_get(v_s_624_, 0);
v_startInclusive_630_ = lean_ctor_get(v_s_624_, 1);
v_isSharedCheck_640_ = !lean_is_exclusive(v_s_624_);
if (v_isSharedCheck_640_ == 0)
{
lean_object* v_unused_641_; 
v_unused_641_ = lean_ctor_get(v_s_624_, 2);
lean_dec(v_unused_641_);
v___x_632_ = v_s_624_;
v_isShared_633_ = v_isSharedCheck_640_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_startInclusive_630_);
lean_inc(v_str_629_);
lean_dec(v_s_624_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_640_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_634_ = lean_nat_add(v_startInclusive_630_, v_newStart_625_);
v___x_635_ = lean_nat_add(v_startInclusive_630_, v_newEnd_626_);
lean_dec(v_startInclusive_630_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 2, v___x_635_);
lean_ctor_set(v___x_632_, 1, v___x_634_);
v___x_637_ = v___x_632_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_str_629_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_639_, 2, v___x_635_);
v___x_637_ = v_reuseFailAlloc_639_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_638_; 
v___x_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
return v___x_638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f___boxed(lean_object* v_s_642_, lean_object* v_newStart_643_, lean_object* v_newEnd_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_String_Slice_slice_x3f(v_s_642_, v_newStart_643_, v_newEnd_644_);
lean_dec(v_newEnd_644_);
lean_dec(v_newStart_643_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_slice_x21_spec__0(lean_object* v_msg_646_){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = l_String_instInhabitedSlice;
v___x_648_ = lean_panic_fn_borrowed(v___x_647_, v_msg_646_);
return v___x_648_;
}
}
static lean_object* _init_l_String_Slice_slice_x21___closed__2(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_651_ = ((lean_object*)(l_String_Slice_slice_x21___closed__1));
v___x_652_ = lean_unsigned_to_nat(4u);
v___x_653_ = lean_unsigned_to_nat(1096u);
v___x_654_ = ((lean_object*)(l_String_Slice_slice_x21___closed__0));
v___x_655_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_656_ = l_mkPanicMessageWithDecl(v___x_655_, v___x_654_, v___x_653_, v___x_652_, v___x_651_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x21(lean_object* v_s_657_, lean_object* v_newStart_658_, lean_object* v_newEnd_659_){
_start:
{
uint8_t v___x_660_; 
v___x_660_ = lean_nat_dec_le(v_newStart_658_, v_newEnd_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; 
lean_dec_ref(v_s_657_);
v___x_661_ = lean_obj_once(&l_String_Slice_slice_x21___closed__2, &l_String_Slice_slice_x21___closed__2_once, _init_l_String_Slice_slice_x21___closed__2);
v___x_662_ = l_panic___at___00String_Slice_slice_x21_spec__0(v___x_661_);
return v___x_662_;
}
else
{
lean_object* v_str_663_; lean_object* v_startInclusive_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_673_; 
v_str_663_ = lean_ctor_get(v_s_657_, 0);
v_startInclusive_664_ = lean_ctor_get(v_s_657_, 1);
v_isSharedCheck_673_ = !lean_is_exclusive(v_s_657_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; 
v_unused_674_ = lean_ctor_get(v_s_657_, 2);
lean_dec(v_unused_674_);
v___x_666_ = v_s_657_;
v_isShared_667_ = v_isSharedCheck_673_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_startInclusive_664_);
lean_inc(v_str_663_);
lean_dec(v_s_657_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_673_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_668_ = lean_nat_add(v_startInclusive_664_, v_newStart_658_);
v___x_669_ = lean_nat_add(v_startInclusive_664_, v_newEnd_659_);
lean_dec(v_startInclusive_664_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 2, v___x_669_);
lean_ctor_set(v___x_666_, 1, v___x_668_);
v___x_671_ = v___x_666_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_str_663_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v___x_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x21___boxed(lean_object* v_s_675_, lean_object* v_newStart_676_, lean_object* v_newEnd_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_String_Slice_slice_x21(v_s_675_, v_newStart_676_, v_newEnd_677_);
lean_dec(v_newEnd_677_);
lean_dec(v_newStart_676_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21(lean_object* v_s_679_, lean_object* v_newStart_680_, lean_object* v_newEnd_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_String_Slice_slice_x21(v_s_679_, v_newStart_680_, v_newEnd_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21___boxed(lean_object* v_s_683_, lean_object* v_newStart_684_, lean_object* v_newEnd_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_String_Slice_replaceStartEnd_x21(v_s_683_, v_newStart_684_, v_newEnd_685_);
lean_dec(v_newEnd_685_);
lean_dec(v_newStart_684_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_String_decodeChar___boxed(lean_object* v_s_690_, lean_object* v_byteIdx_691_, lean_object* v_h_692_){
_start:
{
uint32_t v_res_693_; lean_object* v_r_694_; 
v_res_693_ = lean_string_utf8_get_fast(v_s_690_, v_byteIdx_691_);
lean_dec(v_byteIdx_691_);
lean_dec_ref(v_s_690_);
v_r_694_ = lean_box_uint32(v_res_693_);
return v_r_694_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get___redArg(lean_object* v_s_695_, lean_object* v_pos_696_){
_start:
{
lean_object* v_str_697_; lean_object* v_startInclusive_698_; lean_object* v___x_699_; uint32_t v___x_700_; 
v_str_697_ = lean_ctor_get(v_s_695_, 0);
v_startInclusive_698_ = lean_ctor_get(v_s_695_, 1);
v___x_699_ = lean_nat_add(v_startInclusive_698_, v_pos_696_);
v___x_700_ = lean_string_utf8_get_fast(v_str_697_, v___x_699_);
lean_dec(v___x_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___redArg___boxed(lean_object* v_s_701_, lean_object* v_pos_702_){
_start:
{
uint32_t v_res_703_; lean_object* v_r_704_; 
v_res_703_ = l_String_Slice_Pos_get___redArg(v_s_701_, v_pos_702_);
lean_dec(v_pos_702_);
lean_dec_ref(v_s_701_);
v_r_704_ = lean_box_uint32(v_res_703_);
return v_r_704_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get(lean_object* v_s_705_, lean_object* v_pos_706_, lean_object* v_h_707_){
_start:
{
lean_object* v_str_708_; lean_object* v_startInclusive_709_; lean_object* v___x_710_; uint32_t v___x_711_; 
v_str_708_ = lean_ctor_get(v_s_705_, 0);
v_startInclusive_709_ = lean_ctor_get(v_s_705_, 1);
v___x_710_ = lean_nat_add(v_startInclusive_709_, v_pos_706_);
v___x_711_ = lean_string_utf8_get_fast(v_str_708_, v___x_710_);
lean_dec(v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___boxed(lean_object* v_s_712_, lean_object* v_pos_713_, lean_object* v_h_714_){
_start:
{
uint32_t v_res_715_; lean_object* v_r_716_; 
v_res_715_ = l_String_Slice_Pos_get(v_s_712_, v_pos_713_, v_h_714_);
lean_dec(v_pos_713_);
lean_dec_ref(v_s_712_);
v_r_716_ = lean_box_uint32(v_res_715_);
return v_r_716_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f(lean_object* v_s_717_, lean_object* v_pos_718_){
_start:
{
lean_object* v_str_719_; lean_object* v_startInclusive_720_; lean_object* v_endExclusive_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_str_719_ = lean_ctor_get(v_s_717_, 0);
v_startInclusive_720_ = lean_ctor_get(v_s_717_, 1);
v_endExclusive_721_ = lean_ctor_get(v_s_717_, 2);
v___x_722_ = lean_nat_sub(v_endExclusive_721_, v_startInclusive_720_);
v___x_723_ = lean_nat_dec_eq(v_pos_718_, v___x_722_);
lean_dec(v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; uint32_t v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_724_ = lean_nat_add(v_startInclusive_720_, v_pos_718_);
v___x_725_ = lean_string_utf8_get_fast(v_str_719_, v___x_724_);
lean_dec(v___x_724_);
v___x_726_ = lean_box_uint32(v___x_725_);
v___x_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
else
{
lean_object* v___x_728_; 
v___x_728_ = lean_box(0);
return v___x_728_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f___boxed(lean_object* v_s_729_, lean_object* v_pos_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_String_Slice_Pos_get_x3f(v_s_729_, v_pos_730_);
lean_dec(v_pos_730_);
lean_dec_ref(v_s_729_);
return v_res_731_;
}
}
static lean_object* _init_l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1(void){
_start:
{
uint32_t v___x_732_; lean_object* v___x_733_; 
v___x_732_ = 65;
v___x_733_ = lean_box_uint32(v___x_732_);
return v___x_733_;
}
}
LEAN_EXPORT uint32_t l_panic___at___00String_Slice_Pos_get_x21_spec__0(lean_object* v_msg_734_){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; uint32_t v___x_737_; 
v___x_735_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1;
v___x_736_ = lean_panic_fn_borrowed(v___x_735_, v_msg_734_);
v___x_737_ = lean_unbox_uint32(v___x_736_);
lean_dec(v___x_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed(lean_object* v_msg_738_){
_start:
{
uint32_t v_res_739_; lean_object* v_r_740_; 
v_res_739_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v_msg_738_);
v_r_740_ = lean_box_uint32(v_res_739_);
return v_r_740_;
}
}
static lean_object* _init_l_String_Slice_Pos_get_x21___closed__2(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_743_ = ((lean_object*)(l_String_Slice_Pos_get_x21___closed__1));
v___x_744_ = lean_unsigned_to_nat(29u);
v___x_745_ = lean_unsigned_to_nat(1181u);
v___x_746_ = ((lean_object*)(l_String_Slice_Pos_get_x21___closed__0));
v___x_747_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_748_ = l_mkPanicMessageWithDecl(v___x_747_, v___x_746_, v___x_745_, v___x_744_, v___x_743_);
return v___x_748_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get_x21(lean_object* v_s_749_, lean_object* v_pos_750_){
_start:
{
lean_object* v_str_751_; lean_object* v_startInclusive_752_; lean_object* v_endExclusive_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v_str_751_ = lean_ctor_get(v_s_749_, 0);
v_startInclusive_752_ = lean_ctor_get(v_s_749_, 1);
v_endExclusive_753_ = lean_ctor_get(v_s_749_, 2);
v___x_754_ = lean_nat_sub(v_endExclusive_753_, v_startInclusive_752_);
v___x_755_ = lean_nat_dec_eq(v_pos_750_, v___x_754_);
lean_dec(v___x_754_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; uint32_t v___x_757_; 
v___x_756_ = lean_nat_add(v_startInclusive_752_, v_pos_750_);
v___x_757_ = lean_string_utf8_get_fast(v_str_751_, v___x_756_);
lean_dec(v___x_756_);
return v___x_757_;
}
else
{
lean_object* v___x_758_; uint32_t v___x_759_; 
v___x_758_ = lean_obj_once(&l_String_Slice_Pos_get_x21___closed__2, &l_String_Slice_Pos_get_x21___closed__2_once, _init_l_String_Slice_Pos_get_x21___closed__2);
v___x_759_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v___x_758_);
return v___x_759_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x21___boxed(lean_object* v_s_760_, lean_object* v_pos_761_){
_start:
{
uint32_t v_res_762_; lean_object* v_r_763_; 
v_res_762_ = l_String_Slice_Pos_get_x21(v_s_760_, v_pos_761_);
lean_dec(v_pos_761_);
lean_dec_ref(v_s_760_);
v_r_763_ = lean_box_uint32(v_res_762_);
return v_r_763_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg(lean_object* v_pos_764_){
_start:
{
lean_inc(v_pos_764_);
return v_pos_764_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg___boxed(lean_object* v_pos_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_String_Pos_toSlice___redArg(v_pos_765_);
lean_dec(v_pos_765_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice(lean_object* v_s_767_, lean_object* v_pos_768_){
_start:
{
lean_inc(v_pos_768_);
return v_pos_768_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___boxed(lean_object* v_s_769_, lean_object* v_pos_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_String_Pos_toSlice(v_s_769_, v_pos_770_);
lean_dec(v_pos_770_);
lean_dec_ref(v_s_769_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg(lean_object* v_pos_772_){
_start:
{
lean_inc(v_pos_772_);
return v_pos_772_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg___boxed(lean_object* v_pos_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_String_Pos_ofToSlice___redArg(v_pos_773_);
lean_dec(v_pos_773_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice(lean_object* v_s_775_, lean_object* v_pos_776_){
_start:
{
lean_inc(v_pos_776_);
return v_pos_776_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___boxed(lean_object* v_s_777_, lean_object* v_pos_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_String_Pos_ofToSlice(v_s_777_, v_pos_778_);
lean_dec(v_pos_778_);
lean_dec_ref(v_s_777_);
return v_res_779_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get___redArg(lean_object* v_s_780_, lean_object* v_pos_781_){
_start:
{
uint32_t v___x_782_; 
v___x_782_ = lean_string_utf8_get_fast(v_s_780_, v_pos_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get___redArg___boxed(lean_object* v_s_783_, lean_object* v_pos_784_){
_start:
{
uint32_t v_res_785_; lean_object* v_r_786_; 
v_res_785_ = l_String_Pos_get___redArg(v_s_783_, v_pos_784_);
lean_dec(v_pos_784_);
lean_dec_ref(v_s_783_);
v_r_786_ = lean_box_uint32(v_res_785_);
return v_r_786_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get(lean_object* v_s_787_, lean_object* v_pos_788_, lean_object* v_h_789_){
_start:
{
uint32_t v___x_790_; 
v___x_790_ = lean_string_utf8_get_fast(v_s_787_, v_pos_788_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get___boxed(lean_object* v_s_791_, lean_object* v_pos_792_, lean_object* v_h_793_){
_start:
{
uint32_t v_res_794_; lean_object* v_r_795_; 
v_res_794_ = l_String_Pos_get(v_s_791_, v_pos_792_, v_h_793_);
lean_dec(v_pos_792_);
lean_dec_ref(v_s_791_);
v_r_795_ = lean_box_uint32(v_res_794_);
return v_r_795_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x3f(lean_object* v_s_796_, lean_object* v_pos_797_){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = lean_string_utf8_byte_size(v_s_796_);
v___x_800_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_800_, 0, v_s_796_);
lean_ctor_set(v___x_800_, 1, v___x_798_);
lean_ctor_set(v___x_800_, 2, v___x_799_);
v___x_801_ = l_String_Slice_Pos_get_x3f(v___x_800_, v_pos_797_);
lean_dec_ref_known(v___x_800_, 3);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x3f___boxed(lean_object* v_s_802_, lean_object* v_pos_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_String_Pos_get_x3f(v_s_802_, v_pos_803_);
lean_dec(v_pos_803_);
return v_res_804_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get_x21(lean_object* v_s_805_, lean_object* v_pos_806_){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; uint32_t v___x_810_; 
v___x_807_ = lean_unsigned_to_nat(0u);
v___x_808_ = lean_string_utf8_byte_size(v_s_805_);
v___x_809_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_809_, 0, v_s_805_);
lean_ctor_set(v___x_809_, 1, v___x_807_);
lean_ctor_set(v___x_809_, 2, v___x_808_);
v___x_810_ = l_String_Slice_Pos_get_x21(v___x_809_, v_pos_806_);
lean_dec_ref_known(v___x_809_, 3);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x21___boxed(lean_object* v_s_811_, lean_object* v_pos_812_){
_start:
{
uint32_t v_res_813_; lean_object* v_r_814_; 
v_res_813_ = l_String_Pos_get_x21(v_s_811_, v_pos_812_);
lean_dec(v_pos_812_);
v_r_814_ = lean_box_uint32(v_res_813_);
return v_r_814_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_byte___redArg(lean_object* v_s_815_, lean_object* v_pos_816_){
_start:
{
uint8_t v___x_817_; 
v___x_817_ = lean_string_get_byte_fast(v_s_815_, v_pos_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_byte___redArg___boxed(lean_object* v_s_818_, lean_object* v_pos_819_){
_start:
{
uint8_t v_res_820_; lean_object* v_r_821_; 
v_res_820_ = l_String_Pos_byte___redArg(v_s_818_, v_pos_819_);
lean_dec_ref(v_s_818_);
v_r_821_ = lean_box(v_res_820_);
return v_r_821_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_byte(lean_object* v_s_822_, lean_object* v_pos_823_, lean_object* v_h_824_){
_start:
{
uint8_t v___x_825_; 
v___x_825_ = lean_string_get_byte_fast(v_s_822_, v_pos_823_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_byte___boxed(lean_object* v_s_826_, lean_object* v_pos_827_, lean_object* v_h_828_){
_start:
{
uint8_t v_res_829_; lean_object* v_r_830_; 
v_res_829_ = l_String_Pos_byte(v_s_826_, v_pos_827_, v_h_828_);
lean_dec_ref(v_s_826_);
v_r_830_ = lean_box(v_res_829_);
return v_r_830_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg(lean_object* v_pos_831_){
_start:
{
lean_inc(v_pos_831_);
return v_pos_831_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg___boxed(lean_object* v_pos_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_String_Pos_ofCopy___redArg(v_pos_832_);
lean_dec(v_pos_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy(lean_object* v_s_834_, lean_object* v_pos_835_){
_start:
{
lean_inc(v_pos_835_);
return v_pos_835_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___boxed(lean_object* v_s_836_, lean_object* v_pos_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_String_Pos_ofCopy(v_s_836_, v_pos_837_);
lean_dec(v_pos_837_);
lean_dec_ref(v_s_836_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg(lean_object* v_pos_839_){
_start:
{
lean_inc(v_pos_839_);
return v_pos_839_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg___boxed(lean_object* v_pos_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_String_Slice_Pos_copy___redArg(v_pos_840_);
lean_dec(v_pos_840_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy(lean_object* v_s_842_, lean_object* v_pos_843_){
_start:
{
lean_inc(v_pos_843_);
return v_pos_843_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___boxed(lean_object* v_s_844_, lean_object* v_pos_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_String_Slice_Pos_copy(v_s_844_, v_pos_845_);
lean_dec(v_pos_845_);
lean_dec_ref(v_s_844_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg(lean_object* v_pos_847_){
_start:
{
lean_inc(v_pos_847_);
return v_pos_847_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg___boxed(lean_object* v_pos_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_String_Slice_Pos_toCopy___redArg(v_pos_848_);
lean_dec(v_pos_848_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy(lean_object* v_s_850_, lean_object* v_pos_851_){
_start:
{
lean_inc(v_pos_851_);
return v_pos_851_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___boxed(lean_object* v_s_852_, lean_object* v_pos_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_String_Slice_Pos_toCopy(v_s_852_, v_pos_853_);
lean_dec(v_pos_853_);
lean_dec_ref(v_s_852_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg(lean_object* v_p_u2080_855_, lean_object* v_pos_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = lean_nat_add(v_p_u2080_855_, v_pos_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg___boxed(lean_object* v_p_u2080_858_, lean_object* v_pos_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_String_Slice_Pos_ofSliceFrom___redArg(v_p_u2080_858_, v_pos_859_);
lean_dec(v_pos_859_);
lean_dec(v_p_u2080_858_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom(lean_object* v_s_861_, lean_object* v_p_u2080_862_, lean_object* v_pos_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = lean_nat_add(v_p_u2080_862_, v_pos_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___boxed(lean_object* v_s_865_, lean_object* v_p_u2080_866_, lean_object* v_pos_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_String_Slice_Pos_ofSliceFrom(v_s_865_, v_p_u2080_866_, v_pos_867_);
lean_dec(v_pos_867_);
lean_dec(v_p_u2080_866_);
lean_dec_ref(v_s_865_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg(lean_object* v_p_u2080_869_, lean_object* v_pos_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = lean_nat_add(v_p_u2080_869_, v_pos_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg___boxed(lean_object* v_p_u2080_872_, lean_object* v_pos_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_String_Slice_Pos_ofReplaceStart___redArg(v_p_u2080_872_, v_pos_873_);
lean_dec(v_pos_873_);
lean_dec(v_p_u2080_872_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart(lean_object* v_s_875_, lean_object* v_p_u2080_876_, lean_object* v_pos_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = lean_nat_add(v_p_u2080_876_, v_pos_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___boxed(lean_object* v_s_879_, lean_object* v_p_u2080_880_, lean_object* v_pos_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_String_Slice_Pos_ofReplaceStart(v_s_879_, v_p_u2080_880_, v_pos_881_);
lean_dec(v_pos_881_);
lean_dec(v_p_u2080_880_);
lean_dec_ref(v_s_879_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg(lean_object* v_p_u2080_883_, lean_object* v_pos_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = lean_nat_sub(v_pos_884_, v_p_u2080_883_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg___boxed(lean_object* v_p_u2080_886_, lean_object* v_pos_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_String_Slice_Pos_sliceFrom___redArg(v_p_u2080_886_, v_pos_887_);
lean_dec(v_pos_887_);
lean_dec(v_p_u2080_886_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom(lean_object* v_s_889_, lean_object* v_p_u2080_890_, lean_object* v_pos_891_, lean_object* v_h_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = lean_nat_sub(v_pos_891_, v_p_u2080_890_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___boxed(lean_object* v_s_894_, lean_object* v_p_u2080_895_, lean_object* v_pos_896_, lean_object* v_h_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_String_Slice_Pos_sliceFrom(v_s_894_, v_p_u2080_895_, v_pos_896_, v_h_897_);
lean_dec(v_pos_896_);
lean_dec(v_p_u2080_895_);
lean_dec_ref(v_s_894_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg(lean_object* v_p_u2080_899_, lean_object* v_pos_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = lean_nat_sub(v_pos_900_, v_p_u2080_899_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg___boxed(lean_object* v_p_u2080_902_, lean_object* v_pos_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_String_Slice_Pos_toReplaceStart___redArg(v_p_u2080_902_, v_pos_903_);
lean_dec(v_pos_903_);
lean_dec(v_p_u2080_902_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart(lean_object* v_s_905_, lean_object* v_p_u2080_906_, lean_object* v_pos_907_, lean_object* v_h_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = lean_nat_sub(v_pos_907_, v_p_u2080_906_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___boxed(lean_object* v_s_910_, lean_object* v_p_u2080_911_, lean_object* v_pos_912_, lean_object* v_h_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_String_Slice_Pos_toReplaceStart(v_s_910_, v_p_u2080_911_, v_pos_912_, v_h_913_);
lean_dec(v_pos_912_);
lean_dec(v_p_u2080_911_);
lean_dec_ref(v_s_910_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg(lean_object* v_pos_915_){
_start:
{
lean_inc(v_pos_915_);
return v_pos_915_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg___boxed(lean_object* v_pos_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_String_Slice_Pos_ofSliceTo___redArg(v_pos_916_);
lean_dec(v_pos_916_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo(lean_object* v_s_918_, lean_object* v_p_u2080_919_, lean_object* v_pos_920_){
_start:
{
lean_inc(v_pos_920_);
return v_pos_920_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___boxed(lean_object* v_s_921_, lean_object* v_p_u2080_922_, lean_object* v_pos_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_String_Slice_Pos_ofSliceTo(v_s_921_, v_p_u2080_922_, v_pos_923_);
lean_dec(v_pos_923_);
lean_dec(v_p_u2080_922_);
lean_dec_ref(v_s_921_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg(lean_object* v_pos_925_){
_start:
{
lean_inc(v_pos_925_);
return v_pos_925_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg___boxed(lean_object* v_pos_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_String_Slice_Pos_ofReplaceEnd___redArg(v_pos_926_);
lean_dec(v_pos_926_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd(lean_object* v_s_928_, lean_object* v_p_u2080_929_, lean_object* v_pos_930_){
_start:
{
lean_inc(v_pos_930_);
return v_pos_930_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___boxed(lean_object* v_s_931_, lean_object* v_p_u2080_932_, lean_object* v_pos_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_String_Slice_Pos_ofReplaceEnd(v_s_931_, v_p_u2080_932_, v_pos_933_);
lean_dec(v_pos_933_);
lean_dec(v_p_u2080_932_);
lean_dec_ref(v_s_931_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg(lean_object* v_pos_935_){
_start:
{
lean_inc(v_pos_935_);
return v_pos_935_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg___boxed(lean_object* v_pos_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_String_Slice_Pos_sliceTo___redArg(v_pos_936_);
lean_dec(v_pos_936_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo(lean_object* v_s_938_, lean_object* v_p_u2080_939_, lean_object* v_pos_940_, lean_object* v_h_941_){
_start:
{
lean_inc(v_pos_940_);
return v_pos_940_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___boxed(lean_object* v_s_942_, lean_object* v_p_u2080_943_, lean_object* v_pos_944_, lean_object* v_h_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_String_Slice_Pos_sliceTo(v_s_942_, v_p_u2080_943_, v_pos_944_, v_h_945_);
lean_dec(v_pos_944_);
lean_dec(v_p_u2080_943_);
lean_dec_ref(v_s_942_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg(lean_object* v_pos_947_){
_start:
{
lean_inc(v_pos_947_);
return v_pos_947_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg___boxed(lean_object* v_pos_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_String_Slice_Pos_toReplaceEnd___redArg(v_pos_948_);
lean_dec(v_pos_948_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd(lean_object* v_s_950_, lean_object* v_p_u2080_951_, lean_object* v_pos_952_, lean_object* v_h_953_){
_start:
{
lean_inc(v_pos_952_);
return v_pos_952_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___boxed(lean_object* v_s_954_, lean_object* v_p_u2080_955_, lean_object* v_pos_956_, lean_object* v_h_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_String_Slice_Pos_toReplaceEnd(v_s_954_, v_p_u2080_955_, v_pos_956_, v_h_957_);
lean_dec(v_pos_956_);
lean_dec(v_p_u2080_955_);
lean_dec_ref(v_s_954_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg(lean_object* v_s_959_, lean_object* v_pos_960_){
_start:
{
lean_object* v_str_961_; lean_object* v_startInclusive_962_; lean_object* v___x_963_; uint8_t v___x_964_; uint8_t v___x_965_; uint8_t v___x_966_; uint8_t v___x_967_; uint8_t v___x_968_; 
v_str_961_ = lean_ctor_get(v_s_959_, 0);
v_startInclusive_962_ = lean_ctor_get(v_s_959_, 1);
v___x_963_ = lean_nat_add(v_startInclusive_962_, v_pos_960_);
v___x_964_ = lean_string_get_byte_fast(v_str_961_, v___x_963_);
v___x_965_ = 128;
v___x_966_ = lean_uint8_land(v___x_964_, v___x_965_);
v___x_967_ = 0;
v___x_968_ = lean_uint8_dec_eq(v___x_966_, v___x_967_);
if (v___x_968_ == 0)
{
uint8_t v___x_969_; uint8_t v___x_970_; uint8_t v___x_971_; uint8_t v___x_972_; 
v___x_969_ = 224;
v___x_970_ = lean_uint8_land(v___x_964_, v___x_969_);
v___x_971_ = 192;
v___x_972_ = lean_uint8_dec_eq(v___x_970_, v___x_971_);
if (v___x_972_ == 0)
{
uint8_t v___x_973_; uint8_t v___x_974_; uint8_t v___x_975_; 
v___x_973_ = 240;
v___x_974_ = lean_uint8_land(v___x_964_, v___x_973_);
v___x_975_ = lean_uint8_dec_eq(v___x_974_, v___x_969_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = lean_unsigned_to_nat(4u);
v___x_977_ = lean_nat_add(v_pos_960_, v___x_976_);
return v___x_977_;
}
else
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = lean_unsigned_to_nat(3u);
v___x_979_ = lean_nat_add(v_pos_960_, v___x_978_);
return v___x_979_;
}
}
else
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = lean_unsigned_to_nat(2u);
v___x_981_ = lean_nat_add(v_pos_960_, v___x_980_);
return v___x_981_;
}
}
else
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_unsigned_to_nat(1u);
v___x_983_ = lean_nat_add(v_pos_960_, v___x_982_);
return v___x_983_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg___boxed(lean_object* v_s_984_, lean_object* v_pos_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_String_Slice_Pos_next___redArg(v_s_984_, v_pos_985_);
lean_dec(v_pos_985_);
lean_dec_ref(v_s_984_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next(lean_object* v_s_987_, lean_object* v_pos_988_, lean_object* v_h_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_String_Slice_Pos_next___redArg(v_s_987_, v_pos_988_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___boxed(lean_object* v_s_991_, lean_object* v_pos_992_, lean_object* v_h_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_String_Slice_Pos_next(v_s_991_, v_pos_992_, v_h_993_);
lean_dec(v_pos_992_);
lean_dec_ref(v_s_991_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f(lean_object* v_s_995_, lean_object* v_pos_996_){
_start:
{
lean_object* v_startInclusive_997_; lean_object* v_endExclusive_998_; lean_object* v___x_999_; uint8_t v___x_1000_; 
v_startInclusive_997_ = lean_ctor_get(v_s_995_, 1);
v_endExclusive_998_ = lean_ctor_get(v_s_995_, 2);
v___x_999_ = lean_nat_sub(v_endExclusive_998_, v_startInclusive_997_);
v___x_1000_ = lean_nat_dec_eq(v_pos_996_, v___x_999_);
lean_dec(v___x_999_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = l_String_Slice_Pos_next___redArg(v_s_995_, v_pos_996_);
v___x_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
return v___x_1002_;
}
else
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_box(0);
return v___x_1003_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f___boxed(lean_object* v_s_1004_, lean_object* v_pos_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_String_Slice_Pos_next_x3f(v_s_1004_, v_pos_1005_);
lean_dec(v_pos_1005_);
lean_dec_ref(v_s_1004_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(lean_object* v_msg_1007_){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = lean_unsigned_to_nat(0u);
v___x_1009_ = lean_panic_fn_borrowed(v___x_1008_, v_msg_1007_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0(lean_object* v_s_1010_, lean_object* v_msg_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v_msg_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___boxed(lean_object* v_s_1013_, lean_object* v_msg_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0(v_s_1013_, v_msg_1014_);
lean_dec_ref(v_s_1013_);
return v_res_1015_;
}
}
static lean_object* _init_l_String_Slice_Pos_next_x21___closed__2(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1018_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__1));
v___x_1019_ = lean_unsigned_to_nat(29u);
v___x_1020_ = lean_unsigned_to_nat(1573u);
v___x_1021_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__0));
v___x_1022_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1023_ = l_mkPanicMessageWithDecl(v___x_1022_, v___x_1021_, v___x_1020_, v___x_1019_, v___x_1018_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21(lean_object* v_s_1024_, lean_object* v_pos_1025_){
_start:
{
lean_object* v_startInclusive_1026_; lean_object* v_endExclusive_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
v_startInclusive_1026_ = lean_ctor_get(v_s_1024_, 1);
v_endExclusive_1027_ = lean_ctor_get(v_s_1024_, 2);
v___x_1028_ = lean_nat_sub(v_endExclusive_1027_, v_startInclusive_1026_);
v___x_1029_ = lean_nat_dec_eq(v_pos_1025_, v___x_1028_);
lean_dec(v___x_1028_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; 
v___x_1030_ = l_String_Slice_Pos_next___redArg(v_s_1024_, v_pos_1025_);
return v___x_1030_;
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = lean_obj_once(&l_String_Slice_Pos_next_x21___closed__2, &l_String_Slice_Pos_next_x21___closed__2_once, _init_l_String_Slice_Pos_next_x21___closed__2);
v___x_1032_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_1031_);
return v___x_1032_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21___boxed(lean_object* v_s_1033_, lean_object* v_pos_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_String_Slice_Pos_next_x21(v_s_1033_, v_pos_1034_);
lean_dec(v_pos_1034_);
lean_dec_ref(v_s_1033_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg(lean_object* v_s_1036_, lean_object* v_off_1037_){
_start:
{
lean_object* v_str_1038_; lean_object* v_startInclusive_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; uint8_t v___x_1042_; 
v_str_1038_ = lean_ctor_get(v_s_1036_, 0);
v_startInclusive_1039_ = lean_ctor_get(v_s_1036_, 1);
v___x_1040_ = lean_nat_add(v_startInclusive_1039_, v_off_1037_);
v___x_1041_ = lean_string_get_byte_fast(v_str_1038_, v___x_1040_);
v___x_1042_ = l_UInt8_instDecidableIsUTF8FirstByte___aux__1(v___x_1041_);
if (v___x_1042_ == 0)
{
lean_object* v_zero_1043_; uint8_t v_isZero_1044_; lean_object* v_one_1045_; lean_object* v_n_1046_; 
v_zero_1043_ = lean_unsigned_to_nat(0u);
v_isZero_1044_ = lean_nat_dec_eq(v_off_1037_, v_zero_1043_);
v_one_1045_ = lean_unsigned_to_nat(1u);
v_n_1046_ = lean_nat_sub(v_off_1037_, v_one_1045_);
lean_dec(v_off_1037_);
v_off_1037_ = v_n_1046_;
goto _start;
}
else
{
return v_off_1037_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg___boxed(lean_object* v_s_1048_, lean_object* v_off_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1048_, v_off_1049_);
lean_dec_ref(v_s_1048_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go(lean_object* v_s_1051_, lean_object* v_off_1052_, lean_object* v_h_u2081_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1051_, v_off_1052_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___boxed(lean_object* v_s_1055_, lean_object* v_off_1056_, lean_object* v_h_u2081_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_String_Slice_Pos_prevAux_go(v_s_1055_, v_off_1056_, v_h_u2081_1057_);
lean_dec_ref(v_s_1055_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg(lean_object* v_s_1059_, lean_object* v_pos_1060_){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1061_ = lean_unsigned_to_nat(1u);
v___x_1062_ = lean_nat_sub(v_pos_1060_, v___x_1061_);
v___x_1063_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1059_, v___x_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg___boxed(lean_object* v_s_1064_, lean_object* v_pos_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_String_Slice_Pos_prevAux___redArg(v_s_1064_, v_pos_1065_);
lean_dec(v_pos_1065_);
lean_dec_ref(v_s_1064_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux(lean_object* v_s_1067_, lean_object* v_pos_1068_, lean_object* v_h_1069_){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1070_ = lean_unsigned_to_nat(1u);
v___x_1071_ = lean_nat_sub(v_pos_1068_, v___x_1070_);
v___x_1072_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1067_, v___x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___boxed(lean_object* v_s_1073_, lean_object* v_pos_1074_, lean_object* v_h_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_String_Slice_Pos_prevAux(v_s_1073_, v_pos_1074_, v_h_1075_);
lean_dec(v_pos_1074_);
lean_dec_ref(v_s_1073_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(lean_object* v_off_1077_, lean_object* v_h__1_1078_, lean_object* v_h__2_1079_){
_start:
{
lean_object* v_zero_1080_; uint8_t v_isZero_1081_; 
v_zero_1080_ = lean_unsigned_to_nat(0u);
v_isZero_1081_ = lean_nat_dec_eq(v_off_1077_, v_zero_1080_);
if (v_isZero_1081_ == 1)
{
lean_object* v___x_1082_; 
lean_dec(v_h__2_1079_);
v___x_1082_ = lean_apply_3(v_h__1_1078_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1082_;
}
else
{
lean_object* v_one_1083_; lean_object* v_n_1084_; lean_object* v___x_1085_; 
lean_dec(v_h__1_1078_);
v_one_1083_ = lean_unsigned_to_nat(1u);
v_n_1084_ = lean_nat_sub(v_off_1077_, v_one_1083_);
v___x_1085_ = lean_apply_4(v_h__2_1079_, v_n_1084_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1085_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg___boxed(lean_object* v_off_1086_, lean_object* v_h__1_1087_, lean_object* v_h__2_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(v_off_1086_, v_h__1_1087_, v_h__2_1088_);
lean_dec(v_off_1086_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(lean_object* v_s_1090_, lean_object* v_motive_1091_, lean_object* v_off_1092_, lean_object* v_h_u2081_1093_, lean_object* v_hbyte_1094_, lean_object* v_this_1095_, lean_object* v_h__1_1096_, lean_object* v_h__2_1097_){
_start:
{
lean_object* v_zero_1098_; uint8_t v_isZero_1099_; 
v_zero_1098_ = lean_unsigned_to_nat(0u);
v_isZero_1099_ = lean_nat_dec_eq(v_off_1092_, v_zero_1098_);
if (v_isZero_1099_ == 1)
{
lean_object* v___x_1100_; 
lean_dec(v_h__2_1097_);
v___x_1100_ = lean_apply_3(v_h__1_1096_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1100_;
}
else
{
lean_object* v_one_1101_; lean_object* v_n_1102_; lean_object* v___x_1103_; 
lean_dec(v_h__1_1096_);
v_one_1101_ = lean_unsigned_to_nat(1u);
v_n_1102_ = lean_nat_sub(v_off_1092_, v_one_1101_);
v___x_1103_ = lean_apply_4(v_h__2_1097_, v_n_1102_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___boxed(lean_object* v_s_1104_, lean_object* v_motive_1105_, lean_object* v_off_1106_, lean_object* v_h_u2081_1107_, lean_object* v_hbyte_1108_, lean_object* v_this_1109_, lean_object* v_h__1_1110_, lean_object* v_h__2_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(v_s_1104_, v_motive_1105_, v_off_1106_, v_h_u2081_1107_, v_hbyte_1108_, v_this_1109_, v_h__1_1110_, v_h__2_1111_);
lean_dec(v_off_1106_);
lean_dec_ref(v_s_1104_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg(lean_object* v_off_1113_){
_start:
{
lean_inc(v_off_1113_);
return v_off_1113_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg___boxed(lean_object* v_off_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_String_Slice_pos___redArg(v_off_1114_);
lean_dec(v_off_1114_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos(lean_object* v_s_1116_, lean_object* v_off_1117_, lean_object* v_h_1118_){
_start:
{
lean_inc(v_off_1117_);
return v_off_1117_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___boxed(lean_object* v_s_1119_, lean_object* v_off_1120_, lean_object* v_h_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_String_Slice_pos(v_s_1119_, v_off_1120_, v_h_1121_);
lean_dec(v_off_1120_);
lean_dec_ref(v_s_1119_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f(lean_object* v_s_1123_, lean_object* v_off_1124_){
_start:
{
uint8_t v___x_1125_; 
v___x_1125_ = l_String_Pos_Raw_isValidForSlice(v_s_1123_, v_off_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; 
lean_dec(v_off_1124_);
v___x_1126_ = lean_box(0);
return v___x_1126_;
}
else
{
lean_object* v___x_1127_; 
v___x_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1127_, 0, v_off_1124_);
return v___x_1127_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f___boxed(lean_object* v_s_1128_, lean_object* v_off_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_String_Slice_pos_x3f(v_s_1128_, v_off_1129_);
lean_dec_ref(v_s_1128_);
return v_res_1130_;
}
}
static lean_object* _init_l_String_Slice_pos_x21___closed__2(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1133_ = ((lean_object*)(l_String_Slice_pos_x21___closed__1));
v___x_1134_ = lean_unsigned_to_nat(4u);
v___x_1135_ = lean_unsigned_to_nat(1661u);
v___x_1136_ = ((lean_object*)(l_String_Slice_pos_x21___closed__0));
v___x_1137_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1138_ = l_mkPanicMessageWithDecl(v___x_1137_, v___x_1136_, v___x_1135_, v___x_1134_, v___x_1133_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21(lean_object* v_s_1139_, lean_object* v_off_1140_){
_start:
{
uint8_t v___x_1141_; 
v___x_1141_ = l_String_Pos_Raw_isValidForSlice(v_s_1139_, v_off_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_obj_once(&l_String_Slice_pos_x21___closed__2, &l_String_Slice_pos_x21___closed__2_once, _init_l_String_Slice_pos_x21___closed__2);
v___x_1143_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_1142_);
return v___x_1143_;
}
else
{
lean_inc(v_off_1140_);
return v_off_1140_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21___boxed(lean_object* v_s_1144_, lean_object* v_off_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_String_Slice_pos_x21(v_s_1144_, v_off_1145_);
lean_dec(v_off_1145_);
lean_dec_ref(v_s_1144_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next___boxed(lean_object* v_s_1150_, lean_object* v_pos_1151_, lean_object* v_h_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = lean_string_utf8_next_fast(v_s_1150_, v_pos_1151_);
lean_dec(v_pos_1151_);
lean_dec_ref(v_s_1150_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x3f(lean_object* v_s_1154_, lean_object* v_pos_1155_){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1156_ = lean_unsigned_to_nat(0u);
v___x_1157_ = lean_string_utf8_byte_size(v_s_1154_);
v___x_1158_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1158_, 0, v_s_1154_);
lean_ctor_set(v___x_1158_, 1, v___x_1156_);
lean_ctor_set(v___x_1158_, 2, v___x_1157_);
v___x_1159_ = l_String_Slice_Pos_next_x3f(v___x_1158_, v_pos_1155_);
lean_dec_ref_known(v___x_1158_, 3);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_box(0);
return v___x_1160_;
}
else
{
lean_object* v_val_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
v_val_1161_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1159_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_val_1161_);
lean_dec(v___x_1159_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_val_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x3f___boxed(lean_object* v_s_1169_, lean_object* v_pos_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_String_Pos_next_x3f(v_s_1169_, v_pos_1170_);
lean_dec(v_pos_1170_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21(lean_object* v_s_1172_, lean_object* v_pos_1173_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1174_ = lean_unsigned_to_nat(0u);
v___x_1175_ = lean_string_utf8_byte_size(v_s_1172_);
v___x_1176_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1176_, 0, v_s_1172_);
lean_ctor_set(v___x_1176_, 1, v___x_1174_);
lean_ctor_set(v___x_1176_, 2, v___x_1175_);
v___x_1177_ = l_String_Slice_Pos_next_x21(v___x_1176_, v_pos_1173_);
lean_dec_ref_known(v___x_1176_, 3);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21___boxed(lean_object* v_s_1178_, lean_object* v_pos_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_String_Pos_next_x21(v_s_1178_, v_pos_1179_);
lean_dec(v_pos_1179_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg(lean_object* v_off_1181_){
_start:
{
lean_inc(v_off_1181_);
return v_off_1181_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg___boxed(lean_object* v_off_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_String_pos___redArg(v_off_1182_);
lean_dec(v_off_1182_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_String_pos(lean_object* v_s_1184_, lean_object* v_off_1185_, lean_object* v_h_1186_){
_start:
{
lean_inc(v_off_1185_);
return v_off_1185_;
}
}
LEAN_EXPORT lean_object* l_String_pos___boxed(lean_object* v_s_1187_, lean_object* v_off_1188_, lean_object* v_h_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_String_pos(v_s_1187_, v_off_1188_, v_h_1189_);
lean_dec(v_off_1188_);
lean_dec_ref(v_s_1187_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x3f(lean_object* v_s_1191_, lean_object* v_off_1192_){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1193_ = lean_unsigned_to_nat(0u);
v___x_1194_ = lean_string_utf8_byte_size(v_s_1191_);
v___x_1195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1195_, 0, v_s_1191_);
lean_ctor_set(v___x_1195_, 1, v___x_1193_);
lean_ctor_set(v___x_1195_, 2, v___x_1194_);
v___x_1196_ = l_String_Slice_pos_x3f(v___x_1195_, v_off_1192_);
lean_dec_ref_known(v___x_1195_, 3);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v___x_1197_; 
v___x_1197_ = lean_box(0);
return v___x_1197_;
}
else
{
lean_object* v_val_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
v_val_1198_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1196_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_val_1198_);
lean_dec(v___x_1196_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_val_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_pos_x21(lean_object* v_s_1206_, lean_object* v_off_1207_){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1208_ = lean_unsigned_to_nat(0u);
v___x_1209_ = lean_string_utf8_byte_size(v_s_1206_);
v___x_1210_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1210_, 0, v_s_1206_);
lean_ctor_set(v___x_1210_, 1, v___x_1208_);
lean_ctor_set(v___x_1210_, 2, v___x_1209_);
v___x_1211_ = l_String_Slice_pos_x21(v___x_1210_, v_off_1207_);
lean_dec_ref_known(v___x_1210_, 3);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x21___boxed(lean_object* v_s_1212_, lean_object* v_off_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_String_pos_x21(v_s_1212_, v_off_1213_);
lean_dec(v_off_1213_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg(lean_object* v_pos_1215_){
_start:
{
lean_inc(v_pos_1215_);
return v_pos_1215_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg___boxed(lean_object* v_pos_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_String_Slice_Pos_cast___redArg(v_pos_1216_);
lean_dec(v_pos_1216_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast(lean_object* v_s_1218_, lean_object* v_t_1219_, lean_object* v_pos_1220_, lean_object* v_h_1221_){
_start:
{
lean_inc(v_pos_1220_);
return v_pos_1220_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___boxed(lean_object* v_s_1222_, lean_object* v_t_1223_, lean_object* v_pos_1224_, lean_object* v_h_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_String_Slice_Pos_cast(v_s_1222_, v_t_1223_, v_pos_1224_, v_h_1225_);
lean_dec(v_pos_1224_);
lean_dec_ref(v_t_1223_);
lean_dec_ref(v_s_1222_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg(lean_object* v_pos_1227_){
_start:
{
lean_inc(v_pos_1227_);
return v_pos_1227_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg___boxed(lean_object* v_pos_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_String_Pos_cast___redArg(v_pos_1228_);
lean_dec(v_pos_1228_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast(lean_object* v_s_1230_, lean_object* v_t_1231_, lean_object* v_pos_1232_, lean_object* v_h_1233_){
_start:
{
lean_inc(v_pos_1232_);
return v_pos_1232_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___boxed(lean_object* v_s_1234_, lean_object* v_t_1235_, lean_object* v_pos_1236_, lean_object* v_h_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_String_Pos_cast(v_s_1234_, v_t_1235_, v_pos_1236_, v_h_1237_);
lean_dec(v_pos_1236_);
lean_dec_ref(v_t_1235_);
lean_dec_ref(v_s_1234_);
return v_res_1238_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_Raw_utf8GetAux(lean_object* v_x_1239_, lean_object* v_x_1240_, lean_object* v_x_1241_){
_start:
{
if (lean_obj_tag(v_x_1239_) == 0)
{
uint32_t v___x_1242_; 
lean_dec(v_x_1240_);
v___x_1242_ = 65;
return v___x_1242_;
}
else
{
lean_object* v_head_1243_; lean_object* v_tail_1244_; uint8_t v___x_1245_; 
v_head_1243_ = lean_ctor_get(v_x_1239_, 0);
v_tail_1244_ = lean_ctor_get(v_x_1239_, 1);
v___x_1245_ = lean_nat_dec_eq(v_x_1240_, v_x_1241_);
if (v___x_1245_ == 0)
{
uint32_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1246_ = lean_unbox_uint32(v_head_1243_);
v___x_1247_ = l_Char_utf8Size(v___x_1246_);
v___x_1248_ = lean_nat_add(v_x_1240_, v___x_1247_);
lean_dec(v___x_1247_);
lean_dec(v_x_1240_);
v_x_1239_ = v_tail_1244_;
v_x_1240_ = v___x_1248_;
goto _start;
}
else
{
uint32_t v___x_1250_; 
lean_dec(v_x_1240_);
v___x_1250_ = lean_unbox_uint32(v_head_1243_);
return v___x_1250_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux___boxed(lean_object* v_x_1251_, lean_object* v_x_1252_, lean_object* v_x_1253_){
_start:
{
uint32_t v_res_1254_; lean_object* v_r_1255_; 
v_res_1254_ = l_String_Pos_Raw_utf8GetAux(v_x_1251_, v_x_1252_, v_x_1253_);
lean_dec(v_x_1253_);
lean_dec(v_x_1251_);
v_r_1255_ = lean_box_uint32(v_res_1254_);
return v_r_1255_;
}
}
LEAN_EXPORT uint32_t l_String_utf8GetAux(lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_){
_start:
{
uint32_t v___x_1259_; 
v___x_1259_ = l_String_Pos_Raw_utf8GetAux(v_a_1256_, v_a_1257_, v_a_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux___boxed(lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
uint32_t v_res_1263_; lean_object* v_r_1264_; 
v_res_1263_ = l_String_utf8GetAux(v_a_1260_, v_a_1261_, v_a_1262_);
lean_dec(v_a_1262_);
lean_dec(v_a_1260_);
v_r_1264_ = lean_box_uint32(v_res_1263_);
return v_r_1264_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get___boxed(lean_object* v_s_1267_, lean_object* v_p_1268_){
_start:
{
uint32_t v_res_1269_; lean_object* v_r_1270_; 
v_res_1269_ = lean_string_utf8_get(v_s_1267_, v_p_1268_);
lean_dec(v_p_1268_);
lean_dec_ref(v_s_1267_);
v_r_1270_ = lean_box_uint32(v_res_1269_);
return v_r_1270_;
}
}
LEAN_EXPORT lean_object* l_String_get___boxed(lean_object* v_s_1273_, lean_object* v_p_1274_){
_start:
{
uint32_t v_res_1275_; lean_object* v_r_1276_; 
v_res_1275_ = lean_string_utf8_get(v_s_1273_, v_p_1274_);
lean_dec(v_p_1274_);
lean_dec_ref(v_s_1273_);
v_r_1276_ = lean_box_uint32(v_res_1275_);
return v_r_1276_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f(lean_object* v_x_1277_, lean_object* v_x_1278_, lean_object* v_x_1279_){
_start:
{
if (lean_obj_tag(v_x_1277_) == 0)
{
lean_object* v___x_1280_; 
lean_dec(v_x_1278_);
v___x_1280_ = lean_box(0);
return v___x_1280_;
}
else
{
lean_object* v_head_1281_; lean_object* v_tail_1282_; uint8_t v___x_1283_; 
v_head_1281_ = lean_ctor_get(v_x_1277_, 0);
v_tail_1282_ = lean_ctor_get(v_x_1277_, 1);
v___x_1283_ = lean_nat_dec_eq(v_x_1278_, v_x_1279_);
if (v___x_1283_ == 0)
{
uint32_t v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = lean_unbox_uint32(v_head_1281_);
v___x_1285_ = l_Char_utf8Size(v___x_1284_);
v___x_1286_ = lean_nat_add(v_x_1278_, v___x_1285_);
lean_dec(v___x_1285_);
lean_dec(v_x_1278_);
v_x_1277_ = v_tail_1282_;
v_x_1278_ = v___x_1286_;
goto _start;
}
else
{
lean_object* v___x_1288_; 
lean_dec(v_x_1278_);
lean_inc(v_head_1281_);
v___x_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1288_, 0, v_head_1281_);
return v___x_1288_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f___boxed(lean_object* v_x_1289_, lean_object* v_x_1290_, lean_object* v_x_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_String_Pos_Raw_utf8GetAux_x3f(v_x_1289_, v_x_1290_, v_x_1291_);
lean_dec(v_x_1291_);
lean_dec(v_x_1289_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f(lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_String_Pos_Raw_utf8GetAux_x3f(v_a_1293_, v_a_1294_, v_a_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f___boxed(lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_String_utf8GetAux_x3f(v_a_1297_, v_a_1298_, v_a_1299_);
lean_dec(v_a_1299_);
lean_dec(v_a_1297_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1303_, lean_object* v_a_00___x40___internal___hyg_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1303_, v_a_00___x40___internal___hyg_1304_);
lean_dec(v_a_00___x40___internal___hyg_1304_);
lean_dec_ref(v_a_00___x40___internal___hyg_1303_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_String_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1308_, lean_object* v_a_00___x40___internal___hyg_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1308_, v_a_00___x40___internal___hyg_1309_);
lean_dec(v_a_00___x40___internal___hyg_1309_);
lean_dec_ref(v_a_00___x40___internal___hyg_1308_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x21___boxed(lean_object* v_s_1313_, lean_object* v_p_1314_){
_start:
{
uint32_t v_res_1315_; lean_object* v_r_1316_; 
v_res_1315_ = lean_string_utf8_get_bang(v_s_1313_, v_p_1314_);
lean_dec(v_p_1314_);
lean_dec_ref(v_s_1313_);
v_r_1316_ = lean_box_uint32(v_res_1315_);
return v_r_1316_;
}
}
LEAN_EXPORT lean_object* l_String_get_x21___boxed(lean_object* v_s_1319_, lean_object* v_p_1320_){
_start:
{
uint32_t v_res_1321_; lean_object* v_r_1322_; 
v_res_1321_ = lean_string_utf8_get_bang(v_s_1319_, v_p_1320_);
lean_dec(v_p_1320_);
lean_dec_ref(v_s_1319_);
v_r_1322_ = lean_box_uint32(v_res_1321_);
return v_r_1322_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux(uint32_t v_c_x27_1323_, lean_object* v_x_1324_, lean_object* v_x_1325_, lean_object* v_x_1326_){
_start:
{
if (lean_obj_tag(v_x_1324_) == 0)
{
return v_x_1324_;
}
else
{
lean_object* v_head_1327_; lean_object* v_tail_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1344_; 
v_head_1327_ = lean_ctor_get(v_x_1324_, 0);
v_tail_1328_ = lean_ctor_get(v_x_1324_, 1);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_x_1324_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1330_ = v_x_1324_;
v_isShared_1331_ = v_isSharedCheck_1344_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_tail_1328_);
lean_inc(v_head_1327_);
lean_dec(v_x_1324_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1344_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
uint8_t v___x_1332_; 
v___x_1332_ = lean_nat_dec_eq(v_x_1325_, v_x_1326_);
if (v___x_1332_ == 0)
{
uint32_t v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1338_; 
v___x_1333_ = lean_unbox_uint32(v_head_1327_);
v___x_1334_ = l_Char_utf8Size(v___x_1333_);
v___x_1335_ = lean_nat_add(v_x_1325_, v___x_1334_);
lean_dec(v___x_1334_);
v___x_1336_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1323_, v_tail_1328_, v___x_1335_, v_x_1326_);
lean_dec(v___x_1335_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 1, v___x_1336_);
v___x_1338_ = v___x_1330_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_head_1327_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
else
{
lean_object* v___x_1340_; lean_object* v___x_1342_; 
lean_dec(v_head_1327_);
v___x_1340_ = lean_box_uint32(v_c_x27_1323_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v___x_1340_);
v___x_1342_ = v___x_1330_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_tail_1328_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux___boxed(lean_object* v_c_x27_1345_, lean_object* v_x_1346_, lean_object* v_x_1347_, lean_object* v_x_1348_){
_start:
{
uint32_t v_c_x27_boxed_1349_; lean_object* v_res_1350_; 
v_c_x27_boxed_1349_ = lean_unbox_uint32(v_c_x27_1345_);
lean_dec(v_c_x27_1345_);
v_res_1350_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_boxed_1349_, v_x_1346_, v_x_1347_, v_x_1348_);
lean_dec(v_x_1348_);
lean_dec(v_x_1347_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux(uint32_t v_c_x27_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux___boxed(lean_object* v_c_x27_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
uint32_t v_c_x27_boxed_1360_; lean_object* v_res_1361_; 
v_c_x27_boxed_1360_ = lean_unbox_uint32(v_c_x27_1356_);
lean_dec(v_c_x27_1356_);
v_res_1361_ = l_String_utf8SetAux(v_c_x27_boxed_1360_, v_a_1357_, v_a_1358_, v_a_1359_);
lean_dec(v_a_1359_);
lean_dec(v_a_1358_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg(lean_object* v_s_1362_, lean_object* v_pos_1363_){
_start:
{
lean_object* v_str_1364_; lean_object* v_startInclusive_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v_str_1364_ = lean_ctor_get(v_s_1362_, 0);
v_startInclusive_1365_ = lean_ctor_get(v_s_1362_, 1);
v___x_1366_ = lean_nat_add(v_startInclusive_1365_, v_pos_1363_);
v___x_1367_ = lean_string_utf8_next_fast(v_str_1364_, v___x_1366_);
lean_dec(v___x_1366_);
v___x_1368_ = lean_nat_sub(v___x_1367_, v_startInclusive_1365_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg___boxed(lean_object* v_s_1369_, lean_object* v_pos_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_String_Slice_Pos_nextFast___redArg(v_s_1369_, v_pos_1370_);
lean_dec(v_pos_1370_);
lean_dec_ref(v_s_1369_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast(lean_object* v_s_1372_, lean_object* v_pos_1373_, lean_object* v_h_1374_){
_start:
{
lean_object* v_str_1375_; lean_object* v_startInclusive_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v_str_1375_ = lean_ctor_get(v_s_1372_, 0);
v_startInclusive_1376_ = lean_ctor_get(v_s_1372_, 1);
v___x_1377_ = lean_nat_add(v_startInclusive_1376_, v_pos_1373_);
v___x_1378_ = lean_string_utf8_next_fast(v_str_1375_, v___x_1377_);
lean_dec(v___x_1377_);
v___x_1379_ = lean_nat_sub(v___x_1378_, v_startInclusive_1376_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___boxed(lean_object* v_s_1380_, lean_object* v_pos_1381_, lean_object* v_h_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_String_Slice_Pos_nextFast(v_s_1380_, v_pos_1381_, v_h_1382_);
lean_dec(v_pos_1381_);
lean_dec_ref(v_s_1380_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_String_sliceTo(lean_object* v_s_1384_, lean_object* v_p_1385_){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_unsigned_to_nat(0u);
v___x_1387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1387_, 0, v_s_1384_);
lean_ctor_set(v___x_1387_, 1, v___x_1386_);
lean_ctor_set(v___x_1387_, 2, v_p_1385_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_String_replaceEnd(lean_object* v_s_1388_, lean_object* v_p_1389_){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = lean_unsigned_to_nat(0u);
v___x_1391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1391_, 0, v_s_1388_);
lean_ctor_set(v___x_1391_, 1, v___x_1390_);
lean_ctor_set(v___x_1391_, 2, v_p_1389_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_String_sliceFrom(lean_object* v_s_1392_, lean_object* v_p_1393_){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = lean_string_utf8_byte_size(v_s_1392_);
v___x_1395_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1395_, 0, v_s_1392_);
lean_ctor_set(v___x_1395_, 1, v_p_1393_);
lean_ctor_set(v___x_1395_, 2, v___x_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStart(lean_object* v_s_1396_, lean_object* v_p_1397_){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = lean_string_utf8_byte_size(v_s_1396_);
v___x_1399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1399_, 0, v_s_1396_);
lean_ctor_set(v___x_1399_, 1, v_p_1397_);
lean_ctor_set(v___x_1399_, 2, v___x_1398_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_String_slice___redArg(lean_object* v_s_1400_, lean_object* v_startInclusive_1401_, lean_object* v_endExclusive_1402_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1403_, 0, v_s_1400_);
lean_ctor_set(v___x_1403_, 1, v_startInclusive_1401_);
lean_ctor_set(v___x_1403_, 2, v_endExclusive_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_String_slice(lean_object* v_s_1404_, lean_object* v_startInclusive_1405_, lean_object* v_endExclusive_1406_, lean_object* v_h_1407_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1408_, 0, v_s_1404_);
lean_ctor_set(v___x_1408_, 1, v_startInclusive_1405_);
lean_ctor_set(v___x_1408_, 2, v_endExclusive_1406_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x3f(lean_object* v_s_1409_, lean_object* v_startInclusive_1410_, lean_object* v_endExclusive_1411_){
_start:
{
uint8_t v___x_1412_; 
v___x_1412_ = lean_nat_dec_le(v_startInclusive_1410_, v_endExclusive_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; 
lean_dec(v_endExclusive_1411_);
lean_dec(v_startInclusive_1410_);
lean_dec_ref(v_s_1409_);
v___x_1413_ = lean_box(0);
return v___x_1413_;
}
else
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1414_, 0, v_s_1409_);
lean_ctor_set(v___x_1414_, 1, v_startInclusive_1410_);
lean_ctor_set(v___x_1414_, 2, v_endExclusive_1411_);
v___x_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
return v___x_1415_;
}
}
}
LEAN_EXPORT lean_object* l_String_slice_x21(lean_object* v_s_1416_, lean_object* v_p_u2081_1417_, lean_object* v_p_u2082_1418_){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1419_ = lean_unsigned_to_nat(0u);
v___x_1420_ = lean_string_utf8_byte_size(v_s_1416_);
v___x_1421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1421_, 0, v_s_1416_);
lean_ctor_set(v___x_1421_, 1, v___x_1419_);
lean_ctor_set(v___x_1421_, 2, v___x_1420_);
v___x_1422_ = l_String_Slice_slice_x21(v___x_1421_, v_p_u2081_1417_, v_p_u2082_1418_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x21___boxed(lean_object* v_s_1423_, lean_object* v_p_u2081_1424_, lean_object* v_p_u2082_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_String_slice_x21(v_s_1423_, v_p_u2081_1424_, v_p_u2082_1425_);
lean_dec(v_p_u2082_1425_);
lean_dec(v_p_u2081_1424_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21(lean_object* v_s_1427_, lean_object* v_p_u2081_1428_, lean_object* v_p_u2082_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_String_slice_x21(v_s_1427_, v_p_u2081_1428_, v_p_u2082_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21___boxed(lean_object* v_s_1431_, lean_object* v_p_u2081_1432_, lean_object* v_p_u2082_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_String_replaceStartEnd_x21(v_s_1431_, v_p_u2081_1432_, v_p_u2082_1433_);
lean_dec(v_p_u2082_1433_);
lean_dec(v_p_u2081_1432_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg(lean_object* v_p_u2080_1435_, lean_object* v_pos_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = lean_nat_add(v_p_u2080_1435_, v_pos_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg___boxed(lean_object* v_p_u2080_1438_, lean_object* v_pos_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_String_Pos_ofSliceFrom___redArg(v_p_u2080_1438_, v_pos_1439_);
lean_dec(v_pos_1439_);
lean_dec(v_p_u2080_1438_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom(lean_object* v_s_1441_, lean_object* v_p_u2080_1442_, lean_object* v_pos_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_nat_add(v_p_u2080_1442_, v_pos_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___boxed(lean_object* v_s_1445_, lean_object* v_p_u2080_1446_, lean_object* v_pos_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_String_Pos_ofSliceFrom(v_s_1445_, v_p_u2080_1446_, v_pos_1447_);
lean_dec(v_pos_1447_);
lean_dec(v_p_u2080_1446_);
lean_dec_ref(v_s_1445_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg(lean_object* v_p_u2080_1449_, lean_object* v_pos_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = lean_nat_add(v_p_u2080_1449_, v_pos_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg___boxed(lean_object* v_p_u2080_1452_, lean_object* v_pos_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_String_Pos_ofReplaceStart___redArg(v_p_u2080_1452_, v_pos_1453_);
lean_dec(v_pos_1453_);
lean_dec(v_p_u2080_1452_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart(lean_object* v_s_1455_, lean_object* v_p_u2080_1456_, lean_object* v_pos_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = lean_nat_add(v_p_u2080_1456_, v_pos_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___boxed(lean_object* v_s_1459_, lean_object* v_p_u2080_1460_, lean_object* v_pos_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_String_Pos_ofReplaceStart(v_s_1459_, v_p_u2080_1460_, v_pos_1461_);
lean_dec(v_pos_1461_);
lean_dec(v_p_u2080_1460_);
lean_dec_ref(v_s_1459_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg(lean_object* v_p_u2080_1463_, lean_object* v_pos_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = lean_nat_sub(v_pos_1464_, v_p_u2080_1463_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg___boxed(lean_object* v_p_u2080_1466_, lean_object* v_pos_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_String_Pos_sliceFrom___redArg(v_p_u2080_1466_, v_pos_1467_);
lean_dec(v_pos_1467_);
lean_dec(v_p_u2080_1466_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom(lean_object* v_s_1469_, lean_object* v_p_u2080_1470_, lean_object* v_pos_1471_, lean_object* v_h_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = lean_nat_sub(v_pos_1471_, v_p_u2080_1470_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___boxed(lean_object* v_s_1474_, lean_object* v_p_u2080_1475_, lean_object* v_pos_1476_, lean_object* v_h_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_String_Pos_sliceFrom(v_s_1474_, v_p_u2080_1475_, v_pos_1476_, v_h_1477_);
lean_dec(v_pos_1476_);
lean_dec(v_p_u2080_1475_);
lean_dec_ref(v_s_1474_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg(lean_object* v_p_u2080_1479_, lean_object* v_pos_1480_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = lean_nat_sub(v_pos_1480_, v_p_u2080_1479_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg___boxed(lean_object* v_p_u2080_1482_, lean_object* v_pos_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_String_Pos_toReplaceStart___redArg(v_p_u2080_1482_, v_pos_1483_);
lean_dec(v_pos_1483_);
lean_dec(v_p_u2080_1482_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart(lean_object* v_s_1485_, lean_object* v_p_u2080_1486_, lean_object* v_pos_1487_, lean_object* v_h_1488_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_nat_sub(v_pos_1487_, v_p_u2080_1486_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___boxed(lean_object* v_s_1490_, lean_object* v_p_u2080_1491_, lean_object* v_pos_1492_, lean_object* v_h_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_String_Pos_toReplaceStart(v_s_1490_, v_p_u2080_1491_, v_pos_1492_, v_h_1493_);
lean_dec(v_pos_1492_);
lean_dec(v_p_u2080_1491_);
lean_dec_ref(v_s_1490_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg(lean_object* v_pos_1495_){
_start:
{
lean_inc(v_pos_1495_);
return v_pos_1495_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg___boxed(lean_object* v_pos_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_String_Pos_ofSliceTo___redArg(v_pos_1496_);
lean_dec(v_pos_1496_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo(lean_object* v_s_1498_, lean_object* v_p_u2080_1499_, lean_object* v_pos_1500_){
_start:
{
lean_inc(v_pos_1500_);
return v_pos_1500_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___boxed(lean_object* v_s_1501_, lean_object* v_p_u2080_1502_, lean_object* v_pos_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_String_Pos_ofSliceTo(v_s_1501_, v_p_u2080_1502_, v_pos_1503_);
lean_dec(v_pos_1503_);
lean_dec(v_p_u2080_1502_);
lean_dec_ref(v_s_1501_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg(lean_object* v_pos_1505_){
_start:
{
lean_inc(v_pos_1505_);
return v_pos_1505_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg___boxed(lean_object* v_pos_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_String_Pos_ofReplaceEnd___redArg(v_pos_1506_);
lean_dec(v_pos_1506_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd(lean_object* v_s_1508_, lean_object* v_p_u2080_1509_, lean_object* v_pos_1510_){
_start:
{
lean_inc(v_pos_1510_);
return v_pos_1510_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___boxed(lean_object* v_s_1511_, lean_object* v_p_u2080_1512_, lean_object* v_pos_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_String_Pos_ofReplaceEnd(v_s_1511_, v_p_u2080_1512_, v_pos_1513_);
lean_dec(v_pos_1513_);
lean_dec(v_p_u2080_1512_);
lean_dec_ref(v_s_1511_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg(lean_object* v_pos_1515_){
_start:
{
lean_inc(v_pos_1515_);
return v_pos_1515_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg___boxed(lean_object* v_pos_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_String_Pos_sliceTo___redArg(v_pos_1516_);
lean_dec(v_pos_1516_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo(lean_object* v_s_1518_, lean_object* v_p_u2080_1519_, lean_object* v_pos_1520_, lean_object* v_h_1521_){
_start:
{
lean_inc(v_pos_1520_);
return v_pos_1520_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___boxed(lean_object* v_s_1522_, lean_object* v_p_u2080_1523_, lean_object* v_pos_1524_, lean_object* v_h_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_String_Pos_sliceTo(v_s_1522_, v_p_u2080_1523_, v_pos_1524_, v_h_1525_);
lean_dec(v_pos_1524_);
lean_dec(v_p_u2080_1523_);
lean_dec_ref(v_s_1522_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg(lean_object* v_pos_1527_){
_start:
{
lean_inc(v_pos_1527_);
return v_pos_1527_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg___boxed(lean_object* v_pos_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_String_Pos_toReplaceEnd___redArg(v_pos_1528_);
lean_dec(v_pos_1528_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd(lean_object* v_s_1530_, lean_object* v_p_u2080_1531_, lean_object* v_pos_1532_, lean_object* v_h_1533_){
_start:
{
lean_inc(v_pos_1532_);
return v_pos_1532_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___boxed(lean_object* v_s_1534_, lean_object* v_p_u2080_1535_, lean_object* v_pos_1536_, lean_object* v_h_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_String_Pos_toReplaceEnd(v_s_1534_, v_p_u2080_1535_, v_pos_1536_, v_h_1537_);
lean_dec(v_pos_1536_);
lean_dec(v_p_u2080_1535_);
lean_dec_ref(v_s_1534_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg(lean_object* v_p_u2080_1539_, lean_object* v_pos_1540_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = lean_nat_add(v_p_u2080_1539_, v_pos_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1542_, lean_object* v_pos_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_String_Slice_Pos_ofSlice___redArg(v_p_u2080_1542_, v_pos_1543_);
lean_dec(v_pos_1543_);
lean_dec(v_p_u2080_1542_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice(lean_object* v_s_1545_, lean_object* v_p_u2080_1546_, lean_object* v_p_u2081_1547_, lean_object* v_h_1548_, lean_object* v_pos_1549_){
_start:
{
lean_object* v___x_1550_; 
v___x_1550_ = lean_nat_add(v_p_u2080_1546_, v_pos_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___boxed(lean_object* v_s_1551_, lean_object* v_p_u2080_1552_, lean_object* v_p_u2081_1553_, lean_object* v_h_1554_, lean_object* v_pos_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_String_Slice_Pos_ofSlice(v_s_1551_, v_p_u2080_1552_, v_p_u2081_1553_, v_h_1554_, v_pos_1555_);
lean_dec(v_pos_1555_);
lean_dec(v_p_u2081_1553_);
lean_dec(v_p_u2080_1552_);
lean_dec_ref(v_s_1551_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg(lean_object* v_p_u2080_1557_, lean_object* v_pos_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_nat_add(v_p_u2080_1557_, v_pos_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1560_, lean_object* v_pos_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_String_Pos_ofSlice___redArg(v_p_u2080_1560_, v_pos_1561_);
lean_dec(v_pos_1561_);
lean_dec(v_p_u2080_1560_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice(lean_object* v_s_1563_, lean_object* v_p_u2080_1564_, lean_object* v_p_u2081_1565_, lean_object* v_h_1566_, lean_object* v_pos_1567_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_nat_add(v_p_u2080_1564_, v_pos_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___boxed(lean_object* v_s_1569_, lean_object* v_p_u2080_1570_, lean_object* v_p_u2081_1571_, lean_object* v_h_1572_, lean_object* v_pos_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_String_Pos_ofSlice(v_s_1569_, v_p_u2080_1570_, v_p_u2081_1571_, v_h_1572_, v_pos_1573_);
lean_dec(v_pos_1573_);
lean_dec(v_p_u2081_1571_);
lean_dec(v_p_u2080_1570_);
lean_dec_ref(v_s_1569_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg(lean_object* v_pos_1575_, lean_object* v_p_u2080_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = lean_nat_sub(v_pos_1575_, v_p_u2080_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg___boxed(lean_object* v_pos_1578_, lean_object* v_p_u2080_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_String_Slice_Pos_slice___redArg(v_pos_1578_, v_p_u2080_1579_);
lean_dec(v_p_u2080_1579_);
lean_dec(v_pos_1578_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice(lean_object* v_s_1581_, lean_object* v_pos_1582_, lean_object* v_p_u2080_1583_, lean_object* v_p_u2081_1584_, lean_object* v_h_u2081_1585_, lean_object* v_h_u2082_1586_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = lean_nat_sub(v_pos_1582_, v_p_u2080_1583_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___boxed(lean_object* v_s_1588_, lean_object* v_pos_1589_, lean_object* v_p_u2080_1590_, lean_object* v_p_u2081_1591_, lean_object* v_h_u2081_1592_, lean_object* v_h_u2082_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_String_Slice_Pos_slice(v_s_1588_, v_pos_1589_, v_p_u2080_1590_, v_p_u2081_1591_, v_h_u2081_1592_, v_h_u2082_1593_);
lean_dec(v_p_u2081_1591_);
lean_dec(v_p_u2080_1590_);
lean_dec(v_pos_1589_);
lean_dec_ref(v_s_1588_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg(lean_object* v_pos_1595_, lean_object* v_p_u2080_1596_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = lean_nat_sub(v_pos_1595_, v_p_u2080_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg___boxed(lean_object* v_pos_1598_, lean_object* v_p_u2080_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_String_Pos_slice___redArg(v_pos_1598_, v_p_u2080_1599_);
lean_dec(v_p_u2080_1599_);
lean_dec(v_pos_1598_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice(lean_object* v_s_1601_, lean_object* v_pos_1602_, lean_object* v_p_u2080_1603_, lean_object* v_p_u2081_1604_, lean_object* v_h_u2081_1605_, lean_object* v_h_u2082_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = lean_nat_sub(v_pos_1602_, v_p_u2080_1603_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___boxed(lean_object* v_s_1608_, lean_object* v_pos_1609_, lean_object* v_p_u2080_1610_, lean_object* v_p_u2081_1611_, lean_object* v_h_u2081_1612_, lean_object* v_h_u2082_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_String_Pos_slice(v_s_1608_, v_pos_1609_, v_p_u2080_1610_, v_p_u2081_1611_, v_h_u2081_1612_, v_h_u2082_1613_);
lean_dec(v_p_u2081_1611_);
lean_dec(v_p_u2080_1610_);
lean_dec(v_pos_1609_);
lean_dec_ref(v_s_1608_);
return v_res_1614_;
}
}
static lean_object* _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2(void){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1617_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__1));
v___x_1618_ = lean_unsigned_to_nat(4u);
v___x_1619_ = lean_unsigned_to_nat(2676u);
v___x_1620_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__0));
v___x_1621_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1622_ = l_mkPanicMessageWithDecl(v___x_1621_, v___x_1620_, v___x_1619_, v___x_1618_, v___x_1617_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg(lean_object* v_pos_1623_, lean_object* v_p_u2080_1624_, lean_object* v_p_u2081_1625_){
_start:
{
uint8_t v___x_1630_; 
v___x_1630_ = lean_nat_dec_le(v_p_u2080_1624_, v_pos_1623_);
if (v___x_1630_ == 0)
{
goto v___jp_1626_;
}
else
{
uint8_t v___x_1631_; 
v___x_1631_ = lean_nat_dec_le(v_pos_1623_, v_p_u2081_1625_);
if (v___x_1631_ == 0)
{
goto v___jp_1626_;
}
else
{
lean_object* v___x_1632_; 
v___x_1632_ = lean_nat_sub(v_pos_1623_, v_p_u2080_1624_);
return v___x_1632_;
}
}
v___jp_1626_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1627_ = lean_unsigned_to_nat(0u);
v___x_1628_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1629_ = l_panic___redArg(v___x_1627_, v___x_1628_);
return v___x_1629_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1633_, lean_object* v_p_u2080_1634_, lean_object* v_p_u2081_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_String_Slice_Pos_sliceOrPanic___redArg(v_pos_1633_, v_p_u2080_1634_, v_p_u2081_1635_);
lean_dec(v_p_u2081_1635_);
lean_dec(v_p_u2080_1634_);
lean_dec(v_pos_1633_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic(lean_object* v_s_1637_, lean_object* v_pos_1638_, lean_object* v_p_u2080_1639_, lean_object* v_p_u2081_1640_, lean_object* v_h_1641_){
_start:
{
uint8_t v___x_1646_; 
v___x_1646_ = lean_nat_dec_le(v_p_u2080_1639_, v_pos_1638_);
if (v___x_1646_ == 0)
{
goto v___jp_1642_;
}
else
{
uint8_t v___x_1647_; 
v___x_1647_ = lean_nat_dec_le(v_pos_1638_, v_p_u2081_1640_);
if (v___x_1647_ == 0)
{
goto v___jp_1642_;
}
else
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_nat_sub(v_pos_1638_, v_p_u2080_1639_);
return v___x_1648_;
}
}
v___jp_1642_:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1643_ = lean_unsigned_to_nat(0u);
v___x_1644_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1645_ = l_panic___redArg(v___x_1643_, v___x_1644_);
return v___x_1645_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___boxed(lean_object* v_s_1649_, lean_object* v_pos_1650_, lean_object* v_p_u2080_1651_, lean_object* v_p_u2081_1652_, lean_object* v_h_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_String_Slice_Pos_sliceOrPanic(v_s_1649_, v_pos_1650_, v_p_u2080_1651_, v_p_u2081_1652_, v_h_1653_);
lean_dec(v_p_u2081_1652_);
lean_dec(v_p_u2080_1651_);
lean_dec(v_pos_1650_);
lean_dec_ref(v_s_1649_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg(lean_object* v_pos_1655_, lean_object* v_p_u2080_1656_, lean_object* v_p_u2081_1657_){
_start:
{
uint8_t v___x_1662_; 
v___x_1662_ = lean_nat_dec_le(v_p_u2080_1656_, v_pos_1655_);
if (v___x_1662_ == 0)
{
goto v___jp_1658_;
}
else
{
uint8_t v___x_1663_; 
v___x_1663_ = lean_nat_dec_le(v_pos_1655_, v_p_u2081_1657_);
if (v___x_1663_ == 0)
{
goto v___jp_1658_;
}
else
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_nat_sub(v_pos_1655_, v_p_u2080_1656_);
return v___x_1664_;
}
}
v___jp_1658_:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = lean_unsigned_to_nat(0u);
v___x_1660_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1661_ = l_panic___redArg(v___x_1659_, v___x_1660_);
return v___x_1661_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1665_, lean_object* v_p_u2080_1666_, lean_object* v_p_u2081_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_String_Pos_sliceOrPanic___redArg(v_pos_1665_, v_p_u2080_1666_, v_p_u2081_1667_);
lean_dec(v_p_u2081_1667_);
lean_dec(v_p_u2080_1666_);
lean_dec(v_pos_1665_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic(lean_object* v_s_1669_, lean_object* v_pos_1670_, lean_object* v_p_u2080_1671_, lean_object* v_p_u2081_1672_, lean_object* v_h_1673_){
_start:
{
uint8_t v___x_1678_; 
v___x_1678_ = lean_nat_dec_le(v_p_u2080_1671_, v_pos_1670_);
if (v___x_1678_ == 0)
{
goto v___jp_1674_;
}
else
{
uint8_t v___x_1679_; 
v___x_1679_ = lean_nat_dec_le(v_pos_1670_, v_p_u2081_1672_);
if (v___x_1679_ == 0)
{
goto v___jp_1674_;
}
else
{
lean_object* v___x_1680_; 
v___x_1680_ = lean_nat_sub(v_pos_1670_, v_p_u2080_1671_);
return v___x_1680_;
}
}
v___jp_1674_:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1675_ = lean_unsigned_to_nat(0u);
v___x_1676_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1677_ = l_panic___redArg(v___x_1675_, v___x_1676_);
return v___x_1677_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___boxed(lean_object* v_s_1681_, lean_object* v_pos_1682_, lean_object* v_p_u2080_1683_, lean_object* v_p_u2081_1684_, lean_object* v_h_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_String_Pos_sliceOrPanic(v_s_1681_, v_pos_1682_, v_p_u2080_1683_, v_p_u2081_1684_, v_h_1685_);
lean_dec(v_p_u2081_1684_);
lean_dec(v_p_u2080_1683_);
lean_dec(v_pos_1682_);
lean_dec_ref(v_s_1681_);
return v_res_1686_;
}
}
static lean_object* _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1688_ = ((lean_object*)(l_String_Slice_slice_x21___closed__1));
v___x_1689_ = lean_unsigned_to_nat(4u);
v___x_1690_ = lean_unsigned_to_nat(2700u);
v___x_1691_ = ((lean_object*)(l_String_Slice_Pos_ofSlice_x21___redArg___closed__0));
v___x_1692_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1693_ = l_mkPanicMessageWithDecl(v___x_1692_, v___x_1691_, v___x_1690_, v___x_1689_, v___x_1688_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1694_, lean_object* v_p_u2081_1695_, lean_object* v_pos_1696_){
_start:
{
uint8_t v___x_1697_; 
v___x_1697_ = lean_nat_dec_le(v_p_u2080_1694_, v_p_u2081_1695_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1698_ = lean_unsigned_to_nat(0u);
v___x_1699_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1700_ = l_panic___redArg(v___x_1698_, v___x_1699_);
return v___x_1700_;
}
else
{
lean_object* v___x_1701_; 
v___x_1701_ = lean_nat_add(v_p_u2080_1694_, v_pos_1696_);
return v___x_1701_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1702_, lean_object* v_p_u2081_1703_, lean_object* v_pos_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_String_Slice_Pos_ofSlice_x21___redArg(v_p_u2080_1702_, v_p_u2081_1703_, v_pos_1704_);
lean_dec(v_pos_1704_);
lean_dec(v_p_u2081_1703_);
lean_dec(v_p_u2080_1702_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21(lean_object* v_s_1706_, lean_object* v_p_u2080_1707_, lean_object* v_p_u2081_1708_, lean_object* v_pos_1709_){
_start:
{
uint8_t v___x_1710_; 
v___x_1710_ = lean_nat_dec_le(v_p_u2080_1707_, v_p_u2081_1708_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1711_ = lean_unsigned_to_nat(0u);
v___x_1712_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1713_ = l_panic___redArg(v___x_1711_, v___x_1712_);
return v___x_1713_;
}
else
{
lean_object* v___x_1714_; 
v___x_1714_ = lean_nat_add(v_p_u2080_1707_, v_pos_1709_);
return v___x_1714_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___boxed(lean_object* v_s_1715_, lean_object* v_p_u2080_1716_, lean_object* v_p_u2081_1717_, lean_object* v_pos_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_String_Slice_Pos_ofSlice_x21(v_s_1715_, v_p_u2080_1716_, v_p_u2081_1717_, v_pos_1718_);
lean_dec(v_pos_1718_);
lean_dec(v_p_u2081_1717_);
lean_dec(v_p_u2080_1716_);
lean_dec_ref(v_s_1715_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1720_, lean_object* v_p_u2081_1721_, lean_object* v_pos_1722_){
_start:
{
uint8_t v___x_1723_; 
v___x_1723_ = lean_nat_dec_le(v_p_u2080_1720_, v_p_u2081_1721_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1724_ = lean_unsigned_to_nat(0u);
v___x_1725_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1726_ = l_panic___redArg(v___x_1724_, v___x_1725_);
return v___x_1726_;
}
else
{
lean_object* v___x_1727_; 
v___x_1727_ = lean_nat_add(v_p_u2080_1720_, v_pos_1722_);
return v___x_1727_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1728_, lean_object* v_p_u2081_1729_, lean_object* v_pos_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_String_Pos_ofSlice_x21___redArg(v_p_u2080_1728_, v_p_u2081_1729_, v_pos_1730_);
lean_dec(v_pos_1730_);
lean_dec(v_p_u2081_1729_);
lean_dec(v_p_u2080_1728_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21(lean_object* v_s_1732_, lean_object* v_p_u2080_1733_, lean_object* v_p_u2081_1734_, lean_object* v_pos_1735_){
_start:
{
uint8_t v___x_1736_; 
v___x_1736_ = lean_nat_dec_le(v_p_u2080_1733_, v_p_u2081_1734_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1737_ = lean_unsigned_to_nat(0u);
v___x_1738_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1739_ = l_panic___redArg(v___x_1737_, v___x_1738_);
return v___x_1739_;
}
else
{
lean_object* v___x_1740_; 
v___x_1740_ = lean_nat_add(v_p_u2080_1733_, v_pos_1735_);
return v___x_1740_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___boxed(lean_object* v_s_1741_, lean_object* v_p_u2080_1742_, lean_object* v_p_u2081_1743_, lean_object* v_pos_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_String_Pos_ofSlice_x21(v_s_1741_, v_p_u2080_1742_, v_p_u2081_1743_, v_pos_1744_);
lean_dec(v_pos_1744_);
lean_dec(v_p_u2081_1743_);
lean_dec(v_p_u2080_1742_);
lean_dec_ref(v_s_1741_);
return v_res_1745_;
}
}
static lean_object* _init_l_String_Slice_Pos_slice_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1748_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__1));
v___x_1749_ = lean_unsigned_to_nat(4u);
v___x_1750_ = lean_unsigned_to_nat(2718u);
v___x_1751_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__0));
v___x_1752_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1753_ = l_mkPanicMessageWithDecl(v___x_1752_, v___x_1751_, v___x_1750_, v___x_1749_, v___x_1748_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg(lean_object* v_pos_1754_, lean_object* v_p_u2080_1755_, lean_object* v_p_u2081_1756_){
_start:
{
uint8_t v___x_1761_; 
v___x_1761_ = lean_nat_dec_le(v_p_u2080_1755_, v_pos_1754_);
if (v___x_1761_ == 0)
{
goto v___jp_1757_;
}
else
{
uint8_t v___x_1762_; 
v___x_1762_ = lean_nat_dec_le(v_pos_1754_, v_p_u2081_1756_);
if (v___x_1762_ == 0)
{
goto v___jp_1757_;
}
else
{
lean_object* v___x_1763_; 
v___x_1763_ = lean_nat_sub(v_pos_1754_, v_p_u2080_1755_);
return v___x_1763_;
}
}
v___jp_1757_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1758_ = lean_unsigned_to_nat(0u);
v___x_1759_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1760_ = l_panic___redArg(v___x_1758_, v___x_1759_);
return v___x_1760_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1764_, lean_object* v_p_u2080_1765_, lean_object* v_p_u2081_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_String_Slice_Pos_slice_x21___redArg(v_pos_1764_, v_p_u2080_1765_, v_p_u2081_1766_);
lean_dec(v_p_u2081_1766_);
lean_dec(v_p_u2080_1765_);
lean_dec(v_pos_1764_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21(lean_object* v_s_1768_, lean_object* v_pos_1769_, lean_object* v_p_u2080_1770_, lean_object* v_p_u2081_1771_){
_start:
{
uint8_t v___x_1776_; 
v___x_1776_ = lean_nat_dec_le(v_p_u2080_1770_, v_pos_1769_);
if (v___x_1776_ == 0)
{
goto v___jp_1772_;
}
else
{
uint8_t v___x_1777_; 
v___x_1777_ = lean_nat_dec_le(v_pos_1769_, v_p_u2081_1771_);
if (v___x_1777_ == 0)
{
goto v___jp_1772_;
}
else
{
lean_object* v___x_1778_; 
v___x_1778_ = lean_nat_sub(v_pos_1769_, v_p_u2080_1770_);
return v___x_1778_;
}
}
v___jp_1772_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = lean_unsigned_to_nat(0u);
v___x_1774_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1775_ = l_panic___redArg(v___x_1773_, v___x_1774_);
return v___x_1775_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___boxed(lean_object* v_s_1779_, lean_object* v_pos_1780_, lean_object* v_p_u2080_1781_, lean_object* v_p_u2081_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_String_Slice_Pos_slice_x21(v_s_1779_, v_pos_1780_, v_p_u2080_1781_, v_p_u2081_1782_);
lean_dec(v_p_u2081_1782_);
lean_dec(v_p_u2080_1781_);
lean_dec(v_pos_1780_);
lean_dec_ref(v_s_1779_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg(lean_object* v_pos_1784_, lean_object* v_p_u2080_1785_, lean_object* v_p_u2081_1786_){
_start:
{
uint8_t v___x_1791_; 
v___x_1791_ = lean_nat_dec_le(v_p_u2080_1785_, v_pos_1784_);
if (v___x_1791_ == 0)
{
goto v___jp_1787_;
}
else
{
uint8_t v___x_1792_; 
v___x_1792_ = lean_nat_dec_le(v_pos_1784_, v_p_u2081_1786_);
if (v___x_1792_ == 0)
{
goto v___jp_1787_;
}
else
{
lean_object* v___x_1793_; 
v___x_1793_ = lean_nat_sub(v_pos_1784_, v_p_u2080_1785_);
return v___x_1793_;
}
}
v___jp_1787_:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1788_ = lean_unsigned_to_nat(0u);
v___x_1789_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1790_ = l_panic___redArg(v___x_1788_, v___x_1789_);
return v___x_1790_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1794_, lean_object* v_p_u2080_1795_, lean_object* v_p_u2081_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_String_Pos_slice_x21___redArg(v_pos_1794_, v_p_u2080_1795_, v_p_u2081_1796_);
lean_dec(v_p_u2081_1796_);
lean_dec(v_p_u2080_1795_);
lean_dec(v_pos_1794_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21(lean_object* v_s_1798_, lean_object* v_pos_1799_, lean_object* v_p_u2080_1800_, lean_object* v_p_u2081_1801_){
_start:
{
uint8_t v___x_1806_; 
v___x_1806_ = lean_nat_dec_le(v_p_u2080_1800_, v_pos_1799_);
if (v___x_1806_ == 0)
{
goto v___jp_1802_;
}
else
{
uint8_t v___x_1807_; 
v___x_1807_ = lean_nat_dec_le(v_pos_1799_, v_p_u2081_1801_);
if (v___x_1807_ == 0)
{
goto v___jp_1802_;
}
else
{
lean_object* v___x_1808_; 
v___x_1808_ = lean_nat_sub(v_pos_1799_, v_p_u2080_1800_);
return v___x_1808_;
}
}
v___jp_1802_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1803_ = lean_unsigned_to_nat(0u);
v___x_1804_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1805_ = l_panic___redArg(v___x_1803_, v___x_1804_);
return v___x_1805_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___boxed(lean_object* v_s_1809_, lean_object* v_pos_1810_, lean_object* v_p_u2080_1811_, lean_object* v_p_u2081_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_String_Pos_slice_x21(v_s_1809_, v_pos_1810_, v_p_u2080_1811_, v_p_u2081_1812_);
lean_dec(v_p_u2081_1812_);
lean_dec(v_p_u2080_1811_);
lean_dec(v_pos_1810_);
lean_dec_ref(v_s_1809_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract(lean_object* v_s_1814_, lean_object* v_p_u2080_1815_, lean_object* v_p_u2081_1816_){
_start:
{
lean_object* v_str_1817_; lean_object* v_startInclusive_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v_str_1817_ = lean_ctor_get(v_s_1814_, 0);
v_startInclusive_1818_ = lean_ctor_get(v_s_1814_, 1);
v___x_1819_ = lean_nat_add(v_startInclusive_1818_, v_p_u2080_1815_);
v___x_1820_ = lean_nat_add(v_startInclusive_1818_, v_p_u2081_1816_);
v___x_1821_ = lean_string_utf8_extract(v_str_1817_, v___x_1819_, v___x_1820_);
lean_dec(v___x_1820_);
lean_dec(v___x_1819_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract___boxed(lean_object* v_s_1822_, lean_object* v_p_u2080_1823_, lean_object* v_p_u2081_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_String_Slice_extract(v_s_1822_, v_p_u2080_1823_, v_p_u2081_1824_);
lean_dec(v_p_u2081_1824_);
lean_dec(v_p_u2080_1823_);
lean_dec_ref(v_s_1822_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn(lean_object* v_s_1826_, lean_object* v_p_1827_, lean_object* v_n_1828_){
_start:
{
lean_object* v_str_1829_; lean_object* v_startInclusive_1830_; lean_object* v_endExclusive_1831_; lean_object* v_zero_1832_; uint8_t v_isZero_1833_; 
v_str_1829_ = lean_ctor_get(v_s_1826_, 0);
v_startInclusive_1830_ = lean_ctor_get(v_s_1826_, 1);
v_endExclusive_1831_ = lean_ctor_get(v_s_1826_, 2);
v_zero_1832_ = lean_unsigned_to_nat(0u);
v_isZero_1833_ = lean_nat_dec_eq(v_n_1828_, v_zero_1832_);
if (v_isZero_1833_ == 1)
{
lean_dec(v_n_1828_);
return v_p_1827_;
}
else
{
lean_object* v___x_1834_; uint8_t v___x_1835_; lean_object* v_one_1836_; lean_object* v_n_1837_; 
v___x_1834_ = lean_nat_sub(v_endExclusive_1831_, v_startInclusive_1830_);
v___x_1835_ = lean_nat_dec_eq(v_p_1827_, v___x_1834_);
lean_dec(v___x_1834_);
v_one_1836_ = lean_unsigned_to_nat(1u);
v_n_1837_ = lean_nat_sub(v_n_1828_, v_one_1836_);
lean_dec(v_n_1828_);
if (v___x_1835_ == 0)
{
goto v___jp_1838_;
}
else
{
if (v_isZero_1833_ == 0)
{
lean_dec(v_n_1837_);
return v_p_1827_;
}
else
{
goto v___jp_1838_;
}
}
v___jp_1838_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1839_ = lean_nat_add(v_startInclusive_1830_, v_p_1827_);
lean_dec(v_p_1827_);
v___x_1840_ = lean_string_utf8_next_fast(v_str_1829_, v___x_1839_);
lean_dec(v___x_1839_);
v___x_1841_ = lean_nat_sub(v___x_1840_, v_startInclusive_1830_);
v_p_1827_ = v___x_1841_;
v_n_1828_ = v_n_1837_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn___boxed(lean_object* v_s_1843_, lean_object* v_p_1844_, lean_object* v_n_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_String_Slice_Pos_nextn(v_s_1843_, v_p_1844_, v_n_1845_);
lean_dec_ref(v_s_1843_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_nextn(lean_object* v_s_1847_, lean_object* v_p_1848_, lean_object* v_n_1849_){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1850_ = lean_unsigned_to_nat(0u);
v___x_1851_ = lean_string_utf8_byte_size(v_s_1847_);
v___x_1852_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1852_, 0, v_s_1847_);
lean_ctor_set(v___x_1852_, 1, v___x_1850_);
lean_ctor_set(v___x_1852_, 2, v___x_1851_);
v___x_1853_ = l_String_Slice_Pos_nextn(v___x_1852_, v_p_1848_, v_n_1849_);
lean_dec_ref_known(v___x_1852_, 3);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(lean_object* v_n_1854_, lean_object* v_h__1_1855_, lean_object* v_h__2_1856_){
_start:
{
lean_object* v_zero_1857_; uint8_t v_isZero_1858_; 
v_zero_1857_ = lean_unsigned_to_nat(0u);
v_isZero_1858_ = lean_nat_dec_eq(v_n_1854_, v_zero_1857_);
if (v_isZero_1858_ == 1)
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
lean_dec(v_h__2_1856_);
v___x_1859_ = lean_box(0);
v___x_1860_ = lean_apply_1(v_h__1_1855_, v___x_1859_);
return v___x_1860_;
}
else
{
lean_object* v_one_1861_; lean_object* v_n_1862_; lean_object* v___x_1863_; 
lean_dec(v_h__1_1855_);
v_one_1861_ = lean_unsigned_to_nat(1u);
v_n_1862_ = lean_nat_sub(v_n_1854_, v_one_1861_);
v___x_1863_ = lean_apply_1(v_h__2_1856_, v_n_1862_);
return v___x_1863_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg___boxed(lean_object* v_n_1864_, lean_object* v_h__1_1865_, lean_object* v_h__2_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(v_n_1864_, v_h__1_1865_, v_h__2_1866_);
lean_dec(v_n_1864_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(lean_object* v_motive_1868_, lean_object* v_n_1869_, lean_object* v_h__1_1870_, lean_object* v_h__2_1871_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___boxed(lean_object* v_motive_1879_, lean_object* v_n_1880_, lean_object* v_h__1_1881_, lean_object* v_h__2_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(v_motive_1879_, v_n_1880_, v_h__1_1881_, v_h__2_1882_);
lean_dec(v_n_1880_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next___boxed(lean_object* v_s_1886_, lean_object* v_p_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = lean_string_utf8_next(v_s_1886_, v_p_1887_);
lean_dec(v_p_1887_);
lean_dec_ref(v_s_1886_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_String_next___boxed(lean_object* v_s_1891_, lean_object* v_p_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = lean_string_utf8_next(v_s_1891_, v_p_1892_);
lean_dec(v_p_1892_);
lean_dec_ref(v_s_1891_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux(lean_object* v_x_1894_, lean_object* v_x_1895_, lean_object* v_x_1896_){
_start:
{
if (lean_obj_tag(v_x_1894_) == 0)
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
lean_dec(v_x_1895_);
v___x_1897_ = lean_unsigned_to_nat(1u);
v___x_1898_ = lean_nat_sub(v_x_1896_, v___x_1897_);
return v___x_1898_;
}
else
{
lean_object* v_head_1899_; lean_object* v_tail_1900_; uint32_t v___x_1901_; lean_object* v___x_1902_; lean_object* v_i_x27_1903_; uint8_t v___x_1904_; 
v_head_1899_ = lean_ctor_get(v_x_1894_, 0);
v_tail_1900_ = lean_ctor_get(v_x_1894_, 1);
v___x_1901_ = lean_unbox_uint32(v_head_1899_);
v___x_1902_ = l_Char_utf8Size(v___x_1901_);
v_i_x27_1903_ = lean_nat_add(v_x_1895_, v___x_1902_);
lean_dec(v___x_1902_);
v___x_1904_ = lean_nat_dec_le(v_x_1896_, v_i_x27_1903_);
if (v___x_1904_ == 0)
{
lean_dec(v_x_1895_);
v_x_1894_ = v_tail_1900_;
v_x_1895_ = v_i_x27_1903_;
goto _start;
}
else
{
lean_dec(v_i_x27_1903_);
return v_x_1895_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux___boxed(lean_object* v_x_1906_, lean_object* v_x_1907_, lean_object* v_x_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_String_Pos_Raw_utf8PrevAux(v_x_1906_, v_x_1907_, v_x_1908_);
lean_dec(v_x_1908_);
lean_dec(v_x_1906_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux(lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_String_Pos_Raw_utf8PrevAux(v_a_1910_, v_a_1911_, v_a_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux___boxed(lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_String_utf8PrevAux(v_a_1914_, v_a_1915_, v_a_1916_);
lean_dec(v_a_1916_);
lean_dec(v_a_1914_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_prev___boxed(lean_object* v_a_00___x40___internal___hyg_1920_, lean_object* v_a_00___x40___internal___hyg_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_1920_, v_a_00___x40___internal___hyg_1921_);
lean_dec(v_a_00___x40___internal___hyg_1921_);
lean_dec_ref(v_a_00___x40___internal___hyg_1920_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_String_prev___boxed(lean_object* v_a_00___x40___internal___hyg_1925_, lean_object* v_a_00___x40___internal___hyg_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_1925_, v_a_00___x40___internal___hyg_1926_);
lean_dec(v_a_00___x40___internal___hyg_1926_);
lean_dec_ref(v_a_00___x40___internal___hyg_1925_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_1930_, lean_object* v_a_00___x40___internal___hyg_1931_){
_start:
{
uint8_t v_res_1932_; lean_object* v_r_1933_; 
v_res_1932_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_1930_, v_a_00___x40___internal___hyg_1931_);
lean_dec(v_a_00___x40___internal___hyg_1931_);
lean_dec_ref(v_a_00___x40___internal___hyg_1930_);
v_r_1933_ = lean_box(v_res_1932_);
return v_r_1933_;
}
}
LEAN_EXPORT lean_object* l_String_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_1936_, lean_object* v_a_00___x40___internal___hyg_1937_){
_start:
{
uint8_t v_res_1938_; lean_object* v_r_1939_; 
v_res_1938_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_1936_, v_a_00___x40___internal___hyg_1937_);
lean_dec(v_a_00___x40___internal___hyg_1937_);
lean_dec_ref(v_a_00___x40___internal___hyg_1936_);
v_r_1939_ = lean_box(v_res_1938_);
return v_r_1939_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x27___boxed(lean_object* v_s_1943_, lean_object* v_p_1944_, lean_object* v_h_1945_){
_start:
{
uint32_t v_res_1946_; lean_object* v_r_1947_; 
v_res_1946_ = lean_string_utf8_get_fast(v_s_1943_, v_p_1944_);
lean_dec(v_p_1944_);
lean_dec_ref(v_s_1943_);
v_r_1947_ = lean_box_uint32(v_res_1946_);
return v_r_1947_;
}
}
LEAN_EXPORT lean_object* l_String_get_x27___boxed(lean_object* v_s_1951_, lean_object* v_p_1952_, lean_object* v_h_1953_){
_start:
{
uint32_t v_res_1954_; lean_object* v_r_1955_; 
v_res_1954_ = lean_string_utf8_get_fast(v_s_1951_, v_p_1952_);
lean_dec(v_p_1952_);
lean_dec_ref(v_s_1951_);
v_r_1955_ = lean_box_uint32(v_res_1954_);
return v_r_1955_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next_x27___boxed(lean_object* v_s_1959_, lean_object* v_p_1960_, lean_object* v_h_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = lean_string_utf8_next_fast(v_s_1959_, v_p_1960_);
lean_dec(v_p_1960_);
lean_dec_ref(v_s_1959_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_String_next_x27___boxed(lean_object* v_s_1966_, lean_object* v_p_1967_, lean_object* v_h_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = lean_string_utf8_next_fast(v_s_1966_, v_p_1967_);
lean_dec(v_p_1967_);
lean_dec_ref(v_s_1966_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter___redArg(lean_object* v_x_1970_, lean_object* v_x_1971_, lean_object* v_x_1972_, lean_object* v_h__1_1973_, lean_object* v_h__2_1974_){
_start:
{
if (lean_obj_tag(v_x_1970_) == 0)
{
lean_object* v___x_1975_; 
lean_dec(v_h__2_1974_);
v___x_1975_ = lean_apply_2(v_h__1_1973_, v_x_1971_, v_x_1972_);
return v___x_1975_;
}
else
{
lean_object* v_head_1976_; lean_object* v_tail_1977_; lean_object* v___x_1978_; 
lean_dec(v_h__1_1973_);
v_head_1976_ = lean_ctor_get(v_x_1970_, 0);
lean_inc(v_head_1976_);
v_tail_1977_ = lean_ctor_get(v_x_1970_, 1);
lean_inc(v_tail_1977_);
lean_dec_ref_known(v_x_1970_, 2);
v___x_1978_ = lean_apply_4(v_h__2_1974_, v_head_1976_, v_tail_1977_, v_x_1971_, v_x_1972_);
return v___x_1978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter(lean_object* v_motive_1979_, lean_object* v_x_1980_, lean_object* v_x_1981_, lean_object* v_x_1982_, lean_object* v_h__1_1983_, lean_object* v_h__2_1984_){
_start:
{
if (lean_obj_tag(v_x_1980_) == 0)
{
lean_object* v___x_1985_; 
lean_dec(v_h__2_1984_);
v___x_1985_ = lean_apply_2(v_h__1_1983_, v_x_1981_, v_x_1982_);
return v___x_1985_;
}
else
{
lean_object* v_head_1986_; lean_object* v_tail_1987_; lean_object* v___x_1988_; 
lean_dec(v_h__1_1983_);
v_head_1986_ = lean_ctor_get(v_x_1980_, 0);
lean_inc(v_head_1986_);
v_tail_1987_ = lean_ctor_get(v_x_1980_, 1);
lean_inc(v_tail_1987_);
lean_dec_ref_known(v_x_1980_, 2);
v___x_1988_ = lean_apply_4(v_h__2_1984_, v_head_1986_, v_tail_1987_, v_x_1981_, v_x_1982_);
return v___x_1988_;
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop(lean_object* v_a_1989_, lean_object* v_b_1990_, lean_object* v_stopPos_1991_, lean_object* v_i_1992_){
_start:
{
uint8_t v___x_1993_; 
v___x_1993_ = lean_nat_dec_lt(v_i_1992_, v_stopPos_1991_);
if (v___x_1993_ == 0)
{
return v_i_1992_;
}
else
{
uint32_t v___x_1994_; uint32_t v___x_1995_; uint8_t v___x_1996_; uint8_t v___x_1997_; 
v___x_1994_ = lean_string_utf8_get(v_a_1989_, v_i_1992_);
v___x_1995_ = lean_string_utf8_get(v_b_1990_, v_i_1992_);
v___x_1996_ = lean_uint32_dec_eq(v___x_1994_, v___x_1995_);
v___x_1997_ = lean_bool_not(v___x_1996_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; 
v___x_1998_ = lean_string_utf8_next(v_a_1989_, v_i_1992_);
lean_dec(v_i_1992_);
v_i_1992_ = v___x_1998_;
goto _start;
}
else
{
return v_i_1992_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop___boxed(lean_object* v_a_2000_, lean_object* v_b_2001_, lean_object* v_stopPos_2002_, lean_object* v_i_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_String_firstDiffPos_loop(v_a_2000_, v_b_2001_, v_stopPos_2002_, v_i_2003_);
lean_dec(v_stopPos_2002_);
lean_dec_ref(v_b_2001_);
lean_dec_ref(v_a_2000_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos(lean_object* v_a_2005_, lean_object* v_b_2006_){
_start:
{
lean_object* v___y_2008_; lean_object* v___x_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; 
v___x_2011_ = lean_string_utf8_byte_size(v_a_2005_);
v___x_2012_ = lean_string_utf8_byte_size(v_b_2006_);
v___x_2013_ = lean_nat_dec_le(v___x_2011_, v___x_2012_);
if (v___x_2013_ == 0)
{
v___y_2008_ = v___x_2012_;
goto v___jp_2007_;
}
else
{
v___y_2008_ = v___x_2011_;
goto v___jp_2007_;
}
v___jp_2007_:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = lean_unsigned_to_nat(0u);
v___x_2010_ = l_String_firstDiffPos_loop(v_a_2005_, v_b_2006_, v___y_2008_, v___x_2009_);
lean_dec(v___y_2008_);
return v___x_2010_;
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos___boxed(lean_object* v_a_2014_, lean_object* v_b_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_String_firstDiffPos(v_a_2014_, v_b_2015_);
lean_dec_ref(v_b_2015_);
lean_dec_ref(v_a_2014_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082(lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_){
_start:
{
if (lean_obj_tag(v_a_2017_) == 0)
{
return v_a_2017_;
}
else
{
lean_object* v_head_2020_; lean_object* v_tail_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2034_; 
v_head_2020_ = lean_ctor_get(v_a_2017_, 0);
v_tail_2021_ = lean_ctor_get(v_a_2017_, 1);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_a_2017_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2023_ = v_a_2017_;
v_isShared_2024_ = v_isSharedCheck_2034_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_tail_2021_);
lean_inc(v_head_2020_);
lean_dec(v_a_2017_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2034_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
uint8_t v___x_2025_; 
v___x_2025_ = lean_nat_dec_eq(v_a_2018_, v_a_2019_);
if (v___x_2025_ == 0)
{
uint32_t v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2026_ = lean_unbox_uint32(v_head_2020_);
v___x_2027_ = l_Char_utf8Size(v___x_2026_);
v___x_2028_ = lean_nat_add(v_a_2018_, v___x_2027_);
lean_dec(v___x_2027_);
v___x_2029_ = l_String_Pos_Raw_extract_go_u2082(v_tail_2021_, v___x_2028_, v_a_2019_);
lean_dec(v___x_2028_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 1, v___x_2029_);
v___x_2031_ = v___x_2023_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_head_2020_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
else
{
lean_object* v___x_2033_; 
lean_del_object(v___x_2023_);
lean_dec(v_tail_2021_);
lean_dec(v_head_2020_);
v___x_2033_ = lean_box(0);
return v___x_2033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082___boxed(lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_String_Pos_Raw_extract_go_u2082(v_a_2035_, v_a_2036_, v_a_2037_);
lean_dec(v_a_2037_);
lean_dec(v_a_2036_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081(lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
if (lean_obj_tag(v_a_2039_) == 0)
{
lean_dec(v_a_2040_);
return v_a_2039_;
}
else
{
lean_object* v_head_2043_; lean_object* v_tail_2044_; uint8_t v___x_2045_; 
v_head_2043_ = lean_ctor_get(v_a_2039_, 0);
v_tail_2044_ = lean_ctor_get(v_a_2039_, 1);
v___x_2045_ = lean_nat_dec_eq(v_a_2040_, v_a_2041_);
if (v___x_2045_ == 0)
{
uint32_t v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
lean_inc(v_tail_2044_);
lean_inc(v_head_2043_);
lean_dec_ref_known(v_a_2039_, 2);
v___x_2046_ = lean_unbox_uint32(v_head_2043_);
lean_dec(v_head_2043_);
v___x_2047_ = l_Char_utf8Size(v___x_2046_);
v___x_2048_ = lean_nat_add(v_a_2040_, v___x_2047_);
lean_dec(v___x_2047_);
lean_dec(v_a_2040_);
v_a_2039_ = v_tail_2044_;
v_a_2040_ = v___x_2048_;
goto _start;
}
else
{
lean_object* v___x_2050_; 
v___x_2050_ = l_String_Pos_Raw_extract_go_u2082(v_a_2039_, v_a_2040_, v_a_2042_);
lean_dec(v_a_2040_);
return v___x_2050_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081___boxed(lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_String_Pos_Raw_extract_go_u2081(v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_);
lean_dec(v_a_2054_);
lean_dec(v_a_2053_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract___boxed(lean_object* v_a_00___x40___internal___hyg_2059_, lean_object* v_a_00___x40___internal___hyg_2060_, lean_object* v_a_00___x40___internal___hyg_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = lean_string_utf8_extract(v_a_00___x40___internal___hyg_2059_, v_a_00___x40___internal___hyg_2060_, v_a_00___x40___internal___hyg_2061_);
lean_dec(v_a_00___x40___internal___hyg_2061_);
lean_dec(v_a_00___x40___internal___hyg_2060_);
lean_dec_ref(v_a_00___x40___internal___hyg_2059_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux(lean_object* v_s_2063_, lean_object* v_pos_2064_, lean_object* v_i_2065_, lean_object* v_offset_2066_){
_start:
{
uint8_t v___x_2067_; 
v___x_2067_ = lean_nat_dec_le(v_pos_2064_, v_i_2065_);
if (v___x_2067_ == 0)
{
uint8_t v___x_2068_; 
v___x_2068_ = lean_string_utf8_at_end(v_s_2063_, v_i_2065_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2069_ = lean_string_utf8_next(v_s_2063_, v_i_2065_);
lean_dec(v_i_2065_);
v___x_2070_ = lean_unsigned_to_nat(1u);
v___x_2071_ = lean_nat_add(v_offset_2066_, v___x_2070_);
lean_dec(v_offset_2066_);
v_i_2065_ = v___x_2069_;
v_offset_2066_ = v___x_2071_;
goto _start;
}
else
{
lean_dec(v_i_2065_);
return v_offset_2066_;
}
}
else
{
lean_dec(v_i_2065_);
return v_offset_2066_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux___boxed(lean_object* v_s_2073_, lean_object* v_pos_2074_, lean_object* v_i_2075_, lean_object* v_offset_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2073_, v_pos_2074_, v_i_2075_, v_offset_2076_);
lean_dec(v_pos_2074_);
lean_dec_ref(v_s_2073_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos(lean_object* v_s_2078_, lean_object* v_pos_2079_){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2080_ = lean_unsigned_to_nat(0u);
v___x_2081_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2078_, v_pos_2079_, v___x_2080_, v___x_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos___boxed(lean_object* v_s_2082_, lean_object* v_pos_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_String_Pos_Raw_offsetOfPos(v_s_2082_, v_pos_2083_);
lean_dec(v_pos_2083_);
lean_dec_ref(v_s_2082_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos(lean_object* v_s_2085_, lean_object* v_pos_2086_){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = lean_unsigned_to_nat(0u);
v___x_2088_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2085_, v_pos_2086_, v___x_2087_, v___x_2087_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos___boxed(lean_object* v_s_2089_, lean_object* v_pos_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_String_offsetOfPos(v_s_2089_, v_pos_2090_);
lean_dec(v_pos_2090_);
lean_dec_ref(v_s_2089_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* lean_string_offsetofpos(lean_object* v_s_2092_, lean_object* v_pos_2093_){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2094_ = lean_unsigned_to_nat(0u);
v___x_2095_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2092_, v_pos_2093_, v___x_2094_, v___x_2094_);
lean_dec(v_pos_2093_);
lean_dec_ref(v_s_2092_);
return v___x_2095_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(lean_object* v_s1_2096_, lean_object* v_s2_2097_, lean_object* v_off1_2098_, lean_object* v_off2_2099_, lean_object* v_stop1_2100_){
_start:
{
uint8_t v___x_2101_; 
v___x_2101_ = lean_nat_dec_lt(v_off1_2098_, v_stop1_2100_);
if (v___x_2101_ == 0)
{
uint8_t v___x_2102_; 
lean_dec(v_off2_2099_);
lean_dec(v_off1_2098_);
v___x_2102_ = 1;
return v___x_2102_;
}
else
{
uint32_t v_c_u2081_2103_; uint32_t v_c_u2082_2104_; uint8_t v___x_2105_; 
v_c_u2081_2103_ = lean_string_utf8_get(v_s1_2096_, v_off1_2098_);
v_c_u2082_2104_ = lean_string_utf8_get(v_s2_2097_, v_off2_2099_);
v___x_2105_ = lean_uint32_dec_eq(v_c_u2081_2103_, v_c_u2082_2104_);
if (v___x_2105_ == 0)
{
lean_dec(v_off2_2099_);
lean_dec(v_off1_2098_);
return v___x_2105_;
}
else
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2106_ = l_Char_utf8Size(v_c_u2081_2103_);
v___x_2107_ = lean_nat_add(v_off1_2098_, v___x_2106_);
lean_dec(v___x_2106_);
lean_dec(v_off1_2098_);
v___x_2108_ = l_Char_utf8Size(v_c_u2082_2104_);
v___x_2109_ = lean_nat_add(v_off2_2099_, v___x_2108_);
lean_dec(v___x_2108_);
lean_dec(v_off2_2099_);
v_off1_2098_ = v___x_2107_;
v_off2_2099_ = v___x_2109_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop___boxed(lean_object* v_s1_2111_, lean_object* v_s2_2112_, lean_object* v_off1_2113_, lean_object* v_off2_2114_, lean_object* v_stop1_2115_){
_start:
{
uint8_t v_res_2116_; lean_object* v_r_2117_; 
v_res_2116_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2111_, v_s2_2112_, v_off1_2113_, v_off2_2114_, v_stop1_2115_);
lean_dec(v_stop1_2115_);
lean_dec_ref(v_s2_2112_);
lean_dec_ref(v_s1_2111_);
v_r_2117_ = lean_box(v_res_2116_);
return v_r_2117_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_substrEq(lean_object* v_s1_2118_, lean_object* v_pos1_2119_, lean_object* v_s2_2120_, lean_object* v_pos2_2121_, lean_object* v_sz_2122_){
_start:
{
uint8_t v___y_2124_; lean_object* v___x_2127_; lean_object* v___x_2128_; uint8_t v___x_2129_; 
v___x_2127_ = lean_nat_add(v_pos1_2119_, v_sz_2122_);
v___x_2128_ = lean_string_utf8_byte_size(v_s1_2118_);
v___x_2129_ = lean_nat_dec_le(v___x_2127_, v___x_2128_);
lean_dec(v___x_2127_);
if (v___x_2129_ == 0)
{
v___y_2124_ = v___x_2129_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; 
v___x_2130_ = lean_nat_add(v_pos2_2121_, v_sz_2122_);
v___x_2131_ = lean_string_utf8_byte_size(v_s2_2120_);
v___x_2132_ = lean_nat_dec_le(v___x_2130_, v___x_2131_);
lean_dec(v___x_2130_);
v___y_2124_ = v___x_2132_;
goto v___jp_2123_;
}
v___jp_2123_:
{
if (v___y_2124_ == 0)
{
lean_dec(v_pos2_2121_);
lean_dec(v_pos1_2119_);
return v___y_2124_;
}
else
{
lean_object* v___x_2125_; uint8_t v___x_2126_; 
v___x_2125_ = lean_nat_add(v_pos1_2119_, v_sz_2122_);
v___x_2126_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2118_, v_s2_2120_, v_pos1_2119_, v_pos2_2121_, v___x_2125_);
lean_dec(v___x_2125_);
return v___x_2126_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_substrEq___boxed(lean_object* v_s1_2133_, lean_object* v_pos1_2134_, lean_object* v_s2_2135_, lean_object* v_pos2_2136_, lean_object* v_sz_2137_){
_start:
{
uint8_t v_res_2138_; lean_object* v_r_2139_; 
v_res_2138_ = l_String_Pos_Raw_substrEq(v_s1_2133_, v_pos1_2134_, v_s2_2135_, v_pos2_2136_, v_sz_2137_);
lean_dec(v_sz_2137_);
lean_dec_ref(v_s2_2135_);
lean_dec_ref(v_s1_2133_);
v_r_2139_ = lean_box(v_res_2138_);
return v_r_2139_;
}
}
LEAN_EXPORT uint8_t l_String_substrEq(lean_object* v_s1_2140_, lean_object* v_pos1_2141_, lean_object* v_s2_2142_, lean_object* v_pos2_2143_, lean_object* v_sz_2144_){
_start:
{
uint8_t v___x_2145_; 
v___x_2145_ = l_String_Pos_Raw_substrEq(v_s1_2140_, v_pos1_2141_, v_s2_2142_, v_pos2_2143_, v_sz_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_String_substrEq___boxed(lean_object* v_s1_2146_, lean_object* v_pos1_2147_, lean_object* v_s2_2148_, lean_object* v_pos2_2149_, lean_object* v_sz_2150_){
_start:
{
uint8_t v_res_2151_; lean_object* v_r_2152_; 
v_res_2151_ = l_String_substrEq(v_s1_2146_, v_pos1_2147_, v_s2_2148_, v_pos2_2149_, v_sz_2150_);
lean_dec(v_sz_2150_);
lean_dec_ref(v_s2_2148_);
lean_dec_ref(v_s1_2146_);
v_r_2152_ = lean_box(v_res_2151_);
return v_r_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object* v_x_2153_, lean_object* v_x_2154_, lean_object* v_h__1_2155_){
_start:
{
lean_object* v___x_2156_; 
v___x_2156_ = lean_apply_2(v_h__1_2155_, v_x_2153_, v_x_2154_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object* v_motive_2157_, lean_object* v_x_2158_, lean_object* v_x_2159_, lean_object* v_h__1_2160_){
_start:
{
lean_object* v___x_2161_; 
v___x_2161_ = lean_apply_2(v_h__1_2160_, v_x_2158_, v_x_2159_);
return v___x_2161_;
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
