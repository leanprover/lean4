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
lean_object* v___y_171_; uint8_t v___y_175_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_192_ = lean_byte_array_size(v_b_168_);
v___x_193_ = lean_nat_dec_lt(v_i_169_, v___x_192_);
if (v___x_193_ == 0)
{
uint8_t v___x_194_; 
lean_dec(v_i_169_);
v___x_194_ = 1;
return v___x_194_;
}
else
{
if (v___x_193_ == 0)
{
lean_dec(v_i_169_);
return v___x_193_;
}
else
{
uint8_t v___x_195_; uint8_t v___x_196_; uint8_t v___x_197_; uint8_t v___x_198_; uint8_t v___x_199_; 
v___x_195_ = lean_byte_array_fget(v_b_168_, v_i_169_);
v___x_196_ = 128;
v___x_197_ = lean_uint8_land(v___x_195_, v___x_196_);
v___x_198_ = 0;
v___x_199_ = lean_uint8_dec_eq(v___x_197_, v___x_198_);
if (v___x_199_ == 0)
{
uint8_t v___x_200_; uint8_t v___x_201_; uint8_t v___x_202_; uint8_t v___x_203_; 
v___x_200_ = 224;
v___x_201_ = lean_uint8_land(v___x_195_, v___x_200_);
v___x_202_ = 192;
v___x_203_ = lean_uint8_dec_eq(v___x_201_, v___x_202_);
if (v___x_203_ == 0)
{
uint8_t v___x_204_; uint8_t v___x_205_; uint8_t v___x_206_; 
v___x_204_ = 240;
v___x_205_ = lean_uint8_land(v___x_195_, v___x_204_);
v___x_206_ = lean_uint8_dec_eq(v___x_205_, v___x_200_);
if (v___x_206_ == 0)
{
uint8_t v___x_207_; uint8_t v___x_208_; uint8_t v___x_209_; 
v___x_207_ = 248;
v___x_208_ = lean_uint8_land(v___x_195_, v___x_207_);
v___x_209_ = lean_uint8_dec_eq(v___x_208_, v___x_204_);
if (v___x_209_ == 0)
{
v___y_175_ = v___x_209_;
goto v___jp_174_;
}
else
{
lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_210_ = lean_unsigned_to_nat(3u);
v___x_211_ = lean_nat_add(v_i_169_, v___x_210_);
v___x_212_ = lean_nat_dec_lt(v___x_211_, v___x_192_);
if (v___x_212_ == 0)
{
lean_dec(v___x_211_);
v___y_175_ = v___x_206_;
goto v___jp_174_;
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; uint8_t v___x_216_; uint8_t v___x_217_; 
v___x_213_ = lean_unsigned_to_nat(1u);
v___x_214_ = lean_nat_add(v_i_169_, v___x_213_);
v___x_215_ = lean_byte_array_fget(v_b_168_, v___x_214_);
lean_dec(v___x_214_);
v___x_216_ = lean_uint8_land(v___x_215_, v___x_202_);
v___x_217_ = lean_uint8_dec_eq(v___x_216_, v___x_196_);
if (v___x_217_ == 0)
{
lean_dec(v___x_211_);
v___y_175_ = v___x_217_;
goto v___jp_174_;
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; uint8_t v___x_221_; uint8_t v___x_222_; 
v___x_218_ = lean_unsigned_to_nat(2u);
v___x_219_ = lean_nat_add(v_i_169_, v___x_218_);
v___x_220_ = lean_byte_array_fget(v_b_168_, v___x_219_);
lean_dec(v___x_219_);
v___x_221_ = lean_uint8_land(v___x_220_, v___x_202_);
v___x_222_ = lean_uint8_dec_eq(v___x_221_, v___x_196_);
if (v___x_222_ == 0)
{
lean_dec(v___x_211_);
v___y_175_ = v___x_222_;
goto v___jp_174_;
}
else
{
uint8_t v___x_223_; uint8_t v___x_224_; uint8_t v___x_225_; 
v___x_223_ = lean_byte_array_fget(v_b_168_, v___x_211_);
lean_dec(v___x_211_);
v___x_224_ = lean_uint8_land(v___x_223_, v___x_202_);
v___x_225_ = lean_uint8_dec_eq(v___x_224_, v___x_196_);
if (v___x_225_ == 0)
{
v___y_175_ = v___x_225_;
goto v___jp_174_;
}
else
{
uint8_t v___x_226_; uint8_t v_b_u2080_227_; uint8_t v___x_228_; uint8_t v_b_u2081_229_; uint8_t v_b_u2082_230_; uint8_t v_b_u2083_231_; uint32_t v___x_232_; uint32_t v___x_233_; uint32_t v___x_234_; uint32_t v___x_235_; uint32_t v___x_236_; uint32_t v___x_237_; uint32_t v___x_238_; uint32_t v___x_239_; uint32_t v___x_240_; uint32_t v___x_241_; uint32_t v___x_242_; uint32_t v___x_243_; uint32_t v_r_244_; uint32_t v___x_245_; uint8_t v___x_246_; 
v___x_226_ = 7;
v_b_u2080_227_ = lean_uint8_land(v___x_195_, v___x_226_);
v___x_228_ = 63;
v_b_u2081_229_ = lean_uint8_land(v___x_215_, v___x_228_);
v_b_u2082_230_ = lean_uint8_land(v___x_220_, v___x_228_);
v_b_u2083_231_ = lean_uint8_land(v___x_223_, v___x_228_);
v___x_232_ = lean_uint8_to_uint32(v_b_u2080_227_);
v___x_233_ = 18;
v___x_234_ = lean_uint32_shift_left(v___x_232_, v___x_233_);
v___x_235_ = lean_uint8_to_uint32(v_b_u2081_229_);
v___x_236_ = 12;
v___x_237_ = lean_uint32_shift_left(v___x_235_, v___x_236_);
v___x_238_ = lean_uint32_lor(v___x_234_, v___x_237_);
v___x_239_ = lean_uint8_to_uint32(v_b_u2082_230_);
v___x_240_ = 6;
v___x_241_ = lean_uint32_shift_left(v___x_239_, v___x_240_);
v___x_242_ = lean_uint32_lor(v___x_238_, v___x_241_);
v___x_243_ = lean_uint8_to_uint32(v_b_u2083_231_);
v_r_244_ = lean_uint32_lor(v___x_242_, v___x_243_);
v___x_245_ = 65536;
v___x_246_ = lean_uint32_dec_le(v___x_245_, v_r_244_);
if (v___x_246_ == 0)
{
v___y_175_ = v___x_206_;
goto v___jp_174_;
}
else
{
uint32_t v___x_247_; uint8_t v___x_248_; 
v___x_247_ = 1114111;
v___x_248_ = lean_uint32_dec_le(v_r_244_, v___x_247_);
if (v___x_248_ == 0)
{
v___y_175_ = v___x_206_;
goto v___jp_174_;
}
else
{
v___y_175_ = v___x_225_;
goto v___jp_174_;
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
lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_249_ = lean_unsigned_to_nat(2u);
v___x_250_ = lean_nat_add(v_i_169_, v___x_249_);
v___x_251_ = lean_nat_dec_lt(v___x_250_, v___x_192_);
if (v___x_251_ == 0)
{
lean_dec(v___x_250_);
v___y_175_ = v___x_203_;
goto v___jp_174_;
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; uint8_t v___x_255_; uint8_t v___x_256_; 
v___x_252_ = lean_unsigned_to_nat(1u);
v___x_253_ = lean_nat_add(v_i_169_, v___x_252_);
v___x_254_ = lean_byte_array_fget(v_b_168_, v___x_253_);
lean_dec(v___x_253_);
v___x_255_ = lean_uint8_land(v___x_254_, v___x_202_);
v___x_256_ = lean_uint8_dec_eq(v___x_255_, v___x_196_);
if (v___x_256_ == 0)
{
lean_dec(v___x_250_);
v___y_175_ = v___x_256_;
goto v___jp_174_;
}
else
{
uint8_t v___x_257_; uint8_t v___x_258_; uint8_t v___x_259_; 
v___x_257_ = lean_byte_array_fget(v_b_168_, v___x_250_);
lean_dec(v___x_250_);
v___x_258_ = lean_uint8_land(v___x_257_, v___x_202_);
v___x_259_ = lean_uint8_dec_eq(v___x_258_, v___x_196_);
if (v___x_259_ == 0)
{
v___y_175_ = v___x_259_;
goto v___jp_174_;
}
else
{
uint8_t v___x_260_; uint8_t v_b_u2080_261_; uint8_t v___x_262_; uint8_t v_b_u2081_263_; uint8_t v_b_u2082_264_; uint32_t v___x_265_; uint32_t v___x_266_; uint32_t v___x_267_; uint32_t v___x_268_; uint32_t v___x_269_; uint32_t v___x_270_; uint32_t v___x_271_; uint32_t v___x_272_; uint32_t v_r_273_; uint32_t v___x_274_; uint8_t v___x_275_; 
v___x_260_ = 15;
v_b_u2080_261_ = lean_uint8_land(v___x_195_, v___x_260_);
v___x_262_ = 63;
v_b_u2081_263_ = lean_uint8_land(v___x_254_, v___x_262_);
v_b_u2082_264_ = lean_uint8_land(v___x_257_, v___x_262_);
v___x_265_ = lean_uint8_to_uint32(v_b_u2080_261_);
v___x_266_ = 12;
v___x_267_ = lean_uint32_shift_left(v___x_265_, v___x_266_);
v___x_268_ = lean_uint8_to_uint32(v_b_u2081_263_);
v___x_269_ = 6;
v___x_270_ = lean_uint32_shift_left(v___x_268_, v___x_269_);
v___x_271_ = lean_uint32_lor(v___x_267_, v___x_270_);
v___x_272_ = lean_uint8_to_uint32(v_b_u2082_264_);
v_r_273_ = lean_uint32_lor(v___x_271_, v___x_272_);
v___x_274_ = 2048;
v___x_275_ = lean_uint32_dec_le(v___x_274_, v_r_273_);
if (v___x_275_ == 0)
{
v___y_175_ = v___x_203_;
goto v___jp_174_;
}
else
{
uint32_t v___x_276_; uint8_t v___x_277_; 
v___x_276_ = 55296;
v___x_277_ = lean_uint32_dec_lt(v_r_273_, v___x_276_);
if (v___x_277_ == 0)
{
uint32_t v___x_278_; uint8_t v___x_279_; 
v___x_278_ = 57343;
v___x_279_ = lean_uint32_dec_lt(v___x_278_, v_r_273_);
if (v___x_279_ == 0)
{
v___y_175_ = v___x_203_;
goto v___jp_174_;
}
else
{
v___y_175_ = v___x_259_;
goto v___jp_174_;
}
}
else
{
v___y_175_ = v___x_259_;
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
lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_280_ = lean_unsigned_to_nat(1u);
v___x_281_ = lean_nat_add(v_i_169_, v___x_280_);
v___x_282_ = lean_nat_dec_lt(v___x_281_, v___x_192_);
if (v___x_282_ == 0)
{
lean_dec(v___x_281_);
v___y_175_ = v___x_199_;
goto v___jp_174_;
}
else
{
uint8_t v___x_283_; uint8_t v___x_284_; uint8_t v___x_285_; 
v___x_283_ = lean_byte_array_fget(v_b_168_, v___x_281_);
lean_dec(v___x_281_);
v___x_284_ = lean_uint8_land(v___x_283_, v___x_202_);
v___x_285_ = lean_uint8_dec_eq(v___x_284_, v___x_196_);
if (v___x_285_ == 0)
{
v___y_175_ = v___x_285_;
goto v___jp_174_;
}
else
{
uint8_t v___x_286_; uint8_t v_b_u2080_287_; uint8_t v___x_288_; uint8_t v_b_u2081_289_; uint32_t v___x_290_; uint32_t v___x_291_; uint32_t v___x_292_; uint32_t v___x_293_; uint32_t v_r_294_; uint32_t v___x_295_; uint8_t v___x_296_; 
v___x_286_ = 31;
v_b_u2080_287_ = lean_uint8_land(v___x_195_, v___x_286_);
v___x_288_ = 63;
v_b_u2081_289_ = lean_uint8_land(v___x_283_, v___x_288_);
v___x_290_ = lean_uint8_to_uint32(v_b_u2080_287_);
v___x_291_ = 6;
v___x_292_ = lean_uint32_shift_left(v___x_290_, v___x_291_);
v___x_293_ = lean_uint8_to_uint32(v_b_u2081_289_);
v_r_294_ = lean_uint32_lor(v___x_292_, v___x_293_);
v___x_295_ = 128;
v___x_296_ = lean_uint32_dec_le(v___x_295_, v_r_294_);
v___y_175_ = v___x_296_;
goto v___jp_174_;
}
}
}
}
else
{
v___y_175_ = v___x_199_;
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
if (v___y_175_ == 0)
{
lean_dec(v_i_169_);
return v___y_175_;
}
else
{
uint8_t v___x_176_; uint8_t v___x_177_; uint8_t v___x_178_; uint8_t v___x_179_; uint8_t v___x_180_; 
v___x_176_ = lean_byte_array_fget(v_b_168_, v_i_169_);
v___x_177_ = 128;
v___x_178_ = lean_uint8_land(v___x_176_, v___x_177_);
v___x_179_ = 0;
v___x_180_ = lean_uint8_dec_eq(v___x_178_, v___x_179_);
if (v___x_180_ == 0)
{
uint8_t v___x_181_; uint8_t v___x_182_; uint8_t v___x_183_; uint8_t v___x_184_; 
v___x_181_ = 224;
v___x_182_ = lean_uint8_land(v___x_176_, v___x_181_);
v___x_183_ = 192;
v___x_184_ = lean_uint8_dec_eq(v___x_182_, v___x_183_);
if (v___x_184_ == 0)
{
uint8_t v___x_185_; uint8_t v___x_186_; uint8_t v___x_187_; 
v___x_185_ = 240;
v___x_186_ = lean_uint8_land(v___x_176_, v___x_185_);
v___x_187_ = lean_uint8_dec_eq(v___x_186_, v___x_181_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; 
v___x_188_ = lean_unsigned_to_nat(4u);
v___y_171_ = v___x_188_;
goto v___jp_170_;
}
else
{
lean_object* v___x_189_; 
v___x_189_ = lean_unsigned_to_nat(3u);
v___y_171_ = v___x_189_;
goto v___jp_170_;
}
}
else
{
lean_object* v___x_190_; 
v___x_190_ = lean_unsigned_to_nat(2u);
v___y_171_ = v___x_190_;
goto v___jp_170_;
}
}
else
{
lean_object* v___x_191_; 
v___x_191_ = lean_unsigned_to_nat(1u);
v___y_171_ = v___x_191_;
goto v___jp_170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___redArg___boxed(lean_object* v_b_297_, lean_object* v_i_298_){
_start:
{
uint8_t v_res_299_; lean_object* v_r_300_; 
v_res_299_ = l_ByteArray_validateUTF8_go___redArg(v_b_297_, v_i_298_);
lean_dec_ref(v_b_297_);
v_r_300_ = lean_box(v_res_299_);
return v_r_300_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8_go(lean_object* v_b_301_, lean_object* v_i_302_, lean_object* v_hi_303_){
_start:
{
uint8_t v___x_304_; 
v___x_304_ = l_ByteArray_validateUTF8_go___redArg(v_b_301_, v_i_302_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___boxed(lean_object* v_b_305_, lean_object* v_i_306_, lean_object* v_hi_307_){
_start:
{
uint8_t v_res_308_; lean_object* v_r_309_; 
v_res_308_ = l_ByteArray_validateUTF8_go(v_b_305_, v_i_306_, v_hi_307_);
lean_dec_ref(v_b_305_);
v_r_309_ = lean_box(v_res_308_);
return v_r_309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(uint8_t v_x_310_, lean_object* v_h__1_311_, lean_object* v_h__2_312_){
_start:
{
if (v_x_310_ == 0)
{
lean_object* v___x_313_; 
lean_dec(v_h__2_312_);
v___x_313_ = lean_apply_1(v_h__1_311_, lean_box(0));
return v___x_313_;
}
else
{
lean_object* v___x_314_; 
lean_dec(v_h__1_311_);
v___x_314_ = lean_apply_1(v_h__2_312_, lean_box(0));
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg___boxed(lean_object* v_x_315_, lean_object* v_h__1_316_, lean_object* v_h__2_317_){
_start:
{
uint8_t v_x_26__boxed_318_; lean_object* v_res_319_; 
v_x_26__boxed_318_ = lean_unbox(v_x_315_);
v_res_319_ = l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(v_x_26__boxed_318_, v_h__1_316_, v_h__2_317_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(lean_object* v_motive_320_, uint8_t v_x_321_, lean_object* v_h__1_322_, lean_object* v_h__2_323_){
_start:
{
if (v_x_321_ == 0)
{
lean_object* v___x_324_; 
lean_dec(v_h__2_323_);
v___x_324_ = lean_apply_1(v_h__1_322_, lean_box(0));
return v___x_324_;
}
else
{
lean_object* v___x_325_; 
lean_dec(v_h__1_322_);
v___x_325_ = lean_apply_1(v_h__2_323_, lean_box(0));
return v___x_325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___boxed(lean_object* v_motive_326_, lean_object* v_x_327_, lean_object* v_h__1_328_, lean_object* v_h__2_329_){
_start:
{
uint8_t v_x_33__boxed_330_; lean_object* v_res_331_; 
v_x_33__boxed_330_ = lean_unbox(v_x_327_);
v_res_331_ = l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(v_motive_326_, v_x_33__boxed_330_, v_h__1_328_, v_h__2_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8___boxed(lean_object* v_b_333_){
_start:
{
uint8_t v_res_334_; lean_object* v_r_335_; 
v_res_334_ = lean_string_validate_utf8(v_b_333_);
lean_dec_ref(v_b_333_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
LEAN_EXPORT uint8_t l_instDecidableIsValidUTF8(lean_object* v_b_336_){
_start:
{
uint8_t v___x_337_; 
v___x_337_ = lean_string_validate_utf8(v_b_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_instDecidableIsValidUTF8___boxed(lean_object* v_b_338_){
_start:
{
uint8_t v_res_339_; lean_object* v_r_340_; 
v_res_339_ = l_instDecidableIsValidUTF8(v_b_338_);
lean_dec_ref(v_b_338_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_x3f(lean_object* v_a_341_){
_start:
{
uint8_t v___x_342_; 
v___x_342_ = lean_string_validate_utf8(v_a_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; 
lean_dec_ref(v_a_341_);
v___x_343_ = lean_box(0);
return v___x_343_;
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_string_from_utf8_unchecked(v_a_341_);
v___x_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
}
static lean_object* _init_l_String_fromUTF8_x21___closed__4(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_350_ = ((lean_object*)(l_String_fromUTF8_x21___closed__3));
v___x_351_ = lean_unsigned_to_nat(46u);
v___x_352_ = lean_unsigned_to_nat(193u);
v___x_353_ = ((lean_object*)(l_String_fromUTF8_x21___closed__2));
v___x_354_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_355_ = l_mkPanicMessageWithDecl(v___x_354_, v___x_353_, v___x_352_, v___x_351_, v___x_350_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_x21(lean_object* v_a_356_){
_start:
{
uint8_t v___x_357_; 
v___x_357_ = lean_string_validate_utf8(v_a_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
lean_dec_ref(v_a_356_);
v___x_358_ = ((lean_object*)(l_String_fromUTF8_x21___closed__0));
v___x_359_ = lean_obj_once(&l_String_fromUTF8_x21___closed__4, &l_String_fromUTF8_x21___closed__4_once, _init_l_String_fromUTF8_x21___closed__4);
v___x_360_ = l_panic___redArg(v___x_358_, v___x_359_);
return v___x_360_;
}
else
{
lean_object* v___x_361_; 
v___x_361_ = lean_string_from_utf8_unchecked(v_a_356_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l_String_Internal_toArray(lean_object* v_b_362_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v_val_367_; 
v___x_363_ = lean_string_to_utf8(v_b_362_);
v___x_364_ = lean_unsigned_to_nat(0u);
v___x_365_ = ((lean_object*)(l_ByteArray_utf8Decode_x3f___closed__0));
v___x_366_ = l_ByteArray_utf8Decode_x3f_go___redArg(v___x_363_, v___x_364_, v___x_365_);
lean_dec_ref(v___x_363_);
v_val_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_val_367_);
lean_dec(v___x_366_);
return v_val_367_;
}
}
LEAN_EXPORT lean_object* l_String_toList___boxed(lean_object* v_s_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = lean_string_data(v_s_369_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_String_data___boxed(lean_object* v_b_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = lean_string_data(v_b_372_);
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
lean_object* v___x_434_; uint8_t v___x_435_; uint8_t v___x_436_; 
lean_dec(v___x_431_);
v___x_434_ = lean_nat_add(v_startInclusive_429_, v_p_427_);
v___x_435_ = lean_string_get_byte_fast(v_str_428_, v___x_434_);
v___x_436_ = l_UInt8_instDecidableIsUTF8FirstByte___aux__1(v___x_435_);
return v___x_436_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValidForSlice___boxed(lean_object* v_s_437_, lean_object* v_p_438_){
_start:
{
uint8_t v_res_439_; lean_object* v_r_440_; 
v_res_439_ = l_String_Pos_Raw_isValidForSlice(v_s_437_, v_p_438_);
lean_dec(v_p_438_);
lean_dec_ref(v_s_437_);
v_r_440_ = lean_box(v_res_439_);
return v_r_440_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsValidForSlice(lean_object* v_s_441_, lean_object* v_p_442_){
_start:
{
uint8_t v___x_443_; 
v___x_443_ = l_String_Pos_Raw_isValidForSlice(v_s_441_, v_p_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsValidForSlice___boxed(lean_object* v_s_444_, lean_object* v_p_445_){
_start:
{
uint8_t v_res_446_; lean_object* v_r_447_; 
v_res_446_ = l_String_instDecidableIsValidForSlice(v_s_444_, v_p_445_);
lean_dec(v_p_445_);
lean_dec_ref(v_s_444_);
v_r_447_ = lean_box(v_res_446_);
return v_r_447_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str(lean_object* v_s_448_, lean_object* v_pos_449_){
_start:
{
lean_object* v_startInclusive_450_; lean_object* v___x_451_; 
v_startInclusive_450_ = lean_ctor_get(v_s_448_, 1);
v___x_451_ = lean_nat_add(v_startInclusive_450_, v_pos_449_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str___boxed(lean_object* v_s_452_, lean_object* v_pos_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_String_Slice_Pos_str(v_s_452_, v_pos_453_);
lean_dec(v_pos_453_);
lean_dec_ref(v_s_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg(lean_object* v_s_455_, lean_object* v_pos_456_){
_start:
{
lean_object* v_startInclusive_457_; lean_object* v___x_458_; 
v_startInclusive_457_ = lean_ctor_get(v_s_455_, 1);
v___x_458_ = lean_nat_sub(v_pos_456_, v_startInclusive_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg___boxed(lean_object* v_s_459_, lean_object* v_pos_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_String_Slice_Pos_ofStr___redArg(v_s_459_, v_pos_460_);
lean_dec(v_pos_460_);
lean_dec_ref(v_s_459_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr(lean_object* v_s_462_, lean_object* v_pos_463_, lean_object* v_h_u2081_464_, lean_object* v_h_u2082_465_){
_start:
{
lean_object* v_startInclusive_466_; lean_object* v___x_467_; 
v_startInclusive_466_ = lean_ctor_get(v_s_462_, 1);
v___x_467_ = lean_nat_sub(v_pos_463_, v_startInclusive_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___boxed(lean_object* v_s_468_, lean_object* v_pos_469_, lean_object* v_h_u2081_470_, lean_object* v_h_u2082_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_String_Slice_Pos_ofStr(v_s_468_, v_pos_469_, v_h_u2081_470_, v_h_u2082_471_);
lean_dec(v_pos_469_);
lean_dec_ref(v_s_468_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom(lean_object* v_s_473_, lean_object* v_pos_474_){
_start:
{
lean_object* v_str_475_; lean_object* v_startInclusive_476_; lean_object* v_endExclusive_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_485_; 
v_str_475_ = lean_ctor_get(v_s_473_, 0);
v_startInclusive_476_ = lean_ctor_get(v_s_473_, 1);
v_endExclusive_477_ = lean_ctor_get(v_s_473_, 2);
v_isSharedCheck_485_ = !lean_is_exclusive(v_s_473_);
if (v_isSharedCheck_485_ == 0)
{
v___x_479_ = v_s_473_;
v_isShared_480_ = v_isSharedCheck_485_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_endExclusive_477_);
lean_inc(v_startInclusive_476_);
lean_inc(v_str_475_);
lean_dec(v_s_473_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_485_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_481_ = lean_nat_add(v_startInclusive_476_, v_pos_474_);
lean_dec(v_startInclusive_476_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 1, v___x_481_);
v___x_483_ = v___x_479_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_str_475_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v___x_481_);
lean_ctor_set(v_reuseFailAlloc_484_, 2, v_endExclusive_477_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom___boxed(lean_object* v_s_486_, lean_object* v_pos_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_String_Slice_sliceFrom(v_s_486_, v_pos_487_);
lean_dec(v_pos_487_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStart(lean_object* v_s_489_, lean_object* v_pos_490_){
_start:
{
lean_object* v_str_491_; lean_object* v_startInclusive_492_; lean_object* v_endExclusive_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_501_; 
v_str_491_ = lean_ctor_get(v_s_489_, 0);
v_startInclusive_492_ = lean_ctor_get(v_s_489_, 1);
v_endExclusive_493_ = lean_ctor_get(v_s_489_, 2);
v_isSharedCheck_501_ = !lean_is_exclusive(v_s_489_);
if (v_isSharedCheck_501_ == 0)
{
v___x_495_ = v_s_489_;
v_isShared_496_ = v_isSharedCheck_501_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_endExclusive_493_);
lean_inc(v_startInclusive_492_);
lean_inc(v_str_491_);
lean_dec(v_s_489_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_501_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_497_ = lean_nat_add(v_startInclusive_492_, v_pos_490_);
lean_dec(v_startInclusive_492_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 1, v___x_497_);
v___x_499_ = v___x_495_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_str_491_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_500_, 2, v_endExclusive_493_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStart___boxed(lean_object* v_s_502_, lean_object* v_pos_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_String_Slice_replaceStart(v_s_502_, v_pos_503_);
lean_dec(v_pos_503_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceTo(lean_object* v_s_505_, lean_object* v_pos_506_){
_start:
{
lean_object* v_str_507_; lean_object* v_startInclusive_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_516_; 
v_str_507_ = lean_ctor_get(v_s_505_, 0);
v_startInclusive_508_ = lean_ctor_get(v_s_505_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v_s_505_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; 
v_unused_517_ = lean_ctor_get(v_s_505_, 2);
lean_dec(v_unused_517_);
v___x_510_ = v_s_505_;
v_isShared_511_ = v_isSharedCheck_516_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_startInclusive_508_);
lean_inc(v_str_507_);
lean_dec(v_s_505_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_516_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_512_ = lean_nat_add(v_startInclusive_508_, v_pos_506_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 2, v___x_512_);
v___x_514_ = v___x_510_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_str_507_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_startInclusive_508_);
lean_ctor_set(v_reuseFailAlloc_515_, 2, v___x_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceTo___boxed(lean_object* v_s_518_, lean_object* v_pos_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_String_Slice_sliceTo(v_s_518_, v_pos_519_);
lean_dec(v_pos_519_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd(lean_object* v_s_521_, lean_object* v_pos_522_){
_start:
{
lean_object* v_str_523_; lean_object* v_startInclusive_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_532_; 
v_str_523_ = lean_ctor_get(v_s_521_, 0);
v_startInclusive_524_ = lean_ctor_get(v_s_521_, 1);
v_isSharedCheck_532_ = !lean_is_exclusive(v_s_521_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; 
v_unused_533_ = lean_ctor_get(v_s_521_, 2);
lean_dec(v_unused_533_);
v___x_526_ = v_s_521_;
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_startInclusive_524_);
lean_inc(v_str_523_);
lean_dec(v_s_521_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_528_ = lean_nat_add(v_startInclusive_524_, v_pos_522_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 2, v___x_528_);
v___x_530_ = v___x_526_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_str_523_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_startInclusive_524_);
lean_ctor_set(v_reuseFailAlloc_531_, 2, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd___boxed(lean_object* v_s_534_, lean_object* v_pos_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_String_Slice_replaceEnd(v_s_534_, v_pos_535_);
lean_dec(v_pos_535_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg(lean_object* v_s_537_, lean_object* v_newStart_538_, lean_object* v_newEnd_539_){
_start:
{
lean_object* v_str_540_; lean_object* v_startInclusive_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_550_; 
v_str_540_ = lean_ctor_get(v_s_537_, 0);
v_startInclusive_541_ = lean_ctor_get(v_s_537_, 1);
v_isSharedCheck_550_ = !lean_is_exclusive(v_s_537_);
if (v_isSharedCheck_550_ == 0)
{
lean_object* v_unused_551_; 
v_unused_551_ = lean_ctor_get(v_s_537_, 2);
lean_dec(v_unused_551_);
v___x_543_ = v_s_537_;
v_isShared_544_ = v_isSharedCheck_550_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_startInclusive_541_);
lean_inc(v_str_540_);
lean_dec(v_s_537_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_550_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_545_ = lean_nat_add(v_startInclusive_541_, v_newStart_538_);
v___x_546_ = lean_nat_add(v_startInclusive_541_, v_newEnd_539_);
lean_dec(v_startInclusive_541_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 2, v___x_546_);
lean_ctor_set(v___x_543_, 1, v___x_545_);
v___x_548_ = v___x_543_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_str_540_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v___x_545_);
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
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg___boxed(lean_object* v_s_552_, lean_object* v_newStart_553_, lean_object* v_newEnd_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_String_Slice_slice___redArg(v_s_552_, v_newStart_553_, v_newEnd_554_);
lean_dec(v_newEnd_554_);
lean_dec(v_newStart_553_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice(lean_object* v_s_556_, lean_object* v_newStart_557_, lean_object* v_newEnd_558_, lean_object* v_h_559_){
_start:
{
lean_object* v_str_560_; lean_object* v_startInclusive_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_570_; 
v_str_560_ = lean_ctor_get(v_s_556_, 0);
v_startInclusive_561_ = lean_ctor_get(v_s_556_, 1);
v_isSharedCheck_570_ = !lean_is_exclusive(v_s_556_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; 
v_unused_571_ = lean_ctor_get(v_s_556_, 2);
lean_dec(v_unused_571_);
v___x_563_ = v_s_556_;
v_isShared_564_ = v_isSharedCheck_570_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_startInclusive_561_);
lean_inc(v_str_560_);
lean_dec(v_s_556_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_570_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_565_ = lean_nat_add(v_startInclusive_561_, v_newStart_557_);
v___x_566_ = lean_nat_add(v_startInclusive_561_, v_newEnd_558_);
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
LEAN_EXPORT lean_object* l_String_Slice_slice___boxed(lean_object* v_s_572_, lean_object* v_newStart_573_, lean_object* v_newEnd_574_, lean_object* v_h_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_String_Slice_slice(v_s_572_, v_newStart_573_, v_newEnd_574_, v_h_575_);
lean_dec(v_newEnd_574_);
lean_dec(v_newStart_573_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg(lean_object* v_s_577_, lean_object* v_newStart_578_, lean_object* v_newEnd_579_){
_start:
{
lean_object* v_str_580_; lean_object* v_startInclusive_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_590_; 
v_str_580_ = lean_ctor_get(v_s_577_, 0);
v_startInclusive_581_ = lean_ctor_get(v_s_577_, 1);
v_isSharedCheck_590_ = !lean_is_exclusive(v_s_577_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; 
v_unused_591_ = lean_ctor_get(v_s_577_, 2);
lean_dec(v_unused_591_);
v___x_583_ = v_s_577_;
v_isShared_584_ = v_isSharedCheck_590_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_startInclusive_581_);
lean_inc(v_str_580_);
lean_dec(v_s_577_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_590_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_585_ = lean_nat_add(v_startInclusive_581_, v_newStart_578_);
v___x_586_ = lean_nat_add(v_startInclusive_581_, v_newEnd_579_);
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
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg___boxed(lean_object* v_s_592_, lean_object* v_newStart_593_, lean_object* v_newEnd_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_String_Slice_replaceStartEnd___redArg(v_s_592_, v_newStart_593_, v_newEnd_594_);
lean_dec(v_newEnd_594_);
lean_dec(v_newStart_593_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd(lean_object* v_s_596_, lean_object* v_newStart_597_, lean_object* v_newEnd_598_, lean_object* v_h_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_String_Slice_replaceStartEnd___redArg(v_s_596_, v_newStart_597_, v_newEnd_598_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___boxed(lean_object* v_s_601_, lean_object* v_newStart_602_, lean_object* v_newEnd_603_, lean_object* v_h_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_String_Slice_replaceStartEnd(v_s_601_, v_newStart_602_, v_newEnd_603_, v_h_604_);
lean_dec(v_newEnd_603_);
lean_dec(v_newStart_602_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f(lean_object* v_s_606_, lean_object* v_newStart_607_, lean_object* v_newEnd_608_){
_start:
{
uint8_t v___x_609_; 
v___x_609_ = lean_nat_dec_le(v_newStart_607_, v_newEnd_608_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; 
lean_dec_ref(v_s_606_);
v___x_610_ = lean_box(0);
return v___x_610_;
}
else
{
lean_object* v_str_611_; lean_object* v_startInclusive_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_622_; 
v_str_611_ = lean_ctor_get(v_s_606_, 0);
v_startInclusive_612_ = lean_ctor_get(v_s_606_, 1);
v_isSharedCheck_622_ = !lean_is_exclusive(v_s_606_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; 
v_unused_623_ = lean_ctor_get(v_s_606_, 2);
lean_dec(v_unused_623_);
v___x_614_ = v_s_606_;
v_isShared_615_ = v_isSharedCheck_622_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_startInclusive_612_);
lean_inc(v_str_611_);
lean_dec(v_s_606_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_622_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_616_ = lean_nat_add(v_startInclusive_612_, v_newStart_607_);
v___x_617_ = lean_nat_add(v_startInclusive_612_, v_newEnd_608_);
lean_dec(v_startInclusive_612_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 2, v___x_617_);
lean_ctor_set(v___x_614_, 1, v___x_616_);
v___x_619_ = v___x_614_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_str_611_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v___x_616_);
lean_ctor_set(v_reuseFailAlloc_621_, 2, v___x_617_);
v___x_619_ = v_reuseFailAlloc_621_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; 
v___x_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
return v___x_620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f___boxed(lean_object* v_s_624_, lean_object* v_newStart_625_, lean_object* v_newEnd_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_String_Slice_slice_x3f(v_s_624_, v_newStart_625_, v_newEnd_626_);
lean_dec(v_newEnd_626_);
lean_dec(v_newStart_625_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_slice_x21_spec__0(lean_object* v_msg_628_){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = l_String_instInhabitedSlice;
v___x_630_ = lean_panic_fn_borrowed(v___x_629_, v_msg_628_);
return v___x_630_;
}
}
static lean_object* _init_l_String_Slice_slice_x21___closed__2(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_633_ = ((lean_object*)(l_String_Slice_slice_x21___closed__1));
v___x_634_ = lean_unsigned_to_nat(4u);
v___x_635_ = lean_unsigned_to_nat(1096u);
v___x_636_ = ((lean_object*)(l_String_Slice_slice_x21___closed__0));
v___x_637_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_638_ = l_mkPanicMessageWithDecl(v___x_637_, v___x_636_, v___x_635_, v___x_634_, v___x_633_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x21(lean_object* v_s_639_, lean_object* v_newStart_640_, lean_object* v_newEnd_641_){
_start:
{
uint8_t v___x_642_; 
v___x_642_ = lean_nat_dec_le(v_newStart_640_, v_newEnd_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; 
lean_dec_ref(v_s_639_);
v___x_643_ = lean_obj_once(&l_String_Slice_slice_x21___closed__2, &l_String_Slice_slice_x21___closed__2_once, _init_l_String_Slice_slice_x21___closed__2);
v___x_644_ = l_panic___at___00String_Slice_slice_x21_spec__0(v___x_643_);
return v___x_644_;
}
else
{
lean_object* v_str_645_; lean_object* v_startInclusive_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_655_; 
v_str_645_ = lean_ctor_get(v_s_639_, 0);
v_startInclusive_646_ = lean_ctor_get(v_s_639_, 1);
v_isSharedCheck_655_ = !lean_is_exclusive(v_s_639_);
if (v_isSharedCheck_655_ == 0)
{
lean_object* v_unused_656_; 
v_unused_656_ = lean_ctor_get(v_s_639_, 2);
lean_dec(v_unused_656_);
v___x_648_ = v_s_639_;
v_isShared_649_ = v_isSharedCheck_655_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_startInclusive_646_);
lean_inc(v_str_645_);
lean_dec(v_s_639_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_655_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_653_; 
v___x_650_ = lean_nat_add(v_startInclusive_646_, v_newStart_640_);
v___x_651_ = lean_nat_add(v_startInclusive_646_, v_newEnd_641_);
lean_dec(v_startInclusive_646_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 2, v___x_651_);
lean_ctor_set(v___x_648_, 1, v___x_650_);
v___x_653_ = v___x_648_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_str_645_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v___x_650_);
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
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x21___boxed(lean_object* v_s_657_, lean_object* v_newStart_658_, lean_object* v_newEnd_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_String_Slice_slice_x21(v_s_657_, v_newStart_658_, v_newEnd_659_);
lean_dec(v_newEnd_659_);
lean_dec(v_newStart_658_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21(lean_object* v_s_661_, lean_object* v_newStart_662_, lean_object* v_newEnd_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_String_Slice_slice_x21(v_s_661_, v_newStart_662_, v_newEnd_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21___boxed(lean_object* v_s_665_, lean_object* v_newStart_666_, lean_object* v_newEnd_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_String_Slice_replaceStartEnd_x21(v_s_665_, v_newStart_666_, v_newEnd_667_);
lean_dec(v_newEnd_667_);
lean_dec(v_newStart_666_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_String_decodeChar___boxed(lean_object* v_s_672_, lean_object* v_byteIdx_673_, lean_object* v_h_674_){
_start:
{
uint32_t v_res_675_; lean_object* v_r_676_; 
v_res_675_ = lean_string_utf8_get_fast(v_s_672_, v_byteIdx_673_);
lean_dec(v_byteIdx_673_);
lean_dec_ref(v_s_672_);
v_r_676_ = lean_box_uint32(v_res_675_);
return v_r_676_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get___redArg(lean_object* v_s_677_, lean_object* v_pos_678_){
_start:
{
lean_object* v_str_679_; lean_object* v_startInclusive_680_; lean_object* v___x_681_; uint32_t v___x_682_; 
v_str_679_ = lean_ctor_get(v_s_677_, 0);
v_startInclusive_680_ = lean_ctor_get(v_s_677_, 1);
v___x_681_ = lean_nat_add(v_startInclusive_680_, v_pos_678_);
v___x_682_ = lean_string_utf8_get_fast(v_str_679_, v___x_681_);
lean_dec(v___x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___redArg___boxed(lean_object* v_s_683_, lean_object* v_pos_684_){
_start:
{
uint32_t v_res_685_; lean_object* v_r_686_; 
v_res_685_ = l_String_Slice_Pos_get___redArg(v_s_683_, v_pos_684_);
lean_dec(v_pos_684_);
lean_dec_ref(v_s_683_);
v_r_686_ = lean_box_uint32(v_res_685_);
return v_r_686_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get(lean_object* v_s_687_, lean_object* v_pos_688_, lean_object* v_h_689_){
_start:
{
lean_object* v_str_690_; lean_object* v_startInclusive_691_; lean_object* v___x_692_; uint32_t v___x_693_; 
v_str_690_ = lean_ctor_get(v_s_687_, 0);
v_startInclusive_691_ = lean_ctor_get(v_s_687_, 1);
v___x_692_ = lean_nat_add(v_startInclusive_691_, v_pos_688_);
v___x_693_ = lean_string_utf8_get_fast(v_str_690_, v___x_692_);
lean_dec(v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___boxed(lean_object* v_s_694_, lean_object* v_pos_695_, lean_object* v_h_696_){
_start:
{
uint32_t v_res_697_; lean_object* v_r_698_; 
v_res_697_ = l_String_Slice_Pos_get(v_s_694_, v_pos_695_, v_h_696_);
lean_dec(v_pos_695_);
lean_dec_ref(v_s_694_);
v_r_698_ = lean_box_uint32(v_res_697_);
return v_r_698_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f(lean_object* v_s_699_, lean_object* v_pos_700_){
_start:
{
lean_object* v_str_701_; lean_object* v_startInclusive_702_; lean_object* v_endExclusive_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v_str_701_ = lean_ctor_get(v_s_699_, 0);
v_startInclusive_702_ = lean_ctor_get(v_s_699_, 1);
v_endExclusive_703_ = lean_ctor_get(v_s_699_, 2);
v___x_704_ = lean_nat_sub(v_endExclusive_703_, v_startInclusive_702_);
v___x_705_ = lean_nat_dec_eq(v_pos_700_, v___x_704_);
lean_dec(v___x_704_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; uint32_t v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_706_ = lean_nat_add(v_startInclusive_702_, v_pos_700_);
v___x_707_ = lean_string_utf8_get_fast(v_str_701_, v___x_706_);
lean_dec(v___x_706_);
v___x_708_ = lean_box_uint32(v___x_707_);
v___x_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
return v___x_709_;
}
else
{
lean_object* v___x_710_; 
v___x_710_ = lean_box(0);
return v___x_710_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f___boxed(lean_object* v_s_711_, lean_object* v_pos_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_String_Slice_Pos_get_x3f(v_s_711_, v_pos_712_);
lean_dec(v_pos_712_);
lean_dec_ref(v_s_711_);
return v_res_713_;
}
}
static lean_object* _init_l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1(void){
_start:
{
uint32_t v___x_714_; lean_object* v___x_715_; 
v___x_714_ = 65;
v___x_715_ = lean_box_uint32(v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT uint32_t l_panic___at___00String_Slice_Pos_get_x21_spec__0(lean_object* v_msg_716_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; uint32_t v___x_719_; 
v___x_717_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1;
v___x_718_ = lean_panic_fn_borrowed(v___x_717_, v_msg_716_);
v___x_719_ = lean_unbox_uint32(v___x_718_);
lean_dec(v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed(lean_object* v_msg_720_){
_start:
{
uint32_t v_res_721_; lean_object* v_r_722_; 
v_res_721_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v_msg_720_);
v_r_722_ = lean_box_uint32(v_res_721_);
return v_r_722_;
}
}
static lean_object* _init_l_String_Slice_Pos_get_x21___closed__2(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_725_ = ((lean_object*)(l_String_Slice_Pos_get_x21___closed__1));
v___x_726_ = lean_unsigned_to_nat(29u);
v___x_727_ = lean_unsigned_to_nat(1181u);
v___x_728_ = ((lean_object*)(l_String_Slice_Pos_get_x21___closed__0));
v___x_729_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_730_ = l_mkPanicMessageWithDecl(v___x_729_, v___x_728_, v___x_727_, v___x_726_, v___x_725_);
return v___x_730_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get_x21(lean_object* v_s_731_, lean_object* v_pos_732_){
_start:
{
lean_object* v_str_733_; lean_object* v_startInclusive_734_; lean_object* v_endExclusive_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v_str_733_ = lean_ctor_get(v_s_731_, 0);
v_startInclusive_734_ = lean_ctor_get(v_s_731_, 1);
v_endExclusive_735_ = lean_ctor_get(v_s_731_, 2);
v___x_736_ = lean_nat_sub(v_endExclusive_735_, v_startInclusive_734_);
v___x_737_ = lean_nat_dec_eq(v_pos_732_, v___x_736_);
lean_dec(v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; uint32_t v___x_739_; 
v___x_738_ = lean_nat_add(v_startInclusive_734_, v_pos_732_);
v___x_739_ = lean_string_utf8_get_fast(v_str_733_, v___x_738_);
lean_dec(v___x_738_);
return v___x_739_;
}
else
{
lean_object* v___x_740_; uint32_t v___x_741_; 
v___x_740_ = lean_obj_once(&l_String_Slice_Pos_get_x21___closed__2, &l_String_Slice_Pos_get_x21___closed__2_once, _init_l_String_Slice_Pos_get_x21___closed__2);
v___x_741_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v___x_740_);
return v___x_741_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x21___boxed(lean_object* v_s_742_, lean_object* v_pos_743_){
_start:
{
uint32_t v_res_744_; lean_object* v_r_745_; 
v_res_744_ = l_String_Slice_Pos_get_x21(v_s_742_, v_pos_743_);
lean_dec(v_pos_743_);
lean_dec_ref(v_s_742_);
v_r_745_ = lean_box_uint32(v_res_744_);
return v_r_745_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg(lean_object* v_pos_746_){
_start:
{
lean_inc(v_pos_746_);
return v_pos_746_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg___boxed(lean_object* v_pos_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_String_Pos_toSlice___redArg(v_pos_747_);
lean_dec(v_pos_747_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice(lean_object* v_s_749_, lean_object* v_pos_750_){
_start:
{
lean_inc(v_pos_750_);
return v_pos_750_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___boxed(lean_object* v_s_751_, lean_object* v_pos_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_String_Pos_toSlice(v_s_751_, v_pos_752_);
lean_dec(v_pos_752_);
lean_dec_ref(v_s_751_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg(lean_object* v_pos_754_){
_start:
{
lean_inc(v_pos_754_);
return v_pos_754_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg___boxed(lean_object* v_pos_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_String_Pos_ofToSlice___redArg(v_pos_755_);
lean_dec(v_pos_755_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice(lean_object* v_s_757_, lean_object* v_pos_758_){
_start:
{
lean_inc(v_pos_758_);
return v_pos_758_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___boxed(lean_object* v_s_759_, lean_object* v_pos_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_String_Pos_ofToSlice(v_s_759_, v_pos_760_);
lean_dec(v_pos_760_);
lean_dec_ref(v_s_759_);
return v_res_761_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get___redArg(lean_object* v_s_762_, lean_object* v_pos_763_){
_start:
{
uint32_t v___x_764_; 
v___x_764_ = lean_string_utf8_get_fast(v_s_762_, v_pos_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get___redArg___boxed(lean_object* v_s_765_, lean_object* v_pos_766_){
_start:
{
uint32_t v_res_767_; lean_object* v_r_768_; 
v_res_767_ = l_String_Pos_get___redArg(v_s_765_, v_pos_766_);
lean_dec(v_pos_766_);
lean_dec_ref(v_s_765_);
v_r_768_ = lean_box_uint32(v_res_767_);
return v_r_768_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get(lean_object* v_s_769_, lean_object* v_pos_770_, lean_object* v_h_771_){
_start:
{
uint32_t v___x_772_; 
v___x_772_ = lean_string_utf8_get_fast(v_s_769_, v_pos_770_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get___boxed(lean_object* v_s_773_, lean_object* v_pos_774_, lean_object* v_h_775_){
_start:
{
uint32_t v_res_776_; lean_object* v_r_777_; 
v_res_776_ = l_String_Pos_get(v_s_773_, v_pos_774_, v_h_775_);
lean_dec(v_pos_774_);
lean_dec_ref(v_s_773_);
v_r_777_ = lean_box_uint32(v_res_776_);
return v_r_777_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x3f(lean_object* v_s_778_, lean_object* v_pos_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_780_ = lean_unsigned_to_nat(0u);
v___x_781_ = lean_string_utf8_byte_size(v_s_778_);
v___x_782_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_782_, 0, v_s_778_);
lean_ctor_set(v___x_782_, 1, v___x_780_);
lean_ctor_set(v___x_782_, 2, v___x_781_);
v___x_783_ = l_String_Slice_Pos_get_x3f(v___x_782_, v_pos_779_);
lean_dec_ref_known(v___x_782_, 3);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x3f___boxed(lean_object* v_s_784_, lean_object* v_pos_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_String_Pos_get_x3f(v_s_784_, v_pos_785_);
lean_dec(v_pos_785_);
return v_res_786_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get_x21(lean_object* v_s_787_, lean_object* v_pos_788_){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; uint32_t v___x_792_; 
v___x_789_ = lean_unsigned_to_nat(0u);
v___x_790_ = lean_string_utf8_byte_size(v_s_787_);
v___x_791_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_791_, 0, v_s_787_);
lean_ctor_set(v___x_791_, 1, v___x_789_);
lean_ctor_set(v___x_791_, 2, v___x_790_);
v___x_792_ = l_String_Slice_Pos_get_x21(v___x_791_, v_pos_788_);
lean_dec_ref_known(v___x_791_, 3);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x21___boxed(lean_object* v_s_793_, lean_object* v_pos_794_){
_start:
{
uint32_t v_res_795_; lean_object* v_r_796_; 
v_res_795_ = l_String_Pos_get_x21(v_s_793_, v_pos_794_);
lean_dec(v_pos_794_);
v_r_796_ = lean_box_uint32(v_res_795_);
return v_r_796_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_byte___redArg(lean_object* v_s_797_, lean_object* v_pos_798_){
_start:
{
uint8_t v___x_799_; 
v___x_799_ = lean_string_get_byte_fast(v_s_797_, v_pos_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_byte___redArg___boxed(lean_object* v_s_800_, lean_object* v_pos_801_){
_start:
{
uint8_t v_res_802_; lean_object* v_r_803_; 
v_res_802_ = l_String_Pos_byte___redArg(v_s_800_, v_pos_801_);
lean_dec_ref(v_s_800_);
v_r_803_ = lean_box(v_res_802_);
return v_r_803_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_byte(lean_object* v_s_804_, lean_object* v_pos_805_, lean_object* v_h_806_){
_start:
{
uint8_t v___x_807_; 
v___x_807_ = lean_string_get_byte_fast(v_s_804_, v_pos_805_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_byte___boxed(lean_object* v_s_808_, lean_object* v_pos_809_, lean_object* v_h_810_){
_start:
{
uint8_t v_res_811_; lean_object* v_r_812_; 
v_res_811_ = l_String_Pos_byte(v_s_808_, v_pos_809_, v_h_810_);
lean_dec_ref(v_s_808_);
v_r_812_ = lean_box(v_res_811_);
return v_r_812_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg(lean_object* v_pos_813_){
_start:
{
lean_inc(v_pos_813_);
return v_pos_813_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg___boxed(lean_object* v_pos_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_String_Pos_ofCopy___redArg(v_pos_814_);
lean_dec(v_pos_814_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy(lean_object* v_s_816_, lean_object* v_pos_817_){
_start:
{
lean_inc(v_pos_817_);
return v_pos_817_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___boxed(lean_object* v_s_818_, lean_object* v_pos_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_String_Pos_ofCopy(v_s_818_, v_pos_819_);
lean_dec(v_pos_819_);
lean_dec_ref(v_s_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg(lean_object* v_pos_821_){
_start:
{
lean_inc(v_pos_821_);
return v_pos_821_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg___boxed(lean_object* v_pos_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_String_Slice_Pos_copy___redArg(v_pos_822_);
lean_dec(v_pos_822_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy(lean_object* v_s_824_, lean_object* v_pos_825_){
_start:
{
lean_inc(v_pos_825_);
return v_pos_825_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___boxed(lean_object* v_s_826_, lean_object* v_pos_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_String_Slice_Pos_copy(v_s_826_, v_pos_827_);
lean_dec(v_pos_827_);
lean_dec_ref(v_s_826_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg(lean_object* v_pos_829_){
_start:
{
lean_inc(v_pos_829_);
return v_pos_829_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg___boxed(lean_object* v_pos_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_String_Slice_Pos_toCopy___redArg(v_pos_830_);
lean_dec(v_pos_830_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy(lean_object* v_s_832_, lean_object* v_pos_833_){
_start:
{
lean_inc(v_pos_833_);
return v_pos_833_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___boxed(lean_object* v_s_834_, lean_object* v_pos_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_String_Slice_Pos_toCopy(v_s_834_, v_pos_835_);
lean_dec(v_pos_835_);
lean_dec_ref(v_s_834_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg(lean_object* v_p_u2080_837_, lean_object* v_pos_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = lean_nat_add(v_p_u2080_837_, v_pos_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg___boxed(lean_object* v_p_u2080_840_, lean_object* v_pos_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_String_Slice_Pos_ofSliceFrom___redArg(v_p_u2080_840_, v_pos_841_);
lean_dec(v_pos_841_);
lean_dec(v_p_u2080_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom(lean_object* v_s_843_, lean_object* v_p_u2080_844_, lean_object* v_pos_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = lean_nat_add(v_p_u2080_844_, v_pos_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___boxed(lean_object* v_s_847_, lean_object* v_p_u2080_848_, lean_object* v_pos_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_String_Slice_Pos_ofSliceFrom(v_s_847_, v_p_u2080_848_, v_pos_849_);
lean_dec(v_pos_849_);
lean_dec(v_p_u2080_848_);
lean_dec_ref(v_s_847_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg(lean_object* v_p_u2080_851_, lean_object* v_pos_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = lean_nat_add(v_p_u2080_851_, v_pos_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg___boxed(lean_object* v_p_u2080_854_, lean_object* v_pos_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_String_Slice_Pos_ofReplaceStart___redArg(v_p_u2080_854_, v_pos_855_);
lean_dec(v_pos_855_);
lean_dec(v_p_u2080_854_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart(lean_object* v_s_857_, lean_object* v_p_u2080_858_, lean_object* v_pos_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = lean_nat_add(v_p_u2080_858_, v_pos_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___boxed(lean_object* v_s_861_, lean_object* v_p_u2080_862_, lean_object* v_pos_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_String_Slice_Pos_ofReplaceStart(v_s_861_, v_p_u2080_862_, v_pos_863_);
lean_dec(v_pos_863_);
lean_dec(v_p_u2080_862_);
lean_dec_ref(v_s_861_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg(lean_object* v_p_u2080_865_, lean_object* v_pos_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = lean_nat_sub(v_pos_866_, v_p_u2080_865_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg___boxed(lean_object* v_p_u2080_868_, lean_object* v_pos_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_String_Slice_Pos_sliceFrom___redArg(v_p_u2080_868_, v_pos_869_);
lean_dec(v_pos_869_);
lean_dec(v_p_u2080_868_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom(lean_object* v_s_871_, lean_object* v_p_u2080_872_, lean_object* v_pos_873_, lean_object* v_h_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = lean_nat_sub(v_pos_873_, v_p_u2080_872_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___boxed(lean_object* v_s_876_, lean_object* v_p_u2080_877_, lean_object* v_pos_878_, lean_object* v_h_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_String_Slice_Pos_sliceFrom(v_s_876_, v_p_u2080_877_, v_pos_878_, v_h_879_);
lean_dec(v_pos_878_);
lean_dec(v_p_u2080_877_);
lean_dec_ref(v_s_876_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg(lean_object* v_p_u2080_881_, lean_object* v_pos_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = lean_nat_sub(v_pos_882_, v_p_u2080_881_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg___boxed(lean_object* v_p_u2080_884_, lean_object* v_pos_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_String_Slice_Pos_toReplaceStart___redArg(v_p_u2080_884_, v_pos_885_);
lean_dec(v_pos_885_);
lean_dec(v_p_u2080_884_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart(lean_object* v_s_887_, lean_object* v_p_u2080_888_, lean_object* v_pos_889_, lean_object* v_h_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = lean_nat_sub(v_pos_889_, v_p_u2080_888_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___boxed(lean_object* v_s_892_, lean_object* v_p_u2080_893_, lean_object* v_pos_894_, lean_object* v_h_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_String_Slice_Pos_toReplaceStart(v_s_892_, v_p_u2080_893_, v_pos_894_, v_h_895_);
lean_dec(v_pos_894_);
lean_dec(v_p_u2080_893_);
lean_dec_ref(v_s_892_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg(lean_object* v_pos_897_){
_start:
{
lean_inc(v_pos_897_);
return v_pos_897_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg___boxed(lean_object* v_pos_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_String_Slice_Pos_ofSliceTo___redArg(v_pos_898_);
lean_dec(v_pos_898_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo(lean_object* v_s_900_, lean_object* v_p_u2080_901_, lean_object* v_pos_902_){
_start:
{
lean_inc(v_pos_902_);
return v_pos_902_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___boxed(lean_object* v_s_903_, lean_object* v_p_u2080_904_, lean_object* v_pos_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_String_Slice_Pos_ofSliceTo(v_s_903_, v_p_u2080_904_, v_pos_905_);
lean_dec(v_pos_905_);
lean_dec(v_p_u2080_904_);
lean_dec_ref(v_s_903_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg(lean_object* v_pos_907_){
_start:
{
lean_inc(v_pos_907_);
return v_pos_907_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg___boxed(lean_object* v_pos_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_String_Slice_Pos_ofReplaceEnd___redArg(v_pos_908_);
lean_dec(v_pos_908_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd(lean_object* v_s_910_, lean_object* v_p_u2080_911_, lean_object* v_pos_912_){
_start:
{
lean_inc(v_pos_912_);
return v_pos_912_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___boxed(lean_object* v_s_913_, lean_object* v_p_u2080_914_, lean_object* v_pos_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_String_Slice_Pos_ofReplaceEnd(v_s_913_, v_p_u2080_914_, v_pos_915_);
lean_dec(v_pos_915_);
lean_dec(v_p_u2080_914_);
lean_dec_ref(v_s_913_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg(lean_object* v_pos_917_){
_start:
{
lean_inc(v_pos_917_);
return v_pos_917_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg___boxed(lean_object* v_pos_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_String_Slice_Pos_sliceTo___redArg(v_pos_918_);
lean_dec(v_pos_918_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo(lean_object* v_s_920_, lean_object* v_p_u2080_921_, lean_object* v_pos_922_, lean_object* v_h_923_){
_start:
{
lean_inc(v_pos_922_);
return v_pos_922_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___boxed(lean_object* v_s_924_, lean_object* v_p_u2080_925_, lean_object* v_pos_926_, lean_object* v_h_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_String_Slice_Pos_sliceTo(v_s_924_, v_p_u2080_925_, v_pos_926_, v_h_927_);
lean_dec(v_pos_926_);
lean_dec(v_p_u2080_925_);
lean_dec_ref(v_s_924_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg(lean_object* v_pos_929_){
_start:
{
lean_inc(v_pos_929_);
return v_pos_929_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg___boxed(lean_object* v_pos_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_String_Slice_Pos_toReplaceEnd___redArg(v_pos_930_);
lean_dec(v_pos_930_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd(lean_object* v_s_932_, lean_object* v_p_u2080_933_, lean_object* v_pos_934_, lean_object* v_h_935_){
_start:
{
lean_inc(v_pos_934_);
return v_pos_934_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___boxed(lean_object* v_s_936_, lean_object* v_p_u2080_937_, lean_object* v_pos_938_, lean_object* v_h_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_String_Slice_Pos_toReplaceEnd(v_s_936_, v_p_u2080_937_, v_pos_938_, v_h_939_);
lean_dec(v_pos_938_);
lean_dec(v_p_u2080_937_);
lean_dec_ref(v_s_936_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg(lean_object* v_s_941_, lean_object* v_pos_942_){
_start:
{
lean_object* v_str_943_; lean_object* v_startInclusive_944_; lean_object* v___x_945_; uint8_t v___x_946_; uint8_t v___x_947_; uint8_t v___x_948_; uint8_t v___x_949_; uint8_t v___x_950_; 
v_str_943_ = lean_ctor_get(v_s_941_, 0);
v_startInclusive_944_ = lean_ctor_get(v_s_941_, 1);
v___x_945_ = lean_nat_add(v_startInclusive_944_, v_pos_942_);
v___x_946_ = lean_string_get_byte_fast(v_str_943_, v___x_945_);
v___x_947_ = 128;
v___x_948_ = lean_uint8_land(v___x_946_, v___x_947_);
v___x_949_ = 0;
v___x_950_ = lean_uint8_dec_eq(v___x_948_, v___x_949_);
if (v___x_950_ == 0)
{
uint8_t v___x_951_; uint8_t v___x_952_; uint8_t v___x_953_; uint8_t v___x_954_; 
v___x_951_ = 224;
v___x_952_ = lean_uint8_land(v___x_946_, v___x_951_);
v___x_953_ = 192;
v___x_954_ = lean_uint8_dec_eq(v___x_952_, v___x_953_);
if (v___x_954_ == 0)
{
uint8_t v___x_955_; uint8_t v___x_956_; uint8_t v___x_957_; 
v___x_955_ = 240;
v___x_956_ = lean_uint8_land(v___x_946_, v___x_955_);
v___x_957_ = lean_uint8_dec_eq(v___x_956_, v___x_951_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_unsigned_to_nat(4u);
v___x_959_ = lean_nat_add(v_pos_942_, v___x_958_);
return v___x_959_;
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_unsigned_to_nat(3u);
v___x_961_ = lean_nat_add(v_pos_942_, v___x_960_);
return v___x_961_;
}
}
else
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = lean_unsigned_to_nat(2u);
v___x_963_ = lean_nat_add(v_pos_942_, v___x_962_);
return v___x_963_;
}
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = lean_unsigned_to_nat(1u);
v___x_965_ = lean_nat_add(v_pos_942_, v___x_964_);
return v___x_965_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg___boxed(lean_object* v_s_966_, lean_object* v_pos_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_String_Slice_Pos_next___redArg(v_s_966_, v_pos_967_);
lean_dec(v_pos_967_);
lean_dec_ref(v_s_966_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next(lean_object* v_s_969_, lean_object* v_pos_970_, lean_object* v_h_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_String_Slice_Pos_next___redArg(v_s_969_, v_pos_970_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___boxed(lean_object* v_s_973_, lean_object* v_pos_974_, lean_object* v_h_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_String_Slice_Pos_next(v_s_973_, v_pos_974_, v_h_975_);
lean_dec(v_pos_974_);
lean_dec_ref(v_s_973_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f(lean_object* v_s_977_, lean_object* v_pos_978_){
_start:
{
lean_object* v_startInclusive_979_; lean_object* v_endExclusive_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v_startInclusive_979_ = lean_ctor_get(v_s_977_, 1);
v_endExclusive_980_ = lean_ctor_get(v_s_977_, 2);
v___x_981_ = lean_nat_sub(v_endExclusive_980_, v_startInclusive_979_);
v___x_982_ = lean_nat_dec_eq(v_pos_978_, v___x_981_);
lean_dec(v___x_981_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = l_String_Slice_Pos_next___redArg(v_s_977_, v_pos_978_);
v___x_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
else
{
lean_object* v___x_985_; 
v___x_985_ = lean_box(0);
return v___x_985_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f___boxed(lean_object* v_s_986_, lean_object* v_pos_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_String_Slice_Pos_next_x3f(v_s_986_, v_pos_987_);
lean_dec(v_pos_987_);
lean_dec_ref(v_s_986_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(lean_object* v_msg_989_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_unsigned_to_nat(0u);
v___x_991_ = lean_panic_fn_borrowed(v___x_990_, v_msg_989_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0(lean_object* v_s_992_, lean_object* v_msg_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v_msg_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___boxed(lean_object* v_s_995_, lean_object* v_msg_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0(v_s_995_, v_msg_996_);
lean_dec_ref(v_s_995_);
return v_res_997_;
}
}
static lean_object* _init_l_String_Slice_Pos_next_x21___closed__2(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1000_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__1));
v___x_1001_ = lean_unsigned_to_nat(29u);
v___x_1002_ = lean_unsigned_to_nat(1573u);
v___x_1003_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__0));
v___x_1004_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1005_ = l_mkPanicMessageWithDecl(v___x_1004_, v___x_1003_, v___x_1002_, v___x_1001_, v___x_1000_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21(lean_object* v_s_1006_, lean_object* v_pos_1007_){
_start:
{
lean_object* v_startInclusive_1008_; lean_object* v_endExclusive_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; 
v_startInclusive_1008_ = lean_ctor_get(v_s_1006_, 1);
v_endExclusive_1009_ = lean_ctor_get(v_s_1006_, 2);
v___x_1010_ = lean_nat_sub(v_endExclusive_1009_, v_startInclusive_1008_);
v___x_1011_ = lean_nat_dec_eq(v_pos_1007_, v___x_1010_);
lean_dec(v___x_1010_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; 
v___x_1012_ = l_String_Slice_Pos_next___redArg(v_s_1006_, v_pos_1007_);
return v___x_1012_;
}
else
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_obj_once(&l_String_Slice_Pos_next_x21___closed__2, &l_String_Slice_Pos_next_x21___closed__2_once, _init_l_String_Slice_Pos_next_x21___closed__2);
v___x_1014_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_1013_);
return v___x_1014_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21___boxed(lean_object* v_s_1015_, lean_object* v_pos_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_String_Slice_Pos_next_x21(v_s_1015_, v_pos_1016_);
lean_dec(v_pos_1016_);
lean_dec_ref(v_s_1015_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg(lean_object* v_s_1018_, lean_object* v_off_1019_){
_start:
{
lean_object* v_str_1020_; lean_object* v_startInclusive_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; uint8_t v___x_1024_; 
v_str_1020_ = lean_ctor_get(v_s_1018_, 0);
v_startInclusive_1021_ = lean_ctor_get(v_s_1018_, 1);
v___x_1022_ = lean_nat_add(v_startInclusive_1021_, v_off_1019_);
v___x_1023_ = lean_string_get_byte_fast(v_str_1020_, v___x_1022_);
v___x_1024_ = l_UInt8_instDecidableIsUTF8FirstByte___aux__1(v___x_1023_);
if (v___x_1024_ == 0)
{
lean_object* v_zero_1025_; uint8_t v_isZero_1026_; lean_object* v_one_1027_; lean_object* v_n_1028_; 
v_zero_1025_ = lean_unsigned_to_nat(0u);
v_isZero_1026_ = lean_nat_dec_eq(v_off_1019_, v_zero_1025_);
v_one_1027_ = lean_unsigned_to_nat(1u);
v_n_1028_ = lean_nat_sub(v_off_1019_, v_one_1027_);
lean_dec(v_off_1019_);
v_off_1019_ = v_n_1028_;
goto _start;
}
else
{
return v_off_1019_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg___boxed(lean_object* v_s_1030_, lean_object* v_off_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1030_, v_off_1031_);
lean_dec_ref(v_s_1030_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go(lean_object* v_s_1033_, lean_object* v_off_1034_, lean_object* v_h_u2081_1035_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1033_, v_off_1034_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___boxed(lean_object* v_s_1037_, lean_object* v_off_1038_, lean_object* v_h_u2081_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_String_Slice_Pos_prevAux_go(v_s_1037_, v_off_1038_, v_h_u2081_1039_);
lean_dec_ref(v_s_1037_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg(lean_object* v_s_1041_, lean_object* v_pos_1042_){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = lean_unsigned_to_nat(1u);
v___x_1044_ = lean_nat_sub(v_pos_1042_, v___x_1043_);
v___x_1045_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1041_, v___x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg___boxed(lean_object* v_s_1046_, lean_object* v_pos_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_String_Slice_Pos_prevAux___redArg(v_s_1046_, v_pos_1047_);
lean_dec(v_pos_1047_);
lean_dec_ref(v_s_1046_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux(lean_object* v_s_1049_, lean_object* v_pos_1050_, lean_object* v_h_1051_){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = lean_unsigned_to_nat(1u);
v___x_1053_ = lean_nat_sub(v_pos_1050_, v___x_1052_);
v___x_1054_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1049_, v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___boxed(lean_object* v_s_1055_, lean_object* v_pos_1056_, lean_object* v_h_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_String_Slice_Pos_prevAux(v_s_1055_, v_pos_1056_, v_h_1057_);
lean_dec(v_pos_1056_);
lean_dec_ref(v_s_1055_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(lean_object* v_off_1059_, lean_object* v_h__1_1060_, lean_object* v_h__2_1061_){
_start:
{
lean_object* v_zero_1062_; uint8_t v_isZero_1063_; 
v_zero_1062_ = lean_unsigned_to_nat(0u);
v_isZero_1063_ = lean_nat_dec_eq(v_off_1059_, v_zero_1062_);
if (v_isZero_1063_ == 1)
{
lean_object* v___x_1064_; 
lean_dec(v_h__2_1061_);
v___x_1064_ = lean_apply_3(v_h__1_1060_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1064_;
}
else
{
lean_object* v_one_1065_; lean_object* v_n_1066_; lean_object* v___x_1067_; 
lean_dec(v_h__1_1060_);
v_one_1065_ = lean_unsigned_to_nat(1u);
v_n_1066_ = lean_nat_sub(v_off_1059_, v_one_1065_);
v___x_1067_ = lean_apply_4(v_h__2_1061_, v_n_1066_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1067_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg___boxed(lean_object* v_off_1068_, lean_object* v_h__1_1069_, lean_object* v_h__2_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(v_off_1068_, v_h__1_1069_, v_h__2_1070_);
lean_dec(v_off_1068_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(lean_object* v_s_1072_, lean_object* v_motive_1073_, lean_object* v_off_1074_, lean_object* v_h_u2081_1075_, lean_object* v_hbyte_1076_, lean_object* v_this_1077_, lean_object* v_h__1_1078_, lean_object* v_h__2_1079_){
_start:
{
lean_object* v_zero_1080_; uint8_t v_isZero_1081_; 
v_zero_1080_ = lean_unsigned_to_nat(0u);
v_isZero_1081_ = lean_nat_dec_eq(v_off_1074_, v_zero_1080_);
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
v_n_1084_ = lean_nat_sub(v_off_1074_, v_one_1083_);
v___x_1085_ = lean_apply_4(v_h__2_1079_, v_n_1084_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1085_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___boxed(lean_object* v_s_1086_, lean_object* v_motive_1087_, lean_object* v_off_1088_, lean_object* v_h_u2081_1089_, lean_object* v_hbyte_1090_, lean_object* v_this_1091_, lean_object* v_h__1_1092_, lean_object* v_h__2_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(v_s_1086_, v_motive_1087_, v_off_1088_, v_h_u2081_1089_, v_hbyte_1090_, v_this_1091_, v_h__1_1092_, v_h__2_1093_);
lean_dec(v_off_1088_);
lean_dec_ref(v_s_1086_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg(lean_object* v_off_1095_){
_start:
{
lean_inc(v_off_1095_);
return v_off_1095_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg___boxed(lean_object* v_off_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_String_Slice_pos___redArg(v_off_1096_);
lean_dec(v_off_1096_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos(lean_object* v_s_1098_, lean_object* v_off_1099_, lean_object* v_h_1100_){
_start:
{
lean_inc(v_off_1099_);
return v_off_1099_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___boxed(lean_object* v_s_1101_, lean_object* v_off_1102_, lean_object* v_h_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_String_Slice_pos(v_s_1101_, v_off_1102_, v_h_1103_);
lean_dec(v_off_1102_);
lean_dec_ref(v_s_1101_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f(lean_object* v_s_1105_, lean_object* v_off_1106_){
_start:
{
uint8_t v___x_1107_; 
v___x_1107_ = l_String_Pos_Raw_isValidForSlice(v_s_1105_, v_off_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; 
lean_dec(v_off_1106_);
v___x_1108_ = lean_box(0);
return v___x_1108_;
}
else
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1109_, 0, v_off_1106_);
return v___x_1109_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f___boxed(lean_object* v_s_1110_, lean_object* v_off_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_String_Slice_pos_x3f(v_s_1110_, v_off_1111_);
lean_dec_ref(v_s_1110_);
return v_res_1112_;
}
}
static lean_object* _init_l_String_Slice_pos_x21___closed__2(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1115_ = ((lean_object*)(l_String_Slice_pos_x21___closed__1));
v___x_1116_ = lean_unsigned_to_nat(4u);
v___x_1117_ = lean_unsigned_to_nat(1661u);
v___x_1118_ = ((lean_object*)(l_String_Slice_pos_x21___closed__0));
v___x_1119_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1120_ = l_mkPanicMessageWithDecl(v___x_1119_, v___x_1118_, v___x_1117_, v___x_1116_, v___x_1115_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21(lean_object* v_s_1121_, lean_object* v_off_1122_){
_start:
{
uint8_t v___x_1123_; 
v___x_1123_ = l_String_Pos_Raw_isValidForSlice(v_s_1121_, v_off_1122_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_obj_once(&l_String_Slice_pos_x21___closed__2, &l_String_Slice_pos_x21___closed__2_once, _init_l_String_Slice_pos_x21___closed__2);
v___x_1125_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_1124_);
return v___x_1125_;
}
else
{
lean_inc(v_off_1122_);
return v_off_1122_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21___boxed(lean_object* v_s_1126_, lean_object* v_off_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_String_Slice_pos_x21(v_s_1126_, v_off_1127_);
lean_dec(v_off_1127_);
lean_dec_ref(v_s_1126_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next___boxed(lean_object* v_s_1132_, lean_object* v_pos_1133_, lean_object* v_h_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = lean_string_utf8_next_fast(v_s_1132_, v_pos_1133_);
lean_dec(v_pos_1133_);
lean_dec_ref(v_s_1132_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x3f(lean_object* v_s_1136_, lean_object* v_pos_1137_){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1138_ = lean_unsigned_to_nat(0u);
v___x_1139_ = lean_string_utf8_byte_size(v_s_1136_);
v___x_1140_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1140_, 0, v_s_1136_);
lean_ctor_set(v___x_1140_, 1, v___x_1138_);
lean_ctor_set(v___x_1140_, 2, v___x_1139_);
v___x_1141_ = l_String_Slice_Pos_next_x3f(v___x_1140_, v_pos_1137_);
lean_dec_ref_known(v___x_1140_, 3);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_box(0);
return v___x_1142_;
}
else
{
lean_object* v_val_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
v_val_1143_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1141_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_val_1143_);
lean_dec(v___x_1141_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_val_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x3f___boxed(lean_object* v_s_1151_, lean_object* v_pos_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_String_Pos_next_x3f(v_s_1151_, v_pos_1152_);
lean_dec(v_pos_1152_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21(lean_object* v_s_1154_, lean_object* v_pos_1155_){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1156_ = lean_unsigned_to_nat(0u);
v___x_1157_ = lean_string_utf8_byte_size(v_s_1154_);
v___x_1158_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1158_, 0, v_s_1154_);
lean_ctor_set(v___x_1158_, 1, v___x_1156_);
lean_ctor_set(v___x_1158_, 2, v___x_1157_);
v___x_1159_ = l_String_Slice_Pos_next_x21(v___x_1158_, v_pos_1155_);
lean_dec_ref_known(v___x_1158_, 3);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21___boxed(lean_object* v_s_1160_, lean_object* v_pos_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_String_Pos_next_x21(v_s_1160_, v_pos_1161_);
lean_dec(v_pos_1161_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg(lean_object* v_off_1163_){
_start:
{
lean_inc(v_off_1163_);
return v_off_1163_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg___boxed(lean_object* v_off_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_String_pos___redArg(v_off_1164_);
lean_dec(v_off_1164_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_String_pos(lean_object* v_s_1166_, lean_object* v_off_1167_, lean_object* v_h_1168_){
_start:
{
lean_inc(v_off_1167_);
return v_off_1167_;
}
}
LEAN_EXPORT lean_object* l_String_pos___boxed(lean_object* v_s_1169_, lean_object* v_off_1170_, lean_object* v_h_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_String_pos(v_s_1169_, v_off_1170_, v_h_1171_);
lean_dec(v_off_1170_);
lean_dec_ref(v_s_1169_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x3f(lean_object* v_s_1173_, lean_object* v_off_1174_){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1175_ = lean_unsigned_to_nat(0u);
v___x_1176_ = lean_string_utf8_byte_size(v_s_1173_);
v___x_1177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1177_, 0, v_s_1173_);
lean_ctor_set(v___x_1177_, 1, v___x_1175_);
lean_ctor_set(v___x_1177_, 2, v___x_1176_);
v___x_1178_ = l_String_Slice_pos_x3f(v___x_1177_, v_off_1174_);
lean_dec_ref_known(v___x_1177_, 3);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_box(0);
return v___x_1179_;
}
else
{
lean_object* v_val_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
v_val_1180_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1178_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_val_1180_);
lean_dec(v___x_1178_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_val_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_pos_x21(lean_object* v_s_1188_, lean_object* v_off_1189_){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1190_ = lean_unsigned_to_nat(0u);
v___x_1191_ = lean_string_utf8_byte_size(v_s_1188_);
v___x_1192_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1192_, 0, v_s_1188_);
lean_ctor_set(v___x_1192_, 1, v___x_1190_);
lean_ctor_set(v___x_1192_, 2, v___x_1191_);
v___x_1193_ = l_String_Slice_pos_x21(v___x_1192_, v_off_1189_);
lean_dec_ref_known(v___x_1192_, 3);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x21___boxed(lean_object* v_s_1194_, lean_object* v_off_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_String_pos_x21(v_s_1194_, v_off_1195_);
lean_dec(v_off_1195_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg(lean_object* v_pos_1197_){
_start:
{
lean_inc(v_pos_1197_);
return v_pos_1197_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg___boxed(lean_object* v_pos_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_String_Slice_Pos_cast___redArg(v_pos_1198_);
lean_dec(v_pos_1198_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast(lean_object* v_s_1200_, lean_object* v_t_1201_, lean_object* v_pos_1202_, lean_object* v_h_1203_){
_start:
{
lean_inc(v_pos_1202_);
return v_pos_1202_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___boxed(lean_object* v_s_1204_, lean_object* v_t_1205_, lean_object* v_pos_1206_, lean_object* v_h_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_String_Slice_Pos_cast(v_s_1204_, v_t_1205_, v_pos_1206_, v_h_1207_);
lean_dec(v_pos_1206_);
lean_dec_ref(v_t_1205_);
lean_dec_ref(v_s_1204_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg(lean_object* v_pos_1209_){
_start:
{
lean_inc(v_pos_1209_);
return v_pos_1209_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg___boxed(lean_object* v_pos_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_String_Pos_cast___redArg(v_pos_1210_);
lean_dec(v_pos_1210_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast(lean_object* v_s_1212_, lean_object* v_t_1213_, lean_object* v_pos_1214_, lean_object* v_h_1215_){
_start:
{
lean_inc(v_pos_1214_);
return v_pos_1214_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___boxed(lean_object* v_s_1216_, lean_object* v_t_1217_, lean_object* v_pos_1218_, lean_object* v_h_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_String_Pos_cast(v_s_1216_, v_t_1217_, v_pos_1218_, v_h_1219_);
lean_dec(v_pos_1218_);
lean_dec_ref(v_t_1217_);
lean_dec_ref(v_s_1216_);
return v_res_1220_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_Raw_utf8GetAux(lean_object* v_x_1221_, lean_object* v_x_1222_, lean_object* v_x_1223_){
_start:
{
if (lean_obj_tag(v_x_1221_) == 0)
{
uint32_t v___x_1224_; 
lean_dec(v_x_1222_);
v___x_1224_ = 65;
return v___x_1224_;
}
else
{
lean_object* v_head_1225_; lean_object* v_tail_1226_; uint8_t v___x_1227_; 
v_head_1225_ = lean_ctor_get(v_x_1221_, 0);
v_tail_1226_ = lean_ctor_get(v_x_1221_, 1);
v___x_1227_ = lean_nat_dec_eq(v_x_1222_, v_x_1223_);
if (v___x_1227_ == 0)
{
uint32_t v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1228_ = lean_unbox_uint32(v_head_1225_);
v___x_1229_ = l_Char_utf8Size(v___x_1228_);
v___x_1230_ = lean_nat_add(v_x_1222_, v___x_1229_);
lean_dec(v___x_1229_);
lean_dec(v_x_1222_);
v_x_1221_ = v_tail_1226_;
v_x_1222_ = v___x_1230_;
goto _start;
}
else
{
uint32_t v___x_1232_; 
lean_dec(v_x_1222_);
v___x_1232_ = lean_unbox_uint32(v_head_1225_);
return v___x_1232_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux___boxed(lean_object* v_x_1233_, lean_object* v_x_1234_, lean_object* v_x_1235_){
_start:
{
uint32_t v_res_1236_; lean_object* v_r_1237_; 
v_res_1236_ = l_String_Pos_Raw_utf8GetAux(v_x_1233_, v_x_1234_, v_x_1235_);
lean_dec(v_x_1235_);
lean_dec(v_x_1233_);
v_r_1237_ = lean_box_uint32(v_res_1236_);
return v_r_1237_;
}
}
LEAN_EXPORT uint32_t l_String_utf8GetAux(lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
uint32_t v___x_1241_; 
v___x_1241_ = l_String_Pos_Raw_utf8GetAux(v_a_1238_, v_a_1239_, v_a_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux___boxed(lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
uint32_t v_res_1245_; lean_object* v_r_1246_; 
v_res_1245_ = l_String_utf8GetAux(v_a_1242_, v_a_1243_, v_a_1244_);
lean_dec(v_a_1244_);
lean_dec(v_a_1242_);
v_r_1246_ = lean_box_uint32(v_res_1245_);
return v_r_1246_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get___boxed(lean_object* v_s_1249_, lean_object* v_p_1250_){
_start:
{
uint32_t v_res_1251_; lean_object* v_r_1252_; 
v_res_1251_ = lean_string_utf8_get(v_s_1249_, v_p_1250_);
lean_dec(v_p_1250_);
lean_dec_ref(v_s_1249_);
v_r_1252_ = lean_box_uint32(v_res_1251_);
return v_r_1252_;
}
}
LEAN_EXPORT lean_object* l_String_get___boxed(lean_object* v_s_1255_, lean_object* v_p_1256_){
_start:
{
uint32_t v_res_1257_; lean_object* v_r_1258_; 
v_res_1257_ = lean_string_utf8_get(v_s_1255_, v_p_1256_);
lean_dec(v_p_1256_);
lean_dec_ref(v_s_1255_);
v_r_1258_ = lean_box_uint32(v_res_1257_);
return v_r_1258_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f(lean_object* v_x_1259_, lean_object* v_x_1260_, lean_object* v_x_1261_){
_start:
{
if (lean_obj_tag(v_x_1259_) == 0)
{
lean_object* v___x_1262_; 
lean_dec(v_x_1260_);
v___x_1262_ = lean_box(0);
return v___x_1262_;
}
else
{
lean_object* v_head_1263_; lean_object* v_tail_1264_; uint8_t v___x_1265_; 
v_head_1263_ = lean_ctor_get(v_x_1259_, 0);
v_tail_1264_ = lean_ctor_get(v_x_1259_, 1);
v___x_1265_ = lean_nat_dec_eq(v_x_1260_, v_x_1261_);
if (v___x_1265_ == 0)
{
uint32_t v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1266_ = lean_unbox_uint32(v_head_1263_);
v___x_1267_ = l_Char_utf8Size(v___x_1266_);
v___x_1268_ = lean_nat_add(v_x_1260_, v___x_1267_);
lean_dec(v___x_1267_);
lean_dec(v_x_1260_);
v_x_1259_ = v_tail_1264_;
v_x_1260_ = v___x_1268_;
goto _start;
}
else
{
lean_object* v___x_1270_; 
lean_dec(v_x_1260_);
lean_inc(v_head_1263_);
v___x_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1270_, 0, v_head_1263_);
return v___x_1270_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f___boxed(lean_object* v_x_1271_, lean_object* v_x_1272_, lean_object* v_x_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_String_Pos_Raw_utf8GetAux_x3f(v_x_1271_, v_x_1272_, v_x_1273_);
lean_dec(v_x_1273_);
lean_dec(v_x_1271_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f(lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_String_Pos_Raw_utf8GetAux_x3f(v_a_1275_, v_a_1276_, v_a_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f___boxed(lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_String_utf8GetAux_x3f(v_a_1279_, v_a_1280_, v_a_1281_);
lean_dec(v_a_1281_);
lean_dec(v_a_1279_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1285_, lean_object* v_a_00___x40___internal___hyg_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1285_, v_a_00___x40___internal___hyg_1286_);
lean_dec(v_a_00___x40___internal___hyg_1286_);
lean_dec_ref(v_a_00___x40___internal___hyg_1285_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_String_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1290_, lean_object* v_a_00___x40___internal___hyg_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1290_, v_a_00___x40___internal___hyg_1291_);
lean_dec(v_a_00___x40___internal___hyg_1291_);
lean_dec_ref(v_a_00___x40___internal___hyg_1290_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x21___boxed(lean_object* v_s_1295_, lean_object* v_p_1296_){
_start:
{
uint32_t v_res_1297_; lean_object* v_r_1298_; 
v_res_1297_ = lean_string_utf8_get_bang(v_s_1295_, v_p_1296_);
lean_dec(v_p_1296_);
lean_dec_ref(v_s_1295_);
v_r_1298_ = lean_box_uint32(v_res_1297_);
return v_r_1298_;
}
}
LEAN_EXPORT lean_object* l_String_get_x21___boxed(lean_object* v_s_1301_, lean_object* v_p_1302_){
_start:
{
uint32_t v_res_1303_; lean_object* v_r_1304_; 
v_res_1303_ = lean_string_utf8_get_bang(v_s_1301_, v_p_1302_);
lean_dec(v_p_1302_);
lean_dec_ref(v_s_1301_);
v_r_1304_ = lean_box_uint32(v_res_1303_);
return v_r_1304_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux(uint32_t v_c_x27_1305_, lean_object* v_x_1306_, lean_object* v_x_1307_, lean_object* v_x_1308_){
_start:
{
if (lean_obj_tag(v_x_1306_) == 0)
{
return v_x_1306_;
}
else
{
lean_object* v_head_1309_; lean_object* v_tail_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1326_; 
v_head_1309_ = lean_ctor_get(v_x_1306_, 0);
v_tail_1310_ = lean_ctor_get(v_x_1306_, 1);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_x_1306_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1312_ = v_x_1306_;
v_isShared_1313_ = v_isSharedCheck_1326_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_tail_1310_);
lean_inc(v_head_1309_);
lean_dec(v_x_1306_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1326_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
uint8_t v___x_1314_; 
v___x_1314_ = lean_nat_dec_eq(v_x_1307_, v_x_1308_);
if (v___x_1314_ == 0)
{
uint32_t v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1320_; 
v___x_1315_ = lean_unbox_uint32(v_head_1309_);
v___x_1316_ = l_Char_utf8Size(v___x_1315_);
v___x_1317_ = lean_nat_add(v_x_1307_, v___x_1316_);
lean_dec(v___x_1316_);
v___x_1318_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1305_, v_tail_1310_, v___x_1317_, v_x_1308_);
lean_dec(v___x_1317_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 1, v___x_1318_);
v___x_1320_ = v___x_1312_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_head_1309_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v___x_1318_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1324_; 
lean_dec(v_head_1309_);
v___x_1322_ = lean_box_uint32(v_c_x27_1305_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v___x_1322_);
v___x_1324_ = v___x_1312_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1322_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v_tail_1310_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux___boxed(lean_object* v_c_x27_1327_, lean_object* v_x_1328_, lean_object* v_x_1329_, lean_object* v_x_1330_){
_start:
{
uint32_t v_c_x27_boxed_1331_; lean_object* v_res_1332_; 
v_c_x27_boxed_1331_ = lean_unbox_uint32(v_c_x27_1327_);
lean_dec(v_c_x27_1327_);
v_res_1332_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_boxed_1331_, v_x_1328_, v_x_1329_, v_x_1330_);
lean_dec(v_x_1330_);
lean_dec(v_x_1329_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux(uint32_t v_c_x27_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux___boxed(lean_object* v_c_x27_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
uint32_t v_c_x27_boxed_1342_; lean_object* v_res_1343_; 
v_c_x27_boxed_1342_ = lean_unbox_uint32(v_c_x27_1338_);
lean_dec(v_c_x27_1338_);
v_res_1343_ = l_String_utf8SetAux(v_c_x27_boxed_1342_, v_a_1339_, v_a_1340_, v_a_1341_);
lean_dec(v_a_1341_);
lean_dec(v_a_1340_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg(lean_object* v_s_1344_, lean_object* v_pos_1345_){
_start:
{
lean_object* v_str_1346_; lean_object* v_startInclusive_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v_str_1346_ = lean_ctor_get(v_s_1344_, 0);
v_startInclusive_1347_ = lean_ctor_get(v_s_1344_, 1);
v___x_1348_ = lean_nat_add(v_startInclusive_1347_, v_pos_1345_);
v___x_1349_ = lean_string_utf8_next_fast(v_str_1346_, v___x_1348_);
lean_dec(v___x_1348_);
v___x_1350_ = lean_nat_sub(v___x_1349_, v_startInclusive_1347_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg___boxed(lean_object* v_s_1351_, lean_object* v_pos_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_String_Slice_Pos_nextFast___redArg(v_s_1351_, v_pos_1352_);
lean_dec(v_pos_1352_);
lean_dec_ref(v_s_1351_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast(lean_object* v_s_1354_, lean_object* v_pos_1355_, lean_object* v_h_1356_){
_start:
{
lean_object* v_str_1357_; lean_object* v_startInclusive_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v_str_1357_ = lean_ctor_get(v_s_1354_, 0);
v_startInclusive_1358_ = lean_ctor_get(v_s_1354_, 1);
v___x_1359_ = lean_nat_add(v_startInclusive_1358_, v_pos_1355_);
v___x_1360_ = lean_string_utf8_next_fast(v_str_1357_, v___x_1359_);
lean_dec(v___x_1359_);
v___x_1361_ = lean_nat_sub(v___x_1360_, v_startInclusive_1358_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___boxed(lean_object* v_s_1362_, lean_object* v_pos_1363_, lean_object* v_h_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_String_Slice_Pos_nextFast(v_s_1362_, v_pos_1363_, v_h_1364_);
lean_dec(v_pos_1363_);
lean_dec_ref(v_s_1362_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_String_sliceTo(lean_object* v_s_1366_, lean_object* v_p_1367_){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_unsigned_to_nat(0u);
v___x_1369_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1369_, 0, v_s_1366_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
lean_ctor_set(v___x_1369_, 2, v_p_1367_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_String_replaceEnd(lean_object* v_s_1370_, lean_object* v_p_1371_){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = lean_unsigned_to_nat(0u);
v___x_1373_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1373_, 0, v_s_1370_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
lean_ctor_set(v___x_1373_, 2, v_p_1371_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_String_sliceFrom(lean_object* v_s_1374_, lean_object* v_p_1375_){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = lean_string_utf8_byte_size(v_s_1374_);
v___x_1377_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1377_, 0, v_s_1374_);
lean_ctor_set(v___x_1377_, 1, v_p_1375_);
lean_ctor_set(v___x_1377_, 2, v___x_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStart(lean_object* v_s_1378_, lean_object* v_p_1379_){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = lean_string_utf8_byte_size(v_s_1378_);
v___x_1381_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1381_, 0, v_s_1378_);
lean_ctor_set(v___x_1381_, 1, v_p_1379_);
lean_ctor_set(v___x_1381_, 2, v___x_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_String_slice___redArg(lean_object* v_s_1382_, lean_object* v_startInclusive_1383_, lean_object* v_endExclusive_1384_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1385_, 0, v_s_1382_);
lean_ctor_set(v___x_1385_, 1, v_startInclusive_1383_);
lean_ctor_set(v___x_1385_, 2, v_endExclusive_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_String_slice(lean_object* v_s_1386_, lean_object* v_startInclusive_1387_, lean_object* v_endExclusive_1388_, lean_object* v_h_1389_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1390_, 0, v_s_1386_);
lean_ctor_set(v___x_1390_, 1, v_startInclusive_1387_);
lean_ctor_set(v___x_1390_, 2, v_endExclusive_1388_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x3f(lean_object* v_s_1391_, lean_object* v_startInclusive_1392_, lean_object* v_endExclusive_1393_){
_start:
{
uint8_t v___x_1394_; 
v___x_1394_ = lean_nat_dec_le(v_startInclusive_1392_, v_endExclusive_1393_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; 
lean_dec(v_endExclusive_1393_);
lean_dec(v_startInclusive_1392_);
lean_dec_ref(v_s_1391_);
v___x_1395_ = lean_box(0);
return v___x_1395_;
}
else
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1396_, 0, v_s_1391_);
lean_ctor_set(v___x_1396_, 1, v_startInclusive_1392_);
lean_ctor_set(v___x_1396_, 2, v_endExclusive_1393_);
v___x_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
return v___x_1397_;
}
}
}
LEAN_EXPORT lean_object* l_String_slice_x21(lean_object* v_s_1398_, lean_object* v_p_u2081_1399_, lean_object* v_p_u2082_1400_){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1401_ = lean_unsigned_to_nat(0u);
v___x_1402_ = lean_string_utf8_byte_size(v_s_1398_);
v___x_1403_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1403_, 0, v_s_1398_);
lean_ctor_set(v___x_1403_, 1, v___x_1401_);
lean_ctor_set(v___x_1403_, 2, v___x_1402_);
v___x_1404_ = l_String_Slice_slice_x21(v___x_1403_, v_p_u2081_1399_, v_p_u2082_1400_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x21___boxed(lean_object* v_s_1405_, lean_object* v_p_u2081_1406_, lean_object* v_p_u2082_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_String_slice_x21(v_s_1405_, v_p_u2081_1406_, v_p_u2082_1407_);
lean_dec(v_p_u2082_1407_);
lean_dec(v_p_u2081_1406_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21(lean_object* v_s_1409_, lean_object* v_p_u2081_1410_, lean_object* v_p_u2082_1411_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_String_slice_x21(v_s_1409_, v_p_u2081_1410_, v_p_u2082_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21___boxed(lean_object* v_s_1413_, lean_object* v_p_u2081_1414_, lean_object* v_p_u2082_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_String_replaceStartEnd_x21(v_s_1413_, v_p_u2081_1414_, v_p_u2082_1415_);
lean_dec(v_p_u2082_1415_);
lean_dec(v_p_u2081_1414_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg(lean_object* v_p_u2080_1417_, lean_object* v_pos_1418_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_nat_add(v_p_u2080_1417_, v_pos_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg___boxed(lean_object* v_p_u2080_1420_, lean_object* v_pos_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_String_Pos_ofSliceFrom___redArg(v_p_u2080_1420_, v_pos_1421_);
lean_dec(v_pos_1421_);
lean_dec(v_p_u2080_1420_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom(lean_object* v_s_1423_, lean_object* v_p_u2080_1424_, lean_object* v_pos_1425_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_nat_add(v_p_u2080_1424_, v_pos_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___boxed(lean_object* v_s_1427_, lean_object* v_p_u2080_1428_, lean_object* v_pos_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_String_Pos_ofSliceFrom(v_s_1427_, v_p_u2080_1428_, v_pos_1429_);
lean_dec(v_pos_1429_);
lean_dec(v_p_u2080_1428_);
lean_dec_ref(v_s_1427_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg(lean_object* v_p_u2080_1431_, lean_object* v_pos_1432_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_nat_add(v_p_u2080_1431_, v_pos_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg___boxed(lean_object* v_p_u2080_1434_, lean_object* v_pos_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_String_Pos_ofReplaceStart___redArg(v_p_u2080_1434_, v_pos_1435_);
lean_dec(v_pos_1435_);
lean_dec(v_p_u2080_1434_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart(lean_object* v_s_1437_, lean_object* v_p_u2080_1438_, lean_object* v_pos_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = lean_nat_add(v_p_u2080_1438_, v_pos_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___boxed(lean_object* v_s_1441_, lean_object* v_p_u2080_1442_, lean_object* v_pos_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_String_Pos_ofReplaceStart(v_s_1441_, v_p_u2080_1442_, v_pos_1443_);
lean_dec(v_pos_1443_);
lean_dec(v_p_u2080_1442_);
lean_dec_ref(v_s_1441_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg(lean_object* v_p_u2080_1445_, lean_object* v_pos_1446_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_nat_sub(v_pos_1446_, v_p_u2080_1445_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg___boxed(lean_object* v_p_u2080_1448_, lean_object* v_pos_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_String_Pos_sliceFrom___redArg(v_p_u2080_1448_, v_pos_1449_);
lean_dec(v_pos_1449_);
lean_dec(v_p_u2080_1448_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom(lean_object* v_s_1451_, lean_object* v_p_u2080_1452_, lean_object* v_pos_1453_, lean_object* v_h_1454_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = lean_nat_sub(v_pos_1453_, v_p_u2080_1452_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___boxed(lean_object* v_s_1456_, lean_object* v_p_u2080_1457_, lean_object* v_pos_1458_, lean_object* v_h_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_String_Pos_sliceFrom(v_s_1456_, v_p_u2080_1457_, v_pos_1458_, v_h_1459_);
lean_dec(v_pos_1458_);
lean_dec(v_p_u2080_1457_);
lean_dec_ref(v_s_1456_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg(lean_object* v_p_u2080_1461_, lean_object* v_pos_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_nat_sub(v_pos_1462_, v_p_u2080_1461_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg___boxed(lean_object* v_p_u2080_1464_, lean_object* v_pos_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_String_Pos_toReplaceStart___redArg(v_p_u2080_1464_, v_pos_1465_);
lean_dec(v_pos_1465_);
lean_dec(v_p_u2080_1464_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart(lean_object* v_s_1467_, lean_object* v_p_u2080_1468_, lean_object* v_pos_1469_, lean_object* v_h_1470_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_nat_sub(v_pos_1469_, v_p_u2080_1468_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___boxed(lean_object* v_s_1472_, lean_object* v_p_u2080_1473_, lean_object* v_pos_1474_, lean_object* v_h_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_String_Pos_toReplaceStart(v_s_1472_, v_p_u2080_1473_, v_pos_1474_, v_h_1475_);
lean_dec(v_pos_1474_);
lean_dec(v_p_u2080_1473_);
lean_dec_ref(v_s_1472_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg(lean_object* v_pos_1477_){
_start:
{
lean_inc(v_pos_1477_);
return v_pos_1477_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg___boxed(lean_object* v_pos_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_String_Pos_ofSliceTo___redArg(v_pos_1478_);
lean_dec(v_pos_1478_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo(lean_object* v_s_1480_, lean_object* v_p_u2080_1481_, lean_object* v_pos_1482_){
_start:
{
lean_inc(v_pos_1482_);
return v_pos_1482_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___boxed(lean_object* v_s_1483_, lean_object* v_p_u2080_1484_, lean_object* v_pos_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_String_Pos_ofSliceTo(v_s_1483_, v_p_u2080_1484_, v_pos_1485_);
lean_dec(v_pos_1485_);
lean_dec(v_p_u2080_1484_);
lean_dec_ref(v_s_1483_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg(lean_object* v_pos_1487_){
_start:
{
lean_inc(v_pos_1487_);
return v_pos_1487_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg___boxed(lean_object* v_pos_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_String_Pos_ofReplaceEnd___redArg(v_pos_1488_);
lean_dec(v_pos_1488_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd(lean_object* v_s_1490_, lean_object* v_p_u2080_1491_, lean_object* v_pos_1492_){
_start:
{
lean_inc(v_pos_1492_);
return v_pos_1492_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___boxed(lean_object* v_s_1493_, lean_object* v_p_u2080_1494_, lean_object* v_pos_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_String_Pos_ofReplaceEnd(v_s_1493_, v_p_u2080_1494_, v_pos_1495_);
lean_dec(v_pos_1495_);
lean_dec(v_p_u2080_1494_);
lean_dec_ref(v_s_1493_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg(lean_object* v_pos_1497_){
_start:
{
lean_inc(v_pos_1497_);
return v_pos_1497_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg___boxed(lean_object* v_pos_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_String_Pos_sliceTo___redArg(v_pos_1498_);
lean_dec(v_pos_1498_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo(lean_object* v_s_1500_, lean_object* v_p_u2080_1501_, lean_object* v_pos_1502_, lean_object* v_h_1503_){
_start:
{
lean_inc(v_pos_1502_);
return v_pos_1502_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___boxed(lean_object* v_s_1504_, lean_object* v_p_u2080_1505_, lean_object* v_pos_1506_, lean_object* v_h_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_String_Pos_sliceTo(v_s_1504_, v_p_u2080_1505_, v_pos_1506_, v_h_1507_);
lean_dec(v_pos_1506_);
lean_dec(v_p_u2080_1505_);
lean_dec_ref(v_s_1504_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg(lean_object* v_pos_1509_){
_start:
{
lean_inc(v_pos_1509_);
return v_pos_1509_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg___boxed(lean_object* v_pos_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_String_Pos_toReplaceEnd___redArg(v_pos_1510_);
lean_dec(v_pos_1510_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd(lean_object* v_s_1512_, lean_object* v_p_u2080_1513_, lean_object* v_pos_1514_, lean_object* v_h_1515_){
_start:
{
lean_inc(v_pos_1514_);
return v_pos_1514_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___boxed(lean_object* v_s_1516_, lean_object* v_p_u2080_1517_, lean_object* v_pos_1518_, lean_object* v_h_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_String_Pos_toReplaceEnd(v_s_1516_, v_p_u2080_1517_, v_pos_1518_, v_h_1519_);
lean_dec(v_pos_1518_);
lean_dec(v_p_u2080_1517_);
lean_dec_ref(v_s_1516_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg(lean_object* v_p_u2080_1521_, lean_object* v_pos_1522_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = lean_nat_add(v_p_u2080_1521_, v_pos_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1524_, lean_object* v_pos_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_String_Slice_Pos_ofSlice___redArg(v_p_u2080_1524_, v_pos_1525_);
lean_dec(v_pos_1525_);
lean_dec(v_p_u2080_1524_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice(lean_object* v_s_1527_, lean_object* v_p_u2080_1528_, lean_object* v_p_u2081_1529_, lean_object* v_h_1530_, lean_object* v_pos_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_nat_add(v_p_u2080_1528_, v_pos_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___boxed(lean_object* v_s_1533_, lean_object* v_p_u2080_1534_, lean_object* v_p_u2081_1535_, lean_object* v_h_1536_, lean_object* v_pos_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_String_Slice_Pos_ofSlice(v_s_1533_, v_p_u2080_1534_, v_p_u2081_1535_, v_h_1536_, v_pos_1537_);
lean_dec(v_pos_1537_);
lean_dec(v_p_u2081_1535_);
lean_dec(v_p_u2080_1534_);
lean_dec_ref(v_s_1533_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg(lean_object* v_p_u2080_1539_, lean_object* v_pos_1540_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = lean_nat_add(v_p_u2080_1539_, v_pos_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1542_, lean_object* v_pos_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_String_Pos_ofSlice___redArg(v_p_u2080_1542_, v_pos_1543_);
lean_dec(v_pos_1543_);
lean_dec(v_p_u2080_1542_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice(lean_object* v_s_1545_, lean_object* v_p_u2080_1546_, lean_object* v_p_u2081_1547_, lean_object* v_h_1548_, lean_object* v_pos_1549_){
_start:
{
lean_object* v___x_1550_; 
v___x_1550_ = lean_nat_add(v_p_u2080_1546_, v_pos_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___boxed(lean_object* v_s_1551_, lean_object* v_p_u2080_1552_, lean_object* v_p_u2081_1553_, lean_object* v_h_1554_, lean_object* v_pos_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_String_Pos_ofSlice(v_s_1551_, v_p_u2080_1552_, v_p_u2081_1553_, v_h_1554_, v_pos_1555_);
lean_dec(v_pos_1555_);
lean_dec(v_p_u2081_1553_);
lean_dec(v_p_u2080_1552_);
lean_dec_ref(v_s_1551_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg(lean_object* v_pos_1557_, lean_object* v_p_u2080_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_nat_sub(v_pos_1557_, v_p_u2080_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg___boxed(lean_object* v_pos_1560_, lean_object* v_p_u2080_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_String_Slice_Pos_slice___redArg(v_pos_1560_, v_p_u2080_1561_);
lean_dec(v_p_u2080_1561_);
lean_dec(v_pos_1560_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice(lean_object* v_s_1563_, lean_object* v_pos_1564_, lean_object* v_p_u2080_1565_, lean_object* v_p_u2081_1566_, lean_object* v_h_u2081_1567_, lean_object* v_h_u2082_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_nat_sub(v_pos_1564_, v_p_u2080_1565_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___boxed(lean_object* v_s_1570_, lean_object* v_pos_1571_, lean_object* v_p_u2080_1572_, lean_object* v_p_u2081_1573_, lean_object* v_h_u2081_1574_, lean_object* v_h_u2082_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_String_Slice_Pos_slice(v_s_1570_, v_pos_1571_, v_p_u2080_1572_, v_p_u2081_1573_, v_h_u2081_1574_, v_h_u2082_1575_);
lean_dec(v_p_u2081_1573_);
lean_dec(v_p_u2080_1572_);
lean_dec(v_pos_1571_);
lean_dec_ref(v_s_1570_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg(lean_object* v_pos_1577_, lean_object* v_p_u2080_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_nat_sub(v_pos_1577_, v_p_u2080_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg___boxed(lean_object* v_pos_1580_, lean_object* v_p_u2080_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_String_Pos_slice___redArg(v_pos_1580_, v_p_u2080_1581_);
lean_dec(v_p_u2080_1581_);
lean_dec(v_pos_1580_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice(lean_object* v_s_1583_, lean_object* v_pos_1584_, lean_object* v_p_u2080_1585_, lean_object* v_p_u2081_1586_, lean_object* v_h_u2081_1587_, lean_object* v_h_u2082_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_nat_sub(v_pos_1584_, v_p_u2080_1585_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___boxed(lean_object* v_s_1590_, lean_object* v_pos_1591_, lean_object* v_p_u2080_1592_, lean_object* v_p_u2081_1593_, lean_object* v_h_u2081_1594_, lean_object* v_h_u2082_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_String_Pos_slice(v_s_1590_, v_pos_1591_, v_p_u2080_1592_, v_p_u2081_1593_, v_h_u2081_1594_, v_h_u2082_1595_);
lean_dec(v_p_u2081_1593_);
lean_dec(v_p_u2080_1592_);
lean_dec(v_pos_1591_);
lean_dec_ref(v_s_1590_);
return v_res_1596_;
}
}
static lean_object* _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2(void){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1599_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__1));
v___x_1600_ = lean_unsigned_to_nat(4u);
v___x_1601_ = lean_unsigned_to_nat(2676u);
v___x_1602_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__0));
v___x_1603_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1604_ = l_mkPanicMessageWithDecl(v___x_1603_, v___x_1602_, v___x_1601_, v___x_1600_, v___x_1599_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg(lean_object* v_pos_1605_, lean_object* v_p_u2080_1606_, lean_object* v_p_u2081_1607_){
_start:
{
uint8_t v___x_1612_; 
v___x_1612_ = lean_nat_dec_le(v_p_u2080_1606_, v_pos_1605_);
if (v___x_1612_ == 0)
{
goto v___jp_1608_;
}
else
{
uint8_t v___x_1613_; 
v___x_1613_ = lean_nat_dec_le(v_pos_1605_, v_p_u2081_1607_);
if (v___x_1613_ == 0)
{
goto v___jp_1608_;
}
else
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_nat_sub(v_pos_1605_, v_p_u2080_1606_);
return v___x_1614_;
}
}
v___jp_1608_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1609_ = lean_unsigned_to_nat(0u);
v___x_1610_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1611_ = l_panic___redArg(v___x_1609_, v___x_1610_);
return v___x_1611_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1615_, lean_object* v_p_u2080_1616_, lean_object* v_p_u2081_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_String_Slice_Pos_sliceOrPanic___redArg(v_pos_1615_, v_p_u2080_1616_, v_p_u2081_1617_);
lean_dec(v_p_u2081_1617_);
lean_dec(v_p_u2080_1616_);
lean_dec(v_pos_1615_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic(lean_object* v_s_1619_, lean_object* v_pos_1620_, lean_object* v_p_u2080_1621_, lean_object* v_p_u2081_1622_, lean_object* v_h_1623_){
_start:
{
uint8_t v___x_1628_; 
v___x_1628_ = lean_nat_dec_le(v_p_u2080_1621_, v_pos_1620_);
if (v___x_1628_ == 0)
{
goto v___jp_1624_;
}
else
{
uint8_t v___x_1629_; 
v___x_1629_ = lean_nat_dec_le(v_pos_1620_, v_p_u2081_1622_);
if (v___x_1629_ == 0)
{
goto v___jp_1624_;
}
else
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_nat_sub(v_pos_1620_, v_p_u2080_1621_);
return v___x_1630_;
}
}
v___jp_1624_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1625_ = lean_unsigned_to_nat(0u);
v___x_1626_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1627_ = l_panic___redArg(v___x_1625_, v___x_1626_);
return v___x_1627_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___boxed(lean_object* v_s_1631_, lean_object* v_pos_1632_, lean_object* v_p_u2080_1633_, lean_object* v_p_u2081_1634_, lean_object* v_h_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_String_Slice_Pos_sliceOrPanic(v_s_1631_, v_pos_1632_, v_p_u2080_1633_, v_p_u2081_1634_, v_h_1635_);
lean_dec(v_p_u2081_1634_);
lean_dec(v_p_u2080_1633_);
lean_dec(v_pos_1632_);
lean_dec_ref(v_s_1631_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg(lean_object* v_pos_1637_, lean_object* v_p_u2080_1638_, lean_object* v_p_u2081_1639_){
_start:
{
uint8_t v___x_1644_; 
v___x_1644_ = lean_nat_dec_le(v_p_u2080_1638_, v_pos_1637_);
if (v___x_1644_ == 0)
{
goto v___jp_1640_;
}
else
{
uint8_t v___x_1645_; 
v___x_1645_ = lean_nat_dec_le(v_pos_1637_, v_p_u2081_1639_);
if (v___x_1645_ == 0)
{
goto v___jp_1640_;
}
else
{
lean_object* v___x_1646_; 
v___x_1646_ = lean_nat_sub(v_pos_1637_, v_p_u2080_1638_);
return v___x_1646_;
}
}
v___jp_1640_:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1641_ = lean_unsigned_to_nat(0u);
v___x_1642_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1643_ = l_panic___redArg(v___x_1641_, v___x_1642_);
return v___x_1643_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1647_, lean_object* v_p_u2080_1648_, lean_object* v_p_u2081_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_String_Pos_sliceOrPanic___redArg(v_pos_1647_, v_p_u2080_1648_, v_p_u2081_1649_);
lean_dec(v_p_u2081_1649_);
lean_dec(v_p_u2080_1648_);
lean_dec(v_pos_1647_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic(lean_object* v_s_1651_, lean_object* v_pos_1652_, lean_object* v_p_u2080_1653_, lean_object* v_p_u2081_1654_, lean_object* v_h_1655_){
_start:
{
uint8_t v___x_1660_; 
v___x_1660_ = lean_nat_dec_le(v_p_u2080_1653_, v_pos_1652_);
if (v___x_1660_ == 0)
{
goto v___jp_1656_;
}
else
{
uint8_t v___x_1661_; 
v___x_1661_ = lean_nat_dec_le(v_pos_1652_, v_p_u2081_1654_);
if (v___x_1661_ == 0)
{
goto v___jp_1656_;
}
else
{
lean_object* v___x_1662_; 
v___x_1662_ = lean_nat_sub(v_pos_1652_, v_p_u2080_1653_);
return v___x_1662_;
}
}
v___jp_1656_:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1657_ = lean_unsigned_to_nat(0u);
v___x_1658_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1659_ = l_panic___redArg(v___x_1657_, v___x_1658_);
return v___x_1659_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___boxed(lean_object* v_s_1663_, lean_object* v_pos_1664_, lean_object* v_p_u2080_1665_, lean_object* v_p_u2081_1666_, lean_object* v_h_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_String_Pos_sliceOrPanic(v_s_1663_, v_pos_1664_, v_p_u2080_1665_, v_p_u2081_1666_, v_h_1667_);
lean_dec(v_p_u2081_1666_);
lean_dec(v_p_u2080_1665_);
lean_dec(v_pos_1664_);
lean_dec_ref(v_s_1663_);
return v_res_1668_;
}
}
static lean_object* _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1670_ = ((lean_object*)(l_String_Slice_slice_x21___closed__1));
v___x_1671_ = lean_unsigned_to_nat(4u);
v___x_1672_ = lean_unsigned_to_nat(2700u);
v___x_1673_ = ((lean_object*)(l_String_Slice_Pos_ofSlice_x21___redArg___closed__0));
v___x_1674_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1675_ = l_mkPanicMessageWithDecl(v___x_1674_, v___x_1673_, v___x_1672_, v___x_1671_, v___x_1670_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1676_, lean_object* v_p_u2081_1677_, lean_object* v_pos_1678_){
_start:
{
uint8_t v___x_1679_; 
v___x_1679_ = lean_nat_dec_le(v_p_u2080_1676_, v_p_u2081_1677_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1680_ = lean_unsigned_to_nat(0u);
v___x_1681_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1682_ = l_panic___redArg(v___x_1680_, v___x_1681_);
return v___x_1682_;
}
else
{
lean_object* v___x_1683_; 
v___x_1683_ = lean_nat_add(v_p_u2080_1676_, v_pos_1678_);
return v___x_1683_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1684_, lean_object* v_p_u2081_1685_, lean_object* v_pos_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_String_Slice_Pos_ofSlice_x21___redArg(v_p_u2080_1684_, v_p_u2081_1685_, v_pos_1686_);
lean_dec(v_pos_1686_);
lean_dec(v_p_u2081_1685_);
lean_dec(v_p_u2080_1684_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21(lean_object* v_s_1688_, lean_object* v_p_u2080_1689_, lean_object* v_p_u2081_1690_, lean_object* v_pos_1691_){
_start:
{
uint8_t v___x_1692_; 
v___x_1692_ = lean_nat_dec_le(v_p_u2080_1689_, v_p_u2081_1690_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1693_ = lean_unsigned_to_nat(0u);
v___x_1694_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1695_ = l_panic___redArg(v___x_1693_, v___x_1694_);
return v___x_1695_;
}
else
{
lean_object* v___x_1696_; 
v___x_1696_ = lean_nat_add(v_p_u2080_1689_, v_pos_1691_);
return v___x_1696_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___boxed(lean_object* v_s_1697_, lean_object* v_p_u2080_1698_, lean_object* v_p_u2081_1699_, lean_object* v_pos_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_String_Slice_Pos_ofSlice_x21(v_s_1697_, v_p_u2080_1698_, v_p_u2081_1699_, v_pos_1700_);
lean_dec(v_pos_1700_);
lean_dec(v_p_u2081_1699_);
lean_dec(v_p_u2080_1698_);
lean_dec_ref(v_s_1697_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1702_, lean_object* v_p_u2081_1703_, lean_object* v_pos_1704_){
_start:
{
uint8_t v___x_1705_; 
v___x_1705_ = lean_nat_dec_le(v_p_u2080_1702_, v_p_u2081_1703_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1706_ = lean_unsigned_to_nat(0u);
v___x_1707_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1708_ = l_panic___redArg(v___x_1706_, v___x_1707_);
return v___x_1708_;
}
else
{
lean_object* v___x_1709_; 
v___x_1709_ = lean_nat_add(v_p_u2080_1702_, v_pos_1704_);
return v___x_1709_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1710_, lean_object* v_p_u2081_1711_, lean_object* v_pos_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_String_Pos_ofSlice_x21___redArg(v_p_u2080_1710_, v_p_u2081_1711_, v_pos_1712_);
lean_dec(v_pos_1712_);
lean_dec(v_p_u2081_1711_);
lean_dec(v_p_u2080_1710_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21(lean_object* v_s_1714_, lean_object* v_p_u2080_1715_, lean_object* v_p_u2081_1716_, lean_object* v_pos_1717_){
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
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___boxed(lean_object* v_s_1723_, lean_object* v_p_u2080_1724_, lean_object* v_p_u2081_1725_, lean_object* v_pos_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_String_Pos_ofSlice_x21(v_s_1723_, v_p_u2080_1724_, v_p_u2081_1725_, v_pos_1726_);
lean_dec(v_pos_1726_);
lean_dec(v_p_u2081_1725_);
lean_dec(v_p_u2080_1724_);
lean_dec_ref(v_s_1723_);
return v_res_1727_;
}
}
static lean_object* _init_l_String_Slice_Pos_slice_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1730_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__1));
v___x_1731_ = lean_unsigned_to_nat(4u);
v___x_1732_ = lean_unsigned_to_nat(2718u);
v___x_1733_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__0));
v___x_1734_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1735_ = l_mkPanicMessageWithDecl(v___x_1734_, v___x_1733_, v___x_1732_, v___x_1731_, v___x_1730_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg(lean_object* v_pos_1736_, lean_object* v_p_u2080_1737_, lean_object* v_p_u2081_1738_){
_start:
{
uint8_t v___x_1743_; 
v___x_1743_ = lean_nat_dec_le(v_p_u2080_1737_, v_pos_1736_);
if (v___x_1743_ == 0)
{
goto v___jp_1739_;
}
else
{
uint8_t v___x_1744_; 
v___x_1744_ = lean_nat_dec_le(v_pos_1736_, v_p_u2081_1738_);
if (v___x_1744_ == 0)
{
goto v___jp_1739_;
}
else
{
lean_object* v___x_1745_; 
v___x_1745_ = lean_nat_sub(v_pos_1736_, v_p_u2080_1737_);
return v___x_1745_;
}
}
v___jp_1739_:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1740_ = lean_unsigned_to_nat(0u);
v___x_1741_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1742_ = l_panic___redArg(v___x_1740_, v___x_1741_);
return v___x_1742_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1746_, lean_object* v_p_u2080_1747_, lean_object* v_p_u2081_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_String_Slice_Pos_slice_x21___redArg(v_pos_1746_, v_p_u2080_1747_, v_p_u2081_1748_);
lean_dec(v_p_u2081_1748_);
lean_dec(v_p_u2080_1747_);
lean_dec(v_pos_1746_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21(lean_object* v_s_1750_, lean_object* v_pos_1751_, lean_object* v_p_u2080_1752_, lean_object* v_p_u2081_1753_){
_start:
{
uint8_t v___x_1758_; 
v___x_1758_ = lean_nat_dec_le(v_p_u2080_1752_, v_pos_1751_);
if (v___x_1758_ == 0)
{
goto v___jp_1754_;
}
else
{
uint8_t v___x_1759_; 
v___x_1759_ = lean_nat_dec_le(v_pos_1751_, v_p_u2081_1753_);
if (v___x_1759_ == 0)
{
goto v___jp_1754_;
}
else
{
lean_object* v___x_1760_; 
v___x_1760_ = lean_nat_sub(v_pos_1751_, v_p_u2080_1752_);
return v___x_1760_;
}
}
v___jp_1754_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1755_ = lean_unsigned_to_nat(0u);
v___x_1756_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1757_ = l_panic___redArg(v___x_1755_, v___x_1756_);
return v___x_1757_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___boxed(lean_object* v_s_1761_, lean_object* v_pos_1762_, lean_object* v_p_u2080_1763_, lean_object* v_p_u2081_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_String_Slice_Pos_slice_x21(v_s_1761_, v_pos_1762_, v_p_u2080_1763_, v_p_u2081_1764_);
lean_dec(v_p_u2081_1764_);
lean_dec(v_p_u2080_1763_);
lean_dec(v_pos_1762_);
lean_dec_ref(v_s_1761_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg(lean_object* v_pos_1766_, lean_object* v_p_u2080_1767_, lean_object* v_p_u2081_1768_){
_start:
{
uint8_t v___x_1773_; 
v___x_1773_ = lean_nat_dec_le(v_p_u2080_1767_, v_pos_1766_);
if (v___x_1773_ == 0)
{
goto v___jp_1769_;
}
else
{
uint8_t v___x_1774_; 
v___x_1774_ = lean_nat_dec_le(v_pos_1766_, v_p_u2081_1768_);
if (v___x_1774_ == 0)
{
goto v___jp_1769_;
}
else
{
lean_object* v___x_1775_; 
v___x_1775_ = lean_nat_sub(v_pos_1766_, v_p_u2080_1767_);
return v___x_1775_;
}
}
v___jp_1769_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1770_ = lean_unsigned_to_nat(0u);
v___x_1771_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1772_ = l_panic___redArg(v___x_1770_, v___x_1771_);
return v___x_1772_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1776_, lean_object* v_p_u2080_1777_, lean_object* v_p_u2081_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_String_Pos_slice_x21___redArg(v_pos_1776_, v_p_u2080_1777_, v_p_u2081_1778_);
lean_dec(v_p_u2081_1778_);
lean_dec(v_p_u2080_1777_);
lean_dec(v_pos_1776_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21(lean_object* v_s_1780_, lean_object* v_pos_1781_, lean_object* v_p_u2080_1782_, lean_object* v_p_u2081_1783_){
_start:
{
uint8_t v___x_1788_; 
v___x_1788_ = lean_nat_dec_le(v_p_u2080_1782_, v_pos_1781_);
if (v___x_1788_ == 0)
{
goto v___jp_1784_;
}
else
{
uint8_t v___x_1789_; 
v___x_1789_ = lean_nat_dec_le(v_pos_1781_, v_p_u2081_1783_);
if (v___x_1789_ == 0)
{
goto v___jp_1784_;
}
else
{
lean_object* v___x_1790_; 
v___x_1790_ = lean_nat_sub(v_pos_1781_, v_p_u2080_1782_);
return v___x_1790_;
}
}
v___jp_1784_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = lean_unsigned_to_nat(0u);
v___x_1786_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1787_ = l_panic___redArg(v___x_1785_, v___x_1786_);
return v___x_1787_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___boxed(lean_object* v_s_1791_, lean_object* v_pos_1792_, lean_object* v_p_u2080_1793_, lean_object* v_p_u2081_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_String_Pos_slice_x21(v_s_1791_, v_pos_1792_, v_p_u2080_1793_, v_p_u2081_1794_);
lean_dec(v_p_u2081_1794_);
lean_dec(v_p_u2080_1793_);
lean_dec(v_pos_1792_);
lean_dec_ref(v_s_1791_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract(lean_object* v_s_1796_, lean_object* v_p_u2080_1797_, lean_object* v_p_u2081_1798_){
_start:
{
lean_object* v_str_1799_; lean_object* v_startInclusive_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v_str_1799_ = lean_ctor_get(v_s_1796_, 0);
v_startInclusive_1800_ = lean_ctor_get(v_s_1796_, 1);
v___x_1801_ = lean_nat_add(v_startInclusive_1800_, v_p_u2080_1797_);
v___x_1802_ = lean_nat_add(v_startInclusive_1800_, v_p_u2081_1798_);
v___x_1803_ = lean_string_utf8_extract(v_str_1799_, v___x_1801_, v___x_1802_);
lean_dec(v___x_1802_);
lean_dec(v___x_1801_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract___boxed(lean_object* v_s_1804_, lean_object* v_p_u2080_1805_, lean_object* v_p_u2081_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_String_Slice_extract(v_s_1804_, v_p_u2080_1805_, v_p_u2081_1806_);
lean_dec(v_p_u2081_1806_);
lean_dec(v_p_u2080_1805_);
lean_dec_ref(v_s_1804_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn(lean_object* v_s_1808_, lean_object* v_p_1809_, lean_object* v_n_1810_){
_start:
{
lean_object* v_str_1811_; lean_object* v_startInclusive_1812_; lean_object* v_endExclusive_1813_; lean_object* v_zero_1814_; uint8_t v_isZero_1815_; 
v_str_1811_ = lean_ctor_get(v_s_1808_, 0);
v_startInclusive_1812_ = lean_ctor_get(v_s_1808_, 1);
v_endExclusive_1813_ = lean_ctor_get(v_s_1808_, 2);
v_zero_1814_ = lean_unsigned_to_nat(0u);
v_isZero_1815_ = lean_nat_dec_eq(v_n_1810_, v_zero_1814_);
if (v_isZero_1815_ == 1)
{
lean_dec(v_n_1810_);
return v_p_1809_;
}
else
{
lean_object* v___x_1816_; uint8_t v___x_1817_; lean_object* v_one_1818_; lean_object* v_n_1819_; 
v___x_1816_ = lean_nat_sub(v_endExclusive_1813_, v_startInclusive_1812_);
v___x_1817_ = lean_nat_dec_eq(v_p_1809_, v___x_1816_);
lean_dec(v___x_1816_);
v_one_1818_ = lean_unsigned_to_nat(1u);
v_n_1819_ = lean_nat_sub(v_n_1810_, v_one_1818_);
lean_dec(v_n_1810_);
if (v___x_1817_ == 0)
{
goto v___jp_1820_;
}
else
{
if (v_isZero_1815_ == 0)
{
lean_dec(v_n_1819_);
return v_p_1809_;
}
else
{
goto v___jp_1820_;
}
}
v___jp_1820_:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1821_ = lean_nat_add(v_startInclusive_1812_, v_p_1809_);
lean_dec(v_p_1809_);
v___x_1822_ = lean_string_utf8_next_fast(v_str_1811_, v___x_1821_);
lean_dec(v___x_1821_);
v___x_1823_ = lean_nat_sub(v___x_1822_, v_startInclusive_1812_);
v_p_1809_ = v___x_1823_;
v_n_1810_ = v_n_1819_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn___boxed(lean_object* v_s_1825_, lean_object* v_p_1826_, lean_object* v_n_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_String_Slice_Pos_nextn(v_s_1825_, v_p_1826_, v_n_1827_);
lean_dec_ref(v_s_1825_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_nextn(lean_object* v_s_1829_, lean_object* v_p_1830_, lean_object* v_n_1831_){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1832_ = lean_unsigned_to_nat(0u);
v___x_1833_ = lean_string_utf8_byte_size(v_s_1829_);
v___x_1834_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1834_, 0, v_s_1829_);
lean_ctor_set(v___x_1834_, 1, v___x_1832_);
lean_ctor_set(v___x_1834_, 2, v___x_1833_);
v___x_1835_ = l_String_Slice_Pos_nextn(v___x_1834_, v_p_1830_, v_n_1831_);
lean_dec_ref_known(v___x_1834_, 3);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(lean_object* v_n_1836_, lean_object* v_h__1_1837_, lean_object* v_h__2_1838_){
_start:
{
lean_object* v_zero_1839_; uint8_t v_isZero_1840_; 
v_zero_1839_ = lean_unsigned_to_nat(0u);
v_isZero_1840_ = lean_nat_dec_eq(v_n_1836_, v_zero_1839_);
if (v_isZero_1840_ == 1)
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
lean_dec(v_h__2_1838_);
v___x_1841_ = lean_box(0);
v___x_1842_ = lean_apply_1(v_h__1_1837_, v___x_1841_);
return v___x_1842_;
}
else
{
lean_object* v_one_1843_; lean_object* v_n_1844_; lean_object* v___x_1845_; 
lean_dec(v_h__1_1837_);
v_one_1843_ = lean_unsigned_to_nat(1u);
v_n_1844_ = lean_nat_sub(v_n_1836_, v_one_1843_);
v___x_1845_ = lean_apply_1(v_h__2_1838_, v_n_1844_);
return v___x_1845_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg___boxed(lean_object* v_n_1846_, lean_object* v_h__1_1847_, lean_object* v_h__2_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(v_n_1846_, v_h__1_1847_, v_h__2_1848_);
lean_dec(v_n_1846_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(lean_object* v_motive_1850_, lean_object* v_n_1851_, lean_object* v_h__1_1852_, lean_object* v_h__2_1853_){
_start:
{
lean_object* v_zero_1854_; uint8_t v_isZero_1855_; 
v_zero_1854_ = lean_unsigned_to_nat(0u);
v_isZero_1855_ = lean_nat_dec_eq(v_n_1851_, v_zero_1854_);
if (v_isZero_1855_ == 1)
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
lean_dec(v_h__2_1853_);
v___x_1856_ = lean_box(0);
v___x_1857_ = lean_apply_1(v_h__1_1852_, v___x_1856_);
return v___x_1857_;
}
else
{
lean_object* v_one_1858_; lean_object* v_n_1859_; lean_object* v___x_1860_; 
lean_dec(v_h__1_1852_);
v_one_1858_ = lean_unsigned_to_nat(1u);
v_n_1859_ = lean_nat_sub(v_n_1851_, v_one_1858_);
v___x_1860_ = lean_apply_1(v_h__2_1853_, v_n_1859_);
return v___x_1860_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___boxed(lean_object* v_motive_1861_, lean_object* v_n_1862_, lean_object* v_h__1_1863_, lean_object* v_h__2_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(v_motive_1861_, v_n_1862_, v_h__1_1863_, v_h__2_1864_);
lean_dec(v_n_1862_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next___boxed(lean_object* v_s_1868_, lean_object* v_p_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = lean_string_utf8_next(v_s_1868_, v_p_1869_);
lean_dec(v_p_1869_);
lean_dec_ref(v_s_1868_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_String_next___boxed(lean_object* v_s_1873_, lean_object* v_p_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = lean_string_utf8_next(v_s_1873_, v_p_1874_);
lean_dec(v_p_1874_);
lean_dec_ref(v_s_1873_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux(lean_object* v_x_1876_, lean_object* v_x_1877_, lean_object* v_x_1878_){
_start:
{
if (lean_obj_tag(v_x_1876_) == 0)
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
lean_dec(v_x_1877_);
v___x_1879_ = lean_unsigned_to_nat(1u);
v___x_1880_ = lean_nat_sub(v_x_1878_, v___x_1879_);
return v___x_1880_;
}
else
{
lean_object* v_head_1881_; lean_object* v_tail_1882_; uint32_t v___x_1883_; lean_object* v___x_1884_; lean_object* v_i_x27_1885_; uint8_t v___x_1886_; 
v_head_1881_ = lean_ctor_get(v_x_1876_, 0);
v_tail_1882_ = lean_ctor_get(v_x_1876_, 1);
v___x_1883_ = lean_unbox_uint32(v_head_1881_);
v___x_1884_ = l_Char_utf8Size(v___x_1883_);
v_i_x27_1885_ = lean_nat_add(v_x_1877_, v___x_1884_);
lean_dec(v___x_1884_);
v___x_1886_ = lean_nat_dec_le(v_x_1878_, v_i_x27_1885_);
if (v___x_1886_ == 0)
{
lean_dec(v_x_1877_);
v_x_1876_ = v_tail_1882_;
v_x_1877_ = v_i_x27_1885_;
goto _start;
}
else
{
lean_dec(v_i_x27_1885_);
return v_x_1877_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux___boxed(lean_object* v_x_1888_, lean_object* v_x_1889_, lean_object* v_x_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_String_Pos_Raw_utf8PrevAux(v_x_1888_, v_x_1889_, v_x_1890_);
lean_dec(v_x_1890_);
lean_dec(v_x_1888_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux(lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_String_Pos_Raw_utf8PrevAux(v_a_1892_, v_a_1893_, v_a_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux___boxed(lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_String_utf8PrevAux(v_a_1896_, v_a_1897_, v_a_1898_);
lean_dec(v_a_1898_);
lean_dec(v_a_1896_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_prev___boxed(lean_object* v_a_00___x40___internal___hyg_1902_, lean_object* v_a_00___x40___internal___hyg_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_1902_, v_a_00___x40___internal___hyg_1903_);
lean_dec(v_a_00___x40___internal___hyg_1903_);
lean_dec_ref(v_a_00___x40___internal___hyg_1902_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_String_prev___boxed(lean_object* v_a_00___x40___internal___hyg_1907_, lean_object* v_a_00___x40___internal___hyg_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_1907_, v_a_00___x40___internal___hyg_1908_);
lean_dec(v_a_00___x40___internal___hyg_1908_);
lean_dec_ref(v_a_00___x40___internal___hyg_1907_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_1912_, lean_object* v_a_00___x40___internal___hyg_1913_){
_start:
{
uint8_t v_res_1914_; lean_object* v_r_1915_; 
v_res_1914_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_1912_, v_a_00___x40___internal___hyg_1913_);
lean_dec(v_a_00___x40___internal___hyg_1913_);
lean_dec_ref(v_a_00___x40___internal___hyg_1912_);
v_r_1915_ = lean_box(v_res_1914_);
return v_r_1915_;
}
}
LEAN_EXPORT lean_object* l_String_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_1918_, lean_object* v_a_00___x40___internal___hyg_1919_){
_start:
{
uint8_t v_res_1920_; lean_object* v_r_1921_; 
v_res_1920_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_1918_, v_a_00___x40___internal___hyg_1919_);
lean_dec(v_a_00___x40___internal___hyg_1919_);
lean_dec_ref(v_a_00___x40___internal___hyg_1918_);
v_r_1921_ = lean_box(v_res_1920_);
return v_r_1921_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x27___boxed(lean_object* v_s_1925_, lean_object* v_p_1926_, lean_object* v_h_1927_){
_start:
{
uint32_t v_res_1928_; lean_object* v_r_1929_; 
v_res_1928_ = lean_string_utf8_get_fast(v_s_1925_, v_p_1926_);
lean_dec(v_p_1926_);
lean_dec_ref(v_s_1925_);
v_r_1929_ = lean_box_uint32(v_res_1928_);
return v_r_1929_;
}
}
LEAN_EXPORT lean_object* l_String_get_x27___boxed(lean_object* v_s_1933_, lean_object* v_p_1934_, lean_object* v_h_1935_){
_start:
{
uint32_t v_res_1936_; lean_object* v_r_1937_; 
v_res_1936_ = lean_string_utf8_get_fast(v_s_1933_, v_p_1934_);
lean_dec(v_p_1934_);
lean_dec_ref(v_s_1933_);
v_r_1937_ = lean_box_uint32(v_res_1936_);
return v_r_1937_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next_x27___boxed(lean_object* v_s_1941_, lean_object* v_p_1942_, lean_object* v_h_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = lean_string_utf8_next_fast(v_s_1941_, v_p_1942_);
lean_dec(v_p_1942_);
lean_dec_ref(v_s_1941_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_String_next_x27___boxed(lean_object* v_s_1948_, lean_object* v_p_1949_, lean_object* v_h_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = lean_string_utf8_next_fast(v_s_1948_, v_p_1949_);
lean_dec(v_p_1949_);
lean_dec_ref(v_s_1948_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter___redArg(lean_object* v_x_1952_, lean_object* v_x_1953_, lean_object* v_x_1954_, lean_object* v_h__1_1955_, lean_object* v_h__2_1956_){
_start:
{
if (lean_obj_tag(v_x_1952_) == 0)
{
lean_object* v___x_1957_; 
lean_dec(v_h__2_1956_);
v___x_1957_ = lean_apply_2(v_h__1_1955_, v_x_1953_, v_x_1954_);
return v___x_1957_;
}
else
{
lean_object* v_head_1958_; lean_object* v_tail_1959_; lean_object* v___x_1960_; 
lean_dec(v_h__1_1955_);
v_head_1958_ = lean_ctor_get(v_x_1952_, 0);
lean_inc(v_head_1958_);
v_tail_1959_ = lean_ctor_get(v_x_1952_, 1);
lean_inc(v_tail_1959_);
lean_dec_ref_known(v_x_1952_, 2);
v___x_1960_ = lean_apply_4(v_h__2_1956_, v_head_1958_, v_tail_1959_, v_x_1953_, v_x_1954_);
return v___x_1960_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter(lean_object* v_motive_1961_, lean_object* v_x_1962_, lean_object* v_x_1963_, lean_object* v_x_1964_, lean_object* v_h__1_1965_, lean_object* v_h__2_1966_){
_start:
{
if (lean_obj_tag(v_x_1962_) == 0)
{
lean_object* v___x_1967_; 
lean_dec(v_h__2_1966_);
v___x_1967_ = lean_apply_2(v_h__1_1965_, v_x_1963_, v_x_1964_);
return v___x_1967_;
}
else
{
lean_object* v_head_1968_; lean_object* v_tail_1969_; lean_object* v___x_1970_; 
lean_dec(v_h__1_1965_);
v_head_1968_ = lean_ctor_get(v_x_1962_, 0);
lean_inc(v_head_1968_);
v_tail_1969_ = lean_ctor_get(v_x_1962_, 1);
lean_inc(v_tail_1969_);
lean_dec_ref_known(v_x_1962_, 2);
v___x_1970_ = lean_apply_4(v_h__2_1966_, v_head_1968_, v_tail_1969_, v_x_1963_, v_x_1964_);
return v___x_1970_;
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop(lean_object* v_a_1971_, lean_object* v_b_1972_, lean_object* v_stopPos_1973_, lean_object* v_i_1974_){
_start:
{
uint8_t v___x_1975_; 
v___x_1975_ = lean_nat_dec_lt(v_i_1974_, v_stopPos_1973_);
if (v___x_1975_ == 0)
{
return v_i_1974_;
}
else
{
uint32_t v___x_1976_; uint32_t v___x_1977_; uint8_t v___x_1978_; 
v___x_1976_ = lean_string_utf8_get(v_a_1971_, v_i_1974_);
v___x_1977_ = lean_string_utf8_get(v_b_1972_, v_i_1974_);
v___x_1978_ = lean_uint32_dec_eq(v___x_1976_, v___x_1977_);
if (v___x_1978_ == 0)
{
return v_i_1974_;
}
else
{
lean_object* v___x_1979_; 
v___x_1979_ = lean_string_utf8_next(v_a_1971_, v_i_1974_);
lean_dec(v_i_1974_);
v_i_1974_ = v___x_1979_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop___boxed(lean_object* v_a_1981_, lean_object* v_b_1982_, lean_object* v_stopPos_1983_, lean_object* v_i_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_String_firstDiffPos_loop(v_a_1981_, v_b_1982_, v_stopPos_1983_, v_i_1984_);
lean_dec(v_stopPos_1983_);
lean_dec_ref(v_b_1982_);
lean_dec_ref(v_a_1981_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos(lean_object* v_a_1986_, lean_object* v_b_1987_){
_start:
{
lean_object* v___y_1989_; lean_object* v___x_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v___x_1992_ = lean_string_utf8_byte_size(v_a_1986_);
v___x_1993_ = lean_string_utf8_byte_size(v_b_1987_);
v___x_1994_ = lean_nat_dec_le(v___x_1992_, v___x_1993_);
if (v___x_1994_ == 0)
{
v___y_1989_ = v___x_1993_;
goto v___jp_1988_;
}
else
{
v___y_1989_ = v___x_1992_;
goto v___jp_1988_;
}
v___jp_1988_:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = lean_unsigned_to_nat(0u);
v___x_1991_ = l_String_firstDiffPos_loop(v_a_1986_, v_b_1987_, v___y_1989_, v___x_1990_);
lean_dec(v___y_1989_);
return v___x_1991_;
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos___boxed(lean_object* v_a_1995_, lean_object* v_b_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_String_firstDiffPos(v_a_1995_, v_b_1996_);
lean_dec_ref(v_b_1996_);
lean_dec_ref(v_a_1995_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082(lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_){
_start:
{
if (lean_obj_tag(v_a_1998_) == 0)
{
return v_a_1998_;
}
else
{
lean_object* v_head_2001_; lean_object* v_tail_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2015_; 
v_head_2001_ = lean_ctor_get(v_a_1998_, 0);
v_tail_2002_ = lean_ctor_get(v_a_1998_, 1);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_a_1998_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2004_ = v_a_1998_;
v_isShared_2005_ = v_isSharedCheck_2015_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_tail_2002_);
lean_inc(v_head_2001_);
lean_dec(v_a_1998_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2015_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
uint8_t v___x_2006_; 
v___x_2006_ = lean_nat_dec_eq(v_a_1999_, v_a_2000_);
if (v___x_2006_ == 0)
{
uint32_t v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2012_; 
v___x_2007_ = lean_unbox_uint32(v_head_2001_);
v___x_2008_ = l_Char_utf8Size(v___x_2007_);
v___x_2009_ = lean_nat_add(v_a_1999_, v___x_2008_);
lean_dec(v___x_2008_);
v___x_2010_ = l_String_Pos_Raw_extract_go_u2082(v_tail_2002_, v___x_2009_, v_a_2000_);
lean_dec(v___x_2009_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 1, v___x_2010_);
v___x_2012_ = v___x_2004_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_head_2001_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
else
{
lean_object* v___x_2014_; 
lean_del_object(v___x_2004_);
lean_dec(v_tail_2002_);
lean_dec(v_head_2001_);
v___x_2014_ = lean_box(0);
return v___x_2014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082___boxed(lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_String_Pos_Raw_extract_go_u2082(v_a_2016_, v_a_2017_, v_a_2018_);
lean_dec(v_a_2018_);
lean_dec(v_a_2017_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081(lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_){
_start:
{
if (lean_obj_tag(v_a_2020_) == 0)
{
lean_dec(v_a_2021_);
return v_a_2020_;
}
else
{
lean_object* v_head_2024_; lean_object* v_tail_2025_; uint8_t v___x_2026_; 
v_head_2024_ = lean_ctor_get(v_a_2020_, 0);
v_tail_2025_ = lean_ctor_get(v_a_2020_, 1);
v___x_2026_ = lean_nat_dec_eq(v_a_2021_, v_a_2022_);
if (v___x_2026_ == 0)
{
uint32_t v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
lean_inc(v_tail_2025_);
lean_inc(v_head_2024_);
lean_dec_ref_known(v_a_2020_, 2);
v___x_2027_ = lean_unbox_uint32(v_head_2024_);
lean_dec(v_head_2024_);
v___x_2028_ = l_Char_utf8Size(v___x_2027_);
v___x_2029_ = lean_nat_add(v_a_2021_, v___x_2028_);
lean_dec(v___x_2028_);
lean_dec(v_a_2021_);
v_a_2020_ = v_tail_2025_;
v_a_2021_ = v___x_2029_;
goto _start;
}
else
{
lean_object* v___x_2031_; 
v___x_2031_ = l_String_Pos_Raw_extract_go_u2082(v_a_2020_, v_a_2021_, v_a_2023_);
lean_dec(v_a_2021_);
return v___x_2031_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081___boxed(lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_String_Pos_Raw_extract_go_u2081(v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
lean_dec(v_a_2035_);
lean_dec(v_a_2034_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract___boxed(lean_object* v_a_00___x40___internal___hyg_2040_, lean_object* v_a_00___x40___internal___hyg_2041_, lean_object* v_a_00___x40___internal___hyg_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = lean_string_utf8_extract(v_a_00___x40___internal___hyg_2040_, v_a_00___x40___internal___hyg_2041_, v_a_00___x40___internal___hyg_2042_);
lean_dec(v_a_00___x40___internal___hyg_2042_);
lean_dec(v_a_00___x40___internal___hyg_2041_);
lean_dec_ref(v_a_00___x40___internal___hyg_2040_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux(lean_object* v_s_2044_, lean_object* v_pos_2045_, lean_object* v_i_2046_, lean_object* v_offset_2047_){
_start:
{
uint8_t v___x_2048_; 
v___x_2048_ = lean_nat_dec_le(v_pos_2045_, v_i_2046_);
if (v___x_2048_ == 0)
{
uint8_t v___x_2049_; 
v___x_2049_ = lean_string_utf8_at_end(v_s_2044_, v_i_2046_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2050_ = lean_string_utf8_next(v_s_2044_, v_i_2046_);
lean_dec(v_i_2046_);
v___x_2051_ = lean_unsigned_to_nat(1u);
v___x_2052_ = lean_nat_add(v_offset_2047_, v___x_2051_);
lean_dec(v_offset_2047_);
v_i_2046_ = v___x_2050_;
v_offset_2047_ = v___x_2052_;
goto _start;
}
else
{
lean_dec(v_i_2046_);
return v_offset_2047_;
}
}
else
{
lean_dec(v_i_2046_);
return v_offset_2047_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux___boxed(lean_object* v_s_2054_, lean_object* v_pos_2055_, lean_object* v_i_2056_, lean_object* v_offset_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2054_, v_pos_2055_, v_i_2056_, v_offset_2057_);
lean_dec(v_pos_2055_);
lean_dec_ref(v_s_2054_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos(lean_object* v_s_2059_, lean_object* v_pos_2060_){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = lean_unsigned_to_nat(0u);
v___x_2062_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2059_, v_pos_2060_, v___x_2061_, v___x_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos___boxed(lean_object* v_s_2063_, lean_object* v_pos_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_String_Pos_Raw_offsetOfPos(v_s_2063_, v_pos_2064_);
lean_dec(v_pos_2064_);
lean_dec_ref(v_s_2063_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos(lean_object* v_s_2066_, lean_object* v_pos_2067_){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = lean_unsigned_to_nat(0u);
v___x_2069_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2066_, v_pos_2067_, v___x_2068_, v___x_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos___boxed(lean_object* v_s_2070_, lean_object* v_pos_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_String_offsetOfPos(v_s_2070_, v_pos_2071_);
lean_dec(v_pos_2071_);
lean_dec_ref(v_s_2070_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* lean_string_offsetofpos(lean_object* v_s_2073_, lean_object* v_pos_2074_){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = lean_unsigned_to_nat(0u);
v___x_2076_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2073_, v_pos_2074_, v___x_2075_, v___x_2075_);
lean_dec(v_pos_2074_);
lean_dec_ref(v_s_2073_);
return v___x_2076_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(lean_object* v_s1_2077_, lean_object* v_s2_2078_, lean_object* v_off1_2079_, lean_object* v_off2_2080_, lean_object* v_stop1_2081_){
_start:
{
uint8_t v___x_2082_; 
v___x_2082_ = lean_nat_dec_lt(v_off1_2079_, v_stop1_2081_);
if (v___x_2082_ == 0)
{
uint8_t v___x_2083_; 
lean_dec(v_off2_2080_);
lean_dec(v_off1_2079_);
v___x_2083_ = 1;
return v___x_2083_;
}
else
{
uint32_t v_c_u2081_2084_; uint32_t v_c_u2082_2085_; uint8_t v___x_2086_; 
v_c_u2081_2084_ = lean_string_utf8_get(v_s1_2077_, v_off1_2079_);
v_c_u2082_2085_ = lean_string_utf8_get(v_s2_2078_, v_off2_2080_);
v___x_2086_ = lean_uint32_dec_eq(v_c_u2081_2084_, v_c_u2082_2085_);
if (v___x_2086_ == 0)
{
lean_dec(v_off2_2080_);
lean_dec(v_off1_2079_);
return v___x_2086_;
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2087_ = l_Char_utf8Size(v_c_u2081_2084_);
v___x_2088_ = lean_nat_add(v_off1_2079_, v___x_2087_);
lean_dec(v___x_2087_);
lean_dec(v_off1_2079_);
v___x_2089_ = l_Char_utf8Size(v_c_u2082_2085_);
v___x_2090_ = lean_nat_add(v_off2_2080_, v___x_2089_);
lean_dec(v___x_2089_);
lean_dec(v_off2_2080_);
v_off1_2079_ = v___x_2088_;
v_off2_2080_ = v___x_2090_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop___boxed(lean_object* v_s1_2092_, lean_object* v_s2_2093_, lean_object* v_off1_2094_, lean_object* v_off2_2095_, lean_object* v_stop1_2096_){
_start:
{
uint8_t v_res_2097_; lean_object* v_r_2098_; 
v_res_2097_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2092_, v_s2_2093_, v_off1_2094_, v_off2_2095_, v_stop1_2096_);
lean_dec(v_stop1_2096_);
lean_dec_ref(v_s2_2093_);
lean_dec_ref(v_s1_2092_);
v_r_2098_ = lean_box(v_res_2097_);
return v_r_2098_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_substrEq(lean_object* v_s1_2099_, lean_object* v_pos1_2100_, lean_object* v_s2_2101_, lean_object* v_pos2_2102_, lean_object* v_sz_2103_){
_start:
{
uint8_t v___y_2105_; lean_object* v___x_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; 
v___x_2108_ = lean_nat_add(v_pos1_2100_, v_sz_2103_);
v___x_2109_ = lean_string_utf8_byte_size(v_s1_2099_);
v___x_2110_ = lean_nat_dec_le(v___x_2108_, v___x_2109_);
lean_dec(v___x_2108_);
if (v___x_2110_ == 0)
{
v___y_2105_ = v___x_2110_;
goto v___jp_2104_;
}
else
{
lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2111_ = lean_nat_add(v_pos2_2102_, v_sz_2103_);
v___x_2112_ = lean_string_utf8_byte_size(v_s2_2101_);
v___x_2113_ = lean_nat_dec_le(v___x_2111_, v___x_2112_);
lean_dec(v___x_2111_);
v___y_2105_ = v___x_2113_;
goto v___jp_2104_;
}
v___jp_2104_:
{
if (v___y_2105_ == 0)
{
lean_dec(v_pos2_2102_);
lean_dec(v_pos1_2100_);
return v___y_2105_;
}
else
{
lean_object* v___x_2106_; uint8_t v___x_2107_; 
v___x_2106_ = lean_nat_add(v_pos1_2100_, v_sz_2103_);
v___x_2107_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2099_, v_s2_2101_, v_pos1_2100_, v_pos2_2102_, v___x_2106_);
lean_dec(v___x_2106_);
return v___x_2107_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_substrEq___boxed(lean_object* v_s1_2114_, lean_object* v_pos1_2115_, lean_object* v_s2_2116_, lean_object* v_pos2_2117_, lean_object* v_sz_2118_){
_start:
{
uint8_t v_res_2119_; lean_object* v_r_2120_; 
v_res_2119_ = l_String_Pos_Raw_substrEq(v_s1_2114_, v_pos1_2115_, v_s2_2116_, v_pos2_2117_, v_sz_2118_);
lean_dec(v_sz_2118_);
lean_dec_ref(v_s2_2116_);
lean_dec_ref(v_s1_2114_);
v_r_2120_ = lean_box(v_res_2119_);
return v_r_2120_;
}
}
LEAN_EXPORT uint8_t l_String_substrEq(lean_object* v_s1_2121_, lean_object* v_pos1_2122_, lean_object* v_s2_2123_, lean_object* v_pos2_2124_, lean_object* v_sz_2125_){
_start:
{
uint8_t v___x_2126_; 
v___x_2126_ = l_String_Pos_Raw_substrEq(v_s1_2121_, v_pos1_2122_, v_s2_2123_, v_pos2_2124_, v_sz_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_String_substrEq___boxed(lean_object* v_s1_2127_, lean_object* v_pos1_2128_, lean_object* v_s2_2129_, lean_object* v_pos2_2130_, lean_object* v_sz_2131_){
_start:
{
uint8_t v_res_2132_; lean_object* v_r_2133_; 
v_res_2132_ = l_String_substrEq(v_s1_2127_, v_pos1_2128_, v_s2_2129_, v_pos2_2130_, v_sz_2131_);
lean_dec(v_sz_2131_);
lean_dec_ref(v_s2_2129_);
lean_dec_ref(v_s1_2127_);
v_r_2133_ = lean_box(v_res_2132_);
return v_r_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object* v_x_2134_, lean_object* v_x_2135_, lean_object* v_h__1_2136_){
_start:
{
lean_object* v___x_2137_; 
v___x_2137_ = lean_apply_2(v_h__1_2136_, v_x_2134_, v_x_2135_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object* v_motive_2138_, lean_object* v_x_2139_, lean_object* v_x_2140_, lean_object* v_h__1_2141_){
_start:
{
lean_object* v___x_2142_; 
v___x_2142_ = lean_apply_2(v_h__1_2141_, v_x_2139_, v_x_2140_);
return v___x_2142_;
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
