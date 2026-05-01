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
lean_dec_ref(v_x_154_);
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
LEAN_EXPORT lean_object* l_String_length___boxed(lean_object* v_b_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = lean_string_length(v_b_375_);
lean_dec_ref(v_b_375_);
return v_res_376_;
}
}
static lean_object* _init_l_String_instLT(void){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lean_box(0);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_String_decidableLT___boxed(lean_object* v_s_u2081_380_, lean_object* v_s_u2082_381_){
_start:
{
uint8_t v_res_382_; lean_object* v_r_383_; 
v_res_382_ = lean_string_dec_lt(v_s_u2081_380_, v_s_u2082_381_);
lean_dec_ref(v_s_u2082_381_);
lean_dec_ref(v_s_u2081_380_);
v_r_383_ = lean_box(v_res_382_);
return v_r_383_;
}
}
static lean_object* _init_l_String_instLE(void){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = lean_box(0);
return v___x_384_;
}
}
LEAN_EXPORT uint8_t l_String_decLE(lean_object* v_s_u2081_385_, lean_object* v_s_u2082_386_){
_start:
{
uint8_t v___x_387_; 
v___x_387_ = lean_string_dec_lt(v_s_u2082_386_, v_s_u2081_385_);
if (v___x_387_ == 0)
{
uint8_t v___x_388_; 
v___x_388_ = 1;
return v___x_388_;
}
else
{
uint8_t v___x_389_; 
v___x_389_ = 0;
return v___x_389_;
}
}
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
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValid___boxed(lean_object* v_s_396_, lean_object* v_p_397_){
_start:
{
uint8_t v_res_398_; lean_object* v_r_399_; 
v_res_398_ = lean_string_is_valid_pos(v_s_396_, v_p_397_);
lean_dec(v_p_397_);
lean_dec_ref(v_s_396_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsValid(lean_object* v_s_400_, lean_object* v_p_401_){
_start:
{
uint8_t v___x_402_; 
v___x_402_ = lean_string_is_valid_pos(v_s_400_, v_p_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsValid___boxed(lean_object* v_s_403_, lean_object* v_p_404_){
_start:
{
uint8_t v_res_405_; lean_object* v_r_406_; 
v_res_405_ = l_String_instDecidableIsValid(v_s_403_, v_p_404_);
lean_dec(v_p_404_);
lean_dec_ref(v_s_403_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
LEAN_EXPORT lean_object* l_String_extract___boxed(lean_object* v_s_410_, lean_object* v_b_411_, lean_object* v_e_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = lean_string_utf8_extract(v_s_410_, v_b_411_, v_e_412_);
lean_dec(v_e_412_);
lean_dec(v_b_411_);
lean_dec_ref(v_s_410_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_extract(lean_object* v_s_414_, lean_object* v_b_415_, lean_object* v_e_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = lean_string_utf8_extract(v_s_414_, v_b_415_, v_e_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_extract___boxed(lean_object* v_s_418_, lean_object* v_b_419_, lean_object* v_e_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_String_Pos_extract(v_s_418_, v_b_419_, v_e_420_);
lean_dec(v_e_420_);
lean_dec(v_b_419_);
lean_dec_ref(v_s_418_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_copy(lean_object* v_s_422_){
_start:
{
lean_object* v_str_423_; lean_object* v_startInclusive_424_; lean_object* v_endExclusive_425_; lean_object* v___x_426_; 
v_str_423_ = lean_ctor_get(v_s_422_, 0);
v_startInclusive_424_ = lean_ctor_get(v_s_422_, 1);
v_endExclusive_425_ = lean_ctor_get(v_s_422_, 2);
v___x_426_ = lean_string_utf8_extract(v_str_423_, v_startInclusive_424_, v_endExclusive_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_copy___boxed(lean_object* v_s_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_String_Slice_copy(v_s_427_);
lean_dec_ref(v_s_427_);
return v_res_428_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_isValidForSlice(lean_object* v_s_429_, lean_object* v_p_430_){
_start:
{
lean_object* v_str_431_; lean_object* v_startInclusive_432_; lean_object* v_endExclusive_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v_str_431_ = lean_ctor_get(v_s_429_, 0);
v_startInclusive_432_ = lean_ctor_get(v_s_429_, 1);
v_endExclusive_433_ = lean_ctor_get(v_s_429_, 2);
v___x_434_ = lean_nat_sub(v_endExclusive_433_, v_startInclusive_432_);
v___x_435_ = lean_nat_dec_lt(v_p_430_, v___x_434_);
if (v___x_435_ == 0)
{
uint8_t v___x_436_; 
v___x_436_ = lean_nat_dec_eq(v_p_430_, v___x_434_);
lean_dec(v___x_434_);
return v___x_436_;
}
else
{
lean_object* v___x_437_; uint8_t v___x_438_; uint8_t v___x_439_; 
lean_dec(v___x_434_);
v___x_437_ = lean_nat_add(v_startInclusive_432_, v_p_430_);
v___x_438_ = lean_string_get_byte_fast(v_str_431_, v___x_437_);
v___x_439_ = l_UInt8_instDecidableIsUTF8FirstByte___aux__1(v___x_438_);
return v___x_439_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValidForSlice___boxed(lean_object* v_s_440_, lean_object* v_p_441_){
_start:
{
uint8_t v_res_442_; lean_object* v_r_443_; 
v_res_442_ = l_String_Pos_Raw_isValidForSlice(v_s_440_, v_p_441_);
lean_dec(v_p_441_);
lean_dec_ref(v_s_440_);
v_r_443_ = lean_box(v_res_442_);
return v_r_443_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsValidForSlice(lean_object* v_s_444_, lean_object* v_p_445_){
_start:
{
uint8_t v___x_446_; 
v___x_446_ = l_String_Pos_Raw_isValidForSlice(v_s_444_, v_p_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsValidForSlice___boxed(lean_object* v_s_447_, lean_object* v_p_448_){
_start:
{
uint8_t v_res_449_; lean_object* v_r_450_; 
v_res_449_ = l_String_instDecidableIsValidForSlice(v_s_447_, v_p_448_);
lean_dec(v_p_448_);
lean_dec_ref(v_s_447_);
v_r_450_ = lean_box(v_res_449_);
return v_r_450_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str(lean_object* v_s_451_, lean_object* v_pos_452_){
_start:
{
lean_object* v_startInclusive_453_; lean_object* v___x_454_; 
v_startInclusive_453_ = lean_ctor_get(v_s_451_, 1);
v___x_454_ = lean_nat_add(v_startInclusive_453_, v_pos_452_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str___boxed(lean_object* v_s_455_, lean_object* v_pos_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_String_Slice_Pos_str(v_s_455_, v_pos_456_);
lean_dec(v_pos_456_);
lean_dec_ref(v_s_455_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg(lean_object* v_s_458_, lean_object* v_pos_459_){
_start:
{
lean_object* v_startInclusive_460_; lean_object* v___x_461_; 
v_startInclusive_460_ = lean_ctor_get(v_s_458_, 1);
v___x_461_ = lean_nat_sub(v_pos_459_, v_startInclusive_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg___boxed(lean_object* v_s_462_, lean_object* v_pos_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_String_Slice_Pos_ofStr___redArg(v_s_462_, v_pos_463_);
lean_dec(v_pos_463_);
lean_dec_ref(v_s_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr(lean_object* v_s_465_, lean_object* v_pos_466_, lean_object* v_h_u2081_467_, lean_object* v_h_u2082_468_){
_start:
{
lean_object* v_startInclusive_469_; lean_object* v___x_470_; 
v_startInclusive_469_ = lean_ctor_get(v_s_465_, 1);
v___x_470_ = lean_nat_sub(v_pos_466_, v_startInclusive_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___boxed(lean_object* v_s_471_, lean_object* v_pos_472_, lean_object* v_h_u2081_473_, lean_object* v_h_u2082_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_String_Slice_Pos_ofStr(v_s_471_, v_pos_472_, v_h_u2081_473_, v_h_u2082_474_);
lean_dec(v_pos_472_);
lean_dec_ref(v_s_471_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom(lean_object* v_s_476_, lean_object* v_pos_477_){
_start:
{
lean_object* v_str_478_; lean_object* v_startInclusive_479_; lean_object* v_endExclusive_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_488_; 
v_str_478_ = lean_ctor_get(v_s_476_, 0);
v_startInclusive_479_ = lean_ctor_get(v_s_476_, 1);
v_endExclusive_480_ = lean_ctor_get(v_s_476_, 2);
v_isSharedCheck_488_ = !lean_is_exclusive(v_s_476_);
if (v_isSharedCheck_488_ == 0)
{
v___x_482_ = v_s_476_;
v_isShared_483_ = v_isSharedCheck_488_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_endExclusive_480_);
lean_inc(v_startInclusive_479_);
lean_inc(v_str_478_);
lean_dec(v_s_476_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_488_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_484_ = lean_nat_add(v_startInclusive_479_, v_pos_477_);
lean_dec(v_startInclusive_479_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 1, v___x_484_);
v___x_486_ = v___x_482_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_str_478_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_487_, 2, v_endExclusive_480_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom___boxed(lean_object* v_s_489_, lean_object* v_pos_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_String_Slice_sliceFrom(v_s_489_, v_pos_490_);
lean_dec(v_pos_490_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStart(lean_object* v_s_492_, lean_object* v_pos_493_){
_start:
{
lean_object* v_str_494_; lean_object* v_startInclusive_495_; lean_object* v_endExclusive_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_504_; 
v_str_494_ = lean_ctor_get(v_s_492_, 0);
v_startInclusive_495_ = lean_ctor_get(v_s_492_, 1);
v_endExclusive_496_ = lean_ctor_get(v_s_492_, 2);
v_isSharedCheck_504_ = !lean_is_exclusive(v_s_492_);
if (v_isSharedCheck_504_ == 0)
{
v___x_498_ = v_s_492_;
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_endExclusive_496_);
lean_inc(v_startInclusive_495_);
lean_inc(v_str_494_);
lean_dec(v_s_492_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_500_ = lean_nat_add(v_startInclusive_495_, v_pos_493_);
lean_dec(v_startInclusive_495_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 1, v___x_500_);
v___x_502_ = v___x_498_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_str_494_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v___x_500_);
lean_ctor_set(v_reuseFailAlloc_503_, 2, v_endExclusive_496_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStart___boxed(lean_object* v_s_505_, lean_object* v_pos_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_String_Slice_replaceStart(v_s_505_, v_pos_506_);
lean_dec(v_pos_506_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceTo(lean_object* v_s_508_, lean_object* v_pos_509_){
_start:
{
lean_object* v_str_510_; lean_object* v_startInclusive_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_519_; 
v_str_510_ = lean_ctor_get(v_s_508_, 0);
v_startInclusive_511_ = lean_ctor_get(v_s_508_, 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v_s_508_);
if (v_isSharedCheck_519_ == 0)
{
lean_object* v_unused_520_; 
v_unused_520_ = lean_ctor_get(v_s_508_, 2);
lean_dec(v_unused_520_);
v___x_513_ = v_s_508_;
v_isShared_514_ = v_isSharedCheck_519_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_startInclusive_511_);
lean_inc(v_str_510_);
lean_dec(v_s_508_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_519_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_515_ = lean_nat_add(v_startInclusive_511_, v_pos_509_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 2, v___x_515_);
v___x_517_ = v___x_513_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_str_510_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_startInclusive_511_);
lean_ctor_set(v_reuseFailAlloc_518_, 2, v___x_515_);
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
LEAN_EXPORT lean_object* l_String_Slice_sliceTo___boxed(lean_object* v_s_521_, lean_object* v_pos_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_String_Slice_sliceTo(v_s_521_, v_pos_522_);
lean_dec(v_pos_522_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd(lean_object* v_s_524_, lean_object* v_pos_525_){
_start:
{
lean_object* v_str_526_; lean_object* v_startInclusive_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_535_; 
v_str_526_ = lean_ctor_get(v_s_524_, 0);
v_startInclusive_527_ = lean_ctor_get(v_s_524_, 1);
v_isSharedCheck_535_ = !lean_is_exclusive(v_s_524_);
if (v_isSharedCheck_535_ == 0)
{
lean_object* v_unused_536_; 
v_unused_536_ = lean_ctor_get(v_s_524_, 2);
lean_dec(v_unused_536_);
v___x_529_ = v_s_524_;
v_isShared_530_ = v_isSharedCheck_535_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_startInclusive_527_);
lean_inc(v_str_526_);
lean_dec(v_s_524_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_535_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_531_ = lean_nat_add(v_startInclusive_527_, v_pos_525_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 2, v___x_531_);
v___x_533_ = v___x_529_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_str_526_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_startInclusive_527_);
lean_ctor_set(v_reuseFailAlloc_534_, 2, v___x_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd___boxed(lean_object* v_s_537_, lean_object* v_pos_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_String_Slice_replaceEnd(v_s_537_, v_pos_538_);
lean_dec(v_pos_538_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg(lean_object* v_s_540_, lean_object* v_newStart_541_, lean_object* v_newEnd_542_){
_start:
{
lean_object* v_str_543_; lean_object* v_startInclusive_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_553_; 
v_str_543_ = lean_ctor_get(v_s_540_, 0);
v_startInclusive_544_ = lean_ctor_get(v_s_540_, 1);
v_isSharedCheck_553_ = !lean_is_exclusive(v_s_540_);
if (v_isSharedCheck_553_ == 0)
{
lean_object* v_unused_554_; 
v_unused_554_ = lean_ctor_get(v_s_540_, 2);
lean_dec(v_unused_554_);
v___x_546_ = v_s_540_;
v_isShared_547_ = v_isSharedCheck_553_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_startInclusive_544_);
lean_inc(v_str_543_);
lean_dec(v_s_540_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_553_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_548_ = lean_nat_add(v_startInclusive_544_, v_newStart_541_);
v___x_549_ = lean_nat_add(v_startInclusive_544_, v_newEnd_542_);
lean_dec(v_startInclusive_544_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 2, v___x_549_);
lean_ctor_set(v___x_546_, 1, v___x_548_);
v___x_551_ = v___x_546_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_str_543_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg___boxed(lean_object* v_s_555_, lean_object* v_newStart_556_, lean_object* v_newEnd_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_String_Slice_slice___redArg(v_s_555_, v_newStart_556_, v_newEnd_557_);
lean_dec(v_newEnd_557_);
lean_dec(v_newStart_556_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice(lean_object* v_s_559_, lean_object* v_newStart_560_, lean_object* v_newEnd_561_, lean_object* v_h_562_){
_start:
{
lean_object* v_str_563_; lean_object* v_startInclusive_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_573_; 
v_str_563_ = lean_ctor_get(v_s_559_, 0);
v_startInclusive_564_ = lean_ctor_get(v_s_559_, 1);
v_isSharedCheck_573_ = !lean_is_exclusive(v_s_559_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; 
v_unused_574_ = lean_ctor_get(v_s_559_, 2);
lean_dec(v_unused_574_);
v___x_566_ = v_s_559_;
v_isShared_567_ = v_isSharedCheck_573_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_startInclusive_564_);
lean_inc(v_str_563_);
lean_dec(v_s_559_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_573_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_568_ = lean_nat_add(v_startInclusive_564_, v_newStart_560_);
v___x_569_ = lean_nat_add(v_startInclusive_564_, v_newEnd_561_);
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
LEAN_EXPORT lean_object* l_String_Slice_slice___boxed(lean_object* v_s_575_, lean_object* v_newStart_576_, lean_object* v_newEnd_577_, lean_object* v_h_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_String_Slice_slice(v_s_575_, v_newStart_576_, v_newEnd_577_, v_h_578_);
lean_dec(v_newEnd_577_);
lean_dec(v_newStart_576_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg(lean_object* v_s_580_, lean_object* v_newStart_581_, lean_object* v_newEnd_582_){
_start:
{
lean_object* v_str_583_; lean_object* v_startInclusive_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_593_; 
v_str_583_ = lean_ctor_get(v_s_580_, 0);
v_startInclusive_584_ = lean_ctor_get(v_s_580_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v_s_580_);
if (v_isSharedCheck_593_ == 0)
{
lean_object* v_unused_594_; 
v_unused_594_ = lean_ctor_get(v_s_580_, 2);
lean_dec(v_unused_594_);
v___x_586_ = v_s_580_;
v_isShared_587_ = v_isSharedCheck_593_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_startInclusive_584_);
lean_inc(v_str_583_);
lean_dec(v_s_580_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_593_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_588_ = lean_nat_add(v_startInclusive_584_, v_newStart_581_);
v___x_589_ = lean_nat_add(v_startInclusive_584_, v_newEnd_582_);
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
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg___boxed(lean_object* v_s_595_, lean_object* v_newStart_596_, lean_object* v_newEnd_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_String_Slice_replaceStartEnd___redArg(v_s_595_, v_newStart_596_, v_newEnd_597_);
lean_dec(v_newEnd_597_);
lean_dec(v_newStart_596_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd(lean_object* v_s_599_, lean_object* v_newStart_600_, lean_object* v_newEnd_601_, lean_object* v_h_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_String_Slice_replaceStartEnd___redArg(v_s_599_, v_newStart_600_, v_newEnd_601_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___boxed(lean_object* v_s_604_, lean_object* v_newStart_605_, lean_object* v_newEnd_606_, lean_object* v_h_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_String_Slice_replaceStartEnd(v_s_604_, v_newStart_605_, v_newEnd_606_, v_h_607_);
lean_dec(v_newEnd_606_);
lean_dec(v_newStart_605_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f(lean_object* v_s_609_, lean_object* v_newStart_610_, lean_object* v_newEnd_611_){
_start:
{
uint8_t v___x_612_; 
v___x_612_ = lean_nat_dec_le(v_newStart_610_, v_newEnd_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; 
lean_dec_ref(v_s_609_);
v___x_613_ = lean_box(0);
return v___x_613_;
}
else
{
lean_object* v_str_614_; lean_object* v_startInclusive_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_625_; 
v_str_614_ = lean_ctor_get(v_s_609_, 0);
v_startInclusive_615_ = lean_ctor_get(v_s_609_, 1);
v_isSharedCheck_625_ = !lean_is_exclusive(v_s_609_);
if (v_isSharedCheck_625_ == 0)
{
lean_object* v_unused_626_; 
v_unused_626_ = lean_ctor_get(v_s_609_, 2);
lean_dec(v_unused_626_);
v___x_617_ = v_s_609_;
v_isShared_618_ = v_isSharedCheck_625_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_startInclusive_615_);
lean_inc(v_str_614_);
lean_dec(v_s_609_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_625_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_619_ = lean_nat_add(v_startInclusive_615_, v_newStart_610_);
v___x_620_ = lean_nat_add(v_startInclusive_615_, v_newEnd_611_);
lean_dec(v_startInclusive_615_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 2, v___x_620_);
lean_ctor_set(v___x_617_, 1, v___x_619_);
v___x_622_ = v___x_617_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_str_614_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v___x_620_);
v___x_622_ = v_reuseFailAlloc_624_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_623_; 
v___x_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f___boxed(lean_object* v_s_627_, lean_object* v_newStart_628_, lean_object* v_newEnd_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_String_Slice_slice_x3f(v_s_627_, v_newStart_628_, v_newEnd_629_);
lean_dec(v_newEnd_629_);
lean_dec(v_newStart_628_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_slice_x21_spec__0(lean_object* v_msg_631_){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = l_String_instInhabitedSlice;
v___x_633_ = lean_panic_fn_borrowed(v___x_632_, v_msg_631_);
return v___x_633_;
}
}
static lean_object* _init_l_String_Slice_slice_x21___closed__2(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_636_ = ((lean_object*)(l_String_Slice_slice_x21___closed__1));
v___x_637_ = lean_unsigned_to_nat(4u);
v___x_638_ = lean_unsigned_to_nat(1126u);
v___x_639_ = ((lean_object*)(l_String_Slice_slice_x21___closed__0));
v___x_640_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_641_ = l_mkPanicMessageWithDecl(v___x_640_, v___x_639_, v___x_638_, v___x_637_, v___x_636_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x21(lean_object* v_s_642_, lean_object* v_newStart_643_, lean_object* v_newEnd_644_){
_start:
{
uint8_t v___x_645_; 
v___x_645_ = lean_nat_dec_le(v_newStart_643_, v_newEnd_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; 
lean_dec_ref(v_s_642_);
v___x_646_ = lean_obj_once(&l_String_Slice_slice_x21___closed__2, &l_String_Slice_slice_x21___closed__2_once, _init_l_String_Slice_slice_x21___closed__2);
v___x_647_ = l_panic___at___00String_Slice_slice_x21_spec__0(v___x_646_);
return v___x_647_;
}
else
{
lean_object* v_str_648_; lean_object* v_startInclusive_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_658_; 
v_str_648_ = lean_ctor_get(v_s_642_, 0);
v_startInclusive_649_ = lean_ctor_get(v_s_642_, 1);
v_isSharedCheck_658_ = !lean_is_exclusive(v_s_642_);
if (v_isSharedCheck_658_ == 0)
{
lean_object* v_unused_659_; 
v_unused_659_ = lean_ctor_get(v_s_642_, 2);
lean_dec(v_unused_659_);
v___x_651_ = v_s_642_;
v_isShared_652_ = v_isSharedCheck_658_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_startInclusive_649_);
lean_inc(v_str_648_);
lean_dec(v_s_642_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_658_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_653_ = lean_nat_add(v_startInclusive_649_, v_newStart_643_);
v___x_654_ = lean_nat_add(v_startInclusive_649_, v_newEnd_644_);
lean_dec(v_startInclusive_649_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 2, v___x_654_);
lean_ctor_set(v___x_651_, 1, v___x_653_);
v___x_656_ = v___x_651_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_str_648_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_657_, 2, v___x_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x21___boxed(lean_object* v_s_660_, lean_object* v_newStart_661_, lean_object* v_newEnd_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_String_Slice_slice_x21(v_s_660_, v_newStart_661_, v_newEnd_662_);
lean_dec(v_newEnd_662_);
lean_dec(v_newStart_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21(lean_object* v_s_664_, lean_object* v_newStart_665_, lean_object* v_newEnd_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_String_Slice_slice_x21(v_s_664_, v_newStart_665_, v_newEnd_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21___boxed(lean_object* v_s_668_, lean_object* v_newStart_669_, lean_object* v_newEnd_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_String_Slice_replaceStartEnd_x21(v_s_668_, v_newStart_669_, v_newEnd_670_);
lean_dec(v_newEnd_670_);
lean_dec(v_newStart_669_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_String_decodeChar___boxed(lean_object* v_s_675_, lean_object* v_byteIdx_676_, lean_object* v_h_677_){
_start:
{
uint32_t v_res_678_; lean_object* v_r_679_; 
v_res_678_ = lean_string_utf8_get_fast(v_s_675_, v_byteIdx_676_);
lean_dec(v_byteIdx_676_);
lean_dec_ref(v_s_675_);
v_r_679_ = lean_box_uint32(v_res_678_);
return v_r_679_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get___redArg(lean_object* v_s_680_, lean_object* v_pos_681_){
_start:
{
lean_object* v_str_682_; lean_object* v_startInclusive_683_; lean_object* v___x_684_; uint32_t v___x_685_; 
v_str_682_ = lean_ctor_get(v_s_680_, 0);
v_startInclusive_683_ = lean_ctor_get(v_s_680_, 1);
v___x_684_ = lean_nat_add(v_startInclusive_683_, v_pos_681_);
v___x_685_ = lean_string_utf8_get_fast(v_str_682_, v___x_684_);
lean_dec(v___x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___redArg___boxed(lean_object* v_s_686_, lean_object* v_pos_687_){
_start:
{
uint32_t v_res_688_; lean_object* v_r_689_; 
v_res_688_ = l_String_Slice_Pos_get___redArg(v_s_686_, v_pos_687_);
lean_dec(v_pos_687_);
lean_dec_ref(v_s_686_);
v_r_689_ = lean_box_uint32(v_res_688_);
return v_r_689_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get(lean_object* v_s_690_, lean_object* v_pos_691_, lean_object* v_h_692_){
_start:
{
lean_object* v_str_693_; lean_object* v_startInclusive_694_; lean_object* v___x_695_; uint32_t v___x_696_; 
v_str_693_ = lean_ctor_get(v_s_690_, 0);
v_startInclusive_694_ = lean_ctor_get(v_s_690_, 1);
v___x_695_ = lean_nat_add(v_startInclusive_694_, v_pos_691_);
v___x_696_ = lean_string_utf8_get_fast(v_str_693_, v___x_695_);
lean_dec(v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___boxed(lean_object* v_s_697_, lean_object* v_pos_698_, lean_object* v_h_699_){
_start:
{
uint32_t v_res_700_; lean_object* v_r_701_; 
v_res_700_ = l_String_Slice_Pos_get(v_s_697_, v_pos_698_, v_h_699_);
lean_dec(v_pos_698_);
lean_dec_ref(v_s_697_);
v_r_701_ = lean_box_uint32(v_res_700_);
return v_r_701_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f(lean_object* v_s_702_, lean_object* v_pos_703_){
_start:
{
lean_object* v_str_704_; lean_object* v_startInclusive_705_; lean_object* v_endExclusive_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v_str_704_ = lean_ctor_get(v_s_702_, 0);
v_startInclusive_705_ = lean_ctor_get(v_s_702_, 1);
v_endExclusive_706_ = lean_ctor_get(v_s_702_, 2);
v___x_707_ = lean_nat_sub(v_endExclusive_706_, v_startInclusive_705_);
v___x_708_ = lean_nat_dec_eq(v_pos_703_, v___x_707_);
lean_dec(v___x_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; uint32_t v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_709_ = lean_nat_add(v_startInclusive_705_, v_pos_703_);
v___x_710_ = lean_string_utf8_get_fast(v_str_704_, v___x_709_);
lean_dec(v___x_709_);
v___x_711_ = lean_box_uint32(v___x_710_);
v___x_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
return v___x_712_;
}
else
{
lean_object* v___x_713_; 
v___x_713_ = lean_box(0);
return v___x_713_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f___boxed(lean_object* v_s_714_, lean_object* v_pos_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_String_Slice_Pos_get_x3f(v_s_714_, v_pos_715_);
lean_dec(v_pos_715_);
lean_dec_ref(v_s_714_);
return v_res_716_;
}
}
static lean_object* _init_l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1(void){
_start:
{
uint32_t v___x_717_; lean_object* v___x_718_; 
v___x_717_ = 65;
v___x_718_ = lean_box_uint32(v___x_717_);
return v___x_718_;
}
}
LEAN_EXPORT uint32_t l_panic___at___00String_Slice_Pos_get_x21_spec__0(lean_object* v_msg_719_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; uint32_t v___x_722_; 
v___x_720_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1;
v___x_721_ = lean_panic_fn_borrowed(v___x_720_, v_msg_719_);
v___x_722_ = lean_unbox_uint32(v___x_721_);
lean_dec(v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed(lean_object* v_msg_723_){
_start:
{
uint32_t v_res_724_; lean_object* v_r_725_; 
v_res_724_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v_msg_723_);
v_r_725_ = lean_box_uint32(v_res_724_);
return v_r_725_;
}
}
static lean_object* _init_l_String_Slice_Pos_get_x21___closed__2(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_728_ = ((lean_object*)(l_String_Slice_Pos_get_x21___closed__1));
v___x_729_ = lean_unsigned_to_nat(29u);
v___x_730_ = lean_unsigned_to_nat(1211u);
v___x_731_ = ((lean_object*)(l_String_Slice_Pos_get_x21___closed__0));
v___x_732_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_733_ = l_mkPanicMessageWithDecl(v___x_732_, v___x_731_, v___x_730_, v___x_729_, v___x_728_);
return v___x_733_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get_x21(lean_object* v_s_734_, lean_object* v_pos_735_){
_start:
{
lean_object* v_str_736_; lean_object* v_startInclusive_737_; lean_object* v_endExclusive_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v_str_736_ = lean_ctor_get(v_s_734_, 0);
v_startInclusive_737_ = lean_ctor_get(v_s_734_, 1);
v_endExclusive_738_ = lean_ctor_get(v_s_734_, 2);
v___x_739_ = lean_nat_sub(v_endExclusive_738_, v_startInclusive_737_);
v___x_740_ = lean_nat_dec_eq(v_pos_735_, v___x_739_);
lean_dec(v___x_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; uint32_t v___x_742_; 
v___x_741_ = lean_nat_add(v_startInclusive_737_, v_pos_735_);
v___x_742_ = lean_string_utf8_get_fast(v_str_736_, v___x_741_);
lean_dec(v___x_741_);
return v___x_742_;
}
else
{
lean_object* v___x_743_; uint32_t v___x_744_; 
v___x_743_ = lean_obj_once(&l_String_Slice_Pos_get_x21___closed__2, &l_String_Slice_Pos_get_x21___closed__2_once, _init_l_String_Slice_Pos_get_x21___closed__2);
v___x_744_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v___x_743_);
return v___x_744_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x21___boxed(lean_object* v_s_745_, lean_object* v_pos_746_){
_start:
{
uint32_t v_res_747_; lean_object* v_r_748_; 
v_res_747_ = l_String_Slice_Pos_get_x21(v_s_745_, v_pos_746_);
lean_dec(v_pos_746_);
lean_dec_ref(v_s_745_);
v_r_748_ = lean_box_uint32(v_res_747_);
return v_r_748_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg(lean_object* v_pos_749_){
_start:
{
lean_inc(v_pos_749_);
return v_pos_749_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg___boxed(lean_object* v_pos_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_String_Pos_toSlice___redArg(v_pos_750_);
lean_dec(v_pos_750_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice(lean_object* v_s_752_, lean_object* v_pos_753_){
_start:
{
lean_inc(v_pos_753_);
return v_pos_753_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___boxed(lean_object* v_s_754_, lean_object* v_pos_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_String_Pos_toSlice(v_s_754_, v_pos_755_);
lean_dec(v_pos_755_);
lean_dec_ref(v_s_754_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg(lean_object* v_pos_757_){
_start:
{
lean_inc(v_pos_757_);
return v_pos_757_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg___boxed(lean_object* v_pos_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_String_Pos_ofToSlice___redArg(v_pos_758_);
lean_dec(v_pos_758_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice(lean_object* v_s_760_, lean_object* v_pos_761_){
_start:
{
lean_inc(v_pos_761_);
return v_pos_761_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___boxed(lean_object* v_s_762_, lean_object* v_pos_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_String_Pos_ofToSlice(v_s_762_, v_pos_763_);
lean_dec(v_pos_763_);
lean_dec_ref(v_s_762_);
return v_res_764_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get___redArg(lean_object* v_s_765_, lean_object* v_pos_766_){
_start:
{
uint32_t v___x_767_; 
v___x_767_ = lean_string_utf8_get_fast(v_s_765_, v_pos_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get___redArg___boxed(lean_object* v_s_768_, lean_object* v_pos_769_){
_start:
{
uint32_t v_res_770_; lean_object* v_r_771_; 
v_res_770_ = l_String_Pos_get___redArg(v_s_768_, v_pos_769_);
lean_dec(v_pos_769_);
lean_dec_ref(v_s_768_);
v_r_771_ = lean_box_uint32(v_res_770_);
return v_r_771_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get(lean_object* v_s_772_, lean_object* v_pos_773_, lean_object* v_h_774_){
_start:
{
uint32_t v___x_775_; 
v___x_775_ = lean_string_utf8_get_fast(v_s_772_, v_pos_773_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get___boxed(lean_object* v_s_776_, lean_object* v_pos_777_, lean_object* v_h_778_){
_start:
{
uint32_t v_res_779_; lean_object* v_r_780_; 
v_res_779_ = l_String_Pos_get(v_s_776_, v_pos_777_, v_h_778_);
lean_dec(v_pos_777_);
lean_dec_ref(v_s_776_);
v_r_780_ = lean_box_uint32(v_res_779_);
return v_r_780_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x3f(lean_object* v_s_781_, lean_object* v_pos_782_){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_783_ = lean_unsigned_to_nat(0u);
v___x_784_ = lean_string_utf8_byte_size(v_s_781_);
v___x_785_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_785_, 0, v_s_781_);
lean_ctor_set(v___x_785_, 1, v___x_783_);
lean_ctor_set(v___x_785_, 2, v___x_784_);
v___x_786_ = l_String_Slice_Pos_get_x3f(v___x_785_, v_pos_782_);
lean_dec_ref(v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x3f___boxed(lean_object* v_s_787_, lean_object* v_pos_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_String_Pos_get_x3f(v_s_787_, v_pos_788_);
lean_dec(v_pos_788_);
return v_res_789_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get_x21(lean_object* v_s_790_, lean_object* v_pos_791_){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; uint32_t v___x_795_; 
v___x_792_ = lean_unsigned_to_nat(0u);
v___x_793_ = lean_string_utf8_byte_size(v_s_790_);
v___x_794_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_794_, 0, v_s_790_);
lean_ctor_set(v___x_794_, 1, v___x_792_);
lean_ctor_set(v___x_794_, 2, v___x_793_);
v___x_795_ = l_String_Slice_Pos_get_x21(v___x_794_, v_pos_791_);
lean_dec_ref(v___x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x21___boxed(lean_object* v_s_796_, lean_object* v_pos_797_){
_start:
{
uint32_t v_res_798_; lean_object* v_r_799_; 
v_res_798_ = l_String_Pos_get_x21(v_s_796_, v_pos_797_);
lean_dec(v_pos_797_);
v_r_799_ = lean_box_uint32(v_res_798_);
return v_r_799_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_byte___redArg(lean_object* v_s_800_, lean_object* v_pos_801_){
_start:
{
uint8_t v___x_802_; 
v___x_802_ = lean_string_get_byte_fast(v_s_800_, v_pos_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_byte___redArg___boxed(lean_object* v_s_803_, lean_object* v_pos_804_){
_start:
{
uint8_t v_res_805_; lean_object* v_r_806_; 
v_res_805_ = l_String_Pos_byte___redArg(v_s_803_, v_pos_804_);
lean_dec_ref(v_s_803_);
v_r_806_ = lean_box(v_res_805_);
return v_r_806_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_byte(lean_object* v_s_807_, lean_object* v_pos_808_, lean_object* v_h_809_){
_start:
{
uint8_t v___x_810_; 
v___x_810_ = lean_string_get_byte_fast(v_s_807_, v_pos_808_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_byte___boxed(lean_object* v_s_811_, lean_object* v_pos_812_, lean_object* v_h_813_){
_start:
{
uint8_t v_res_814_; lean_object* v_r_815_; 
v_res_814_ = l_String_Pos_byte(v_s_811_, v_pos_812_, v_h_813_);
lean_dec_ref(v_s_811_);
v_r_815_ = lean_box(v_res_814_);
return v_r_815_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg(lean_object* v_pos_816_){
_start:
{
lean_inc(v_pos_816_);
return v_pos_816_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg___boxed(lean_object* v_pos_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_String_Pos_ofCopy___redArg(v_pos_817_);
lean_dec(v_pos_817_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy(lean_object* v_s_819_, lean_object* v_pos_820_){
_start:
{
lean_inc(v_pos_820_);
return v_pos_820_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___boxed(lean_object* v_s_821_, lean_object* v_pos_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_String_Pos_ofCopy(v_s_821_, v_pos_822_);
lean_dec(v_pos_822_);
lean_dec_ref(v_s_821_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg(lean_object* v_pos_824_){
_start:
{
lean_inc(v_pos_824_);
return v_pos_824_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg___boxed(lean_object* v_pos_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_String_Slice_Pos_copy___redArg(v_pos_825_);
lean_dec(v_pos_825_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy(lean_object* v_s_827_, lean_object* v_pos_828_){
_start:
{
lean_inc(v_pos_828_);
return v_pos_828_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___boxed(lean_object* v_s_829_, lean_object* v_pos_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_String_Slice_Pos_copy(v_s_829_, v_pos_830_);
lean_dec(v_pos_830_);
lean_dec_ref(v_s_829_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg(lean_object* v_pos_832_){
_start:
{
lean_inc(v_pos_832_);
return v_pos_832_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg___boxed(lean_object* v_pos_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_String_Slice_Pos_toCopy___redArg(v_pos_833_);
lean_dec(v_pos_833_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy(lean_object* v_s_835_, lean_object* v_pos_836_){
_start:
{
lean_inc(v_pos_836_);
return v_pos_836_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___boxed(lean_object* v_s_837_, lean_object* v_pos_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_String_Slice_Pos_toCopy(v_s_837_, v_pos_838_);
lean_dec(v_pos_838_);
lean_dec_ref(v_s_837_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg(lean_object* v_p_u2080_840_, lean_object* v_pos_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = lean_nat_add(v_p_u2080_840_, v_pos_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg___boxed(lean_object* v_p_u2080_843_, lean_object* v_pos_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_String_Slice_Pos_ofSliceFrom___redArg(v_p_u2080_843_, v_pos_844_);
lean_dec(v_pos_844_);
lean_dec(v_p_u2080_843_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom(lean_object* v_s_846_, lean_object* v_p_u2080_847_, lean_object* v_pos_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = lean_nat_add(v_p_u2080_847_, v_pos_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___boxed(lean_object* v_s_850_, lean_object* v_p_u2080_851_, lean_object* v_pos_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_String_Slice_Pos_ofSliceFrom(v_s_850_, v_p_u2080_851_, v_pos_852_);
lean_dec(v_pos_852_);
lean_dec(v_p_u2080_851_);
lean_dec_ref(v_s_850_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg(lean_object* v_p_u2080_854_, lean_object* v_pos_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = lean_nat_add(v_p_u2080_854_, v_pos_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg___boxed(lean_object* v_p_u2080_857_, lean_object* v_pos_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_String_Slice_Pos_ofReplaceStart___redArg(v_p_u2080_857_, v_pos_858_);
lean_dec(v_pos_858_);
lean_dec(v_p_u2080_857_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart(lean_object* v_s_860_, lean_object* v_p_u2080_861_, lean_object* v_pos_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = lean_nat_add(v_p_u2080_861_, v_pos_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___boxed(lean_object* v_s_864_, lean_object* v_p_u2080_865_, lean_object* v_pos_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_String_Slice_Pos_ofReplaceStart(v_s_864_, v_p_u2080_865_, v_pos_866_);
lean_dec(v_pos_866_);
lean_dec(v_p_u2080_865_);
lean_dec_ref(v_s_864_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg(lean_object* v_p_u2080_868_, lean_object* v_pos_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = lean_nat_sub(v_pos_869_, v_p_u2080_868_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg___boxed(lean_object* v_p_u2080_871_, lean_object* v_pos_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_String_Slice_Pos_sliceFrom___redArg(v_p_u2080_871_, v_pos_872_);
lean_dec(v_pos_872_);
lean_dec(v_p_u2080_871_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom(lean_object* v_s_874_, lean_object* v_p_u2080_875_, lean_object* v_pos_876_, lean_object* v_h_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = lean_nat_sub(v_pos_876_, v_p_u2080_875_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___boxed(lean_object* v_s_879_, lean_object* v_p_u2080_880_, lean_object* v_pos_881_, lean_object* v_h_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_String_Slice_Pos_sliceFrom(v_s_879_, v_p_u2080_880_, v_pos_881_, v_h_882_);
lean_dec(v_pos_881_);
lean_dec(v_p_u2080_880_);
lean_dec_ref(v_s_879_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg(lean_object* v_p_u2080_884_, lean_object* v_pos_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = lean_nat_sub(v_pos_885_, v_p_u2080_884_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg___boxed(lean_object* v_p_u2080_887_, lean_object* v_pos_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_String_Slice_Pos_toReplaceStart___redArg(v_p_u2080_887_, v_pos_888_);
lean_dec(v_pos_888_);
lean_dec(v_p_u2080_887_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart(lean_object* v_s_890_, lean_object* v_p_u2080_891_, lean_object* v_pos_892_, lean_object* v_h_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = lean_nat_sub(v_pos_892_, v_p_u2080_891_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___boxed(lean_object* v_s_895_, lean_object* v_p_u2080_896_, lean_object* v_pos_897_, lean_object* v_h_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_String_Slice_Pos_toReplaceStart(v_s_895_, v_p_u2080_896_, v_pos_897_, v_h_898_);
lean_dec(v_pos_897_);
lean_dec(v_p_u2080_896_);
lean_dec_ref(v_s_895_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg(lean_object* v_pos_900_){
_start:
{
lean_inc(v_pos_900_);
return v_pos_900_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg___boxed(lean_object* v_pos_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_String_Slice_Pos_ofSliceTo___redArg(v_pos_901_);
lean_dec(v_pos_901_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo(lean_object* v_s_903_, lean_object* v_p_u2080_904_, lean_object* v_pos_905_){
_start:
{
lean_inc(v_pos_905_);
return v_pos_905_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___boxed(lean_object* v_s_906_, lean_object* v_p_u2080_907_, lean_object* v_pos_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_String_Slice_Pos_ofSliceTo(v_s_906_, v_p_u2080_907_, v_pos_908_);
lean_dec(v_pos_908_);
lean_dec(v_p_u2080_907_);
lean_dec_ref(v_s_906_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg(lean_object* v_pos_910_){
_start:
{
lean_inc(v_pos_910_);
return v_pos_910_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg___boxed(lean_object* v_pos_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_String_Slice_Pos_ofReplaceEnd___redArg(v_pos_911_);
lean_dec(v_pos_911_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd(lean_object* v_s_913_, lean_object* v_p_u2080_914_, lean_object* v_pos_915_){
_start:
{
lean_inc(v_pos_915_);
return v_pos_915_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___boxed(lean_object* v_s_916_, lean_object* v_p_u2080_917_, lean_object* v_pos_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_String_Slice_Pos_ofReplaceEnd(v_s_916_, v_p_u2080_917_, v_pos_918_);
lean_dec(v_pos_918_);
lean_dec(v_p_u2080_917_);
lean_dec_ref(v_s_916_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg(lean_object* v_pos_920_){
_start:
{
lean_inc(v_pos_920_);
return v_pos_920_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg___boxed(lean_object* v_pos_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_String_Slice_Pos_sliceTo___redArg(v_pos_921_);
lean_dec(v_pos_921_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo(lean_object* v_s_923_, lean_object* v_p_u2080_924_, lean_object* v_pos_925_, lean_object* v_h_926_){
_start:
{
lean_inc(v_pos_925_);
return v_pos_925_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___boxed(lean_object* v_s_927_, lean_object* v_p_u2080_928_, lean_object* v_pos_929_, lean_object* v_h_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_String_Slice_Pos_sliceTo(v_s_927_, v_p_u2080_928_, v_pos_929_, v_h_930_);
lean_dec(v_pos_929_);
lean_dec(v_p_u2080_928_);
lean_dec_ref(v_s_927_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg(lean_object* v_pos_932_){
_start:
{
lean_inc(v_pos_932_);
return v_pos_932_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg___boxed(lean_object* v_pos_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_String_Slice_Pos_toReplaceEnd___redArg(v_pos_933_);
lean_dec(v_pos_933_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd(lean_object* v_s_935_, lean_object* v_p_u2080_936_, lean_object* v_pos_937_, lean_object* v_h_938_){
_start:
{
lean_inc(v_pos_937_);
return v_pos_937_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___boxed(lean_object* v_s_939_, lean_object* v_p_u2080_940_, lean_object* v_pos_941_, lean_object* v_h_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_String_Slice_Pos_toReplaceEnd(v_s_939_, v_p_u2080_940_, v_pos_941_, v_h_942_);
lean_dec(v_pos_941_);
lean_dec(v_p_u2080_940_);
lean_dec_ref(v_s_939_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg(lean_object* v_s_944_, lean_object* v_pos_945_){
_start:
{
lean_object* v_str_946_; lean_object* v_startInclusive_947_; lean_object* v___x_948_; uint8_t v___x_949_; uint8_t v___x_950_; uint8_t v___x_951_; uint8_t v___x_952_; uint8_t v___x_953_; 
v_str_946_ = lean_ctor_get(v_s_944_, 0);
v_startInclusive_947_ = lean_ctor_get(v_s_944_, 1);
v___x_948_ = lean_nat_add(v_startInclusive_947_, v_pos_945_);
v___x_949_ = lean_string_get_byte_fast(v_str_946_, v___x_948_);
v___x_950_ = 128;
v___x_951_ = lean_uint8_land(v___x_949_, v___x_950_);
v___x_952_ = 0;
v___x_953_ = lean_uint8_dec_eq(v___x_951_, v___x_952_);
if (v___x_953_ == 0)
{
uint8_t v___x_954_; uint8_t v___x_955_; uint8_t v___x_956_; uint8_t v___x_957_; 
v___x_954_ = 224;
v___x_955_ = lean_uint8_land(v___x_949_, v___x_954_);
v___x_956_ = 192;
v___x_957_ = lean_uint8_dec_eq(v___x_955_, v___x_956_);
if (v___x_957_ == 0)
{
uint8_t v___x_958_; uint8_t v___x_959_; uint8_t v___x_960_; 
v___x_958_ = 240;
v___x_959_ = lean_uint8_land(v___x_949_, v___x_958_);
v___x_960_ = lean_uint8_dec_eq(v___x_959_, v___x_954_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = lean_unsigned_to_nat(4u);
v___x_962_ = lean_nat_add(v_pos_945_, v___x_961_);
return v___x_962_;
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_unsigned_to_nat(3u);
v___x_964_ = lean_nat_add(v_pos_945_, v___x_963_);
return v___x_964_;
}
}
else
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = lean_unsigned_to_nat(2u);
v___x_966_ = lean_nat_add(v_pos_945_, v___x_965_);
return v___x_966_;
}
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = lean_unsigned_to_nat(1u);
v___x_968_ = lean_nat_add(v_pos_945_, v___x_967_);
return v___x_968_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg___boxed(lean_object* v_s_969_, lean_object* v_pos_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_String_Slice_Pos_next___redArg(v_s_969_, v_pos_970_);
lean_dec(v_pos_970_);
lean_dec_ref(v_s_969_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next(lean_object* v_s_972_, lean_object* v_pos_973_, lean_object* v_h_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_String_Slice_Pos_next___redArg(v_s_972_, v_pos_973_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___boxed(lean_object* v_s_976_, lean_object* v_pos_977_, lean_object* v_h_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_String_Slice_Pos_next(v_s_976_, v_pos_977_, v_h_978_);
lean_dec(v_pos_977_);
lean_dec_ref(v_s_976_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f(lean_object* v_s_980_, lean_object* v_pos_981_){
_start:
{
lean_object* v_startInclusive_982_; lean_object* v_endExclusive_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v_startInclusive_982_ = lean_ctor_get(v_s_980_, 1);
v_endExclusive_983_ = lean_ctor_get(v_s_980_, 2);
v___x_984_ = lean_nat_sub(v_endExclusive_983_, v_startInclusive_982_);
v___x_985_ = lean_nat_dec_eq(v_pos_981_, v___x_984_);
lean_dec(v___x_984_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = l_String_Slice_Pos_next___redArg(v_s_980_, v_pos_981_);
v___x_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
return v___x_987_;
}
else
{
lean_object* v___x_988_; 
v___x_988_ = lean_box(0);
return v___x_988_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f___boxed(lean_object* v_s_989_, lean_object* v_pos_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_String_Slice_Pos_next_x3f(v_s_989_, v_pos_990_);
lean_dec(v_pos_990_);
lean_dec_ref(v_s_989_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(lean_object* v_msg_992_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = lean_panic_fn_borrowed(v___x_993_, v_msg_992_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0(lean_object* v_s_995_, lean_object* v_msg_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v_msg_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___boxed(lean_object* v_s_998_, lean_object* v_msg_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0(v_s_998_, v_msg_999_);
lean_dec_ref(v_s_998_);
return v_res_1000_;
}
}
static lean_object* _init_l_String_Slice_Pos_next_x21___closed__2(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1003_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__1));
v___x_1004_ = lean_unsigned_to_nat(29u);
v___x_1005_ = lean_unsigned_to_nat(1603u);
v___x_1006_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__0));
v___x_1007_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1008_ = l_mkPanicMessageWithDecl(v___x_1007_, v___x_1006_, v___x_1005_, v___x_1004_, v___x_1003_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21(lean_object* v_s_1009_, lean_object* v_pos_1010_){
_start:
{
lean_object* v_startInclusive_1011_; lean_object* v_endExclusive_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v_startInclusive_1011_ = lean_ctor_get(v_s_1009_, 1);
v_endExclusive_1012_ = lean_ctor_get(v_s_1009_, 2);
v___x_1013_ = lean_nat_sub(v_endExclusive_1012_, v_startInclusive_1011_);
v___x_1014_ = lean_nat_dec_eq(v_pos_1010_, v___x_1013_);
lean_dec(v___x_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; 
v___x_1015_ = l_String_Slice_Pos_next___redArg(v_s_1009_, v_pos_1010_);
return v___x_1015_;
}
else
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_obj_once(&l_String_Slice_Pos_next_x21___closed__2, &l_String_Slice_Pos_next_x21___closed__2_once, _init_l_String_Slice_Pos_next_x21___closed__2);
v___x_1017_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_1016_);
return v___x_1017_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21___boxed(lean_object* v_s_1018_, lean_object* v_pos_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_String_Slice_Pos_next_x21(v_s_1018_, v_pos_1019_);
lean_dec(v_pos_1019_);
lean_dec_ref(v_s_1018_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg(lean_object* v_s_1021_, lean_object* v_off_1022_){
_start:
{
lean_object* v_str_1023_; lean_object* v_startInclusive_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; uint8_t v___x_1027_; 
v_str_1023_ = lean_ctor_get(v_s_1021_, 0);
v_startInclusive_1024_ = lean_ctor_get(v_s_1021_, 1);
v___x_1025_ = lean_nat_add(v_startInclusive_1024_, v_off_1022_);
v___x_1026_ = lean_string_get_byte_fast(v_str_1023_, v___x_1025_);
v___x_1027_ = l_UInt8_instDecidableIsUTF8FirstByte___aux__1(v___x_1026_);
if (v___x_1027_ == 0)
{
lean_object* v_zero_1028_; uint8_t v_isZero_1029_; lean_object* v_one_1030_; lean_object* v_n_1031_; 
v_zero_1028_ = lean_unsigned_to_nat(0u);
v_isZero_1029_ = lean_nat_dec_eq(v_off_1022_, v_zero_1028_);
v_one_1030_ = lean_unsigned_to_nat(1u);
v_n_1031_ = lean_nat_sub(v_off_1022_, v_one_1030_);
lean_dec(v_off_1022_);
v_off_1022_ = v_n_1031_;
goto _start;
}
else
{
return v_off_1022_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg___boxed(lean_object* v_s_1033_, lean_object* v_off_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1033_, v_off_1034_);
lean_dec_ref(v_s_1033_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go(lean_object* v_s_1036_, lean_object* v_off_1037_, lean_object* v_h_u2081_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1036_, v_off_1037_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___boxed(lean_object* v_s_1040_, lean_object* v_off_1041_, lean_object* v_h_u2081_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_String_Slice_Pos_prevAux_go(v_s_1040_, v_off_1041_, v_h_u2081_1042_);
lean_dec_ref(v_s_1040_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg(lean_object* v_s_1044_, lean_object* v_pos_1045_){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = lean_unsigned_to_nat(1u);
v___x_1047_ = lean_nat_sub(v_pos_1045_, v___x_1046_);
v___x_1048_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1044_, v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg___boxed(lean_object* v_s_1049_, lean_object* v_pos_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_String_Slice_Pos_prevAux___redArg(v_s_1049_, v_pos_1050_);
lean_dec(v_pos_1050_);
lean_dec_ref(v_s_1049_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux(lean_object* v_s_1052_, lean_object* v_pos_1053_, lean_object* v_h_1054_){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1055_ = lean_unsigned_to_nat(1u);
v___x_1056_ = lean_nat_sub(v_pos_1053_, v___x_1055_);
v___x_1057_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1052_, v___x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___boxed(lean_object* v_s_1058_, lean_object* v_pos_1059_, lean_object* v_h_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_String_Slice_Pos_prevAux(v_s_1058_, v_pos_1059_, v_h_1060_);
lean_dec(v_pos_1059_);
lean_dec_ref(v_s_1058_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(lean_object* v_off_1062_, lean_object* v_h__1_1063_, lean_object* v_h__2_1064_){
_start:
{
lean_object* v_zero_1065_; uint8_t v_isZero_1066_; 
v_zero_1065_ = lean_unsigned_to_nat(0u);
v_isZero_1066_ = lean_nat_dec_eq(v_off_1062_, v_zero_1065_);
if (v_isZero_1066_ == 1)
{
lean_object* v___x_1067_; 
lean_dec(v_h__2_1064_);
v___x_1067_ = lean_apply_3(v_h__1_1063_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1067_;
}
else
{
lean_object* v_one_1068_; lean_object* v_n_1069_; lean_object* v___x_1070_; 
lean_dec(v_h__1_1063_);
v_one_1068_ = lean_unsigned_to_nat(1u);
v_n_1069_ = lean_nat_sub(v_off_1062_, v_one_1068_);
v___x_1070_ = lean_apply_4(v_h__2_1064_, v_n_1069_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1070_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg___boxed(lean_object* v_off_1071_, lean_object* v_h__1_1072_, lean_object* v_h__2_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(v_off_1071_, v_h__1_1072_, v_h__2_1073_);
lean_dec(v_off_1071_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(lean_object* v_s_1075_, lean_object* v_motive_1076_, lean_object* v_off_1077_, lean_object* v_h_u2081_1078_, lean_object* v_hbyte_1079_, lean_object* v_this_1080_, lean_object* v_h__1_1081_, lean_object* v_h__2_1082_){
_start:
{
lean_object* v_zero_1083_; uint8_t v_isZero_1084_; 
v_zero_1083_ = lean_unsigned_to_nat(0u);
v_isZero_1084_ = lean_nat_dec_eq(v_off_1077_, v_zero_1083_);
if (v_isZero_1084_ == 1)
{
lean_object* v___x_1085_; 
lean_dec(v_h__2_1082_);
v___x_1085_ = lean_apply_3(v_h__1_1081_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1085_;
}
else
{
lean_object* v_one_1086_; lean_object* v_n_1087_; lean_object* v___x_1088_; 
lean_dec(v_h__1_1081_);
v_one_1086_ = lean_unsigned_to_nat(1u);
v_n_1087_ = lean_nat_sub(v_off_1077_, v_one_1086_);
v___x_1088_ = lean_apply_4(v_h__2_1082_, v_n_1087_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1088_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___boxed(lean_object* v_s_1089_, lean_object* v_motive_1090_, lean_object* v_off_1091_, lean_object* v_h_u2081_1092_, lean_object* v_hbyte_1093_, lean_object* v_this_1094_, lean_object* v_h__1_1095_, lean_object* v_h__2_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(v_s_1089_, v_motive_1090_, v_off_1091_, v_h_u2081_1092_, v_hbyte_1093_, v_this_1094_, v_h__1_1095_, v_h__2_1096_);
lean_dec(v_off_1091_);
lean_dec_ref(v_s_1089_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg(lean_object* v_off_1098_){
_start:
{
lean_inc(v_off_1098_);
return v_off_1098_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg___boxed(lean_object* v_off_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_String_Slice_pos___redArg(v_off_1099_);
lean_dec(v_off_1099_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos(lean_object* v_s_1101_, lean_object* v_off_1102_, lean_object* v_h_1103_){
_start:
{
lean_inc(v_off_1102_);
return v_off_1102_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___boxed(lean_object* v_s_1104_, lean_object* v_off_1105_, lean_object* v_h_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_String_Slice_pos(v_s_1104_, v_off_1105_, v_h_1106_);
lean_dec(v_off_1105_);
lean_dec_ref(v_s_1104_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f(lean_object* v_s_1108_, lean_object* v_off_1109_){
_start:
{
uint8_t v___x_1110_; 
v___x_1110_ = l_String_Pos_Raw_isValidForSlice(v_s_1108_, v_off_1109_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; 
lean_dec(v_off_1109_);
v___x_1111_ = lean_box(0);
return v___x_1111_;
}
else
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1112_, 0, v_off_1109_);
return v___x_1112_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f___boxed(lean_object* v_s_1113_, lean_object* v_off_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_String_Slice_pos_x3f(v_s_1113_, v_off_1114_);
lean_dec_ref(v_s_1113_);
return v_res_1115_;
}
}
static lean_object* _init_l_String_Slice_pos_x21___closed__2(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1118_ = ((lean_object*)(l_String_Slice_pos_x21___closed__1));
v___x_1119_ = lean_unsigned_to_nat(4u);
v___x_1120_ = lean_unsigned_to_nat(1691u);
v___x_1121_ = ((lean_object*)(l_String_Slice_pos_x21___closed__0));
v___x_1122_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1123_ = l_mkPanicMessageWithDecl(v___x_1122_, v___x_1121_, v___x_1120_, v___x_1119_, v___x_1118_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21(lean_object* v_s_1124_, lean_object* v_off_1125_){
_start:
{
uint8_t v___x_1126_; 
v___x_1126_ = l_String_Pos_Raw_isValidForSlice(v_s_1124_, v_off_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = lean_obj_once(&l_String_Slice_pos_x21___closed__2, &l_String_Slice_pos_x21___closed__2_once, _init_l_String_Slice_pos_x21___closed__2);
v___x_1128_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_1127_);
return v___x_1128_;
}
else
{
lean_inc(v_off_1125_);
return v_off_1125_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21___boxed(lean_object* v_s_1129_, lean_object* v_off_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_String_Slice_pos_x21(v_s_1129_, v_off_1130_);
lean_dec(v_off_1130_);
lean_dec_ref(v_s_1129_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next___boxed(lean_object* v_s_1135_, lean_object* v_pos_1136_, lean_object* v_h_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = lean_string_utf8_next_fast(v_s_1135_, v_pos_1136_);
lean_dec(v_pos_1136_);
lean_dec_ref(v_s_1135_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x3f(lean_object* v_s_1139_, lean_object* v_pos_1140_){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1141_ = lean_unsigned_to_nat(0u);
v___x_1142_ = lean_string_utf8_byte_size(v_s_1139_);
v___x_1143_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1143_, 0, v_s_1139_);
lean_ctor_set(v___x_1143_, 1, v___x_1141_);
lean_ctor_set(v___x_1143_, 2, v___x_1142_);
v___x_1144_ = l_String_Slice_Pos_next_x3f(v___x_1143_, v_pos_1140_);
lean_dec_ref(v___x_1143_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_box(0);
return v___x_1145_;
}
else
{
lean_object* v_val_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
v_val_1146_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1144_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_val_1146_);
lean_dec(v___x_1144_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_val_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x3f___boxed(lean_object* v_s_1154_, lean_object* v_pos_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_String_Pos_next_x3f(v_s_1154_, v_pos_1155_);
lean_dec(v_pos_1155_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21(lean_object* v_s_1157_, lean_object* v_pos_1158_){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1159_ = lean_unsigned_to_nat(0u);
v___x_1160_ = lean_string_utf8_byte_size(v_s_1157_);
v___x_1161_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1161_, 0, v_s_1157_);
lean_ctor_set(v___x_1161_, 1, v___x_1159_);
lean_ctor_set(v___x_1161_, 2, v___x_1160_);
v___x_1162_ = l_String_Slice_Pos_next_x21(v___x_1161_, v_pos_1158_);
lean_dec_ref(v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21___boxed(lean_object* v_s_1163_, lean_object* v_pos_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_String_Pos_next_x21(v_s_1163_, v_pos_1164_);
lean_dec(v_pos_1164_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg(lean_object* v_off_1166_){
_start:
{
lean_inc(v_off_1166_);
return v_off_1166_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg___boxed(lean_object* v_off_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_String_pos___redArg(v_off_1167_);
lean_dec(v_off_1167_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_String_pos(lean_object* v_s_1169_, lean_object* v_off_1170_, lean_object* v_h_1171_){
_start:
{
lean_inc(v_off_1170_);
return v_off_1170_;
}
}
LEAN_EXPORT lean_object* l_String_pos___boxed(lean_object* v_s_1172_, lean_object* v_off_1173_, lean_object* v_h_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_String_pos(v_s_1172_, v_off_1173_, v_h_1174_);
lean_dec(v_off_1173_);
lean_dec_ref(v_s_1172_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x3f(lean_object* v_s_1176_, lean_object* v_off_1177_){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1178_ = lean_unsigned_to_nat(0u);
v___x_1179_ = lean_string_utf8_byte_size(v_s_1176_);
v___x_1180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1180_, 0, v_s_1176_);
lean_ctor_set(v___x_1180_, 1, v___x_1178_);
lean_ctor_set(v___x_1180_, 2, v___x_1179_);
v___x_1181_ = l_String_Slice_pos_x3f(v___x_1180_, v_off_1177_);
lean_dec_ref(v___x_1180_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v___x_1182_; 
v___x_1182_ = lean_box(0);
return v___x_1182_;
}
else
{
lean_object* v_val_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
v_val_1183_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1181_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_val_1183_);
lean_dec(v___x_1181_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_val_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_pos_x21(lean_object* v_s_1191_, lean_object* v_off_1192_){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1193_ = lean_unsigned_to_nat(0u);
v___x_1194_ = lean_string_utf8_byte_size(v_s_1191_);
v___x_1195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1195_, 0, v_s_1191_);
lean_ctor_set(v___x_1195_, 1, v___x_1193_);
lean_ctor_set(v___x_1195_, 2, v___x_1194_);
v___x_1196_ = l_String_Slice_pos_x21(v___x_1195_, v_off_1192_);
lean_dec_ref(v___x_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x21___boxed(lean_object* v_s_1197_, lean_object* v_off_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_String_pos_x21(v_s_1197_, v_off_1198_);
lean_dec(v_off_1198_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg(lean_object* v_pos_1200_){
_start:
{
lean_inc(v_pos_1200_);
return v_pos_1200_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg___boxed(lean_object* v_pos_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_String_Slice_Pos_cast___redArg(v_pos_1201_);
lean_dec(v_pos_1201_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast(lean_object* v_s_1203_, lean_object* v_t_1204_, lean_object* v_pos_1205_, lean_object* v_h_1206_){
_start:
{
lean_inc(v_pos_1205_);
return v_pos_1205_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___boxed(lean_object* v_s_1207_, lean_object* v_t_1208_, lean_object* v_pos_1209_, lean_object* v_h_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_String_Slice_Pos_cast(v_s_1207_, v_t_1208_, v_pos_1209_, v_h_1210_);
lean_dec(v_pos_1209_);
lean_dec_ref(v_t_1208_);
lean_dec_ref(v_s_1207_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg(lean_object* v_pos_1212_){
_start:
{
lean_inc(v_pos_1212_);
return v_pos_1212_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg___boxed(lean_object* v_pos_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_String_Pos_cast___redArg(v_pos_1213_);
lean_dec(v_pos_1213_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast(lean_object* v_s_1215_, lean_object* v_t_1216_, lean_object* v_pos_1217_, lean_object* v_h_1218_){
_start:
{
lean_inc(v_pos_1217_);
return v_pos_1217_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___boxed(lean_object* v_s_1219_, lean_object* v_t_1220_, lean_object* v_pos_1221_, lean_object* v_h_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_String_Pos_cast(v_s_1219_, v_t_1220_, v_pos_1221_, v_h_1222_);
lean_dec(v_pos_1221_);
lean_dec_ref(v_t_1220_);
lean_dec_ref(v_s_1219_);
return v_res_1223_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_Raw_utf8GetAux(lean_object* v_x_1224_, lean_object* v_x_1225_, lean_object* v_x_1226_){
_start:
{
if (lean_obj_tag(v_x_1224_) == 0)
{
uint32_t v___x_1227_; 
lean_dec(v_x_1225_);
v___x_1227_ = 65;
return v___x_1227_;
}
else
{
lean_object* v_head_1228_; lean_object* v_tail_1229_; uint8_t v___x_1230_; 
v_head_1228_ = lean_ctor_get(v_x_1224_, 0);
v_tail_1229_ = lean_ctor_get(v_x_1224_, 1);
v___x_1230_ = lean_nat_dec_eq(v_x_1225_, v_x_1226_);
if (v___x_1230_ == 0)
{
uint32_t v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1231_ = lean_unbox_uint32(v_head_1228_);
v___x_1232_ = l_Char_utf8Size(v___x_1231_);
v___x_1233_ = lean_nat_add(v_x_1225_, v___x_1232_);
lean_dec(v___x_1232_);
lean_dec(v_x_1225_);
v_x_1224_ = v_tail_1229_;
v_x_1225_ = v___x_1233_;
goto _start;
}
else
{
uint32_t v___x_1235_; 
lean_dec(v_x_1225_);
v___x_1235_ = lean_unbox_uint32(v_head_1228_);
return v___x_1235_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux___boxed(lean_object* v_x_1236_, lean_object* v_x_1237_, lean_object* v_x_1238_){
_start:
{
uint32_t v_res_1239_; lean_object* v_r_1240_; 
v_res_1239_ = l_String_Pos_Raw_utf8GetAux(v_x_1236_, v_x_1237_, v_x_1238_);
lean_dec(v_x_1238_);
lean_dec(v_x_1236_);
v_r_1240_ = lean_box_uint32(v_res_1239_);
return v_r_1240_;
}
}
LEAN_EXPORT uint32_t l_String_utf8GetAux(lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
uint32_t v___x_1244_; 
v___x_1244_ = l_String_Pos_Raw_utf8GetAux(v_a_1241_, v_a_1242_, v_a_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux___boxed(lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
uint32_t v_res_1248_; lean_object* v_r_1249_; 
v_res_1248_ = l_String_utf8GetAux(v_a_1245_, v_a_1246_, v_a_1247_);
lean_dec(v_a_1247_);
lean_dec(v_a_1245_);
v_r_1249_ = lean_box_uint32(v_res_1248_);
return v_r_1249_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get___boxed(lean_object* v_s_1252_, lean_object* v_p_1253_){
_start:
{
uint32_t v_res_1254_; lean_object* v_r_1255_; 
v_res_1254_ = lean_string_utf8_get(v_s_1252_, v_p_1253_);
lean_dec(v_p_1253_);
lean_dec_ref(v_s_1252_);
v_r_1255_ = lean_box_uint32(v_res_1254_);
return v_r_1255_;
}
}
LEAN_EXPORT lean_object* l_String_get___boxed(lean_object* v_s_1258_, lean_object* v_p_1259_){
_start:
{
uint32_t v_res_1260_; lean_object* v_r_1261_; 
v_res_1260_ = lean_string_utf8_get(v_s_1258_, v_p_1259_);
lean_dec(v_p_1259_);
lean_dec_ref(v_s_1258_);
v_r_1261_ = lean_box_uint32(v_res_1260_);
return v_r_1261_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f(lean_object* v_x_1262_, lean_object* v_x_1263_, lean_object* v_x_1264_){
_start:
{
if (lean_obj_tag(v_x_1262_) == 0)
{
lean_object* v___x_1265_; 
lean_dec(v_x_1263_);
v___x_1265_ = lean_box(0);
return v___x_1265_;
}
else
{
lean_object* v_head_1266_; lean_object* v_tail_1267_; uint8_t v___x_1268_; 
v_head_1266_ = lean_ctor_get(v_x_1262_, 0);
v_tail_1267_ = lean_ctor_get(v_x_1262_, 1);
v___x_1268_ = lean_nat_dec_eq(v_x_1263_, v_x_1264_);
if (v___x_1268_ == 0)
{
uint32_t v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1269_ = lean_unbox_uint32(v_head_1266_);
v___x_1270_ = l_Char_utf8Size(v___x_1269_);
v___x_1271_ = lean_nat_add(v_x_1263_, v___x_1270_);
lean_dec(v___x_1270_);
lean_dec(v_x_1263_);
v_x_1262_ = v_tail_1267_;
v_x_1263_ = v___x_1271_;
goto _start;
}
else
{
lean_object* v___x_1273_; 
lean_dec(v_x_1263_);
lean_inc(v_head_1266_);
v___x_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1273_, 0, v_head_1266_);
return v___x_1273_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f___boxed(lean_object* v_x_1274_, lean_object* v_x_1275_, lean_object* v_x_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_String_Pos_Raw_utf8GetAux_x3f(v_x_1274_, v_x_1275_, v_x_1276_);
lean_dec(v_x_1276_);
lean_dec(v_x_1274_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f(lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_String_Pos_Raw_utf8GetAux_x3f(v_a_1278_, v_a_1279_, v_a_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f___boxed(lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_String_utf8GetAux_x3f(v_a_1282_, v_a_1283_, v_a_1284_);
lean_dec(v_a_1284_);
lean_dec(v_a_1282_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1288_, lean_object* v_a_00___x40___internal___hyg_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1288_, v_a_00___x40___internal___hyg_1289_);
lean_dec(v_a_00___x40___internal___hyg_1289_);
lean_dec_ref(v_a_00___x40___internal___hyg_1288_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_String_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1293_, lean_object* v_a_00___x40___internal___hyg_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1293_, v_a_00___x40___internal___hyg_1294_);
lean_dec(v_a_00___x40___internal___hyg_1294_);
lean_dec_ref(v_a_00___x40___internal___hyg_1293_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x21___boxed(lean_object* v_s_1298_, lean_object* v_p_1299_){
_start:
{
uint32_t v_res_1300_; lean_object* v_r_1301_; 
v_res_1300_ = lean_string_utf8_get_bang(v_s_1298_, v_p_1299_);
lean_dec(v_p_1299_);
lean_dec_ref(v_s_1298_);
v_r_1301_ = lean_box_uint32(v_res_1300_);
return v_r_1301_;
}
}
LEAN_EXPORT lean_object* l_String_get_x21___boxed(lean_object* v_s_1304_, lean_object* v_p_1305_){
_start:
{
uint32_t v_res_1306_; lean_object* v_r_1307_; 
v_res_1306_ = lean_string_utf8_get_bang(v_s_1304_, v_p_1305_);
lean_dec(v_p_1305_);
lean_dec_ref(v_s_1304_);
v_r_1307_ = lean_box_uint32(v_res_1306_);
return v_r_1307_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux(uint32_t v_c_x27_1308_, lean_object* v_x_1309_, lean_object* v_x_1310_, lean_object* v_x_1311_){
_start:
{
if (lean_obj_tag(v_x_1309_) == 0)
{
return v_x_1309_;
}
else
{
lean_object* v_head_1312_; lean_object* v_tail_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1329_; 
v_head_1312_ = lean_ctor_get(v_x_1309_, 0);
v_tail_1313_ = lean_ctor_get(v_x_1309_, 1);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_x_1309_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1315_ = v_x_1309_;
v_isShared_1316_ = v_isSharedCheck_1329_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_tail_1313_);
lean_inc(v_head_1312_);
lean_dec(v_x_1309_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1329_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
uint8_t v___x_1317_; 
v___x_1317_ = lean_nat_dec_eq(v_x_1310_, v_x_1311_);
if (v___x_1317_ == 0)
{
uint32_t v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1318_ = lean_unbox_uint32(v_head_1312_);
v___x_1319_ = l_Char_utf8Size(v___x_1318_);
v___x_1320_ = lean_nat_add(v_x_1310_, v___x_1319_);
lean_dec(v___x_1319_);
v___x_1321_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1308_, v_tail_1313_, v___x_1320_, v_x_1311_);
lean_dec(v___x_1320_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 1, v___x_1321_);
v___x_1323_ = v___x_1315_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_head_1312_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
else
{
lean_object* v___x_1325_; lean_object* v___x_1327_; 
lean_dec(v_head_1312_);
v___x_1325_ = lean_box_uint32(v_c_x27_1308_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 0, v___x_1325_);
v___x_1327_ = v___x_1315_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1325_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_tail_1313_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux___boxed(lean_object* v_c_x27_1330_, lean_object* v_x_1331_, lean_object* v_x_1332_, lean_object* v_x_1333_){
_start:
{
uint32_t v_c_x27_boxed_1334_; lean_object* v_res_1335_; 
v_c_x27_boxed_1334_ = lean_unbox_uint32(v_c_x27_1330_);
lean_dec(v_c_x27_1330_);
v_res_1335_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_boxed_1334_, v_x_1331_, v_x_1332_, v_x_1333_);
lean_dec(v_x_1333_);
lean_dec(v_x_1332_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux(uint32_t v_c_x27_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux___boxed(lean_object* v_c_x27_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
uint32_t v_c_x27_boxed_1345_; lean_object* v_res_1346_; 
v_c_x27_boxed_1345_ = lean_unbox_uint32(v_c_x27_1341_);
lean_dec(v_c_x27_1341_);
v_res_1346_ = l_String_utf8SetAux(v_c_x27_boxed_1345_, v_a_1342_, v_a_1343_, v_a_1344_);
lean_dec(v_a_1344_);
lean_dec(v_a_1343_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg(lean_object* v_s_1347_, lean_object* v_pos_1348_){
_start:
{
lean_object* v_str_1349_; lean_object* v_startInclusive_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v_str_1349_ = lean_ctor_get(v_s_1347_, 0);
v_startInclusive_1350_ = lean_ctor_get(v_s_1347_, 1);
v___x_1351_ = lean_nat_add(v_startInclusive_1350_, v_pos_1348_);
v___x_1352_ = lean_string_utf8_next_fast(v_str_1349_, v___x_1351_);
lean_dec(v___x_1351_);
v___x_1353_ = lean_nat_sub(v___x_1352_, v_startInclusive_1350_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg___boxed(lean_object* v_s_1354_, lean_object* v_pos_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_String_Slice_Pos_nextFast___redArg(v_s_1354_, v_pos_1355_);
lean_dec(v_pos_1355_);
lean_dec_ref(v_s_1354_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast(lean_object* v_s_1357_, lean_object* v_pos_1358_, lean_object* v_h_1359_){
_start:
{
lean_object* v_str_1360_; lean_object* v_startInclusive_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v_str_1360_ = lean_ctor_get(v_s_1357_, 0);
v_startInclusive_1361_ = lean_ctor_get(v_s_1357_, 1);
v___x_1362_ = lean_nat_add(v_startInclusive_1361_, v_pos_1358_);
v___x_1363_ = lean_string_utf8_next_fast(v_str_1360_, v___x_1362_);
lean_dec(v___x_1362_);
v___x_1364_ = lean_nat_sub(v___x_1363_, v_startInclusive_1361_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___boxed(lean_object* v_s_1365_, lean_object* v_pos_1366_, lean_object* v_h_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_String_Slice_Pos_nextFast(v_s_1365_, v_pos_1366_, v_h_1367_);
lean_dec(v_pos_1366_);
lean_dec_ref(v_s_1365_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_String_sliceTo(lean_object* v_s_1369_, lean_object* v_p_1370_){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_unsigned_to_nat(0u);
v___x_1372_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1372_, 0, v_s_1369_);
lean_ctor_set(v___x_1372_, 1, v___x_1371_);
lean_ctor_set(v___x_1372_, 2, v_p_1370_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_String_replaceEnd(lean_object* v_s_1373_, lean_object* v_p_1374_){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = lean_unsigned_to_nat(0u);
v___x_1376_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1376_, 0, v_s_1373_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
lean_ctor_set(v___x_1376_, 2, v_p_1374_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_String_sliceFrom(lean_object* v_s_1377_, lean_object* v_p_1378_){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = lean_string_utf8_byte_size(v_s_1377_);
v___x_1380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1380_, 0, v_s_1377_);
lean_ctor_set(v___x_1380_, 1, v_p_1378_);
lean_ctor_set(v___x_1380_, 2, v___x_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStart(lean_object* v_s_1381_, lean_object* v_p_1382_){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = lean_string_utf8_byte_size(v_s_1381_);
v___x_1384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1384_, 0, v_s_1381_);
lean_ctor_set(v___x_1384_, 1, v_p_1382_);
lean_ctor_set(v___x_1384_, 2, v___x_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_String_slice___redArg(lean_object* v_s_1385_, lean_object* v_startInclusive_1386_, lean_object* v_endExclusive_1387_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1388_, 0, v_s_1385_);
lean_ctor_set(v___x_1388_, 1, v_startInclusive_1386_);
lean_ctor_set(v___x_1388_, 2, v_endExclusive_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_String_slice(lean_object* v_s_1389_, lean_object* v_startInclusive_1390_, lean_object* v_endExclusive_1391_, lean_object* v_h_1392_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1393_, 0, v_s_1389_);
lean_ctor_set(v___x_1393_, 1, v_startInclusive_1390_);
lean_ctor_set(v___x_1393_, 2, v_endExclusive_1391_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x3f(lean_object* v_s_1394_, lean_object* v_startInclusive_1395_, lean_object* v_endExclusive_1396_){
_start:
{
uint8_t v___x_1397_; 
v___x_1397_ = lean_nat_dec_le(v_startInclusive_1395_, v_endExclusive_1396_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; 
lean_dec(v_endExclusive_1396_);
lean_dec(v_startInclusive_1395_);
lean_dec_ref(v_s_1394_);
v___x_1398_ = lean_box(0);
return v___x_1398_;
}
else
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1399_, 0, v_s_1394_);
lean_ctor_set(v___x_1399_, 1, v_startInclusive_1395_);
lean_ctor_set(v___x_1399_, 2, v_endExclusive_1396_);
v___x_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
return v___x_1400_;
}
}
}
LEAN_EXPORT lean_object* l_String_slice_x21(lean_object* v_s_1401_, lean_object* v_p_u2081_1402_, lean_object* v_p_u2082_1403_){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1404_ = lean_unsigned_to_nat(0u);
v___x_1405_ = lean_string_utf8_byte_size(v_s_1401_);
v___x_1406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1406_, 0, v_s_1401_);
lean_ctor_set(v___x_1406_, 1, v___x_1404_);
lean_ctor_set(v___x_1406_, 2, v___x_1405_);
v___x_1407_ = l_String_Slice_slice_x21(v___x_1406_, v_p_u2081_1402_, v_p_u2082_1403_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x21___boxed(lean_object* v_s_1408_, lean_object* v_p_u2081_1409_, lean_object* v_p_u2082_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_String_slice_x21(v_s_1408_, v_p_u2081_1409_, v_p_u2082_1410_);
lean_dec(v_p_u2082_1410_);
lean_dec(v_p_u2081_1409_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21(lean_object* v_s_1412_, lean_object* v_p_u2081_1413_, lean_object* v_p_u2082_1414_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_String_slice_x21(v_s_1412_, v_p_u2081_1413_, v_p_u2082_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21___boxed(lean_object* v_s_1416_, lean_object* v_p_u2081_1417_, lean_object* v_p_u2082_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_String_replaceStartEnd_x21(v_s_1416_, v_p_u2081_1417_, v_p_u2082_1418_);
lean_dec(v_p_u2082_1418_);
lean_dec(v_p_u2081_1417_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg(lean_object* v_p_u2080_1420_, lean_object* v_pos_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = lean_nat_add(v_p_u2080_1420_, v_pos_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg___boxed(lean_object* v_p_u2080_1423_, lean_object* v_pos_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_String_Pos_ofSliceFrom___redArg(v_p_u2080_1423_, v_pos_1424_);
lean_dec(v_pos_1424_);
lean_dec(v_p_u2080_1423_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom(lean_object* v_s_1426_, lean_object* v_p_u2080_1427_, lean_object* v_pos_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_nat_add(v_p_u2080_1427_, v_pos_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___boxed(lean_object* v_s_1430_, lean_object* v_p_u2080_1431_, lean_object* v_pos_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_String_Pos_ofSliceFrom(v_s_1430_, v_p_u2080_1431_, v_pos_1432_);
lean_dec(v_pos_1432_);
lean_dec(v_p_u2080_1431_);
lean_dec_ref(v_s_1430_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg(lean_object* v_p_u2080_1434_, lean_object* v_pos_1435_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_nat_add(v_p_u2080_1434_, v_pos_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg___boxed(lean_object* v_p_u2080_1437_, lean_object* v_pos_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_String_Pos_ofReplaceStart___redArg(v_p_u2080_1437_, v_pos_1438_);
lean_dec(v_pos_1438_);
lean_dec(v_p_u2080_1437_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart(lean_object* v_s_1440_, lean_object* v_p_u2080_1441_, lean_object* v_pos_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_nat_add(v_p_u2080_1441_, v_pos_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___boxed(lean_object* v_s_1444_, lean_object* v_p_u2080_1445_, lean_object* v_pos_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_String_Pos_ofReplaceStart(v_s_1444_, v_p_u2080_1445_, v_pos_1446_);
lean_dec(v_pos_1446_);
lean_dec(v_p_u2080_1445_);
lean_dec_ref(v_s_1444_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg(lean_object* v_p_u2080_1448_, lean_object* v_pos_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_nat_sub(v_pos_1449_, v_p_u2080_1448_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg___boxed(lean_object* v_p_u2080_1451_, lean_object* v_pos_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_String_Pos_sliceFrom___redArg(v_p_u2080_1451_, v_pos_1452_);
lean_dec(v_pos_1452_);
lean_dec(v_p_u2080_1451_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom(lean_object* v_s_1454_, lean_object* v_p_u2080_1455_, lean_object* v_pos_1456_, lean_object* v_h_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = lean_nat_sub(v_pos_1456_, v_p_u2080_1455_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___boxed(lean_object* v_s_1459_, lean_object* v_p_u2080_1460_, lean_object* v_pos_1461_, lean_object* v_h_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_String_Pos_sliceFrom(v_s_1459_, v_p_u2080_1460_, v_pos_1461_, v_h_1462_);
lean_dec(v_pos_1461_);
lean_dec(v_p_u2080_1460_);
lean_dec_ref(v_s_1459_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg(lean_object* v_p_u2080_1464_, lean_object* v_pos_1465_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = lean_nat_sub(v_pos_1465_, v_p_u2080_1464_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg___boxed(lean_object* v_p_u2080_1467_, lean_object* v_pos_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_String_Pos_toReplaceStart___redArg(v_p_u2080_1467_, v_pos_1468_);
lean_dec(v_pos_1468_);
lean_dec(v_p_u2080_1467_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart(lean_object* v_s_1470_, lean_object* v_p_u2080_1471_, lean_object* v_pos_1472_, lean_object* v_h_1473_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = lean_nat_sub(v_pos_1472_, v_p_u2080_1471_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___boxed(lean_object* v_s_1475_, lean_object* v_p_u2080_1476_, lean_object* v_pos_1477_, lean_object* v_h_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_String_Pos_toReplaceStart(v_s_1475_, v_p_u2080_1476_, v_pos_1477_, v_h_1478_);
lean_dec(v_pos_1477_);
lean_dec(v_p_u2080_1476_);
lean_dec_ref(v_s_1475_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg(lean_object* v_pos_1480_){
_start:
{
lean_inc(v_pos_1480_);
return v_pos_1480_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg___boxed(lean_object* v_pos_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_String_Pos_ofSliceTo___redArg(v_pos_1481_);
lean_dec(v_pos_1481_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo(lean_object* v_s_1483_, lean_object* v_p_u2080_1484_, lean_object* v_pos_1485_){
_start:
{
lean_inc(v_pos_1485_);
return v_pos_1485_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___boxed(lean_object* v_s_1486_, lean_object* v_p_u2080_1487_, lean_object* v_pos_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_String_Pos_ofSliceTo(v_s_1486_, v_p_u2080_1487_, v_pos_1488_);
lean_dec(v_pos_1488_);
lean_dec(v_p_u2080_1487_);
lean_dec_ref(v_s_1486_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg(lean_object* v_pos_1490_){
_start:
{
lean_inc(v_pos_1490_);
return v_pos_1490_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg___boxed(lean_object* v_pos_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_String_Pos_ofReplaceEnd___redArg(v_pos_1491_);
lean_dec(v_pos_1491_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd(lean_object* v_s_1493_, lean_object* v_p_u2080_1494_, lean_object* v_pos_1495_){
_start:
{
lean_inc(v_pos_1495_);
return v_pos_1495_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___boxed(lean_object* v_s_1496_, lean_object* v_p_u2080_1497_, lean_object* v_pos_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_String_Pos_ofReplaceEnd(v_s_1496_, v_p_u2080_1497_, v_pos_1498_);
lean_dec(v_pos_1498_);
lean_dec(v_p_u2080_1497_);
lean_dec_ref(v_s_1496_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg(lean_object* v_pos_1500_){
_start:
{
lean_inc(v_pos_1500_);
return v_pos_1500_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg___boxed(lean_object* v_pos_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_String_Pos_sliceTo___redArg(v_pos_1501_);
lean_dec(v_pos_1501_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo(lean_object* v_s_1503_, lean_object* v_p_u2080_1504_, lean_object* v_pos_1505_, lean_object* v_h_1506_){
_start:
{
lean_inc(v_pos_1505_);
return v_pos_1505_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___boxed(lean_object* v_s_1507_, lean_object* v_p_u2080_1508_, lean_object* v_pos_1509_, lean_object* v_h_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_String_Pos_sliceTo(v_s_1507_, v_p_u2080_1508_, v_pos_1509_, v_h_1510_);
lean_dec(v_pos_1509_);
lean_dec(v_p_u2080_1508_);
lean_dec_ref(v_s_1507_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg(lean_object* v_pos_1512_){
_start:
{
lean_inc(v_pos_1512_);
return v_pos_1512_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg___boxed(lean_object* v_pos_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_String_Pos_toReplaceEnd___redArg(v_pos_1513_);
lean_dec(v_pos_1513_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd(lean_object* v_s_1515_, lean_object* v_p_u2080_1516_, lean_object* v_pos_1517_, lean_object* v_h_1518_){
_start:
{
lean_inc(v_pos_1517_);
return v_pos_1517_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___boxed(lean_object* v_s_1519_, lean_object* v_p_u2080_1520_, lean_object* v_pos_1521_, lean_object* v_h_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_String_Pos_toReplaceEnd(v_s_1519_, v_p_u2080_1520_, v_pos_1521_, v_h_1522_);
lean_dec(v_pos_1521_);
lean_dec(v_p_u2080_1520_);
lean_dec_ref(v_s_1519_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg(lean_object* v_p_u2080_1524_, lean_object* v_pos_1525_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_nat_add(v_p_u2080_1524_, v_pos_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1527_, lean_object* v_pos_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_String_Slice_Pos_ofSlice___redArg(v_p_u2080_1527_, v_pos_1528_);
lean_dec(v_pos_1528_);
lean_dec(v_p_u2080_1527_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice(lean_object* v_s_1530_, lean_object* v_p_u2080_1531_, lean_object* v_p_u2081_1532_, lean_object* v_h_1533_, lean_object* v_pos_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_nat_add(v_p_u2080_1531_, v_pos_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___boxed(lean_object* v_s_1536_, lean_object* v_p_u2080_1537_, lean_object* v_p_u2081_1538_, lean_object* v_h_1539_, lean_object* v_pos_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_String_Slice_Pos_ofSlice(v_s_1536_, v_p_u2080_1537_, v_p_u2081_1538_, v_h_1539_, v_pos_1540_);
lean_dec(v_pos_1540_);
lean_dec(v_p_u2081_1538_);
lean_dec(v_p_u2080_1537_);
lean_dec_ref(v_s_1536_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg(lean_object* v_p_u2080_1542_, lean_object* v_pos_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_nat_add(v_p_u2080_1542_, v_pos_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1545_, lean_object* v_pos_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_String_Pos_ofSlice___redArg(v_p_u2080_1545_, v_pos_1546_);
lean_dec(v_pos_1546_);
lean_dec(v_p_u2080_1545_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice(lean_object* v_s_1548_, lean_object* v_p_u2080_1549_, lean_object* v_p_u2081_1550_, lean_object* v_h_1551_, lean_object* v_pos_1552_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_nat_add(v_p_u2080_1549_, v_pos_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___boxed(lean_object* v_s_1554_, lean_object* v_p_u2080_1555_, lean_object* v_p_u2081_1556_, lean_object* v_h_1557_, lean_object* v_pos_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_String_Pos_ofSlice(v_s_1554_, v_p_u2080_1555_, v_p_u2081_1556_, v_h_1557_, v_pos_1558_);
lean_dec(v_pos_1558_);
lean_dec(v_p_u2081_1556_);
lean_dec(v_p_u2080_1555_);
lean_dec_ref(v_s_1554_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg(lean_object* v_pos_1560_, lean_object* v_p_u2080_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_nat_sub(v_pos_1560_, v_p_u2080_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg___boxed(lean_object* v_pos_1563_, lean_object* v_p_u2080_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_String_Slice_Pos_slice___redArg(v_pos_1563_, v_p_u2080_1564_);
lean_dec(v_p_u2080_1564_);
lean_dec(v_pos_1563_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice(lean_object* v_s_1566_, lean_object* v_pos_1567_, lean_object* v_p_u2080_1568_, lean_object* v_p_u2081_1569_, lean_object* v_h_u2081_1570_, lean_object* v_h_u2082_1571_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = lean_nat_sub(v_pos_1567_, v_p_u2080_1568_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___boxed(lean_object* v_s_1573_, lean_object* v_pos_1574_, lean_object* v_p_u2080_1575_, lean_object* v_p_u2081_1576_, lean_object* v_h_u2081_1577_, lean_object* v_h_u2082_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_String_Slice_Pos_slice(v_s_1573_, v_pos_1574_, v_p_u2080_1575_, v_p_u2081_1576_, v_h_u2081_1577_, v_h_u2082_1578_);
lean_dec(v_p_u2081_1576_);
lean_dec(v_p_u2080_1575_);
lean_dec(v_pos_1574_);
lean_dec_ref(v_s_1573_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg(lean_object* v_pos_1580_, lean_object* v_p_u2080_1581_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_nat_sub(v_pos_1580_, v_p_u2080_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg___boxed(lean_object* v_pos_1583_, lean_object* v_p_u2080_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_String_Pos_slice___redArg(v_pos_1583_, v_p_u2080_1584_);
lean_dec(v_p_u2080_1584_);
lean_dec(v_pos_1583_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice(lean_object* v_s_1586_, lean_object* v_pos_1587_, lean_object* v_p_u2080_1588_, lean_object* v_p_u2081_1589_, lean_object* v_h_u2081_1590_, lean_object* v_h_u2082_1591_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = lean_nat_sub(v_pos_1587_, v_p_u2080_1588_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___boxed(lean_object* v_s_1593_, lean_object* v_pos_1594_, lean_object* v_p_u2080_1595_, lean_object* v_p_u2081_1596_, lean_object* v_h_u2081_1597_, lean_object* v_h_u2082_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_String_Pos_slice(v_s_1593_, v_pos_1594_, v_p_u2080_1595_, v_p_u2081_1596_, v_h_u2081_1597_, v_h_u2082_1598_);
lean_dec(v_p_u2081_1596_);
lean_dec(v_p_u2080_1595_);
lean_dec(v_pos_1594_);
lean_dec_ref(v_s_1593_);
return v_res_1599_;
}
}
static lean_object* _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2(void){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1602_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__1));
v___x_1603_ = lean_unsigned_to_nat(4u);
v___x_1604_ = lean_unsigned_to_nat(2706u);
v___x_1605_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__0));
v___x_1606_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1607_ = l_mkPanicMessageWithDecl(v___x_1606_, v___x_1605_, v___x_1604_, v___x_1603_, v___x_1602_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg(lean_object* v_pos_1608_, lean_object* v_p_u2080_1609_, lean_object* v_p_u2081_1610_){
_start:
{
uint8_t v___x_1615_; 
v___x_1615_ = lean_nat_dec_le(v_p_u2080_1609_, v_pos_1608_);
if (v___x_1615_ == 0)
{
goto v___jp_1611_;
}
else
{
uint8_t v___x_1616_; 
v___x_1616_ = lean_nat_dec_le(v_pos_1608_, v_p_u2081_1610_);
if (v___x_1616_ == 0)
{
goto v___jp_1611_;
}
else
{
lean_object* v___x_1617_; 
v___x_1617_ = lean_nat_sub(v_pos_1608_, v_p_u2080_1609_);
return v___x_1617_;
}
}
v___jp_1611_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1612_ = lean_unsigned_to_nat(0u);
v___x_1613_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1614_ = l_panic___redArg(v___x_1612_, v___x_1613_);
return v___x_1614_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1618_, lean_object* v_p_u2080_1619_, lean_object* v_p_u2081_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_String_Slice_Pos_sliceOrPanic___redArg(v_pos_1618_, v_p_u2080_1619_, v_p_u2081_1620_);
lean_dec(v_p_u2081_1620_);
lean_dec(v_p_u2080_1619_);
lean_dec(v_pos_1618_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic(lean_object* v_s_1622_, lean_object* v_pos_1623_, lean_object* v_p_u2080_1624_, lean_object* v_p_u2081_1625_, lean_object* v_h_1626_){
_start:
{
uint8_t v___x_1631_; 
v___x_1631_ = lean_nat_dec_le(v_p_u2080_1624_, v_pos_1623_);
if (v___x_1631_ == 0)
{
goto v___jp_1627_;
}
else
{
uint8_t v___x_1632_; 
v___x_1632_ = lean_nat_dec_le(v_pos_1623_, v_p_u2081_1625_);
if (v___x_1632_ == 0)
{
goto v___jp_1627_;
}
else
{
lean_object* v___x_1633_; 
v___x_1633_ = lean_nat_sub(v_pos_1623_, v_p_u2080_1624_);
return v___x_1633_;
}
}
v___jp_1627_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1628_ = lean_unsigned_to_nat(0u);
v___x_1629_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1630_ = l_panic___redArg(v___x_1628_, v___x_1629_);
return v___x_1630_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___boxed(lean_object* v_s_1634_, lean_object* v_pos_1635_, lean_object* v_p_u2080_1636_, lean_object* v_p_u2081_1637_, lean_object* v_h_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_String_Slice_Pos_sliceOrPanic(v_s_1634_, v_pos_1635_, v_p_u2080_1636_, v_p_u2081_1637_, v_h_1638_);
lean_dec(v_p_u2081_1637_);
lean_dec(v_p_u2080_1636_);
lean_dec(v_pos_1635_);
lean_dec_ref(v_s_1634_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg(lean_object* v_pos_1640_, lean_object* v_p_u2080_1641_, lean_object* v_p_u2081_1642_){
_start:
{
uint8_t v___x_1647_; 
v___x_1647_ = lean_nat_dec_le(v_p_u2080_1641_, v_pos_1640_);
if (v___x_1647_ == 0)
{
goto v___jp_1643_;
}
else
{
uint8_t v___x_1648_; 
v___x_1648_ = lean_nat_dec_le(v_pos_1640_, v_p_u2081_1642_);
if (v___x_1648_ == 0)
{
goto v___jp_1643_;
}
else
{
lean_object* v___x_1649_; 
v___x_1649_ = lean_nat_sub(v_pos_1640_, v_p_u2080_1641_);
return v___x_1649_;
}
}
v___jp_1643_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1644_ = lean_unsigned_to_nat(0u);
v___x_1645_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1646_ = l_panic___redArg(v___x_1644_, v___x_1645_);
return v___x_1646_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1650_, lean_object* v_p_u2080_1651_, lean_object* v_p_u2081_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_String_Pos_sliceOrPanic___redArg(v_pos_1650_, v_p_u2080_1651_, v_p_u2081_1652_);
lean_dec(v_p_u2081_1652_);
lean_dec(v_p_u2080_1651_);
lean_dec(v_pos_1650_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic(lean_object* v_s_1654_, lean_object* v_pos_1655_, lean_object* v_p_u2080_1656_, lean_object* v_p_u2081_1657_, lean_object* v_h_1658_){
_start:
{
uint8_t v___x_1663_; 
v___x_1663_ = lean_nat_dec_le(v_p_u2080_1656_, v_pos_1655_);
if (v___x_1663_ == 0)
{
goto v___jp_1659_;
}
else
{
uint8_t v___x_1664_; 
v___x_1664_ = lean_nat_dec_le(v_pos_1655_, v_p_u2081_1657_);
if (v___x_1664_ == 0)
{
goto v___jp_1659_;
}
else
{
lean_object* v___x_1665_; 
v___x_1665_ = lean_nat_sub(v_pos_1655_, v_p_u2080_1656_);
return v___x_1665_;
}
}
v___jp_1659_:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1660_ = lean_unsigned_to_nat(0u);
v___x_1661_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1662_ = l_panic___redArg(v___x_1660_, v___x_1661_);
return v___x_1662_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___boxed(lean_object* v_s_1666_, lean_object* v_pos_1667_, lean_object* v_p_u2080_1668_, lean_object* v_p_u2081_1669_, lean_object* v_h_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_String_Pos_sliceOrPanic(v_s_1666_, v_pos_1667_, v_p_u2080_1668_, v_p_u2081_1669_, v_h_1670_);
lean_dec(v_p_u2081_1669_);
lean_dec(v_p_u2080_1668_);
lean_dec(v_pos_1667_);
lean_dec_ref(v_s_1666_);
return v_res_1671_;
}
}
static lean_object* _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1673_ = ((lean_object*)(l_String_Slice_slice_x21___closed__1));
v___x_1674_ = lean_unsigned_to_nat(4u);
v___x_1675_ = lean_unsigned_to_nat(2730u);
v___x_1676_ = ((lean_object*)(l_String_Slice_Pos_ofSlice_x21___redArg___closed__0));
v___x_1677_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1678_ = l_mkPanicMessageWithDecl(v___x_1677_, v___x_1676_, v___x_1675_, v___x_1674_, v___x_1673_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1679_, lean_object* v_p_u2081_1680_, lean_object* v_pos_1681_){
_start:
{
uint8_t v___x_1682_; 
v___x_1682_ = lean_nat_dec_le(v_p_u2080_1679_, v_p_u2081_1680_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = lean_unsigned_to_nat(0u);
v___x_1684_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1685_ = l_panic___redArg(v___x_1683_, v___x_1684_);
return v___x_1685_;
}
else
{
lean_object* v___x_1686_; 
v___x_1686_ = lean_nat_add(v_p_u2080_1679_, v_pos_1681_);
return v___x_1686_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1687_, lean_object* v_p_u2081_1688_, lean_object* v_pos_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_String_Slice_Pos_ofSlice_x21___redArg(v_p_u2080_1687_, v_p_u2081_1688_, v_pos_1689_);
lean_dec(v_pos_1689_);
lean_dec(v_p_u2081_1688_);
lean_dec(v_p_u2080_1687_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21(lean_object* v_s_1691_, lean_object* v_p_u2080_1692_, lean_object* v_p_u2081_1693_, lean_object* v_pos_1694_){
_start:
{
uint8_t v___x_1695_; 
v___x_1695_ = lean_nat_dec_le(v_p_u2080_1692_, v_p_u2081_1693_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1696_ = lean_unsigned_to_nat(0u);
v___x_1697_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1698_ = l_panic___redArg(v___x_1696_, v___x_1697_);
return v___x_1698_;
}
else
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_nat_add(v_p_u2080_1692_, v_pos_1694_);
return v___x_1699_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___boxed(lean_object* v_s_1700_, lean_object* v_p_u2080_1701_, lean_object* v_p_u2081_1702_, lean_object* v_pos_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_String_Slice_Pos_ofSlice_x21(v_s_1700_, v_p_u2080_1701_, v_p_u2081_1702_, v_pos_1703_);
lean_dec(v_pos_1703_);
lean_dec(v_p_u2081_1702_);
lean_dec(v_p_u2080_1701_);
lean_dec_ref(v_s_1700_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1705_, lean_object* v_p_u2081_1706_, lean_object* v_pos_1707_){
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
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1713_, lean_object* v_p_u2081_1714_, lean_object* v_pos_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_String_Pos_ofSlice_x21___redArg(v_p_u2080_1713_, v_p_u2081_1714_, v_pos_1715_);
lean_dec(v_pos_1715_);
lean_dec(v_p_u2081_1714_);
lean_dec(v_p_u2080_1713_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21(lean_object* v_s_1717_, lean_object* v_p_u2080_1718_, lean_object* v_p_u2081_1719_, lean_object* v_pos_1720_){
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
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___boxed(lean_object* v_s_1726_, lean_object* v_p_u2080_1727_, lean_object* v_p_u2081_1728_, lean_object* v_pos_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_String_Pos_ofSlice_x21(v_s_1726_, v_p_u2080_1727_, v_p_u2081_1728_, v_pos_1729_);
lean_dec(v_pos_1729_);
lean_dec(v_p_u2081_1728_);
lean_dec(v_p_u2080_1727_);
lean_dec_ref(v_s_1726_);
return v_res_1730_;
}
}
static lean_object* _init_l_String_Slice_Pos_slice_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1733_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__1));
v___x_1734_ = lean_unsigned_to_nat(4u);
v___x_1735_ = lean_unsigned_to_nat(2748u);
v___x_1736_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__0));
v___x_1737_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1738_ = l_mkPanicMessageWithDecl(v___x_1737_, v___x_1736_, v___x_1735_, v___x_1734_, v___x_1733_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg(lean_object* v_pos_1739_, lean_object* v_p_u2080_1740_, lean_object* v_p_u2081_1741_){
_start:
{
uint8_t v___x_1746_; 
v___x_1746_ = lean_nat_dec_le(v_p_u2080_1740_, v_pos_1739_);
if (v___x_1746_ == 0)
{
goto v___jp_1742_;
}
else
{
uint8_t v___x_1747_; 
v___x_1747_ = lean_nat_dec_le(v_pos_1739_, v_p_u2081_1741_);
if (v___x_1747_ == 0)
{
goto v___jp_1742_;
}
else
{
lean_object* v___x_1748_; 
v___x_1748_ = lean_nat_sub(v_pos_1739_, v_p_u2080_1740_);
return v___x_1748_;
}
}
v___jp_1742_:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1743_ = lean_unsigned_to_nat(0u);
v___x_1744_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1745_ = l_panic___redArg(v___x_1743_, v___x_1744_);
return v___x_1745_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1749_, lean_object* v_p_u2080_1750_, lean_object* v_p_u2081_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_String_Slice_Pos_slice_x21___redArg(v_pos_1749_, v_p_u2080_1750_, v_p_u2081_1751_);
lean_dec(v_p_u2081_1751_);
lean_dec(v_p_u2080_1750_);
lean_dec(v_pos_1749_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21(lean_object* v_s_1753_, lean_object* v_pos_1754_, lean_object* v_p_u2080_1755_, lean_object* v_p_u2081_1756_){
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
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___boxed(lean_object* v_s_1764_, lean_object* v_pos_1765_, lean_object* v_p_u2080_1766_, lean_object* v_p_u2081_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_String_Slice_Pos_slice_x21(v_s_1764_, v_pos_1765_, v_p_u2080_1766_, v_p_u2081_1767_);
lean_dec(v_p_u2081_1767_);
lean_dec(v_p_u2080_1766_);
lean_dec(v_pos_1765_);
lean_dec_ref(v_s_1764_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg(lean_object* v_pos_1769_, lean_object* v_p_u2080_1770_, lean_object* v_p_u2081_1771_){
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
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1779_, lean_object* v_p_u2080_1780_, lean_object* v_p_u2081_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_String_Pos_slice_x21___redArg(v_pos_1779_, v_p_u2080_1780_, v_p_u2081_1781_);
lean_dec(v_p_u2081_1781_);
lean_dec(v_p_u2080_1780_);
lean_dec(v_pos_1779_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21(lean_object* v_s_1783_, lean_object* v_pos_1784_, lean_object* v_p_u2080_1785_, lean_object* v_p_u2081_1786_){
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
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___boxed(lean_object* v_s_1794_, lean_object* v_pos_1795_, lean_object* v_p_u2080_1796_, lean_object* v_p_u2081_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_String_Pos_slice_x21(v_s_1794_, v_pos_1795_, v_p_u2080_1796_, v_p_u2081_1797_);
lean_dec(v_p_u2081_1797_);
lean_dec(v_p_u2080_1796_);
lean_dec(v_pos_1795_);
lean_dec_ref(v_s_1794_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract(lean_object* v_s_1799_, lean_object* v_p_u2080_1800_, lean_object* v_p_u2081_1801_){
_start:
{
lean_object* v_str_1802_; lean_object* v_startInclusive_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v_str_1802_ = lean_ctor_get(v_s_1799_, 0);
v_startInclusive_1803_ = lean_ctor_get(v_s_1799_, 1);
v___x_1804_ = lean_nat_add(v_startInclusive_1803_, v_p_u2080_1800_);
v___x_1805_ = lean_nat_add(v_startInclusive_1803_, v_p_u2081_1801_);
v___x_1806_ = lean_string_utf8_extract(v_str_1802_, v___x_1804_, v___x_1805_);
lean_dec(v___x_1805_);
lean_dec(v___x_1804_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract___boxed(lean_object* v_s_1807_, lean_object* v_p_u2080_1808_, lean_object* v_p_u2081_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_String_Slice_extract(v_s_1807_, v_p_u2080_1808_, v_p_u2081_1809_);
lean_dec(v_p_u2081_1809_);
lean_dec(v_p_u2080_1808_);
lean_dec_ref(v_s_1807_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn(lean_object* v_s_1811_, lean_object* v_p_1812_, lean_object* v_n_1813_){
_start:
{
lean_object* v_str_1814_; lean_object* v_startInclusive_1815_; lean_object* v_endExclusive_1816_; lean_object* v_zero_1817_; uint8_t v_isZero_1818_; 
v_str_1814_ = lean_ctor_get(v_s_1811_, 0);
v_startInclusive_1815_ = lean_ctor_get(v_s_1811_, 1);
v_endExclusive_1816_ = lean_ctor_get(v_s_1811_, 2);
v_zero_1817_ = lean_unsigned_to_nat(0u);
v_isZero_1818_ = lean_nat_dec_eq(v_n_1813_, v_zero_1817_);
if (v_isZero_1818_ == 1)
{
lean_dec(v_n_1813_);
return v_p_1812_;
}
else
{
lean_object* v___x_1819_; uint8_t v___x_1820_; lean_object* v_one_1821_; lean_object* v_n_1822_; 
v___x_1819_ = lean_nat_sub(v_endExclusive_1816_, v_startInclusive_1815_);
v___x_1820_ = lean_nat_dec_eq(v_p_1812_, v___x_1819_);
lean_dec(v___x_1819_);
v_one_1821_ = lean_unsigned_to_nat(1u);
v_n_1822_ = lean_nat_sub(v_n_1813_, v_one_1821_);
lean_dec(v_n_1813_);
if (v___x_1820_ == 0)
{
goto v___jp_1823_;
}
else
{
if (v_isZero_1818_ == 0)
{
lean_dec(v_n_1822_);
return v_p_1812_;
}
else
{
goto v___jp_1823_;
}
}
v___jp_1823_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1824_ = lean_nat_add(v_startInclusive_1815_, v_p_1812_);
lean_dec(v_p_1812_);
v___x_1825_ = lean_string_utf8_next_fast(v_str_1814_, v___x_1824_);
lean_dec(v___x_1824_);
v___x_1826_ = lean_nat_sub(v___x_1825_, v_startInclusive_1815_);
v_p_1812_ = v___x_1826_;
v_n_1813_ = v_n_1822_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn___boxed(lean_object* v_s_1828_, lean_object* v_p_1829_, lean_object* v_n_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_String_Slice_Pos_nextn(v_s_1828_, v_p_1829_, v_n_1830_);
lean_dec_ref(v_s_1828_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_nextn(lean_object* v_s_1832_, lean_object* v_p_1833_, lean_object* v_n_1834_){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1835_ = lean_unsigned_to_nat(0u);
v___x_1836_ = lean_string_utf8_byte_size(v_s_1832_);
v___x_1837_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1837_, 0, v_s_1832_);
lean_ctor_set(v___x_1837_, 1, v___x_1835_);
lean_ctor_set(v___x_1837_, 2, v___x_1836_);
v___x_1838_ = l_String_Slice_Pos_nextn(v___x_1837_, v_p_1833_, v_n_1834_);
lean_dec_ref(v___x_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(lean_object* v_n_1839_, lean_object* v_h__1_1840_, lean_object* v_h__2_1841_){
_start:
{
lean_object* v_zero_1842_; uint8_t v_isZero_1843_; 
v_zero_1842_ = lean_unsigned_to_nat(0u);
v_isZero_1843_ = lean_nat_dec_eq(v_n_1839_, v_zero_1842_);
if (v_isZero_1843_ == 1)
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_dec(v_h__2_1841_);
v___x_1844_ = lean_box(0);
v___x_1845_ = lean_apply_1(v_h__1_1840_, v___x_1844_);
return v___x_1845_;
}
else
{
lean_object* v_one_1846_; lean_object* v_n_1847_; lean_object* v___x_1848_; 
lean_dec(v_h__1_1840_);
v_one_1846_ = lean_unsigned_to_nat(1u);
v_n_1847_ = lean_nat_sub(v_n_1839_, v_one_1846_);
v___x_1848_ = lean_apply_1(v_h__2_1841_, v_n_1847_);
return v___x_1848_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg___boxed(lean_object* v_n_1849_, lean_object* v_h__1_1850_, lean_object* v_h__2_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(v_n_1849_, v_h__1_1850_, v_h__2_1851_);
lean_dec(v_n_1849_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(lean_object* v_motive_1853_, lean_object* v_n_1854_, lean_object* v_h__1_1855_, lean_object* v_h__2_1856_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___boxed(lean_object* v_motive_1864_, lean_object* v_n_1865_, lean_object* v_h__1_1866_, lean_object* v_h__2_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(v_motive_1864_, v_n_1865_, v_h__1_1866_, v_h__2_1867_);
lean_dec(v_n_1865_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next___boxed(lean_object* v_s_1871_, lean_object* v_p_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = lean_string_utf8_next(v_s_1871_, v_p_1872_);
lean_dec(v_p_1872_);
lean_dec_ref(v_s_1871_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_String_next___boxed(lean_object* v_s_1876_, lean_object* v_p_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = lean_string_utf8_next(v_s_1876_, v_p_1877_);
lean_dec(v_p_1877_);
lean_dec_ref(v_s_1876_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux(lean_object* v_x_1879_, lean_object* v_x_1880_, lean_object* v_x_1881_){
_start:
{
if (lean_obj_tag(v_x_1879_) == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_dec(v_x_1880_);
v___x_1882_ = lean_unsigned_to_nat(1u);
v___x_1883_ = lean_nat_sub(v_x_1881_, v___x_1882_);
return v___x_1883_;
}
else
{
lean_object* v_head_1884_; lean_object* v_tail_1885_; uint32_t v___x_1886_; lean_object* v___x_1887_; lean_object* v_i_x27_1888_; uint8_t v___x_1889_; 
v_head_1884_ = lean_ctor_get(v_x_1879_, 0);
v_tail_1885_ = lean_ctor_get(v_x_1879_, 1);
v___x_1886_ = lean_unbox_uint32(v_head_1884_);
v___x_1887_ = l_Char_utf8Size(v___x_1886_);
v_i_x27_1888_ = lean_nat_add(v_x_1880_, v___x_1887_);
lean_dec(v___x_1887_);
v___x_1889_ = lean_nat_dec_le(v_x_1881_, v_i_x27_1888_);
if (v___x_1889_ == 0)
{
lean_dec(v_x_1880_);
v_x_1879_ = v_tail_1885_;
v_x_1880_ = v_i_x27_1888_;
goto _start;
}
else
{
lean_dec(v_i_x27_1888_);
return v_x_1880_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux___boxed(lean_object* v_x_1891_, lean_object* v_x_1892_, lean_object* v_x_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_String_Pos_Raw_utf8PrevAux(v_x_1891_, v_x_1892_, v_x_1893_);
lean_dec(v_x_1893_);
lean_dec(v_x_1891_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux(lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_String_Pos_Raw_utf8PrevAux(v_a_1895_, v_a_1896_, v_a_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux___boxed(lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_String_utf8PrevAux(v_a_1899_, v_a_1900_, v_a_1901_);
lean_dec(v_a_1901_);
lean_dec(v_a_1899_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_prev___boxed(lean_object* v_a_00___x40___internal___hyg_1905_, lean_object* v_a_00___x40___internal___hyg_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_1905_, v_a_00___x40___internal___hyg_1906_);
lean_dec(v_a_00___x40___internal___hyg_1906_);
lean_dec_ref(v_a_00___x40___internal___hyg_1905_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_String_prev___boxed(lean_object* v_a_00___x40___internal___hyg_1910_, lean_object* v_a_00___x40___internal___hyg_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_1910_, v_a_00___x40___internal___hyg_1911_);
lean_dec(v_a_00___x40___internal___hyg_1911_);
lean_dec_ref(v_a_00___x40___internal___hyg_1910_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_1915_, lean_object* v_a_00___x40___internal___hyg_1916_){
_start:
{
uint8_t v_res_1917_; lean_object* v_r_1918_; 
v_res_1917_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_1915_, v_a_00___x40___internal___hyg_1916_);
lean_dec(v_a_00___x40___internal___hyg_1916_);
lean_dec_ref(v_a_00___x40___internal___hyg_1915_);
v_r_1918_ = lean_box(v_res_1917_);
return v_r_1918_;
}
}
LEAN_EXPORT lean_object* l_String_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_1921_, lean_object* v_a_00___x40___internal___hyg_1922_){
_start:
{
uint8_t v_res_1923_; lean_object* v_r_1924_; 
v_res_1923_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_1921_, v_a_00___x40___internal___hyg_1922_);
lean_dec(v_a_00___x40___internal___hyg_1922_);
lean_dec_ref(v_a_00___x40___internal___hyg_1921_);
v_r_1924_ = lean_box(v_res_1923_);
return v_r_1924_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x27___boxed(lean_object* v_s_1928_, lean_object* v_p_1929_, lean_object* v_h_1930_){
_start:
{
uint32_t v_res_1931_; lean_object* v_r_1932_; 
v_res_1931_ = lean_string_utf8_get_fast(v_s_1928_, v_p_1929_);
lean_dec(v_p_1929_);
lean_dec_ref(v_s_1928_);
v_r_1932_ = lean_box_uint32(v_res_1931_);
return v_r_1932_;
}
}
LEAN_EXPORT lean_object* l_String_get_x27___boxed(lean_object* v_s_1936_, lean_object* v_p_1937_, lean_object* v_h_1938_){
_start:
{
uint32_t v_res_1939_; lean_object* v_r_1940_; 
v_res_1939_ = lean_string_utf8_get_fast(v_s_1936_, v_p_1937_);
lean_dec(v_p_1937_);
lean_dec_ref(v_s_1936_);
v_r_1940_ = lean_box_uint32(v_res_1939_);
return v_r_1940_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next_x27___boxed(lean_object* v_s_1944_, lean_object* v_p_1945_, lean_object* v_h_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = lean_string_utf8_next_fast(v_s_1944_, v_p_1945_);
lean_dec(v_p_1945_);
lean_dec_ref(v_s_1944_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_String_next_x27___boxed(lean_object* v_s_1951_, lean_object* v_p_1952_, lean_object* v_h_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = lean_string_utf8_next_fast(v_s_1951_, v_p_1952_);
lean_dec(v_p_1952_);
lean_dec_ref(v_s_1951_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter___redArg(lean_object* v_x_1955_, lean_object* v_x_1956_, lean_object* v_x_1957_, lean_object* v_h__1_1958_, lean_object* v_h__2_1959_){
_start:
{
if (lean_obj_tag(v_x_1955_) == 0)
{
lean_object* v___x_1960_; 
lean_dec(v_h__2_1959_);
v___x_1960_ = lean_apply_2(v_h__1_1958_, v_x_1956_, v_x_1957_);
return v___x_1960_;
}
else
{
lean_object* v_head_1961_; lean_object* v_tail_1962_; lean_object* v___x_1963_; 
lean_dec(v_h__1_1958_);
v_head_1961_ = lean_ctor_get(v_x_1955_, 0);
lean_inc(v_head_1961_);
v_tail_1962_ = lean_ctor_get(v_x_1955_, 1);
lean_inc(v_tail_1962_);
lean_dec_ref(v_x_1955_);
v___x_1963_ = lean_apply_4(v_h__2_1959_, v_head_1961_, v_tail_1962_, v_x_1956_, v_x_1957_);
return v___x_1963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter(lean_object* v_motive_1964_, lean_object* v_x_1965_, lean_object* v_x_1966_, lean_object* v_x_1967_, lean_object* v_h__1_1968_, lean_object* v_h__2_1969_){
_start:
{
if (lean_obj_tag(v_x_1965_) == 0)
{
lean_object* v___x_1970_; 
lean_dec(v_h__2_1969_);
v___x_1970_ = lean_apply_2(v_h__1_1968_, v_x_1966_, v_x_1967_);
return v___x_1970_;
}
else
{
lean_object* v_head_1971_; lean_object* v_tail_1972_; lean_object* v___x_1973_; 
lean_dec(v_h__1_1968_);
v_head_1971_ = lean_ctor_get(v_x_1965_, 0);
lean_inc(v_head_1971_);
v_tail_1972_ = lean_ctor_get(v_x_1965_, 1);
lean_inc(v_tail_1972_);
lean_dec_ref(v_x_1965_);
v___x_1973_ = lean_apply_4(v_h__2_1969_, v_head_1971_, v_tail_1972_, v_x_1966_, v_x_1967_);
return v___x_1973_;
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop(lean_object* v_a_1974_, lean_object* v_b_1975_, lean_object* v_stopPos_1976_, lean_object* v_i_1977_){
_start:
{
uint8_t v___x_1978_; 
v___x_1978_ = lean_nat_dec_lt(v_i_1977_, v_stopPos_1976_);
if (v___x_1978_ == 0)
{
return v_i_1977_;
}
else
{
uint32_t v___x_1979_; uint32_t v___x_1980_; uint8_t v___x_1981_; 
v___x_1979_ = lean_string_utf8_get(v_a_1974_, v_i_1977_);
v___x_1980_ = lean_string_utf8_get(v_b_1975_, v_i_1977_);
v___x_1981_ = lean_uint32_dec_eq(v___x_1979_, v___x_1980_);
if (v___x_1981_ == 0)
{
return v_i_1977_;
}
else
{
lean_object* v___x_1982_; 
v___x_1982_ = lean_string_utf8_next(v_a_1974_, v_i_1977_);
lean_dec(v_i_1977_);
v_i_1977_ = v___x_1982_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop___boxed(lean_object* v_a_1984_, lean_object* v_b_1985_, lean_object* v_stopPos_1986_, lean_object* v_i_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_String_firstDiffPos_loop(v_a_1984_, v_b_1985_, v_stopPos_1986_, v_i_1987_);
lean_dec(v_stopPos_1986_);
lean_dec_ref(v_b_1985_);
lean_dec_ref(v_a_1984_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos(lean_object* v_a_1989_, lean_object* v_b_1990_){
_start:
{
lean_object* v___y_1992_; lean_object* v___x_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; 
v___x_1995_ = lean_string_utf8_byte_size(v_a_1989_);
v___x_1996_ = lean_string_utf8_byte_size(v_b_1990_);
v___x_1997_ = lean_nat_dec_le(v___x_1995_, v___x_1996_);
if (v___x_1997_ == 0)
{
v___y_1992_ = v___x_1996_;
goto v___jp_1991_;
}
else
{
v___y_1992_ = v___x_1995_;
goto v___jp_1991_;
}
v___jp_1991_:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = lean_unsigned_to_nat(0u);
v___x_1994_ = l_String_firstDiffPos_loop(v_a_1989_, v_b_1990_, v___y_1992_, v___x_1993_);
lean_dec(v___y_1992_);
return v___x_1994_;
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos___boxed(lean_object* v_a_1998_, lean_object* v_b_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_String_firstDiffPos(v_a_1998_, v_b_1999_);
lean_dec_ref(v_b_1999_);
lean_dec_ref(v_a_1998_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082(lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_){
_start:
{
if (lean_obj_tag(v_a_2001_) == 0)
{
return v_a_2001_;
}
else
{
lean_object* v_head_2004_; lean_object* v_tail_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2018_; 
v_head_2004_ = lean_ctor_get(v_a_2001_, 0);
v_tail_2005_ = lean_ctor_get(v_a_2001_, 1);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_a_2001_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2007_ = v_a_2001_;
v_isShared_2008_ = v_isSharedCheck_2018_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_tail_2005_);
lean_inc(v_head_2004_);
lean_dec(v_a_2001_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2018_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
uint8_t v___x_2009_; 
v___x_2009_ = lean_nat_dec_eq(v_a_2002_, v_a_2003_);
if (v___x_2009_ == 0)
{
uint32_t v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2015_; 
v___x_2010_ = lean_unbox_uint32(v_head_2004_);
v___x_2011_ = l_Char_utf8Size(v___x_2010_);
v___x_2012_ = lean_nat_add(v_a_2002_, v___x_2011_);
lean_dec(v___x_2011_);
v___x_2013_ = l_String_Pos_Raw_extract_go_u2082(v_tail_2005_, v___x_2012_, v_a_2003_);
lean_dec(v___x_2012_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 1, v___x_2013_);
v___x_2015_ = v___x_2007_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_head_2004_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
else
{
lean_object* v___x_2017_; 
lean_del_object(v___x_2007_);
lean_dec(v_tail_2005_);
lean_dec(v_head_2004_);
v___x_2017_ = lean_box(0);
return v___x_2017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082___boxed(lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_String_Pos_Raw_extract_go_u2082(v_a_2019_, v_a_2020_, v_a_2021_);
lean_dec(v_a_2021_);
lean_dec(v_a_2020_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081(lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_){
_start:
{
if (lean_obj_tag(v_a_2023_) == 0)
{
lean_dec(v_a_2024_);
return v_a_2023_;
}
else
{
lean_object* v_head_2027_; lean_object* v_tail_2028_; uint8_t v___x_2029_; 
v_head_2027_ = lean_ctor_get(v_a_2023_, 0);
v_tail_2028_ = lean_ctor_get(v_a_2023_, 1);
v___x_2029_ = lean_nat_dec_eq(v_a_2024_, v_a_2025_);
if (v___x_2029_ == 0)
{
uint32_t v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
lean_inc(v_tail_2028_);
lean_inc(v_head_2027_);
lean_dec_ref(v_a_2023_);
v___x_2030_ = lean_unbox_uint32(v_head_2027_);
lean_dec(v_head_2027_);
v___x_2031_ = l_Char_utf8Size(v___x_2030_);
v___x_2032_ = lean_nat_add(v_a_2024_, v___x_2031_);
lean_dec(v___x_2031_);
lean_dec(v_a_2024_);
v_a_2023_ = v_tail_2028_;
v_a_2024_ = v___x_2032_;
goto _start;
}
else
{
lean_object* v___x_2034_; 
v___x_2034_ = l_String_Pos_Raw_extract_go_u2082(v_a_2023_, v_a_2024_, v_a_2026_);
lean_dec(v_a_2024_);
return v___x_2034_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081___boxed(lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_String_Pos_Raw_extract_go_u2081(v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_);
lean_dec(v_a_2038_);
lean_dec(v_a_2037_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract___boxed(lean_object* v_a_00___x40___internal___hyg_2043_, lean_object* v_a_00___x40___internal___hyg_2044_, lean_object* v_a_00___x40___internal___hyg_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = lean_string_utf8_extract(v_a_00___x40___internal___hyg_2043_, v_a_00___x40___internal___hyg_2044_, v_a_00___x40___internal___hyg_2045_);
lean_dec(v_a_00___x40___internal___hyg_2045_);
lean_dec(v_a_00___x40___internal___hyg_2044_);
lean_dec_ref(v_a_00___x40___internal___hyg_2043_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux(lean_object* v_s_2047_, lean_object* v_pos_2048_, lean_object* v_i_2049_, lean_object* v_offset_2050_){
_start:
{
uint8_t v___x_2051_; 
v___x_2051_ = lean_nat_dec_le(v_pos_2048_, v_i_2049_);
if (v___x_2051_ == 0)
{
uint8_t v___x_2052_; 
v___x_2052_ = lean_string_utf8_at_end(v_s_2047_, v_i_2049_);
if (v___x_2052_ == 0)
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2053_ = lean_string_utf8_next(v_s_2047_, v_i_2049_);
lean_dec(v_i_2049_);
v___x_2054_ = lean_unsigned_to_nat(1u);
v___x_2055_ = lean_nat_add(v_offset_2050_, v___x_2054_);
lean_dec(v_offset_2050_);
v_i_2049_ = v___x_2053_;
v_offset_2050_ = v___x_2055_;
goto _start;
}
else
{
lean_dec(v_i_2049_);
return v_offset_2050_;
}
}
else
{
lean_dec(v_i_2049_);
return v_offset_2050_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux___boxed(lean_object* v_s_2057_, lean_object* v_pos_2058_, lean_object* v_i_2059_, lean_object* v_offset_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2057_, v_pos_2058_, v_i_2059_, v_offset_2060_);
lean_dec(v_pos_2058_);
lean_dec_ref(v_s_2057_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos(lean_object* v_s_2062_, lean_object* v_pos_2063_){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = lean_unsigned_to_nat(0u);
v___x_2065_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2062_, v_pos_2063_, v___x_2064_, v___x_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos___boxed(lean_object* v_s_2066_, lean_object* v_pos_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_String_Pos_Raw_offsetOfPos(v_s_2066_, v_pos_2067_);
lean_dec(v_pos_2067_);
lean_dec_ref(v_s_2066_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos(lean_object* v_s_2069_, lean_object* v_pos_2070_){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2071_ = lean_unsigned_to_nat(0u);
v___x_2072_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2069_, v_pos_2070_, v___x_2071_, v___x_2071_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos___boxed(lean_object* v_s_2073_, lean_object* v_pos_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_String_offsetOfPos(v_s_2073_, v_pos_2074_);
lean_dec(v_pos_2074_);
lean_dec_ref(v_s_2073_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* lean_string_offsetofpos(lean_object* v_s_2076_, lean_object* v_pos_2077_){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = lean_unsigned_to_nat(0u);
v___x_2079_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2076_, v_pos_2077_, v___x_2078_, v___x_2078_);
lean_dec(v_pos_2077_);
lean_dec_ref(v_s_2076_);
return v___x_2079_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(lean_object* v_s1_2080_, lean_object* v_s2_2081_, lean_object* v_off1_2082_, lean_object* v_off2_2083_, lean_object* v_stop1_2084_){
_start:
{
uint8_t v___x_2085_; 
v___x_2085_ = lean_nat_dec_lt(v_off1_2082_, v_stop1_2084_);
if (v___x_2085_ == 0)
{
uint8_t v___x_2086_; 
lean_dec(v_off2_2083_);
lean_dec(v_off1_2082_);
v___x_2086_ = 1;
return v___x_2086_;
}
else
{
uint32_t v_c_u2081_2087_; uint32_t v_c_u2082_2088_; uint8_t v___x_2089_; 
v_c_u2081_2087_ = lean_string_utf8_get(v_s1_2080_, v_off1_2082_);
v_c_u2082_2088_ = lean_string_utf8_get(v_s2_2081_, v_off2_2083_);
v___x_2089_ = lean_uint32_dec_eq(v_c_u2081_2087_, v_c_u2082_2088_);
if (v___x_2089_ == 0)
{
lean_dec(v_off2_2083_);
lean_dec(v_off1_2082_);
return v___x_2089_;
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2090_ = l_Char_utf8Size(v_c_u2081_2087_);
v___x_2091_ = lean_nat_add(v_off1_2082_, v___x_2090_);
lean_dec(v___x_2090_);
lean_dec(v_off1_2082_);
v___x_2092_ = l_Char_utf8Size(v_c_u2082_2088_);
v___x_2093_ = lean_nat_add(v_off2_2083_, v___x_2092_);
lean_dec(v___x_2092_);
lean_dec(v_off2_2083_);
v_off1_2082_ = v___x_2091_;
v_off2_2083_ = v___x_2093_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop___boxed(lean_object* v_s1_2095_, lean_object* v_s2_2096_, lean_object* v_off1_2097_, lean_object* v_off2_2098_, lean_object* v_stop1_2099_){
_start:
{
uint8_t v_res_2100_; lean_object* v_r_2101_; 
v_res_2100_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2095_, v_s2_2096_, v_off1_2097_, v_off2_2098_, v_stop1_2099_);
lean_dec(v_stop1_2099_);
lean_dec_ref(v_s2_2096_);
lean_dec_ref(v_s1_2095_);
v_r_2101_ = lean_box(v_res_2100_);
return v_r_2101_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_substrEq(lean_object* v_s1_2102_, lean_object* v_pos1_2103_, lean_object* v_s2_2104_, lean_object* v_pos2_2105_, lean_object* v_sz_2106_){
_start:
{
uint8_t v___y_2108_; lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2111_ = lean_nat_add(v_pos1_2103_, v_sz_2106_);
v___x_2112_ = lean_string_utf8_byte_size(v_s1_2102_);
v___x_2113_ = lean_nat_dec_le(v___x_2111_, v___x_2112_);
lean_dec(v___x_2111_);
if (v___x_2113_ == 0)
{
v___y_2108_ = v___x_2113_;
goto v___jp_2107_;
}
else
{
lean_object* v___x_2114_; lean_object* v___x_2115_; uint8_t v___x_2116_; 
v___x_2114_ = lean_nat_add(v_pos2_2105_, v_sz_2106_);
v___x_2115_ = lean_string_utf8_byte_size(v_s2_2104_);
v___x_2116_ = lean_nat_dec_le(v___x_2114_, v___x_2115_);
lean_dec(v___x_2114_);
v___y_2108_ = v___x_2116_;
goto v___jp_2107_;
}
v___jp_2107_:
{
if (v___y_2108_ == 0)
{
lean_dec(v_pos2_2105_);
lean_dec(v_pos1_2103_);
return v___y_2108_;
}
else
{
lean_object* v___x_2109_; uint8_t v___x_2110_; 
v___x_2109_ = lean_nat_add(v_pos1_2103_, v_sz_2106_);
v___x_2110_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2102_, v_s2_2104_, v_pos1_2103_, v_pos2_2105_, v___x_2109_);
lean_dec(v___x_2109_);
return v___x_2110_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_substrEq___boxed(lean_object* v_s1_2117_, lean_object* v_pos1_2118_, lean_object* v_s2_2119_, lean_object* v_pos2_2120_, lean_object* v_sz_2121_){
_start:
{
uint8_t v_res_2122_; lean_object* v_r_2123_; 
v_res_2122_ = l_String_Pos_Raw_substrEq(v_s1_2117_, v_pos1_2118_, v_s2_2119_, v_pos2_2120_, v_sz_2121_);
lean_dec(v_sz_2121_);
lean_dec_ref(v_s2_2119_);
lean_dec_ref(v_s1_2117_);
v_r_2123_ = lean_box(v_res_2122_);
return v_r_2123_;
}
}
LEAN_EXPORT uint8_t l_String_substrEq(lean_object* v_s1_2124_, lean_object* v_pos1_2125_, lean_object* v_s2_2126_, lean_object* v_pos2_2127_, lean_object* v_sz_2128_){
_start:
{
uint8_t v___x_2129_; 
v___x_2129_ = l_String_Pos_Raw_substrEq(v_s1_2124_, v_pos1_2125_, v_s2_2126_, v_pos2_2127_, v_sz_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_String_substrEq___boxed(lean_object* v_s1_2130_, lean_object* v_pos1_2131_, lean_object* v_s2_2132_, lean_object* v_pos2_2133_, lean_object* v_sz_2134_){
_start:
{
uint8_t v_res_2135_; lean_object* v_r_2136_; 
v_res_2135_ = l_String_substrEq(v_s1_2130_, v_pos1_2131_, v_s2_2132_, v_pos2_2133_, v_sz_2134_);
lean_dec(v_sz_2134_);
lean_dec_ref(v_s2_2132_);
lean_dec_ref(v_s1_2130_);
v_r_2136_ = lean_box(v_res_2135_);
return v_r_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter___redArg(lean_object* v_x_2137_, lean_object* v_x_2138_, lean_object* v_h__1_2139_, lean_object* v_h__2_2140_){
_start:
{
lean_object* v_zero_2141_; uint8_t v_isZero_2142_; 
v_zero_2141_ = lean_unsigned_to_nat(0u);
v_isZero_2142_ = lean_nat_dec_eq(v_x_2137_, v_zero_2141_);
if (v_isZero_2142_ == 1)
{
lean_object* v___x_2143_; 
lean_dec(v_h__2_2140_);
v___x_2143_ = lean_apply_1(v_h__1_2139_, v_x_2138_);
return v___x_2143_;
}
else
{
lean_object* v_one_2144_; lean_object* v_n_2145_; lean_object* v___x_2146_; 
lean_dec(v_h__1_2139_);
v_one_2144_ = lean_unsigned_to_nat(1u);
v_n_2145_ = lean_nat_sub(v_x_2137_, v_one_2144_);
v___x_2146_ = lean_apply_2(v_h__2_2140_, v_n_2145_, v_x_2138_);
return v___x_2146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter___redArg___boxed(lean_object* v_x_2147_, lean_object* v_x_2148_, lean_object* v_h__1_2149_, lean_object* v_h__2_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter___redArg(v_x_2147_, v_x_2148_, v_h__1_2149_, v_h__2_2150_);
lean_dec(v_x_2147_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter(lean_object* v_00_u03b1_2152_, lean_object* v_motive_2153_, lean_object* v_x_2154_, lean_object* v_x_2155_, lean_object* v_h__1_2156_, lean_object* v_h__2_2157_){
_start:
{
lean_object* v_zero_2158_; uint8_t v_isZero_2159_; 
v_zero_2158_ = lean_unsigned_to_nat(0u);
v_isZero_2159_ = lean_nat_dec_eq(v_x_2154_, v_zero_2158_);
if (v_isZero_2159_ == 1)
{
lean_object* v___x_2160_; 
lean_dec(v_h__2_2157_);
v___x_2160_ = lean_apply_1(v_h__1_2156_, v_x_2155_);
return v___x_2160_;
}
else
{
lean_object* v_one_2161_; lean_object* v_n_2162_; lean_object* v___x_2163_; 
lean_dec(v_h__1_2156_);
v_one_2161_ = lean_unsigned_to_nat(1u);
v_n_2162_ = lean_nat_sub(v_x_2154_, v_one_2161_);
v___x_2163_ = lean_apply_2(v_h__2_2157_, v_n_2162_, v_x_2155_);
return v___x_2163_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter___boxed(lean_object* v_00_u03b1_2164_, lean_object* v_motive_2165_, lean_object* v_x_2166_, lean_object* v_x_2167_, lean_object* v_h__1_2168_, lean_object* v_h__2_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter(v_00_u03b1_2164_, v_motive_2165_, v_x_2166_, v_x_2167_, v_h__1_2168_, v_h__2_2169_);
lean_dec(v_x_2166_);
return v_res_2170_;
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
