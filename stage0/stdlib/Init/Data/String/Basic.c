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
if (v___x_24_ == 0)
{
lean_object* v___x_26_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_26_ = lean_box(0);
return v___x_26_;
}
else
{
uint8_t v___x_27_; uint8_t v___x_28_; uint8_t v___x_29_; uint8_t v___x_30_; uint8_t v___x_31_; 
v___x_27_ = lean_byte_array_fget(v_b_1_, v_i_2_);
v___x_28_ = 128;
v___x_29_ = lean_uint8_land(v___x_27_, v___x_28_);
v___x_30_ = 0;
v___x_31_ = lean_uint8_dec_eq(v___x_29_, v___x_30_);
if (v___x_31_ == 0)
{
uint8_t v___x_32_; uint8_t v___x_33_; uint8_t v___x_34_; uint8_t v___x_35_; 
v___x_32_ = 224;
v___x_33_ = lean_uint8_land(v___x_27_, v___x_32_);
v___x_34_ = 192;
v___x_35_ = lean_uint8_dec_eq(v___x_33_, v___x_34_);
if (v___x_35_ == 0)
{
uint8_t v___x_36_; uint8_t v___x_37_; uint8_t v___x_38_; 
v___x_36_ = 240;
v___x_37_ = lean_uint8_land(v___x_27_, v___x_36_);
v___x_38_ = lean_uint8_dec_eq(v___x_37_, v___x_32_);
if (v___x_38_ == 0)
{
uint8_t v___x_39_; uint8_t v___x_40_; uint8_t v___x_41_; 
v___x_39_ = 248;
v___x_40_ = lean_uint8_land(v___x_27_, v___x_39_);
v___x_41_ = lean_uint8_dec_eq(v___x_40_, v___x_36_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_42_ = lean_box(0);
return v___x_42_;
}
else
{
lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_43_ = lean_unsigned_to_nat(3u);
v___x_44_ = lean_nat_add(v_i_2_, v___x_43_);
v___x_45_ = lean_nat_dec_lt(v___x_44_, v___x_23_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; 
lean_dec(v___x_44_);
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_46_ = lean_box(0);
return v___x_46_;
}
else
{
lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; uint8_t v___x_50_; uint8_t v___x_51_; 
v___x_47_ = lean_unsigned_to_nat(1u);
v___x_48_ = lean_nat_add(v_i_2_, v___x_47_);
v___x_49_ = lean_byte_array_fget(v_b_1_, v___x_48_);
lean_dec(v___x_48_);
v___x_50_ = lean_uint8_land(v___x_49_, v___x_34_);
v___x_51_ = lean_uint8_dec_eq(v___x_50_, v___x_28_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; 
lean_dec(v___x_44_);
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_52_ = lean_box(0);
return v___x_52_;
}
else
{
lean_object* v___x_53_; lean_object* v___x_54_; uint8_t v___x_55_; uint8_t v___x_56_; uint8_t v___x_57_; 
v___x_53_ = lean_unsigned_to_nat(2u);
v___x_54_ = lean_nat_add(v_i_2_, v___x_53_);
v___x_55_ = lean_byte_array_fget(v_b_1_, v___x_54_);
lean_dec(v___x_54_);
v___x_56_ = lean_uint8_land(v___x_55_, v___x_34_);
v___x_57_ = lean_uint8_dec_eq(v___x_56_, v___x_28_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; 
lean_dec(v___x_44_);
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_58_ = lean_box(0);
return v___x_58_;
}
else
{
uint8_t v___x_59_; uint8_t v___x_60_; uint8_t v___x_61_; 
v___x_59_ = lean_byte_array_fget(v_b_1_, v___x_44_);
lean_dec(v___x_44_);
v___x_60_ = lean_uint8_land(v___x_59_, v___x_34_);
v___x_61_ = lean_uint8_dec_eq(v___x_60_, v___x_28_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_62_ = lean_box(0);
return v___x_62_;
}
else
{
uint8_t v___x_63_; uint8_t v_b_u2080_64_; uint8_t v___x_65_; uint8_t v_b_u2081_66_; uint8_t v_b_u2082_67_; uint8_t v_b_u2083_68_; uint32_t v___x_69_; uint32_t v___x_70_; uint32_t v___x_71_; uint32_t v___x_72_; uint32_t v___x_73_; uint32_t v___x_74_; uint32_t v___x_75_; uint32_t v___x_76_; uint32_t v___x_77_; uint32_t v___x_78_; uint32_t v___x_79_; uint32_t v___x_80_; uint32_t v_r_81_; uint32_t v___x_82_; uint8_t v___x_83_; 
v___x_63_ = 7;
v_b_u2080_64_ = lean_uint8_land(v___x_27_, v___x_63_);
v___x_65_ = 63;
v_b_u2081_66_ = lean_uint8_land(v___x_49_, v___x_65_);
v_b_u2082_67_ = lean_uint8_land(v___x_55_, v___x_65_);
v_b_u2083_68_ = lean_uint8_land(v___x_59_, v___x_65_);
v___x_69_ = lean_uint8_to_uint32(v_b_u2080_64_);
v___x_70_ = 18;
v___x_71_ = lean_uint32_shift_left(v___x_69_, v___x_70_);
v___x_72_ = lean_uint8_to_uint32(v_b_u2081_66_);
v___x_73_ = 12;
v___x_74_ = lean_uint32_shift_left(v___x_72_, v___x_73_);
v___x_75_ = lean_uint32_lor(v___x_71_, v___x_74_);
v___x_76_ = lean_uint8_to_uint32(v_b_u2082_67_);
v___x_77_ = 6;
v___x_78_ = lean_uint32_shift_left(v___x_76_, v___x_77_);
v___x_79_ = lean_uint32_lor(v___x_75_, v___x_78_);
v___x_80_ = lean_uint8_to_uint32(v_b_u2083_68_);
v_r_81_ = lean_uint32_lor(v___x_79_, v___x_80_);
v___x_82_ = 65536;
v___x_83_ = lean_uint32_dec_lt(v_r_81_, v___x_82_);
if (v___x_83_ == 0)
{
uint32_t v___x_84_; uint8_t v___x_85_; 
v___x_84_ = 1114111;
v___x_85_ = lean_uint32_dec_lt(v___x_84_, v_r_81_);
if (v___x_85_ == 0)
{
v_val_12_ = v_r_81_;
goto v___jp_11_;
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
else
{
lean_object* v___x_87_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_87_ = lean_box(0);
return v___x_87_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_88_ = lean_unsigned_to_nat(2u);
v___x_89_ = lean_nat_add(v_i_2_, v___x_88_);
v___x_90_ = lean_nat_dec_lt(v___x_89_, v___x_23_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; 
lean_dec(v___x_89_);
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_91_ = lean_box(0);
return v___x_91_;
}
else
{
lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; uint8_t v___x_95_; uint8_t v___x_96_; 
v___x_92_ = lean_unsigned_to_nat(1u);
v___x_93_ = lean_nat_add(v_i_2_, v___x_92_);
v___x_94_ = lean_byte_array_fget(v_b_1_, v___x_93_);
lean_dec(v___x_93_);
v___x_95_ = lean_uint8_land(v___x_94_, v___x_34_);
v___x_96_ = lean_uint8_dec_eq(v___x_95_, v___x_28_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
lean_dec(v___x_89_);
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_97_ = lean_box(0);
return v___x_97_;
}
else
{
uint8_t v___x_98_; uint8_t v___x_99_; uint8_t v___x_100_; 
v___x_98_ = lean_byte_array_fget(v_b_1_, v___x_89_);
lean_dec(v___x_89_);
v___x_99_ = lean_uint8_land(v___x_98_, v___x_34_);
v___x_100_ = lean_uint8_dec_eq(v___x_99_, v___x_28_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_101_ = lean_box(0);
return v___x_101_;
}
else
{
uint8_t v___x_102_; uint8_t v_b_u2080_103_; uint8_t v___x_104_; uint8_t v_b_u2081_105_; uint8_t v_b_u2082_106_; uint32_t v___x_107_; uint32_t v___x_108_; uint32_t v___x_109_; uint32_t v___x_110_; uint32_t v___x_111_; uint32_t v___x_112_; uint32_t v___x_113_; uint32_t v___x_114_; uint32_t v_r_115_; uint32_t v___x_116_; uint8_t v___x_117_; 
v___x_102_ = 15;
v_b_u2080_103_ = lean_uint8_land(v___x_27_, v___x_102_);
v___x_104_ = 63;
v_b_u2081_105_ = lean_uint8_land(v___x_94_, v___x_104_);
v_b_u2082_106_ = lean_uint8_land(v___x_98_, v___x_104_);
v___x_107_ = lean_uint8_to_uint32(v_b_u2080_103_);
v___x_108_ = 12;
v___x_109_ = lean_uint32_shift_left(v___x_107_, v___x_108_);
v___x_110_ = lean_uint8_to_uint32(v_b_u2081_105_);
v___x_111_ = 6;
v___x_112_ = lean_uint32_shift_left(v___x_110_, v___x_111_);
v___x_113_ = lean_uint32_lor(v___x_109_, v___x_112_);
v___x_114_ = lean_uint8_to_uint32(v_b_u2082_106_);
v_r_115_ = lean_uint32_lor(v___x_113_, v___x_114_);
v___x_116_ = 2048;
v___x_117_ = lean_uint32_dec_lt(v_r_115_, v___x_116_);
if (v___x_117_ == 0)
{
uint32_t v___x_118_; uint8_t v___x_119_; 
v___x_118_ = 55296;
v___x_119_ = lean_uint32_dec_le(v___x_118_, v_r_115_);
if (v___x_119_ == 0)
{
v_val_12_ = v_r_115_;
goto v___jp_11_;
}
else
{
uint32_t v___x_120_; uint8_t v___x_121_; 
v___x_120_ = 57343;
v___x_121_ = lean_uint32_dec_le(v_r_115_, v___x_120_);
if (v___x_121_ == 0)
{
v_val_12_ = v_r_115_;
goto v___jp_11_;
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
else
{
lean_object* v___x_123_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_123_ = lean_box(0);
return v___x_123_;
}
}
}
}
}
}
else
{
lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = lean_nat_add(v_i_2_, v___x_124_);
v___x_126_ = lean_nat_dec_lt(v___x_125_, v___x_23_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
lean_dec(v___x_125_);
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_127_ = lean_box(0);
return v___x_127_;
}
else
{
uint8_t v___x_128_; uint8_t v___x_129_; uint8_t v___x_130_; 
v___x_128_ = lean_byte_array_fget(v_b_1_, v___x_125_);
lean_dec(v___x_125_);
v___x_129_ = lean_uint8_land(v___x_128_, v___x_34_);
v___x_130_ = lean_uint8_dec_eq(v___x_129_, v___x_28_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_131_ = lean_box(0);
return v___x_131_;
}
else
{
uint8_t v___x_132_; uint8_t v_b_u2080_133_; uint8_t v___x_134_; uint8_t v_b_u2081_135_; uint32_t v___x_136_; uint32_t v___x_137_; uint32_t v___x_138_; uint32_t v___x_139_; uint32_t v_r_140_; uint32_t v___x_141_; uint8_t v___x_142_; 
v___x_132_ = 31;
v_b_u2080_133_ = lean_uint8_land(v___x_27_, v___x_132_);
v___x_134_ = 63;
v_b_u2081_135_ = lean_uint8_land(v___x_128_, v___x_134_);
v___x_136_ = lean_uint8_to_uint32(v_b_u2080_133_);
v___x_137_ = 6;
v___x_138_ = lean_uint32_shift_left(v___x_136_, v___x_137_);
v___x_139_ = lean_uint8_to_uint32(v_b_u2081_135_);
v_r_140_ = lean_uint32_lor(v___x_138_, v___x_139_);
v___x_141_ = 128;
v___x_142_ = lean_uint32_dec_lt(v_r_140_, v___x_141_);
if (v___x_142_ == 0)
{
v_val_12_ = v_r_140_;
goto v___jp_11_;
}
else
{
lean_object* v___x_143_; 
lean_dec_ref(v_acc_3_);
lean_dec(v_i_2_);
v___x_143_ = lean_box(0);
return v___x_143_;
}
}
}
}
}
else
{
uint32_t v___x_144_; 
v___x_144_ = lean_uint8_to_uint32(v___x_27_);
v_val_12_ = v___x_144_;
goto v___jp_11_;
}
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
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go___redArg___boxed(lean_object* v_b_145_, lean_object* v_i_146_, lean_object* v_acc_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_ByteArray_utf8Decode_x3f_go___redArg(v_b_145_, v_i_146_, v_acc_147_);
lean_dec_ref(v_b_145_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go(lean_object* v_b_149_, lean_object* v_i_150_, lean_object* v_acc_151_, lean_object* v_hi_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_ByteArray_utf8Decode_x3f_go___redArg(v_b_149_, v_i_150_, v_acc_151_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go___boxed(lean_object* v_b_154_, lean_object* v_i_155_, lean_object* v_acc_156_, lean_object* v_hi_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_ByteArray_utf8Decode_x3f_go(v_b_154_, v_i_155_, v_acc_156_, v_hi_157_);
lean_dec_ref(v_b_154_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__1_splitter___redArg(lean_object* v_x_159_, lean_object* v_h__1_160_, lean_object* v_h__2_161_){
_start:
{
if (lean_obj_tag(v_x_159_) == 0)
{
lean_object* v___x_162_; 
lean_dec(v_h__2_161_);
v___x_162_ = lean_apply_1(v_h__1_160_, lean_box(0));
return v___x_162_;
}
else
{
lean_object* v_val_163_; lean_object* v___x_164_; 
lean_dec(v_h__1_160_);
v_val_163_ = lean_ctor_get(v_x_159_, 0);
lean_inc(v_val_163_);
lean_dec_ref_known(v_x_159_, 1);
v___x_164_ = lean_apply_2(v_h__2_161_, v_val_163_, lean_box(0));
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__1_splitter(lean_object* v_motive_165_, lean_object* v_x_166_, lean_object* v_h__1_167_, lean_object* v_h__2_168_){
_start:
{
if (lean_obj_tag(v_x_166_) == 0)
{
lean_object* v___x_169_; 
lean_dec(v_h__2_168_);
v___x_169_ = lean_apply_1(v_h__1_167_, lean_box(0));
return v___x_169_;
}
else
{
lean_object* v_val_170_; lean_object* v___x_171_; 
lean_dec(v_h__1_167_);
v_val_170_ = lean_ctor_get(v_x_166_, 0);
lean_inc(v_val_170_);
lean_dec_ref_known(v_x_166_, 1);
v___x_171_ = lean_apply_2(v_h__2_168_, v_val_170_, lean_box(0));
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f(lean_object* v_b_174_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = ((lean_object*)(l_ByteArray_utf8Decode_x3f___closed__0));
v___x_177_ = l_ByteArray_utf8Decode_x3f_go___redArg(v_b_174_, v___x_175_, v___x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f___boxed(lean_object* v_b_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_ByteArray_utf8Decode_x3f(v_b_178_);
lean_dec_ref(v_b_178_);
return v_res_179_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8_go___redArg(lean_object* v_b_180_, lean_object* v_i_181_){
_start:
{
lean_object* v___y_183_; uint8_t v___y_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = lean_byte_array_size(v_b_180_);
v___x_206_ = lean_nat_dec_lt(v_i_181_, v___x_205_);
if (v___x_206_ == 0)
{
uint8_t v___x_207_; 
lean_dec(v_i_181_);
v___x_207_ = 1;
return v___x_207_;
}
else
{
if (v___x_206_ == 0)
{
lean_dec(v_i_181_);
return v___x_206_;
}
else
{
uint8_t v___x_208_; uint8_t v___x_209_; uint8_t v___x_210_; uint8_t v___x_211_; uint8_t v___x_212_; 
v___x_208_ = lean_byte_array_fget(v_b_180_, v_i_181_);
v___x_209_ = 128;
v___x_210_ = lean_uint8_land(v___x_208_, v___x_209_);
v___x_211_ = 0;
v___x_212_ = lean_uint8_dec_eq(v___x_210_, v___x_211_);
if (v___x_212_ == 0)
{
uint8_t v___x_213_; uint8_t v___x_214_; uint8_t v___x_215_; uint8_t v___x_216_; 
v___x_213_ = 224;
v___x_214_ = lean_uint8_land(v___x_208_, v___x_213_);
v___x_215_ = 192;
v___x_216_ = lean_uint8_dec_eq(v___x_214_, v___x_215_);
if (v___x_216_ == 0)
{
uint8_t v___x_217_; uint8_t v___x_218_; uint8_t v___x_219_; 
v___x_217_ = 240;
v___x_218_ = lean_uint8_land(v___x_208_, v___x_217_);
v___x_219_ = lean_uint8_dec_eq(v___x_218_, v___x_213_);
if (v___x_219_ == 0)
{
uint8_t v___x_220_; uint8_t v___x_221_; uint8_t v___x_222_; 
v___x_220_ = 248;
v___x_221_ = lean_uint8_land(v___x_208_, v___x_220_);
v___x_222_ = lean_uint8_dec_eq(v___x_221_, v___x_217_);
if (v___x_222_ == 0)
{
lean_dec(v_i_181_);
return v___x_222_;
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_223_ = lean_unsigned_to_nat(3u);
v___x_224_ = lean_nat_add(v_i_181_, v___x_223_);
v___x_225_ = lean_nat_dec_lt(v___x_224_, v___x_205_);
if (v___x_225_ == 0)
{
lean_dec(v___x_224_);
lean_dec(v_i_181_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; uint8_t v___x_229_; uint8_t v___x_230_; 
v___x_226_ = lean_unsigned_to_nat(1u);
v___x_227_ = lean_nat_add(v_i_181_, v___x_226_);
v___x_228_ = lean_byte_array_fget(v_b_180_, v___x_227_);
lean_dec(v___x_227_);
v___x_229_ = lean_uint8_land(v___x_228_, v___x_215_);
v___x_230_ = lean_uint8_dec_eq(v___x_229_, v___x_209_);
if (v___x_230_ == 0)
{
lean_dec(v___x_224_);
lean_dec(v_i_181_);
return v___x_230_;
}
else
{
lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; uint8_t v___x_234_; uint8_t v___x_235_; 
v___x_231_ = lean_unsigned_to_nat(2u);
v___x_232_ = lean_nat_add(v_i_181_, v___x_231_);
v___x_233_ = lean_byte_array_fget(v_b_180_, v___x_232_);
lean_dec(v___x_232_);
v___x_234_ = lean_uint8_land(v___x_233_, v___x_215_);
v___x_235_ = lean_uint8_dec_eq(v___x_234_, v___x_209_);
if (v___x_235_ == 0)
{
lean_dec(v___x_224_);
lean_dec(v_i_181_);
return v___x_219_;
}
else
{
uint8_t v___x_236_; uint8_t v___x_237_; uint8_t v___x_238_; 
v___x_236_ = lean_byte_array_fget(v_b_180_, v___x_224_);
lean_dec(v___x_224_);
v___x_237_ = lean_uint8_land(v___x_236_, v___x_215_);
v___x_238_ = lean_uint8_dec_eq(v___x_237_, v___x_209_);
if (v___x_238_ == 0)
{
lean_dec(v_i_181_);
return v___x_219_;
}
else
{
uint8_t v___x_239_; uint8_t v_b_u2080_240_; uint8_t v___x_241_; uint8_t v_b_u2081_242_; uint8_t v_b_u2082_243_; uint8_t v_b_u2083_244_; uint32_t v___x_245_; uint32_t v___x_246_; uint32_t v___x_247_; uint32_t v___x_248_; uint32_t v___x_249_; uint32_t v___x_250_; uint32_t v___x_251_; uint32_t v___x_252_; uint32_t v___x_253_; uint32_t v___x_254_; uint32_t v___x_255_; uint32_t v___x_256_; uint32_t v_r_257_; uint32_t v___x_258_; uint8_t v___x_259_; 
v___x_239_ = 7;
v_b_u2080_240_ = lean_uint8_land(v___x_208_, v___x_239_);
v___x_241_ = 63;
v_b_u2081_242_ = lean_uint8_land(v___x_228_, v___x_241_);
v_b_u2082_243_ = lean_uint8_land(v___x_233_, v___x_241_);
v_b_u2083_244_ = lean_uint8_land(v___x_236_, v___x_241_);
v___x_245_ = lean_uint8_to_uint32(v_b_u2080_240_);
v___x_246_ = 18;
v___x_247_ = lean_uint32_shift_left(v___x_245_, v___x_246_);
v___x_248_ = lean_uint8_to_uint32(v_b_u2081_242_);
v___x_249_ = 12;
v___x_250_ = lean_uint32_shift_left(v___x_248_, v___x_249_);
v___x_251_ = lean_uint32_lor(v___x_247_, v___x_250_);
v___x_252_ = lean_uint8_to_uint32(v_b_u2082_243_);
v___x_253_ = 6;
v___x_254_ = lean_uint32_shift_left(v___x_252_, v___x_253_);
v___x_255_ = lean_uint32_lor(v___x_251_, v___x_254_);
v___x_256_ = lean_uint8_to_uint32(v_b_u2083_244_);
v_r_257_ = lean_uint32_lor(v___x_255_, v___x_256_);
v___x_258_ = 65536;
v___x_259_ = lean_uint32_dec_le(v___x_258_, v_r_257_);
if (v___x_259_ == 0)
{
lean_dec(v_i_181_);
return v___x_219_;
}
else
{
uint32_t v___x_260_; uint8_t v___x_261_; 
v___x_260_ = 1114111;
v___x_261_ = lean_uint32_dec_le(v_r_257_, v___x_260_);
v___y_204_ = v___x_261_;
goto v___jp_203_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_262_ = lean_unsigned_to_nat(2u);
v___x_263_ = lean_nat_add(v_i_181_, v___x_262_);
v___x_264_ = lean_nat_dec_lt(v___x_263_, v___x_205_);
if (v___x_264_ == 0)
{
lean_dec(v___x_263_);
lean_dec(v_i_181_);
return v___x_264_;
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; uint8_t v___x_268_; uint8_t v___x_269_; 
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = lean_nat_add(v_i_181_, v___x_265_);
v___x_267_ = lean_byte_array_fget(v_b_180_, v___x_266_);
lean_dec(v___x_266_);
v___x_268_ = lean_uint8_land(v___x_267_, v___x_215_);
v___x_269_ = lean_uint8_dec_eq(v___x_268_, v___x_209_);
if (v___x_269_ == 0)
{
lean_dec(v___x_263_);
lean_dec(v_i_181_);
return v___x_269_;
}
else
{
uint8_t v___x_270_; uint8_t v___x_271_; uint8_t v___x_272_; 
v___x_270_ = lean_byte_array_fget(v_b_180_, v___x_263_);
lean_dec(v___x_263_);
v___x_271_ = lean_uint8_land(v___x_270_, v___x_215_);
v___x_272_ = lean_uint8_dec_eq(v___x_271_, v___x_209_);
if (v___x_272_ == 0)
{
lean_dec(v_i_181_);
return v___x_216_;
}
else
{
uint8_t v___x_273_; uint8_t v_b_u2080_274_; uint8_t v___x_275_; uint8_t v_b_u2081_276_; uint8_t v_b_u2082_277_; uint32_t v___x_278_; uint32_t v___x_279_; uint32_t v___x_280_; uint32_t v___x_281_; uint32_t v___x_282_; uint32_t v___x_283_; uint32_t v___x_284_; uint32_t v___x_285_; uint32_t v_r_286_; uint32_t v___x_287_; uint8_t v___x_288_; 
v___x_273_ = 15;
v_b_u2080_274_ = lean_uint8_land(v___x_208_, v___x_273_);
v___x_275_ = 63;
v_b_u2081_276_ = lean_uint8_land(v___x_267_, v___x_275_);
v_b_u2082_277_ = lean_uint8_land(v___x_270_, v___x_275_);
v___x_278_ = lean_uint8_to_uint32(v_b_u2080_274_);
v___x_279_ = 12;
v___x_280_ = lean_uint32_shift_left(v___x_278_, v___x_279_);
v___x_281_ = lean_uint8_to_uint32(v_b_u2081_276_);
v___x_282_ = 6;
v___x_283_ = lean_uint32_shift_left(v___x_281_, v___x_282_);
v___x_284_ = lean_uint32_lor(v___x_280_, v___x_283_);
v___x_285_ = lean_uint8_to_uint32(v_b_u2082_277_);
v_r_286_ = lean_uint32_lor(v___x_284_, v___x_285_);
v___x_287_ = 2048;
v___x_288_ = lean_uint32_dec_le(v___x_287_, v_r_286_);
if (v___x_288_ == 0)
{
lean_dec(v_i_181_);
return v___x_216_;
}
else
{
uint32_t v___x_289_; uint8_t v___x_290_; 
v___x_289_ = 55296;
v___x_290_ = lean_uint32_dec_lt(v_r_286_, v___x_289_);
if (v___x_290_ == 0)
{
uint32_t v___x_291_; uint8_t v___x_292_; 
v___x_291_ = 57343;
v___x_292_ = lean_uint32_dec_lt(v___x_291_, v_r_286_);
v___y_204_ = v___x_292_;
goto v___jp_203_;
}
else
{
goto v___jp_186_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = lean_nat_add(v_i_181_, v___x_293_);
v___x_295_ = lean_nat_dec_lt(v___x_294_, v___x_205_);
if (v___x_295_ == 0)
{
lean_dec(v___x_294_);
lean_dec(v_i_181_);
return v___x_295_;
}
else
{
uint8_t v___x_296_; uint8_t v___x_297_; uint8_t v___x_298_; 
v___x_296_ = lean_byte_array_fget(v_b_180_, v___x_294_);
lean_dec(v___x_294_);
v___x_297_ = lean_uint8_land(v___x_296_, v___x_215_);
v___x_298_ = lean_uint8_dec_eq(v___x_297_, v___x_209_);
if (v___x_298_ == 0)
{
lean_dec(v_i_181_);
return v___x_298_;
}
else
{
uint8_t v___x_299_; uint8_t v_b_u2080_300_; uint8_t v___x_301_; uint8_t v_b_u2081_302_; uint32_t v___x_303_; uint32_t v___x_304_; uint32_t v___x_305_; uint32_t v___x_306_; uint32_t v_r_307_; uint32_t v___x_308_; uint8_t v___x_309_; 
v___x_299_ = 31;
v_b_u2080_300_ = lean_uint8_land(v___x_208_, v___x_299_);
v___x_301_ = 63;
v_b_u2081_302_ = lean_uint8_land(v___x_296_, v___x_301_);
v___x_303_ = lean_uint8_to_uint32(v_b_u2080_300_);
v___x_304_ = 6;
v___x_305_ = lean_uint32_shift_left(v___x_303_, v___x_304_);
v___x_306_ = lean_uint8_to_uint32(v_b_u2081_302_);
v_r_307_ = lean_uint32_lor(v___x_305_, v___x_306_);
v___x_308_ = 128;
v___x_309_ = lean_uint32_dec_le(v___x_308_, v_r_307_);
v___y_204_ = v___x_309_;
goto v___jp_203_;
}
}
}
}
else
{
goto v___jp_186_;
}
}
}
v___jp_182_:
{
lean_object* v___x_184_; 
v___x_184_ = lean_nat_add(v_i_181_, v___y_183_);
lean_dec(v_i_181_);
v_i_181_ = v___x_184_;
goto _start;
}
v___jp_186_:
{
uint8_t v___x_187_; uint8_t v___x_188_; uint8_t v___x_189_; uint8_t v___x_190_; uint8_t v___x_191_; 
v___x_187_ = lean_byte_array_fget(v_b_180_, v_i_181_);
v___x_188_ = 128;
v___x_189_ = lean_uint8_land(v___x_187_, v___x_188_);
v___x_190_ = 0;
v___x_191_ = lean_uint8_dec_eq(v___x_189_, v___x_190_);
if (v___x_191_ == 0)
{
uint8_t v___x_192_; uint8_t v___x_193_; uint8_t v___x_194_; uint8_t v___x_195_; 
v___x_192_ = 224;
v___x_193_ = lean_uint8_land(v___x_187_, v___x_192_);
v___x_194_ = 192;
v___x_195_ = lean_uint8_dec_eq(v___x_193_, v___x_194_);
if (v___x_195_ == 0)
{
uint8_t v___x_196_; uint8_t v___x_197_; uint8_t v___x_198_; 
v___x_196_ = 240;
v___x_197_ = lean_uint8_land(v___x_187_, v___x_196_);
v___x_198_ = lean_uint8_dec_eq(v___x_197_, v___x_192_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; 
v___x_199_ = lean_unsigned_to_nat(4u);
v___y_183_ = v___x_199_;
goto v___jp_182_;
}
else
{
lean_object* v___x_200_; 
v___x_200_ = lean_unsigned_to_nat(3u);
v___y_183_ = v___x_200_;
goto v___jp_182_;
}
}
else
{
lean_object* v___x_201_; 
v___x_201_ = lean_unsigned_to_nat(2u);
v___y_183_ = v___x_201_;
goto v___jp_182_;
}
}
else
{
lean_object* v___x_202_; 
v___x_202_ = lean_unsigned_to_nat(1u);
v___y_183_ = v___x_202_;
goto v___jp_182_;
}
}
v___jp_203_:
{
if (v___y_204_ == 0)
{
lean_dec(v_i_181_);
return v___y_204_;
}
else
{
goto v___jp_186_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___redArg___boxed(lean_object* v_b_310_, lean_object* v_i_311_){
_start:
{
uint8_t v_res_312_; lean_object* v_r_313_; 
v_res_312_ = l_ByteArray_validateUTF8_go___redArg(v_b_310_, v_i_311_);
lean_dec_ref(v_b_310_);
v_r_313_ = lean_box(v_res_312_);
return v_r_313_;
}
}
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8_go(lean_object* v_b_314_, lean_object* v_i_315_, lean_object* v_hi_316_){
_start:
{
uint8_t v___x_317_; 
v___x_317_ = l_ByteArray_validateUTF8_go___redArg(v_b_314_, v_i_315_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___boxed(lean_object* v_b_318_, lean_object* v_i_319_, lean_object* v_hi_320_){
_start:
{
uint8_t v_res_321_; lean_object* v_r_322_; 
v_res_321_ = l_ByteArray_validateUTF8_go(v_b_318_, v_i_319_, v_hi_320_);
lean_dec_ref(v_b_318_);
v_r_322_ = lean_box(v_res_321_);
return v_r_322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(uint8_t v_x_323_, lean_object* v_h__1_324_, lean_object* v_h__2_325_){
_start:
{
if (v_x_323_ == 0)
{
lean_object* v___x_326_; 
lean_dec(v_h__2_325_);
v___x_326_ = lean_apply_1(v_h__1_324_, lean_box(0));
return v___x_326_;
}
else
{
lean_object* v___x_327_; 
lean_dec(v_h__1_324_);
v___x_327_ = lean_apply_1(v_h__2_325_, lean_box(0));
return v___x_327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg___boxed(lean_object* v_x_328_, lean_object* v_h__1_329_, lean_object* v_h__2_330_){
_start:
{
uint8_t v_x_26__boxed_331_; lean_object* v_res_332_; 
v_x_26__boxed_331_ = lean_unbox(v_x_328_);
v_res_332_ = l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(v_x_26__boxed_331_, v_h__1_329_, v_h__2_330_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(lean_object* v_motive_333_, uint8_t v_x_334_, lean_object* v_h__1_335_, lean_object* v_h__2_336_){
_start:
{
if (v_x_334_ == 0)
{
lean_object* v___x_337_; 
lean_dec(v_h__2_336_);
v___x_337_ = lean_apply_1(v_h__1_335_, lean_box(0));
return v___x_337_;
}
else
{
lean_object* v___x_338_; 
lean_dec(v_h__1_335_);
v___x_338_ = lean_apply_1(v_h__2_336_, lean_box(0));
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___boxed(lean_object* v_motive_339_, lean_object* v_x_340_, lean_object* v_h__1_341_, lean_object* v_h__2_342_){
_start:
{
uint8_t v_x_33__boxed_343_; lean_object* v_res_344_; 
v_x_33__boxed_343_ = lean_unbox(v_x_340_);
v_res_344_ = l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(v_motive_339_, v_x_33__boxed_343_, v_h__1_341_, v_h__2_342_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8___boxed(lean_object* v_b_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = lean_string_validate_utf8(v_b_346_);
lean_dec_ref(v_b_346_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT uint8_t l_instDecidableIsValidUTF8(lean_object* v_b_349_){
_start:
{
uint8_t v___x_350_; 
v___x_350_ = lean_string_validate_utf8(v_b_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_instDecidableIsValidUTF8___boxed(lean_object* v_b_351_){
_start:
{
uint8_t v_res_352_; lean_object* v_r_353_; 
v_res_352_ = l_instDecidableIsValidUTF8(v_b_351_);
lean_dec_ref(v_b_351_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_x3f(lean_object* v_a_354_){
_start:
{
uint8_t v___x_355_; 
v___x_355_ = lean_string_validate_utf8(v_a_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; 
lean_dec_ref(v_a_354_);
v___x_356_ = lean_box(0);
return v___x_356_;
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_string_from_utf8_unchecked(v_a_354_);
v___x_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
}
static lean_object* _init_l_String_fromUTF8_x21___closed__4(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_363_ = ((lean_object*)(l_String_fromUTF8_x21___closed__3));
v___x_364_ = lean_unsigned_to_nat(46u);
v___x_365_ = lean_unsigned_to_nat(193u);
v___x_366_ = ((lean_object*)(l_String_fromUTF8_x21___closed__2));
v___x_367_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_368_ = l_mkPanicMessageWithDecl(v___x_367_, v___x_366_, v___x_365_, v___x_364_, v___x_363_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_x21(lean_object* v_a_369_){
_start:
{
uint8_t v___x_370_; 
v___x_370_ = lean_string_validate_utf8(v_a_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
lean_dec_ref(v_a_369_);
v___x_371_ = ((lean_object*)(l_String_fromUTF8_x21___closed__0));
v___x_372_ = lean_obj_once(&l_String_fromUTF8_x21___closed__4, &l_String_fromUTF8_x21___closed__4_once, _init_l_String_fromUTF8_x21___closed__4);
v___x_373_ = l_panic___redArg(v___x_371_, v___x_372_);
return v___x_373_;
}
else
{
lean_object* v___x_374_; 
v___x_374_ = lean_string_from_utf8_unchecked(v_a_369_);
return v___x_374_;
}
}
}
LEAN_EXPORT lean_object* l_String_Internal_toArray(lean_object* v_b_375_){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v_val_380_; 
v___x_376_ = lean_string_to_utf8(v_b_375_);
v___x_377_ = lean_unsigned_to_nat(0u);
v___x_378_ = ((lean_object*)(l_ByteArray_utf8Decode_x3f___closed__0));
v___x_379_ = l_ByteArray_utf8Decode_x3f_go___redArg(v___x_376_, v___x_377_, v___x_378_);
lean_dec_ref(v___x_376_);
v_val_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_val_380_);
lean_dec(v___x_379_);
return v_val_380_;
}
}
static lean_object* _init_l_String_instLT(void){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = lean_box(0);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_String_decidableLT___boxed(lean_object* v_s_u2081_384_, lean_object* v_s_u2082_385_){
_start:
{
uint8_t v_res_386_; lean_object* v_r_387_; 
v_res_386_ = lean_string_dec_lt(v_s_u2081_384_, v_s_u2082_385_);
lean_dec_ref(v_s_u2082_385_);
lean_dec_ref(v_s_u2081_384_);
v_r_387_ = lean_box(v_res_386_);
return v_r_387_;
}
}
static lean_object* _init_l_String_instLE(void){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = lean_box(0);
return v___x_388_;
}
}
LEAN_EXPORT uint8_t l_String_decLE(lean_object* v_s_u2081_389_, lean_object* v_s_u2082_390_){
_start:
{
uint8_t v___x_391_; 
v___x_391_ = lean_string_dec_lt(v_s_u2082_390_, v_s_u2081_389_);
if (v___x_391_ == 0)
{
uint8_t v___x_392_; 
v___x_392_ = 1;
return v___x_392_;
}
else
{
uint8_t v___x_393_; 
v___x_393_ = 0;
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l_String_decLE___boxed(lean_object* v_s_u2081_394_, lean_object* v_s_u2082_395_){
_start:
{
uint8_t v_res_396_; lean_object* v_r_397_; 
v_res_396_ = l_String_decLE(v_s_u2081_394_, v_s_u2082_395_);
lean_dec_ref(v_s_u2082_395_);
lean_dec_ref(v_s_u2081_394_);
v_r_397_ = lean_box(v_res_396_);
return v_r_397_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValid___boxed(lean_object* v_s_400_, lean_object* v_p_401_){
_start:
{
uint8_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = lean_string_is_valid_pos(v_s_400_, v_p_401_);
lean_dec(v_p_401_);
lean_dec_ref(v_s_400_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsValid(lean_object* v_s_404_, lean_object* v_p_405_){
_start:
{
uint8_t v___x_406_; 
v___x_406_ = lean_string_is_valid_pos(v_s_404_, v_p_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsValid___boxed(lean_object* v_s_407_, lean_object* v_p_408_){
_start:
{
uint8_t v_res_409_; lean_object* v_r_410_; 
v_res_409_ = l_String_instDecidableIsValid(v_s_407_, v_p_408_);
lean_dec(v_p_408_);
lean_dec_ref(v_s_407_);
v_r_410_ = lean_box(v_res_409_);
return v_r_410_;
}
}
LEAN_EXPORT lean_object* l_String_extract___boxed(lean_object* v_s_414_, lean_object* v_b_415_, lean_object* v_e_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = lean_string_utf8_extract_fast(v_s_414_, v_b_415_, v_e_416_);
lean_dec(v_e_416_);
lean_dec(v_b_415_);
lean_dec_ref(v_s_414_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_extract(lean_object* v_s_418_, lean_object* v_b_419_, lean_object* v_e_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = lean_string_utf8_extract_fast(v_s_418_, v_b_419_, v_e_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_extract___boxed(lean_object* v_s_422_, lean_object* v_b_423_, lean_object* v_e_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_String_Pos_extract(v_s_422_, v_b_423_, v_e_424_);
lean_dec(v_e_424_);
lean_dec(v_b_423_);
lean_dec_ref(v_s_422_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_copy(lean_object* v_s_426_){
_start:
{
lean_object* v_str_427_; lean_object* v_startInclusive_428_; lean_object* v_endExclusive_429_; lean_object* v___x_430_; 
v_str_427_ = lean_ctor_get(v_s_426_, 0);
v_startInclusive_428_ = lean_ctor_get(v_s_426_, 1);
v_endExclusive_429_ = lean_ctor_get(v_s_426_, 2);
v___x_430_ = lean_string_utf8_extract_fast(v_str_427_, v_startInclusive_428_, v_endExclusive_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_copy___boxed(lean_object* v_s_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_String_Slice_copy(v_s_431_);
lean_dec_ref(v_s_431_);
return v_res_432_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_isValidForSlice(lean_object* v_s_433_, lean_object* v_p_434_){
_start:
{
lean_object* v_str_435_; lean_object* v_startInclusive_436_; lean_object* v_endExclusive_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v_str_435_ = lean_ctor_get(v_s_433_, 0);
v_startInclusive_436_ = lean_ctor_get(v_s_433_, 1);
v_endExclusive_437_ = lean_ctor_get(v_s_433_, 2);
v___x_438_ = lean_nat_sub(v_endExclusive_437_, v_startInclusive_436_);
v___x_439_ = lean_unsigned_to_nat(1u);
v___x_440_ = lean_nat_add(v_p_434_, v___x_439_);
v___x_441_ = lean_nat_dec_le(v___x_440_, v___x_438_);
lean_dec(v___x_440_);
if (v___x_441_ == 0)
{
uint8_t v_decide_442_; 
v_decide_442_ = lean_nat_dec_eq(v_p_434_, v___x_438_);
lean_dec(v___x_438_);
return v_decide_442_;
}
else
{
lean_object* v___x_443_; uint8_t v___x_444_; uint8_t v___x_445_; uint8_t v___x_446_; uint8_t v___x_447_; uint8_t v___x_448_; 
lean_dec(v___x_438_);
v___x_443_ = lean_nat_add(v_startInclusive_436_, v_p_434_);
v___x_444_ = lean_string_get_byte_fast(v_str_435_, v___x_443_);
v___x_445_ = 128;
v___x_446_ = lean_uint8_land(v___x_444_, v___x_445_);
v___x_447_ = 0;
v___x_448_ = lean_uint8_dec_eq(v___x_446_, v___x_447_);
if (v___x_448_ == 0)
{
uint8_t v___x_449_; uint8_t v___x_450_; uint8_t v___x_451_; uint8_t v___x_452_; 
v___x_449_ = 224;
v___x_450_ = lean_uint8_land(v___x_444_, v___x_449_);
v___x_451_ = 192;
v___x_452_ = lean_uint8_dec_eq(v___x_450_, v___x_451_);
if (v___x_452_ == 0)
{
uint8_t v___x_453_; uint8_t v___x_454_; uint8_t v___x_455_; 
v___x_453_ = 240;
v___x_454_ = lean_uint8_land(v___x_444_, v___x_453_);
v___x_455_ = lean_uint8_dec_eq(v___x_454_, v___x_449_);
if (v___x_455_ == 0)
{
uint8_t v___x_456_; uint8_t v___x_457_; uint8_t v___x_458_; 
v___x_456_ = 248;
v___x_457_ = lean_uint8_land(v___x_444_, v___x_456_);
v___x_458_ = lean_uint8_dec_eq(v___x_457_, v___x_453_);
return v___x_458_;
}
else
{
return v___x_455_;
}
}
else
{
return v___x_452_;
}
}
else
{
return v___x_448_;
}
}
}
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
LEAN_EXPORT uint8_t l_String_instDecidableIsValidForSlice(lean_object* v_s_463_, lean_object* v_p_464_){
_start:
{
uint8_t v___x_465_; 
v___x_465_ = l_String_Pos_Raw_isValidForSlice(v_s_463_, v_p_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsValidForSlice___boxed(lean_object* v_s_466_, lean_object* v_p_467_){
_start:
{
uint8_t v_res_468_; lean_object* v_r_469_; 
v_res_468_ = l_String_instDecidableIsValidForSlice(v_s_466_, v_p_467_);
lean_dec(v_p_467_);
lean_dec_ref(v_s_466_);
v_r_469_ = lean_box(v_res_468_);
return v_r_469_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str(lean_object* v_s_470_, lean_object* v_pos_471_){
_start:
{
lean_object* v_startInclusive_472_; lean_object* v___x_473_; 
v_startInclusive_472_ = lean_ctor_get(v_s_470_, 1);
v___x_473_ = lean_nat_add(v_startInclusive_472_, v_pos_471_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str___boxed(lean_object* v_s_474_, lean_object* v_pos_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_String_Slice_Pos_str(v_s_474_, v_pos_475_);
lean_dec(v_pos_475_);
lean_dec_ref(v_s_474_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg(lean_object* v_s_477_, lean_object* v_pos_478_){
_start:
{
lean_object* v_startInclusive_479_; lean_object* v___x_480_; 
v_startInclusive_479_ = lean_ctor_get(v_s_477_, 1);
v___x_480_ = lean_nat_sub(v_pos_478_, v_startInclusive_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___redArg___boxed(lean_object* v_s_481_, lean_object* v_pos_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_String_Slice_Pos_ofStr___redArg(v_s_481_, v_pos_482_);
lean_dec(v_pos_482_);
lean_dec_ref(v_s_481_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr(lean_object* v_s_484_, lean_object* v_pos_485_, lean_object* v_h_u2081_486_, lean_object* v_h_u2082_487_){
_start:
{
lean_object* v_startInclusive_488_; lean_object* v___x_489_; 
v_startInclusive_488_ = lean_ctor_get(v_s_484_, 1);
v___x_489_ = lean_nat_sub(v_pos_485_, v_startInclusive_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofStr___boxed(lean_object* v_s_490_, lean_object* v_pos_491_, lean_object* v_h_u2081_492_, lean_object* v_h_u2082_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_String_Slice_Pos_ofStr(v_s_490_, v_pos_491_, v_h_u2081_492_, v_h_u2082_493_);
lean_dec(v_pos_491_);
lean_dec_ref(v_s_490_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom(lean_object* v_s_495_, lean_object* v_pos_496_){
_start:
{
lean_object* v_str_497_; lean_object* v_startInclusive_498_; lean_object* v_endExclusive_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_507_; 
v_str_497_ = lean_ctor_get(v_s_495_, 0);
v_startInclusive_498_ = lean_ctor_get(v_s_495_, 1);
v_endExclusive_499_ = lean_ctor_get(v_s_495_, 2);
v_isSharedCheck_507_ = !lean_is_exclusive(v_s_495_);
if (v_isSharedCheck_507_ == 0)
{
v___x_501_ = v_s_495_;
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_endExclusive_499_);
lean_inc(v_startInclusive_498_);
lean_inc(v_str_497_);
lean_dec(v_s_495_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = lean_nat_add(v_startInclusive_498_, v_pos_496_);
lean_dec(v_startInclusive_498_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 1, v___x_503_);
v___x_505_ = v___x_501_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_str_497_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_506_, 2, v_endExclusive_499_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceFrom___boxed(lean_object* v_s_508_, lean_object* v_pos_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_String_Slice_sliceFrom(v_s_508_, v_pos_509_);
lean_dec(v_pos_509_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStart(lean_object* v_s_511_, lean_object* v_pos_512_){
_start:
{
lean_object* v_str_513_; lean_object* v_startInclusive_514_; lean_object* v_endExclusive_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_523_; 
v_str_513_ = lean_ctor_get(v_s_511_, 0);
v_startInclusive_514_ = lean_ctor_get(v_s_511_, 1);
v_endExclusive_515_ = lean_ctor_get(v_s_511_, 2);
v_isSharedCheck_523_ = !lean_is_exclusive(v_s_511_);
if (v_isSharedCheck_523_ == 0)
{
v___x_517_ = v_s_511_;
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_endExclusive_515_);
lean_inc(v_startInclusive_514_);
lean_inc(v_str_513_);
lean_dec(v_s_511_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_519_ = lean_nat_add(v_startInclusive_514_, v_pos_512_);
lean_dec(v_startInclusive_514_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 1, v___x_519_);
v___x_521_ = v___x_517_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_str_513_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_522_, 2, v_endExclusive_515_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStart___boxed(lean_object* v_s_524_, lean_object* v_pos_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_String_Slice_replaceStart(v_s_524_, v_pos_525_);
lean_dec(v_pos_525_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceTo(lean_object* v_s_527_, lean_object* v_pos_528_){
_start:
{
lean_object* v_str_529_; lean_object* v_startInclusive_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_538_; 
v_str_529_ = lean_ctor_get(v_s_527_, 0);
v_startInclusive_530_ = lean_ctor_get(v_s_527_, 1);
v_isSharedCheck_538_ = !lean_is_exclusive(v_s_527_);
if (v_isSharedCheck_538_ == 0)
{
lean_object* v_unused_539_; 
v_unused_539_ = lean_ctor_get(v_s_527_, 2);
lean_dec(v_unused_539_);
v___x_532_ = v_s_527_;
v_isShared_533_ = v_isSharedCheck_538_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_startInclusive_530_);
lean_inc(v_str_529_);
lean_dec(v_s_527_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_538_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_534_ = lean_nat_add(v_startInclusive_530_, v_pos_528_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 2, v___x_534_);
v___x_536_ = v___x_532_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_str_529_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_startInclusive_530_);
lean_ctor_set(v_reuseFailAlloc_537_, 2, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_sliceTo___boxed(lean_object* v_s_540_, lean_object* v_pos_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_String_Slice_sliceTo(v_s_540_, v_pos_541_);
lean_dec(v_pos_541_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd(lean_object* v_s_543_, lean_object* v_pos_544_){
_start:
{
lean_object* v_str_545_; lean_object* v_startInclusive_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_554_; 
v_str_545_ = lean_ctor_get(v_s_543_, 0);
v_startInclusive_546_ = lean_ctor_get(v_s_543_, 1);
v_isSharedCheck_554_ = !lean_is_exclusive(v_s_543_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; 
v_unused_555_ = lean_ctor_get(v_s_543_, 2);
lean_dec(v_unused_555_);
v___x_548_ = v_s_543_;
v_isShared_549_ = v_isSharedCheck_554_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_startInclusive_546_);
lean_inc(v_str_545_);
lean_dec(v_s_543_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_554_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_550_ = lean_nat_add(v_startInclusive_546_, v_pos_544_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 2, v___x_550_);
v___x_552_ = v___x_548_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_str_545_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_startInclusive_546_);
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
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd___boxed(lean_object* v_s_556_, lean_object* v_pos_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_String_Slice_replaceEnd(v_s_556_, v_pos_557_);
lean_dec(v_pos_557_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg(lean_object* v_s_559_, lean_object* v_newStart_560_, lean_object* v_newEnd_561_){
_start:
{
lean_object* v_str_562_; lean_object* v_startInclusive_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_572_; 
v_str_562_ = lean_ctor_get(v_s_559_, 0);
v_startInclusive_563_ = lean_ctor_get(v_s_559_, 1);
v_isSharedCheck_572_ = !lean_is_exclusive(v_s_559_);
if (v_isSharedCheck_572_ == 0)
{
lean_object* v_unused_573_; 
v_unused_573_ = lean_ctor_get(v_s_559_, 2);
lean_dec(v_unused_573_);
v___x_565_ = v_s_559_;
v_isShared_566_ = v_isSharedCheck_572_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_startInclusive_563_);
lean_inc(v_str_562_);
lean_dec(v_s_559_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_572_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_567_ = lean_nat_add(v_startInclusive_563_, v_newStart_560_);
v___x_568_ = lean_nat_add(v_startInclusive_563_, v_newEnd_561_);
lean_dec(v_startInclusive_563_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 2, v___x_568_);
lean_ctor_set(v___x_565_, 1, v___x_567_);
v___x_570_ = v___x_565_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_str_562_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___redArg___boxed(lean_object* v_s_574_, lean_object* v_newStart_575_, lean_object* v_newEnd_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_String_Slice_slice___redArg(v_s_574_, v_newStart_575_, v_newEnd_576_);
lean_dec(v_newEnd_576_);
lean_dec(v_newStart_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice(lean_object* v_s_578_, lean_object* v_newStart_579_, lean_object* v_newEnd_580_, lean_object* v_h_581_){
_start:
{
lean_object* v_str_582_; lean_object* v_startInclusive_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_592_; 
v_str_582_ = lean_ctor_get(v_s_578_, 0);
v_startInclusive_583_ = lean_ctor_get(v_s_578_, 1);
v_isSharedCheck_592_ = !lean_is_exclusive(v_s_578_);
if (v_isSharedCheck_592_ == 0)
{
lean_object* v_unused_593_; 
v_unused_593_ = lean_ctor_get(v_s_578_, 2);
lean_dec(v_unused_593_);
v___x_585_ = v_s_578_;
v_isShared_586_ = v_isSharedCheck_592_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_startInclusive_583_);
lean_inc(v_str_582_);
lean_dec(v_s_578_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_592_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_587_ = lean_nat_add(v_startInclusive_583_, v_newStart_579_);
v___x_588_ = lean_nat_add(v_startInclusive_583_, v_newEnd_580_);
lean_dec(v_startInclusive_583_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 2, v___x_588_);
lean_ctor_set(v___x_585_, 1, v___x_587_);
v___x_590_ = v___x_585_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_str_582_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice___boxed(lean_object* v_s_594_, lean_object* v_newStart_595_, lean_object* v_newEnd_596_, lean_object* v_h_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_String_Slice_slice(v_s_594_, v_newStart_595_, v_newEnd_596_, v_h_597_);
lean_dec(v_newEnd_596_);
lean_dec(v_newStart_595_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg(lean_object* v_s_599_, lean_object* v_newStart_600_, lean_object* v_newEnd_601_){
_start:
{
lean_object* v_str_602_; lean_object* v_startInclusive_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_612_; 
v_str_602_ = lean_ctor_get(v_s_599_, 0);
v_startInclusive_603_ = lean_ctor_get(v_s_599_, 1);
v_isSharedCheck_612_ = !lean_is_exclusive(v_s_599_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; 
v_unused_613_ = lean_ctor_get(v_s_599_, 2);
lean_dec(v_unused_613_);
v___x_605_ = v_s_599_;
v_isShared_606_ = v_isSharedCheck_612_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_startInclusive_603_);
lean_inc(v_str_602_);
lean_dec(v_s_599_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_612_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_607_ = lean_nat_add(v_startInclusive_603_, v_newStart_600_);
v___x_608_ = lean_nat_add(v_startInclusive_603_, v_newEnd_601_);
lean_dec(v_startInclusive_603_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 2, v___x_608_);
lean_ctor_set(v___x_605_, 1, v___x_607_);
v___x_610_ = v___x_605_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_str_602_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg___boxed(lean_object* v_s_614_, lean_object* v_newStart_615_, lean_object* v_newEnd_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_String_Slice_replaceStartEnd___redArg(v_s_614_, v_newStart_615_, v_newEnd_616_);
lean_dec(v_newEnd_616_);
lean_dec(v_newStart_615_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd(lean_object* v_s_618_, lean_object* v_newStart_619_, lean_object* v_newEnd_620_, lean_object* v_h_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_String_Slice_replaceStartEnd___redArg(v_s_618_, v_newStart_619_, v_newEnd_620_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___boxed(lean_object* v_s_623_, lean_object* v_newStart_624_, lean_object* v_newEnd_625_, lean_object* v_h_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_String_Slice_replaceStartEnd(v_s_623_, v_newStart_624_, v_newEnd_625_, v_h_626_);
lean_dec(v_newEnd_625_);
lean_dec(v_newStart_624_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f(lean_object* v_s_628_, lean_object* v_newStart_629_, lean_object* v_newEnd_630_){
_start:
{
uint8_t v___x_631_; 
v___x_631_ = lean_nat_dec_le(v_newStart_629_, v_newEnd_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; 
lean_dec_ref(v_s_628_);
v___x_632_ = lean_box(0);
return v___x_632_;
}
else
{
lean_object* v_str_633_; lean_object* v_startInclusive_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_644_; 
v_str_633_ = lean_ctor_get(v_s_628_, 0);
v_startInclusive_634_ = lean_ctor_get(v_s_628_, 1);
v_isSharedCheck_644_ = !lean_is_exclusive(v_s_628_);
if (v_isSharedCheck_644_ == 0)
{
lean_object* v_unused_645_; 
v_unused_645_ = lean_ctor_get(v_s_628_, 2);
lean_dec(v_unused_645_);
v___x_636_ = v_s_628_;
v_isShared_637_ = v_isSharedCheck_644_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_startInclusive_634_);
lean_inc(v_str_633_);
lean_dec(v_s_628_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_644_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_638_ = lean_nat_add(v_startInclusive_634_, v_newStart_629_);
v___x_639_ = lean_nat_add(v_startInclusive_634_, v_newEnd_630_);
lean_dec(v_startInclusive_634_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 2, v___x_639_);
lean_ctor_set(v___x_636_, 1, v___x_638_);
v___x_641_ = v___x_636_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_str_633_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v___x_639_);
v___x_641_ = v_reuseFailAlloc_643_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_642_; 
v___x_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
return v___x_642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x3f___boxed(lean_object* v_s_646_, lean_object* v_newStart_647_, lean_object* v_newEnd_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_String_Slice_slice_x3f(v_s_646_, v_newStart_647_, v_newEnd_648_);
lean_dec(v_newEnd_648_);
lean_dec(v_newStart_647_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_slice_x21_spec__0(lean_object* v_msg_650_){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = l_String_instInhabitedSlice;
v___x_652_ = lean_panic_fn_borrowed(v___x_651_, v_msg_650_);
return v___x_652_;
}
}
static lean_object* _init_l_String_Slice_slice_x21___closed__2(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_655_ = ((lean_object*)(l_String_Slice_slice_x21___closed__1));
v___x_656_ = lean_unsigned_to_nat(4u);
v___x_657_ = lean_unsigned_to_nat(1046u);
v___x_658_ = ((lean_object*)(l_String_Slice_slice_x21___closed__0));
v___x_659_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_660_ = l_mkPanicMessageWithDecl(v___x_659_, v___x_658_, v___x_657_, v___x_656_, v___x_655_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x21(lean_object* v_s_661_, lean_object* v_newStart_662_, lean_object* v_newEnd_663_){
_start:
{
uint8_t v___x_664_; 
v___x_664_ = lean_nat_dec_le(v_newStart_662_, v_newEnd_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; 
lean_dec_ref(v_s_661_);
v___x_665_ = lean_obj_once(&l_String_Slice_slice_x21___closed__2, &l_String_Slice_slice_x21___closed__2_once, _init_l_String_Slice_slice_x21___closed__2);
v___x_666_ = l_panic___at___00String_Slice_slice_x21_spec__0(v___x_665_);
return v___x_666_;
}
else
{
lean_object* v_str_667_; lean_object* v_startInclusive_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_677_; 
v_str_667_ = lean_ctor_get(v_s_661_, 0);
v_startInclusive_668_ = lean_ctor_get(v_s_661_, 1);
v_isSharedCheck_677_ = !lean_is_exclusive(v_s_661_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; 
v_unused_678_ = lean_ctor_get(v_s_661_, 2);
lean_dec(v_unused_678_);
v___x_670_ = v_s_661_;
v_isShared_671_ = v_isSharedCheck_677_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_startInclusive_668_);
lean_inc(v_str_667_);
lean_dec(v_s_661_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_677_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_672_ = lean_nat_add(v_startInclusive_668_, v_newStart_662_);
v___x_673_ = lean_nat_add(v_startInclusive_668_, v_newEnd_663_);
lean_dec(v_startInclusive_668_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 2, v___x_673_);
lean_ctor_set(v___x_670_, 1, v___x_672_);
v___x_675_ = v___x_670_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_str_667_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_slice_x21___boxed(lean_object* v_s_679_, lean_object* v_newStart_680_, lean_object* v_newEnd_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_String_Slice_slice_x21(v_s_679_, v_newStart_680_, v_newEnd_681_);
lean_dec(v_newEnd_681_);
lean_dec(v_newStart_680_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21(lean_object* v_s_683_, lean_object* v_newStart_684_, lean_object* v_newEnd_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_String_Slice_slice_x21(v_s_683_, v_newStart_684_, v_newEnd_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21___boxed(lean_object* v_s_687_, lean_object* v_newStart_688_, lean_object* v_newEnd_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_String_Slice_replaceStartEnd_x21(v_s_687_, v_newStart_688_, v_newEnd_689_);
lean_dec(v_newEnd_689_);
lean_dec(v_newStart_688_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_String_decodeChar___boxed(lean_object* v_s_694_, lean_object* v_byteIdx_695_, lean_object* v_h_696_){
_start:
{
uint32_t v_res_697_; lean_object* v_r_698_; 
v_res_697_ = lean_string_utf8_get_fast(v_s_694_, v_byteIdx_695_);
lean_dec(v_byteIdx_695_);
lean_dec_ref(v_s_694_);
v_r_698_ = lean_box_uint32(v_res_697_);
return v_r_698_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get___redArg(lean_object* v_s_699_, lean_object* v_pos_700_){
_start:
{
lean_object* v_str_701_; lean_object* v_startInclusive_702_; lean_object* v___x_703_; uint32_t v___x_704_; 
v_str_701_ = lean_ctor_get(v_s_699_, 0);
v_startInclusive_702_ = lean_ctor_get(v_s_699_, 1);
v___x_703_ = lean_nat_add(v_startInclusive_702_, v_pos_700_);
v___x_704_ = lean_string_utf8_get_fast(v_str_701_, v___x_703_);
lean_dec(v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___redArg___boxed(lean_object* v_s_705_, lean_object* v_pos_706_){
_start:
{
uint32_t v_res_707_; lean_object* v_r_708_; 
v_res_707_ = l_String_Slice_Pos_get___redArg(v_s_705_, v_pos_706_);
lean_dec(v_pos_706_);
lean_dec_ref(v_s_705_);
v_r_708_ = lean_box_uint32(v_res_707_);
return v_r_708_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get(lean_object* v_s_709_, lean_object* v_pos_710_, lean_object* v_h_711_){
_start:
{
lean_object* v_str_712_; lean_object* v_startInclusive_713_; lean_object* v___x_714_; uint32_t v___x_715_; 
v_str_712_ = lean_ctor_get(v_s_709_, 0);
v_startInclusive_713_ = lean_ctor_get(v_s_709_, 1);
v___x_714_ = lean_nat_add(v_startInclusive_713_, v_pos_710_);
v___x_715_ = lean_string_utf8_get_fast(v_str_712_, v___x_714_);
lean_dec(v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___boxed(lean_object* v_s_716_, lean_object* v_pos_717_, lean_object* v_h_718_){
_start:
{
uint32_t v_res_719_; lean_object* v_r_720_; 
v_res_719_ = l_String_Slice_Pos_get(v_s_716_, v_pos_717_, v_h_718_);
lean_dec(v_pos_717_);
lean_dec_ref(v_s_716_);
v_r_720_ = lean_box_uint32(v_res_719_);
return v_r_720_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f(lean_object* v_s_721_, lean_object* v_pos_722_){
_start:
{
lean_object* v_str_723_; lean_object* v_startInclusive_724_; lean_object* v_endExclusive_725_; lean_object* v___x_726_; uint8_t v_decide_727_; 
v_str_723_ = lean_ctor_get(v_s_721_, 0);
v_startInclusive_724_ = lean_ctor_get(v_s_721_, 1);
v_endExclusive_725_ = lean_ctor_get(v_s_721_, 2);
v___x_726_ = lean_nat_sub(v_endExclusive_725_, v_startInclusive_724_);
v_decide_727_ = lean_nat_dec_eq(v_pos_722_, v___x_726_);
lean_dec(v___x_726_);
if (v_decide_727_ == 0)
{
lean_object* v___x_728_; uint32_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_728_ = lean_nat_add(v_startInclusive_724_, v_pos_722_);
v___x_729_ = lean_string_utf8_get_fast(v_str_723_, v___x_728_);
lean_dec(v___x_728_);
v___x_730_ = lean_box_uint32(v___x_729_);
v___x_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
else
{
lean_object* v___x_732_; 
v___x_732_ = lean_box(0);
return v___x_732_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f___boxed(lean_object* v_s_733_, lean_object* v_pos_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_String_Slice_Pos_get_x3f(v_s_733_, v_pos_734_);
lean_dec(v_pos_734_);
lean_dec_ref(v_s_733_);
return v_res_735_;
}
}
static lean_object* _init_l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1(void){
_start:
{
uint32_t v___x_736_; lean_object* v___x_737_; 
v___x_736_ = 65;
v___x_737_ = lean_box_uint32(v___x_736_);
return v___x_737_;
}
}
LEAN_EXPORT uint32_t l_panic___at___00String_Slice_Pos_get_x21_spec__0(lean_object* v_msg_738_){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; uint32_t v___x_741_; 
v___x_739_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1;
v___x_740_ = lean_panic_fn_borrowed(v___x_739_, v_msg_738_);
v___x_741_ = lean_unbox_uint32(v___x_740_);
lean_dec(v___x_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed(lean_object* v_msg_742_){
_start:
{
uint32_t v_res_743_; lean_object* v_r_744_; 
v_res_743_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v_msg_742_);
v_r_744_ = lean_box_uint32(v_res_743_);
return v_r_744_;
}
}
static lean_object* _init_l_String_Slice_Pos_get_x21___closed__2(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_747_ = ((lean_object*)(l_String_Slice_Pos_get_x21___closed__1));
v___x_748_ = lean_unsigned_to_nat(29u);
v___x_749_ = lean_unsigned_to_nat(1131u);
v___x_750_ = ((lean_object*)(l_String_Slice_Pos_get_x21___closed__0));
v___x_751_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_752_ = l_mkPanicMessageWithDecl(v___x_751_, v___x_750_, v___x_749_, v___x_748_, v___x_747_);
return v___x_752_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get_x21(lean_object* v_s_753_, lean_object* v_pos_754_){
_start:
{
lean_object* v_str_755_; lean_object* v_startInclusive_756_; lean_object* v_endExclusive_757_; lean_object* v___x_758_; uint8_t v_decide_759_; 
v_str_755_ = lean_ctor_get(v_s_753_, 0);
v_startInclusive_756_ = lean_ctor_get(v_s_753_, 1);
v_endExclusive_757_ = lean_ctor_get(v_s_753_, 2);
v___x_758_ = lean_nat_sub(v_endExclusive_757_, v_startInclusive_756_);
v_decide_759_ = lean_nat_dec_eq(v_pos_754_, v___x_758_);
lean_dec(v___x_758_);
if (v_decide_759_ == 0)
{
lean_object* v___x_760_; uint32_t v___x_761_; 
v___x_760_ = lean_nat_add(v_startInclusive_756_, v_pos_754_);
v___x_761_ = lean_string_utf8_get_fast(v_str_755_, v___x_760_);
lean_dec(v___x_760_);
return v___x_761_;
}
else
{
lean_object* v___x_762_; uint32_t v___x_763_; 
v___x_762_ = lean_obj_once(&l_String_Slice_Pos_get_x21___closed__2, &l_String_Slice_Pos_get_x21___closed__2_once, _init_l_String_Slice_Pos_get_x21___closed__2);
v___x_763_ = l_panic___at___00String_Slice_Pos_get_x21_spec__0(v___x_762_);
return v___x_763_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x21___boxed(lean_object* v_s_764_, lean_object* v_pos_765_){
_start:
{
uint32_t v_res_766_; lean_object* v_r_767_; 
v_res_766_ = l_String_Slice_Pos_get_x21(v_s_764_, v_pos_765_);
lean_dec(v_pos_765_);
lean_dec_ref(v_s_764_);
v_r_767_ = lean_box_uint32(v_res_766_);
return v_r_767_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg(lean_object* v_pos_768_){
_start:
{
lean_inc(v_pos_768_);
return v_pos_768_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___redArg___boxed(lean_object* v_pos_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_String_Pos_toSlice___redArg(v_pos_769_);
lean_dec(v_pos_769_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice(lean_object* v_s_771_, lean_object* v_pos_772_){
_start:
{
lean_inc(v_pos_772_);
return v_pos_772_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSlice___boxed(lean_object* v_s_773_, lean_object* v_pos_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_String_Pos_toSlice(v_s_773_, v_pos_774_);
lean_dec(v_pos_774_);
lean_dec_ref(v_s_773_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg(lean_object* v_pos_776_){
_start:
{
lean_inc(v_pos_776_);
return v_pos_776_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___redArg___boxed(lean_object* v_pos_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_String_Pos_ofToSlice___redArg(v_pos_777_);
lean_dec(v_pos_777_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice(lean_object* v_s_779_, lean_object* v_pos_780_){
_start:
{
lean_inc(v_pos_780_);
return v_pos_780_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofToSlice___boxed(lean_object* v_s_781_, lean_object* v_pos_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_String_Pos_ofToSlice(v_s_781_, v_pos_782_);
lean_dec(v_pos_782_);
lean_dec_ref(v_s_781_);
return v_res_783_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get___redArg(lean_object* v_s_784_, lean_object* v_pos_785_){
_start:
{
uint32_t v___x_786_; 
v___x_786_ = lean_string_utf8_get_fast(v_s_784_, v_pos_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get___redArg___boxed(lean_object* v_s_787_, lean_object* v_pos_788_){
_start:
{
uint32_t v_res_789_; lean_object* v_r_790_; 
v_res_789_ = l_String_Pos_get___redArg(v_s_787_, v_pos_788_);
lean_dec(v_pos_788_);
lean_dec_ref(v_s_787_);
v_r_790_ = lean_box_uint32(v_res_789_);
return v_r_790_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get(lean_object* v_s_791_, lean_object* v_pos_792_, lean_object* v_h_793_){
_start:
{
uint32_t v___x_794_; 
v___x_794_ = lean_string_utf8_get_fast(v_s_791_, v_pos_792_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get___boxed(lean_object* v_s_795_, lean_object* v_pos_796_, lean_object* v_h_797_){
_start:
{
uint32_t v_res_798_; lean_object* v_r_799_; 
v_res_798_ = l_String_Pos_get(v_s_795_, v_pos_796_, v_h_797_);
lean_dec(v_pos_796_);
lean_dec_ref(v_s_795_);
v_r_799_ = lean_box_uint32(v_res_798_);
return v_r_799_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x3f(lean_object* v_s_800_, lean_object* v_pos_801_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = lean_string_utf8_byte_size(v_s_800_);
v___x_804_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_804_, 0, v_s_800_);
lean_ctor_set(v___x_804_, 1, v___x_802_);
lean_ctor_set(v___x_804_, 2, v___x_803_);
v___x_805_ = l_String_Slice_Pos_get_x3f(v___x_804_, v_pos_801_);
lean_dec_ref_known(v___x_804_, 3);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x3f___boxed(lean_object* v_s_806_, lean_object* v_pos_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_String_Pos_get_x3f(v_s_806_, v_pos_807_);
lean_dec(v_pos_807_);
return v_res_808_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_get_x21(lean_object* v_s_809_, lean_object* v_pos_810_){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; uint32_t v___x_814_; 
v___x_811_ = lean_unsigned_to_nat(0u);
v___x_812_ = lean_string_utf8_byte_size(v_s_809_);
v___x_813_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_813_, 0, v_s_809_);
lean_ctor_set(v___x_813_, 1, v___x_811_);
lean_ctor_set(v___x_813_, 2, v___x_812_);
v___x_814_ = l_String_Slice_Pos_get_x21(v___x_813_, v_pos_810_);
lean_dec_ref_known(v___x_813_, 3);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_get_x21___boxed(lean_object* v_s_815_, lean_object* v_pos_816_){
_start:
{
uint32_t v_res_817_; lean_object* v_r_818_; 
v_res_817_ = l_String_Pos_get_x21(v_s_815_, v_pos_816_);
lean_dec(v_pos_816_);
v_r_818_ = lean_box_uint32(v_res_817_);
return v_r_818_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_byte___redArg(lean_object* v_s_819_, lean_object* v_pos_820_){
_start:
{
uint8_t v___x_821_; 
v___x_821_ = lean_string_get_byte_fast(v_s_819_, v_pos_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_byte___redArg___boxed(lean_object* v_s_822_, lean_object* v_pos_823_){
_start:
{
uint8_t v_res_824_; lean_object* v_r_825_; 
v_res_824_ = l_String_Pos_byte___redArg(v_s_822_, v_pos_823_);
lean_dec_ref(v_s_822_);
v_r_825_ = lean_box(v_res_824_);
return v_r_825_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_byte(lean_object* v_s_826_, lean_object* v_pos_827_, lean_object* v_h_828_){
_start:
{
uint8_t v___x_829_; 
v___x_829_ = lean_string_get_byte_fast(v_s_826_, v_pos_827_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_byte___boxed(lean_object* v_s_830_, lean_object* v_pos_831_, lean_object* v_h_832_){
_start:
{
uint8_t v_res_833_; lean_object* v_r_834_; 
v_res_833_ = l_String_Pos_byte(v_s_830_, v_pos_831_, v_h_832_);
lean_dec_ref(v_s_830_);
v_r_834_ = lean_box(v_res_833_);
return v_r_834_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg(lean_object* v_pos_835_){
_start:
{
lean_inc(v_pos_835_);
return v_pos_835_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___redArg___boxed(lean_object* v_pos_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_String_Pos_ofCopy___redArg(v_pos_836_);
lean_dec(v_pos_836_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy(lean_object* v_s_838_, lean_object* v_pos_839_){
_start:
{
lean_inc(v_pos_839_);
return v_pos_839_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofCopy___boxed(lean_object* v_s_840_, lean_object* v_pos_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_String_Pos_ofCopy(v_s_840_, v_pos_841_);
lean_dec(v_pos_841_);
lean_dec_ref(v_s_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg(lean_object* v_pos_843_){
_start:
{
lean_inc(v_pos_843_);
return v_pos_843_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___redArg___boxed(lean_object* v_pos_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_String_Slice_Pos_copy___redArg(v_pos_844_);
lean_dec(v_pos_844_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy(lean_object* v_s_846_, lean_object* v_pos_847_){
_start:
{
lean_inc(v_pos_847_);
return v_pos_847_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_copy___boxed(lean_object* v_s_848_, lean_object* v_pos_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_String_Slice_Pos_copy(v_s_848_, v_pos_849_);
lean_dec(v_pos_849_);
lean_dec_ref(v_s_848_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg(lean_object* v_pos_851_){
_start:
{
lean_inc(v_pos_851_);
return v_pos_851_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg___boxed(lean_object* v_pos_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_String_Slice_Pos_toCopy___redArg(v_pos_852_);
lean_dec(v_pos_852_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy(lean_object* v_s_854_, lean_object* v_pos_855_){
_start:
{
lean_inc(v_pos_855_);
return v_pos_855_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___boxed(lean_object* v_s_856_, lean_object* v_pos_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_String_Slice_Pos_toCopy(v_s_856_, v_pos_857_);
lean_dec(v_pos_857_);
lean_dec_ref(v_s_856_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg(lean_object* v_p_u2080_859_, lean_object* v_pos_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = lean_nat_add(v_p_u2080_859_, v_pos_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___redArg___boxed(lean_object* v_p_u2080_862_, lean_object* v_pos_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_String_Slice_Pos_ofSliceFrom___redArg(v_p_u2080_862_, v_pos_863_);
lean_dec(v_pos_863_);
lean_dec(v_p_u2080_862_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom(lean_object* v_s_865_, lean_object* v_p_u2080_866_, lean_object* v_pos_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = lean_nat_add(v_p_u2080_866_, v_pos_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceFrom___boxed(lean_object* v_s_869_, lean_object* v_p_u2080_870_, lean_object* v_pos_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_String_Slice_Pos_ofSliceFrom(v_s_869_, v_p_u2080_870_, v_pos_871_);
lean_dec(v_pos_871_);
lean_dec(v_p_u2080_870_);
lean_dec_ref(v_s_869_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg(lean_object* v_p_u2080_873_, lean_object* v_pos_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = lean_nat_add(v_p_u2080_873_, v_pos_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg___boxed(lean_object* v_p_u2080_876_, lean_object* v_pos_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_String_Slice_Pos_ofReplaceStart___redArg(v_p_u2080_876_, v_pos_877_);
lean_dec(v_pos_877_);
lean_dec(v_p_u2080_876_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart(lean_object* v_s_879_, lean_object* v_p_u2080_880_, lean_object* v_pos_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = lean_nat_add(v_p_u2080_880_, v_pos_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___boxed(lean_object* v_s_883_, lean_object* v_p_u2080_884_, lean_object* v_pos_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_String_Slice_Pos_ofReplaceStart(v_s_883_, v_p_u2080_884_, v_pos_885_);
lean_dec(v_pos_885_);
lean_dec(v_p_u2080_884_);
lean_dec_ref(v_s_883_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg(lean_object* v_p_u2080_887_, lean_object* v_pos_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = lean_nat_sub(v_pos_888_, v_p_u2080_887_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___redArg___boxed(lean_object* v_p_u2080_890_, lean_object* v_pos_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_String_Slice_Pos_sliceFrom___redArg(v_p_u2080_890_, v_pos_891_);
lean_dec(v_pos_891_);
lean_dec(v_p_u2080_890_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom(lean_object* v_s_893_, lean_object* v_p_u2080_894_, lean_object* v_pos_895_, lean_object* v_h_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = lean_nat_sub(v_pos_895_, v_p_u2080_894_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceFrom___boxed(lean_object* v_s_898_, lean_object* v_p_u2080_899_, lean_object* v_pos_900_, lean_object* v_h_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_String_Slice_Pos_sliceFrom(v_s_898_, v_p_u2080_899_, v_pos_900_, v_h_901_);
lean_dec(v_pos_900_);
lean_dec(v_p_u2080_899_);
lean_dec_ref(v_s_898_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg(lean_object* v_p_u2080_903_, lean_object* v_pos_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = lean_nat_sub(v_pos_904_, v_p_u2080_903_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg___boxed(lean_object* v_p_u2080_906_, lean_object* v_pos_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_String_Slice_Pos_toReplaceStart___redArg(v_p_u2080_906_, v_pos_907_);
lean_dec(v_pos_907_);
lean_dec(v_p_u2080_906_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart(lean_object* v_s_909_, lean_object* v_p_u2080_910_, lean_object* v_pos_911_, lean_object* v_h_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = lean_nat_sub(v_pos_911_, v_p_u2080_910_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___boxed(lean_object* v_s_914_, lean_object* v_p_u2080_915_, lean_object* v_pos_916_, lean_object* v_h_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_String_Slice_Pos_toReplaceStart(v_s_914_, v_p_u2080_915_, v_pos_916_, v_h_917_);
lean_dec(v_pos_916_);
lean_dec(v_p_u2080_915_);
lean_dec_ref(v_s_914_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg(lean_object* v_pos_919_){
_start:
{
lean_inc(v_pos_919_);
return v_pos_919_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___redArg___boxed(lean_object* v_pos_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_String_Slice_Pos_ofSliceTo___redArg(v_pos_920_);
lean_dec(v_pos_920_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo(lean_object* v_s_922_, lean_object* v_p_u2080_923_, lean_object* v_pos_924_){
_start:
{
lean_inc(v_pos_924_);
return v_pos_924_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSliceTo___boxed(lean_object* v_s_925_, lean_object* v_p_u2080_926_, lean_object* v_pos_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_String_Slice_Pos_ofSliceTo(v_s_925_, v_p_u2080_926_, v_pos_927_);
lean_dec(v_pos_927_);
lean_dec(v_p_u2080_926_);
lean_dec_ref(v_s_925_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg(lean_object* v_pos_929_){
_start:
{
lean_inc(v_pos_929_);
return v_pos_929_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg___boxed(lean_object* v_pos_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_String_Slice_Pos_ofReplaceEnd___redArg(v_pos_930_);
lean_dec(v_pos_930_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd(lean_object* v_s_932_, lean_object* v_p_u2080_933_, lean_object* v_pos_934_){
_start:
{
lean_inc(v_pos_934_);
return v_pos_934_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___boxed(lean_object* v_s_935_, lean_object* v_p_u2080_936_, lean_object* v_pos_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_String_Slice_Pos_ofReplaceEnd(v_s_935_, v_p_u2080_936_, v_pos_937_);
lean_dec(v_pos_937_);
lean_dec(v_p_u2080_936_);
lean_dec_ref(v_s_935_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg(lean_object* v_pos_939_){
_start:
{
lean_inc(v_pos_939_);
return v_pos_939_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___redArg___boxed(lean_object* v_pos_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_String_Slice_Pos_sliceTo___redArg(v_pos_940_);
lean_dec(v_pos_940_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo(lean_object* v_s_942_, lean_object* v_p_u2080_943_, lean_object* v_pos_944_, lean_object* v_h_945_){
_start:
{
lean_inc(v_pos_944_);
return v_pos_944_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceTo___boxed(lean_object* v_s_946_, lean_object* v_p_u2080_947_, lean_object* v_pos_948_, lean_object* v_h_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_String_Slice_Pos_sliceTo(v_s_946_, v_p_u2080_947_, v_pos_948_, v_h_949_);
lean_dec(v_pos_948_);
lean_dec(v_p_u2080_947_);
lean_dec_ref(v_s_946_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg(lean_object* v_pos_951_){
_start:
{
lean_inc(v_pos_951_);
return v_pos_951_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg___boxed(lean_object* v_pos_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_String_Slice_Pos_toReplaceEnd___redArg(v_pos_952_);
lean_dec(v_pos_952_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd(lean_object* v_s_954_, lean_object* v_p_u2080_955_, lean_object* v_pos_956_, lean_object* v_h_957_){
_start:
{
lean_inc(v_pos_956_);
return v_pos_956_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___boxed(lean_object* v_s_958_, lean_object* v_p_u2080_959_, lean_object* v_pos_960_, lean_object* v_h_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_String_Slice_Pos_toReplaceEnd(v_s_958_, v_p_u2080_959_, v_pos_960_, v_h_961_);
lean_dec(v_pos_960_);
lean_dec(v_p_u2080_959_);
lean_dec_ref(v_s_958_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg(lean_object* v_s_963_, lean_object* v_pos_964_){
_start:
{
lean_object* v_str_965_; lean_object* v_startInclusive_966_; lean_object* v___x_967_; uint8_t v___x_968_; uint8_t v___x_969_; uint8_t v___x_970_; uint8_t v___x_971_; uint8_t v___x_972_; 
v_str_965_ = lean_ctor_get(v_s_963_, 0);
v_startInclusive_966_ = lean_ctor_get(v_s_963_, 1);
v___x_967_ = lean_nat_add(v_startInclusive_966_, v_pos_964_);
v___x_968_ = lean_string_get_byte_fast(v_str_965_, v___x_967_);
v___x_969_ = 128;
v___x_970_ = lean_uint8_land(v___x_968_, v___x_969_);
v___x_971_ = 0;
v___x_972_ = lean_uint8_dec_eq(v___x_970_, v___x_971_);
if (v___x_972_ == 0)
{
uint8_t v___x_973_; uint8_t v___x_974_; uint8_t v___x_975_; uint8_t v___x_976_; 
v___x_973_ = 224;
v___x_974_ = lean_uint8_land(v___x_968_, v___x_973_);
v___x_975_ = 192;
v___x_976_ = lean_uint8_dec_eq(v___x_974_, v___x_975_);
if (v___x_976_ == 0)
{
uint8_t v___x_977_; uint8_t v___x_978_; uint8_t v___x_979_; 
v___x_977_ = 240;
v___x_978_ = lean_uint8_land(v___x_968_, v___x_977_);
v___x_979_ = lean_uint8_dec_eq(v___x_978_, v___x_973_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = lean_unsigned_to_nat(4u);
v___x_981_ = lean_nat_add(v_pos_964_, v___x_980_);
return v___x_981_;
}
else
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_unsigned_to_nat(3u);
v___x_983_ = lean_nat_add(v_pos_964_, v___x_982_);
return v___x_983_;
}
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = lean_unsigned_to_nat(2u);
v___x_985_ = lean_nat_add(v_pos_964_, v___x_984_);
return v___x_985_;
}
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = lean_unsigned_to_nat(1u);
v___x_987_ = lean_nat_add(v_pos_964_, v___x_986_);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg___boxed(lean_object* v_s_988_, lean_object* v_pos_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_String_Slice_Pos_next___redArg(v_s_988_, v_pos_989_);
lean_dec(v_pos_989_);
lean_dec_ref(v_s_988_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next(lean_object* v_s_991_, lean_object* v_pos_992_, lean_object* v_h_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_String_Slice_Pos_next___redArg(v_s_991_, v_pos_992_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___boxed(lean_object* v_s_995_, lean_object* v_pos_996_, lean_object* v_h_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_String_Slice_Pos_next(v_s_995_, v_pos_996_, v_h_997_);
lean_dec(v_pos_996_);
lean_dec_ref(v_s_995_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f(lean_object* v_s_999_, lean_object* v_pos_1000_){
_start:
{
lean_object* v_startInclusive_1001_; lean_object* v_endExclusive_1002_; lean_object* v___x_1003_; uint8_t v_decide_1004_; 
v_startInclusive_1001_ = lean_ctor_get(v_s_999_, 1);
v_endExclusive_1002_ = lean_ctor_get(v_s_999_, 2);
v___x_1003_ = lean_nat_sub(v_endExclusive_1002_, v_startInclusive_1001_);
v_decide_1004_ = lean_nat_dec_eq(v_pos_1000_, v___x_1003_);
lean_dec(v___x_1003_);
if (v_decide_1004_ == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = l_String_Slice_Pos_next___redArg(v_s_999_, v_pos_1000_);
v___x_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
return v___x_1006_;
}
else
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_box(0);
return v___x_1007_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f___boxed(lean_object* v_s_1008_, lean_object* v_pos_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_String_Slice_Pos_next_x3f(v_s_1008_, v_pos_1009_);
lean_dec(v_pos_1009_);
lean_dec_ref(v_s_1008_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(lean_object* v_msg_1011_){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_unsigned_to_nat(0u);
v___x_1013_ = lean_panic_fn_borrowed(v___x_1012_, v_msg_1011_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0(lean_object* v_s_1014_, lean_object* v_msg_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v_msg_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___boxed(lean_object* v_s_1017_, lean_object* v_msg_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0(v_s_1017_, v_msg_1018_);
lean_dec_ref(v_s_1017_);
return v_res_1019_;
}
}
static lean_object* _init_l_String_Slice_Pos_next_x21___closed__2(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1022_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__1));
v___x_1023_ = lean_unsigned_to_nat(29u);
v___x_1024_ = lean_unsigned_to_nat(1518u);
v___x_1025_ = ((lean_object*)(l_String_Slice_Pos_next_x21___closed__0));
v___x_1026_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1027_ = l_mkPanicMessageWithDecl(v___x_1026_, v___x_1025_, v___x_1024_, v___x_1023_, v___x_1022_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21(lean_object* v_s_1028_, lean_object* v_pos_1029_){
_start:
{
lean_object* v_startInclusive_1030_; lean_object* v_endExclusive_1031_; lean_object* v___x_1032_; uint8_t v_decide_1033_; 
v_startInclusive_1030_ = lean_ctor_get(v_s_1028_, 1);
v_endExclusive_1031_ = lean_ctor_get(v_s_1028_, 2);
v___x_1032_ = lean_nat_sub(v_endExclusive_1031_, v_startInclusive_1030_);
v_decide_1033_ = lean_nat_dec_eq(v_pos_1029_, v___x_1032_);
lean_dec(v___x_1032_);
if (v_decide_1033_ == 0)
{
lean_object* v___x_1034_; 
v___x_1034_ = l_String_Slice_Pos_next___redArg(v_s_1028_, v_pos_1029_);
return v___x_1034_;
}
else
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = lean_obj_once(&l_String_Slice_Pos_next_x21___closed__2, &l_String_Slice_Pos_next_x21___closed__2_once, _init_l_String_Slice_Pos_next_x21___closed__2);
v___x_1036_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_1035_);
return v___x_1036_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21___boxed(lean_object* v_s_1037_, lean_object* v_pos_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_String_Slice_Pos_next_x21(v_s_1037_, v_pos_1038_);
lean_dec(v_pos_1038_);
lean_dec_ref(v_s_1037_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg(lean_object* v_s_1040_, lean_object* v_off_1041_){
_start:
{
uint8_t v___y_1043_; lean_object* v_str_1049_; lean_object* v_startInclusive_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; uint8_t v___x_1053_; uint8_t v___x_1054_; uint8_t v___x_1055_; uint8_t v___x_1056_; 
v_str_1049_ = lean_ctor_get(v_s_1040_, 0);
v_startInclusive_1050_ = lean_ctor_get(v_s_1040_, 1);
v___x_1051_ = lean_nat_add(v_startInclusive_1050_, v_off_1041_);
v___x_1052_ = lean_string_get_byte_fast(v_str_1049_, v___x_1051_);
v___x_1053_ = 128;
v___x_1054_ = lean_uint8_land(v___x_1052_, v___x_1053_);
v___x_1055_ = 0;
v___x_1056_ = lean_uint8_dec_eq(v___x_1054_, v___x_1055_);
if (v___x_1056_ == 0)
{
uint8_t v___x_1057_; uint8_t v___x_1058_; uint8_t v___x_1059_; uint8_t v___x_1060_; 
v___x_1057_ = 224;
v___x_1058_ = lean_uint8_land(v___x_1052_, v___x_1057_);
v___x_1059_ = 192;
v___x_1060_ = lean_uint8_dec_eq(v___x_1058_, v___x_1059_);
if (v___x_1060_ == 0)
{
uint8_t v___x_1061_; uint8_t v___x_1062_; uint8_t v___x_1063_; 
v___x_1061_ = 240;
v___x_1062_ = lean_uint8_land(v___x_1052_, v___x_1061_);
v___x_1063_ = lean_uint8_dec_eq(v___x_1062_, v___x_1057_);
if (v___x_1063_ == 0)
{
uint8_t v___x_1064_; uint8_t v___x_1065_; uint8_t v___x_1066_; 
v___x_1064_ = 248;
v___x_1065_ = lean_uint8_land(v___x_1052_, v___x_1064_);
v___x_1066_ = lean_uint8_dec_eq(v___x_1065_, v___x_1061_);
v___y_1043_ = v___x_1066_;
goto v___jp_1042_;
}
else
{
v___y_1043_ = v___x_1063_;
goto v___jp_1042_;
}
}
else
{
v___y_1043_ = v___x_1060_;
goto v___jp_1042_;
}
}
else
{
v___y_1043_ = v___x_1056_;
goto v___jp_1042_;
}
v___jp_1042_:
{
if (v___y_1043_ == 0)
{
lean_object* v_zero_1044_; uint8_t v_isZero_1045_; lean_object* v_one_1046_; lean_object* v_n_1047_; 
v_zero_1044_ = lean_unsigned_to_nat(0u);
v_isZero_1045_ = lean_nat_dec_eq(v_off_1041_, v_zero_1044_);
v_one_1046_ = lean_unsigned_to_nat(1u);
v_n_1047_ = lean_nat_sub(v_off_1041_, v_one_1046_);
lean_dec(v_off_1041_);
v_off_1041_ = v_n_1047_;
goto _start;
}
else
{
return v_off_1041_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg___boxed(lean_object* v_s_1067_, lean_object* v_off_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1067_, v_off_1068_);
lean_dec_ref(v_s_1067_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go(lean_object* v_s_1070_, lean_object* v_off_1071_, lean_object* v_h_u2081_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1070_, v_off_1071_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___boxed(lean_object* v_s_1074_, lean_object* v_off_1075_, lean_object* v_h_u2081_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_String_Slice_Pos_prevAux_go(v_s_1074_, v_off_1075_, v_h_u2081_1076_);
lean_dec_ref(v_s_1074_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg(lean_object* v_s_1078_, lean_object* v_pos_1079_){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1080_ = lean_unsigned_to_nat(1u);
v___x_1081_ = lean_nat_sub(v_pos_1079_, v___x_1080_);
v___x_1082_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1078_, v___x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg___boxed(lean_object* v_s_1083_, lean_object* v_pos_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_String_Slice_Pos_prevAux___redArg(v_s_1083_, v_pos_1084_);
lean_dec(v_pos_1084_);
lean_dec_ref(v_s_1083_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux(lean_object* v_s_1086_, lean_object* v_pos_1087_, lean_object* v_h_1088_){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = lean_unsigned_to_nat(1u);
v___x_1090_ = lean_nat_sub(v_pos_1087_, v___x_1089_);
v___x_1091_ = l_String_Slice_Pos_prevAux_go___redArg(v_s_1086_, v___x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___boxed(lean_object* v_s_1092_, lean_object* v_pos_1093_, lean_object* v_h_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_String_Slice_Pos_prevAux(v_s_1092_, v_pos_1093_, v_h_1094_);
lean_dec(v_pos_1093_);
lean_dec_ref(v_s_1092_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(lean_object* v_off_1096_, lean_object* v_h__1_1097_, lean_object* v_h__2_1098_){
_start:
{
lean_object* v_zero_1099_; uint8_t v_isZero_1100_; 
v_zero_1099_ = lean_unsigned_to_nat(0u);
v_isZero_1100_ = lean_nat_dec_eq(v_off_1096_, v_zero_1099_);
if (v_isZero_1100_ == 1)
{
lean_object* v___x_1101_; 
lean_dec(v_h__2_1098_);
v___x_1101_ = lean_apply_3(v_h__1_1097_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1101_;
}
else
{
lean_object* v_one_1102_; lean_object* v_n_1103_; lean_object* v___x_1104_; 
lean_dec(v_h__1_1097_);
v_one_1102_ = lean_unsigned_to_nat(1u);
v_n_1103_ = lean_nat_sub(v_off_1096_, v_one_1102_);
v___x_1104_ = lean_apply_4(v_h__2_1098_, v_n_1103_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg___boxed(lean_object* v_off_1105_, lean_object* v_h__1_1106_, lean_object* v_h__2_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(v_off_1105_, v_h__1_1106_, v_h__2_1107_);
lean_dec(v_off_1105_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(lean_object* v_s_1109_, lean_object* v_motive_1110_, lean_object* v_off_1111_, lean_object* v_h_u2081_1112_, lean_object* v_hbyte_1113_, lean_object* v_this_1114_, lean_object* v_h__1_1115_, lean_object* v_h__2_1116_){
_start:
{
lean_object* v_zero_1117_; uint8_t v_isZero_1118_; 
v_zero_1117_ = lean_unsigned_to_nat(0u);
v_isZero_1118_ = lean_nat_dec_eq(v_off_1111_, v_zero_1117_);
if (v_isZero_1118_ == 1)
{
lean_object* v___x_1119_; 
lean_dec(v_h__2_1116_);
v___x_1119_ = lean_apply_3(v_h__1_1115_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1119_;
}
else
{
lean_object* v_one_1120_; lean_object* v_n_1121_; lean_object* v___x_1122_; 
lean_dec(v_h__1_1115_);
v_one_1120_ = lean_unsigned_to_nat(1u);
v_n_1121_ = lean_nat_sub(v_off_1111_, v_one_1120_);
v___x_1122_ = lean_apply_4(v_h__2_1116_, v_n_1121_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1122_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___boxed(lean_object* v_s_1123_, lean_object* v_motive_1124_, lean_object* v_off_1125_, lean_object* v_h_u2081_1126_, lean_object* v_hbyte_1127_, lean_object* v_this_1128_, lean_object* v_h__1_1129_, lean_object* v_h__2_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(v_s_1123_, v_motive_1124_, v_off_1125_, v_h_u2081_1126_, v_hbyte_1127_, v_this_1128_, v_h__1_1129_, v_h__2_1130_);
lean_dec(v_off_1125_);
lean_dec_ref(v_s_1123_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg(lean_object* v_off_1132_){
_start:
{
lean_inc(v_off_1132_);
return v_off_1132_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg___boxed(lean_object* v_off_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_String_Slice_pos___redArg(v_off_1133_);
lean_dec(v_off_1133_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos(lean_object* v_s_1135_, lean_object* v_off_1136_, lean_object* v_h_1137_){
_start:
{
lean_inc(v_off_1136_);
return v_off_1136_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___boxed(lean_object* v_s_1138_, lean_object* v_off_1139_, lean_object* v_h_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_String_Slice_pos(v_s_1138_, v_off_1139_, v_h_1140_);
lean_dec(v_off_1139_);
lean_dec_ref(v_s_1138_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f(lean_object* v_s_1142_, lean_object* v_off_1143_){
_start:
{
uint8_t v___x_1144_; 
v___x_1144_ = l_String_Pos_Raw_isValidForSlice(v_s_1142_, v_off_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; 
lean_dec(v_off_1143_);
v___x_1145_ = lean_box(0);
return v___x_1145_;
}
else
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1146_, 0, v_off_1143_);
return v___x_1146_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f___boxed(lean_object* v_s_1147_, lean_object* v_off_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_String_Slice_pos_x3f(v_s_1147_, v_off_1148_);
lean_dec_ref(v_s_1147_);
return v_res_1149_;
}
}
static lean_object* _init_l_String_Slice_pos_x21___closed__2(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1152_ = ((lean_object*)(l_String_Slice_pos_x21___closed__1));
v___x_1153_ = lean_unsigned_to_nat(4u);
v___x_1154_ = lean_unsigned_to_nat(1606u);
v___x_1155_ = ((lean_object*)(l_String_Slice_pos_x21___closed__0));
v___x_1156_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1157_ = l_mkPanicMessageWithDecl(v___x_1156_, v___x_1155_, v___x_1154_, v___x_1153_, v___x_1152_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21(lean_object* v_s_1158_, lean_object* v_off_1159_){
_start:
{
uint8_t v___x_1160_; 
v___x_1160_ = l_String_Pos_Raw_isValidForSlice(v_s_1158_, v_off_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = lean_obj_once(&l_String_Slice_pos_x21___closed__2, &l_String_Slice_pos_x21___closed__2_once, _init_l_String_Slice_pos_x21___closed__2);
v___x_1162_ = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(v___x_1161_);
return v___x_1162_;
}
else
{
lean_inc(v_off_1159_);
return v_off_1159_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21___boxed(lean_object* v_s_1163_, lean_object* v_off_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_String_Slice_pos_x21(v_s_1163_, v_off_1164_);
lean_dec(v_off_1164_);
lean_dec_ref(v_s_1163_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next___boxed(lean_object* v_s_1169_, lean_object* v_pos_1170_, lean_object* v_h_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = lean_string_utf8_next_fast(v_s_1169_, v_pos_1170_);
lean_dec(v_pos_1170_);
lean_dec_ref(v_s_1169_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x3f(lean_object* v_s_1173_, lean_object* v_pos_1174_){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1175_ = lean_unsigned_to_nat(0u);
v___x_1176_ = lean_string_utf8_byte_size(v_s_1173_);
v___x_1177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1177_, 0, v_s_1173_);
lean_ctor_set(v___x_1177_, 1, v___x_1175_);
lean_ctor_set(v___x_1177_, 2, v___x_1176_);
v___x_1178_ = l_String_Slice_Pos_next_x3f(v___x_1177_, v_pos_1174_);
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
LEAN_EXPORT lean_object* l_String_Pos_next_x3f___boxed(lean_object* v_s_1188_, lean_object* v_pos_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_String_Pos_next_x3f(v_s_1188_, v_pos_1189_);
lean_dec(v_pos_1189_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21(lean_object* v_s_1191_, lean_object* v_pos_1192_){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1193_ = lean_unsigned_to_nat(0u);
v___x_1194_ = lean_string_utf8_byte_size(v_s_1191_);
v___x_1195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1195_, 0, v_s_1191_);
lean_ctor_set(v___x_1195_, 1, v___x_1193_);
lean_ctor_set(v___x_1195_, 2, v___x_1194_);
v___x_1196_ = l_String_Slice_Pos_next_x21(v___x_1195_, v_pos_1192_);
lean_dec_ref_known(v___x_1195_, 3);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_next_x21___boxed(lean_object* v_s_1197_, lean_object* v_pos_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_String_Pos_next_x21(v_s_1197_, v_pos_1198_);
lean_dec(v_pos_1198_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg(lean_object* v_off_1200_){
_start:
{
lean_inc(v_off_1200_);
return v_off_1200_;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg___boxed(lean_object* v_off_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_String_pos___redArg(v_off_1201_);
lean_dec(v_off_1201_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_String_pos(lean_object* v_s_1203_, lean_object* v_off_1204_, lean_object* v_h_1205_){
_start:
{
lean_inc(v_off_1204_);
return v_off_1204_;
}
}
LEAN_EXPORT lean_object* l_String_pos___boxed(lean_object* v_s_1206_, lean_object* v_off_1207_, lean_object* v_h_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_String_pos(v_s_1206_, v_off_1207_, v_h_1208_);
lean_dec(v_off_1207_);
lean_dec_ref(v_s_1206_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x3f(lean_object* v_s_1210_, lean_object* v_off_1211_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1212_ = lean_unsigned_to_nat(0u);
v___x_1213_ = lean_string_utf8_byte_size(v_s_1210_);
v___x_1214_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1214_, 0, v_s_1210_);
lean_ctor_set(v___x_1214_, 1, v___x_1212_);
lean_ctor_set(v___x_1214_, 2, v___x_1213_);
v___x_1215_ = l_String_Slice_pos_x3f(v___x_1214_, v_off_1211_);
lean_dec_ref_known(v___x_1214_, 3);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_box(0);
return v___x_1216_;
}
else
{
lean_object* v_val_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
v_val_1217_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1215_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_val_1217_);
lean_dec(v___x_1215_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_val_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_pos_x21(lean_object* v_s_1225_, lean_object* v_off_1226_){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1227_ = lean_unsigned_to_nat(0u);
v___x_1228_ = lean_string_utf8_byte_size(v_s_1225_);
v___x_1229_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1229_, 0, v_s_1225_);
lean_ctor_set(v___x_1229_, 1, v___x_1227_);
lean_ctor_set(v___x_1229_, 2, v___x_1228_);
v___x_1230_ = l_String_Slice_pos_x21(v___x_1229_, v_off_1226_);
lean_dec_ref_known(v___x_1229_, 3);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_String_pos_x21___boxed(lean_object* v_s_1231_, lean_object* v_off_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_String_pos_x21(v_s_1231_, v_off_1232_);
lean_dec(v_off_1232_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg(lean_object* v_pos_1234_){
_start:
{
lean_inc(v_pos_1234_);
return v_pos_1234_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg___boxed(lean_object* v_pos_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_String_Slice_Pos_cast___redArg(v_pos_1235_);
lean_dec(v_pos_1235_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast(lean_object* v_s_1237_, lean_object* v_t_1238_, lean_object* v_pos_1239_, lean_object* v_h_1240_){
_start:
{
lean_inc(v_pos_1239_);
return v_pos_1239_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___boxed(lean_object* v_s_1241_, lean_object* v_t_1242_, lean_object* v_pos_1243_, lean_object* v_h_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_String_Slice_Pos_cast(v_s_1241_, v_t_1242_, v_pos_1243_, v_h_1244_);
lean_dec(v_pos_1243_);
lean_dec_ref(v_t_1242_);
lean_dec_ref(v_s_1241_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg(lean_object* v_pos_1246_){
_start:
{
lean_inc(v_pos_1246_);
return v_pos_1246_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___redArg___boxed(lean_object* v_pos_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_String_Pos_cast___redArg(v_pos_1247_);
lean_dec(v_pos_1247_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast(lean_object* v_s_1249_, lean_object* v_t_1250_, lean_object* v_pos_1251_, lean_object* v_h_1252_){
_start:
{
lean_inc(v_pos_1251_);
return v_pos_1251_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_cast___boxed(lean_object* v_s_1253_, lean_object* v_t_1254_, lean_object* v_pos_1255_, lean_object* v_h_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_String_Pos_cast(v_s_1253_, v_t_1254_, v_pos_1255_, v_h_1256_);
lean_dec(v_pos_1255_);
lean_dec_ref(v_t_1254_);
lean_dec_ref(v_s_1253_);
return v_res_1257_;
}
}
LEAN_EXPORT uint32_t l_String_Pos_Raw_utf8GetAux(lean_object* v_x_1258_, lean_object* v_x_1259_, lean_object* v_x_1260_){
_start:
{
if (lean_obj_tag(v_x_1258_) == 0)
{
uint32_t v___x_1261_; 
lean_dec(v_x_1259_);
v___x_1261_ = 65;
return v___x_1261_;
}
else
{
lean_object* v_head_1262_; lean_object* v_tail_1263_; lean_object* v___y_1265_; uint8_t v_decide_1268_; 
v_head_1262_ = lean_ctor_get(v_x_1258_, 0);
v_tail_1263_ = lean_ctor_get(v_x_1258_, 1);
v_decide_1268_ = lean_nat_dec_eq(v_x_1259_, v_x_1260_);
if (v_decide_1268_ == 0)
{
uint32_t v___x_1269_; uint32_t v___x_1270_; uint8_t v___x_1271_; 
v___x_1269_ = 127;
v___x_1270_ = lean_unbox_uint32(v_head_1262_);
v___x_1271_ = lean_uint32_dec_le(v___x_1270_, v___x_1269_);
if (v___x_1271_ == 0)
{
uint32_t v___x_1272_; uint32_t v___x_1273_; uint8_t v___x_1274_; 
v___x_1272_ = 2047;
v___x_1273_ = lean_unbox_uint32(v_head_1262_);
v___x_1274_ = lean_uint32_dec_le(v___x_1273_, v___x_1272_);
if (v___x_1274_ == 0)
{
uint32_t v___x_1275_; uint32_t v___x_1276_; uint8_t v___x_1277_; 
v___x_1275_ = 65535;
v___x_1276_ = lean_unbox_uint32(v_head_1262_);
v___x_1277_ = lean_uint32_dec_le(v___x_1276_, v___x_1275_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; 
v___x_1278_ = lean_unsigned_to_nat(4u);
v___y_1265_ = v___x_1278_;
goto v___jp_1264_;
}
else
{
lean_object* v___x_1279_; 
v___x_1279_ = lean_unsigned_to_nat(3u);
v___y_1265_ = v___x_1279_;
goto v___jp_1264_;
}
}
else
{
lean_object* v___x_1280_; 
v___x_1280_ = lean_unsigned_to_nat(2u);
v___y_1265_ = v___x_1280_;
goto v___jp_1264_;
}
}
else
{
lean_object* v___x_1281_; 
v___x_1281_ = lean_unsigned_to_nat(1u);
v___y_1265_ = v___x_1281_;
goto v___jp_1264_;
}
}
else
{
uint32_t v___x_1282_; 
lean_dec(v_x_1259_);
v___x_1282_ = lean_unbox_uint32(v_head_1262_);
return v___x_1282_;
}
v___jp_1264_:
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_nat_add(v_x_1259_, v___y_1265_);
lean_dec(v_x_1259_);
v_x_1258_ = v_tail_1263_;
v_x_1259_ = v___x_1266_;
goto _start;
}
}
}
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
LEAN_EXPORT uint32_t l_String_utf8GetAux(lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
uint32_t v___x_1291_; 
v___x_1291_ = l_String_Pos_Raw_utf8GetAux(v_a_1288_, v_a_1289_, v_a_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux___boxed(lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
uint32_t v_res_1295_; lean_object* v_r_1296_; 
v_res_1295_ = l_String_utf8GetAux(v_a_1292_, v_a_1293_, v_a_1294_);
lean_dec(v_a_1294_);
lean_dec(v_a_1292_);
v_r_1296_ = lean_box_uint32(v_res_1295_);
return v_r_1296_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get___boxed(lean_object* v_s_1299_, lean_object* v_p_1300_){
_start:
{
uint32_t v_res_1301_; lean_object* v_r_1302_; 
v_res_1301_ = lean_string_utf8_get(v_s_1299_, v_p_1300_);
lean_dec(v_p_1300_);
lean_dec_ref(v_s_1299_);
v_r_1302_ = lean_box_uint32(v_res_1301_);
return v_r_1302_;
}
}
LEAN_EXPORT lean_object* l_String_get___boxed(lean_object* v_s_1305_, lean_object* v_p_1306_){
_start:
{
uint32_t v_res_1307_; lean_object* v_r_1308_; 
v_res_1307_ = lean_string_utf8_get(v_s_1305_, v_p_1306_);
lean_dec(v_p_1306_);
lean_dec_ref(v_s_1305_);
v_r_1308_ = lean_box_uint32(v_res_1307_);
return v_r_1308_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f(lean_object* v_x_1309_, lean_object* v_x_1310_, lean_object* v_x_1311_){
_start:
{
if (lean_obj_tag(v_x_1309_) == 0)
{
lean_object* v___x_1312_; 
lean_dec(v_x_1310_);
v___x_1312_ = lean_box(0);
return v___x_1312_;
}
else
{
lean_object* v_head_1313_; lean_object* v_tail_1314_; lean_object* v___y_1316_; uint8_t v_decide_1319_; 
v_head_1313_ = lean_ctor_get(v_x_1309_, 0);
v_tail_1314_ = lean_ctor_get(v_x_1309_, 1);
v_decide_1319_ = lean_nat_dec_eq(v_x_1310_, v_x_1311_);
if (v_decide_1319_ == 0)
{
uint32_t v___x_1320_; uint32_t v___x_1321_; uint8_t v___x_1322_; 
v___x_1320_ = 127;
v___x_1321_ = lean_unbox_uint32(v_head_1313_);
v___x_1322_ = lean_uint32_dec_le(v___x_1321_, v___x_1320_);
if (v___x_1322_ == 0)
{
uint32_t v___x_1323_; uint32_t v___x_1324_; uint8_t v___x_1325_; 
v___x_1323_ = 2047;
v___x_1324_ = lean_unbox_uint32(v_head_1313_);
v___x_1325_ = lean_uint32_dec_le(v___x_1324_, v___x_1323_);
if (v___x_1325_ == 0)
{
uint32_t v___x_1326_; uint32_t v___x_1327_; uint8_t v___x_1328_; 
v___x_1326_ = 65535;
v___x_1327_ = lean_unbox_uint32(v_head_1313_);
v___x_1328_ = lean_uint32_dec_le(v___x_1327_, v___x_1326_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; 
v___x_1329_ = lean_unsigned_to_nat(4u);
v___y_1316_ = v___x_1329_;
goto v___jp_1315_;
}
else
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_unsigned_to_nat(3u);
v___y_1316_ = v___x_1330_;
goto v___jp_1315_;
}
}
else
{
lean_object* v___x_1331_; 
v___x_1331_ = lean_unsigned_to_nat(2u);
v___y_1316_ = v___x_1331_;
goto v___jp_1315_;
}
}
else
{
lean_object* v___x_1332_; 
v___x_1332_ = lean_unsigned_to_nat(1u);
v___y_1316_ = v___x_1332_;
goto v___jp_1315_;
}
}
else
{
lean_object* v___x_1333_; 
lean_dec(v_x_1310_);
lean_inc(v_head_1313_);
v___x_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1333_, 0, v_head_1313_);
return v___x_1333_;
}
v___jp_1315_:
{
lean_object* v___x_1317_; 
v___x_1317_ = lean_nat_add(v_x_1310_, v___y_1316_);
lean_dec(v_x_1310_);
v_x_1309_ = v_tail_1314_;
v_x_1310_ = v___x_1317_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f___boxed(lean_object* v_x_1334_, lean_object* v_x_1335_, lean_object* v_x_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_String_Pos_Raw_utf8GetAux_x3f(v_x_1334_, v_x_1335_, v_x_1336_);
lean_dec(v_x_1336_);
lean_dec(v_x_1334_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f(lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_String_Pos_Raw_utf8GetAux_x3f(v_a_1338_, v_a_1339_, v_a_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f___boxed(lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_String_utf8GetAux_x3f(v_a_1342_, v_a_1343_, v_a_1344_);
lean_dec(v_a_1344_);
lean_dec(v_a_1342_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1348_, lean_object* v_a_00___x40___internal___hyg_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1348_, v_a_00___x40___internal___hyg_1349_);
lean_dec(v_a_00___x40___internal___hyg_1349_);
lean_dec_ref(v_a_00___x40___internal___hyg_1348_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_String_get_x3f___boxed(lean_object* v_a_00___x40___internal___hyg_1353_, lean_object* v_a_00___x40___internal___hyg_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = lean_string_utf8_get_opt(v_a_00___x40___internal___hyg_1353_, v_a_00___x40___internal___hyg_1354_);
lean_dec(v_a_00___x40___internal___hyg_1354_);
lean_dec_ref(v_a_00___x40___internal___hyg_1353_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x21___boxed(lean_object* v_s_1358_, lean_object* v_p_1359_){
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
LEAN_EXPORT lean_object* l_String_get_x21___boxed(lean_object* v_s_1364_, lean_object* v_p_1365_){
_start:
{
uint32_t v_res_1366_; lean_object* v_r_1367_; 
v_res_1366_ = lean_string_utf8_get_bang(v_s_1364_, v_p_1365_);
lean_dec(v_p_1365_);
lean_dec_ref(v_s_1364_);
v_r_1367_ = lean_box_uint32(v_res_1366_);
return v_r_1367_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux(uint32_t v_c_x27_1368_, lean_object* v_x_1369_, lean_object* v_x_1370_, lean_object* v_x_1371_){
_start:
{
if (lean_obj_tag(v_x_1369_) == 0)
{
return v_x_1369_;
}
else
{
lean_object* v_head_1372_; lean_object* v_tail_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1400_; 
v_head_1372_ = lean_ctor_get(v_x_1369_, 0);
v_tail_1373_ = lean_ctor_get(v_x_1369_, 1);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_x_1369_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1375_ = v_x_1369_;
v_isShared_1376_ = v_isSharedCheck_1400_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_tail_1373_);
lean_inc(v_head_1372_);
lean_dec(v_x_1369_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1400_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___y_1378_; uint8_t v_decide_1384_; 
v_decide_1384_ = lean_nat_dec_eq(v_x_1370_, v_x_1371_);
if (v_decide_1384_ == 0)
{
uint32_t v___x_1385_; uint32_t v___x_1386_; uint8_t v___x_1387_; 
v___x_1385_ = 127;
v___x_1386_ = lean_unbox_uint32(v_head_1372_);
v___x_1387_ = lean_uint32_dec_le(v___x_1386_, v___x_1385_);
if (v___x_1387_ == 0)
{
uint32_t v___x_1388_; uint32_t v___x_1389_; uint8_t v___x_1390_; 
v___x_1388_ = 2047;
v___x_1389_ = lean_unbox_uint32(v_head_1372_);
v___x_1390_ = lean_uint32_dec_le(v___x_1389_, v___x_1388_);
if (v___x_1390_ == 0)
{
uint32_t v___x_1391_; uint32_t v___x_1392_; uint8_t v___x_1393_; 
v___x_1391_ = 65535;
v___x_1392_ = lean_unbox_uint32(v_head_1372_);
v___x_1393_ = lean_uint32_dec_le(v___x_1392_, v___x_1391_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_unsigned_to_nat(4u);
v___y_1378_ = v___x_1394_;
goto v___jp_1377_;
}
else
{
lean_object* v___x_1395_; 
v___x_1395_ = lean_unsigned_to_nat(3u);
v___y_1378_ = v___x_1395_;
goto v___jp_1377_;
}
}
else
{
lean_object* v___x_1396_; 
v___x_1396_ = lean_unsigned_to_nat(2u);
v___y_1378_ = v___x_1396_;
goto v___jp_1377_;
}
}
else
{
lean_object* v___x_1397_; 
v___x_1397_ = lean_unsigned_to_nat(1u);
v___y_1378_ = v___x_1397_;
goto v___jp_1377_;
}
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_del_object(v___x_1375_);
lean_dec(v_head_1372_);
v___x_1398_ = lean_box_uint32(v_c_x27_1368_);
v___x_1399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
lean_ctor_set(v___x_1399_, 1, v_tail_1373_);
return v___x_1399_;
}
v___jp_1377_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1382_; 
v___x_1379_ = lean_nat_add(v_x_1370_, v___y_1378_);
v___x_1380_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1368_, v_tail_1373_, v___x_1379_, v_x_1371_);
lean_dec(v___x_1379_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 1, v___x_1380_);
v___x_1382_ = v___x_1375_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_head_1372_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux___boxed(lean_object* v_c_x27_1401_, lean_object* v_x_1402_, lean_object* v_x_1403_, lean_object* v_x_1404_){
_start:
{
uint32_t v_c_x27_boxed_1405_; lean_object* v_res_1406_; 
v_c_x27_boxed_1405_ = lean_unbox_uint32(v_c_x27_1401_);
lean_dec(v_c_x27_1401_);
v_res_1406_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_boxed_1405_, v_x_1402_, v_x_1403_, v_x_1404_);
lean_dec(v_x_1404_);
lean_dec(v_x_1403_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux(uint32_t v_c_x27_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_String_Pos_Raw_utf8SetAux(v_c_x27_1407_, v_a_1408_, v_a_1409_, v_a_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux___boxed(lean_object* v_c_x27_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_){
_start:
{
uint32_t v_c_x27_boxed_1416_; lean_object* v_res_1417_; 
v_c_x27_boxed_1416_ = lean_unbox_uint32(v_c_x27_1412_);
lean_dec(v_c_x27_1412_);
v_res_1417_ = l_String_utf8SetAux(v_c_x27_boxed_1416_, v_a_1413_, v_a_1414_, v_a_1415_);
lean_dec(v_a_1415_);
lean_dec(v_a_1414_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg(lean_object* v_s_1418_, lean_object* v_pos_1419_){
_start:
{
lean_object* v_str_1420_; lean_object* v_startInclusive_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v_str_1420_ = lean_ctor_get(v_s_1418_, 0);
v_startInclusive_1421_ = lean_ctor_get(v_s_1418_, 1);
v___x_1422_ = lean_nat_add(v_startInclusive_1421_, v_pos_1419_);
v___x_1423_ = lean_string_utf8_next_fast(v_str_1420_, v___x_1422_);
lean_dec(v___x_1422_);
v___x_1424_ = lean_nat_sub(v___x_1423_, v_startInclusive_1421_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___redArg___boxed(lean_object* v_s_1425_, lean_object* v_pos_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_String_Slice_Pos_nextFast___redArg(v_s_1425_, v_pos_1426_);
lean_dec(v_pos_1426_);
lean_dec_ref(v_s_1425_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast(lean_object* v_s_1428_, lean_object* v_pos_1429_, lean_object* v_h_1430_){
_start:
{
lean_object* v_str_1431_; lean_object* v_startInclusive_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v_str_1431_ = lean_ctor_get(v_s_1428_, 0);
v_startInclusive_1432_ = lean_ctor_get(v_s_1428_, 1);
v___x_1433_ = lean_nat_add(v_startInclusive_1432_, v_pos_1429_);
v___x_1434_ = lean_string_utf8_next_fast(v_str_1431_, v___x_1433_);
lean_dec(v___x_1433_);
v___x_1435_ = lean_nat_sub(v___x_1434_, v_startInclusive_1432_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextFast___boxed(lean_object* v_s_1436_, lean_object* v_pos_1437_, lean_object* v_h_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_String_Slice_Pos_nextFast(v_s_1436_, v_pos_1437_, v_h_1438_);
lean_dec(v_pos_1437_);
lean_dec_ref(v_s_1436_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_String_sliceTo(lean_object* v_s_1440_, lean_object* v_p_1441_){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1442_ = lean_unsigned_to_nat(0u);
v___x_1443_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1443_, 0, v_s_1440_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
lean_ctor_set(v___x_1443_, 2, v_p_1441_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_String_replaceEnd(lean_object* v_s_1444_, lean_object* v_p_1445_){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = lean_unsigned_to_nat(0u);
v___x_1447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1447_, 0, v_s_1444_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
lean_ctor_set(v___x_1447_, 2, v_p_1445_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_String_sliceFrom(lean_object* v_s_1448_, lean_object* v_p_1449_){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = lean_string_utf8_byte_size(v_s_1448_);
v___x_1451_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1451_, 0, v_s_1448_);
lean_ctor_set(v___x_1451_, 1, v_p_1449_);
lean_ctor_set(v___x_1451_, 2, v___x_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStart(lean_object* v_s_1452_, lean_object* v_p_1453_){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_string_utf8_byte_size(v_s_1452_);
v___x_1455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1455_, 0, v_s_1452_);
lean_ctor_set(v___x_1455_, 1, v_p_1453_);
lean_ctor_set(v___x_1455_, 2, v___x_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_String_slice___redArg(lean_object* v_s_1456_, lean_object* v_startInclusive_1457_, lean_object* v_endExclusive_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1459_, 0, v_s_1456_);
lean_ctor_set(v___x_1459_, 1, v_startInclusive_1457_);
lean_ctor_set(v___x_1459_, 2, v_endExclusive_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_String_slice(lean_object* v_s_1460_, lean_object* v_startInclusive_1461_, lean_object* v_endExclusive_1462_, lean_object* v_h_1463_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1464_, 0, v_s_1460_);
lean_ctor_set(v___x_1464_, 1, v_startInclusive_1461_);
lean_ctor_set(v___x_1464_, 2, v_endExclusive_1462_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x3f(lean_object* v_s_1465_, lean_object* v_startInclusive_1466_, lean_object* v_endExclusive_1467_){
_start:
{
uint8_t v___x_1468_; 
v___x_1468_ = lean_nat_dec_le(v_startInclusive_1466_, v_endExclusive_1467_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; 
lean_dec(v_endExclusive_1467_);
lean_dec(v_startInclusive_1466_);
lean_dec_ref(v_s_1465_);
v___x_1469_ = lean_box(0);
return v___x_1469_;
}
else
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1470_, 0, v_s_1465_);
lean_ctor_set(v___x_1470_, 1, v_startInclusive_1466_);
lean_ctor_set(v___x_1470_, 2, v_endExclusive_1467_);
v___x_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
return v___x_1471_;
}
}
}
LEAN_EXPORT lean_object* l_String_slice_x21(lean_object* v_s_1472_, lean_object* v_p_u2081_1473_, lean_object* v_p_u2082_1474_){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1475_ = lean_unsigned_to_nat(0u);
v___x_1476_ = lean_string_utf8_byte_size(v_s_1472_);
v___x_1477_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1477_, 0, v_s_1472_);
lean_ctor_set(v___x_1477_, 1, v___x_1475_);
lean_ctor_set(v___x_1477_, 2, v___x_1476_);
v___x_1478_ = l_String_Slice_slice_x21(v___x_1477_, v_p_u2081_1473_, v_p_u2082_1474_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_String_slice_x21___boxed(lean_object* v_s_1479_, lean_object* v_p_u2081_1480_, lean_object* v_p_u2082_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_String_slice_x21(v_s_1479_, v_p_u2081_1480_, v_p_u2082_1481_);
lean_dec(v_p_u2082_1481_);
lean_dec(v_p_u2081_1480_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21(lean_object* v_s_1483_, lean_object* v_p_u2081_1484_, lean_object* v_p_u2082_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_String_slice_x21(v_s_1483_, v_p_u2081_1484_, v_p_u2082_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_String_replaceStartEnd_x21___boxed(lean_object* v_s_1487_, lean_object* v_p_u2081_1488_, lean_object* v_p_u2082_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_String_replaceStartEnd_x21(v_s_1487_, v_p_u2081_1488_, v_p_u2082_1489_);
lean_dec(v_p_u2082_1489_);
lean_dec(v_p_u2081_1488_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg(lean_object* v_p_u2080_1491_, lean_object* v_pos_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_nat_add(v_p_u2080_1491_, v_pos_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___redArg___boxed(lean_object* v_p_u2080_1494_, lean_object* v_pos_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_String_Pos_ofSliceFrom___redArg(v_p_u2080_1494_, v_pos_1495_);
lean_dec(v_pos_1495_);
lean_dec(v_p_u2080_1494_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom(lean_object* v_s_1497_, lean_object* v_p_u2080_1498_, lean_object* v_pos_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_nat_add(v_p_u2080_1498_, v_pos_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceFrom___boxed(lean_object* v_s_1501_, lean_object* v_p_u2080_1502_, lean_object* v_pos_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_String_Pos_ofSliceFrom(v_s_1501_, v_p_u2080_1502_, v_pos_1503_);
lean_dec(v_pos_1503_);
lean_dec(v_p_u2080_1502_);
lean_dec_ref(v_s_1501_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg(lean_object* v_p_u2080_1505_, lean_object* v_pos_1506_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_nat_add(v_p_u2080_1505_, v_pos_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___redArg___boxed(lean_object* v_p_u2080_1508_, lean_object* v_pos_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_String_Pos_ofReplaceStart___redArg(v_p_u2080_1508_, v_pos_1509_);
lean_dec(v_pos_1509_);
lean_dec(v_p_u2080_1508_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart(lean_object* v_s_1511_, lean_object* v_p_u2080_1512_, lean_object* v_pos_1513_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_nat_add(v_p_u2080_1512_, v_pos_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceStart___boxed(lean_object* v_s_1515_, lean_object* v_p_u2080_1516_, lean_object* v_pos_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_String_Pos_ofReplaceStart(v_s_1515_, v_p_u2080_1516_, v_pos_1517_);
lean_dec(v_pos_1517_);
lean_dec(v_p_u2080_1516_);
lean_dec_ref(v_s_1515_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg(lean_object* v_p_u2080_1519_, lean_object* v_pos_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_nat_sub(v_pos_1520_, v_p_u2080_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___redArg___boxed(lean_object* v_p_u2080_1522_, lean_object* v_pos_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_String_Pos_sliceFrom___redArg(v_p_u2080_1522_, v_pos_1523_);
lean_dec(v_pos_1523_);
lean_dec(v_p_u2080_1522_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom(lean_object* v_s_1525_, lean_object* v_p_u2080_1526_, lean_object* v_pos_1527_, lean_object* v_h_1528_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_nat_sub(v_pos_1527_, v_p_u2080_1526_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceFrom___boxed(lean_object* v_s_1530_, lean_object* v_p_u2080_1531_, lean_object* v_pos_1532_, lean_object* v_h_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_String_Pos_sliceFrom(v_s_1530_, v_p_u2080_1531_, v_pos_1532_, v_h_1533_);
lean_dec(v_pos_1532_);
lean_dec(v_p_u2080_1531_);
lean_dec_ref(v_s_1530_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg(lean_object* v_p_u2080_1535_, lean_object* v_pos_1536_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_nat_sub(v_pos_1536_, v_p_u2080_1535_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___redArg___boxed(lean_object* v_p_u2080_1538_, lean_object* v_pos_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_String_Pos_toReplaceStart___redArg(v_p_u2080_1538_, v_pos_1539_);
lean_dec(v_pos_1539_);
lean_dec(v_p_u2080_1538_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart(lean_object* v_s_1541_, lean_object* v_p_u2080_1542_, lean_object* v_pos_1543_, lean_object* v_h_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = lean_nat_sub(v_pos_1543_, v_p_u2080_1542_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceStart___boxed(lean_object* v_s_1546_, lean_object* v_p_u2080_1547_, lean_object* v_pos_1548_, lean_object* v_h_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_String_Pos_toReplaceStart(v_s_1546_, v_p_u2080_1547_, v_pos_1548_, v_h_1549_);
lean_dec(v_pos_1548_);
lean_dec(v_p_u2080_1547_);
lean_dec_ref(v_s_1546_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg(lean_object* v_pos_1551_){
_start:
{
lean_inc(v_pos_1551_);
return v_pos_1551_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___redArg___boxed(lean_object* v_pos_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_String_Pos_ofSliceTo___redArg(v_pos_1552_);
lean_dec(v_pos_1552_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo(lean_object* v_s_1554_, lean_object* v_p_u2080_1555_, lean_object* v_pos_1556_){
_start:
{
lean_inc(v_pos_1556_);
return v_pos_1556_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSliceTo___boxed(lean_object* v_s_1557_, lean_object* v_p_u2080_1558_, lean_object* v_pos_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_String_Pos_ofSliceTo(v_s_1557_, v_p_u2080_1558_, v_pos_1559_);
lean_dec(v_pos_1559_);
lean_dec(v_p_u2080_1558_);
lean_dec_ref(v_s_1557_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg(lean_object* v_pos_1561_){
_start:
{
lean_inc(v_pos_1561_);
return v_pos_1561_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___redArg___boxed(lean_object* v_pos_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_String_Pos_ofReplaceEnd___redArg(v_pos_1562_);
lean_dec(v_pos_1562_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd(lean_object* v_s_1564_, lean_object* v_p_u2080_1565_, lean_object* v_pos_1566_){
_start:
{
lean_inc(v_pos_1566_);
return v_pos_1566_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofReplaceEnd___boxed(lean_object* v_s_1567_, lean_object* v_p_u2080_1568_, lean_object* v_pos_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_String_Pos_ofReplaceEnd(v_s_1567_, v_p_u2080_1568_, v_pos_1569_);
lean_dec(v_pos_1569_);
lean_dec(v_p_u2080_1568_);
lean_dec_ref(v_s_1567_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg(lean_object* v_pos_1571_){
_start:
{
lean_inc(v_pos_1571_);
return v_pos_1571_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___redArg___boxed(lean_object* v_pos_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_String_Pos_sliceTo___redArg(v_pos_1572_);
lean_dec(v_pos_1572_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo(lean_object* v_s_1574_, lean_object* v_p_u2080_1575_, lean_object* v_pos_1576_, lean_object* v_h_1577_){
_start:
{
lean_inc(v_pos_1576_);
return v_pos_1576_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceTo___boxed(lean_object* v_s_1578_, lean_object* v_p_u2080_1579_, lean_object* v_pos_1580_, lean_object* v_h_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_String_Pos_sliceTo(v_s_1578_, v_p_u2080_1579_, v_pos_1580_, v_h_1581_);
lean_dec(v_pos_1580_);
lean_dec(v_p_u2080_1579_);
lean_dec_ref(v_s_1578_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg(lean_object* v_pos_1583_){
_start:
{
lean_inc(v_pos_1583_);
return v_pos_1583_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___redArg___boxed(lean_object* v_pos_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_String_Pos_toReplaceEnd___redArg(v_pos_1584_);
lean_dec(v_pos_1584_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd(lean_object* v_s_1586_, lean_object* v_p_u2080_1587_, lean_object* v_pos_1588_, lean_object* v_h_1589_){
_start:
{
lean_inc(v_pos_1588_);
return v_pos_1588_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toReplaceEnd___boxed(lean_object* v_s_1590_, lean_object* v_p_u2080_1591_, lean_object* v_pos_1592_, lean_object* v_h_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_String_Pos_toReplaceEnd(v_s_1590_, v_p_u2080_1591_, v_pos_1592_, v_h_1593_);
lean_dec(v_pos_1592_);
lean_dec(v_p_u2080_1591_);
lean_dec_ref(v_s_1590_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg(lean_object* v_p_u2080_1595_, lean_object* v_pos_1596_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = lean_nat_add(v_p_u2080_1595_, v_pos_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1598_, lean_object* v_pos_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_String_Slice_Pos_ofSlice___redArg(v_p_u2080_1598_, v_pos_1599_);
lean_dec(v_pos_1599_);
lean_dec(v_p_u2080_1598_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice(lean_object* v_s_1601_, lean_object* v_p_u2080_1602_, lean_object* v_p_u2081_1603_, lean_object* v_h_1604_, lean_object* v_pos_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = lean_nat_add(v_p_u2080_1602_, v_pos_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___boxed(lean_object* v_s_1607_, lean_object* v_p_u2080_1608_, lean_object* v_p_u2081_1609_, lean_object* v_h_1610_, lean_object* v_pos_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_String_Slice_Pos_ofSlice(v_s_1607_, v_p_u2080_1608_, v_p_u2081_1609_, v_h_1610_, v_pos_1611_);
lean_dec(v_pos_1611_);
lean_dec(v_p_u2081_1609_);
lean_dec(v_p_u2080_1608_);
lean_dec_ref(v_s_1607_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg(lean_object* v_p_u2080_1613_, lean_object* v_pos_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = lean_nat_add(v_p_u2080_1613_, v_pos_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___redArg___boxed(lean_object* v_p_u2080_1616_, lean_object* v_pos_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_String_Pos_ofSlice___redArg(v_p_u2080_1616_, v_pos_1617_);
lean_dec(v_pos_1617_);
lean_dec(v_p_u2080_1616_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice(lean_object* v_s_1619_, lean_object* v_p_u2080_1620_, lean_object* v_p_u2081_1621_, lean_object* v_h_1622_, lean_object* v_pos_1623_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = lean_nat_add(v_p_u2080_1620_, v_pos_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice___boxed(lean_object* v_s_1625_, lean_object* v_p_u2080_1626_, lean_object* v_p_u2081_1627_, lean_object* v_h_1628_, lean_object* v_pos_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_String_Pos_ofSlice(v_s_1625_, v_p_u2080_1626_, v_p_u2081_1627_, v_h_1628_, v_pos_1629_);
lean_dec(v_pos_1629_);
lean_dec(v_p_u2081_1627_);
lean_dec(v_p_u2080_1626_);
lean_dec_ref(v_s_1625_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg(lean_object* v_pos_1631_, lean_object* v_p_u2080_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = lean_nat_sub(v_pos_1631_, v_p_u2080_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___redArg___boxed(lean_object* v_pos_1634_, lean_object* v_p_u2080_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_String_Slice_Pos_slice___redArg(v_pos_1634_, v_p_u2080_1635_);
lean_dec(v_p_u2080_1635_);
lean_dec(v_pos_1634_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice(lean_object* v_s_1637_, lean_object* v_pos_1638_, lean_object* v_p_u2080_1639_, lean_object* v_p_u2081_1640_, lean_object* v_h_u2081_1641_, lean_object* v_h_u2082_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = lean_nat_sub(v_pos_1638_, v_p_u2080_1639_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice___boxed(lean_object* v_s_1644_, lean_object* v_pos_1645_, lean_object* v_p_u2080_1646_, lean_object* v_p_u2081_1647_, lean_object* v_h_u2081_1648_, lean_object* v_h_u2082_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_String_Slice_Pos_slice(v_s_1644_, v_pos_1645_, v_p_u2080_1646_, v_p_u2081_1647_, v_h_u2081_1648_, v_h_u2082_1649_);
lean_dec(v_p_u2081_1647_);
lean_dec(v_p_u2080_1646_);
lean_dec(v_pos_1645_);
lean_dec_ref(v_s_1644_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg(lean_object* v_pos_1651_, lean_object* v_p_u2080_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_nat_sub(v_pos_1651_, v_p_u2080_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___redArg___boxed(lean_object* v_pos_1654_, lean_object* v_p_u2080_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_String_Pos_slice___redArg(v_pos_1654_, v_p_u2080_1655_);
lean_dec(v_p_u2080_1655_);
lean_dec(v_pos_1654_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice(lean_object* v_s_1657_, lean_object* v_pos_1658_, lean_object* v_p_u2080_1659_, lean_object* v_p_u2081_1660_, lean_object* v_h_u2081_1661_, lean_object* v_h_u2082_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_nat_sub(v_pos_1658_, v_p_u2080_1659_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice___boxed(lean_object* v_s_1664_, lean_object* v_pos_1665_, lean_object* v_p_u2080_1666_, lean_object* v_p_u2081_1667_, lean_object* v_h_u2081_1668_, lean_object* v_h_u2082_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_String_Pos_slice(v_s_1664_, v_pos_1665_, v_p_u2080_1666_, v_p_u2081_1667_, v_h_u2081_1668_, v_h_u2082_1669_);
lean_dec(v_p_u2081_1667_);
lean_dec(v_p_u2080_1666_);
lean_dec(v_pos_1665_);
lean_dec_ref(v_s_1664_);
return v_res_1670_;
}
}
static lean_object* _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2(void){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1673_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__1));
v___x_1674_ = lean_unsigned_to_nat(4u);
v___x_1675_ = lean_unsigned_to_nat(2621u);
v___x_1676_ = ((lean_object*)(l_String_Slice_Pos_sliceOrPanic___redArg___closed__0));
v___x_1677_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1678_ = l_mkPanicMessageWithDecl(v___x_1677_, v___x_1676_, v___x_1675_, v___x_1674_, v___x_1673_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg(lean_object* v_pos_1679_, lean_object* v_p_u2080_1680_, lean_object* v_p_u2081_1681_){
_start:
{
uint8_t v___y_1683_; uint8_t v___x_1688_; 
v___x_1688_ = lean_nat_dec_le(v_p_u2080_1680_, v_pos_1679_);
if (v___x_1688_ == 0)
{
v___y_1683_ = v___x_1688_;
goto v___jp_1682_;
}
else
{
uint8_t v___x_1689_; 
v___x_1689_ = lean_nat_dec_le(v_pos_1679_, v_p_u2081_1681_);
v___y_1683_ = v___x_1689_;
goto v___jp_1682_;
}
v___jp_1682_:
{
if (v___y_1683_ == 0)
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1684_ = lean_unsigned_to_nat(0u);
v___x_1685_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1686_ = l_panic___redArg(v___x_1684_, v___x_1685_);
return v___x_1686_;
}
else
{
lean_object* v___x_1687_; 
v___x_1687_ = lean_nat_sub(v_pos_1679_, v_p_u2080_1680_);
return v___x_1687_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1690_, lean_object* v_p_u2080_1691_, lean_object* v_p_u2081_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_String_Slice_Pos_sliceOrPanic___redArg(v_pos_1690_, v_p_u2080_1691_, v_p_u2081_1692_);
lean_dec(v_p_u2081_1692_);
lean_dec(v_p_u2080_1691_);
lean_dec(v_pos_1690_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic(lean_object* v_s_1694_, lean_object* v_pos_1695_, lean_object* v_p_u2080_1696_, lean_object* v_p_u2081_1697_, lean_object* v_h_1698_){
_start:
{
uint8_t v___y_1700_; uint8_t v___x_1705_; 
v___x_1705_ = lean_nat_dec_le(v_p_u2080_1696_, v_pos_1695_);
if (v___x_1705_ == 0)
{
v___y_1700_ = v___x_1705_;
goto v___jp_1699_;
}
else
{
uint8_t v___x_1706_; 
v___x_1706_ = lean_nat_dec_le(v_pos_1695_, v_p_u2081_1697_);
v___y_1700_ = v___x_1706_;
goto v___jp_1699_;
}
v___jp_1699_:
{
if (v___y_1700_ == 0)
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1701_ = lean_unsigned_to_nat(0u);
v___x_1702_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1703_ = l_panic___redArg(v___x_1701_, v___x_1702_);
return v___x_1703_;
}
else
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_nat_sub(v_pos_1695_, v_p_u2080_1696_);
return v___x_1704_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_sliceOrPanic___boxed(lean_object* v_s_1707_, lean_object* v_pos_1708_, lean_object* v_p_u2080_1709_, lean_object* v_p_u2081_1710_, lean_object* v_h_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_String_Slice_Pos_sliceOrPanic(v_s_1707_, v_pos_1708_, v_p_u2080_1709_, v_p_u2081_1710_, v_h_1711_);
lean_dec(v_p_u2081_1710_);
lean_dec(v_p_u2080_1709_);
lean_dec(v_pos_1708_);
lean_dec_ref(v_s_1707_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg(lean_object* v_pos_1713_, lean_object* v_p_u2080_1714_, lean_object* v_p_u2081_1715_){
_start:
{
uint8_t v___y_1717_; uint8_t v___x_1722_; 
v___x_1722_ = lean_nat_dec_le(v_p_u2080_1714_, v_pos_1713_);
if (v___x_1722_ == 0)
{
v___y_1717_ = v___x_1722_;
goto v___jp_1716_;
}
else
{
uint8_t v___x_1723_; 
v___x_1723_ = lean_nat_dec_le(v_pos_1713_, v_p_u2081_1715_);
v___y_1717_ = v___x_1723_;
goto v___jp_1716_;
}
v___jp_1716_:
{
if (v___y_1717_ == 0)
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1718_ = lean_unsigned_to_nat(0u);
v___x_1719_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1720_ = l_panic___redArg(v___x_1718_, v___x_1719_);
return v___x_1720_;
}
else
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_nat_sub(v_pos_1713_, v_p_u2080_1714_);
return v___x_1721_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___redArg___boxed(lean_object* v_pos_1724_, lean_object* v_p_u2080_1725_, lean_object* v_p_u2081_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_String_Pos_sliceOrPanic___redArg(v_pos_1724_, v_p_u2080_1725_, v_p_u2081_1726_);
lean_dec(v_p_u2081_1726_);
lean_dec(v_p_u2080_1725_);
lean_dec(v_pos_1724_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic(lean_object* v_s_1728_, lean_object* v_pos_1729_, lean_object* v_p_u2080_1730_, lean_object* v_p_u2081_1731_, lean_object* v_h_1732_){
_start:
{
uint8_t v___y_1734_; uint8_t v___x_1739_; 
v___x_1739_ = lean_nat_dec_le(v_p_u2080_1730_, v_pos_1729_);
if (v___x_1739_ == 0)
{
v___y_1734_ = v___x_1739_;
goto v___jp_1733_;
}
else
{
uint8_t v___x_1740_; 
v___x_1740_ = lean_nat_dec_le(v_pos_1729_, v_p_u2081_1731_);
v___y_1734_ = v___x_1740_;
goto v___jp_1733_;
}
v___jp_1733_:
{
if (v___y_1734_ == 0)
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1735_ = lean_unsigned_to_nat(0u);
v___x_1736_ = lean_obj_once(&l_String_Slice_Pos_sliceOrPanic___redArg___closed__2, &l_String_Slice_Pos_sliceOrPanic___redArg___closed__2_once, _init_l_String_Slice_Pos_sliceOrPanic___redArg___closed__2);
v___x_1737_ = l_panic___redArg(v___x_1735_, v___x_1736_);
return v___x_1737_;
}
else
{
lean_object* v___x_1738_; 
v___x_1738_ = lean_nat_sub(v_pos_1729_, v_p_u2080_1730_);
return v___x_1738_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_sliceOrPanic___boxed(lean_object* v_s_1741_, lean_object* v_pos_1742_, lean_object* v_p_u2080_1743_, lean_object* v_p_u2081_1744_, lean_object* v_h_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_String_Pos_sliceOrPanic(v_s_1741_, v_pos_1742_, v_p_u2080_1743_, v_p_u2081_1744_, v_h_1745_);
lean_dec(v_p_u2081_1744_);
lean_dec(v_p_u2080_1743_);
lean_dec(v_pos_1742_);
lean_dec_ref(v_s_1741_);
return v_res_1746_;
}
}
static lean_object* _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1748_ = ((lean_object*)(l_String_Slice_slice_x21___closed__1));
v___x_1749_ = lean_unsigned_to_nat(4u);
v___x_1750_ = lean_unsigned_to_nat(2645u);
v___x_1751_ = ((lean_object*)(l_String_Slice_Pos_ofSlice_x21___redArg___closed__0));
v___x_1752_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1753_ = l_mkPanicMessageWithDecl(v___x_1752_, v___x_1751_, v___x_1750_, v___x_1749_, v___x_1748_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1754_, lean_object* v_p_u2081_1755_, lean_object* v_pos_1756_){
_start:
{
uint8_t v___x_1757_; 
v___x_1757_ = lean_nat_dec_le(v_p_u2080_1754_, v_p_u2081_1755_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1758_ = lean_unsigned_to_nat(0u);
v___x_1759_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1760_ = l_panic___redArg(v___x_1758_, v___x_1759_);
return v___x_1760_;
}
else
{
lean_object* v___x_1761_; 
v___x_1761_ = lean_nat_add(v_p_u2080_1754_, v_pos_1756_);
return v___x_1761_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1762_, lean_object* v_p_u2081_1763_, lean_object* v_pos_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_String_Slice_Pos_ofSlice_x21___redArg(v_p_u2080_1762_, v_p_u2081_1763_, v_pos_1764_);
lean_dec(v_pos_1764_);
lean_dec(v_p_u2081_1763_);
lean_dec(v_p_u2080_1762_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21(lean_object* v_s_1766_, lean_object* v_p_u2080_1767_, lean_object* v_p_u2081_1768_, lean_object* v_pos_1769_){
_start:
{
uint8_t v___x_1770_; 
v___x_1770_ = lean_nat_dec_le(v_p_u2080_1767_, v_p_u2081_1768_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1771_ = lean_unsigned_to_nat(0u);
v___x_1772_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1773_ = l_panic___redArg(v___x_1771_, v___x_1772_);
return v___x_1773_;
}
else
{
lean_object* v___x_1774_; 
v___x_1774_ = lean_nat_add(v_p_u2080_1767_, v_pos_1769_);
return v___x_1774_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice_x21___boxed(lean_object* v_s_1775_, lean_object* v_p_u2080_1776_, lean_object* v_p_u2081_1777_, lean_object* v_pos_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_String_Slice_Pos_ofSlice_x21(v_s_1775_, v_p_u2080_1776_, v_p_u2081_1777_, v_pos_1778_);
lean_dec(v_pos_1778_);
lean_dec(v_p_u2081_1777_);
lean_dec(v_p_u2080_1776_);
lean_dec_ref(v_s_1775_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg(lean_object* v_p_u2080_1780_, lean_object* v_p_u2081_1781_, lean_object* v_pos_1782_){
_start:
{
uint8_t v___x_1783_; 
v___x_1783_ = lean_nat_dec_le(v_p_u2080_1780_, v_p_u2081_1781_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1784_ = lean_unsigned_to_nat(0u);
v___x_1785_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1786_ = l_panic___redArg(v___x_1784_, v___x_1785_);
return v___x_1786_;
}
else
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_nat_add(v_p_u2080_1780_, v_pos_1782_);
return v___x_1787_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___redArg___boxed(lean_object* v_p_u2080_1788_, lean_object* v_p_u2081_1789_, lean_object* v_pos_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_String_Pos_ofSlice_x21___redArg(v_p_u2080_1788_, v_p_u2081_1789_, v_pos_1790_);
lean_dec(v_pos_1790_);
lean_dec(v_p_u2081_1789_);
lean_dec(v_p_u2080_1788_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21(lean_object* v_s_1792_, lean_object* v_p_u2080_1793_, lean_object* v_p_u2081_1794_, lean_object* v_pos_1795_){
_start:
{
uint8_t v___x_1796_; 
v___x_1796_ = lean_nat_dec_le(v_p_u2080_1793_, v_p_u2081_1794_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = lean_unsigned_to_nat(0u);
v___x_1798_ = lean_obj_once(&l_String_Slice_Pos_ofSlice_x21___redArg___closed__1, &l_String_Slice_Pos_ofSlice_x21___redArg___closed__1_once, _init_l_String_Slice_Pos_ofSlice_x21___redArg___closed__1);
v___x_1799_ = l_panic___redArg(v___x_1797_, v___x_1798_);
return v___x_1799_;
}
else
{
lean_object* v___x_1800_; 
v___x_1800_ = lean_nat_add(v_p_u2080_1793_, v_pos_1795_);
return v___x_1800_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofSlice_x21___boxed(lean_object* v_s_1801_, lean_object* v_p_u2080_1802_, lean_object* v_p_u2081_1803_, lean_object* v_pos_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_String_Pos_ofSlice_x21(v_s_1801_, v_p_u2080_1802_, v_p_u2081_1803_, v_pos_1804_);
lean_dec(v_pos_1804_);
lean_dec(v_p_u2081_1803_);
lean_dec(v_p_u2080_1802_);
lean_dec_ref(v_s_1801_);
return v_res_1805_;
}
}
static lean_object* _init_l_String_Slice_Pos_slice_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1808_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__1));
v___x_1809_ = lean_unsigned_to_nat(4u);
v___x_1810_ = lean_unsigned_to_nat(2663u);
v___x_1811_ = ((lean_object*)(l_String_Slice_Pos_slice_x21___redArg___closed__0));
v___x_1812_ = ((lean_object*)(l_String_fromUTF8_x21___closed__1));
v___x_1813_ = l_mkPanicMessageWithDecl(v___x_1812_, v___x_1811_, v___x_1810_, v___x_1809_, v___x_1808_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg(lean_object* v_pos_1814_, lean_object* v_p_u2080_1815_, lean_object* v_p_u2081_1816_){
_start:
{
uint8_t v___y_1818_; uint8_t v___x_1823_; 
v___x_1823_ = lean_nat_dec_le(v_p_u2080_1815_, v_pos_1814_);
if (v___x_1823_ == 0)
{
v___y_1818_ = v___x_1823_;
goto v___jp_1817_;
}
else
{
uint8_t v___x_1824_; 
v___x_1824_ = lean_nat_dec_le(v_pos_1814_, v_p_u2081_1816_);
v___y_1818_ = v___x_1824_;
goto v___jp_1817_;
}
v___jp_1817_:
{
if (v___y_1818_ == 0)
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1819_ = lean_unsigned_to_nat(0u);
v___x_1820_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1821_ = l_panic___redArg(v___x_1819_, v___x_1820_);
return v___x_1821_;
}
else
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_nat_sub(v_pos_1814_, v_p_u2080_1815_);
return v___x_1822_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1825_, lean_object* v_p_u2080_1826_, lean_object* v_p_u2081_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_String_Slice_Pos_slice_x21___redArg(v_pos_1825_, v_p_u2080_1826_, v_p_u2081_1827_);
lean_dec(v_p_u2081_1827_);
lean_dec(v_p_u2080_1826_);
lean_dec(v_pos_1825_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21(lean_object* v_s_1829_, lean_object* v_pos_1830_, lean_object* v_p_u2080_1831_, lean_object* v_p_u2081_1832_){
_start:
{
uint8_t v___y_1834_; uint8_t v___x_1839_; 
v___x_1839_ = lean_nat_dec_le(v_p_u2080_1831_, v_pos_1830_);
if (v___x_1839_ == 0)
{
v___y_1834_ = v___x_1839_;
goto v___jp_1833_;
}
else
{
uint8_t v___x_1840_; 
v___x_1840_ = lean_nat_dec_le(v_pos_1830_, v_p_u2081_1832_);
v___y_1834_ = v___x_1840_;
goto v___jp_1833_;
}
v___jp_1833_:
{
if (v___y_1834_ == 0)
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = lean_unsigned_to_nat(0u);
v___x_1836_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1837_ = l_panic___redArg(v___x_1835_, v___x_1836_);
return v___x_1837_;
}
else
{
lean_object* v___x_1838_; 
v___x_1838_ = lean_nat_sub(v_pos_1830_, v_p_u2080_1831_);
return v___x_1838_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_slice_x21___boxed(lean_object* v_s_1841_, lean_object* v_pos_1842_, lean_object* v_p_u2080_1843_, lean_object* v_p_u2081_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_String_Slice_Pos_slice_x21(v_s_1841_, v_pos_1842_, v_p_u2080_1843_, v_p_u2081_1844_);
lean_dec(v_p_u2081_1844_);
lean_dec(v_p_u2080_1843_);
lean_dec(v_pos_1842_);
lean_dec_ref(v_s_1841_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg(lean_object* v_pos_1846_, lean_object* v_p_u2080_1847_, lean_object* v_p_u2081_1848_){
_start:
{
uint8_t v___y_1850_; uint8_t v___x_1855_; 
v___x_1855_ = lean_nat_dec_le(v_p_u2080_1847_, v_pos_1846_);
if (v___x_1855_ == 0)
{
v___y_1850_ = v___x_1855_;
goto v___jp_1849_;
}
else
{
uint8_t v___x_1856_; 
v___x_1856_ = lean_nat_dec_le(v_pos_1846_, v_p_u2081_1848_);
v___y_1850_ = v___x_1856_;
goto v___jp_1849_;
}
v___jp_1849_:
{
if (v___y_1850_ == 0)
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1851_ = lean_unsigned_to_nat(0u);
v___x_1852_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1853_ = l_panic___redArg(v___x_1851_, v___x_1852_);
return v___x_1853_;
}
else
{
lean_object* v___x_1854_; 
v___x_1854_ = lean_nat_sub(v_pos_1846_, v_p_u2080_1847_);
return v___x_1854_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___redArg___boxed(lean_object* v_pos_1857_, lean_object* v_p_u2080_1858_, lean_object* v_p_u2081_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_String_Pos_slice_x21___redArg(v_pos_1857_, v_p_u2080_1858_, v_p_u2081_1859_);
lean_dec(v_p_u2081_1859_);
lean_dec(v_p_u2080_1858_);
lean_dec(v_pos_1857_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21(lean_object* v_s_1861_, lean_object* v_pos_1862_, lean_object* v_p_u2080_1863_, lean_object* v_p_u2081_1864_){
_start:
{
uint8_t v___y_1866_; uint8_t v___x_1871_; 
v___x_1871_ = lean_nat_dec_le(v_p_u2080_1863_, v_pos_1862_);
if (v___x_1871_ == 0)
{
v___y_1866_ = v___x_1871_;
goto v___jp_1865_;
}
else
{
uint8_t v___x_1872_; 
v___x_1872_ = lean_nat_dec_le(v_pos_1862_, v_p_u2081_1864_);
v___y_1866_ = v___x_1872_;
goto v___jp_1865_;
}
v___jp_1865_:
{
if (v___y_1866_ == 0)
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1867_ = lean_unsigned_to_nat(0u);
v___x_1868_ = lean_obj_once(&l_String_Slice_Pos_slice_x21___redArg___closed__2, &l_String_Slice_Pos_slice_x21___redArg___closed__2_once, _init_l_String_Slice_Pos_slice_x21___redArg___closed__2);
v___x_1869_ = l_panic___redArg(v___x_1867_, v___x_1868_);
return v___x_1869_;
}
else
{
lean_object* v___x_1870_; 
v___x_1870_ = lean_nat_sub(v_pos_1862_, v_p_u2080_1863_);
return v___x_1870_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_slice_x21___boxed(lean_object* v_s_1873_, lean_object* v_pos_1874_, lean_object* v_p_u2080_1875_, lean_object* v_p_u2081_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_String_Pos_slice_x21(v_s_1873_, v_pos_1874_, v_p_u2080_1875_, v_p_u2081_1876_);
lean_dec(v_p_u2081_1876_);
lean_dec(v_p_u2080_1875_);
lean_dec(v_pos_1874_);
lean_dec_ref(v_s_1873_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract(lean_object* v_s_1878_, lean_object* v_p_u2080_1879_, lean_object* v_p_u2081_1880_){
_start:
{
lean_object* v_str_1881_; lean_object* v_startInclusive_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v_str_1881_ = lean_ctor_get(v_s_1878_, 0);
v_startInclusive_1882_ = lean_ctor_get(v_s_1878_, 1);
v___x_1883_ = lean_nat_add(v_startInclusive_1882_, v_p_u2080_1879_);
v___x_1884_ = lean_nat_add(v_startInclusive_1882_, v_p_u2081_1880_);
v___x_1885_ = lean_string_utf8_extract_fast(v_str_1881_, v___x_1883_, v___x_1884_);
lean_dec(v___x_1884_);
lean_dec(v___x_1883_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_extract___boxed(lean_object* v_s_1886_, lean_object* v_p_u2080_1887_, lean_object* v_p_u2081_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_String_Slice_extract(v_s_1886_, v_p_u2080_1887_, v_p_u2081_1888_);
lean_dec(v_p_u2081_1888_);
lean_dec(v_p_u2080_1887_);
lean_dec_ref(v_s_1886_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn(lean_object* v_s_1890_, lean_object* v_p_1891_, lean_object* v_n_1892_){
_start:
{
lean_object* v_zero_1893_; uint8_t v_isZero_1894_; 
v_zero_1893_ = lean_unsigned_to_nat(0u);
v_isZero_1894_ = lean_nat_dec_eq(v_n_1892_, v_zero_1893_);
if (v_isZero_1894_ == 1)
{
lean_dec(v_n_1892_);
return v_p_1891_;
}
else
{
lean_object* v_str_1895_; lean_object* v_startInclusive_1896_; lean_object* v_endExclusive_1897_; lean_object* v_one_1898_; lean_object* v_n_1899_; lean_object* v___x_1905_; uint8_t v_decide_1906_; 
v_str_1895_ = lean_ctor_get(v_s_1890_, 0);
v_startInclusive_1896_ = lean_ctor_get(v_s_1890_, 1);
v_endExclusive_1897_ = lean_ctor_get(v_s_1890_, 2);
v_one_1898_ = lean_unsigned_to_nat(1u);
v_n_1899_ = lean_nat_sub(v_n_1892_, v_one_1898_);
lean_dec(v_n_1892_);
v___x_1905_ = lean_nat_sub(v_endExclusive_1897_, v_startInclusive_1896_);
v_decide_1906_ = lean_nat_dec_eq(v_p_1891_, v___x_1905_);
lean_dec(v___x_1905_);
if (v_decide_1906_ == 0)
{
goto v___jp_1900_;
}
else
{
if (v_isZero_1894_ == 0)
{
lean_dec(v_n_1899_);
return v_p_1891_;
}
else
{
goto v___jp_1900_;
}
}
v___jp_1900_:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1901_ = lean_nat_add(v_startInclusive_1896_, v_p_1891_);
lean_dec(v_p_1891_);
v___x_1902_ = lean_string_utf8_next_fast(v_str_1895_, v___x_1901_);
lean_dec(v___x_1901_);
v___x_1903_ = lean_nat_sub(v___x_1902_, v_startInclusive_1896_);
v_p_1891_ = v___x_1903_;
v_n_1892_ = v_n_1899_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn___boxed(lean_object* v_s_1907_, lean_object* v_p_1908_, lean_object* v_n_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_String_Slice_Pos_nextn(v_s_1907_, v_p_1908_, v_n_1909_);
lean_dec_ref(v_s_1907_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_nextn(lean_object* v_s_1911_, lean_object* v_p_1912_, lean_object* v_n_1913_){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1914_ = lean_unsigned_to_nat(0u);
v___x_1915_ = lean_string_utf8_byte_size(v_s_1911_);
v___x_1916_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1916_, 0, v_s_1911_);
lean_ctor_set(v___x_1916_, 1, v___x_1914_);
lean_ctor_set(v___x_1916_, 2, v___x_1915_);
v___x_1917_ = l_String_Slice_Pos_nextn(v___x_1916_, v_p_1912_, v_n_1913_);
lean_dec_ref_known(v___x_1916_, 3);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(lean_object* v_n_1918_, lean_object* v_h__1_1919_, lean_object* v_h__2_1920_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg___boxed(lean_object* v_n_1928_, lean_object* v_h__1_1929_, lean_object* v_h__2_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(v_n_1928_, v_h__1_1929_, v_h__2_1930_);
lean_dec(v_n_1928_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(lean_object* v_motive_1932_, lean_object* v_n_1933_, lean_object* v_h__1_1934_, lean_object* v_h__2_1935_){
_start:
{
lean_object* v_zero_1936_; uint8_t v_isZero_1937_; 
v_zero_1936_ = lean_unsigned_to_nat(0u);
v_isZero_1937_ = lean_nat_dec_eq(v_n_1933_, v_zero_1936_);
if (v_isZero_1937_ == 1)
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
lean_dec(v_h__2_1935_);
v___x_1938_ = lean_box(0);
v___x_1939_ = lean_apply_1(v_h__1_1934_, v___x_1938_);
return v___x_1939_;
}
else
{
lean_object* v_one_1940_; lean_object* v_n_1941_; lean_object* v___x_1942_; 
lean_dec(v_h__1_1934_);
v_one_1940_ = lean_unsigned_to_nat(1u);
v_n_1941_ = lean_nat_sub(v_n_1933_, v_one_1940_);
v___x_1942_ = lean_apply_1(v_h__2_1935_, v_n_1941_);
return v___x_1942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter___boxed(lean_object* v_motive_1943_, lean_object* v_n_1944_, lean_object* v_h__1_1945_, lean_object* v_h__2_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l___private_Init_Data_String_Basic_0__String_Slice_Pos_nextn_match__1_splitter(v_motive_1943_, v_n_1944_, v_h__1_1945_, v_h__2_1946_);
lean_dec(v_n_1944_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next___boxed(lean_object* v_s_1950_, lean_object* v_p_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = lean_string_utf8_next(v_s_1950_, v_p_1951_);
lean_dec(v_p_1951_);
lean_dec_ref(v_s_1950_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_String_next___boxed(lean_object* v_s_1955_, lean_object* v_p_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = lean_string_utf8_next(v_s_1955_, v_p_1956_);
lean_dec(v_p_1956_);
lean_dec_ref(v_s_1955_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux(lean_object* v_x_1958_, lean_object* v_x_1959_, lean_object* v_x_1960_){
_start:
{
if (lean_obj_tag(v_x_1958_) == 0)
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
lean_dec(v_x_1959_);
v___x_1961_ = lean_unsigned_to_nat(1u);
v___x_1962_ = lean_nat_sub(v_x_1960_, v___x_1961_);
return v___x_1962_;
}
else
{
lean_object* v_head_1963_; lean_object* v_tail_1964_; lean_object* v___y_1966_; uint32_t v___x_1970_; uint32_t v___x_1971_; uint8_t v___x_1972_; 
v_head_1963_ = lean_ctor_get(v_x_1958_, 0);
v_tail_1964_ = lean_ctor_get(v_x_1958_, 1);
v___x_1970_ = 127;
v___x_1971_ = lean_unbox_uint32(v_head_1963_);
v___x_1972_ = lean_uint32_dec_le(v___x_1971_, v___x_1970_);
if (v___x_1972_ == 0)
{
uint32_t v___x_1973_; uint32_t v___x_1974_; uint8_t v___x_1975_; 
v___x_1973_ = 2047;
v___x_1974_ = lean_unbox_uint32(v_head_1963_);
v___x_1975_ = lean_uint32_dec_le(v___x_1974_, v___x_1973_);
if (v___x_1975_ == 0)
{
uint32_t v___x_1976_; uint32_t v___x_1977_; uint8_t v___x_1978_; 
v___x_1976_ = 65535;
v___x_1977_ = lean_unbox_uint32(v_head_1963_);
v___x_1978_ = lean_uint32_dec_le(v___x_1977_, v___x_1976_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; 
v___x_1979_ = lean_unsigned_to_nat(4u);
v___y_1966_ = v___x_1979_;
goto v___jp_1965_;
}
else
{
lean_object* v___x_1980_; 
v___x_1980_ = lean_unsigned_to_nat(3u);
v___y_1966_ = v___x_1980_;
goto v___jp_1965_;
}
}
else
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_unsigned_to_nat(2u);
v___y_1966_ = v___x_1981_;
goto v___jp_1965_;
}
}
else
{
lean_object* v___x_1982_; 
v___x_1982_ = lean_unsigned_to_nat(1u);
v___y_1966_ = v___x_1982_;
goto v___jp_1965_;
}
v___jp_1965_:
{
lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1967_ = lean_nat_add(v_x_1959_, v___y_1966_);
v___x_1968_ = lean_nat_dec_le(v_x_1960_, v___x_1967_);
if (v___x_1968_ == 0)
{
lean_dec(v_x_1959_);
v_x_1958_ = v_tail_1964_;
v_x_1959_ = v___x_1967_;
goto _start;
}
else
{
lean_dec(v___x_1967_);
return v_x_1959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux___boxed(lean_object* v_x_1983_, lean_object* v_x_1984_, lean_object* v_x_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_String_Pos_Raw_utf8PrevAux(v_x_1983_, v_x_1984_, v_x_1985_);
lean_dec(v_x_1985_);
lean_dec(v_x_1983_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux(lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_){
_start:
{
lean_object* v___x_1990_; 
v___x_1990_ = l_String_Pos_Raw_utf8PrevAux(v_a_1987_, v_a_1988_, v_a_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux___boxed(lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_String_utf8PrevAux(v_a_1991_, v_a_1992_, v_a_1993_);
lean_dec(v_a_1993_);
lean_dec(v_a_1991_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_prev___boxed(lean_object* v_a_00___x40___internal___hyg_1997_, lean_object* v_a_00___x40___internal___hyg_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_1997_, v_a_00___x40___internal___hyg_1998_);
lean_dec(v_a_00___x40___internal___hyg_1998_);
lean_dec_ref(v_a_00___x40___internal___hyg_1997_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_String_prev___boxed(lean_object* v_a_00___x40___internal___hyg_2002_, lean_object* v_a_00___x40___internal___hyg_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = lean_string_utf8_prev(v_a_00___x40___internal___hyg_2002_, v_a_00___x40___internal___hyg_2003_);
lean_dec(v_a_00___x40___internal___hyg_2003_);
lean_dec_ref(v_a_00___x40___internal___hyg_2002_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_2007_, lean_object* v_a_00___x40___internal___hyg_2008_){
_start:
{
uint8_t v_res_2009_; lean_object* v_r_2010_; 
v_res_2009_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_2007_, v_a_00___x40___internal___hyg_2008_);
lean_dec(v_a_00___x40___internal___hyg_2008_);
lean_dec_ref(v_a_00___x40___internal___hyg_2007_);
v_r_2010_ = lean_box(v_res_2009_);
return v_r_2010_;
}
}
LEAN_EXPORT lean_object* l_String_atEnd___boxed(lean_object* v_a_00___x40___internal___hyg_2013_, lean_object* v_a_00___x40___internal___hyg_2014_){
_start:
{
uint8_t v_res_2015_; lean_object* v_r_2016_; 
v_res_2015_ = lean_string_utf8_at_end(v_a_00___x40___internal___hyg_2013_, v_a_00___x40___internal___hyg_2014_);
lean_dec(v_a_00___x40___internal___hyg_2014_);
lean_dec_ref(v_a_00___x40___internal___hyg_2013_);
v_r_2016_ = lean_box(v_res_2015_);
return v_r_2016_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x27___boxed(lean_object* v_s_2020_, lean_object* v_p_2021_, lean_object* v_h_2022_){
_start:
{
uint32_t v_res_2023_; lean_object* v_r_2024_; 
v_res_2023_ = lean_string_utf8_get_fast(v_s_2020_, v_p_2021_);
lean_dec(v_p_2021_);
lean_dec_ref(v_s_2020_);
v_r_2024_ = lean_box_uint32(v_res_2023_);
return v_r_2024_;
}
}
LEAN_EXPORT lean_object* l_String_get_x27___boxed(lean_object* v_s_2028_, lean_object* v_p_2029_, lean_object* v_h_2030_){
_start:
{
uint32_t v_res_2031_; lean_object* v_r_2032_; 
v_res_2031_ = lean_string_utf8_get_fast(v_s_2028_, v_p_2029_);
lean_dec(v_p_2029_);
lean_dec_ref(v_s_2028_);
v_r_2032_ = lean_box_uint32(v_res_2031_);
return v_r_2032_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next_x27___boxed(lean_object* v_s_2036_, lean_object* v_p_2037_, lean_object* v_h_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = lean_string_utf8_next_fast(v_s_2036_, v_p_2037_);
lean_dec(v_p_2037_);
lean_dec_ref(v_s_2036_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_String_next_x27___boxed(lean_object* v_s_2043_, lean_object* v_p_2044_, lean_object* v_h_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = lean_string_utf8_next_fast(v_s_2043_, v_p_2044_);
lean_dec(v_p_2044_);
lean_dec_ref(v_s_2043_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter___redArg(lean_object* v_x_2047_, lean_object* v_x_2048_, lean_object* v_x_2049_, lean_object* v_h__1_2050_, lean_object* v_h__2_2051_){
_start:
{
if (lean_obj_tag(v_x_2047_) == 0)
{
lean_object* v___x_2052_; 
lean_dec(v_h__2_2051_);
v___x_2052_ = lean_apply_2(v_h__1_2050_, v_x_2048_, v_x_2049_);
return v___x_2052_;
}
else
{
lean_object* v_head_2053_; lean_object* v_tail_2054_; lean_object* v___x_2055_; 
lean_dec(v_h__1_2050_);
v_head_2053_ = lean_ctor_get(v_x_2047_, 0);
lean_inc(v_head_2053_);
v_tail_2054_ = lean_ctor_get(v_x_2047_, 1);
lean_inc(v_tail_2054_);
lean_dec_ref_known(v_x_2047_, 2);
v___x_2055_ = lean_apply_4(v_h__2_2051_, v_head_2053_, v_tail_2054_, v_x_2048_, v_x_2049_);
return v___x_2055_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter(lean_object* v_motive_2056_, lean_object* v_x_2057_, lean_object* v_x_2058_, lean_object* v_x_2059_, lean_object* v_h__1_2060_, lean_object* v_h__2_2061_){
_start:
{
if (lean_obj_tag(v_x_2057_) == 0)
{
lean_object* v___x_2062_; 
lean_dec(v_h__2_2061_);
v___x_2062_ = lean_apply_2(v_h__1_2060_, v_x_2058_, v_x_2059_);
return v___x_2062_;
}
else
{
lean_object* v_head_2063_; lean_object* v_tail_2064_; lean_object* v___x_2065_; 
lean_dec(v_h__1_2060_);
v_head_2063_ = lean_ctor_get(v_x_2057_, 0);
lean_inc(v_head_2063_);
v_tail_2064_ = lean_ctor_get(v_x_2057_, 1);
lean_inc(v_tail_2064_);
lean_dec_ref_known(v_x_2057_, 2);
v___x_2065_ = lean_apply_4(v_h__2_2061_, v_head_2063_, v_tail_2064_, v_x_2058_, v_x_2059_);
return v___x_2065_;
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop(lean_object* v_a_2066_, lean_object* v_b_2067_, lean_object* v_stopPos_2068_, lean_object* v_i_2069_){
_start:
{
uint8_t v___y_2071_; lean_object* v___x_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; uint8_t v___y_2078_; 
v___x_2074_ = lean_unsigned_to_nat(1u);
v___x_2075_ = lean_nat_add(v_i_2069_, v___x_2074_);
v___x_2076_ = lean_nat_dec_le(v___x_2075_, v_stopPos_2068_);
lean_dec(v___x_2075_);
if (v___x_2076_ == 0)
{
return v_i_2069_;
}
else
{
uint32_t v___x_2079_; uint32_t v___x_2080_; uint8_t v___x_2081_; 
v___x_2079_ = lean_string_utf8_get(v_a_2066_, v_i_2069_);
v___x_2080_ = lean_string_utf8_get(v_b_2067_, v_i_2069_);
v___x_2081_ = lean_uint32_dec_eq(v___x_2079_, v___x_2080_);
if (v___x_2081_ == 0)
{
v___y_2078_ = v___x_2076_;
goto v___jp_2077_;
}
else
{
uint8_t v___x_2082_; 
v___x_2082_ = 0;
v___y_2078_ = v___x_2082_;
goto v___jp_2077_;
}
}
v___jp_2070_:
{
if (v___y_2071_ == 0)
{
lean_object* v___x_2072_; 
v___x_2072_ = lean_string_utf8_next(v_a_2066_, v_i_2069_);
lean_dec(v_i_2069_);
v_i_2069_ = v___x_2072_;
goto _start;
}
else
{
return v_i_2069_;
}
}
v___jp_2077_:
{
if (v___x_2076_ == 0)
{
v___y_2071_ = v___x_2076_;
goto v___jp_2070_;
}
else
{
v___y_2071_ = v___y_2078_;
goto v___jp_2070_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop___boxed(lean_object* v_a_2083_, lean_object* v_b_2084_, lean_object* v_stopPos_2085_, lean_object* v_i_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_String_firstDiffPos_loop(v_a_2083_, v_b_2084_, v_stopPos_2085_, v_i_2086_);
lean_dec(v_stopPos_2085_);
lean_dec_ref(v_b_2084_);
lean_dec_ref(v_a_2083_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos(lean_object* v_a_2088_, lean_object* v_b_2089_){
_start:
{
lean_object* v___y_2091_; lean_object* v___x_2094_; lean_object* v___x_2095_; uint8_t v___x_2096_; 
v___x_2094_ = lean_string_utf8_byte_size(v_a_2088_);
v___x_2095_ = lean_string_utf8_byte_size(v_b_2089_);
v___x_2096_ = lean_nat_dec_le(v___x_2094_, v___x_2095_);
if (v___x_2096_ == 0)
{
v___y_2091_ = v___x_2095_;
goto v___jp_2090_;
}
else
{
v___y_2091_ = v___x_2094_;
goto v___jp_2090_;
}
v___jp_2090_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = lean_unsigned_to_nat(0u);
v___x_2093_ = l_String_firstDiffPos_loop(v_a_2088_, v_b_2089_, v___y_2091_, v___x_2092_);
lean_dec(v___y_2091_);
return v___x_2093_;
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos___boxed(lean_object* v_a_2097_, lean_object* v_b_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_String_firstDiffPos(v_a_2097_, v_b_2098_);
lean_dec_ref(v_b_2098_);
lean_dec_ref(v_a_2097_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082(lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_){
_start:
{
if (lean_obj_tag(v_a_2100_) == 0)
{
return v_a_2100_;
}
else
{
lean_object* v_head_2103_; lean_object* v_tail_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2130_; 
v_head_2103_ = lean_ctor_get(v_a_2100_, 0);
v_tail_2104_ = lean_ctor_get(v_a_2100_, 1);
v_isSharedCheck_2130_ = !lean_is_exclusive(v_a_2100_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2106_ = v_a_2100_;
v_isShared_2107_ = v_isSharedCheck_2130_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_tail_2104_);
lean_inc(v_head_2103_);
lean_dec(v_a_2100_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2130_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___y_2109_; uint8_t v_decide_2115_; 
v_decide_2115_ = lean_nat_dec_eq(v_a_2101_, v_a_2102_);
if (v_decide_2115_ == 0)
{
uint32_t v___x_2116_; uint32_t v___x_2117_; uint8_t v___x_2118_; 
v___x_2116_ = 127;
v___x_2117_ = lean_unbox_uint32(v_head_2103_);
v___x_2118_ = lean_uint32_dec_le(v___x_2117_, v___x_2116_);
if (v___x_2118_ == 0)
{
uint32_t v___x_2119_; uint32_t v___x_2120_; uint8_t v___x_2121_; 
v___x_2119_ = 2047;
v___x_2120_ = lean_unbox_uint32(v_head_2103_);
v___x_2121_ = lean_uint32_dec_le(v___x_2120_, v___x_2119_);
if (v___x_2121_ == 0)
{
uint32_t v___x_2122_; uint32_t v___x_2123_; uint8_t v___x_2124_; 
v___x_2122_ = 65535;
v___x_2123_ = lean_unbox_uint32(v_head_2103_);
v___x_2124_ = lean_uint32_dec_le(v___x_2123_, v___x_2122_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; 
v___x_2125_ = lean_unsigned_to_nat(4u);
v___y_2109_ = v___x_2125_;
goto v___jp_2108_;
}
else
{
lean_object* v___x_2126_; 
v___x_2126_ = lean_unsigned_to_nat(3u);
v___y_2109_ = v___x_2126_;
goto v___jp_2108_;
}
}
else
{
lean_object* v___x_2127_; 
v___x_2127_ = lean_unsigned_to_nat(2u);
v___y_2109_ = v___x_2127_;
goto v___jp_2108_;
}
}
else
{
lean_object* v___x_2128_; 
v___x_2128_ = lean_unsigned_to_nat(1u);
v___y_2109_ = v___x_2128_;
goto v___jp_2108_;
}
}
else
{
lean_object* v___x_2129_; 
lean_del_object(v___x_2106_);
lean_dec(v_tail_2104_);
lean_dec(v_head_2103_);
v___x_2129_ = lean_box(0);
return v___x_2129_;
}
v___jp_2108_:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2113_; 
v___x_2110_ = lean_nat_add(v_a_2101_, v___y_2109_);
v___x_2111_ = l_String_Pos_Raw_extract_go_u2082(v_tail_2104_, v___x_2110_, v_a_2102_);
lean_dec(v___x_2110_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 1, v___x_2111_);
v___x_2113_ = v___x_2106_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_head_2103_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v___x_2111_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082___boxed(lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_String_Pos_Raw_extract_go_u2082(v_a_2131_, v_a_2132_, v_a_2133_);
lean_dec(v_a_2133_);
lean_dec(v_a_2132_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081(lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
if (lean_obj_tag(v_a_2135_) == 0)
{
lean_dec(v_a_2136_);
return v_a_2135_;
}
else
{
lean_object* v_head_2139_; lean_object* v_tail_2140_; lean_object* v___y_2142_; uint8_t v_decide_2145_; 
v_head_2139_ = lean_ctor_get(v_a_2135_, 0);
v_tail_2140_ = lean_ctor_get(v_a_2135_, 1);
v_decide_2145_ = lean_nat_dec_eq(v_a_2136_, v_a_2137_);
if (v_decide_2145_ == 0)
{
uint32_t v___x_2146_; uint32_t v___x_2147_; uint8_t v___x_2148_; 
lean_inc(v_tail_2140_);
lean_inc(v_head_2139_);
lean_dec_ref_known(v_a_2135_, 2);
v___x_2146_ = 127;
v___x_2147_ = lean_unbox_uint32(v_head_2139_);
v___x_2148_ = lean_uint32_dec_le(v___x_2147_, v___x_2146_);
if (v___x_2148_ == 0)
{
uint32_t v___x_2149_; uint32_t v___x_2150_; uint8_t v___x_2151_; 
v___x_2149_ = 2047;
v___x_2150_ = lean_unbox_uint32(v_head_2139_);
v___x_2151_ = lean_uint32_dec_le(v___x_2150_, v___x_2149_);
if (v___x_2151_ == 0)
{
uint32_t v___x_2152_; uint32_t v___x_2153_; uint8_t v___x_2154_; 
v___x_2152_ = 65535;
v___x_2153_ = lean_unbox_uint32(v_head_2139_);
lean_dec(v_head_2139_);
v___x_2154_ = lean_uint32_dec_le(v___x_2153_, v___x_2152_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; 
v___x_2155_ = lean_unsigned_to_nat(4u);
v___y_2142_ = v___x_2155_;
goto v___jp_2141_;
}
else
{
lean_object* v___x_2156_; 
v___x_2156_ = lean_unsigned_to_nat(3u);
v___y_2142_ = v___x_2156_;
goto v___jp_2141_;
}
}
else
{
lean_object* v___x_2157_; 
lean_dec(v_head_2139_);
v___x_2157_ = lean_unsigned_to_nat(2u);
v___y_2142_ = v___x_2157_;
goto v___jp_2141_;
}
}
else
{
lean_object* v___x_2158_; 
lean_dec(v_head_2139_);
v___x_2158_ = lean_unsigned_to_nat(1u);
v___y_2142_ = v___x_2158_;
goto v___jp_2141_;
}
}
else
{
lean_object* v___x_2159_; 
v___x_2159_ = l_String_Pos_Raw_extract_go_u2082(v_a_2135_, v_a_2136_, v_a_2138_);
lean_dec(v_a_2136_);
return v___x_2159_;
}
v___jp_2141_:
{
lean_object* v___x_2143_; 
v___x_2143_ = lean_nat_add(v_a_2136_, v___y_2142_);
lean_dec(v_a_2136_);
v_a_2135_ = v_tail_2140_;
v_a_2136_ = v___x_2143_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081___boxed(lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_String_Pos_Raw_extract_go_u2081(v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_);
lean_dec(v_a_2163_);
lean_dec(v_a_2162_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract___boxed(lean_object* v_a_00___x40___internal___hyg_2168_, lean_object* v_a_00___x40___internal___hyg_2169_, lean_object* v_a_00___x40___internal___hyg_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = lean_string_utf8_extract(v_a_00___x40___internal___hyg_2168_, v_a_00___x40___internal___hyg_2169_, v_a_00___x40___internal___hyg_2170_);
lean_dec(v_a_00___x40___internal___hyg_2170_);
lean_dec(v_a_00___x40___internal___hyg_2169_);
lean_dec_ref(v_a_00___x40___internal___hyg_2168_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux(lean_object* v_s_2172_, lean_object* v_pos_2173_, lean_object* v_i_2174_, lean_object* v_offset_2175_){
_start:
{
uint8_t v___x_2176_; 
v___x_2176_ = lean_nat_dec_le(v_pos_2173_, v_i_2174_);
if (v___x_2176_ == 0)
{
uint8_t v___x_2177_; 
v___x_2177_ = lean_string_utf8_at_end(v_s_2172_, v_i_2174_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2178_ = lean_string_utf8_next(v_s_2172_, v_i_2174_);
lean_dec(v_i_2174_);
v___x_2179_ = lean_unsigned_to_nat(1u);
v___x_2180_ = lean_nat_add(v_offset_2175_, v___x_2179_);
lean_dec(v_offset_2175_);
v_i_2174_ = v___x_2178_;
v_offset_2175_ = v___x_2180_;
goto _start;
}
else
{
lean_dec(v_i_2174_);
return v_offset_2175_;
}
}
else
{
lean_dec(v_i_2174_);
return v_offset_2175_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPosAux___boxed(lean_object* v_s_2182_, lean_object* v_pos_2183_, lean_object* v_i_2184_, lean_object* v_offset_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2182_, v_pos_2183_, v_i_2184_, v_offset_2185_);
lean_dec(v_pos_2183_);
lean_dec_ref(v_s_2182_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos(lean_object* v_s_2187_, lean_object* v_pos_2188_){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2190_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2187_, v_pos_2188_, v___x_2189_, v___x_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetOfPos___boxed(lean_object* v_s_2191_, lean_object* v_pos_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_String_Pos_Raw_offsetOfPos(v_s_2191_, v_pos_2192_);
lean_dec(v_pos_2192_);
lean_dec_ref(v_s_2191_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos(lean_object* v_s_2194_, lean_object* v_pos_2195_){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = lean_unsigned_to_nat(0u);
v___x_2197_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2194_, v_pos_2195_, v___x_2196_, v___x_2196_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos___boxed(lean_object* v_s_2198_, lean_object* v_pos_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_String_offsetOfPos(v_s_2198_, v_pos_2199_);
lean_dec(v_pos_2199_);
lean_dec_ref(v_s_2198_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* lean_string_offsetofpos(lean_object* v_s_2201_, lean_object* v_pos_2202_){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = lean_unsigned_to_nat(0u);
v___x_2204_ = l_String_Pos_Raw_offsetOfPosAux(v_s_2201_, v_pos_2202_, v___x_2203_, v___x_2203_);
lean_dec(v_pos_2202_);
lean_dec_ref(v_s_2201_);
return v___x_2204_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(lean_object* v_s1_2205_, lean_object* v_s2_2206_, lean_object* v_off1_2207_, lean_object* v_off2_2208_, lean_object* v_stop1_2209_){
_start:
{
lean_object* v___y_2211_; lean_object* v___y_2212_; uint8_t v___x_2215_; 
v___x_2215_ = lean_nat_dec_lt(v_off1_2207_, v_stop1_2209_);
if (v___x_2215_ == 0)
{
uint8_t v___x_2216_; 
lean_dec(v_off2_2208_);
lean_dec(v_off1_2207_);
v___x_2216_ = 1;
return v___x_2216_;
}
else
{
uint32_t v_c_u2081_2217_; uint32_t v_c_u2082_2218_; lean_object* v___y_2220_; uint8_t v___x_2232_; 
v_c_u2081_2217_ = lean_string_utf8_get(v_s1_2205_, v_off1_2207_);
v_c_u2082_2218_ = lean_string_utf8_get(v_s2_2206_, v_off2_2208_);
v___x_2232_ = lean_uint32_dec_eq(v_c_u2081_2217_, v_c_u2082_2218_);
if (v___x_2232_ == 0)
{
lean_dec(v_off2_2208_);
lean_dec(v_off1_2207_);
return v___x_2232_;
}
else
{
uint32_t v___x_2233_; uint8_t v___x_2234_; 
v___x_2233_ = 127;
v___x_2234_ = lean_uint32_dec_le(v_c_u2081_2217_, v___x_2233_);
if (v___x_2234_ == 0)
{
uint32_t v___x_2235_; uint8_t v___x_2236_; 
v___x_2235_ = 2047;
v___x_2236_ = lean_uint32_dec_le(v_c_u2081_2217_, v___x_2235_);
if (v___x_2236_ == 0)
{
uint32_t v___x_2237_; uint8_t v___x_2238_; 
v___x_2237_ = 65535;
v___x_2238_ = lean_uint32_dec_le(v_c_u2081_2217_, v___x_2237_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; 
v___x_2239_ = lean_unsigned_to_nat(4u);
v___y_2220_ = v___x_2239_;
goto v___jp_2219_;
}
else
{
lean_object* v___x_2240_; 
v___x_2240_ = lean_unsigned_to_nat(3u);
v___y_2220_ = v___x_2240_;
goto v___jp_2219_;
}
}
else
{
lean_object* v___x_2241_; 
v___x_2241_ = lean_unsigned_to_nat(2u);
v___y_2220_ = v___x_2241_;
goto v___jp_2219_;
}
}
else
{
lean_object* v___x_2242_; 
v___x_2242_ = lean_unsigned_to_nat(1u);
v___y_2220_ = v___x_2242_;
goto v___jp_2219_;
}
}
v___jp_2219_:
{
lean_object* v___x_2221_; uint32_t v___x_2222_; uint8_t v___x_2223_; 
v___x_2221_ = lean_nat_add(v_off1_2207_, v___y_2220_);
lean_dec(v_off1_2207_);
v___x_2222_ = 127;
v___x_2223_ = lean_uint32_dec_le(v_c_u2082_2218_, v___x_2222_);
if (v___x_2223_ == 0)
{
uint32_t v___x_2224_; uint8_t v___x_2225_; 
v___x_2224_ = 2047;
v___x_2225_ = lean_uint32_dec_le(v_c_u2082_2218_, v___x_2224_);
if (v___x_2225_ == 0)
{
uint32_t v___x_2226_; uint8_t v___x_2227_; 
v___x_2226_ = 65535;
v___x_2227_ = lean_uint32_dec_le(v_c_u2082_2218_, v___x_2226_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2228_; 
v___x_2228_ = lean_unsigned_to_nat(4u);
v___y_2211_ = v___x_2221_;
v___y_2212_ = v___x_2228_;
goto v___jp_2210_;
}
else
{
lean_object* v___x_2229_; 
v___x_2229_ = lean_unsigned_to_nat(3u);
v___y_2211_ = v___x_2221_;
v___y_2212_ = v___x_2229_;
goto v___jp_2210_;
}
}
else
{
lean_object* v___x_2230_; 
v___x_2230_ = lean_unsigned_to_nat(2u);
v___y_2211_ = v___x_2221_;
v___y_2212_ = v___x_2230_;
goto v___jp_2210_;
}
}
else
{
lean_object* v___x_2231_; 
v___x_2231_ = lean_unsigned_to_nat(1u);
v___y_2211_ = v___x_2221_;
v___y_2212_ = v___x_2231_;
goto v___jp_2210_;
}
}
}
v___jp_2210_:
{
lean_object* v___x_2213_; 
v___x_2213_ = lean_nat_add(v_off2_2208_, v___y_2212_);
lean_dec(v_off2_2208_);
v_off1_2207_ = v___y_2211_;
v_off2_2208_ = v___x_2213_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop___boxed(lean_object* v_s1_2243_, lean_object* v_s2_2244_, lean_object* v_off1_2245_, lean_object* v_off2_2246_, lean_object* v_stop1_2247_){
_start:
{
uint8_t v_res_2248_; lean_object* v_r_2249_; 
v_res_2248_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2243_, v_s2_2244_, v_off1_2245_, v_off2_2246_, v_stop1_2247_);
lean_dec(v_stop1_2247_);
lean_dec_ref(v_s2_2244_);
lean_dec_ref(v_s1_2243_);
v_r_2249_ = lean_box(v_res_2248_);
return v_r_2249_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_substrEq(lean_object* v_s1_2250_, lean_object* v_pos1_2251_, lean_object* v_s2_2252_, lean_object* v_pos2_2253_, lean_object* v_sz_2254_){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; uint8_t v___x_2257_; 
v___x_2255_ = lean_nat_add(v_pos1_2251_, v_sz_2254_);
v___x_2256_ = lean_string_utf8_byte_size(v_s1_2250_);
v___x_2257_ = lean_nat_dec_le(v___x_2255_, v___x_2256_);
if (v___x_2257_ == 0)
{
lean_dec(v___x_2255_);
lean_dec(v_pos2_2253_);
lean_dec(v_pos1_2251_);
return v___x_2257_;
}
else
{
lean_object* v___x_2258_; lean_object* v___x_2259_; uint8_t v___x_2260_; 
v___x_2258_ = lean_nat_add(v_pos2_2253_, v_sz_2254_);
v___x_2259_ = lean_string_utf8_byte_size(v_s2_2252_);
v___x_2260_ = lean_nat_dec_le(v___x_2258_, v___x_2259_);
lean_dec(v___x_2258_);
if (v___x_2260_ == 0)
{
lean_dec(v___x_2255_);
lean_dec(v_pos2_2253_);
lean_dec(v_pos1_2251_);
return v___x_2260_;
}
else
{
uint8_t v___x_2261_; 
v___x_2261_ = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(v_s1_2250_, v_s2_2252_, v_pos1_2251_, v_pos2_2253_, v___x_2255_);
lean_dec(v___x_2255_);
return v___x_2261_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_substrEq___boxed(lean_object* v_s1_2262_, lean_object* v_pos1_2263_, lean_object* v_s2_2264_, lean_object* v_pos2_2265_, lean_object* v_sz_2266_){
_start:
{
uint8_t v_res_2267_; lean_object* v_r_2268_; 
v_res_2267_ = l_String_Pos_Raw_substrEq(v_s1_2262_, v_pos1_2263_, v_s2_2264_, v_pos2_2265_, v_sz_2266_);
lean_dec(v_sz_2266_);
lean_dec_ref(v_s2_2264_);
lean_dec_ref(v_s1_2262_);
v_r_2268_ = lean_box(v_res_2267_);
return v_r_2268_;
}
}
LEAN_EXPORT uint8_t l_String_substrEq(lean_object* v_s1_2269_, lean_object* v_pos1_2270_, lean_object* v_s2_2271_, lean_object* v_pos2_2272_, lean_object* v_sz_2273_){
_start:
{
uint8_t v___x_2274_; 
v___x_2274_ = l_String_Pos_Raw_substrEq(v_s1_2269_, v_pos1_2270_, v_s2_2271_, v_pos2_2272_, v_sz_2273_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_String_substrEq___boxed(lean_object* v_s1_2275_, lean_object* v_pos1_2276_, lean_object* v_s2_2277_, lean_object* v_pos2_2278_, lean_object* v_sz_2279_){
_start:
{
uint8_t v_res_2280_; lean_object* v_r_2281_; 
v_res_2280_ = l_String_substrEq(v_s1_2275_, v_pos1_2276_, v_s2_2277_, v_pos2_2278_, v_sz_2279_);
lean_dec(v_sz_2279_);
lean_dec_ref(v_s2_2277_);
lean_dec_ref(v_s1_2275_);
v_r_2281_ = lean_box(v_res_2280_);
return v_r_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object* v_x_2282_, lean_object* v_x_2283_, lean_object* v_h__1_2284_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = lean_apply_2(v_h__1_2284_, v_x_2282_, v_x_2283_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object* v_motive_2286_, lean_object* v_x_2287_, lean_object* v_x_2288_, lean_object* v_h__1_2289_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = lean_apply_2(v_h__1_2289_, v_x_2287_, v_x_2288_);
return v___x_2290_;
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
