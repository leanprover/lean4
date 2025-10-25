// Lean compiler output
// Module: Init.Data.String.Basic
// Imports: public import Init.Data.String.Decode public import Init.Data.String.Defs public import Init.Data.String.PosRaw import Init.Data.ByteArray.Lemmas import Init.Data.Char.Lemmas
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
LEAN_EXPORT lean_object* l_String_next_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_pos_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_ValidPos_byte___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_contains___lam__0___boxed(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_bang(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_isNat___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_findLineStart___lam__0___boxed(lean_object*);
static lean_object* l_ByteArray_utf8Decode_x3f___closed__0;
LEAN_EXPORT lean_object* l_String_revFindAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_next_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_next___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_contains___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_String_foldrAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_replaceStartEnd_x21_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_prev___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_String_ValidPos_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableIsValid(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_pos(lean_object*, lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_String_ValidPos_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_containsImpl___boxed(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_ofCopy___redArg(lean_object*);
LEAN_EXPORT lean_object* lean_string_offsetofpos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_findNextPos___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_get_opt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_prev___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revFind___boxed(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_posOfImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_get_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_next_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_all___lam__0(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_toNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_String_revPosOfAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_pos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_String_Pos_Raw_utf8GetAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint8_to_uint32(uint8_t);
LEAN_EXPORT lean_object* l_String_instDecidableIsValid___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_str(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_extract___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revPosOf___boxed(lean_object*, lean_object*);
static lean_object* l_String_Slice_replaceStartEnd_x21___closed__2;
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8_x21(lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_data___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_str___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_String_Slice_Pos_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_atEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_get_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_String_utf8GetAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_isPrefixOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_get_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_string_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21___boxed(lean_object*, lean_object*);
static lean_object* l_String_fromUTF8_x21___closed__4;
LEAN_EXPORT uint8_t l_String_contains(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_length___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_get___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___boxed(lean_object*, lean_object*);
uint8_t lean_uint8_land(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_String_isNat___lam__0(uint8_t, uint32_t);
LEAN_EXPORT lean_object* lean_string_posof(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_foldl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__3_splitter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg(lean_object*, lean_object*);
static lean_object* l_String_Slice_Pos_next_x21___closed__0;
LEAN_EXPORT lean_object* l_String_Pos_Raw_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_findLineStart___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_revFind(lean_object*, lean_object*);
static lean_object* l_String_fromUTF8_x21___closed__2;
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_toSlice___boxed(lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
static lean_object* l_String_Slice_Pos_prev_x21___closed__0;
LEAN_EXPORT lean_object* l_String_foldlAux___at___00String_toNat_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_next_x21(lean_object*, lean_object*);
static lean_object* l_String_Slice_pos_x21___closed__1;
LEAN_EXPORT lean_object* l_String_firstDiffPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_isNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_pos___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_ofCopy___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_pos_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed(lean_object*);
LEAN_EXPORT uint32_t l_String_Slice_Pos_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_replaceEnd(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_substrEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValidForSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8GetAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_findLineStart___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_String_ValidPos_prev_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_toSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8SetAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldrAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_back___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at___00String_toNat_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_String_fromUTF8_x21___closed__1;
LEAN_EXPORT uint8_t l_String_decLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableIsValidForSlice___boxed(lean_object*, lean_object*);
lean_object* lean_string_data(lean_object*);
LEAN_EXPORT lean_object* l_String_replaceStart(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_get_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_findNextPos___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg(lean_object*);
extern lean_object* l_String_instInhabitedSlice;
LEAN_EXPORT lean_object* l_String_findLineStart(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instLE;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableIsValidUTF8(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_next(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8_x3f(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableIsValidForSlice(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_anyAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableIsValidUTF8___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* lean_string_foldl(lean_object*, lean_object*, lean_object*);
static lean_object* l_String_Slice_Pos_prev_x21___closed__2;
LEAN_EXPORT lean_object* l_String_foldl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev___redArg___boxed(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_decLE___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_any___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_get_opt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStart(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_panic___at___00String_Slice_Pos_get_x21_spec__0(lean_object*);
lean_object* l_String_Slice_utf8ByteSize(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f(lean_object*, lean_object*);
static lean_object* l_String_Slice_pos_x21___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_get___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_prev(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_all(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_firstDiffPos(lean_object*, lean_object*);
static lean_object* l_String_Slice_replaceStartEnd_x21___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_String_Slice_pos_x21___closed__2;
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at___00String_Internal_containsImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_next_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_offsetOfPosAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_findNextPos_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_byte___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_decodeChar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posOfAux(lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_String_front(lean_object*);
LEAN_EXPORT lean_object* l_String_splitToList___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_find___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_copy(lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_prev_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_String_Slice_Pos_prev_x21___closed__1;
LEAN_EXPORT lean_object* l_String_foldl___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_String_Slice_replaceStartEnd_x21___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_ofCopy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_offsetOfPosAux(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_String_Slice_Pos_get_x21___closed__2;
LEAN_EXPORT lean_object* l_String_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_findNextPos___redArg___boxed(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_toSlice___redArg___boxed(lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_cast(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Pos_Raw_isValidForSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_copy___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStart___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8SetAux(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revPosOfAux(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT uint8_t l_String_isNat(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_front___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_frontImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_instLT;
LEAN_EXPORT uint8_t l_String_anyAux___at___00String_toNat_x3f_spec__1(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_cast___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_byte___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_findNextPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revPosOf(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_pos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_toList(lean_object*);
static lean_object* l_String_fromUTF8_x21___closed__0;
LEAN_EXPORT lean_object* l_String_foldr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg___boxed(lean_object*);
static lean_object* l_String_Slice_Pos_get_x21___closed__1;
LEAN_EXPORT lean_object* l_String_findAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_atEnd___boxed(lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_get_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_prev___redArg(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_String_all___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_substrEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_bang(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_prev_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux(uint32_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_prev___boxed(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_String_extract___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___at___00String_Internal_foldlImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_split___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_String_back(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posOfAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1;
LEAN_EXPORT uint8_t lean_string_contains(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_pos_x21___boxed(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint32_t lean_uint32_lor(uint32_t, uint32_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t l_UInt8_instDecidableIsUTF8FirstByte(uint8_t);
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x21(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_String_Slice_Pos_get(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT uint8_t l_String_substrEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revFindAux___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitToList(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_ValidPos_byte(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8PrevAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_String_Slice_Pos_next_x21___closed__1;
static lean_object* l_String_Slice_Pos_next_x21___closed__2;
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_next(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8___boxed(lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___at___00String_toNat_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValid___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_next___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8PrevAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT uint32_t lean_string_front(lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_ofCopy___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_offsetOfPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_offsetOfPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_findNextPos_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_next___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_String_all___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f(lean_object*);
static lean_object* l_String_Slice_Pos_get_x21___closed__0;
LEAN_EXPORT lean_object* l_String_toNat_x3f___boxed(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_anyImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_string_isprefixof(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posOf(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_next___boxed(lean_object*, lean_object*);
static lean_object* l_String_fromUTF8_x21___closed__3;
LEAN_EXPORT lean_object* l_String_foldlAux___at___00String_Internal_foldlImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_String_foldrAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_anyAux___at___00String_Internal_containsImpl_spec__0(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_String_ValidPos_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_prev_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitOn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Char_utf8Size(uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_next_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_prev___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_isPrefixOfImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Pos_Raw_substrEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_pos___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_String_Internal_toArray(lean_object*);
LEAN_EXPORT lean_object* l_String_split(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldrAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_next___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at___00String_Internal_anyImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_findAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_decidableLT___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_pos___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_toSlice___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_splitOn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_UInt8_utf8ByteSize___redArg(uint8_t);
LEAN_EXPORT lean_object* l_String_pos_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitOnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_anyAux___at___00String_Internal_anyImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
x_7 = lean_byte_array_size(x_1);
x_8 = lean_nat_dec_eq(x_3, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint32_t x_13; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_2, x_11);
lean_dec(x_2);
x_20 = lean_byte_array_fget(x_1, x_3);
x_21 = 128;
x_22 = lean_uint8_land(x_20, x_21);
x_23 = 0;
x_24 = lean_uint8_dec_eq(x_22, x_23);
if (x_24 == 0)
{
uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; 
x_25 = 224;
x_26 = lean_uint8_land(x_20, x_25);
x_27 = 192;
x_28 = lean_uint8_dec_eq(x_26, x_27);
if (x_28 == 0)
{
uint8_t x_29; uint8_t x_30; uint8_t x_31; 
x_29 = 240;
x_30 = lean_uint8_land(x_20, x_29);
x_31 = lean_uint8_dec_eq(x_30, x_25);
if (x_31 == 0)
{
uint8_t x_32; uint8_t x_33; uint8_t x_34; 
x_32 = 248;
x_33 = lean_uint8_land(x_20, x_32);
x_34 = lean_uint8_dec_eq(x_33, x_29);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec(x_3);
x_35 = lean_box(0);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_add(x_3, x_36);
x_38 = lean_nat_dec_lt(x_37, x_7);
lean_dec(x_7);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_37);
lean_dec(x_12);
lean_dec_ref(x_4);
lean_dec(x_3);
x_39 = lean_box(0);
return x_39;
}
else
{
lean_object* x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; 
x_40 = lean_nat_add(x_3, x_11);
x_41 = lean_byte_array_fget(x_1, x_40);
lean_dec(x_40);
x_42 = lean_uint8_land(x_41, x_27);
x_43 = lean_uint8_dec_eq(x_42, x_21);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_37);
lean_dec(x_12);
lean_dec_ref(x_4);
lean_dec(x_3);
x_44 = lean_box(0);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; 
x_45 = lean_unsigned_to_nat(2u);
x_46 = lean_nat_add(x_3, x_45);
x_47 = lean_byte_array_fget(x_1, x_46);
lean_dec(x_46);
x_48 = lean_uint8_land(x_47, x_27);
x_49 = lean_uint8_dec_eq(x_48, x_21);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_37);
lean_dec(x_12);
lean_dec_ref(x_4);
lean_dec(x_3);
x_50 = lean_box(0);
return x_50;
}
else
{
uint8_t x_51; uint8_t x_52; uint8_t x_53; 
x_51 = lean_byte_array_fget(x_1, x_37);
lean_dec(x_37);
x_52 = lean_uint8_land(x_51, x_27);
x_53 = lean_uint8_dec_eq(x_52, x_21);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_12);
lean_dec_ref(x_4);
lean_dec(x_3);
x_54 = lean_box(0);
return x_54;
}
else
{
uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint32_t x_61; uint32_t x_62; uint32_t x_63; uint32_t x_64; uint32_t x_65; uint32_t x_66; uint32_t x_67; uint32_t x_68; uint32_t x_69; uint32_t x_70; uint32_t x_71; uint32_t x_72; uint32_t x_73; uint32_t x_74; uint8_t x_75; 
x_55 = 7;
x_56 = lean_uint8_land(x_20, x_55);
x_57 = 63;
x_58 = lean_uint8_land(x_41, x_57);
x_59 = lean_uint8_land(x_47, x_57);
x_60 = lean_uint8_land(x_51, x_57);
x_61 = lean_uint8_to_uint32(x_56);
x_62 = 18;
x_63 = lean_uint32_shift_left(x_61, x_62);
x_64 = lean_uint8_to_uint32(x_58);
x_65 = 12;
x_66 = lean_uint32_shift_left(x_64, x_65);
x_67 = lean_uint32_lor(x_63, x_66);
x_68 = lean_uint8_to_uint32(x_59);
x_69 = 6;
x_70 = lean_uint32_shift_left(x_68, x_69);
x_71 = lean_uint32_lor(x_67, x_70);
x_72 = lean_uint8_to_uint32(x_60);
x_73 = lean_uint32_lor(x_71, x_72);
x_74 = 65536;
x_75 = lean_uint32_dec_lt(x_73, x_74);
if (x_75 == 0)
{
uint32_t x_76; uint8_t x_77; 
x_76 = 1114111;
x_77 = lean_uint32_dec_lt(x_76, x_73);
if (x_77 == 0)
{
x_13 = x_73;
goto block_19;
}
else
{
lean_object* x_78; 
lean_dec(x_12);
lean_dec_ref(x_4);
lean_dec(x_3);
x_78 = lean_box(0);
return x_78;
}
}
else
{
lean_object* x_79; 
lean_dec(x_12);
lean_dec_ref(x_4);
lean_dec(x_3);
x_79 = lean_box(0);
return x_79;
}
}
}
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_unsigned_to_nat(2u);
x_81 = lean_nat_add(x_3, x_80);
x_82 = lean_nat_dec_lt(x_81, x_7);
lean_dec(x_7);
if (x_82 == 0)
{
lean_object* x_83; 
lean_dec(x_81);
lean_dec(x_12);
lean_dec_ref(x_4);
lean_dec(x_3);
x_83 = lean_box(0);
return x_83;
}
else
{
lean_object* x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; 
x_84 = lean_nat_add(x_3, x_11);
x_85 = lean_byte_array_fget(x_1, x_84);
lean_dec(x_84);
x_86 = lean_uint8_land(x_85, x_27);
x_87 = lean_uint8_dec_eq(x_86, x_21);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_81);
lean_dec(x_12);
lean_dec_ref(x_4);
lean_dec(x_3);
x_88 = lean_box(0);
return x_88;
}
else
{
uint8_t x_89; uint8_t x_90; uint8_t x_91; 
x_89 = lean_byte_array_fget(x_1, x_81);
lean_dec(x_81);
x_90 = lean_uint8_land(x_89, x_27);
x_91 = lean_uint8_dec_eq(x_90, x_21);
if (x_91 == 0)
{
lean_object* x_92; 
lean_dec(x_12);
lean_dec_ref(x_4);
lean_dec(x_3);
x_92 = lean_box(0);
return x_92;
}
else
{
uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint32_t x_98; uint32_t x_99; uint32_t x_100; uint32_t x_101; uint32_t x_102; uint32_t x_103; uint32_t x_104; uint32_t x_105; uint32_t x_106; uint32_t x_107; uint8_t x_108; 
x_93 = 15;
x_94 = lean_uint8_land(x_20, x_93);
x_95 = 63;
x_96 = lean_uint8_land(x_85, x_95);
x_97 = lean_uint8_land(x_89, x_95);
x_98 = lean_uint8_to_uint32(x_94);
x_99 = 12;
x_100 = lean_uint32_shift_left(x_98, x_99);
x_101 = lean_uint8_to_uint32(x_96);
x_102 = 6;
x_103 = lean_uint32_shift_left(x_101, x_102);
x_104 = lean_uint32_lor(x_100, x_103);
x_105 = lean_uint8_to_uint32(x_97);
x_106 = lean_uint32_lor(x_104, x_105);
x_107 = 2048;
x_108 = lean_uint32_dec_lt(x_106, x_107);
if (x_108 == 0)
{
uint32_t x_109; uint8_t x_110; 
x_109 = 55296;
x_110 = lean_uint32_dec_le(x_109, x_106);
if (x_110 == 0)
{
x_13 = x_106;
goto block_19;
}
else
{
uint32_t x_111; uint8_t x_112; 
x_111 = 57343;
x_112 = lean_uint32_dec_le(x_106, x_111);
if (x_112 == 0)
{
x_13 = x_106;
goto block_19;
}
else
{
lean_object* x_113; 
lean_dec(x_12);
lean_dec_ref(x_4);
lean_dec(x_3);
x_113 = lean_box(0);
return x_113;
}
}
}
else
{
lean_object* x_114; 
lean_dec(x_12);
lean_dec_ref(x_4);
lean_dec(x_3);
x_114 = lean_box(0);
return x_114;
}
}
}
}
}
}
else
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_nat_add(x_3, x_11);
x_116 = lean_nat_dec_lt(x_115, x_7);
lean_dec(x_7);
if (x_116 == 0)
{
lean_object* x_117; 
lean_dec(x_115);
lean_dec(x_12);
lean_dec_ref(x_4);
lean_dec(x_3);
x_117 = lean_box(0);
return x_117;
}
else
{
uint8_t x_118; uint8_t x_119; uint8_t x_120; 
x_118 = lean_byte_array_fget(x_1, x_115);
lean_dec(x_115);
x_119 = lean_uint8_land(x_118, x_27);
x_120 = lean_uint8_dec_eq(x_119, x_21);
if (x_120 == 0)
{
lean_object* x_121; 
lean_dec(x_12);
lean_dec_ref(x_4);
lean_dec(x_3);
x_121 = lean_box(0);
return x_121;
}
else
{
uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint32_t x_126; uint32_t x_127; uint32_t x_128; uint32_t x_129; uint32_t x_130; uint32_t x_131; uint8_t x_132; 
x_122 = 31;
x_123 = lean_uint8_land(x_20, x_122);
x_124 = 63;
x_125 = lean_uint8_land(x_118, x_124);
x_126 = lean_uint8_to_uint32(x_123);
x_127 = 6;
x_128 = lean_uint32_shift_left(x_126, x_127);
x_129 = lean_uint8_to_uint32(x_125);
x_130 = lean_uint32_lor(x_128, x_129);
x_131 = 128;
x_132 = lean_uint32_dec_lt(x_130, x_131);
if (x_132 == 0)
{
x_13 = x_130;
goto block_19;
}
else
{
lean_object* x_133; 
lean_dec(x_12);
lean_dec_ref(x_4);
lean_dec(x_3);
x_133 = lean_box(0);
return x_133;
}
}
}
}
}
else
{
uint32_t x_134; 
lean_dec(x_7);
x_134 = lean_uint8_to_uint32(x_20);
x_13 = x_134;
goto block_19;
}
block_19:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Char_utf8Size(x_13);
x_15 = lean_nat_add(x_3, x_14);
lean_dec(x_14);
lean_dec(x_3);
x_16 = lean_box_uint32(x_13);
x_17 = lean_array_push(x_4, x_16);
x_2 = x_12;
x_3 = x_15;
x_4 = x_17;
goto _start;
}
}
}
else
{
lean_object* x_135; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_4);
return x_135;
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_ByteArray_utf8Decode_x3f_go___redArg(x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_ByteArray_utf8Decode_x3f_go___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_ByteArray_utf8Decode_x3f_go(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_ByteArray_utf8Decode_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_byte_array_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_ByteArray_utf8Decode_x3f___closed__0;
x_7 = l_ByteArray_utf8Decode_x3f_go___redArg(x_1, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ByteArray_utf8Decode_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
x_6 = lean_byte_array_size(x_1);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_3, x_6);
if (x_8 == 0)
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_2, x_9);
lean_dec(x_2);
x_17 = lean_byte_array_fget(x_1, x_3);
x_18 = 128;
x_19 = lean_uint8_land(x_17, x_18);
x_20 = 0;
x_21 = lean_uint8_dec_eq(x_19, x_20);
if (x_21 == 0)
{
uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; 
x_22 = 224;
x_23 = lean_uint8_land(x_17, x_22);
x_24 = 192;
x_25 = lean_uint8_dec_eq(x_23, x_24);
if (x_25 == 0)
{
uint8_t x_26; uint8_t x_27; uint8_t x_28; 
x_26 = 240;
x_27 = lean_uint8_land(x_17, x_26);
x_28 = lean_uint8_dec_eq(x_27, x_22);
if (x_28 == 0)
{
uint8_t x_29; uint8_t x_30; uint8_t x_31; 
x_29 = 248;
x_30 = lean_uint8_land(x_17, x_29);
x_31 = lean_uint8_dec_eq(x_30, x_26);
if (x_31 == 0)
{
lean_dec(x_6);
x_11 = x_31;
goto block_16;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_unsigned_to_nat(3u);
x_33 = lean_nat_add(x_3, x_32);
x_34 = lean_nat_dec_lt(x_33, x_6);
lean_dec(x_6);
if (x_34 == 0)
{
lean_dec(x_33);
x_11 = x_28;
goto block_16;
}
else
{
lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; 
x_35 = lean_nat_add(x_3, x_9);
x_36 = lean_byte_array_fget(x_1, x_35);
lean_dec(x_35);
x_37 = lean_uint8_land(x_36, x_24);
x_38 = lean_uint8_dec_eq(x_37, x_18);
if (x_38 == 0)
{
lean_dec(x_33);
x_11 = x_38;
goto block_16;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; 
x_39 = lean_unsigned_to_nat(2u);
x_40 = lean_nat_add(x_3, x_39);
x_41 = lean_byte_array_fget(x_1, x_40);
lean_dec(x_40);
x_42 = lean_uint8_land(x_41, x_24);
x_43 = lean_uint8_dec_eq(x_42, x_18);
if (x_43 == 0)
{
lean_dec(x_33);
x_11 = x_43;
goto block_16;
}
else
{
uint8_t x_44; uint8_t x_45; uint8_t x_46; 
x_44 = lean_byte_array_fget(x_1, x_33);
lean_dec(x_33);
x_45 = lean_uint8_land(x_44, x_24);
x_46 = lean_uint8_dec_eq(x_45, x_18);
if (x_46 == 0)
{
x_11 = x_46;
goto block_16;
}
else
{
uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint32_t x_53; uint32_t x_54; uint32_t x_55; uint32_t x_56; uint32_t x_57; uint32_t x_58; uint32_t x_59; uint32_t x_60; uint32_t x_61; uint32_t x_62; uint32_t x_63; uint32_t x_64; uint32_t x_65; uint32_t x_66; uint8_t x_67; 
x_47 = 7;
x_48 = lean_uint8_land(x_17, x_47);
x_49 = 63;
x_50 = lean_uint8_land(x_36, x_49);
x_51 = lean_uint8_land(x_41, x_49);
x_52 = lean_uint8_land(x_44, x_49);
x_53 = lean_uint8_to_uint32(x_48);
x_54 = 18;
x_55 = lean_uint32_shift_left(x_53, x_54);
x_56 = lean_uint8_to_uint32(x_50);
x_57 = 12;
x_58 = lean_uint32_shift_left(x_56, x_57);
x_59 = lean_uint32_lor(x_55, x_58);
x_60 = lean_uint8_to_uint32(x_51);
x_61 = 6;
x_62 = lean_uint32_shift_left(x_60, x_61);
x_63 = lean_uint32_lor(x_59, x_62);
x_64 = lean_uint8_to_uint32(x_52);
x_65 = lean_uint32_lor(x_63, x_64);
x_66 = 65536;
x_67 = lean_uint32_dec_le(x_66, x_65);
if (x_67 == 0)
{
x_11 = x_28;
goto block_16;
}
else
{
uint32_t x_68; uint8_t x_69; 
x_68 = 1114111;
x_69 = lean_uint32_dec_le(x_65, x_68);
if (x_69 == 0)
{
x_11 = x_28;
goto block_16;
}
else
{
x_11 = x_46;
goto block_16;
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
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_unsigned_to_nat(2u);
x_71 = lean_nat_add(x_3, x_70);
x_72 = lean_nat_dec_lt(x_71, x_6);
lean_dec(x_6);
if (x_72 == 0)
{
lean_dec(x_71);
x_11 = x_25;
goto block_16;
}
else
{
lean_object* x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; 
x_73 = lean_nat_add(x_3, x_9);
x_74 = lean_byte_array_fget(x_1, x_73);
lean_dec(x_73);
x_75 = lean_uint8_land(x_74, x_24);
x_76 = lean_uint8_dec_eq(x_75, x_18);
if (x_76 == 0)
{
lean_dec(x_71);
x_11 = x_76;
goto block_16;
}
else
{
uint8_t x_77; uint8_t x_78; uint8_t x_79; 
x_77 = lean_byte_array_fget(x_1, x_71);
lean_dec(x_71);
x_78 = lean_uint8_land(x_77, x_24);
x_79 = lean_uint8_dec_eq(x_78, x_18);
if (x_79 == 0)
{
x_11 = x_79;
goto block_16;
}
else
{
uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint32_t x_85; uint32_t x_86; uint32_t x_87; uint32_t x_88; uint32_t x_89; uint32_t x_90; uint32_t x_91; uint32_t x_92; uint32_t x_93; uint32_t x_94; uint8_t x_95; 
x_80 = 15;
x_81 = lean_uint8_land(x_17, x_80);
x_82 = 63;
x_83 = lean_uint8_land(x_74, x_82);
x_84 = lean_uint8_land(x_77, x_82);
x_85 = lean_uint8_to_uint32(x_81);
x_86 = 12;
x_87 = lean_uint32_shift_left(x_85, x_86);
x_88 = lean_uint8_to_uint32(x_83);
x_89 = 6;
x_90 = lean_uint32_shift_left(x_88, x_89);
x_91 = lean_uint32_lor(x_87, x_90);
x_92 = lean_uint8_to_uint32(x_84);
x_93 = lean_uint32_lor(x_91, x_92);
x_94 = 2048;
x_95 = lean_uint32_dec_le(x_94, x_93);
if (x_95 == 0)
{
x_11 = x_25;
goto block_16;
}
else
{
uint32_t x_96; uint8_t x_97; 
x_96 = 55296;
x_97 = lean_uint32_dec_lt(x_93, x_96);
if (x_97 == 0)
{
uint32_t x_98; uint8_t x_99; 
x_98 = 57343;
x_99 = lean_uint32_dec_lt(x_98, x_93);
if (x_99 == 0)
{
x_11 = x_25;
goto block_16;
}
else
{
x_11 = x_79;
goto block_16;
}
}
else
{
x_11 = x_79;
goto block_16;
}
}
}
}
}
}
}
else
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_nat_add(x_3, x_9);
x_101 = lean_nat_dec_lt(x_100, x_6);
lean_dec(x_6);
if (x_101 == 0)
{
lean_dec(x_100);
x_11 = x_21;
goto block_16;
}
else
{
uint8_t x_102; uint8_t x_103; uint8_t x_104; 
x_102 = lean_byte_array_fget(x_1, x_100);
lean_dec(x_100);
x_103 = lean_uint8_land(x_102, x_24);
x_104 = lean_uint8_dec_eq(x_103, x_18);
if (x_104 == 0)
{
x_11 = x_104;
goto block_16;
}
else
{
uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint32_t x_109; uint32_t x_110; uint32_t x_111; uint32_t x_112; uint32_t x_113; uint32_t x_114; uint8_t x_115; 
x_105 = 31;
x_106 = lean_uint8_land(x_17, x_105);
x_107 = 63;
x_108 = lean_uint8_land(x_102, x_107);
x_109 = lean_uint8_to_uint32(x_106);
x_110 = 6;
x_111 = lean_uint32_shift_left(x_109, x_110);
x_112 = lean_uint8_to_uint32(x_108);
x_113 = lean_uint32_lor(x_111, x_112);
x_114 = 128;
x_115 = lean_uint32_dec_le(x_114, x_113);
x_11 = x_115;
goto block_16;
}
}
}
}
else
{
lean_dec(x_6);
x_11 = x_21;
goto block_16;
}
block_16:
{
if (x_11 == 0)
{
lean_dec(x_10);
lean_dec(x_3);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_byte_array_fget(x_1, x_3);
x_13 = l_UInt8_utf8ByteSize___redArg(x_12);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_13);
lean_dec(x_3);
x_2 = x_10;
x_3 = x_14;
goto _start;
}
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
}
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_ByteArray_validateUTF8_go___redArg(x_1, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_ByteArray_validateUTF8_go___redArg(x_1, x_2, x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_ByteArray_validateUTF8_go(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_string_validate_utf8(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
x_7 = lean_apply_2(x_2, x_6, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__3_splitter___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__3_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__3_splitter___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__3_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
x_4 = lean_apply_1(x_2, lean_box(0));
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_2(x_3, x_5, lean_box(0));
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_object* x_4; 
lean_dec(x_3);
x_4 = lean_apply_1(x_2, lean_box(0));
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_apply_1(x_3, lean_box(0));
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_instDecidableIsValidUTF8(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_string_validate_utf8(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instDecidableIsValidUTF8___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_instDecidableIsValidUTF8(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_x3f(lean_object* x_1) {
_start:
{
uint8_t x_2; 
lean_inc_ref(x_1);
x_2 = lean_string_validate_utf8(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_string_from_utf8_unchecked(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
static lean_object* _init_l_String_fromUTF8_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_String_fromUTF8_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.String.Basic", 22, 22);
return x_1;
}
}
static lean_object* _init_l_String_fromUTF8_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_String_fromUTF8_x21___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
return x_1;
}
}
static lean_object* _init_l_String_fromUTF8_x21___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_String_fromUTF8_x21___closed__3;
x_2 = lean_unsigned_to_nat(46u);
x_3 = lean_unsigned_to_nat(212u);
x_4 = l_String_fromUTF8_x21___closed__2;
x_5 = l_String_fromUTF8_x21___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_x21(lean_object* x_1) {
_start:
{
uint8_t x_2; 
lean_inc_ref(x_1);
x_2 = lean_string_validate_utf8(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_dec_ref(x_1);
x_3 = l_String_fromUTF8_x21___closed__0;
x_4 = l_String_fromUTF8_x21___closed__4;
x_5 = l_panic___redArg(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_string_from_utf8_unchecked(x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_String_Internal_toArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_string_to_utf8(x_1);
x_3 = lean_byte_array_size(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_ByteArray_utf8Decode_x3f___closed__0;
x_8 = l_ByteArray_utf8Decode_x3f_go___redArg(x_2, x_5, x_6, x_7);
lean_dec_ref(x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_data___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_data(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_length___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_length(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_String_instLT() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_decidableLT___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_string_dec_lt(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_String_instLE() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_String_decLE(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; 
x_3 = lean_string_dec_lt(x_2, x_1);
x_4 = l_instDecidableNot___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_decLE___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_decLE(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_toList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_data(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValid___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_string_is_valid_pos(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsValid(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_is_valid_pos(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsValid___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_instDecidableIsValid(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_extract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_copy(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_string_utf8_extract(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_copy___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_copy(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_isValidForSlice(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_String_Slice_utf8ByteSize(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_nat_add(x_7, x_2);
x_9 = lean_string_get_byte_fast(x_6, x_8);
x_10 = l_UInt8_instDecidableIsUTF8FirstByte(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValidForSlice___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_Pos_Raw_isValidForSlice(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableIsValidForSlice(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_String_Pos_Raw_isValidForSlice(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableIsValidForSlice___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_instDecidableIsValidForSlice(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_nat_add(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_str___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pos_str(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStart(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_9 = lean_nat_add(x_7, x_2);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStart___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_replaceStart(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
lean_dec(x_5);
x_6 = lean_nat_add(x_4, x_2);
lean_ctor_set(x_1, 2, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_nat_add(x_8, x_2);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_replaceEnd(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
lean_dec(x_6);
x_7 = lean_nat_add(x_5, x_2);
x_8 = lean_nat_add(x_5, x_3);
lean_dec(x_5);
lean_ctor_set(x_1, 2, x_8);
lean_ctor_set(x_1, 1, x_7);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_nat_add(x_10, x_2);
x_12 = lean_nat_add(x_10, x_3);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
lean_dec(x_7);
x_8 = lean_nat_add(x_6, x_2);
x_9 = lean_nat_add(x_6, x_3);
lean_dec(x_6);
lean_ctor_set(x_1, 2, x_9);
lean_ctor_set(x_1, 1, x_8);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_nat_add(x_11, x_2);
x_13 = lean_nat_add(x_11, x_3);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_replaceStartEnd___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_Slice_replaceStartEnd(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_replaceStartEnd_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_String_instInhabitedSlice;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_String_Slice_replaceStartEnd_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.Slice.replaceStartEnd!", 29, 29);
return x_1;
}
}
static lean_object* _init_l_String_Slice_replaceStartEnd_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Starting position must be less than or equal to end position.", 61, 61);
return x_1;
}
}
static lean_object* _init_l_String_Slice_replaceStartEnd_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_String_Slice_replaceStartEnd_x21___closed__1;
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_unsigned_to_nat(981u);
x_4 = l_String_Slice_replaceStartEnd_x21___closed__0;
x_5 = l_String_fromUTF8_x21___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_le(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec_ref(x_1);
x_5 = l_String_Slice_replaceStartEnd_x21___closed__2;
x_6 = l_panic___at___00String_Slice_replaceStartEnd_x21_spec__0(x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
lean_dec(x_9);
x_10 = lean_nat_add(x_8, x_2);
x_11 = lean_nat_add(x_8, x_3);
lean_dec(x_8);
lean_ctor_set(x_1, 2, x_11);
lean_ctor_set(x_1, 1, x_10);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_nat_add(x_13, x_2);
x_15 = lean_nat_add(x_13, x_3);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_replaceStartEnd_x21(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_decodeChar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_string_utf8_get(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box_uint32(x_4);
return x_5;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint32_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_nat_add(x_4, x_2);
x_6 = lean_string_utf8_get(x_3, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint32_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_nat_add(x_5, x_2);
x_7 = lean_string_utf8_get(x_4, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = l_String_Slice_Pos_get___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = l_String_Slice_Pos_get(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box_uint32(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_String_Slice_utf8ByteSize(x_1);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_nat_add(x_6, x_2);
x_8 = lean_string_utf8_get(x_5, x_7);
lean_dec(x_7);
x_9 = lean_box_uint32(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pos_get_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 65;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT uint32_t l_panic___at___00String_Slice_Pos_get_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint32_t x_4; 
x_2 = l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1;
x_3 = lean_panic_fn(x_2, x_1);
x_4 = lean_unbox_uint32(x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_String_Slice_Pos_get_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.Slice.Pos.get!", 21, 21);
return x_1;
}
}
static lean_object* _init_l_String_Slice_Pos_get_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cannot retrieve character at end position", 41, 41);
return x_1;
}
}
static lean_object* _init_l_String_Slice_Pos_get_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_String_Slice_Pos_get_x21___closed__1;
x_2 = lean_unsigned_to_nat(29u);
x_3 = lean_unsigned_to_nat(1057u);
x_4 = l_String_Slice_Pos_get_x21___closed__0;
x_5 = l_String_fromUTF8_x21___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT uint32_t l_String_Slice_Pos_get_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_String_Slice_utf8ByteSize(x_1);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_nat_add(x_6, x_2);
x_8 = lean_string_utf8_get(x_5, x_7);
lean_dec(x_7);
return x_8;
}
else
{
lean_object* x_9; uint32_t x_10; 
x_9 = l_String_Slice_Pos_get_x21___closed__2;
x_10 = l_panic___at___00String_Slice_Pos_get_x21_spec__0(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_panic___at___00String_Slice_Pos_get_x21_spec__0(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = l_String_Slice_Pos_get_x21(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_toSlice___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_toSlice(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_toSlice___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_ValidPos_toSlice___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_toSlice___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_ValidPos_toSlice(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_Pos_ofSlice___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pos_ofSlice(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint32_t l_String_ValidPos_get___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; 
x_3 = lean_string_utf8_get(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t l_String_ValidPos_get(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; 
x_4 = lean_string_utf8_get(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_get___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = l_String_ValidPos_get___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_get___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = l_String_ValidPos_get(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box_uint32(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_get_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_Pos_get_x3f(x_5, x_2);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_get_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_ValidPos_get_x3f(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t l_String_ValidPos_get_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint32_t x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_Pos_get_x21(x_5, x_2);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_get_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = l_String_ValidPos_get_x21(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_ValidPos_byte___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_get_byte_fast(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_String_ValidPos_byte(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_get_byte_fast(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_byte___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_ValidPos_byte___redArg(x_1, x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_byte___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_ValidPos_byte(x_1, x_2, x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_ofCopy___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_ofCopy(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_ofCopy___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_ValidPos_ofCopy___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_ofCopy___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_ValidPos_ofCopy(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_Pos_toCopy___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pos_toCopy(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_nat_add(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pos_ofReplaceStart___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_Pos_ofReplaceStart(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_nat_sub(x_3, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pos_toReplaceStart___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_Slice_Pos_toReplaceStart(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_Pos_ofReplaceEnd___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceEnd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_Pos_ofReplaceEnd(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_Pos_toReplaceEnd___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceEnd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_Slice_Pos_toReplaceEnd(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_nat_add(x_4, x_2);
x_6 = lean_string_get_byte_fast(x_3, x_5);
x_7 = l_UInt8_utf8ByteSize___redArg(x_6);
x_8 = lean_nat_add(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_Pos_next___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pos_next___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_Pos_next(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_String_Slice_utf8ByteSize(x_1);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_String_Slice_Pos_next___redArg(x_1, x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pos_next_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(x_2);
return x_3;
}
}
static lean_object* _init_l_String_Slice_Pos_next_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.Slice.Pos.next!", 22, 22);
return x_1;
}
}
static lean_object* _init_l_String_Slice_Pos_next_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cannot advance the end position", 31, 31);
return x_1;
}
}
static lean_object* _init_l_String_Slice_Pos_next_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_String_Slice_Pos_next_x21___closed__1;
x_2 = lean_unsigned_to_nat(29u);
x_3 = lean_unsigned_to_nat(1371u);
x_4 = l_String_Slice_Pos_next_x21___closed__0;
x_5 = l_String_fromUTF8_x21___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_String_Slice_utf8ByteSize(x_1);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_String_Slice_Pos_next___redArg(x_1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_String_Slice_Pos_next_x21___closed__2;
x_7 = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_next_x21_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___00String_Slice_Pos_next_x21_spec__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pos_next_x21(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_nat_add(x_4, x_2);
x_6 = lean_string_get_byte_fast(x_3, x_5);
x_7 = l_UInt8_instDecidableIsUTF8FirstByte(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_2, x_10);
lean_dec(x_2);
x_2 = x_11;
goto _start;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_Pos_prevAux_go___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pos_prevAux_go___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_Pos_prevAux_go(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
x_5 = l_String_Slice_Pos_prevAux_go___redArg(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_2, x_4);
x_6 = l_String_Slice_Pos_prevAux_go___redArg(x_1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pos_prevAux___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_Pos_prevAux(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_apply_3(x_2, lean_box(0), lean_box(0), lean_box(0));
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_apply_4(x_3, x_8, lean_box(0), lean_box(0), lean_box(0));
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(x_3, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
x_5 = l_String_Slice_Pos_prevAux_go___redArg(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_2, x_4);
x_6 = l_String_Slice_Pos_prevAux_go___redArg(x_1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pos_prev___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_Pos_prev(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = l_String_Slice_Pos_prevAux_go___redArg(x_1, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pos_prev_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_String_Slice_Pos_prev_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.Slice.Pos.prev!", 22, 22);
return x_1;
}
}
static lean_object* _init_l_String_Slice_Pos_prev_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The start position has no previous position", 43, 43);
return x_1;
}
}
static lean_object* _init_l_String_Slice_Pos_prev_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_String_Slice_Pos_prev_x21___closed__1;
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_unsigned_to_nat(1445u);
x_4 = l_String_Slice_Pos_prev_x21___closed__0;
x_5 = l_String_fromUTF8_x21___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = l_String_Slice_Pos_prevAux_go___redArg(x_1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_String_Slice_Pos_prev_x21___closed__2;
x_9 = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pos_prev_x21(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_pos___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_pos(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_String_Pos_Raw_isValidForSlice(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_pos_x3f(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_String_Slice_pos_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.Slice.pos!", 17, 17);
return x_1;
}
}
static lean_object* _init_l_String_Slice_pos_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Offset is not at a valid UTF-8 character boundary", 49, 49);
return x_1;
}
}
static lean_object* _init_l_String_Slice_pos_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_String_Slice_pos_x21___closed__1;
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_unsigned_to_nat(1470u);
x_4 = l_String_Slice_pos_x21___closed__0;
x_5 = l_String_fromUTF8_x21___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_String_Pos_Raw_isValidForSlice(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_String_Slice_pos_x21___closed__2;
x_5 = l_panic___at___00String_Slice_Pos_next_x21_spec__0___redArg(x_4);
return x_5;
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_pos_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_pos_x21(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_next___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_Pos_next___redArg(x_5, x_2);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_next(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = l_String_Slice_Pos_next___redArg(x_6, x_2);
lean_dec_ref(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_next___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_ValidPos_next___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_next___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_ValidPos_next(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_next_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_Pos_next_x3f(x_5, x_2);
lean_dec_ref(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_next_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_ValidPos_next_x3f(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_next_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_Pos_next_x21(x_5, x_2);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_next_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_ValidPos_next_x21(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_prev___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = l_String_Slice_Pos_prevAux_go___redArg(x_5, x_7);
lean_dec_ref(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_prev(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
x_9 = l_String_Slice_Pos_prevAux_go___redArg(x_6, x_8);
lean_dec_ref(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_prev___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_ValidPos_prev___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_prev___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_ValidPos_prev(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_prev_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_Pos_prev_x3f(x_5, x_2);
lean_dec_ref(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_prev_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_ValidPos_prev_x3f(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_prev_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_Pos_prev_x21(x_5, x_2);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_prev_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_ValidPos_prev_x21(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_pos(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_pos___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_pos___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_pos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_pos(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_pos_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_pos_x3f(x_5, x_2);
lean_dec_ref(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_String_pos_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_pos_x21(x_5, x_2);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_pos_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_pos_x21(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_Pos_cast___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_Slice_Pos_cast(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_cast___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_cast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_cast___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_ValidPos_cast___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_cast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_ValidPos_cast(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_findNextPos_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_String_Slice_utf8ByteSize(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_nat_add(x_6, x_2);
x_8 = lean_string_get_byte_fast(x_5, x_7);
x_9 = l_UInt8_instDecidableIsUTF8FirstByte(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
x_2 = x_11;
goto _start;
}
else
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_findNextPos_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_String_Basic_0__String_Slice_findNextPos_go(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_findNextPos___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_1, x_3);
x_5 = l___private_Init_Data_String_Basic_0__String_Slice_findNextPos_go(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_findNextPos(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_1, x_4);
x_6 = l___private_Init_Data_String_Basic_0__String_Slice_findNextPos_go(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_findNextPos___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_findNextPos___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_findNextPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_findNextPos(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_6 = l_String_Slice_utf8ByteSize(x_1);
x_7 = lean_nat_dec_eq(x_2, x_6);
lean_dec(x_6);
x_8 = l_instDecidableNot___redArg(x_7);
if (x_8 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_3);
x_11 = l_String_Slice_Pos_next___redArg(x_1, x_2);
lean_dec(x_2);
x_2 = x_11;
x_3 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_Pos_nextn(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_6; uint8_t x_7; 
x_6 = lean_nat_dec_eq(x_2, x_4);
x_7 = l_instDecidableNot___redArg(x_6);
if (x_7 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_10 = lean_nat_sub(x_2, x_8);
lean_dec(x_2);
x_11 = l_String_Slice_Pos_prevAux_go___redArg(x_1, x_10);
x_2 = x_11;
x_3 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_Pos_prevn(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT uint32_t l_String_Pos_Raw_utf8GetAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint32_t x_4; 
lean_dec(x_2);
x_4 = 65;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_nat_dec_eq(x_2, x_3);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unbox_uint32(x_5);
x_9 = l_Char_utf8Size(x_8);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_9);
lean_dec(x_2);
x_1 = x_6;
x_2 = x_10;
goto _start;
}
else
{
uint32_t x_12; 
lean_dec(x_2);
x_12 = lean_unbox_uint32(x_5);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = l_String_Pos_Raw_utf8GetAux(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box_uint32(x_4);
return x_5;
}
}
LEAN_EXPORT uint32_t l_String_utf8GetAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; 
x_4 = l_String_Pos_Raw_utf8GetAux(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = l_String_utf8GetAux(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box_uint32(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_string_utf8_get(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_get___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_string_utf8_get(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_nat_dec_eq(x_2, x_3);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unbox_uint32(x_5);
x_9 = l_Char_utf8Size(x_8);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_9);
lean_dec(x_2);
x_1 = x_6;
x_2 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
lean_dec(x_2);
lean_inc(x_5);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_5);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8GetAux_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Pos_Raw_utf8GetAux_x3f(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Pos_Raw_utf8GetAux_x3f(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_utf8GetAux_x3f(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_utf8_get_opt(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_get_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_utf8_get_opt(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_string_utf8_get_bang(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_get_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_string_utf8_get_bang(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_2;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_nat_dec_eq(x_3, x_4);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_unbox_uint32(x_6);
x_10 = l_Char_utf8Size(x_9);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_10);
x_12 = l_String_Pos_Raw_utf8SetAux(x_1, x_7, x_11, x_4);
lean_dec(x_11);
lean_ctor_set(x_2, 1, x_12);
return x_2;
}
else
{
lean_object* x_13; 
lean_dec(x_6);
x_13 = lean_box_uint32(x_1);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_16 = lean_nat_dec_eq(x_3, x_4);
if (x_16 == 0)
{
uint32_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_unbox_uint32(x_14);
x_18 = l_Char_utf8Size(x_17);
x_19 = lean_nat_add(x_3, x_18);
lean_dec(x_18);
x_20 = l_String_Pos_Raw_utf8SetAux(x_1, x_15, x_19, x_4);
lean_dec(x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_14);
x_22 = lean_box_uint32(x_1);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8SetAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_6 = l_String_Pos_Raw_utf8SetAux(x_5, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_Pos_Raw_utf8SetAux(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_utf8SetAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_6 = l_String_utf8SetAux(x_5, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_replaceEnd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_replaceStart(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_next___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_unbox_uint32(x_6);
x_9 = l_Char_utf8Size(x_8);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_9);
x_11 = lean_nat_dec_le(x_3, x_10);
if (x_11 == 0)
{
lean_dec(x_2);
x_1 = x_7;
x_2 = x_10;
goto _start;
}
else
{
lean_dec(x_10);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_utf8PrevAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Pos_Raw_utf8PrevAux(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Pos_Raw_utf8PrevAux(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_utf8PrevAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_utf8PrevAux(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_prev___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_utf8_prev(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_prev___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_utf8_prev(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint32_t l_String_front(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_front___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_String_front(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t lean_string_front(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Internal_frontImpl___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_string_front(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t l_String_back(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint32_t x_4; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = lean_string_utf8_prev(x_1, x_2);
lean_dec(x_2);
x_4 = lean_string_utf8_get(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_back___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_String_back(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_atEnd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_string_utf8_at_end(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_atEnd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_string_utf8_at_end(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_string_utf8_get_fast(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box_uint32(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_get_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_string_utf8_get_fast(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box_uint32(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_next_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_string_utf8_next_fast(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_next_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_string_utf8_next_fast(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
x_6 = lean_apply_2(x_4, x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_4(x_5, x_7, x_8, x_2, x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_String_Basic_0__String_Pos_Raw_utf8GetAux_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_posOfAux(lean_object* x_1, uint32_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
return x_4;
}
else
{
uint32_t x_6; uint8_t x_7; 
x_6 = lean_string_utf8_get(x_1, x_4);
x_7 = lean_uint32_dec_eq(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_String_posOfAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_6 = l_String_posOfAux(x_1, x_5, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_posOf(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_String_posOfAux(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_posOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_String_posOf(x_1, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_string_posof(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_String_posOfAux(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Internal_posOfImpl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = lean_string_posof(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_revPosOfAux(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_prev(x_1, x_3);
lean_dec(x_3);
x_7 = lean_string_utf8_get(x_1, x_6);
x_8 = lean_uint32_dec_eq(x_7, x_2);
if (x_8 == 0)
{
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
}
else
{
lean_object* x_11; 
lean_dec(x_3);
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_String_revPosOfAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_String_revPosOfAux(x_1, x_4, x_3);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_revPosOf(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = l_String_revPosOfAux(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_revPosOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_String_revPosOf(x_1, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_findAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec_ref(x_2);
return x_4;
}
else
{
uint32_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_string_utf8_get(x_1, x_4);
x_7 = lean_box_uint32(x_6);
lean_inc_ref(x_2);
x_8 = lean_apply_1(x_2, x_7);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
else
{
lean_dec_ref(x_2);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_String_findAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_findAux(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_find(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_String_findAux(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_find___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_find(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_revFindAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_string_utf8_prev(x_1, x_3);
lean_dec(x_3);
x_7 = lean_string_utf8_get(x_1, x_6);
x_8 = lean_box_uint32(x_7);
lean_inc_ref(x_2);
x_9 = lean_apply_1(x_2, x_8);
x_10 = lean_unbox(x_9);
if (x_10 == 0)
{
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_12; 
lean_dec_ref(x_2);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_6);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_13 = lean_box(0);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_String_revFindAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_revFindAux(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_revFind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = l_String_revFindAux(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_revFind___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_revFind(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
return x_4;
}
else
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get(x_1, x_4);
x_7 = lean_string_utf8_get(x_2, x_4);
x_8 = lean_uint32_dec_eq(x_6, x_7);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; 
x_9 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
x_4 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_firstDiffPos_loop(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_string_utf8_byte_size(x_1);
x_8 = lean_string_utf8_byte_size(x_2);
x_9 = lean_nat_dec_le(x_7, x_8);
if (x_9 == 0)
{
lean_dec(x_7);
x_3 = x_8;
goto block_6;
}
else
{
lean_dec(x_8);
x_3 = x_7;
goto block_6;
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_String_firstDiffPos_loop(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_String_firstDiffPos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_firstDiffPos(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_1;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_nat_dec_eq(x_2, x_3);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unbox_uint32(x_5);
x_9 = l_Char_utf8Size(x_8);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_9);
x_11 = l_String_Pos_Raw_extract_go_u2082(x_6, x_10, x_3);
lean_dec(x_10);
lean_ctor_set(x_1, 1, x_11);
return x_1;
}
else
{
lean_object* x_12; 
lean_free_object(x_1);
lean_dec(x_6);
lean_dec(x_5);
x_12 = lean_box(0);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = lean_nat_dec_eq(x_2, x_3);
if (x_15 == 0)
{
uint32_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_unbox_uint32(x_13);
x_17 = l_Char_utf8Size(x_16);
x_18 = lean_nat_add(x_2, x_17);
lean_dec(x_17);
x_19 = l_String_Pos_Raw_extract_go_u2082(x_14, x_18, x_3);
lean_dec(x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_13);
x_21 = lean_box(0);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Pos_Raw_extract_go_u2082(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_nat_dec_eq(x_2, x_3);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_6);
lean_inc(x_5);
lean_dec_ref(x_1);
x_8 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_9 = l_Char_utf8Size(x_8);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_9);
lean_dec(x_2);
x_1 = x_6;
x_2 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = l_String_Pos_Raw_extract_go_u2082(x_1, x_2, x_4);
lean_dec(x_2);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_Pos_Raw_extract_go_u2081(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_extract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_splitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_4);
if (x_6 == 0)
{
uint32_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_string_utf8_get(x_1, x_4);
x_8 = lean_box_uint32(x_7);
lean_inc_ref(x_2);
x_9 = lean_apply_1(x_2, x_8);
x_10 = lean_unbox(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_string_utf8_next(x_1, x_4);
x_14 = lean_string_utf8_extract(x_1, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
lean_inc(x_13);
x_3 = x_13;
x_4 = x_13;
x_5 = x_15;
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_2);
x_17 = lean_string_utf8_extract(x_1, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
x_19 = l_List_reverse___redArg(x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_String_splitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_splitAux(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_splitToList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_box(0);
x_5 = l_String_splitAux(x_1, x_2, x_3, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_splitToList___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_splitToList(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_split(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_box(0);
x_5 = l_String_splitAux(x_1, x_2, x_3, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_split___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_split(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_splitOnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_string_utf8_at_end(x_1, x_4);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get(x_1, x_4);
x_9 = lean_string_utf8_get(x_2, x_5);
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_nat_sub(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
x_12 = lean_string_utf8_next(x_1, x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_4 = x_12;
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
x_16 = lean_string_utf8_next(x_2, x_5);
lean_dec(x_5);
x_17 = lean_string_utf8_at_end(x_2, x_16);
if (x_17 == 0)
{
x_4 = x_15;
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_sub(x_15, x_16);
lean_dec(x_16);
x_21 = lean_string_utf8_extract(x_1, x_3, x_20);
lean_dec(x_20);
lean_dec(x_3);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
lean_inc(x_15);
x_3 = x_15;
x_4 = x_15;
x_5 = x_19;
x_6 = x_22;
goto _start;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_5);
x_24 = lean_string_utf8_extract(x_1, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_6);
x_26 = l_List_reverse___redArg(x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_String_splitOnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_String_splitOnAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_splitOn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_String_fromUTF8_x21___closed__0;
x_4 = lean_string_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = l_String_splitOnAux(x_1, x_2, x_5, x_5, x_5, x_6);
lean_dec_ref(x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_String_splitOn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_splitOn(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPosAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_2, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_4, x_8);
lean_dec(x_4);
x_3 = x_7;
x_4 = x_9;
goto _start;
}
else
{
lean_dec(x_3);
return x_4;
}
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPosAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_offsetOfPosAux(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_offsetOfPosAux(x_1, x_2, x_3, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_offsetOfPos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_offsetOfPos(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_string_offsetofpos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_offsetOfPosAux(x_1, x_2, x_3, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_string_utf8_next(x_2, x_4);
x_8 = lean_string_utf8_get(x_2, x_4);
lean_dec(x_4);
x_9 = lean_box_uint32(x_8);
lean_inc(x_1);
x_10 = lean_apply_2(x_1, x_5, x_9);
x_4 = x_7;
x_5 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_String_foldlAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_String_foldlAux___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_foldlAux___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_String_foldlAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_foldl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_string_utf8_byte_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_String_foldlAux___redArg(x_1, x_3, x_4, x_5, x_2);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_foldl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_string_utf8_byte_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_String_foldlAux___redArg(x_2, x_4, x_5, x_6, x_3);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_foldl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_foldl___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_foldl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_foldl(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at___00String_Internal_foldlImpl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_string_utf8_next(x_2, x_4);
x_8 = lean_string_utf8_get(x_2, x_4);
lean_dec(x_4);
x_9 = lean_box_uint32(x_8);
lean_inc_ref(x_1);
x_10 = lean_apply_2(x_1, x_5, x_9);
x_4 = x_7;
x_5 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lean_string_foldl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_string_utf8_byte_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_String_foldlAux___at___00String_Internal_foldlImpl_spec__0(x_1, x_3, x_4, x_5, x_2);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at___00String_Internal_foldlImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_foldlAux___at___00String_Internal_foldlImpl_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_foldrAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_string_utf8_prev(x_3, x_4);
lean_dec(x_4);
x_8 = lean_string_utf8_get(x_3, x_7);
x_9 = lean_box_uint32(x_8);
lean_inc(x_1);
x_10 = lean_apply_2(x_1, x_9, x_2);
x_2 = x_10;
x_4 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_String_foldrAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_String_foldrAux___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_foldrAux___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_foldrAux___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_foldrAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_String_foldrAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_foldr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_string_utf8_byte_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_String_foldrAux___redArg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_foldr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_string_utf8_byte_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_String_foldrAux___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_foldr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_foldr___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_foldr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_foldr(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_String_anyAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_2);
if (x_5 == 0)
{
lean_dec(x_4);
lean_dec_ref(x_3);
return x_5;
}
else
{
uint32_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_string_utf8_get(x_1, x_4);
x_7 = lean_box_uint32(x_6);
lean_inc_ref(x_3);
x_8 = lean_apply_1(x_3, x_7);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_12 = lean_unbox(x_8);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_String_anyAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_String_anyAux(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_String_any(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_String_anyAux(x_1, x_3, x_2, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_any___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_any(x_1, x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at___00String_Internal_anyImpl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_4);
lean_dec_ref(x_1);
return x_5;
}
else
{
uint32_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_string_utf8_get(x_2, x_4);
x_7 = lean_box_uint32(x_6);
lean_inc_ref(x_1);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_4);
lean_dec_ref(x_1);
x_12 = lean_unbox(x_8);
return x_12;
}
}
}
}
LEAN_EXPORT uint8_t lean_string_any(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_String_anyAux___at___00String_Internal_anyImpl_spec__0(x_2, x_1, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at___00String_Internal_anyImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_String_anyAux___at___00String_Internal_anyImpl_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Internal_anyImpl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_string_any(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_all___lam__0(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_box_uint32(x_2);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_unbox(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT uint8_t l_String_all(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_alloc_closure((void*)(l_String_all___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_String_anyAux(x_1, x_4, x_3, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_String_all___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_String_all___lam__0(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_all___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_all(x_1, x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_contains___lam__0(uint32_t x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint32_dec_eq(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_String_contains(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_box_uint32(x_2);
x_4 = lean_alloc_closure((void*)(l_String_contains___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_String_anyAux(x_1, x_5, x_4, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_contains___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_String_contains___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_String_contains(x_1, x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at___00String_Internal_containsImpl_spec__0(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
uint32_t x_6; uint8_t x_7; 
x_6 = lean_string_utf8_get(x_2, x_4);
x_7 = lean_uint32_dec_eq(x_6, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_8;
goto _start;
}
else
{
lean_dec(x_4);
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t lean_string_contains(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_String_anyAux___at___00String_Internal_containsImpl_spec__0(x_2, x_1, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at___00String_Internal_containsImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_6 = l_String_anyAux___at___00String_Internal_containsImpl_spec__0(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_Internal_containsImpl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = lean_string_contains(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_String_isNat___lam__0(uint8_t x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; uint32_t x_6; uint8_t x_7; 
x_6 = 48;
x_7 = lean_uint32_dec_le(x_6, x_2);
if (x_7 == 0)
{
x_3 = x_7;
goto block_5;
}
else
{
uint32_t x_8; uint8_t x_9; 
x_8 = 57;
x_9 = lean_uint32_dec_le(x_2, x_8);
x_3 = x_9;
goto block_5;
}
block_5:
{
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
return x_1;
}
}
}
}
LEAN_EXPORT uint8_t l_String_isNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_box(x_4);
x_6 = lean_alloc_closure((void*)(l_String_isNat___lam__0___boxed), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = l_String_anyAux(x_1, x_2, x_6, x_3);
lean_dec(x_2);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
return x_4;
}
}
else
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = 0;
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_String_isNat___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_String_isNat___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_isNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_isNat(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at___00String_toNat_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_string_utf8_next(x_1, x_3);
x_7 = lean_string_utf8_get(x_1, x_3);
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(10u);
x_9 = lean_nat_mul(x_4, x_8);
lean_dec(x_4);
x_10 = lean_uint32_to_nat(x_7);
x_11 = lean_unsigned_to_nat(48u);
x_12 = lean_nat_sub(x_10, x_11);
lean_dec(x_10);
x_13 = lean_nat_add(x_9, x_12);
lean_dec(x_12);
lean_dec(x_9);
x_3 = x_6;
x_4 = x_13;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at___00String_toNat_x3f_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_10 = lean_string_utf8_get(x_2, x_4);
x_11 = 48;
x_12 = lean_uint32_dec_le(x_11, x_10);
if (x_12 == 0)
{
x_6 = x_12;
goto block_9;
}
else
{
uint32_t x_13; uint8_t x_14; 
x_13 = 57;
x_14 = lean_uint32_dec_le(x_10, x_13);
x_6 = x_14;
goto block_9;
}
}
block_9:
{
if (x_6 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
if (x_1 == 0)
{
lean_object* x_7; 
x_7 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_7;
goto _start;
}
else
{
lean_dec(x_4);
return x_1;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_toNat_x3f(lean_object* x_1) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_string_utf8_byte_size(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_String_anyAux___at___00String_toNat_x3f_spec__1(x_9, x_1, x_7, x_8);
lean_dec(x_7);
if (x_10 == 0)
{
goto block_6;
}
else
{
if (x_9 == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
else
{
goto block_6;
}
}
}
else
{
lean_object* x_12; 
lean_dec(x_7);
x_12 = lean_box(0);
return x_12;
}
block_6:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = l_String_foldlAux___at___00String_toNat_x3f_spec__0(x_1, x_3, x_2, x_2);
lean_dec(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at___00String_toNat_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_foldlAux___at___00String_toNat_x3f_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at___00String_toNat_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
x_6 = l_String_anyAux___at___00String_toNat_x3f_spec__1(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_toNat_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_toNat_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = 1;
return x_7;
}
else
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get(x_1, x_3);
x_9 = lean_string_utf8_get(x_2, x_4);
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Char_utf8Size(x_8);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_11);
lean_dec(x_3);
x_13 = l_Char_utf8Size(x_9);
x_14 = lean_nat_add(x_4, x_13);
lean_dec(x_13);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_substrEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_nat_add(x_2, x_5);
x_11 = lean_string_utf8_byte_size(x_1);
x_12 = lean_nat_dec_le(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
x_6 = x_12;
goto block_9;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_nat_add(x_4, x_5);
x_14 = lean_string_utf8_byte_size(x_3);
x_15 = lean_nat_dec_le(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
x_6 = x_15;
goto block_9;
}
block_9:
{
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_nat_add(x_2, x_5);
x_8 = l___private_Init_Data_String_Basic_0__String_Pos_Raw_substrEq_loop(x_1, x_3, x_2, x_4, x_7);
lean_dec(x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_substrEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_String_Pos_Raw_substrEq(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_String_substrEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_String_Pos_Raw_substrEq(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_substrEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_String_substrEq(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_String_isPrefixOf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l_String_Pos_Raw_substrEq(x_1, x_3, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_isPrefixOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_isPrefixOf(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lean_string_isprefixof(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_String_isPrefixOf(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Internal_isPrefixOfImpl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_string_isprefixof(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_findLineStart___lam__0(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 10;
x_3 = lean_uint32_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_findLineStart(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_String_findLineStart___lam__0___boxed), 1, 0);
x_4 = l_String_revFindAux(x_1, x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(0u);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_String_findLineStart___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_String_findLineStart___lam__0(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_findLineStart___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_findLineStart(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 1)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_apply_1(x_3, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
x_10 = lean_apply_2(x_4, x_9, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_4, x_2, x_3);
return x_5;
}
}
lean_object* initialize_Init_Data_String_Decode(uint8_t builtin);
lean_object* initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* initialize_Init_Data_String_PosRaw(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Lemmas(uint8_t builtin);
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
res = initialize_Init_Data_String_PosRaw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_ByteArray_utf8Decode_x3f___closed__0 = _init_l_ByteArray_utf8Decode_x3f___closed__0();
lean_mark_persistent(l_ByteArray_utf8Decode_x3f___closed__0);
l_String_fromUTF8_x21___closed__0 = _init_l_String_fromUTF8_x21___closed__0();
lean_mark_persistent(l_String_fromUTF8_x21___closed__0);
l_String_fromUTF8_x21___closed__1 = _init_l_String_fromUTF8_x21___closed__1();
lean_mark_persistent(l_String_fromUTF8_x21___closed__1);
l_String_fromUTF8_x21___closed__2 = _init_l_String_fromUTF8_x21___closed__2();
lean_mark_persistent(l_String_fromUTF8_x21___closed__2);
l_String_fromUTF8_x21___closed__3 = _init_l_String_fromUTF8_x21___closed__3();
lean_mark_persistent(l_String_fromUTF8_x21___closed__3);
l_String_fromUTF8_x21___closed__4 = _init_l_String_fromUTF8_x21___closed__4();
lean_mark_persistent(l_String_fromUTF8_x21___closed__4);
l_String_instLT = _init_l_String_instLT();
lean_mark_persistent(l_String_instLT);
l_String_instLE = _init_l_String_instLE();
lean_mark_persistent(l_String_instLE);
l_String_Slice_replaceStartEnd_x21___closed__0 = _init_l_String_Slice_replaceStartEnd_x21___closed__0();
lean_mark_persistent(l_String_Slice_replaceStartEnd_x21___closed__0);
l_String_Slice_replaceStartEnd_x21___closed__1 = _init_l_String_Slice_replaceStartEnd_x21___closed__1();
lean_mark_persistent(l_String_Slice_replaceStartEnd_x21___closed__1);
l_String_Slice_replaceStartEnd_x21___closed__2 = _init_l_String_Slice_replaceStartEnd_x21___closed__2();
lean_mark_persistent(l_String_Slice_replaceStartEnd_x21___closed__2);
l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1 = _init_l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1();
lean_mark_persistent(l_panic___at___00String_Slice_Pos_get_x21_spec__0___boxed__const__1);
l_String_Slice_Pos_get_x21___closed__0 = _init_l_String_Slice_Pos_get_x21___closed__0();
lean_mark_persistent(l_String_Slice_Pos_get_x21___closed__0);
l_String_Slice_Pos_get_x21___closed__1 = _init_l_String_Slice_Pos_get_x21___closed__1();
lean_mark_persistent(l_String_Slice_Pos_get_x21___closed__1);
l_String_Slice_Pos_get_x21___closed__2 = _init_l_String_Slice_Pos_get_x21___closed__2();
lean_mark_persistent(l_String_Slice_Pos_get_x21___closed__2);
l_String_Slice_Pos_next_x21___closed__0 = _init_l_String_Slice_Pos_next_x21___closed__0();
lean_mark_persistent(l_String_Slice_Pos_next_x21___closed__0);
l_String_Slice_Pos_next_x21___closed__1 = _init_l_String_Slice_Pos_next_x21___closed__1();
lean_mark_persistent(l_String_Slice_Pos_next_x21___closed__1);
l_String_Slice_Pos_next_x21___closed__2 = _init_l_String_Slice_Pos_next_x21___closed__2();
lean_mark_persistent(l_String_Slice_Pos_next_x21___closed__2);
l_String_Slice_Pos_prev_x21___closed__0 = _init_l_String_Slice_Pos_prev_x21___closed__0();
lean_mark_persistent(l_String_Slice_Pos_prev_x21___closed__0);
l_String_Slice_Pos_prev_x21___closed__1 = _init_l_String_Slice_Pos_prev_x21___closed__1();
lean_mark_persistent(l_String_Slice_Pos_prev_x21___closed__1);
l_String_Slice_Pos_prev_x21___closed__2 = _init_l_String_Slice_Pos_prev_x21___closed__2();
lean_mark_persistent(l_String_Slice_Pos_prev_x21___closed__2);
l_String_Slice_pos_x21___closed__0 = _init_l_String_Slice_pos_x21___closed__0();
lean_mark_persistent(l_String_Slice_pos_x21___closed__0);
l_String_Slice_pos_x21___closed__1 = _init_l_String_Slice_pos_x21___closed__1();
lean_mark_persistent(l_String_Slice_pos_x21___closed__1);
l_String_Slice_pos_x21___closed__2 = _init_l_String_Slice_pos_x21___closed__2();
lean_mark_persistent(l_String_Slice_pos_x21___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
