// Lean compiler output
// Module: Init.Data.String.Basic
// Imports: public import Init.Data.List.Basic public import Init.Data.Char.Basic public import Init.Data.String.Bootstrap public import Init.Data.ByteArray.Basic public import Init.Data.String.Decode import Init.Data.ByteArray.Lemmas
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
LEAN_EXPORT lean_object* l_String_Iterator_ctorIdx___boxed(lean_object*);
LEAN_EXPORT uint8_t l_String_ValidPos_byte___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_nextn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_contains___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_increaseBy___boxed(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_bang(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_isNat___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_toSlice(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_findLineStart___lam__0___boxed(lean_object*);
static lean_object* l_ByteArray_utf8Decode_x3f___closed__0;
LEAN_EXPORT lean_object* l_String_revFindAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___String_Slice_Pos_next_x21_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_utf8ByteSize_x27_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_next_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_next___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_endsWith(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_contains___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldrAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___String_Slice_replaceStartEnd_x21_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_dropWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instLTRaw;
LEAN_EXPORT lean_object* l_String_Pos_Raw_set___boxed(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_stripSuffix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_prev(lean_object*);
LEAN_EXPORT lean_object* l_String_join(lean_object*);
LEAN_EXPORT lean_object* l_Substring_dropPrefix_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_commonPrefix(lean_object*, lean_object*);
LEAN_EXPORT uint32_t lean_substring_front(lean_object*);
LEAN_EXPORT lean_object* l_String_extract_go_u2082(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Substring_atEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_prev___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_String_ValidPos_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableIsValid(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_pos(lean_object*, lean_object*, lean_object*);
static lean_object* l_Substring_trimLeft___closed__0;
LEAN_EXPORT lean_object* l_String_getUtf8Byte___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_String_instAppend___closed__0;
LEAN_EXPORT lean_object* l_instAppendString___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_String_ValidPos_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_containsImpl___boxed(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_String_Iterator_pos(lean_object*);
LEAN_EXPORT lean_object* l_String_pushn___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_endPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableEqValidPos_decEq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_next_x27___redArg(lean_object*);
static lean_object* l_Substring_extract___closed__0;
LEAN_EXPORT uint8_t l_String_instDecidableLePos___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_ofCopy___redArg(lean_object*);
LEAN_EXPORT lean_object* lean_string_offsetofpos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_toNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_findNextPos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_trimLeft(lean_object*);
lean_object* lean_string_utf8_get_opt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_repair(lean_object*);
LEAN_EXPORT lean_object* l_String_instLTPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_prev___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revFind___boxed(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_posOfImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLtValidPos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_endValidPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instLEValidPos(lean_object*);
LEAN_EXPORT lean_object* l_String_get_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableEqIterator___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_utf8GetAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_next_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_all___lam__0(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_toNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_String_revPosOfAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_nextn_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_remainingToString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_pos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_intercalate_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLeRaw___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_append___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_unoffsetBy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLeValidPos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddRaw__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddRaw;
uint32_t lean_uint8_to_uint32(uint8_t);
static lean_object* l_String_instInhabitedSlice___closed__0;
LEAN_EXPORT lean_object* l_String_instDecidableIsValid___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_str(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_trim___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_hasNext___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_extract___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_substring_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revPosOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_substring_isempty(lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableEqValidPos_decEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHSubRawChar___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_String_Slice_replaceStartEnd_x21___closed__2;
LEAN_EXPORT lean_object* l_String_set___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg___boxed(lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8_x21(lean_object*);
LEAN_EXPORT uint32_t l_String_Iterator_curr_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mkIterator(lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_data___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_str___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_ctorIdx(lean_object*);
LEAN_EXPORT uint32_t l_String_Slice_Pos_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_atEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_get_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetBy___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_trim(lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_trimRight(lean_object*);
LEAN_EXPORT uint32_t l_String_utf8GetAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_next(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_isPrefixOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_front___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_get_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_string_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_startValidPos___boxed(lean_object*);
static lean_object* l_String_fromUTF8_x21___closed__4;
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte_x21(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_contains(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_length___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t lean_substring_all(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw;
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_get___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_posOf(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_panic___at___String_Slice_Pos_next_x21_spec__0___boxed(lean_object*, lean_object*);
uint8_t lean_uint8_land(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_String_isNat___lam__0(uint8_t, uint32_t);
LEAN_EXPORT lean_object* lean_string_posof(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_set_match__1_splitter(lean_object*, lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_foldl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__3_splitter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instMinRaw;
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Substring_Internal_takeWhileImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_remainingBytes___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_remainingToString(lean_object*);
LEAN_EXPORT lean_object* l_String_instInhabitedIterator;
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_atEnd(lean_object*, lean_object*);
static lean_object* l_String_Slice_Pos_next_x21___closed__0;
LEAN_EXPORT lean_object* l_String_Pos_Raw_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_getUTF8Byte___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_findLineStart___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instMinRaw___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revFind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte_x21___boxed(lean_object*, lean_object*);
static lean_object* l_String_fromUTF8_x21___closed__2;
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_toSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_posOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Internal_frontImpl___boxed(lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_Iterator_setCurr___boxed(lean_object*, lean_object*);
static lean_object* l_String_toLower___closed__0;
LEAN_EXPORT lean_object* l_String_instMaxRaw;
LEAN_EXPORT lean_object* lean_string_intercalate(lean_object*, lean_object*);
static lean_object* l_String_Slice_Pos_prev_x21___closed__0;
LEAN_EXPORT lean_object* l_String_foldlAux___at___String_toNat_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___String_Internal_trimImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_next_x21(lean_object*, lean_object*);
static lean_object* l_String_Slice_pos_x21___closed__1;
LEAN_EXPORT lean_object* l_String_firstDiffPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_isNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_stripPrefix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_pos___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_isNat(lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_ofCopy___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Internal_beqImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddRaw___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_pos_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_modify___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_String_dropRightWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropRightWhile___boxed(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_pushn(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___String_Slice_Pos_get_x21_spec__0___boxed(lean_object*);
LEAN_EXPORT uint32_t l_String_Slice_Pos_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLtValidPos___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Internal_getImpl___boxed(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_substrEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x21(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLePos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValidForSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8GetAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_decreaseBy___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Iterator_remainingBytes_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_findLineStart___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_extract(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLtValidPos___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_String_Iterator_curr(lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_all___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_prev_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_utf8Decode_x3f_go_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_toSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8SetAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldrAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_dec___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_back___boxed(lean_object*);
LEAN_EXPORT uint8_t l_String_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_String_trimLeft___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instLEValidPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at___String_toNat_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_dropRightWhile(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_String_fromUTF8_x21___closed__1;
LEAN_EXPORT lean_object* l_String_instHAddRawChar___lam__0(lean_object*, uint32_t);
LEAN_EXPORT uint8_t l_String_decLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableIsValidForSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddRaw__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_decapitalize(lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableEqValidPos_decEq___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_string_data(lean_object*);
uint32_t l_Char_toLower(uint32_t);
LEAN_EXPORT lean_object* l_String_instInhabited__1;
LEAN_EXPORT lean_object* l_String_get_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_commonSuffix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHSubRaw___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_findNextPos___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_pos___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_instInhabitedSlice;
LEAN_EXPORT lean_object* l_String_findLineStart(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_all(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instMaxRaw___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instLE;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableIsValidUTF8(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_next(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_curr___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_toUTF8___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8_x3f(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_any___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_pos_min(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddCharRaw;
LEAN_EXPORT lean_object* l_Substring_trim(lean_object*);
LEAN_EXPORT lean_object* l_String_intercalate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_min___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instInhabitedIterator_default;
uint32_t l_Char_toUpper(uint32_t);
LEAN_EXPORT uint8_t l_String_instDecidableIsValidForSlice(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_anyAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_inc(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableIsValidUTF8___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* lean_string_foldl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhile(lean_object*, lean_object*);
static lean_object* l_String_Slice_Pos_prev_x21___closed__2;
LEAN_EXPORT lean_object* lean_string_nextwhile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_contains(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev___redArg___boxed(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_decLE___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_get_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_toIterator(lean_object*);
LEAN_EXPORT lean_object* l_String_any___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Iterator_hasNext(lean_object*);
lean_object* lean_string_utf8_get_opt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStart(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_panic___at___String_Slice_Pos_get_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize(lean_object*);
static lean_object* l_String_toUpper___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f(lean_object*, lean_object*);
static lean_object* l_String_Slice_pos_x21___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_substrEq_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_pos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_get___redArg___boxed(lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_prev(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___String_Internal_trimImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableEqValidPos___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_all(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_utf8ByteSize_x27_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_set_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_byteDistance___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_firstDiffPos(lean_object*, lean_object*);
static lean_object* l_Substring_hasBeq___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_startPos(lean_object*);
LEAN_EXPORT lean_object* l_String_takeWhile___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableEqIterator_decEq(lean_object*, lean_object*);
static lean_object* l_String_Slice_replaceStartEnd_x21___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Char_isWhitespace___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_intercalate_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___String_Slice_Pos_next_x21_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_String_Slice_pos_x21___closed__2;
LEAN_EXPORT lean_object* l_String_startValidPos(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at___String_Internal_containsImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHSubRaw___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_next_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddRaw___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_utf8ByteSize_x27_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_String_Iterator_curr_x27___redArg(lean_object*);
LEAN_EXPORT uint8_t l_String_startsWith(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_dropSuffix_x3f(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_offsetOfPosAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instInhabitedPos(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_findNextPos_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Internal_allImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_byte___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toCopy___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_find(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_substring_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_commonSuffix_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instSizeOfIterator___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLePos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddRawChar___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_trimRight___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_decodeChar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddRawSlice;
LEAN_EXPORT lean_object* l_Substring_takeRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posOfAux(lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_hasPrev___boxed(lean_object*);
LEAN_EXPORT uint32_t l_String_front(lean_object*);
LEAN_EXPORT lean_object* l_String_startsWith___boxed(lean_object*, lean_object*);
lean_object* l_Char_toLower___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Substring_foldr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instMinRaw___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_find___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_splitOn_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLtRaw___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_copy(lean_object*);
LEAN_EXPORT lean_object* l_instAppendString;
LEAN_EXPORT lean_object* l_String_ValidPos_prev_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropWhile(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte___redArg(lean_object*, lean_object*);
static lean_object* l_String_Slice_Pos_prev_x21___closed__1;
LEAN_EXPORT lean_object* l_String_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_substring_takewhile(lean_object*, lean_object*);
static lean_object* l_String_Slice_replaceStartEnd_x21___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHSubRawChar;
LEAN_EXPORT lean_object* l_String_ValidPos_ofCopy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_offsetOfPosAux(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_String_Slice_Pos_get_x21___closed__2;
LEAN_EXPORT lean_object* l_String_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeRight(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_string_isempty(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_set_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_extract_go_u2081(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_endPos(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_findNextPos___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Char_toUpper___boxed(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_toSlice___redArg___boxed(lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_hasBeq;
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_cast(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Pos_Raw_isValidForSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_copy___boxed(lean_object*);
static lean_object* l_String_Slice_getUTF8Byte_x21___closed__2;
LEAN_EXPORT lean_object* l_String_instDecidableLePos___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_splitOn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_replace___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_pushn___lam__0(uint32_t, lean_object*);
LEAN_EXPORT uint8_t l_ByteArray_validateUTF8_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStart___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLeRaw(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_firstDiffPos_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_replace_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2082___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instInhabitedValidPos___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_string_trim(lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_prevn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8SetAux(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetBy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_decreaseBy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_replace_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revPosOfAux(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT uint8_t l_String_isNat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_utf8GetAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLtValidPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHSubRaw;
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_front___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_replace_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_frontImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instLT;
LEAN_EXPORT lean_object* l_String_Pos_Raw_min(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_prev(lean_object*, lean_object*);
static lean_object* l___private_Init_Data_String_Basic_0__Substring_splitOn_loop___closed__0;
LEAN_EXPORT uint8_t l_String_anyAux___at___String_toNat_x3f_spec__1(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_toReplaceStart___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_toUpper(lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_cast___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_byte___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_dropRight(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_extract___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLeValidPos___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_modify(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_findNextPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revPosOf(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_instDecidableEqIterator_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t lean_substring_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_startPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_atEnd___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Iterator_remainingBytes_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_nextn_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instLTPos(lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLtRaw(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_next___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableEqValidPos_decEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_pos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Substring_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_toList(lean_object*);
static lean_object* l_String_fromUTF8_x21___closed__0;
LEAN_EXPORT lean_object* l_String_takeRightWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_iter(lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_nextn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_get_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_curr_x27___redArg___boxed(lean_object*);
static lean_object* l_String_Slice_Pos_get_x21___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_nextn_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_forward(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instLERaw;
LEAN_EXPORT lean_object* l_String_findAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLtPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_atEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_replace(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_substring_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_get_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_remainingBytes(lean_object*);
LEAN_EXPORT lean_object* l_String_foldr___redArg___boxed(lean_object*, lean_object*, lean_object*);
extern uint8_t l_instInhabitedUInt8;
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___String_Internal_pushnImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_panic___at___String_Slice_getUTF8Byte_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_inc___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_takeRightWhile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_capitalize(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_commonPrefix_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_get_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_curr_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___String_Slice_getUTF8Byte_x21_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___String_Internal_trimImpl_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_nextUntil(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_prev___redArg(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddCharRaw___lam__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_all___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_sameAs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_toLower(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_bang(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at___Substring_Internal_allImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_replace_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_prev_x3f___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instMaxRaw___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_prev___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_String_Basic_0__String_substrEq_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_isEmptyImpl___boxed(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Substring_toString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_extract___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_pos_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_sameAs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___String_Internal_pushnImpl_spec__0(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___at___String_Internal_foldlImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_split___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_map(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddCharRaw___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_toString(lean_object*);
LEAN_EXPORT uint32_t l_String_back(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_extract_go_u2081(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_get___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_pushn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_prevn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instLEPos(lean_object*);
LEAN_EXPORT uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__ByteArray_validateUTF8_go_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLeValidPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
LEAN_EXPORT lean_object* l_String_posOfAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___String_Slice_Pos_get_x21_spec__0___boxed__const__1;
LEAN_EXPORT uint8_t lean_string_contains(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_pos_x21___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint32_t lean_uint32_lor(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Substring_prev___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t l_UInt8_instDecidableIsUTF8FirstByte(uint8_t);
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___boxed(lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x21(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_String_Slice_Pos_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_byteDistance(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropWhile___boxed(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT uint8_t l_String_substrEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_nextWhile(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_commonSuffix_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_isNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_revFindAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_unoffsetBy___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Substring_foldl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableEqIterator(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_ValidPos_byte(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8PrevAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Substring_front(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_utf8ByteSize_x27_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_commonPrefix_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instAppend;
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0(lean_object*, lean_object*);
static lean_object* l_String_Slice_Pos_next_x21___closed__1;
LEAN_EXPORT lean_object* l_String_Pos_Raw_dec(lean_object*);
static lean_object* l_String_Slice_Pos_next_x21___closed__2;
LEAN_EXPORT lean_object* l_String_instLEPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_next(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_join___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Substring_Internal_takeWhileImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_validateUTF8___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_substring_tostring(lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___at___String_toNat_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_pushnImpl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_extract___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_endValidPos(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_isValid___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
static lean_object* l_String_instInhabitedIterator_default___closed__0;
LEAN_EXPORT lean_object* l_String_ValidPos_next___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8PrevAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_isEmpty___boxed(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT uint32_t lean_string_front(lean_object*);
LEAN_EXPORT lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instSizeOfIterator___lam__0(lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLeValidPos___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instInhabitedPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_ofCopy___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_nextUntil___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___String_Internal_trimImpl_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_dropright(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_offsetOfPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_offsetOfPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instAppendString___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_capitalize(lean_object*);
LEAN_EXPORT lean_object* lean_substring_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_findNextPos_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_next___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_String_endsWith___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_pushn(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_splitOn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_all___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_next___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_utf8Decode_x3f(lean_object*);
static lean_object* l_String_Slice_Pos_get_x21___closed__0;
LEAN_EXPORT lean_object* l_String_toNat_x3f___boxed(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_anyImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_pos_sub(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_string_isprefixof(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posOf(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableEqValidPos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLtPos___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Iterator_atEnd(lean_object*);
LEAN_EXPORT lean_object* l_String_trimRight(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_next___boxed(lean_object*, lean_object*);
static lean_object* l_String_fromUTF8_x21___closed__3;
LEAN_EXPORT lean_object* l_String_Iterator_toString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instInhabitedValidPos(lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___at___String_Internal_foldlImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableEqValidPos___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldrAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Internal_isEmptyImpl___boxed(lean_object*);
LEAN_EXPORT uint8_t l_String_anyAux___at___String_Internal_containsImpl_spec__0(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_trimLeft(lean_object*);
LEAN_EXPORT lean_object* l_String_instHSubRawChar___lam__0(lean_object*, uint32_t);
LEAN_EXPORT lean_object* lean_string_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_isEmpty___boxed(lean_object*);
LEAN_EXPORT uint32_t l_String_ValidPos_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Substring_splitOn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_prev_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitOn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replaceStartEnd(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableEqValidPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_anyAux___at___Substring_Internal_allImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_toIterator___boxed(lean_object*);
static lean_object* l_String_Slice_getUTF8Byte_x21___closed__1;
lean_object* l_Char_utf8Size(uint32_t);
LEAN_EXPORT lean_object* l_String_nextWhile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Slice_Pos_prevAux_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_next_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddRaw__1;
static lean_object* l_String_Slice_getUTF8Byte_x21___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Nat_repeat_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_prev___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_setCurr(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_Internal_isPrefixOfImpl___boxed(lean_object*, lean_object*);
static lean_object* l___private_Init_Data_String_Basic_0__Substring_splitOn_loop___closed__1;
LEAN_EXPORT lean_object* l_String_Slice_Pos_next_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHSubRawSlice;
LEAN_EXPORT lean_object* l_Substring_toString(lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_increaseBy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_extract_go_u2082___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_nextn_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_pos___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_String_Internal_toArray(lean_object*);
LEAN_EXPORT lean_object* l_String_instLTValidPos(lean_object*);
LEAN_EXPORT lean_object* l_String_extract_go_u2081___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_split(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldrAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instSizeOfIterator;
LEAN_EXPORT lean_object* l_String_Iterator_toEnd(lean_object*);
LEAN_EXPORT lean_object* l_String_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_next_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_next___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Iterator_hasPrev(lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at___String_Internal_anyImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_join___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofReplaceStart(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_findAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_decidableLT___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofSlice___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_pos___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_ValidPos_toSlice___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_splitOn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instLTValidPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddRawChar;
LEAN_EXPORT lean_object* l_String_take(lean_object*, lean_object*);
lean_object* l_UInt8_utf8ByteSize___redArg(uint8_t);
LEAN_EXPORT lean_object* l_String_pos_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitOnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_anyAux___at___String_Internal_anyImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_set_match__1_splitter___redArg(lean_object*, lean_object*, uint32_t, lean_object*);
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
LEAN_EXPORT lean_object* l_String_fromUTF8___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_from_utf8_unchecked(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_from_utf8_unchecked(x_1);
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
x_3 = lean_unsigned_to_nat(239u);
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
LEAN_EXPORT lean_object* l_String_toUTF8___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_to_utf8(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_append___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_append(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instAppendString___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_instAppendString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instAppendString___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instAppendString___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instAppendString___lam__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_utf8ByteSize_x27_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_2(x_3, x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_utf8ByteSize_x27_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Basic_0__String_utf8ByteSize_x27_go_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_utf8ByteSize_x27_go_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_String_Basic_0__String_utf8ByteSize_x27_go_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_utf8ByteSize_x27_go_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Basic_0__String_utf8ByteSize_x27_go_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRaw___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_string_utf8_byte_size(x_2);
x_4 = lean_nat_sub(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_String_instHSubRaw() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_instHSubRaw___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRaw___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_instHSubRaw___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawChar___lam__0(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Char_utf8Size(x_2);
x_4 = lean_nat_sub(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_String_instHSubRawChar() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_instHSubRawChar___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawChar___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_String_instHSubRawChar___lam__0(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_string_pos_sub(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_sub(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawChar___lam__0(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Char_utf8Size(x_2);
x_4 = lean_nat_add(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_String_instHAddRawChar() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_instHAddRawChar___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawChar___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_String_instHAddRawChar___lam__0(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instHAddCharRaw___lam__0(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Char_utf8Size(x_1);
x_4 = lean_nat_add(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_String_instHAddCharRaw() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_instHAddCharRaw___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_instHAddCharRaw___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_String_instHAddCharRaw___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRaw___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_nat_add(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_String_instHAddRaw() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_instHAddRaw___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRaw___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_instHAddRaw___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRaw__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_string_utf8_byte_size(x_2);
x_4 = lean_nat_add(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_String_instHAddRaw__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_instHAddRaw__1___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRaw__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_instHAddRaw__1___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_String_instLERaw() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_String_instLTRaw() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLeRaw(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_le(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLeRaw___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_instDecidableLeRaw(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtRaw(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtRaw___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_instDecidableLtRaw(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instMinRaw___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
static lean_object* _init_l_String_instMinRaw() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_instMinRaw___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_instMinRaw___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_instMinRaw___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instMaxRaw___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
static lean_object* _init_l_String_instMaxRaw() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_instMaxRaw___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_instMaxRaw___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_instMaxRaw___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
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
LEAN_EXPORT lean_object* l_String_Pos_Raw_byteDistance(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_byteDistance___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Pos_Raw_byteDistance(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_getUTF8Byte___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_string_get_byte_fast(x_1, x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_getUtf8Byte___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_string_get_byte_fast(x_1, x_2);
x_5 = lean_box(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_String_ValidPos_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_ValidPos_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_ValidPos_ctorIdx(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqValidPos_decEq___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqValidPos_decEq(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqValidPos_decEq___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_instDecidableEqValidPos_decEq___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqValidPos_decEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_instDecidableEqValidPos_decEq(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqValidPos___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqValidPos(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqValidPos___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_instDecidableEqValidPos___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqValidPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_instDecidableEqValidPos(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_startValidPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_startValidPos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedValidPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedValidPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_instInhabitedValidPos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_endValidPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_endValidPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_endValidPos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instLEValidPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instLEValidPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_instLEValidPos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instLTValidPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instLTValidPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_instLTValidPos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLeValidPos___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_le(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLeValidPos(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_le(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLeValidPos___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_instDecidableLeValidPos___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLeValidPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_instDecidableLeValidPos(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtValidPos___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtValidPos(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtValidPos___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_instDecidableLtValidPos___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtValidPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_instDecidableLtValidPos(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_String_instInhabitedSlice___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_String_fromUTF8_x21___closed__0;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_String_instInhabitedSlice() {
_start:
{
lean_object* x_1; 
x_1 = l_String_instInhabitedSlice___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_toSlice(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_nat_sub(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_utf8ByteSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_utf8ByteSize(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_String_Slice_utf8ByteSize(x_2);
x_4 = lean_nat_add(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_String_instHAddRawSlice() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_instHAddRawSlice___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawSlice___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_instHAddRawSlice___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_String_Slice_utf8ByteSize(x_1);
x_4 = lean_nat_add(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_String_instHAddSliceRaw() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_instHAddSliceRaw___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_instHAddSliceRaw___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_instHAddSliceRaw___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_String_Slice_utf8ByteSize(x_2);
x_4 = lean_nat_sub(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_String_instHSubRawSlice() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_instHSubRawSlice___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawSlice___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_instHSubRawSlice___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_utf8ByteSize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_rawEndPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_rawEndPos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetBy(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_add(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetBy___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Pos_Raw_offsetBy(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_unoffsetBy(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_unoffsetBy___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Pos_Raw_unoffsetBy(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_nat_add(x_4, x_2);
x_6 = lean_string_get_byte_fast(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_nat_add(x_5, x_2);
x_7 = lean_string_get_byte_fast(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_Slice_getUTF8Byte___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_Slice_getUTF8Byte(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_panic___at___String_Slice_getUTF8Byte_x21_spec__0(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l_instInhabitedUInt8;
x_3 = lean_box(x_2);
x_4 = lean_panic_fn(x_3, x_1);
x_5 = lean_unbox(x_4);
return x_5;
}
}
static lean_object* _init_l_String_Slice_getUTF8Byte_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.Slice.getUTF8Byte!", 25, 25);
return x_1;
}
}
static lean_object* _init_l_String_Slice_getUTF8Byte_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String slice access is out of bounds.", 37, 37);
return x_1;
}
}
static lean_object* _init_l_String_Slice_getUTF8Byte_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_String_Slice_getUTF8Byte_x21___closed__1;
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_unsigned_to_nat(1188u);
x_4 = l_String_Slice_getUTF8Byte_x21___closed__0;
x_5 = l_String_fromUTF8_x21___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_String_Slice_getUTF8Byte_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_String_Slice_utf8ByteSize(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_String_Slice_getUTF8Byte_x21___closed__2;
x_6 = l_panic___at___String_Slice_getUTF8Byte_x21_spec__0(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_nat_add(x_8, x_2);
x_10 = lean_string_get_byte_fast(x_7, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___String_Slice_getUTF8Byte_x21_spec__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_panic___at___String_Slice_getUTF8Byte_x21_spec__0(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_getUTF8Byte_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_Slice_getUTF8Byte_x21(x_1, x_2);
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
LEAN_EXPORT lean_object* l_String_Slice_Pos_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pos_ctorIdx(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos_decEq(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_Slice_instDecidableEqPos_decEq___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos_decEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_Slice_instDecidableEqPos_decEq(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableEqPos(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_Slice_instDecidableEqPos___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableEqPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_Slice_instDecidableEqPos(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_startPos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instInhabitedPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_instInhabitedPos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_utf8ByteSize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_endPos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instLEPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_instLEPos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instLTPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_instLTPos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_le(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLePos(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_le(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_instDecidableLePos___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLePos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_instDecidableLePos(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtPos(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_instDecidableLtPos___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_instDecidableLtPos(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
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
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_nat_add(x_4, x_2);
x_6 = lean_string_get_byte_fast(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pos_byte(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_nat_add(x_5, x_2);
x_7 = lean_string_get_byte_fast(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_Slice_Pos_byte___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_byte___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_Slice_Pos_byte(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_panic___at___String_Slice_replaceStartEnd_x21_spec__0(lean_object* x_1) {
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
x_3 = lean_unsigned_to_nat(1518u);
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
x_6 = l_panic___at___String_Slice_replaceStartEnd_x21_spec__0(x_5);
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
static lean_object* _init_l_panic___at___String_Slice_Pos_get_x21_spec__0___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 65;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT uint32_t l_panic___at___String_Slice_Pos_get_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint32_t x_4; 
x_2 = l_panic___at___String_Slice_Pos_get_x21_spec__0___boxed__const__1;
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
x_3 = lean_unsigned_to_nat(1599u);
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
x_10 = l_panic___at___String_Slice_Pos_get_x21_spec__0(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___String_Slice_Pos_get_x21_spec__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_panic___at___String_Slice_Pos_get_x21_spec__0(x_1);
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
LEAN_EXPORT lean_object* l_String_Pos_Raw_increaseBy(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_increaseBy___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Pos_Raw_increaseBy(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_decreaseBy(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_decreaseBy___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Pos_Raw_decreaseBy(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
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
LEAN_EXPORT lean_object* l_panic___at___String_Slice_Pos_next_x21_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___String_Slice_Pos_next_x21_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___String_Slice_Pos_next_x21_spec__0___redArg(x_2);
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
x_3 = lean_unsigned_to_nat(1972u);
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
x_7 = l_panic___at___String_Slice_Pos_next_x21_spec__0___redArg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___String_Slice_Pos_next_x21_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___String_Slice_Pos_next_x21_spec__0(x_1, x_2);
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
LEAN_EXPORT lean_object* l_String_Pos_Raw_inc(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_inc___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Pos_Raw_inc(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_dec(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_dec___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Pos_Raw_dec(x_1);
lean_dec(x_1);
return x_2;
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
x_3 = lean_unsigned_to_nat(2057u);
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
x_9 = l_panic___at___String_Slice_Pos_next_x21_spec__0___redArg(x_8);
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
x_3 = lean_unsigned_to_nat(2082u);
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
x_5 = l_panic___at___String_Slice_Pos_next_x21_spec__0___redArg(x_4);
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
LEAN_EXPORT uint32_t l_String_utf8GetAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_String_utf8GetAux_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_String_utf8SetAux(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_12 = l_String_utf8SetAux(x_1, x_7, x_11, x_4);
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
x_20 = l_String_utf8SetAux(x_1, x_15, x_19, x_4);
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
LEAN_EXPORT lean_object* l_String_Pos_Raw_set___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_5 = lean_string_utf8_set(x_1, x_2, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_set___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_5 = lean_string_utf8_set(x_1, x_2, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_modify(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; 
x_4 = lean_string_utf8_get(x_1, x_2);
x_5 = lean_box_uint32(x_4);
x_6 = lean_apply_1(x_3, x_5);
x_7 = lean_unbox_uint32(x_6);
lean_dec(x_6);
x_8 = lean_string_utf8_set(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_modify___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_modify(x_1, x_2, x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_String_utf8PrevAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_utf8GetAux_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_utf8GetAux_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_String_Basic_0__String_utf8GetAux_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l_String_Pos_Raw_min(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_min___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Pos_Raw_min(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_string_pos_min(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_dec(x_2);
return x_1;
}
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
LEAN_EXPORT lean_object* l_String_extract_go_u2082(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = l_String_extract_go_u2082(x_6, x_10, x_3);
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
x_19 = l_String_extract_go_u2082(x_14, x_18, x_3);
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
LEAN_EXPORT lean_object* l_String_extract_go_u2082___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_extract_go_u2082(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_extract_go_u2081(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_12 = l_String_extract_go_u2082(x_1, x_2, x_4);
lean_dec(x_2);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_String_extract_go_u2081___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_extract_go_u2081(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
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
static lean_object* _init_l_String_instInhabited__1() {
_start:
{
lean_object* x_1; 
x_1 = l_String_fromUTF8_x21___closed__0;
return x_1;
}
}
static lean_object* _init_l_String_instAppend___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_append___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_String_instAppend() {
_start:
{
lean_object* x_1; 
x_1 = l_String_instAppend___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_pushn___lam__0(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_pushn(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box_uint32(x_2);
x_5 = lean_alloc_closure((void*)(l_String_pushn___lam__0___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), x_5, x_3, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_pushn___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_String_pushn___lam__0(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_pushn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_String_pushn(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___String_Internal_pushnImpl_spec__0(uint32_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 1)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_8 = lean_string_push(x_3, x_1);
x_2 = x_7;
x_3 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lean_string_pushn(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___String_Internal_pushnImpl_spec__0(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___String_Internal_pushnImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_5 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___String_Internal_pushnImpl_spec__0(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Internal_pushnImpl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_string_pushn(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_String_isEmpty(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_isEmpty(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_string_isempty(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_string_utf8_byte_size(x_1);
lean_dec_ref(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Internal_isEmptyImpl___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_string_isempty(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_join___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_join(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_String_join___lam__0___boxed), 2, 0);
x_3 = l_String_fromUTF8_x21___closed__0;
x_4 = l_List_foldl___redArg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_join___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_join___lam__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_intercalate_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_string_append(x_1, x_2);
x_7 = lean_string_append(x_6, x_4);
x_1 = x_7;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_intercalate_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_String_Basic_0__String_intercalate_go(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_intercalate(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_String_fromUTF8_x21___closed__0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = l___private_Init_Data_String_Basic_0__String_intercalate_go(x_4, x_1, x_5);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_String_intercalate___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_intercalate(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_string_intercalate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_intercalate(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Iterator_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqIterator_decEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_string_dec_eq(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_4, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqIterator_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_instDecidableEqIterator_decEq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableEqIterator(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_String_instDecidableEqIterator_decEq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableEqIterator___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_instDecidableEqIterator(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_String_instInhabitedIterator_default___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_String_fromUTF8_x21___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_String_instInhabitedIterator_default() {
_start:
{
lean_object* x_1; 
x_1 = l_String_instInhabitedIterator_default___closed__0;
return x_1;
}
}
static lean_object* _init_l_String_instInhabitedIterator() {
_start:
{
lean_object* x_1; 
x_1 = l_String_instInhabitedIterator_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_mkIterator(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_iter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instSizeOfIterator___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_sub(x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
static lean_object* _init_l_String_instSizeOfIterator() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_instSizeOfIterator___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_instSizeOfIterator___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_instSizeOfIterator___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_toString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Iterator_toString(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_remainingBytes(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_sub(x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_remainingBytes___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Iterator_remainingBytes(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_pos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_pos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Iterator_pos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint32_t l_String_Iterator_curr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint32_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_string_utf8_get(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_curr___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_String_Iterator_curr(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_next(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_string_utf8_next(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_string_utf8_next(x_6, x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_String_Iterator_prev(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_string_utf8_prev(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_string_utf8_prev(x_6, x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT uint8_t l_String_Iterator_atEnd(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_le(x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_atEnd___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_Iterator_atEnd(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_String_Iterator_hasNext(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_hasNext___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_Iterator_hasNext(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_String_Iterator_hasPrev(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_hasPrev___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_Iterator_hasPrev(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Iterator_remainingBytes_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Iterator_remainingBytes_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_String_Basic_0__String_Iterator_remainingBytes_match__1_splitter___redArg(x_2, x_3);
return x_4;
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
LEAN_EXPORT uint32_t l_String_Iterator_curr_x27___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint32_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_string_utf8_get_fast(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint32_t l_String_Iterator_curr_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_string_utf8_get_fast(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_curr_x27___redArg___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_String_Iterator_curr_x27___redArg(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_curr_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = l_String_Iterator_curr_x27(x_1, x_2);
lean_dec_ref(x_1);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_next_x27___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_string_utf8_next_fast(x_6, x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_String_Iterator_next_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_string_utf8_next_fast(x_4, x_5);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_6);
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
x_9 = lean_string_utf8_next_fast(x_7, x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_String_Iterator_setCurr(lean_object* x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_string_utf8_set(x_4, x_5, x_2);
lean_ctor_set(x_1, 0, x_6);
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
x_9 = lean_string_utf8_set(x_7, x_8, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_String_Iterator_setCurr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_String_Iterator_setCurr(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_toEnd(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
x_5 = lean_string_utf8_byte_size(x_3);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_string_utf8_byte_size(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_String_Iterator_extract(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_11; uint8_t x_12; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_11 = lean_string_dec_eq(x_3, x_5);
x_12 = l_instDecidableNot___redArg(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_6, x_4);
x_7 = x_13;
goto block_10;
}
else
{
x_7 = x_12;
goto block_10;
}
block_10:
{
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_string_utf8_extract(x_3, x_4, x_6);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l_String_fromUTF8_x21___closed__0;
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Iterator_extract___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Iterator_extract(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_forward(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
lean_dec(x_2);
x_10 = lean_string_utf8_next(x_6, x_7);
lean_dec(x_7);
lean_ctor_set(x_1, 1, x_10);
x_2 = x_9;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_2, x_14);
lean_dec(x_2);
x_16 = lean_string_utf8_next(x_12, x_13);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
x_1 = x_17;
x_2 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Iterator_remainingToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_string_utf8_extract(x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_remainingToString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Iterator_remainingToString(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_nextn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
lean_dec(x_2);
x_10 = lean_string_utf8_next(x_6, x_7);
lean_dec(x_7);
lean_ctor_set(x_1, 1, x_10);
x_2 = x_9;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_2, x_14);
lean_dec(x_2);
x_16 = lean_string_utf8_next(x_12, x_13);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
x_1 = x_17;
x_2 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Iterator_prevn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
lean_dec(x_2);
x_10 = lean_string_utf8_prev(x_6, x_7);
lean_dec(x_7);
lean_ctor_set(x_1, 1, x_10);
x_2 = x_9;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_2, x_14);
lean_dec(x_2);
x_16 = lean_string_utf8_prev(x_12, x_13);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
x_1 = x_17;
x_2 = x_15;
goto _start;
}
}
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
LEAN_EXPORT lean_object* l_String_foldlAux___at___String_Internal_foldlImpl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_6 = l_String_foldlAux___at___String_Internal_foldlImpl_spec__0(x_1, x_3, x_4, x_5, x_2);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at___String_Internal_foldlImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_foldlAux___at___String_Internal_foldlImpl_spec__0(x_1, x_2, x_3, x_4, x_5);
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
LEAN_EXPORT uint8_t l_String_anyAux___at___String_Internal_anyImpl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_5 = l_String_anyAux___at___String_Internal_anyImpl_spec__0(x_2, x_1, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at___String_Internal_anyImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_String_anyAux___at___String_Internal_anyImpl_spec__0(x_1, x_2, x_3, x_4);
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
LEAN_EXPORT uint8_t l_String_anyAux___at___String_Internal_containsImpl_spec__0(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_5 = l_String_anyAux___at___String_Internal_containsImpl_spec__0(x_2, x_1, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at___String_Internal_containsImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_6 = l_String_anyAux___at___String_Internal_containsImpl_spec__0(x_5, x_2, x_3, x_4);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_set_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, uint32_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box_uint32(x_3);
x_6 = lean_apply_3(x_4, x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_set_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint32_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box_uint32(x_4);
x_7 = lean_apply_3(x_5, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_set_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_6 = l___private_Init_Data_String_Basic_0__String_Pos_Raw_set_match__1_splitter___redArg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_Pos_Raw_set_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_String_Basic_0__String_Pos_Raw_set_match__1_splitter(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_mapAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_utf8_at_end(x_3, x_2);
if (x_4 == 0)
{
uint32_t x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_string_utf8_get(x_3, x_2);
x_6 = lean_box_uint32(x_5);
lean_inc_ref(x_1);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_unbox_uint32(x_7);
lean_dec(x_7);
x_9 = lean_string_utf8_set(x_3, x_2, x_8);
x_10 = lean_string_utf8_next(x_9, x_2);
lean_dec(x_2);
x_2 = x_10;
x_3 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_String_map(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_mapAux(x_1, x_3, x_2);
return x_4;
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
LEAN_EXPORT lean_object* l_String_foldlAux___at___String_toNat_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT uint8_t l_String_anyAux___at___String_toNat_x3f_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l_String_anyAux___at___String_toNat_x3f_spec__1(x_9, x_1, x_7, x_8);
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
x_4 = l_String_foldlAux___at___String_toNat_x3f_spec__0(x_1, x_3, x_2, x_2);
lean_dec(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at___String_toNat_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_foldlAux___at___String_toNat_x3f_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at___String_toNat_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
x_6 = l_String_anyAux___at___String_toNat_x3f_spec__1(x_5, x_2, x_3, x_4);
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
LEAN_EXPORT uint8_t l___private_Init_Data_String_Basic_0__String_substrEq_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_substrEq_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l___private_Init_Data_String_Basic_0__String_substrEq_loop(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_String_substrEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_8 = l___private_Init_Data_String_Basic_0__String_substrEq_loop(x_1, x_3, x_2, x_4, x_7);
lean_dec(x_7);
return x_8;
}
}
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
x_5 = l_String_substrEq(x_1, x_3, x_2, x_3, x_4);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_replace_loop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_string_utf8_byte_size(x_1);
x_8 = lean_string_utf8_byte_size(x_2);
x_9 = lean_nat_add(x_6, x_8);
x_10 = lean_nat_dec_lt(x_7, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_7);
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_12 = l_String_substrEq(x_1, x_6, x_2, x_11, x_8);
lean_dec(x_8);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
x_13 = lean_string_utf8_next(x_1, x_6);
lean_dec(x_6);
x_6 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_string_utf8_extract(x_1, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
x_16 = lean_string_append(x_4, x_15);
lean_dec_ref(x_15);
x_17 = lean_string_append(x_16, x_3);
lean_inc(x_9);
x_4 = x_17;
x_5 = x_9;
x_6 = x_9;
goto _start;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_19 = lean_string_utf8_extract(x_1, x_5, x_7);
lean_dec(x_7);
lean_dec(x_5);
x_20 = lean_string_append(x_4, x_19);
lean_dec_ref(x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_replace_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_String_Basic_0__String_replace_loop___redArg(x_1, x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_replace_loop___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_String_Basic_0__String_replace_loop___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__String_replace_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_String_Basic_0__String_replace_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_replace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_String_fromUTF8_x21___closed__0;
x_8 = l___private_Init_Data_String_Basic_0__String_replace_loop___redArg(x_1, x_2, x_3, x_7, x_5, x_5);
return x_8;
}
else
{
lean_inc_ref(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_String_replace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_replace(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
LEAN_EXPORT uint8_t l_Substring_isEmpty(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_nat_sub(x_3, x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Substring_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Substring_isEmpty(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_substring_isempty(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_nat_sub(x_3, x_2);
lean_dec(x_2);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Substring_Internal_isEmptyImpl___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_substring_isempty(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Substring_toString(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Substring_toString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Substring_toString(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_substring_tostring(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_string_utf8_extract(x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_toIterator(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_inc_ref(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_toIterator___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Substring_toIterator(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint32_t l_Substring_get(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Substring_get___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = l_Substring_get(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT uint32_t lean_substring_get(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint32_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_nat_add(x_4, x_2);
lean_dec(x_2);
lean_dec(x_4);
x_6 = lean_string_utf8_get(x_3, x_5);
lean_dec(x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Substring_Internal_getImpl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_substring_get(x_1, x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_next(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_nat_add(x_4, x_2);
x_7 = lean_nat_dec_eq(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_string_utf8_next(x_3, x_6);
lean_dec(x_6);
x_9 = lean_nat_sub(x_8, x_4);
lean_dec(x_8);
return x_9;
}
else
{
lean_dec(x_6);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Substring_next___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Substring_next(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_get_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_4(x_3, x_4, x_5, x_6, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_get_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Basic_0__Substring_get_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_prev(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_nat_add(x_4, x_2);
x_6 = lean_nat_dec_eq(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_string_utf8_prev(x_3, x_5);
lean_dec(x_5);
x_8 = lean_nat_sub(x_7, x_4);
lean_dec(x_7);
return x_8;
}
else
{
lean_dec(x_5);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Substring_prev___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Substring_prev(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_substring_prev(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_nat_add(x_4, x_2);
x_6 = lean_nat_dec_eq(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = lean_string_utf8_prev(x_3, x_5);
lean_dec(x_5);
lean_dec_ref(x_3);
x_8 = lean_nat_sub(x_7, x_4);
lean_dec(x_4);
lean_dec(x_7);
return x_8;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Substring_nextn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 1)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_2, x_9);
lean_dec(x_2);
x_11 = lean_nat_add(x_7, x_3);
x_12 = lean_nat_dec_eq(x_11, x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_string_utf8_next(x_6, x_11);
lean_dec(x_11);
x_14 = lean_nat_sub(x_13, x_7);
lean_dec(x_13);
x_2 = x_10;
x_3 = x_14;
goto _start;
}
else
{
lean_dec(x_11);
x_2 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_nextn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_nextn(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_prevn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 1)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
lean_dec(x_2);
x_10 = lean_nat_add(x_7, x_3);
x_11 = lean_nat_dec_eq(x_10, x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_12 = lean_string_utf8_prev(x_6, x_10);
lean_dec(x_10);
x_13 = lean_nat_sub(x_12, x_7);
lean_dec(x_12);
x_2 = x_9;
x_3 = x_13;
goto _start;
}
else
{
lean_dec(x_10);
x_2 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_prevn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_prevn(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT uint32_t l_Substring_front(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint32_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_string_utf8_get(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_front___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Substring_front(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t lean_substring_front(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint32_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_string_utf8_get(x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_Internal_frontImpl___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_substring_front(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Substring_posOf(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec_ref(x_1);
lean_inc(x_4);
x_6 = l_String_posOfAux(x_3, x_2, x_5, x_4);
lean_dec(x_5);
lean_dec_ref(x_3);
x_7 = lean_nat_sub(x_6, x_4);
lean_dec(x_4);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Substring_posOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_Substring_posOf(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_drop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Substring_nextn(x_1, x_2, x_6);
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_nat_add(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_12);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_nat_add(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* lean_substring_drop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Substring_nextn(x_1, x_2, x_6);
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_nat_add(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_12);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_nat_add(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Substring_dropRight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_nat_sub(x_5, x_4);
x_7 = l_Substring_prevn(x_1, x_2, x_6);
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_nat_add(x_4, x_7);
lean_dec(x_7);
lean_ctor_set(x_1, 2, x_12);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_nat_add(x_4, x_7);
lean_dec(x_7);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Substring_take(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Substring_nextn(x_1, x_2, x_5);
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 2);
lean_dec(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_dec(x_10);
x_11 = lean_nat_add(x_4, x_6);
lean_dec(x_6);
lean_ctor_set(x_1, 2, x_11);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_nat_add(x_4, x_6);
lean_dec(x_6);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_4);
lean_ctor_set(x_13, 2, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeRight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_nat_sub(x_5, x_4);
x_7 = l_Substring_prevn(x_1, x_2, x_6);
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_nat_add(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_12);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_nat_add(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_5);
return x_14;
}
}
}
LEAN_EXPORT uint8_t l_Substring_atEnd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_nat_add(x_3, x_2);
x_6 = lean_nat_dec_eq(x_5, x_4);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Substring_atEnd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Substring_atEnd(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Substring_extract___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_String_fromUTF8_x21___closed__0;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Substring_extract(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_7 = x_1;
} else {
 lean_dec_ref(x_1);
 x_7 = lean_box(0);
}
x_14 = lean_nat_dec_le(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_nat_add(x_5, x_2);
x_16 = lean_nat_dec_le(x_6, x_15);
if (x_16 == 0)
{
x_8 = x_15;
goto block_13;
}
else
{
lean_dec(x_15);
lean_inc(x_6);
x_8 = x_6;
goto block_13;
}
}
else
{
lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_17 = l_Substring_extract___closed__0;
return x_17;
}
block_13:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_nat_add(x_5, x_3);
lean_dec(x_5);
x_10 = lean_nat_dec_le(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
if (lean_is_scalar(x_7)) {
 x_11 = lean_alloc_ctor(0, 3, 0);
} else {
 x_11 = x_7;
}
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_9);
if (lean_is_scalar(x_7)) {
 x_12 = lean_alloc_ctor(0, 3, 0);
} else {
 x_12 = x_7;
}
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_6);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_extract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_substring_extract(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_7 = x_1;
} else {
 lean_dec_ref(x_1);
 x_7 = lean_box(0);
}
x_14 = lean_nat_dec_le(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_nat_add(x_5, x_2);
lean_dec(x_2);
x_16 = lean_nat_dec_le(x_6, x_15);
if (x_16 == 0)
{
x_8 = x_15;
goto block_13;
}
else
{
lean_dec(x_15);
lean_inc(x_6);
x_8 = x_6;
goto block_13;
}
}
else
{
lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = l_Substring_extract___closed__0;
return x_17;
}
block_13:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_nat_add(x_5, x_3);
lean_dec(x_3);
lean_dec(x_5);
x_10 = lean_nat_dec_le(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
if (lean_is_scalar(x_7)) {
 x_11 = lean_alloc_ctor(0, 3, 0);
} else {
 x_11 = x_7;
}
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_9);
if (lean_is_scalar(x_7)) {
 x_12 = lean_alloc_ctor(0, 3, 0);
} else {
 x_12 = x_7;
}
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_6);
return x_12;
}
}
}
}
static lean_object* _init_l___private_Init_Data_String_Basic_0__Substring_splitOn_loop___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_fromUTF8_x21___closed__0;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_String_Basic_0__Substring_splitOn_loop___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Init_Data_String_Basic_0__Substring_splitOn_loop___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_String_fromUTF8_x21___closed__0;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_splitOn_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_33; lean_object* x_44; lean_object* x_50; uint8_t x_51; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
x_23 = lean_ctor_get(x_1, 2);
x_50 = lean_nat_sub(x_23, x_22);
x_51 = lean_nat_dec_lt(x_4, x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
lean_inc(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_52 = x_1;
} else {
 lean_dec_ref(x_1);
 x_52 = lean_box(0);
}
x_53 = lean_string_utf8_at_end(x_2, x_5);
if (x_53 == 0)
{
uint8_t x_54; 
lean_dec(x_52);
lean_dec(x_5);
x_54 = lean_nat_dec_le(x_4, x_3);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_nat_add(x_22, x_3);
lean_dec(x_3);
x_56 = lean_nat_dec_le(x_23, x_55);
if (x_56 == 0)
{
x_44 = x_55;
goto block_49;
}
else
{
lean_dec(x_55);
lean_inc(x_23);
x_44 = x_23;
goto block_49;
}
}
else
{
lean_object* x_57; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_4);
lean_dec(x_3);
x_57 = l_Substring_extract___closed__0;
x_7 = x_57;
goto block_10;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_64; lean_object* x_65; uint8_t x_71; 
x_58 = l___private_Init_Data_String_Basic_0__Substring_splitOn_loop___closed__1;
x_64 = lean_nat_sub(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
x_71 = lean_nat_dec_le(x_64, x_3);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_nat_add(x_22, x_3);
lean_dec(x_3);
x_73 = lean_nat_dec_le(x_23, x_72);
if (x_73 == 0)
{
x_65 = x_72;
goto block_70;
}
else
{
lean_dec(x_72);
lean_inc(x_23);
x_65 = x_23;
goto block_70;
}
}
else
{
lean_object* x_74; 
lean_dec(x_64);
lean_dec(x_52);
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_3);
x_74 = l_Substring_extract___closed__0;
x_59 = x_74;
goto block_63;
}
block_63:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_6);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_List_reverse___redArg(x_61);
return x_62;
}
block_70:
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_nat_add(x_22, x_64);
lean_dec(x_64);
lean_dec(x_22);
x_67 = lean_nat_dec_le(x_23, x_66);
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_23);
if (lean_is_scalar(x_52)) {
 x_68 = lean_alloc_ctor(0, 3, 0);
} else {
 x_68 = x_52;
}
lean_ctor_set(x_68, 0, x_21);
lean_ctor_set(x_68, 1, x_65);
lean_ctor_set(x_68, 2, x_66);
x_59 = x_68;
goto block_63;
}
else
{
lean_object* x_69; 
lean_dec(x_66);
if (lean_is_scalar(x_52)) {
 x_69 = lean_alloc_ctor(0, 3, 0);
} else {
 x_69 = x_52;
}
lean_ctor_set(x_69, 0, x_21);
lean_ctor_set(x_69, 1, x_65);
lean_ctor_set(x_69, 2, x_23);
x_59 = x_69;
goto block_63;
}
}
}
}
else
{
lean_object* x_75; uint32_t x_76; uint32_t x_77; uint8_t x_78; 
x_75 = lean_nat_add(x_22, x_4);
x_76 = lean_string_utf8_get(x_21, x_75);
x_77 = lean_string_utf8_get(x_2, x_5);
x_78 = lean_uint32_dec_eq(x_76, x_77);
if (x_78 == 0)
{
uint8_t x_79; 
lean_dec(x_5);
x_79 = lean_nat_dec_eq(x_75, x_23);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_4);
x_80 = lean_string_utf8_next(x_21, x_75);
lean_dec(x_75);
x_81 = lean_nat_sub(x_80, x_22);
lean_dec(x_80);
x_11 = x_81;
goto block_14;
}
else
{
lean_dec(x_75);
x_11 = x_4;
goto block_14;
}
}
else
{
uint8_t x_82; 
x_82 = lean_nat_dec_eq(x_75, x_23);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_4);
x_83 = lean_string_utf8_next(x_21, x_75);
lean_dec(x_75);
x_84 = lean_nat_sub(x_83, x_22);
lean_dec(x_83);
x_33 = x_84;
goto block_43;
}
else
{
lean_dec(x_75);
x_33 = x_4;
goto block_43;
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_List_reverse___redArg(x_8);
return x_9;
}
block_14:
{
lean_object* x_12; 
x_12 = lean_unsigned_to_nat(0u);
x_4 = x_11;
x_5 = x_12;
goto _start;
}
block_20:
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
lean_inc(x_15);
x_3 = x_15;
x_4 = x_15;
x_5 = x_16;
x_6 = x_18;
goto _start;
}
block_32:
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_nat_add(x_22, x_24);
lean_dec(x_24);
x_29 = lean_nat_dec_le(x_23, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_inc_ref(x_21);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_28);
x_15 = x_25;
x_16 = x_26;
x_17 = x_30;
goto block_20;
}
else
{
lean_object* x_31; 
lean_dec(x_28);
lean_inc(x_23);
lean_inc_ref(x_21);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set(x_31, 2, x_23);
x_15 = x_25;
x_16 = x_26;
x_17 = x_31;
goto block_20;
}
}
block_43:
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_string_utf8_next(x_2, x_5);
lean_dec(x_5);
x_35 = lean_string_utf8_at_end(x_2, x_34);
if (x_35 == 0)
{
x_4 = x_33;
x_5 = x_34;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_sub(x_33, x_34);
lean_dec(x_34);
x_39 = lean_nat_dec_le(x_38, x_3);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_nat_add(x_22, x_3);
lean_dec(x_3);
x_41 = lean_nat_dec_le(x_23, x_40);
if (x_41 == 0)
{
x_24 = x_38;
x_25 = x_33;
x_26 = x_37;
x_27 = x_40;
goto block_32;
}
else
{
lean_dec(x_40);
lean_inc(x_23);
x_24 = x_38;
x_25 = x_33;
x_26 = x_37;
x_27 = x_23;
goto block_32;
}
}
else
{
lean_object* x_42; 
lean_dec(x_38);
lean_dec(x_3);
x_42 = l_Substring_extract___closed__0;
x_15 = x_33;
x_16 = x_37;
x_17 = x_42;
goto block_20;
}
}
}
block_49:
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_nat_add(x_22, x_4);
lean_dec(x_4);
lean_dec(x_22);
x_46 = lean_nat_dec_le(x_23, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_23);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_21);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_45);
x_7 = x_47;
goto block_10;
}
else
{
lean_object* x_48; 
lean_dec(x_45);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_21);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_48, 2, x_23);
x_7 = x_48;
goto block_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_splitOn_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_String_Basic_0__Substring_splitOn_loop(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Substring_splitOn(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Init_Data_String_Basic_0__Substring_splitOn_loop(x_1, x_2, x_5, x_5, x_5, x_6);
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
LEAN_EXPORT lean_object* l_Substring_splitOn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Substring_splitOn(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Substring_foldl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = l_String_foldlAux___redArg(x_1, x_4, x_6, x_5, x_2);
lean_dec(x_6);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Substring_foldl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = l_String_foldlAux___redArg(x_2, x_5, x_7, x_6, x_3);
lean_dec(x_7);
lean_dec_ref(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Substring_foldr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = l_String_foldrAux___redArg(x_1, x_2, x_4, x_6, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Substring_foldr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = l_String_foldrAux___redArg(x_2, x_3, x_5, x_7, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Substring_any(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_String_anyAux(x_3, x_5, x_2, x_4);
lean_dec(x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Substring_any___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Substring_any(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Substring_all(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_alloc_closure((void*)(l_String_all___lam__0___boxed), 2, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = l_String_anyAux(x_3, x_5, x_6, x_4);
lean_dec(x_5);
lean_dec_ref(x_3);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Substring_all___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Substring_all(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at___Substring_Internal_allImpl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_dec(x_4);
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_10; 
x_10 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t lean_substring_all(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_String_anyAux___at___Substring_Internal_allImpl_spec__0(x_2, x_3, x_5, x_4);
lean_dec(x_5);
lean_dec_ref(x_3);
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
LEAN_EXPORT lean_object* l_String_anyAux___at___Substring_Internal_allImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_String_anyAux___at___Substring_Internal_allImpl_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Substring_Internal_allImpl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_substring_all(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Substring_contains(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_box_uint32(x_2);
x_7 = lean_alloc_closure((void*)(l_String_contains___lam__0___boxed), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = l_String_anyAux(x_3, x_5, x_7, x_4);
lean_dec(x_5);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Substring_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_Substring_contains(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_2);
if (x_5 == 0)
{
lean_dec_ref(x_3);
return x_4;
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
lean_dec_ref(x_3);
return x_4;
}
else
{
lean_object* x_10; 
x_10 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Substring_takeWhileAux(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhile(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_7 = l_Substring_takeWhileAux(x_4, x_6, x_2, x_5);
lean_dec(x_6);
lean_ctor_set(x_1, 2, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_9);
x_11 = l_Substring_takeWhileAux(x_8, x_10, x_2, x_9);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Substring_Internal_takeWhileImpl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec_ref(x_1);
return x_4;
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
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_10; 
x_10 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lean_substring_takewhile(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_7 = l_Substring_takeWhileAux___at___Substring_Internal_takeWhileImpl_spec__0(x_2, x_4, x_6, x_5);
lean_dec(x_6);
lean_ctor_set(x_1, 2, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_9);
x_11 = l_Substring_takeWhileAux___at___Substring_Internal_takeWhileImpl_spec__0(x_2, x_8, x_10, x_9);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Substring_Internal_takeWhileImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Substring_takeWhileAux___at___Substring_Internal_takeWhileImpl_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_dropWhile(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = l_Substring_takeWhileAux(x_4, x_6, x_2, x_5);
lean_ctor_set(x_1, 1, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_11 = l_Substring_takeWhileAux(x_8, x_10, x_2, x_9);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_3);
return x_4;
}
else
{
lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_string_utf8_prev(x_1, x_4);
x_7 = lean_string_utf8_get(x_1, x_6);
x_8 = lean_box_uint32(x_7);
lean_inc_ref(x_3);
x_9 = lean_apply_1(x_3, x_8);
x_10 = lean_unbox(x_9);
if (x_10 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_3);
return x_4;
}
else
{
lean_dec(x_4);
x_4 = x_6;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Substring_takeRightWhileAux(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhile(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = l_Substring_takeRightWhileAux(x_4, x_5, x_2, x_6);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_10);
x_11 = l_Substring_takeRightWhileAux(x_8, x_9, x_2, x_10);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Substring_dropRightWhile(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = l_Substring_takeRightWhileAux(x_4, x_5, x_2, x_6);
lean_ctor_set(x_1, 2, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_11 = l_Substring_takeRightWhileAux(x_8, x_9, x_2, x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Substring_trimLeft___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Char_isWhitespace___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Substring_trimLeft(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = l_Substring_trimLeft___closed__0;
x_7 = l_Substring_takeWhileAux(x_3, x_5, x_6, x_4);
lean_ctor_set(x_1, 1, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_11 = l_Substring_trimLeft___closed__0;
x_12 = l_Substring_takeWhileAux(x_8, x_10, x_11, x_9);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Substring_trimRight(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = l_Substring_trimLeft___closed__0;
x_7 = l_Substring_takeRightWhileAux(x_3, x_4, x_6, x_5);
lean_ctor_set(x_1, 2, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_11 = l_Substring_trimLeft___closed__0;
x_12 = l_Substring_takeRightWhileAux(x_8, x_9, x_11, x_10);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Substring_trim(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = l_Substring_trimLeft___closed__0;
x_7 = l_Substring_takeWhileAux(x_3, x_5, x_6, x_4);
x_8 = l_Substring_takeRightWhileAux(x_3, x_7, x_6, x_5);
lean_ctor_set(x_1, 2, x_8);
lean_ctor_set(x_1, 1, x_7);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_12 = l_Substring_trimLeft___closed__0;
x_13 = l_Substring_takeWhileAux(x_9, x_11, x_12, x_10);
x_14 = l_Substring_takeRightWhileAux(x_9, x_13, x_12, x_11);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
}
}
LEAN_EXPORT uint8_t l_Substring_isNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_nat_sub(x_4, x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_box(x_7);
x_9 = lean_alloc_closure((void*)(l_String_isNat___lam__0___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l_String_anyAux(x_2, x_4, x_9, x_3);
lean_dec(x_4);
lean_dec_ref(x_2);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
else
{
return x_7;
}
}
else
{
uint8_t x_12; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Substring_isNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Substring_isNat(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Substring_toNat_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec_ref(x_1);
x_9 = lean_nat_sub(x_4, x_3);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
uint8_t x_12; 
lean_inc(x_3);
x_12 = l_String_anyAux___at___String_toNat_x3f_spec__1(x_11, x_2, x_4, x_3);
if (x_12 == 0)
{
goto block_8;
}
else
{
if (x_11 == 0)
{
lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_13 = lean_box(0);
return x_13;
}
else
{
goto block_8;
}
}
}
else
{
lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_14 = lean_box(0);
return x_14;
}
block_8:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_String_foldlAux___at___String_toNat_x3f_spec__0(x_2, x_4, x_3, x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Substring_repair(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_5 = x_1;
} else {
 lean_dec_ref(x_1);
 x_5 = lean_box(0);
}
x_12 = lean_string_is_valid_pos(x_2, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_3);
x_13 = lean_string_utf8_byte_size(x_2);
x_6 = x_13;
goto block_11;
}
else
{
x_6 = x_3;
goto block_11;
}
block_11:
{
uint8_t x_7; 
x_7 = lean_string_is_valid_pos(x_2, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_string_utf8_byte_size(x_2);
if (lean_is_scalar(x_5)) {
 x_9 = lean_alloc_ctor(0, 3, 0);
} else {
 x_9 = x_5;
}
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_8);
return x_9;
}
else
{
lean_object* x_10; 
if (lean_is_scalar(x_5)) {
 x_10 = lean_alloc_ctor(0, 3, 0);
} else {
 x_10 = x_5;
}
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_4);
return x_10;
}
}
}
}
LEAN_EXPORT uint8_t l_Substring_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_3 = l_Substring_repair(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = l_Substring_repair(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = lean_nat_sub(x_6, x_5);
lean_dec(x_6);
x_12 = lean_nat_sub(x_10, x_9);
lean_dec(x_10);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = l_String_substrEq(x_4, x_5, x_8, x_9, x_11);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Substring_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Substring_beq(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lean_substring_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Substring_beq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Substring_Internal_beqImpl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_substring_beq(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Substring_hasBeq___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Substring_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Substring_hasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Substring_hasBeq___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Substring_sameAs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = l_Substring_beq(x_1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Substring_sameAs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Substring_sameAs(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_commonPrefix_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_nat_dec_lt(x_3, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_nat_dec_lt(x_4, x_9);
if (x_10 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_string_utf8_get(x_5, x_3);
x_12 = lean_string_utf8_get(x_8, x_4);
x_13 = lean_uint32_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_string_utf8_next(x_5, x_3);
lean_dec(x_3);
x_15 = lean_string_utf8_next(x_8, x_4);
lean_dec(x_4);
x_3 = x_14;
x_4 = x_15;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_commonPrefix_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Basic_0__Substring_commonPrefix_loop(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_commonPrefix(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
x_6 = l___private_Init_Data_String_Basic_0__Substring_commonPrefix_loop(x_1, x_2, x_4, x_5);
lean_dec_ref(x_1);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 2);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_2, 0);
lean_dec(x_10);
lean_ctor_set(x_2, 2, x_6);
lean_ctor_set(x_2, 1, x_4);
lean_ctor_set(x_2, 0, x_3);
return x_2;
}
else
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_11, 2, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_commonSuffix_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_nat_dec_lt(x_6, x_3);
if (x_7 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_nat_dec_lt(x_9, x_4);
if (x_10 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; uint32_t x_13; uint32_t x_14; uint8_t x_15; 
x_11 = lean_string_utf8_prev(x_5, x_3);
x_12 = lean_string_utf8_prev(x_8, x_4);
lean_dec(x_4);
x_13 = lean_string_utf8_get(x_5, x_11);
x_14 = lean_string_utf8_get(x_8, x_12);
x_15 = lean_uint32_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
return x_3;
}
else
{
lean_dec(x_3);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_commonSuffix_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Basic_0__Substring_commonSuffix_loop(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_commonSuffix(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_inc(x_4);
x_6 = l___private_Init_Data_String_Basic_0__Substring_commonSuffix_loop(x_1, x_2, x_4, x_5);
lean_dec_ref(x_1);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 2);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_2, 0);
lean_dec(x_10);
lean_ctor_set(x_2, 2, x_4);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_3);
return x_2;
}
else
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_4);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Substring_dropPrefix_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_3 = l_Substring_commonPrefix(x_1, x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_nat_sub(x_5, x_4);
lean_dec(x_4);
x_9 = lean_nat_sub(x_7, x_6);
lean_dec(x_6);
lean_dec(x_7);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_1);
x_11 = lean_box(0);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
lean_ctor_set(x_1, 1, x_5);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_5);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_dropSuffix_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_3 = l_Substring_commonSuffix(x_1, x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_nat_sub(x_5, x_4);
lean_dec(x_5);
x_9 = lean_nat_sub(x_7, x_6);
lean_dec(x_6);
lean_dec(x_7);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_4);
lean_dec_ref(x_1);
x_11 = lean_box(0);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 2);
lean_dec(x_13);
lean_ctor_set(x_1, 2, x_4);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_4);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_String_drop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc(x_4);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_Substring_nextn(x_5, x_2, x_3);
lean_dec_ref(x_5);
x_7 = lean_string_utf8_extract(x_1, x_6, x_4);
lean_dec(x_4);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* lean_string_drop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc(x_4);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_Substring_nextn(x_5, x_2, x_3);
lean_dec_ref(x_5);
x_7 = lean_string_utf8_extract(x_1, x_6, x_4);
lean_dec(x_4);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_dropRight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc(x_4);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_Substring_prevn(x_5, x_2, x_4);
lean_dec_ref(x_5);
x_7 = lean_string_utf8_extract(x_1, x_3, x_6);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* lean_string_dropright(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc(x_4);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_Substring_prevn(x_5, x_2, x_4);
lean_dec_ref(x_5);
x_7 = lean_string_utf8_extract(x_1, x_3, x_6);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_take(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_Substring_nextn(x_5, x_2, x_3);
lean_dec_ref(x_5);
x_7 = lean_string_utf8_extract(x_1, x_3, x_6);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_takeRight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc(x_4);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_inc(x_4);
x_6 = l_Substring_prevn(x_5, x_2, x_4);
lean_dec_ref(x_5);
x_7 = lean_string_utf8_extract(x_1, x_6, x_4);
lean_dec(x_4);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_takeWhile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l_Substring_takeWhileAux(x_1, x_4, x_2, x_3);
lean_dec(x_4);
x_6 = lean_string_utf8_extract(x_1, x_3, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_takeWhile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_takeWhile(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_dropWhile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l_Substring_takeWhileAux(x_1, x_4, x_2, x_3);
x_6 = lean_string_utf8_extract(x_1, x_5, x_4);
lean_dec(x_4);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_dropWhile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_dropWhile(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_takeRightWhile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc(x_4);
x_5 = l_Substring_takeRightWhileAux(x_1, x_3, x_2, x_4);
x_6 = lean_string_utf8_extract(x_1, x_5, x_4);
lean_dec(x_4);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_takeRightWhile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_takeRightWhile(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_dropRightWhile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l_Substring_takeRightWhileAux(x_1, x_3, x_2, x_4);
x_6 = lean_string_utf8_extract(x_1, x_3, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_dropRightWhile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_dropRightWhile(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_String_startsWith(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_string_length(x_2);
x_7 = l_Substring_nextn(x_5, x_6, x_3);
lean_dec_ref(x_5);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_string_utf8_byte_size(x_2);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_Substring_beq(x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_String_startsWith___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_startsWith(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_endsWith(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc(x_4);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_string_length(x_2);
lean_inc(x_4);
x_7 = l_Substring_prevn(x_5, x_6, x_4);
lean_dec_ref(x_5);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_4);
x_9 = lean_string_utf8_byte_size(x_2);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_Substring_beq(x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_String_endsWith___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_endsWith(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_trimRight(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = l_Substring_trimLeft___closed__0;
x_5 = l_Substring_takeRightWhileAux(x_1, x_2, x_4, x_3);
x_6 = lean_string_utf8_extract(x_1, x_2, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_trimRight___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_trimRight(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_trimLeft(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = l_Substring_trimLeft___closed__0;
x_5 = l_Substring_takeWhileAux(x_1, x_3, x_4, x_2);
x_6 = lean_string_utf8_extract(x_1, x_5, x_3);
lean_dec(x_3);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_trimLeft___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_trimLeft(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_trim(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = l_Substring_trimLeft___closed__0;
x_5 = l_Substring_takeWhileAux(x_1, x_3, x_4, x_2);
x_6 = l_Substring_takeRightWhileAux(x_1, x_5, x_4, x_3);
x_7 = lean_string_utf8_extract(x_1, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_trim___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_trim(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___String_Internal_trimImpl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_7; uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_3, x_2);
if (x_9 == 0)
{
return x_3;
}
else
{
uint32_t x_10; uint8_t x_11; uint32_t x_17; uint8_t x_18; 
x_10 = lean_string_utf8_get(x_1, x_3);
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_10, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 9;
x_20 = lean_uint32_dec_eq(x_10, x_19);
x_11 = x_20;
goto block_16;
}
else
{
x_11 = x_18;
goto block_16;
}
block_16:
{
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 13;
x_13 = lean_uint32_dec_eq(x_10, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 10;
x_15 = lean_uint32_dec_eq(x_10, x_14);
x_7 = x_15;
goto block_8;
}
else
{
x_7 = x_13;
goto block_8;
}
}
else
{
goto block_6;
}
}
}
block_6:
{
lean_object* x_4; 
x_4 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_4;
goto _start;
}
block_8:
{
if (x_7 == 0)
{
return x_3;
}
else
{
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___String_Internal_trimImpl_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; uint8_t x_6; uint32_t x_9; uint8_t x_10; uint32_t x_17; uint8_t x_18; 
x_5 = lean_string_utf8_prev(x_1, x_3);
x_9 = lean_string_utf8_get(x_1, x_5);
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_9, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 9;
x_20 = lean_uint32_dec_eq(x_9, x_19);
x_10 = x_20;
goto block_16;
}
else
{
x_10 = x_18;
goto block_16;
}
block_8:
{
if (x_6 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
block_16:
{
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 13;
x_12 = lean_uint32_dec_eq(x_9, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 10;
x_14 = lean_uint32_dec_eq(x_9, x_13);
x_6 = x_14;
goto block_8;
}
else
{
x_6 = x_12;
goto block_8;
}
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lean_string_trim(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = l_Substring_takeWhileAux___at___String_Internal_trimImpl_spec__0(x_1, x_3, x_2);
x_5 = l_Substring_takeRightWhileAux___at___String_Internal_trimImpl_spec__1(x_1, x_4, x_3);
x_6 = lean_string_utf8_extract(x_1, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___String_Internal_trimImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeWhileAux___at___String_Internal_trimImpl_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___String_Internal_trimImpl_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeRightWhileAux___at___String_Internal_trimImpl_spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_nextWhile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l_Substring_takeWhileAux(x_1, x_4, x_2, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_nextWhile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_nextWhile(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_string_nextwhile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l_Substring_takeWhileAux___at___Substring_Internal_takeWhileImpl_spec__0(x_2, x_1, x_4, x_3);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_nextUntil(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_String_all___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = l_Substring_takeWhileAux(x_1, x_5, x_4, x_3);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_nextUntil___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_nextUntil(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_String_toUpper___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Char_toUpper___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_toUpper(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_String_toUpper___closed__0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_mapAux(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_String_toLower___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Char_toLower___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_toLower(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_String_toLower___closed__0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_mapAux(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_capitalize(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = l_Char_toUpper(x_3);
x_5 = lean_string_utf8_set(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_string_capitalize(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = l_Char_toUpper(x_3);
x_5 = lean_string_utf8_set(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_decapitalize(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = l_Char_toLower(x_3);
x_5 = lean_string_utf8_set(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_string_utf8_byte_size(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_Substring_dropPrefix_x3f(x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_string_utf8_byte_size(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_Substring_dropSuffix_x3f(x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_stripPrefix(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_1);
x_3 = l_String_dropPrefix_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_string_utf8_extract(x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_String_stripSuffix(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_1);
x_3 = l_String_dropSuffix_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_string_utf8_extract(x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_8;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_nextn_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_2, x_6);
if (x_7 == 1)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_apply_2(x_4, x_1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_2, x_9);
x_11 = lean_apply_3(x_5, x_1, x_10, x_3);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_nextn_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_String_Basic_0__Substring_nextn_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_nextn_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_String_Basic_0__Substring_nextn_match__1_splitter___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Basic_0__Substring_nextn_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_String_Basic_0__Substring_nextn_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* initialize_Init_Data_List_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Char_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_String_Bootstrap(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ByteArray_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_String_Decode(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Bootstrap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Decode(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Lemmas(builtin, lean_io_mk_world());
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
l_instAppendString = _init_l_instAppendString();
lean_mark_persistent(l_instAppendString);
l_String_instHSubRaw = _init_l_String_instHSubRaw();
lean_mark_persistent(l_String_instHSubRaw);
l_String_instHSubRawChar = _init_l_String_instHSubRawChar();
lean_mark_persistent(l_String_instHSubRawChar);
l_String_instHAddRawChar = _init_l_String_instHAddRawChar();
lean_mark_persistent(l_String_instHAddRawChar);
l_String_instHAddCharRaw = _init_l_String_instHAddCharRaw();
lean_mark_persistent(l_String_instHAddCharRaw);
l_String_instHAddRaw = _init_l_String_instHAddRaw();
lean_mark_persistent(l_String_instHAddRaw);
l_String_instHAddRaw__1 = _init_l_String_instHAddRaw__1();
lean_mark_persistent(l_String_instHAddRaw__1);
l_String_instLERaw = _init_l_String_instLERaw();
lean_mark_persistent(l_String_instLERaw);
l_String_instLTRaw = _init_l_String_instLTRaw();
lean_mark_persistent(l_String_instLTRaw);
l_String_instMinRaw = _init_l_String_instMinRaw();
lean_mark_persistent(l_String_instMinRaw);
l_String_instMaxRaw = _init_l_String_instMaxRaw();
lean_mark_persistent(l_String_instMaxRaw);
l_String_instLT = _init_l_String_instLT();
lean_mark_persistent(l_String_instLT);
l_String_instLE = _init_l_String_instLE();
lean_mark_persistent(l_String_instLE);
l_String_instInhabitedSlice___closed__0 = _init_l_String_instInhabitedSlice___closed__0();
lean_mark_persistent(l_String_instInhabitedSlice___closed__0);
l_String_instInhabitedSlice = _init_l_String_instInhabitedSlice();
lean_mark_persistent(l_String_instInhabitedSlice);
l_String_instHAddRawSlice = _init_l_String_instHAddRawSlice();
lean_mark_persistent(l_String_instHAddRawSlice);
l_String_instHAddSliceRaw = _init_l_String_instHAddSliceRaw();
lean_mark_persistent(l_String_instHAddSliceRaw);
l_String_instHSubRawSlice = _init_l_String_instHSubRawSlice();
lean_mark_persistent(l_String_instHSubRawSlice);
l_String_Slice_getUTF8Byte_x21___closed__0 = _init_l_String_Slice_getUTF8Byte_x21___closed__0();
lean_mark_persistent(l_String_Slice_getUTF8Byte_x21___closed__0);
l_String_Slice_getUTF8Byte_x21___closed__1 = _init_l_String_Slice_getUTF8Byte_x21___closed__1();
lean_mark_persistent(l_String_Slice_getUTF8Byte_x21___closed__1);
l_String_Slice_getUTF8Byte_x21___closed__2 = _init_l_String_Slice_getUTF8Byte_x21___closed__2();
lean_mark_persistent(l_String_Slice_getUTF8Byte_x21___closed__2);
l_String_Slice_replaceStartEnd_x21___closed__0 = _init_l_String_Slice_replaceStartEnd_x21___closed__0();
lean_mark_persistent(l_String_Slice_replaceStartEnd_x21___closed__0);
l_String_Slice_replaceStartEnd_x21___closed__1 = _init_l_String_Slice_replaceStartEnd_x21___closed__1();
lean_mark_persistent(l_String_Slice_replaceStartEnd_x21___closed__1);
l_String_Slice_replaceStartEnd_x21___closed__2 = _init_l_String_Slice_replaceStartEnd_x21___closed__2();
lean_mark_persistent(l_String_Slice_replaceStartEnd_x21___closed__2);
l_panic___at___String_Slice_Pos_get_x21_spec__0___boxed__const__1 = _init_l_panic___at___String_Slice_Pos_get_x21_spec__0___boxed__const__1();
lean_mark_persistent(l_panic___at___String_Slice_Pos_get_x21_spec__0___boxed__const__1);
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
l_String_instInhabited__1 = _init_l_String_instInhabited__1();
lean_mark_persistent(l_String_instInhabited__1);
l_String_instAppend___closed__0 = _init_l_String_instAppend___closed__0();
lean_mark_persistent(l_String_instAppend___closed__0);
l_String_instAppend = _init_l_String_instAppend();
lean_mark_persistent(l_String_instAppend);
l_String_instInhabitedIterator_default___closed__0 = _init_l_String_instInhabitedIterator_default___closed__0();
lean_mark_persistent(l_String_instInhabitedIterator_default___closed__0);
l_String_instInhabitedIterator_default = _init_l_String_instInhabitedIterator_default();
lean_mark_persistent(l_String_instInhabitedIterator_default);
l_String_instInhabitedIterator = _init_l_String_instInhabitedIterator();
lean_mark_persistent(l_String_instInhabitedIterator);
l_String_instSizeOfIterator = _init_l_String_instSizeOfIterator();
lean_mark_persistent(l_String_instSizeOfIterator);
l_Substring_extract___closed__0 = _init_l_Substring_extract___closed__0();
lean_mark_persistent(l_Substring_extract___closed__0);
l___private_Init_Data_String_Basic_0__Substring_splitOn_loop___closed__0 = _init_l___private_Init_Data_String_Basic_0__Substring_splitOn_loop___closed__0();
lean_mark_persistent(l___private_Init_Data_String_Basic_0__Substring_splitOn_loop___closed__0);
l___private_Init_Data_String_Basic_0__Substring_splitOn_loop___closed__1 = _init_l___private_Init_Data_String_Basic_0__Substring_splitOn_loop___closed__1();
lean_mark_persistent(l___private_Init_Data_String_Basic_0__Substring_splitOn_loop___closed__1);
l_Substring_trimLeft___closed__0 = _init_l_Substring_trimLeft___closed__0();
lean_mark_persistent(l_Substring_trimLeft___closed__0);
l_Substring_hasBeq___closed__0 = _init_l_Substring_hasBeq___closed__0();
lean_mark_persistent(l_Substring_hasBeq___closed__0);
l_Substring_hasBeq = _init_l_Substring_hasBeq();
lean_mark_persistent(l_Substring_hasBeq);
l_String_toUpper___closed__0 = _init_l_String_toUpper___closed__0();
lean_mark_persistent(l_String_toUpper___closed__0);
l_String_toLower___closed__0 = _init_l_String_toLower___closed__0();
lean_mark_persistent(l_String_toLower___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
