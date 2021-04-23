// Lean compiler output
// Module: Init.Data.String.Basic
// Imports: Init.Data.List.Basic Init.Data.Char.Basic Init.Data.Option.Basic
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
lean_object* lean_string_data(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__Substring_takeWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_get_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_prev___boxed(lean_object*, lean_object*);
lean_object* l_String_Iterator_curr___boxed(lean_object*);
lean_object* l_String_csize(uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l___private_Init_Data_String_Basic_0__String_utf8ExtractAux_u2081_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_splitOnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_trim(lean_object*);
lean_object* l_String_contains___boxed(lean_object*, lean_object*);
lean_object* l_String_Iterator_remainingToString(lean_object*);
lean_object* l_String_push_match__1___rarg(lean_object*, uint32_t, lean_object*);
lean_object* l_Substring_splitOn(lean_object*, lean_object*);
lean_object* l_String_toList(lean_object*);
lean_object* l_List_intercalate___rarg(lean_object*, lean_object*);
uint8_t l_String_Iterator_isPrefixOfRemaining(lean_object*, lean_object*);
lean_object* l_String_revPosOfAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_get___boxed(lean_object*, lean_object*);
lean_object* l_String_instInhabitedString;
lean_object* l_Substring_extract___closed__1;
lean_object* l_String_atEnd_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_length___boxed(lean_object*);
lean_object* l_String_Iterator_remainingBytes___boxed(lean_object*);
lean_object* l_Substring_extract___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__Substring_takeRightWhileAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_extract_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_anyAux_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_trimRight___boxed(lean_object*);
lean_object* l_String_takeRightWhile___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__Substring_prevn_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_isEmpty___boxed(lean_object*);
lean_object* l_List_map___at_String_intercalate___spec__1(lean_object*);
lean_object* l_String_nextWhile___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__Substring_prev___boxed(lean_object*, lean_object*);
lean_object* l_Substring_drop(lean_object*, lean_object*);
lean_object* l_String_Iterator_extract___boxed(lean_object*, lean_object*);
lean_object* l_String_toUpper(lean_object*);
lean_object* l_List_foldl___at_String_join___spec__1(lean_object*, lean_object*);
lean_object* l_String_push_match__1(lean_object*);
lean_object* l_Substring_toNat_x3f(lean_object*);
uint8_t l_String_anyAux_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_revPosOf(lean_object*, uint32_t);
lean_object* l_Substring_toString___boxed(lean_object*);
lean_object* l_String_offsetOfPosAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_anyAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_modify(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toNat_x3f___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_String_str___boxed(lean_object*, lean_object*);
uint8_t l_Substring_any(lean_object*, lean_object*);
lean_object* l_Substring_splitOn___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__Substring_takeWhileAux___at_String_nextUntil___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* l_Char_toUpper(uint32_t);
lean_object* l_Substring_takeWhile_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_isEmpty___boxed(lean_object*);
lean_object* l_String_back___boxed(lean_object*);
uint8_t l_Char_isDigit(uint32_t);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_String_nextUntil(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__String_utf8PrevAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_String_append___boxed(lean_object*, lean_object*);
lean_object* l_String_Iterator_hasPrev___boxed(lean_object*);
uint8_t l_String_any(lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__String_utf8ExtractAux_u2082___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_drop_match__1(lean_object*);
lean_object* l_String_foldl___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_foldlAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__Substring_takeRightWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_extract_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_splitOn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_String_set___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_foldlAux_loop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_String_contains___lambda__1(uint32_t, uint32_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t l_Char_isWhitespace(uint32_t);
lean_object* l_String_Iterator_toEnd(lean_object*);
uint32_t l___private_Init_Data_String_Basic_0__String_utf8GetAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_toString_match__1(lean_object*);
lean_object* l_String_split___boxed(lean_object*, lean_object*);
lean_object* l_String_get_match__1(lean_object*);
lean_object* l_String_Iterator_toString_match__1___rarg(lean_object*, lean_object*);
lean_object* l_String_splitOn(lean_object*, lean_object*);
lean_object* l_String_dropWhile(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_trimLeft___boxed(lean_object*);
lean_object* l_String_Iterator_forward_match__1(lean_object*);
lean_object* l_String_set_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toNat_x3f___lambda__1(lean_object*, uint32_t);
lean_object* l___private_Init_Data_String_Basic_0__Substring_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Substring_hasBeq___closed__1;
lean_object* l_String_Iterator_setCurr_match__1___rarg(lean_object*, uint32_t, lean_object*);
lean_object* l_String_atEnd_match__1(lean_object*);
lean_object* l_String_trim___boxed(lean_object*);
lean_object* l_Substring_takeWhile_match__1(lean_object*);
lean_object* l_String_foldlAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_offsetOfPosAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_String_Iterator_toString_match__1(lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__Substring_prev(lean_object*, lean_object*);
uint8_t l_Substring_all(lean_object*, lean_object*);
lean_object* l_String_trimRight(lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__Substring_takeWhileAux___at_Substring_trimLeft___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Iterator_setCurr_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_next___boxed(lean_object*, lean_object*);
lean_object* l_String_append_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_isNat___boxed(lean_object*);
lean_object* l_String_instAppendString;
lean_object* l_Substring_dropWhile(lean_object*, lean_object*);
lean_object* l_String_isNat___closed__1;
lean_object* l_Substring_all___boxed(lean_object*, lean_object*);
lean_object* l_String_takeWhile(lean_object*, lean_object*);
lean_object* l_String_push_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at_String_join___spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_repeat_loop___at_String_pushn___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
uint8_t l_String_contains(lean_object*, uint32_t);
lean_object* l_String_atEnd___boxed(lean_object*, lean_object*);
lean_object* l_String_Iterator_forward(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint32_t l_String_getOp(lean_object*, lean_object*);
lean_object* l_String_foldl___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_get_match__1(lean_object*);
lean_object* l_Substring_takeRight(lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__String_utf8SetAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_foldrAux_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Iterator_extract(lean_object*, lean_object*);
uint8_t l_String_isNat___lambda__1(uint32_t);
lean_object* l_String_pushn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__String_utf8GetAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_take(lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__Substring_prevn_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_isNat(lean_object*);
lean_object* l_Substring_foldr___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_contains(lean_object*, uint32_t);
lean_object* l_String_Iterator_extract_match__1(lean_object*);
lean_object* l_String_mapAux___at_String_toLower___spec__1(lean_object*, lean_object*);
lean_object* l_String_capitalize(lean_object*);
lean_object* l_String_Iterator_pos___boxed(lean_object*);
lean_object* l_String_isNat___lambda__1___boxed(lean_object*);
lean_object* l_String_join(lean_object*);
lean_object* l_String_revPosOfAux(lean_object*, uint32_t, lean_object*);
lean_object* l_String_Iterator_nextn(lean_object*, lean_object*);
lean_object* l_String_Iterator_isPrefixOfRemaining___boxed(lean_object*, lean_object*);
lean_object* l_Substring_takeWhile(lean_object*, lean_object*);
lean_object* l_String_singleton(uint32_t);
lean_object* l_String_Iterator_pos(lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__Substring_takeRightWhileAux___at_Substring_trimRight___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_beq___boxed(lean_object*, lean_object*);
lean_object* l_String_Iterator_prev(lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__String_utf8ExtractAux_u2081___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_String_back(lean_object*);
uint8_t l_String_all(lean_object*, lean_object*);
lean_object* l_Substring_foldl(lean_object*);
uint32_t l_Substring_get(lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__Substring_nextn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_any___boxed(lean_object*, lean_object*);
lean_object* l_String_takeRight(lean_object*, lean_object*);
lean_object* l_String_Iterator_setCurr_match__1(lean_object*);
lean_object* l_String_getOp___boxed(lean_object*, lean_object*);
lean_object* l_Substring_toIterator(lean_object*);
lean_object* l_Substring_hasBeq;
lean_object* l___private_Init_Data_String_Basic_0__Substring_prevn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Iterator_toString___boxed(lean_object*);
uint8_t l_String_isNat(lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__Substring_takeWhileAux___at_Substring_trimLeft___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_posOfAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_front___boxed(lean_object*);
lean_object* l_String_Iterator_remainingToString___boxed(lean_object*);
lean_object* l_Substring_trimRight(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_splitOn___boxed(lean_object*, lean_object*);
lean_object* l_String_Iterator_prevn(lean_object*, lean_object*);
lean_object* l_String_foldl(lean_object*);
lean_object* l_String_foldr___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_beq(lean_object*, lean_object*);
lean_object* l_Substring_toString_match__1___rarg(lean_object*, lean_object*);
lean_object* l_String_extract_match__1(lean_object*);
lean_object* l_String_Iterator_next(lean_object*);
lean_object* l_String_nextUntil___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_front___boxed(lean_object*);
lean_object* l_String_trimLeft(lean_object*);
lean_object* l_String_join___boxed(lean_object*);
lean_object* l_String_dropRight(lean_object*, lean_object*);
lean_object* l_String_offsetOfPos___boxed(lean_object*, lean_object*);
lean_object* l_String_mapAux___at_String_toUpper___spec__1(lean_object*, lean_object*);
lean_object* l_String_splitAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_takeRightWhile(lean_object*, lean_object*);
uint8_t l_String_Iterator_hasNext(lean_object*);
lean_object* l_String_all___lambda__1___boxed(lean_object*, lean_object*);
uint32_t l_String_front(lean_object*);
lean_object* l_String_dropWhile___boxed(lean_object*, lean_object*);
lean_object* l_Substring_atEnd___boxed(lean_object*, lean_object*);
lean_object* l_Substring_posOf___boxed(lean_object*, lean_object*);
lean_object* l_String_nextWhile(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Iterator_hasNext___boxed(lean_object*);
lean_object* l_String_revPosOf___boxed(lean_object*, lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_String_posOfAux(lean_object*, uint32_t, lean_object*, lean_object*);
lean_object* l_String_splitAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_set_match__1(lean_object*);
uint8_t l_String_isEmpty(lean_object*);
lean_object* l_String_foldrAux(lean_object*);
lean_object* l_String_foldlAux_loop(lean_object*);
lean_object* l_Substring_takeRightWhile(lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__Substring_takeWhileAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__Substring_nextn_match__1(lean_object*);
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Substring_foldl___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__Substring_prevn_match__1(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Substring_take(lean_object*, lean_object*);
lean_object* l_Nat_repeat_loop___at_String_pushn___spec__1(uint32_t, lean_object*, lean_object*);
lean_object* l_String_foldr___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_isNat___boxed(lean_object*);
lean_object* l_String_split(lean_object*, lean_object*);
lean_object* l_String_any___boxed(lean_object*, lean_object*);
uint32_t l_String_Iterator_curr(lean_object*);
lean_object* l_Substring_foldr(lean_object*);
lean_object* l_String_extract___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_decapitalize(lean_object*);
lean_object* l_String_takeWhile___boxed(lean_object*, lean_object*);
lean_object* l_String_mapAux(lean_object*, lean_object*, lean_object*);
lean_object* l_String_str(lean_object*, uint32_t);
lean_object* l_Char_toLower(uint32_t);
uint8_t l_String_Iterator_hasPrev(lean_object*);
lean_object* l_String_foldlAux_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_decLt___boxed(lean_object*, lean_object*);
lean_object* l_String_foldrAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__String_utf8PrevAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_trimLeft(lean_object*);
lean_object* l_String_Iterator_setCurr(lean_object*, uint32_t);
uint8_t l_String_isPrefixOf_loop(lean_object*, lean_object*, lean_object*);
uint8_t l_String_all___lambda__1(lean_object*, uint32_t);
uint32_t l_Substring_front(lean_object*);
lean_object* l_Char_toString(uint32_t);
lean_object* l___private_Init_Data_String_Basic_0__String_utf8ExtractAux_u2081_match__1(lean_object*);
lean_object* l_Substring_toIterator___boxed(lean_object*);
lean_object* l_Substring_dropRight(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Substring_splitOn_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_String_anyAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__Substring_nextn_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toLower(lean_object*);
lean_object* l_String_foldlAux(lean_object*);
lean_object* l_String_toNat_x3f___boxed(lean_object*);
lean_object* l_String_foldrAux_loop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_posOf___boxed(lean_object*, lean_object*);
lean_object* l_String_instLTString;
lean_object* l_String_isPrefixOf_loop___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_atEnd(lean_object*, lean_object*);
lean_object* l_String_isPrefixOf___boxed(lean_object*, lean_object*);
lean_object* l_String_get_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
lean_object* l_String_mkIterator(lean_object*);
lean_object* l_Substring_splitOn_loop___closed__1;
lean_object* l_String_map(lean_object*, lean_object*);
lean_object* l_String_Iterator_toString(lean_object*);
lean_object* l_String_foldrAux_loop(lean_object*);
lean_object* l_List_asString(lean_object*);
lean_object* l_String_all___boxed(lean_object*, lean_object*);
lean_object* l_String_Iterator_forward_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__Substring_next(lean_object*, lean_object*);
lean_object* l_String_toNat_x3f___closed__1;
lean_object* l___private_Init_Data_String_Basic_0__Substring_prevn(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__String_utf8ExtractAux_u2081(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_isEmpty(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Substring_splitOn_loop___closed__2;
lean_object* l_String_foldr(lean_object*);
lean_object* l_String_Iterator_setCurr___boxed(lean_object*, lean_object*);
lean_object* l_Substring_posOf(lean_object*, uint32_t);
lean_object* l_Substring_extract_match__1(lean_object*);
lean_object* l_String_Iterator_remainingBytes(lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__Substring_takeWhileAux___at_String_nextUntil___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_toString(lean_object*);
lean_object* l_Substring_foldr___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toNat_x3f(lean_object*);
lean_object* l_String_foldrAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_set_match__1___rarg(lean_object*, lean_object*, uint32_t, lean_object*);
lean_object* l_String_push___boxed(lean_object*, lean_object*);
lean_object* l_String_drop(lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__String_utf8GetAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_pushn(lean_object*, uint32_t, lean_object*);
lean_object* l_Substring_drop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__String_utf8ExtractAux_u2082(lean_object*, lean_object*, lean_object*);
lean_object* l_String_singleton___boxed(lean_object*);
lean_object* l_String_contains___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Substring_get___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__Substring_nextn_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_posOf(lean_object*, uint32_t);
lean_object* l_Substring_dropRightWhile(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_String_modify___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__String_utf8GetAux_match__1(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l___private_Init_Data_String_Basic_0__String_utf8SetAux(uint32_t, lean_object*, lean_object*, lean_object*);
lean_object* l_String_append_match__1(lean_object*);
lean_object* l_String_Iterator_extract_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_length_match__1(lean_object*);
lean_object* l_Substring_contains___boxed(lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
lean_object* l_String_dropRightWhile(lean_object*, lean_object*);
lean_object* l_String_instAppendString___closed__1;
lean_object* l_String_dropRightWhile___boxed(lean_object*, lean_object*);
lean_object* l_String_offsetOfPos(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_String_Iterator_forward_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_length_match__1___rarg(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Char_toString___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Basic_0__Substring_next___boxed(lean_object*, lean_object*);
lean_object* l_List_asString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_String_instLTString() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_String_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_string_dec_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_String_length_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_string_data(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
lean_object* l_String_length_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_length_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_String_length___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_length(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_String_push_match__1___rarg(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_string_data(x_1);
x_5 = lean_box_uint32(x_2);
x_6 = lean_apply_2(x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_String_push_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_push_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_String_push_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_String_push_match__1___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_String_push___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = lean_string_push(x_1, x_3);
return x_4;
}
}
lean_object* l_String_append_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_string_data(x_1);
x_5 = lean_string_data(x_2);
x_6 = lean_apply_2(x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_String_append_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_append_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_String_append___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_append(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_String_toList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_data(x_1);
return x_2;
}
}
lean_object* l___private_Init_Data_String_Basic_0__String_utf8GetAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_dec(x_1);
x_9 = lean_apply_4(x_5, x_7, x_8, x_2, x_3);
return x_9;
}
}
}
lean_object* l___private_Init_Data_String_Basic_0__String_utf8GetAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_String_Basic_0__String_utf8GetAux_match__1___rarg), 5, 0);
return x_2;
}
}
uint32_t l___private_Init_Data_String_Basic_0__String_utf8GetAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_nat_dec_eq(x_2, x_3);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_9 = l_String_csize(x_8);
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
lean_dec(x_6);
lean_dec(x_2);
x_12 = lean_unbox_uint32(x_5);
lean_dec(x_5);
return x_12;
}
}
}
}
lean_object* l___private_Init_Data_String_Basic_0__String_utf8GetAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = l___private_Init_Data_String_Basic_0__String_utf8GetAux(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box_uint32(x_4);
return x_5;
}
}
lean_object* l_String_get_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_string_data(x_1);
x_5 = lean_apply_2(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_String_get_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_get_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_String_get___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_string_utf8_get(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
uint32_t l_String_getOp(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; 
x_3 = lean_string_utf8_get(x_1, x_2);
return x_3;
}
}
lean_object* l_String_getOp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = l_String_getOp(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
lean_object* l___private_Init_Data_String_Basic_0__String_utf8SetAux(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_nat_dec_eq(x_3, x_4);
if (x_9 == 0)
{
uint32_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unbox_uint32(x_7);
x_11 = l_String_csize(x_10);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_11);
x_13 = l___private_Init_Data_String_Basic_0__String_utf8SetAux(x_1, x_8, x_12, x_4);
lean_dec(x_12);
lean_ctor_set(x_2, 1, x_13);
return x_2;
}
else
{
lean_object* x_14; 
lean_dec(x_7);
x_14 = lean_box_uint32(x_1);
lean_ctor_set(x_2, 0, x_14);
return x_2;
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_2);
x_17 = lean_nat_dec_eq(x_3, x_4);
if (x_17 == 0)
{
uint32_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_unbox_uint32(x_15);
x_19 = l_String_csize(x_18);
x_20 = lean_nat_add(x_3, x_19);
lean_dec(x_19);
x_21 = l___private_Init_Data_String_Basic_0__String_utf8SetAux(x_1, x_16, x_20, x_4);
lean_dec(x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_15);
x_23 = lean_box_uint32(x_1);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
return x_24;
}
}
}
}
}
lean_object* l___private_Init_Data_String_Basic_0__String_utf8SetAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_6 = l___private_Init_Data_String_Basic_0__String_utf8SetAux(x_5, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_String_set_match__1___rarg(lean_object* x_1, lean_object* x_2, uint32_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_string_data(x_1);
x_6 = lean_box_uint32(x_3);
x_7 = lean_apply_3(x_4, x_5, x_2, x_6);
return x_7;
}
}
lean_object* l_String_set_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_set_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_String_set_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_6 = l_String_set_match__1___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l_String_set___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_String_modify(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_String_modify___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_modify(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_String_next___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Data_String_Basic_0__String_utf8PrevAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_8 = l_String_csize(x_7);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_8);
x_10 = lean_nat_dec_eq(x_9, x_3);
if (x_10 == 0)
{
lean_dec(x_2);
x_1 = x_6;
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_6);
return x_2;
}
}
}
}
lean_object* l___private_Init_Data_String_Basic_0__String_utf8PrevAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_String_Basic_0__String_utf8PrevAux(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_String_prev___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_utf8_prev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
uint32_t l_String_front(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
return x_3;
}
}
lean_object* l_String_front___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_String_front(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
uint32_t l_String_back(lean_object* x_1) {
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
lean_object* l_String_back___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_String_back(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
lean_object* l_String_atEnd_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_String_atEnd_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_atEnd_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_String_atEnd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_string_utf8_at_end(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_String_posOfAux(lean_object* x_1, uint32_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_4, x_3);
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = lean_string_utf8_get(x_1, x_4);
x_7 = x_6 == x_2;
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
else
{
return x_4;
}
}
}
lean_object* l_String_posOfAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_6 = l_String_posOfAux(x_1, x_5, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_String_posOf(lean_object* x_1, uint32_t x_2) {
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
lean_object* l_String_posOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_String_posOf(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_String_revPosOfAux(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; uint8_t x_5; 
x_4 = lean_string_utf8_get(x_1, x_3);
x_5 = x_4 == x_2;
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_string_utf8_prev(x_1, x_3);
lean_dec(x_3);
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_box(0);
return x_10;
}
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_3);
return x_11;
}
}
}
lean_object* l_String_revPosOfAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_String_revPosOfAux(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_String_revPosOf(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_string_utf8_prev(x_1, x_3);
lean_dec(x_3);
x_7 = l_String_revPosOfAux(x_1, x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_box(0);
return x_8;
}
}
}
lean_object* l_String_revPosOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_String_revPosOf(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Data_String_Basic_0__String_utf8ExtractAux_u2082(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_nat_dec_eq(x_2, x_3);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_unbox_uint32(x_6);
x_10 = l_String_csize(x_9);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_10);
x_12 = l___private_Init_Data_String_Basic_0__String_utf8ExtractAux_u2082(x_7, x_11, x_3);
lean_dec(x_11);
lean_ctor_set(x_1, 1, x_12);
return x_1;
}
else
{
lean_object* x_13; 
lean_free_object(x_1);
lean_dec(x_7);
lean_dec(x_6);
x_13 = lean_box(0);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = lean_nat_dec_eq(x_2, x_3);
if (x_16 == 0)
{
uint32_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_unbox_uint32(x_14);
x_18 = l_String_csize(x_17);
x_19 = lean_nat_add(x_2, x_18);
lean_dec(x_18);
x_20 = l___private_Init_Data_String_Basic_0__String_utf8ExtractAux_u2082(x_15, x_19, x_3);
lean_dec(x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_15);
lean_dec(x_14);
x_22 = lean_box(0);
return x_22;
}
}
}
}
}
lean_object* l___private_Init_Data_String_Basic_0__String_utf8ExtractAux_u2082___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_String_Basic_0__String_utf8ExtractAux_u2082(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Data_String_Basic_0__String_utf8ExtractAux_u2081_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; 
lean_dec(x_6);
x_7 = lean_apply_3(x_5, x_2, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_apply_6(x_6, x_1, x_8, x_9, x_2, x_3, x_4);
return x_10;
}
}
}
lean_object* l___private_Init_Data_String_Basic_0__String_utf8ExtractAux_u2081_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_String_Basic_0__String_utf8ExtractAux_u2081_match__1___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_String_Basic_0__String_utf8ExtractAux_u2081(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_nat_dec_eq(x_2, x_3);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_9 = lean_unbox_uint32(x_6);
lean_dec(x_6);
x_10 = l_String_csize(x_9);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_10);
lean_dec(x_2);
x_1 = x_7;
x_2 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
x_13 = l___private_Init_Data_String_Basic_0__String_utf8ExtractAux_u2082(x_1, x_2, x_4);
lean_dec(x_2);
return x_13;
}
}
}
}
lean_object* l___private_Init_Data_String_Basic_0__String_utf8ExtractAux_u2081___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Basic_0__String_utf8ExtractAux_u2081(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_String_extract_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_string_data(x_1);
x_6 = lean_apply_3(x_4, x_5, x_2, x_3);
return x_6;
}
}
lean_object* l_String_extract_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_extract_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_String_extract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_String_splitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_4);
if (x_6 == 0)
{
uint32_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_string_utf8_get(x_1, x_4);
x_8 = lean_box_uint32(x_7);
lean_inc(x_2);
x_9 = lean_apply_1(x_2, x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
x_16 = lean_string_utf8_extract(x_1, x_3, x_15);
lean_dec(x_15);
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
lean_inc(x_13);
x_3 = x_13;
x_4 = x_13;
x_5 = x_17;
goto _start;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_19 = lean_string_utf8_extract(x_1, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_5);
x_21 = l_List_reverse___rarg(x_20);
return x_21;
}
}
}
lean_object* l_String_splitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_splitAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_String_split(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_String_splitAux(x_1, x_2, x_4, x_4, x_3);
return x_5;
}
}
lean_object* l_String_split___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_split(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_String_splitOnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_string_utf8_at_end(x_1, x_4);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get(x_1, x_4);
x_9 = lean_string_utf8_get(x_2, x_5);
x_10 = x_8 == x_9;
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
x_12 = lean_unsigned_to_nat(0u);
x_4 = x_11;
x_5 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
x_15 = lean_string_utf8_next(x_2, x_5);
lean_dec(x_5);
x_16 = lean_string_utf8_at_end(x_2, x_15);
if (x_16 == 0)
{
x_4 = x_14;
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_nat_sub(x_14, x_15);
lean_dec(x_15);
x_19 = lean_string_utf8_extract(x_1, x_3, x_18);
lean_dec(x_18);
lean_dec(x_3);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
x_21 = lean_unsigned_to_nat(0u);
lean_inc(x_14);
x_3 = x_14;
x_4 = x_14;
x_5 = x_21;
x_6 = x_20;
goto _start;
}
}
}
else
{
uint8_t x_23; 
x_23 = lean_string_utf8_at_end(x_2, x_5);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_5);
x_24 = lean_string_utf8_extract(x_1, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_6);
x_26 = l_List_reverse___rarg(x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_nat_sub(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
x_28 = lean_string_utf8_extract(x_1, x_3, x_27);
lean_dec(x_27);
lean_dec(x_3);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_6);
x_30 = l_Lean_instInhabitedParserDescr___closed__1;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_List_reverse___rarg(x_31);
return x_32;
}
}
}
}
lean_object* l_String_splitOnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_String_splitOnAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_String_splitOn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_instInhabitedParserDescr___closed__1;
x_4 = lean_string_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_String_splitOnAux(x_1, x_2, x_6, x_6, x_6, x_5);
lean_dec(x_1);
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
lean_object* l_String_splitOn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_splitOn(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_String_instInhabitedString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedParserDescr___closed__1;
return x_1;
}
}
static lean_object* _init_l_String_instAppendString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_append___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_String_instAppendString() {
_start:
{
lean_object* x_1; 
x_1 = l_String_instAppendString___closed__1;
return x_1;
}
}
lean_object* l_String_str(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_push(x_1, x_2);
return x_3;
}
}
lean_object* l_String_str___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_String_str(x_1, x_3);
return x_4;
}
}
lean_object* l_Nat_repeat_loop___at_String_pushn___spec__1(uint32_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
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
else
{
lean_dec(x_2);
return x_3;
}
}
}
lean_object* l_String_pushn(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_repeat_loop___at_String_pushn___spec__1(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Nat_repeat_loop___at_String_pushn___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_5 = l_Nat_repeat_loop___at_String_pushn___spec__1(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_String_pushn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_String_pushn(x_1, x_4, x_3);
return x_5;
}
}
uint8_t l_String_isEmpty(lean_object* x_1) {
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
lean_object* l_String_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_isEmpty(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_List_foldl___at_String_join___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_string_append(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l_String_join(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedParserDescr___closed__1;
x_3 = l_List_foldl___at_String_join___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_List_foldl___at_String_join___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at_String_join___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_String_join___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_join(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_String_singleton(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedParserDescr___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
lean_object* l_String_singleton___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_String_singleton(x_2);
return x_3;
}
}
lean_object* l_List_map___at_String_intercalate___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_string_data(x_4);
x_7 = l_List_map___at_String_intercalate___spec__1(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_string_data(x_8);
x_11 = l_List_map___at_String_intercalate___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_String_intercalate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_string_data(x_1);
x_4 = l_List_map___at_String_intercalate___spec__1(x_2);
x_5 = l_List_intercalate___rarg(x_3, x_4);
x_6 = lean_string_mk(x_5);
return x_6;
}
}
lean_object* l_String_mkIterator(lean_object* x_1) {
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
lean_object* l_String_Iterator_toString_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_String_Iterator_toString_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_Iterator_toString_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_String_Iterator_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_String_Iterator_toString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Iterator_toString(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_String_Iterator_remainingBytes(lean_object* x_1) {
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
lean_object* l_String_Iterator_remainingBytes___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Iterator_remainingBytes(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_String_Iterator_pos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_String_Iterator_pos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Iterator_pos(x_1);
lean_dec(x_1);
return x_2;
}
}
uint32_t l_String_Iterator_curr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint32_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_string_utf8_get(x_2, x_3);
return x_4;
}
}
lean_object* l_String_Iterator_curr___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_String_Iterator_curr(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
lean_object* l_String_Iterator_next(lean_object* x_1) {
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
lean_object* l_String_Iterator_prev(lean_object* x_1) {
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
uint8_t l_String_Iterator_hasNext(lean_object* x_1) {
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
lean_object* l_String_Iterator_hasNext___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_Iterator_hasNext(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_String_Iterator_hasPrev(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
return x_4;
}
}
lean_object* l_String_Iterator_hasPrev___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_Iterator_hasPrev(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_String_Iterator_setCurr_match__1___rarg(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box_uint32(x_2);
x_7 = lean_apply_3(x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_String_Iterator_setCurr_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_Iterator_setCurr_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_String_Iterator_setCurr_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_String_Iterator_setCurr_match__1___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_String_Iterator_setCurr(lean_object* x_1, uint32_t x_2) {
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
lean_object* l_String_Iterator_setCurr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_String_Iterator_setCurr(x_1, x_3);
return x_4;
}
}
lean_object* l_String_Iterator_toEnd(lean_object* x_1) {
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
lean_object* l_String_Iterator_extract_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_apply_4(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_String_Iterator_extract_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_Iterator_extract_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_String_Iterator_extract(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_string_dec_eq(x_3, x_5);
x_8 = l_instDecidableNot___rarg(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_6, x_4);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_string_utf8_extract(x_3, x_4, x_6);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Lean_instInhabitedParserDescr___closed__1;
return x_11;
}
}
else
{
lean_object* x_12; 
x_12 = l_Lean_instInhabitedParserDescr___closed__1;
return x_12;
}
}
}
lean_object* l_String_Iterator_extract___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Iterator_extract(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_String_Iterator_forward_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
x_9 = lean_apply_2(x_4, x_1, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l_String_Iterator_forward_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_Iterator_forward_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_String_Iterator_forward_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_Iterator_forward_match__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_String_Iterator_forward(lean_object* x_1, lean_object* x_2) {
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
lean_dec(x_2);
x_7 = l_String_Iterator_next(x_1);
x_1 = x_7;
x_2 = x_6;
goto _start;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_String_Iterator_remainingToString(lean_object* x_1) {
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
lean_object* l_String_Iterator_remainingToString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Iterator_remainingToString(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_String_Iterator_isPrefixOfRemaining(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_string_utf8_byte_size(x_3);
x_8 = lean_string_utf8_extract(x_3, x_4, x_7);
x_9 = lean_nat_sub(x_7, x_4);
lean_dec(x_7);
x_10 = lean_nat_add(x_6, x_9);
lean_dec(x_9);
x_11 = lean_string_utf8_extract(x_5, x_6, x_10);
lean_dec(x_10);
x_12 = lean_string_dec_eq(x_8, x_11);
lean_dec(x_11);
lean_dec(x_8);
return x_12;
}
}
lean_object* l_String_Iterator_isPrefixOfRemaining___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_Iterator_isPrefixOfRemaining(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_String_Iterator_nextn(lean_object* x_1, lean_object* x_2) {
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
lean_dec(x_2);
x_7 = l_String_Iterator_next(x_1);
x_1 = x_7;
x_2 = x_6;
goto _start;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_String_Iterator_prevn(lean_object* x_1, lean_object* x_2) {
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
lean_dec(x_2);
x_7 = l_String_Iterator_prev(x_1);
x_1 = x_7;
x_2 = x_6;
goto _start;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_String_offsetOfPosAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_3, x_2);
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
lean_object* l_String_offsetOfPosAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_offsetOfPosAux(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_String_offsetOfPos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_offsetOfPosAux(x_1, x_2, x_3, x_3);
return x_4;
}
}
lean_object* l_String_offsetOfPos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_offsetOfPos(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_String_foldlAux_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_eq(x_4, x_3);
if (x_6 == 0)
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
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_String_foldlAux_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_foldlAux_loop___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_String_foldlAux_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_foldlAux_loop___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_String_foldlAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_foldlAux_loop___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_String_foldlAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_foldlAux___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_String_foldlAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_foldlAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_String_foldl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_string_utf8_byte_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_String_foldlAux_loop___rarg(x_1, x_3, x_4, x_5, x_2);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_String_foldl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_foldl___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_String_foldl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_foldl___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_String_foldrAux_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_eq(x_5, x_4);
if (x_6 == 0)
{
uint32_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_string_utf8_get(x_3, x_5);
x_8 = lean_string_utf8_next(x_3, x_5);
lean_inc(x_1);
x_9 = l_String_foldrAux_loop___rarg(x_1, x_2, x_3, x_4, x_8);
lean_dec(x_8);
x_10 = lean_box_uint32(x_7);
x_11 = lean_apply_2(x_1, x_10, x_9);
return x_11;
}
else
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
}
lean_object* l_String_foldrAux_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_foldrAux_loop___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_String_foldrAux_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_foldrAux_loop___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_String_foldrAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_foldrAux_loop___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_String_foldrAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_foldrAux___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_String_foldrAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_foldrAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_String_foldr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_string_utf8_byte_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_String_foldrAux_loop___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_String_foldr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_foldr___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_String_foldr___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_foldr___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
uint8_t l_String_anyAux_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_4, x_2);
if (x_5 == 0)
{
uint32_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_string_utf8_get(x_1, x_4);
x_7 = lean_box_uint32(x_6);
lean_inc(x_3);
x_8 = lean_apply_1(x_3, x_7);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
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
lean_dec(x_3);
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_13 = 0;
return x_13;
}
}
}
lean_object* l_String_anyAux_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_String_anyAux_loop(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_String_anyAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_String_anyAux_loop(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_String_anyAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_String_anyAux(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_String_any(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_String_anyAux_loop(x_1, x_3, x_2, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_String_any___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_any(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_String_all___lambda__1(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_box_uint32(x_2);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
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
uint8_t l_String_all(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_alloc_closure((void*)(l_String_all___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_String_anyAux_loop(x_1, x_4, x_3, x_5);
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
lean_object* l_String_all___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_String_all___lambda__1(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_String_all___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_all(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_String_contains___lambda__1(uint32_t x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_2 == x_1;
return x_3;
}
}
uint8_t l_String_contains(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_box_uint32(x_2);
x_4 = lean_alloc_closure((void*)(l_String_contains___lambda__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_String_anyAux_loop(x_1, x_5, x_4, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_String_contains___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_String_contains___lambda__1(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_String_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_String_contains(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_String_mapAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_utf8_at_end(x_3, x_2);
if (x_4 == 0)
{
uint32_t x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_string_utf8_get(x_3, x_2);
x_6 = lean_box_uint32(x_5);
lean_inc(x_1);
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
lean_dec(x_1);
return x_3;
}
}
}
lean_object* l_String_map(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_mapAux(x_1, x_3, x_2);
return x_4;
}
}
uint8_t l_String_isNat___lambda__1(uint32_t x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Char_isDigit(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
static lean_object* _init_l_String_isNat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_isNat___lambda__1___boxed), 1, 0);
return x_1;
}
}
uint8_t l_String_isNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = l_String_isNat___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_String_anyAux_loop(x_1, x_2, x_3, x_4);
lean_dec(x_2);
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
lean_object* l_String_isNat___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_String_isNat___lambda__1(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_String_isNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_isNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_String_toNat_x3f___lambda__1(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(10u);
x_4 = lean_nat_mul(x_1, x_3);
x_5 = lean_uint32_to_nat(x_2);
x_6 = lean_unsigned_to_nat(48u);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_5);
x_8 = lean_nat_add(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
return x_8;
}
}
static lean_object* _init_l_String_toNat_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_toNat_x3f___lambda__1___boxed), 2, 0);
return x_1;
}
}
lean_object* l_String_toNat_x3f(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_isNat(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l_String_toNat_x3f___closed__1;
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_String_foldlAux_loop___rarg(x_5, x_1, x_4, x_6, x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
lean_object* l_String_toNat_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_String_toNat_x3f___lambda__1(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_String_toNat_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_toNat_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_String_isPrefixOf_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_utf8_at_end(x_1, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; 
x_5 = lean_string_utf8_get(x_1, x_3);
x_6 = lean_string_utf8_get(x_2, x_3);
x_7 = x_5 == x_6;
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_string_utf8_next(x_2, x_3);
lean_dec(x_3);
x_3 = x_9;
goto _start;
}
}
else
{
uint8_t x_11; 
lean_dec(x_3);
x_11 = 1;
return x_11;
}
}
}
lean_object* l_String_isPrefixOf_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_isPrefixOf_loop(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_String_isPrefixOf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_string_length(x_1);
x_4 = lean_string_length(x_2);
x_5 = lean_nat_dec_le(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_String_isPrefixOf_loop(x_1, x_2, x_7);
return x_8;
}
}
}
lean_object* l_String_isPrefixOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_isPrefixOf(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Substring_isEmpty(lean_object* x_1) {
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
lean_object* l_Substring_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Substring_isEmpty(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Substring_toString_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_3(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Substring_toString_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Substring_toString_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Substring_toString(lean_object* x_1) {
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
lean_object* l_Substring_toString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Substring_toString(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Substring_toIterator(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_Substring_toIterator___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Substring_toIterator(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Substring_get_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_3, x_4, x_5, x_6, x_2);
return x_7;
}
}
lean_object* l_Substring_get_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Substring_get_match__1___rarg), 3, 0);
return x_2;
}
}
uint32_t l_Substring_get(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Substring_get___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = l_Substring_get(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
lean_object* l___private_Init_Data_String_Basic_0__Substring_next(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Init_Data_String_Basic_0__Substring_next___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_String_Basic_0__Substring_next(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Data_String_Basic_0__Substring_prev(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Init_Data_String_Basic_0__Substring_prev___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_String_Basic_0__Substring_prev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Data_String_Basic_0__Substring_nextn_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
x_10 = lean_apply_3(x_5, x_1, x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_5);
x_11 = lean_apply_2(x_4, x_1, x_3);
return x_11;
}
}
}
lean_object* l___private_Init_Data_String_Basic_0__Substring_nextn_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_String_Basic_0__Substring_nextn_match__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_String_Basic_0__Substring_nextn_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_String_Basic_0__Substring_nextn_match__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Init_Data_String_Basic_0__Substring_nextn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_nat_add(x_9, x_3);
x_12 = lean_nat_dec_eq(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_string_utf8_next(x_8, x_11);
lean_dec(x_11);
x_14 = lean_nat_sub(x_13, x_9);
lean_dec(x_13);
x_2 = x_7;
x_3 = x_14;
goto _start;
}
else
{
lean_dec(x_11);
x_2 = x_7;
goto _start;
}
}
else
{
lean_dec(x_2);
return x_3;
}
}
}
lean_object* l___private_Init_Data_String_Basic_0__Substring_nextn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_String_Basic_0__Substring_nextn(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Data_String_Basic_0__Substring_prevn_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
x_10 = lean_apply_3(x_5, x_1, x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_5);
x_11 = lean_apply_2(x_4, x_1, x_3);
return x_11;
}
}
}
lean_object* l___private_Init_Data_String_Basic_0__Substring_prevn_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_String_Basic_0__Substring_prevn_match__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_String_Basic_0__Substring_prevn_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_String_Basic_0__Substring_prevn_match__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Init_Data_String_Basic_0__Substring_prevn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_nat_add(x_9, x_3);
x_11 = lean_nat_dec_eq(x_10, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_12 = lean_string_utf8_prev(x_8, x_10);
lean_dec(x_10);
x_13 = lean_nat_sub(x_12, x_9);
lean_dec(x_12);
x_2 = x_7;
x_3 = x_13;
goto _start;
}
else
{
lean_dec(x_10);
x_2 = x_7;
goto _start;
}
}
else
{
lean_dec(x_2);
return x_3;
}
}
}
lean_object* l___private_Init_Data_String_Basic_0__Substring_prevn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_String_Basic_0__Substring_prevn(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
uint32_t l_Substring_front(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint32_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_add(x_3, x_4);
x_6 = lean_string_utf8_get(x_2, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Substring_front___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Substring_front(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
lean_object* l_Substring_posOf(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_4);
x_6 = l_String_posOfAux(x_3, x_2, x_5, x_4);
lean_dec(x_5);
lean_dec(x_3);
x_7 = lean_nat_sub(x_6, x_4);
lean_dec(x_4);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Substring_posOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_Substring_posOf(x_1, x_3);
return x_4;
}
}
lean_object* l_Substring_drop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_apply_5(x_3, x_1, x_4, x_5, x_6, x_2);
return x_7;
}
}
lean_object* l_Substring_drop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Substring_drop_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Substring_drop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l___private_Init_Data_String_Basic_0__Substring_nextn(x_1, x_2, x_6);
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
lean_object* l_Substring_dropRight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_nat_sub(x_5, x_4);
lean_dec(x_5);
x_7 = l___private_Init_Data_String_Basic_0__Substring_prevn(x_1, x_2, x_6);
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
lean_object* l_Substring_take(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l___private_Init_Data_String_Basic_0__Substring_nextn(x_1, x_2, x_5);
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
lean_object* l_Substring_takeRight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_nat_sub(x_5, x_4);
x_7 = l___private_Init_Data_String_Basic_0__Substring_prevn(x_1, x_2, x_6);
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
uint8_t l_Substring_atEnd(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Substring_atEnd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Substring_atEnd(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Substring_extract_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_5(x_4, x_5, x_6, x_7, x_2, x_3);
return x_8;
}
}
lean_object* l_Substring_extract_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Substring_extract_match__1___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Substring_extract___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_instInhabitedParserDescr___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Substring_extract(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
lean_dec(x_7);
x_8 = lean_nat_dec_le(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_nat_add(x_6, x_2);
x_10 = lean_nat_add(x_6, x_3);
lean_dec(x_6);
lean_ctor_set(x_1, 2, x_10);
lean_ctor_set(x_1, 1, x_9);
return x_1;
}
else
{
lean_object* x_11; 
lean_free_object(x_1);
lean_dec(x_6);
lean_dec(x_5);
x_11 = l_Substring_extract___closed__1;
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_nat_dec_le(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_nat_add(x_13, x_2);
x_16 = lean_nat_add(x_13, x_3);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_12);
x_18 = l_Substring_extract___closed__1;
return x_18;
}
}
}
}
lean_object* l_Substring_extract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Substring_splitOn_loop___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedParserDescr___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Substring_splitOn_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_instInhabitedParserDescr___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Substring_splitOn_loop___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Substring_splitOn_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_6, x_3);
if (x_9 == 0)
{
uint32_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; uint8_t x_16; 
x_10 = lean_string_utf8_get(x_2, x_7);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_nat_add(x_12, x_6);
x_15 = lean_string_utf8_get(x_11, x_14);
x_16 = x_15 == x_10;
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_7);
x_17 = lean_nat_dec_eq(x_14, x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
x_18 = lean_string_utf8_next(x_11, x_14);
lean_dec(x_14);
x_19 = lean_nat_sub(x_18, x_12);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_6 = x_19;
x_7 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_14);
x_22 = lean_unsigned_to_nat(0u);
x_7 = x_22;
goto _start;
}
}
else
{
lean_object* x_24; uint8_t x_25; uint8_t x_26; 
x_24 = lean_string_utf8_next(x_2, x_7);
lean_dec(x_7);
x_25 = lean_string_utf8_at_end(x_2, x_24);
x_26 = lean_nat_dec_eq(x_14, x_13);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_6);
x_27 = lean_string_utf8_next(x_11, x_14);
lean_dec(x_14);
x_28 = lean_nat_sub(x_27, x_12);
lean_dec(x_27);
if (x_25 == 0)
{
x_6 = x_28;
x_7 = x_24;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_nat_sub(x_28, x_24);
lean_dec(x_24);
lean_inc(x_4);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_5);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_8);
x_33 = lean_unsigned_to_nat(0u);
lean_inc(x_28);
x_5 = x_28;
x_6 = x_28;
x_7 = x_33;
x_8 = x_32;
goto _start;
}
}
else
{
lean_dec(x_14);
if (x_25 == 0)
{
x_7 = x_24;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_nat_sub(x_6, x_24);
lean_dec(x_24);
lean_inc(x_4);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_4);
lean_ctor_set(x_37, 1, x_5);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_8);
x_39 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_5 = x_6;
x_7 = x_39;
x_8 = x_38;
goto _start;
}
}
}
}
else
{
uint8_t x_41; 
x_41 = lean_string_utf8_at_end(x_2, x_7);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_7);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_5);
lean_ctor_set(x_42, 2, x_6);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_8);
x_44 = l_List_reverse___rarg(x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_nat_sub(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
lean_ctor_set(x_46, 2, x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_8);
x_48 = l_Substring_splitOn_loop___closed__2;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_List_reverse___rarg(x_49);
return x_50;
}
}
}
}
lean_object* l_Substring_splitOn_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Substring_splitOn_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Substring_splitOn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_instInhabitedParserDescr___closed__1;
x_4 = lean_string_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
x_10 = l_Substring_splitOn_loop(x_1, x_2, x_5, x_6, x_7, x_7, x_9, x_8);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
lean_object* l_Substring_splitOn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Substring_splitOn(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Substring_foldl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_String_foldlAux_loop___rarg(x_1, x_4, x_6, x_5, x_2);
lean_dec(x_6);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Substring_foldl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Substring_foldl___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Substring_foldr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = l_String_foldrAux_loop___rarg(x_1, x_2, x_4, x_6, x_5);
return x_7;
}
}
lean_object* l_Substring_foldr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Substring_foldr___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Substring_foldr___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_foldr___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
uint8_t l_Substring_any(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_String_anyAux_loop(x_3, x_5, x_2, x_4);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Substring_any___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Substring_any(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Substring_all(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_alloc_closure((void*)(l_String_all___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_String_anyAux_loop(x_4, x_6, x_3, x_5);
lean_dec(x_6);
lean_dec(x_4);
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
lean_object* l_Substring_all___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Substring_all(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Substring_contains(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_box_uint32(x_2);
x_4 = lean_alloc_closure((void*)(l_String_contains___lambda__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_String_anyAux_loop(x_5, x_7, x_4, x_6);
lean_dec(x_7);
lean_dec(x_5);
return x_8;
}
}
lean_object* l_Substring_contains___boxed(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Init_Data_String_Basic_0__Substring_takeWhileAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_4, x_2);
if (x_5 == 0)
{
uint32_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_string_utf8_get(x_1, x_4);
x_7 = lean_box_uint32(x_6);
lean_inc(x_3);
x_8 = lean_apply_1(x_3, x_7);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_3);
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
else
{
lean_dec(x_3);
return x_4;
}
}
}
lean_object* l___private_Init_Data_String_Basic_0__Substring_takeWhileAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Basic_0__Substring_takeWhileAux(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Substring_takeWhile_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_3, x_4, x_5, x_6, x_2);
return x_7;
}
}
lean_object* l_Substring_takeWhile_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Substring_takeWhile_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Substring_takeWhile(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Init_Data_String_Basic_0__Substring_takeWhileAux(x_4, x_6, x_2, x_5);
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
x_11 = l___private_Init_Data_String_Basic_0__Substring_takeWhileAux(x_8, x_10, x_2, x_9);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
}
}
lean_object* l_Substring_dropWhile(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Init_Data_String_Basic_0__Substring_takeWhileAux(x_4, x_6, x_2, x_5);
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
x_11 = l___private_Init_Data_String_Basic_0__Substring_takeWhileAux(x_8, x_10, x_2, x_9);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_10);
return x_12;
}
}
}
lean_object* l___private_Init_Data_String_Basic_0__Substring_takeRightWhileAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_4, x_2);
if (x_5 == 0)
{
lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_string_utf8_prev(x_1, x_4);
x_7 = lean_string_utf8_get(x_1, x_6);
x_8 = lean_box_uint32(x_7);
lean_inc(x_3);
x_9 = lean_apply_1(x_3, x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_6);
lean_dec(x_3);
return x_4;
}
else
{
lean_dec(x_4);
x_4 = x_6;
goto _start;
}
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
lean_object* l___private_Init_Data_String_Basic_0__Substring_takeRightWhileAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Basic_0__Substring_takeRightWhileAux(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Substring_takeRightWhile(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Init_Data_String_Basic_0__Substring_takeRightWhileAux(x_4, x_5, x_2, x_6);
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
x_11 = l___private_Init_Data_String_Basic_0__Substring_takeRightWhileAux(x_8, x_9, x_2, x_10);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_10);
return x_12;
}
}
}
lean_object* l_Substring_dropRightWhile(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Init_Data_String_Basic_0__Substring_takeRightWhileAux(x_4, x_5, x_2, x_6);
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
x_11 = l___private_Init_Data_String_Basic_0__Substring_takeRightWhileAux(x_8, x_9, x_2, x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
}
}
lean_object* l___private_Init_Data_String_Basic_0__Substring_takeWhileAux___at_Substring_trimLeft___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_3, x_2);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = lean_string_utf8_get(x_1, x_3);
x_6 = l_Char_isWhitespace(x_5);
if (x_6 == 0)
{
return x_3;
}
else
{
lean_object* x_7; 
x_7 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_7;
goto _start;
}
}
else
{
return x_3;
}
}
}
lean_object* l_Substring_trimLeft(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = l___private_Init_Data_String_Basic_0__Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_3, x_5, x_4);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_10 = l___private_Init_Data_String_Basic_0__Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_7, x_9, x_8);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
}
}
lean_object* l___private_Init_Data_String_Basic_0__Substring_takeWhileAux___at_Substring_trimLeft___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_String_Basic_0__Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Data_String_Basic_0__Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_5 = lean_string_utf8_prev(x_1, x_3);
x_6 = lean_string_utf8_get(x_1, x_5);
x_7 = l_Char_isWhitespace(x_6);
if (x_7 == 0)
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
else
{
return x_3;
}
}
}
lean_object* l_Substring_trimRight(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = l___private_Init_Data_String_Basic_0__Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_3, x_4, x_5);
lean_ctor_set(x_1, 2, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_10 = l___private_Init_Data_String_Basic_0__Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_7, x_8, x_9);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_10);
return x_11;
}
}
}
lean_object* l___private_Init_Data_String_Basic_0__Substring_takeRightWhileAux___at_Substring_trimRight___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_String_Basic_0__Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Substring_trim(lean_object* x_1) {
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
x_6 = l___private_Init_Data_String_Basic_0__Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_3, x_5, x_4);
x_7 = l___private_Init_Data_String_Basic_0__Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_3, x_6, x_5);
lean_ctor_set(x_1, 2, x_7);
lean_ctor_set(x_1, 1, x_6);
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
x_11 = l___private_Init_Data_String_Basic_0__Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_8, x_10, x_9);
x_12 = l___private_Init_Data_String_Basic_0__Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_8, x_11, x_10);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
return x_13;
}
}
}
uint8_t l_Substring_isNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_String_isNat___closed__1;
x_6 = l_String_anyAux_loop(x_2, x_4, x_5, x_3);
lean_dec(x_4);
lean_dec(x_2);
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
lean_object* l_Substring_isNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Substring_isNat(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Substring_toNat_x3f(lean_object* x_1) {
_start:
{
uint8_t x_2; 
lean_inc(x_1);
x_2 = l_Substring_isNat(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_String_toNat_x3f___closed__1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_String_foldlAux_loop___rarg(x_7, x_4, x_6, x_5, x_8);
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
uint8_t l_Substring_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_string_utf8_extract(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_string_utf8_extract(x_7, x_8, x_9);
x_11 = lean_string_dec_eq(x_6, x_10);
lean_dec(x_10);
lean_dec(x_6);
return x_11;
}
}
lean_object* l_Substring_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Substring_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Substring_hasBeq___closed__1() {
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
x_1 = l_Substring_hasBeq___closed__1;
return x_1;
}
}
lean_object* l_String_drop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
lean_inc(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_3);
x_6 = l___private_Init_Data_String_Basic_0__Substring_nextn(x_5, x_2, x_4);
lean_dec(x_5);
x_7 = lean_nat_add(x_4, x_6);
lean_dec(x_6);
x_8 = lean_string_utf8_extract(x_1, x_7, x_3);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_String_dropRight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
lean_inc(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_3);
x_6 = lean_nat_sub(x_3, x_4);
lean_dec(x_3);
x_7 = l___private_Init_Data_String_Basic_0__Substring_prevn(x_5, x_2, x_6);
lean_dec(x_5);
x_8 = lean_nat_add(x_4, x_7);
lean_dec(x_7);
x_9 = lean_string_utf8_extract(x_1, x_4, x_8);
lean_dec(x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_String_take(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_3);
x_6 = l___private_Init_Data_String_Basic_0__Substring_nextn(x_5, x_2, x_4);
lean_dec(x_5);
x_7 = lean_nat_add(x_4, x_6);
lean_dec(x_6);
x_8 = lean_string_utf8_extract(x_1, x_4, x_7);
lean_dec(x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_String_takeRight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
lean_inc(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_3);
x_6 = lean_nat_sub(x_3, x_4);
x_7 = l___private_Init_Data_String_Basic_0__Substring_prevn(x_5, x_2, x_6);
lean_dec(x_5);
x_8 = lean_nat_add(x_4, x_7);
lean_dec(x_7);
x_9 = lean_string_utf8_extract(x_1, x_8, x_3);
lean_dec(x_3);
lean_dec(x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_String_takeWhile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Init_Data_String_Basic_0__Substring_takeWhileAux(x_1, x_3, x_2, x_4);
lean_dec(x_3);
x_6 = lean_string_utf8_extract(x_1, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_String_takeWhile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_takeWhile(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_String_dropWhile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Init_Data_String_Basic_0__Substring_takeWhileAux(x_1, x_3, x_2, x_4);
x_6 = lean_string_utf8_extract(x_1, x_5, x_3);
lean_dec(x_3);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_String_dropWhile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_dropWhile(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_String_takeRightWhile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_5 = l___private_Init_Data_String_Basic_0__Substring_takeRightWhileAux(x_1, x_4, x_2, x_3);
x_6 = lean_string_utf8_extract(x_1, x_5, x_3);
lean_dec(x_3);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_String_takeRightWhile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_takeRightWhile(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_String_dropRightWhile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Init_Data_String_Basic_0__Substring_takeRightWhileAux(x_1, x_4, x_2, x_3);
x_6 = lean_string_utf8_extract(x_1, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_String_dropRightWhile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_dropRightWhile(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_String_trimRight(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Init_Data_String_Basic_0__Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_1, x_3, x_2);
x_5 = lean_string_utf8_extract(x_1, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_String_trimRight___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_trimRight(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_String_trimLeft(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Init_Data_String_Basic_0__Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_1, x_2, x_3);
x_5 = lean_string_utf8_extract(x_1, x_4, x_2);
lean_dec(x_2);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_String_trimLeft___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_trimLeft(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_String_trim(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Init_Data_String_Basic_0__Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_1, x_2, x_3);
x_5 = l___private_Init_Data_String_Basic_0__Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_1, x_4, x_2);
x_6 = lean_string_utf8_extract(x_1, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_String_trim___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_trim(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_String_nextWhile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l___private_Init_Data_String_Basic_0__Substring_takeWhileAux(x_1, x_4, x_2, x_3);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_String_nextWhile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_nextWhile(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Data_String_Basic_0__Substring_takeWhileAux___at_String_nextUntil___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_4, x_3);
if (x_5 == 0)
{
uint32_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_string_utf8_get(x_2, x_4);
x_7 = lean_box_uint32(x_6);
lean_inc(x_1);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
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
lean_dec(x_1);
return x_4;
}
}
else
{
lean_dec(x_1);
return x_4;
}
}
}
lean_object* l_String_nextUntil(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l___private_Init_Data_String_Basic_0__Substring_takeWhileAux___at_String_nextUntil___spec__1(x_2, x_1, x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
lean_object* l___private_Init_Data_String_Basic_0__Substring_takeWhileAux___at_String_nextUntil___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Basic_0__Substring_takeWhileAux___at_String_nextUntil___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_String_nextUntil___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_nextUntil(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_String_mapAux___at_String_toUpper___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_utf8_at_end(x_2, x_1);
if (x_3 == 0)
{
uint32_t x_4; lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_string_utf8_get(x_2, x_1);
x_5 = l_Char_toUpper(x_4);
x_6 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_7 = lean_string_utf8_set(x_2, x_1, x_6);
x_8 = lean_string_utf8_next(x_7, x_1);
lean_dec(x_1);
x_1 = x_8;
x_2 = x_7;
goto _start;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
lean_object* l_String_toUpper(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_String_mapAux___at_String_toUpper___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_String_mapAux___at_String_toLower___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_utf8_at_end(x_2, x_1);
if (x_3 == 0)
{
uint32_t x_4; lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_string_utf8_get(x_2, x_1);
x_5 = l_Char_toLower(x_4);
x_6 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_7 = lean_string_utf8_set(x_2, x_1, x_6);
x_8 = lean_string_utf8_next(x_7, x_1);
lean_dec(x_1);
x_1 = x_8;
x_2 = x_7;
goto _start;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
lean_object* l_String_toLower(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_String_mapAux___at_String_toLower___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_String_capitalize(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; lean_object* x_4; uint32_t x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = l_Char_toUpper(x_3);
x_5 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_6 = lean_string_utf8_set(x_1, x_2, x_5);
return x_6;
}
}
lean_object* l_String_decapitalize(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; lean_object* x_4; uint32_t x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = l_Char_toLower(x_3);
x_5 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_6 = lean_string_utf8_set(x_1, x_2, x_5);
return x_6;
}
}
lean_object* l_Char_toString(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedParserDescr___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
lean_object* l_Char_toString___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_toString(x_2);
return x_3;
}
}
lean_object* initialize_Init_Data_List_Basic(lean_object*);
lean_object* initialize_Init_Data_Char_Basic(lean_object*);
lean_object* initialize_Init_Data_Option_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_String_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_instLTString = _init_l_String_instLTString();
lean_mark_persistent(l_String_instLTString);
l_String_instInhabitedString = _init_l_String_instInhabitedString();
lean_mark_persistent(l_String_instInhabitedString);
l_String_instAppendString___closed__1 = _init_l_String_instAppendString___closed__1();
lean_mark_persistent(l_String_instAppendString___closed__1);
l_String_instAppendString = _init_l_String_instAppendString();
lean_mark_persistent(l_String_instAppendString);
l_String_isNat___closed__1 = _init_l_String_isNat___closed__1();
lean_mark_persistent(l_String_isNat___closed__1);
l_String_toNat_x3f___closed__1 = _init_l_String_toNat_x3f___closed__1();
lean_mark_persistent(l_String_toNat_x3f___closed__1);
l_Substring_extract___closed__1 = _init_l_Substring_extract___closed__1();
lean_mark_persistent(l_Substring_extract___closed__1);
l_Substring_splitOn_loop___closed__1 = _init_l_Substring_splitOn_loop___closed__1();
lean_mark_persistent(l_Substring_splitOn_loop___closed__1);
l_Substring_splitOn_loop___closed__2 = _init_l_Substring_splitOn_loop___closed__2();
lean_mark_persistent(l_Substring_splitOn_loop___closed__2);
l_Substring_hasBeq___closed__1 = _init_l_Substring_hasBeq___closed__1();
lean_mark_persistent(l_Substring_hasBeq___closed__1);
l_Substring_hasBeq = _init_l_Substring_hasBeq();
lean_mark_persistent(l_Substring_hasBeq);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
