// Lean compiler output
// Module: init.data.string.basic
// Imports: init.data.list.basic init.data.char.basic init.data.option.basic
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_String_posOf(obj*, uint32);
uint8 l_String_all(obj*, obj*);
obj* l_String_utf8ByteSize___boxed(obj*);
uint32 l_String_Iterator_curr___main(obj*);
obj* l_String_Iterator_extract(obj*, obj*);
obj* l_String_posOfAux___main(obj*, uint32, obj*, obj*, obj*);
obj* l_String_prev___boxed(obj*, obj*);
obj* l_Substring_dropRight___boxed(obj*, obj*);
obj* l_String_mkIterator(obj*);
obj* l___private_init_data_string_basic_2__utf8ByteSizeAux___main___boxed(obj*, obj*);
obj* l___private_init_data_string_basic_4__utf8SetAux(uint32, obj*, obj*, obj*);
obj* l_String_posOf___boxed(obj*, obj*);
obj* l_Substring_takeWhileAux(obj*, obj*, obj*, obj*, obj*);
obj* l_String_foldlAux___main___at_String_toNat___spec__1___closed__1;
uint8 l_Substring_all(obj*, obj*);
obj* l_String_Iterator_hasPrev___main___boxed(obj*);
obj* l_List_asString(obj*);
obj* l_Substring_next___boxed(obj*, obj*);
uint32 l_Substring_get___main(obj*, obj*);
uint32 l_Substring_front(obj*);
obj* l_List_foldl___main___at_String_join___spec__1___boxed(obj*, obj*);
obj* l___private_init_data_string_basic_4__utf8SetAux___main___boxed(obj*, obj*, obj*, obj*);
obj* l_String_singleton___boxed(obj*);
obj* l_Substring_atEnd___boxed(obj*, obj*);
obj* l_String_foldlAux___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_String_front___boxed(obj*);
obj* l_String_Iterator_prevn(obj*, obj*);
obj* l_String_Iterator_extract___main___boxed(obj*, obj*);
obj* l_String_foldrAux___main___boxed(obj*);
obj* l_String_join___boxed(obj*);
obj* l_String_takeRight(obj*, obj*);
obj* l_Substring_takeRightWhileAux___main___at_Substring_trim___main___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_String_Iterator_remainingToString___main(obj*);
obj* l_Substring_extract___main(obj*, obj*, obj*);
obj* l_String_Iterator_setCurr___main___boxed(obj*, obj*);
obj* l_String_mapAux___main(obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_String_toNat(obj*);
obj* l_String_map(obj*, obj*);
obj* l_Substring_takeRightWhile(obj*, obj*);
obj* l_Substring_prev___main(obj*, obj*);
obj* l_String_foldrAux___main(obj*);
namespace lean {
obj* string_utf8_prev(obj*, obj*);
}
obj* l_String_foldlAux___main___boxed(obj*);
obj* l_Substring_next___main___boxed(obj*, obj*);
uint8 l_String_isEmpty(obj*);
obj* l_String_trim___boxed(obj*);
obj* l_String_foldrAux(obj*);
obj* l_String_intercalate(obj*, obj*);
obj* l___private_init_data_string_basic_8__lineColumnAux___boxed(obj*, obj*, obj*, obj*);
obj* l_String_lineColumn(obj*, obj*);
obj* l_Substring_dropRight___main(obj*, obj*);
obj* l_Substring_prev(obj*, obj*);
obj* l_String_Iterator_hasPrev___boxed(obj*);
obj* l_Substring_isNat___boxed(obj*);
obj* l_String_Iterator_extract___main(obj*, obj*);
obj* l_Substring_any___boxed(obj*, obj*);
obj* l_String_Iterator_pos(obj*);
obj* l_Substring_takeWhile___main(obj*, obj*);
obj* l_String_drop___boxed(obj*, obj*);
obj* l_String_foldr___boxed(obj*);
obj* l_String_Iterator_toString___main___boxed(obj*);
obj* l_Substring_get___boxed(obj*, obj*);
uint8 l_String_Iterator_hasPrev___main(obj*);
obj* l_Char_toString___boxed(obj*);
obj* l_String_push___boxed(obj*, obj*);
obj* l_Substring_takeRightWhileAux___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_String_foldrAux___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Substring_takeRightWhileAux___main___at_Substring_trim___main___spec__2(obj*, obj*, obj*, obj*);
obj* l_String_dropRight___boxed(obj*, obj*);
obj* l___private_init_data_string_basic_4__utf8SetAux___main(uint32, obj*, obj*, obj*);
obj* l___private_init_data_string_basic_7__utf8ExtractAux_u_2081(obj*, obj*, obj*, obj*);
obj* l___private_init_data_string_basic_6__utf8ExtractAux_u_2082(obj*, obj*, obj*);
obj* l_String_split___boxed(obj*, obj*);
obj* l_Substring_dropWhile(obj*, obj*);
obj* l_List_reverse___rarg(obj*);
obj* l_String_Iterator_isPrefixOfRemaining___boxed(obj*, obj*);
obj* l_String_Iterator_remainingBytes___main(obj*);
obj* l_String_Iterator_pos___boxed(obj*);
uint8 l_String_anyAux___main___at_String_isNat___spec__1(obj*, obj*, obj*, obj*);
obj* l_Substring_takeRightWhileAux___main___at_Substring_trimRight___spec__1(obj*, obj*, obj*, obj*);
obj* l_String_foldl___rarg(obj*, obj*, obj*);
obj* l_String_pushn___boxed(obj*, obj*, obj*);
obj* l_String_get___boxed(obj*, obj*);
obj* l___private_init_data_string_basic_2__utf8ByteSizeAux___boxed(obj*, obj*);
uint8 l_String_Iterator_hasNext(obj*);
obj* l_Substring_foldl___boxed(obj*);
obj* l_String_offsetOfPos(obj*, obj*);
obj* l_String_HasAppend;
obj* l_String_HasLess;
obj* l_Substring_contains___boxed(obj*, obj*);
obj* l_Substring_foldl___rarg(obj*, obj*, obj*);
obj* l_String_takeWhile(obj*, obj*);
uint8 l_String_contains(obj*, uint32);
obj* l_Substring_takeRightWhileAux___main___at_Substring_trim___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_String_Iterator_prev___main(obj*);
obj* l_String_dropWhile___boxed(obj*, obj*);
obj* l_Substring_takeWhileAux___main(obj*, obj*, obj*, obj*, obj*);
obj* l_Substring_takeRight___main___boxed(obj*, obj*);
obj* l_Substring_takeWhileAux___main___at_String_trimLeft___spec__1(obj*, obj*, obj*, obj*);
obj* l_String_Iterator_forward___main(obj*, obj*);
uint8 l_String_Iterator_isPrefixOfRemaining(obj*, obj*);
obj* l_String_splitAux(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Substring_takeRight(obj*, obj*);
uint8 l_String_anyAux___main___at_Substring_isNat___spec__1(obj*, obj*, obj*, obj*);
obj* l_Substring_toString(obj*);
uint8 l_String_any(obj*, obj*);
obj* l_Substring_takeRightWhileAux___main___at_Substring_trimRight___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_String_Inhabited;
obj* l_String_toFuel(obj*);
obj* l___private_init_data_string_basic_8__lineColumnAux(obj*, obj*, obj*, obj*);
obj* l_Substring_next(obj*, obj*);
obj* l___private_init_data_string_basic_8__lineColumnAux___main(obj*, obj*, obj*, obj*);
obj* l_Substring_trimRight(obj*);
obj* l_Substring_toIterator___main(obj*);
obj* l_String_anyAux___main___at_Substring_contains___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Substring_extract(obj*, obj*, obj*);
obj* l___private_init_data_string_basic_1__csize(uint32);
obj* l_String_Iterator_prevn___main(obj*, obj*);
obj* l___private_init_data_string_basic_4__utf8SetAux___boxed(obj*, obj*, obj*, obj*);
obj* l_Substring_extract___main___closed__1;
obj* l_Substring_extract___main___boxed(obj*, obj*, obj*);
obj* l_String_back___boxed(obj*);
obj* l_String_foldlAux___main___at_String_toNat___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_String_Iterator_hasNext___main___boxed(obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_Substring_take___boxed(obj*, obj*);
obj* l_String_takeRight___boxed(obj*, obj*);
obj* l_Substring_takeRightWhileAux___main___at_Substring_trim___spec__2(obj*, obj*, obj*, obj*);
obj* l_Substring_drop___main(obj*, obj*);
obj* l_Substring_takeWhileAux___main___at_String_trim___spec__1(obj*, obj*, obj*, obj*);
obj* l_String_Iterator_toString(obj*);
obj* l_Substring_drop(obj*, obj*);
obj* l___private_init_data_string_basic_6__utf8ExtractAux_u_2082___main(obj*, obj*, obj*);
obj* l_Substring_takeWhileAux___main___at_Substring_trim___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_Substring_trim___main(obj*);
obj* l_Char_toString(uint32);
obj* l_String_offsetOfPosAux___main(obj*, obj*, obj*, obj*, obj*);
obj* l_String_Iterator_next(obj*);
obj* l_Substring_splitAux___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_String_Iterator_hasNext___boxed(obj*);
obj* l_Substring_dropRight___main___boxed(obj*, obj*);
obj* l_String_foldlAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Substring_dropRightWhile___main(obj*, obj*);
obj* l_String_foldl(obj*);
obj* l_String_any___boxed(obj*, obj*);
obj* l_String_anyAux___main___at_Substring_isNat___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_data_string_basic_5__utf8PrevAux(obj*, obj*, obj*);
obj* l_String_contains___boxed(obj*, obj*);
obj* l___private_init_data_string_basic_5__utf8PrevAux___main(obj*, obj*, obj*);
obj* l_Substring_posOf(obj*, uint32);
uint8 l_String_anyAux___main___at_Substring_contains___spec__1(uint32, obj*, obj*, obj*, obj*);
obj* l_String_offsetOfPosAux___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_String_offsetOfPosAux(obj*, obj*, obj*, obj*, obj*);
obj* l_String_Iterator_next___main(obj*);
obj* l_Substring_takeRightWhileAux___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_data_string_basic_7__utf8ExtractAux_u_2081___main(obj*, obj*, obj*, obj*);
obj* l_String_all___boxed(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
uint32 l_Substring_get(obj*, obj*);
obj* l_Substring_foldr___rarg___boxed(obj*, obj*, obj*);
obj* l_Substring_foldr(obj*);
namespace lean {
uint8 string_dec_lt(obj*, obj*);
}
obj* l_String_isNat___boxed(obj*);
obj* l_String_Iterator_setCurr___boxed(obj*, obj*);
obj* l_String_offsetOfPos___boxed(obj*, obj*);
obj* l_String_drop___closed__1;
obj* l_String_take(obj*, obj*);
namespace lean {
uint8 string_utf8_at_end(obj*, obj*);
}
obj* l_String_decEq___boxed(obj*, obj*);
obj* l_String_anyAux___main___at_String_contains___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_String_Iterator_prev(obj*);
obj* l_String_foldrAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_String_offsetOfPosAux___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_String_toSubstring(obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Substring_takeWhileAux___main___at_String_trim___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_String_str(obj*, uint32);
obj* l_Substring_drop___main___boxed(obj*, obj*);
obj* l_Substring_split(obj*, obj*);
obj* l_String_drop(obj*, obj*);
obj* l_Substring_drop___main___closed__1;
obj* l_Substring_posOf___boxed(obj*, obj*);
obj* l_String_bsize(obj*);
obj* l_String_anyAux___main___at_Substring_all___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_String_Iterator_remainingToString___boxed(obj*);
obj* l_Substring_dropRight(obj*, obj*);
obj* l_String_Iterator_nextn(obj*, obj*);
obj* l_String_foldrAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Substring_takeWhileAux___main___at_String_trimLeft___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Substring_takeRightWhileAux___main___at_String_trim___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_String_toNat___boxed(obj*);
obj* l_String_Iterator_curr___main___boxed(obj*);
obj* l_String_Iterator_toString___boxed(obj*);
uint8 l_String_anyAux___main___at_Substring_all___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_String_foldlAux___main___at_Substring_toNat___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_String_foldlAux(obj*);
obj* l_String_set___boxed(obj*, obj*, obj*);
obj* l_String_Iterator_remainingToString___main___boxed(obj*);
obj* l_Substring_front___boxed(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Substring_takeRightWhileAux___main___at_String_trim___spec__2(obj*, obj*, obj*, obj*);
obj* l_String_anyAux___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Substring_takeRight___main(obj*, obj*);
obj* l_Substring_takeRightWhileAux___main(obj*, obj*, obj*, obj*, obj*);
obj* l_String_join(obj*);
obj* l_String_Iterator_remainingBytes___main___boxed(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Substring_foldl(obj*);
obj* l_String_splitAux___main___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_String_append___boxed(obj*, obj*);
obj* l_Substring_takeRightWhile___main(obj*, obj*);
obj* l___private_init_data_string_basic_5__utf8PrevAux___boxed(obj*, obj*, obj*);
obj* l_String_Iterator_nextn___main(obj*, obj*);
obj* l_String_Iterator_pos___main___boxed(obj*);
obj* l_String_isEmpty___boxed(obj*);
obj* l_Nat_repeatCore___main___at_String_pushn___spec__1(uint32, obj*, obj*, obj*);
obj* l_List_map___main___at_String_intercalate___spec__1(obj*);
obj* l_String_foldl___rarg___boxed(obj*, obj*, obj*);
obj* l_String_toList(obj*);
obj* l_Substring_takeWhileAux___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_String_atEnd___boxed(obj*, obj*);
obj* l_Substring_takeWhile(obj*, obj*);
namespace lean {
uint32 string_utf8_get(obj*, obj*);
}
obj* l_Substring_drop___boxed(obj*, obj*);
obj* l_String_trimRight___boxed(obj*);
obj* l_Substring_foldr___boxed(obj*);
obj* l_Substring_splitAux(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_String_singleton(uint32);
obj* l___private_init_data_string_basic_8__lineColumnAux___main___boxed(obj*, obj*, obj*, obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_String_anyAux___main___at_String_all___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Substring_extract___boxed(obj*, obj*, obj*);
obj* l_Substring_splitAux___main(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_String_foldrAux___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Substring_dropRightWhile(obj*, obj*);
obj* l_Substring_takeWhileAux___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Substring_toIterator(obj*);
uint8 l_Substring_atEnd(obj*, obj*);
obj* l_Substring_next___main(obj*, obj*);
obj* l_Substring_take___main(obj*, obj*);
uint8 l_Char_isDigit(uint32);
obj* l_String_dropRight(obj*, obj*);
obj* l_Substring_all___boxed(obj*, obj*);
obj* l_Substring_takeWhileAux___main___at_Substring_trimLeft___spec__1(obj*, obj*, obj*, obj*);
obj* l_Substring_splitAux___main___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_String_Iterator_forward(obj*, obj*);
obj* l_Substring_atEnd___main___boxed(obj*, obj*);
obj* l_String_Iterator_isPrefixOfRemaining___main___boxed(obj*, obj*);
obj* l_Substring_takeWhileAux___main___at_Substring_trimLeft___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_String_decLt___boxed(obj*, obj*);
obj* l_String_DecidableEq;
obj* l_String_trim(obj*);
obj* l___private_init_data_string_basic_6__utf8ExtractAux_u_2082___boxed(obj*, obj*, obj*);
obj* l_String_foldr___rarg(obj*, obj*, obj*);
obj* l_String_foldlAux___main___at_Substring_toNat___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Substring_split___boxed(obj*, obj*);
obj* l_String_split(obj*, obj*);
obj* l_String_foldr(obj*);
obj* l_String_posOfAux___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_String_mapAux(obj*, obj*, obj*, obj*);
obj* l___private_init_data_string_basic_1__csize___boxed(obj*);
namespace lean {
obj* string_data(obj*);
}
obj* l_String_extract___boxed(obj*, obj*, obj*);
uint8 l_Substring_any(obj*, obj*);
obj* l_Substring_takeRightWhileAux(obj*, obj*, obj*, obj*, obj*);
uint8 l_String_isNat(obj*);
obj* l_Substring_takeRightWhileAux___main___at_String_trimRight___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_String_Iterator_pos___main(obj*);
obj* l_Substring_trimLeft(obj*);
uint32 l_String_Iterator_curr(obj*);
obj* l_String_pushn(obj*, uint32, obj*);
obj* l_String_splitAux___main(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_data_string_basic_3__utf8GetAux___boxed(obj*, obj*, obj*);
uint8 l_Char_isWhitespace(uint32);
obj* l_String_Iterator_remainingBytes___boxed(obj*);
obj* l_String_posOfAux(obj*, uint32, obj*, obj*, obj*);
uint32 l___private_init_data_string_basic_3__utf8GetAux(obj*, obj*, obj*);
obj* l_Substring_toString___boxed(obj*);
obj* l_String_HasSizeof;
uint32 l_String_front(obj*);
obj* l_String_toFuel___boxed(obj*);
uint8 l_String_anyAux___main___at_String_all___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Substring_get___main___boxed(obj*, obj*);
obj* l_String_anyAux___main___boxed(obj*, obj*, obj*, obj*, obj*);
uint32 l___private_init_data_string_basic_3__utf8GetAux___main(obj*, obj*, obj*);
obj* l_Substring_prev___main___boxed(obj*, obj*);
obj* l_List_intercalate___rarg(obj*, obj*);
obj* l___private_init_data_string_basic_2__utf8ByteSizeAux___main(obj*, obj*);
obj* l___private_init_data_string_basic_6__utf8ExtractAux_u_2082___main___boxed(obj*, obj*, obj*);
obj* l_Substring_dropWhile___main(obj*, obj*);
uint32 l_Char_utf8Size(uint32);
obj* l_String_Iterator_toEnd___main(obj*);
obj* l_Substring_toNat(obj*);
namespace lean {
obj* string_utf8_next(obj*, obj*);
}
obj* l_String_splitAux___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_data_string_basic_3__utf8GetAux___main___boxed(obj*, obj*, obj*);
obj* l_String_Iterator_extract___boxed(obj*, obj*);
uint8 l_Substring_atEnd___main(obj*, obj*);
obj* l___private_init_data_string_basic_7__utf8ExtractAux_u_2081___main___boxed(obj*, obj*, obj*, obj*);
namespace lean {
uint32 uint32_of_nat(obj*);
}
uint8 l_String_Iterator_hasNext___main(obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
namespace lean {
obj* string_utf8_extract(obj*, obj*, obj*);
}
namespace lean {
obj* string_mk(obj*);
}
obj* l_Substring_takeWhileAux___main___at_Substring_trim___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_String_foldrAux___boxed(obj*);
obj* l_String_Iterator_curr___boxed(obj*);
obj* l_Substring_toString___main___boxed(obj*);
obj* l_String_dropWhile(obj*, obj*);
obj* l_Substring_takeRightWhileAux___main___at_String_trimRight___spec__1(obj*, obj*, obj*, obj*);
namespace lean {
obj* string_utf8_byte_size(obj*);
}
obj* l_String_foldr___rarg___boxed(obj*, obj*, obj*);
obj* l_String_foldl___boxed(obj*);
obj* l_String_Iterator_toString___main(obj*);
obj* l_String_foldlAux___main(obj*);
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l_Substring_take___main___boxed(obj*, obj*);
obj* l___private_init_data_string_basic_5__utf8PrevAux___main___boxed(obj*, obj*, obj*);
obj* l_Substring_trim(obj*);
obj* l_String_trimLeft___boxed(obj*);
obj* l_String_take___boxed(obj*, obj*);
obj* l_String_foldlAux___boxed(obj*);
uint8 l_String_Iterator_hasPrev(obj*);
obj* l_Substring_takeWhileAux___main___at_Substring_trim___spec__1(obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_String_join___spec__1(obj*, obj*);
uint8 l_Substring_isNat(obj*);
obj* l_String_Iterator_setCurr(obj*, uint32);
obj* l_Nat_repeatCore___main___at_String_pushn___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_String_foldlAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Substring_toString___main(obj*);
obj* l_String_Iterator_toEnd(obj*);
obj* l_String_bsize___boxed(obj*);
namespace lean {
obj* nat_mul(obj*, obj*);
}
uint8 l_String_Iterator_isPrefixOfRemaining___main(obj*, obj*);
obj* l_String_Iterator_setCurr___main(obj*, uint32);
obj* l___private_init_data_string_basic_7__utf8ExtractAux_u_2081___boxed(obj*, obj*, obj*, obj*);
obj* l_String_posOfAux___main___boxed(obj*, obj*, obj*, obj*, obj*);
uint8 l_Substring_contains(obj*, uint32);
obj* l_String_str___boxed(obj*, obj*);
obj* l_String_takeWhile___boxed(obj*, obj*);
obj* l_String_foldlAux___main___at_String_toNat___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_String_next___boxed(obj*, obj*);
obj* l_String_trimLeft(obj*);
obj* l___private_init_data_string_basic_2__utf8ByteSizeAux(obj*, obj*);
uint8 l_String_anyAux___main___at_String_contains___spec__1(uint32, obj*, obj*, obj*, obj*);
obj* l_String_length___boxed(obj*);
obj* l_String_anyAux___main___at_String_isNat___spec__1___boxed(obj*, obj*, obj*, obj*);
uint8 l_String_anyAux(obj*, obj*, obj*, obj*, obj*);
obj* l_Substring_prev___boxed(obj*, obj*);
obj* l_Substring_take(obj*, obj*);
uint8 l_String_anyAux___main(obj*, obj*, obj*, obj*, obj*);
obj* l_Substring_foldr___rarg(obj*, obj*, obj*);
obj* l_String_lineColumn___closed__1;
obj* l_String_trimRight(obj*);
obj* l_Substring_takeRight___boxed(obj*, obj*);
uint32 l_String_back(obj*);
obj* l_Substring_takeWhileAux___main___at_Substring_trim___main___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_String_Iterator_remainingBytes(obj*);
obj* l_String_foldlAux___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_String_Iterator_remainingToString(obj*);
obj* l_String_splitAux___main___closed__1;
namespace lean {
obj* string_utf8_set(obj*, obj*, uint32);
}
namespace lean {
obj* string_length(obj*);
}
obj* l_String_lineColumn___boxed(obj*, obj*);
obj* l_String_decEq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::string_dec_eq(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_String_DecidableEq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_String_decEq___boxed), 2, 0);
return x_0;
}
}
obj* l_List_asString(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_mk(x_0);
return x_1;
}
}
obj* _init_l_String_HasLess() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_String_decLt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::string_dec_lt(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_String_length___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_length(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_String_push___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = lean::string_push(x_0, x_2);
return x_3;
}
}
obj* l_String_append___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::string_append(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_String_toList(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_data(x_0);
return x_1;
}
}
obj* l___private_init_data_string_basic_1__csize(uint32 x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = l_Char_utf8Size(x_0);
x_2 = lean::uint32_to_nat(x_1);
return x_2;
}
}
obj* l___private_init_data_string_basic_1__csize___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l___private_init_data_string_basic_1__csize(x_1);
return x_2;
}
}
obj* l___private_init_data_string_basic_2__utf8ByteSizeAux___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
return x_1;
}
else
{
obj* x_2; obj* x_3; uint32 x_4; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = lean::unbox_uint32(x_2);
x_5 = l___private_init_data_string_basic_1__csize(x_4);
x_6 = lean::nat_add(x_1, x_5);
lean::dec(x_5);
lean::dec(x_1);
x_0 = x_3;
x_1 = x_6;
goto _start;
}
}
}
obj* l___private_init_data_string_basic_2__utf8ByteSizeAux___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_data_string_basic_2__utf8ByteSizeAux___main(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l___private_init_data_string_basic_2__utf8ByteSizeAux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_data_string_basic_2__utf8ByteSizeAux___main(x_0, x_1);
return x_2;
}
}
obj* l___private_init_data_string_basic_2__utf8ByteSizeAux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_data_string_basic_2__utf8ByteSizeAux(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_String_utf8ByteSize___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_utf8_byte_size(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_String_bsize(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_utf8_byte_size(x_0);
return x_1;
}
}
obj* l_String_bsize___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_bsize(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_String_toFuel(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::string_utf8_byte_size(x_0);
x_2 = lean::mk_nat_obj(1ul);
x_3 = lean::nat_add(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_String_toFuel___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_toFuel(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_String_toSubstring(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::string_utf8_byte_size(x_0);
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
lean::cnstr_set(x_3, 2, x_1);
return x_3;
}
}
uint32 l___private_init_data_string_basic_3__utf8GetAux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint32 x_4; 
lean::dec(x_1);
x_4 = 65;
return x_4;
}
else
{
obj* x_5; obj* x_6; uint8 x_7; 
x_5 = lean::cnstr_get(x_0, 0);
x_6 = lean::cnstr_get(x_0, 1);
x_7 = lean::nat_dec_eq(x_1, x_2);
if (x_7 == 0)
{
uint32 x_8; obj* x_9; obj* x_10; 
x_8 = lean::unbox_uint32(x_5);
x_9 = l___private_init_data_string_basic_1__csize(x_8);
x_10 = lean::nat_add(x_1, x_9);
lean::dec(x_9);
lean::dec(x_1);
x_0 = x_6;
x_1 = x_10;
goto _start;
}
else
{
uint32 x_15; 
lean::dec(x_1);
x_15 = lean::unbox_uint32(x_5);
return x_15;
}
}
}
}
obj* l___private_init_data_string_basic_3__utf8GetAux___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = l___private_init_data_string_basic_3__utf8GetAux___main(x_0, x_1, x_2);
x_4 = lean::box_uint32(x_3);
lean::dec(x_0);
lean::dec(x_2);
return x_4;
}
}
uint32 l___private_init_data_string_basic_3__utf8GetAux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; 
x_3 = l___private_init_data_string_basic_3__utf8GetAux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_init_data_string_basic_3__utf8GetAux___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = l___private_init_data_string_basic_3__utf8GetAux(x_0, x_1, x_2);
x_4 = lean::box_uint32(x_3);
lean::dec(x_0);
lean::dec(x_2);
return x_4;
}
}
obj* l_String_get___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::string_utf8_get(x_0, x_1);
x_3 = lean::box_uint32(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l___private_init_data_string_basic_4__utf8SetAux___main(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_8; uint8 x_9; 
x_4 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_8 = x_1;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
x_9 = lean::nat_dec_eq(x_2, x_3);
if (x_9 == 0)
{
uint32 x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_16; 
x_10 = lean::unbox_uint32(x_4);
x_11 = l___private_init_data_string_basic_1__csize(x_10);
x_12 = lean::nat_add(x_2, x_11);
lean::dec(x_11);
x_14 = l___private_init_data_string_basic_4__utf8SetAux___main(x_0, x_6, x_12, x_3);
lean::dec(x_12);
if (lean::is_scalar(x_8)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_8;
}
lean::cnstr_set(x_16, 0, x_4);
lean::cnstr_set(x_16, 1, x_14);
return x_16;
}
else
{
obj* x_18; obj* x_19; 
lean::dec(x_4);
x_18 = lean::box_uint32(x_0);
if (lean::is_scalar(x_8)) {
 x_19 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_19 = x_8;
}
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_6);
return x_19;
}
}
}
}
obj* l___private_init_data_string_basic_4__utf8SetAux___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l___private_init_data_string_basic_4__utf8SetAux___main(x_4, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* l___private_init_data_string_basic_4__utf8SetAux(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_data_string_basic_4__utf8SetAux___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_data_string_basic_4__utf8SetAux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l___private_init_data_string_basic_4__utf8SetAux(x_4, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* l_String_set___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = lean::string_utf8_set(x_0, x_1, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_String_next___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::string_utf8_next(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_data_string_basic_5__utf8PrevAux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::mk_nat_obj(0ul);
return x_4;
}
else
{
obj* x_5; obj* x_6; uint32 x_7; obj* x_8; obj* x_9; uint8 x_11; 
x_5 = lean::cnstr_get(x_0, 0);
x_6 = lean::cnstr_get(x_0, 1);
x_7 = lean::unbox_uint32(x_5);
x_8 = l___private_init_data_string_basic_1__csize(x_7);
x_9 = lean::nat_add(x_1, x_8);
lean::dec(x_8);
x_11 = lean::nat_dec_eq(x_9, x_2);
if (x_11 == 0)
{
lean::dec(x_1);
x_0 = x_6;
x_1 = x_9;
goto _start;
}
else
{
lean::dec(x_9);
return x_1;
}
}
}
}
obj* l___private_init_data_string_basic_5__utf8PrevAux___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_data_string_basic_5__utf8PrevAux___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_data_string_basic_5__utf8PrevAux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_data_string_basic_5__utf8PrevAux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_init_data_string_basic_5__utf8PrevAux___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_data_string_basic_5__utf8PrevAux(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
}
obj* l_String_prev___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::string_utf8_prev(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint32 l_String_front(obj* x_0) {
_start:
{
obj* x_1; uint32 x_2; 
x_1 = lean::mk_nat_obj(0ul);
x_2 = lean::string_utf8_get(x_0, x_1);
return x_2;
}
}
obj* l_String_front___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = l_String_front(x_0);
x_2 = lean::box_uint32(x_1);
lean::dec(x_0);
return x_2;
}
}
uint32 l_String_back(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint32 x_4; 
x_1 = lean::string_utf8_byte_size(x_0);
x_2 = lean::string_utf8_prev(x_0, x_1);
lean::dec(x_1);
x_4 = lean::string_utf8_get(x_0, x_2);
lean::dec(x_2);
return x_4;
}
}
obj* l_String_back___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = l_String_back(x_0);
x_2 = lean::box_uint32(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_String_atEnd___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::string_utf8_at_end(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_String_posOfAux___main(obj* x_0, uint32 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = lean::nat_dec_eq(x_4, x_2);
if (x_7 == 0)
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_utf8_get(x_0, x_4);
x_9 = x_8 == x_1;
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; 
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_sub(x_3, x_10);
lean::dec(x_3);
x_13 = lean::string_utf8_next(x_0, x_4);
lean::dec(x_4);
x_3 = x_11;
x_4 = x_13;
goto _start;
}
else
{
lean::dec(x_3);
return x_4;
}
}
else
{
lean::dec(x_3);
return x_4;
}
}
else
{
lean::dec(x_3);
return x_4;
}
}
}
obj* l_String_posOfAux___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_1);
x_6 = l_String_posOfAux___main(x_0, x_5, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_6;
}
}
obj* l_String_posOfAux(obj* x_0, uint32 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_String_posOfAux___main(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_String_posOfAux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_1);
x_6 = l_String_posOfAux(x_0, x_5, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_6;
}
}
obj* l_String_posOf(obj* x_0, uint32 x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::string_utf8_byte_size(x_0);
x_3 = lean::mk_nat_obj(1ul);
x_4 = lean::nat_add(x_2, x_3);
x_5 = lean::mk_nat_obj(0ul);
x_6 = l_String_posOfAux___main(x_0, x_1, x_2, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_String_posOf___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_String_posOf(x_0, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l___private_init_data_string_basic_6__utf8ExtractAux_u_2082___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_7; uint8 x_8; 
x_3 = lean::cnstr_get(x_0, 0);
x_5 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_7 = x_0;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_0);
 x_7 = lean::box(0);
}
x_8 = lean::nat_dec_eq(x_1, x_2);
if (x_8 == 0)
{
uint32 x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_15; 
x_9 = lean::unbox_uint32(x_3);
x_10 = l___private_init_data_string_basic_1__csize(x_9);
x_11 = lean::nat_add(x_1, x_10);
lean::dec(x_10);
x_13 = l___private_init_data_string_basic_6__utf8ExtractAux_u_2082___main(x_5, x_11, x_2);
lean::dec(x_11);
if (lean::is_scalar(x_7)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_7;
}
lean::cnstr_set(x_15, 0, x_3);
lean::cnstr_set(x_15, 1, x_13);
return x_15;
}
else
{
obj* x_19; 
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_3);
x_19 = lean::box(0);
return x_19;
}
}
}
}
obj* l___private_init_data_string_basic_6__utf8ExtractAux_u_2082___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_data_string_basic_6__utf8ExtractAux_u_2082___main(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_data_string_basic_6__utf8ExtractAux_u_2082(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_data_string_basic_6__utf8ExtractAux_u_2082___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_init_data_string_basic_6__utf8ExtractAux_u_2082___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_data_string_basic_6__utf8ExtractAux_u_2082(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_data_string_basic_7__utf8ExtractAux_u_2081___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_5; obj* x_7; uint8 x_9; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::nat_dec_eq(x_1, x_2);
if (x_9 == 0)
{
uint32 x_11; obj* x_12; obj* x_13; 
lean::dec(x_0);
x_11 = lean::unbox_uint32(x_5);
x_12 = l___private_init_data_string_basic_1__csize(x_11);
x_13 = lean::nat_add(x_1, x_12);
lean::dec(x_12);
lean::dec(x_1);
x_0 = x_7;
x_1 = x_13;
goto _start;
}
else
{
obj* x_19; 
lean::dec(x_7);
lean::dec(x_5);
x_19 = l___private_init_data_string_basic_6__utf8ExtractAux_u_2082___main(x_0, x_1, x_3);
lean::dec(x_1);
return x_19;
}
}
}
}
obj* l___private_init_data_string_basic_7__utf8ExtractAux_u_2081___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_data_string_basic_7__utf8ExtractAux_u_2081___main(x_0, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l___private_init_data_string_basic_7__utf8ExtractAux_u_2081(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_data_string_basic_7__utf8ExtractAux_u_2081___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_data_string_basic_7__utf8ExtractAux_u_2081___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_data_string_basic_7__utf8ExtractAux_u_2081(x_0, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_String_extract___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::string_utf8_extract(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_String_splitAux___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("");
return x_0;
}
}
obj* l_String_splitAux___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::mk_nat_obj(0ul);
x_8 = lean::nat_dec_eq(x_2, x_7);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = lean::string_utf8_at_end(x_0, x_4);
if (x_9 == 0)
{
obj* x_10; obj* x_11; uint32 x_13; uint32 x_14; uint8 x_15; 
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_sub(x_2, x_10);
lean::dec(x_2);
x_13 = lean::string_utf8_get(x_0, x_4);
x_14 = lean::string_utf8_get(x_1, x_5);
x_15 = x_13 == x_14;
if (x_15 == 0)
{
obj* x_17; 
lean::dec(x_5);
x_17 = lean::string_utf8_next(x_0, x_4);
lean::dec(x_4);
x_2 = x_11;
x_4 = x_17;
x_5 = x_7;
goto _start;
}
else
{
obj* x_20; obj* x_22; uint8 x_24; 
x_20 = lean::string_utf8_next(x_0, x_4);
lean::dec(x_4);
x_22 = lean::string_utf8_next(x_1, x_5);
lean::dec(x_5);
x_24 = lean::string_utf8_at_end(x_1, x_22);
if (x_24 == 0)
{
x_2 = x_11;
x_4 = x_20;
x_5 = x_22;
goto _start;
}
else
{
obj* x_26; obj* x_28; obj* x_31; 
x_26 = lean::nat_sub(x_20, x_22);
lean::dec(x_22);
x_28 = lean::string_utf8_extract(x_0, x_3, x_26);
lean::dec(x_26);
lean::dec(x_3);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_28);
lean::cnstr_set(x_31, 1, x_6);
lean::inc(x_20);
x_2 = x_11;
x_3 = x_20;
x_4 = x_20;
x_5 = x_7;
x_6 = x_31;
goto _start;
}
}
}
else
{
uint8 x_35; 
lean::dec(x_2);
x_35 = lean::string_utf8_at_end(x_1, x_5);
if (x_35 == 0)
{
obj* x_37; obj* x_40; obj* x_41; 
lean::dec(x_5);
x_37 = lean::string_utf8_extract(x_0, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_37);
lean::cnstr_set(x_40, 1, x_6);
x_41 = l_List_reverse___rarg(x_40);
return x_41;
}
else
{
obj* x_42; obj* x_45; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_42 = lean::nat_sub(x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
x_45 = lean::string_utf8_extract(x_0, x_3, x_42);
lean::dec(x_42);
lean::dec(x_3);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_45);
lean::cnstr_set(x_48, 1, x_6);
x_49 = l_String_splitAux___main___closed__1;
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_48);
x_51 = l_List_reverse___rarg(x_50);
return x_51;
}
}
}
else
{
obj* x_57; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_57 = lean::box(0);
return x_57;
}
}
}
obj* l_String_splitAux___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_String_splitAux___main(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_0);
lean::dec(x_1);
return x_7;
}
}
obj* l_String_splitAux(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_String_splitAux___main(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
obj* l_String_splitAux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_String_splitAux(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_0);
lean::dec(x_1);
return x_7;
}
}
obj* l_String_split(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean::string_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::string_utf8_byte_size(x_0);
x_5 = lean::mk_nat_obj(1ul);
x_6 = lean::nat_add(x_4, x_5);
lean::dec(x_4);
x_8 = lean::box(0);
x_9 = lean::mk_nat_obj(0ul);
x_10 = l_String_splitAux___main(x_0, x_1, x_6, x_9, x_9, x_9, x_8);
lean::dec(x_0);
return x_10;
}
else
{
obj* x_12; obj* x_13; 
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_0);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
obj* l_String_split___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_split(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_String_Inhabited() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("");
return x_0;
}
}
obj* _init_l_String_HasSizeof() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_String_length___boxed), 1, 0);
return x_0;
}
}
obj* _init_l_String_HasAppend() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_String_append___boxed), 2, 0);
return x_0;
}
}
obj* l_String_str(obj* x_0, uint32 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::string_push(x_0, x_1);
return x_2;
}
}
obj* l_String_str___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_String_str(x_0, x_2);
return x_3;
}
}
obj* l_Nat_repeatCore___main___at_String_pushn___spec__1(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_9; 
x_6 = lean::mk_nat_obj(1ul);
x_7 = lean::nat_sub(x_2, x_6);
lean::dec(x_2);
x_9 = lean::string_push(x_3, x_0);
x_2 = x_7;
x_3 = x_9;
goto _start;
}
else
{
lean::dec(x_2);
return x_3;
}
}
}
obj* l_String_pushn(obj* x_0, uint32 x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::inc(x_2);
x_4 = l_Nat_repeatCore___main___at_String_pushn___spec__1(x_1, x_2, x_2, x_0);
lean::dec(x_2);
return x_4;
}
}
obj* l_Nat_repeatCore___main___at_String_pushn___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_Nat_repeatCore___main___at_String_pushn___spec__1(x_4, x_1, x_2, x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_String_pushn___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_1);
x_4 = l_String_pushn(x_0, x_3, x_2);
return x_4;
}
}
uint8 l_String_isEmpty(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = lean::string_utf8_byte_size(x_0);
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_1);
if (x_3 == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
}
}
obj* l_String_isEmpty___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_String_isEmpty(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_List_foldl___main___at_String_join___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::string_append(x_0, x_2);
x_0 = x_4;
x_1 = x_3;
goto _start;
}
}
}
obj* l_String_join(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = l_List_foldl___main___at_String_join___spec__1(x_1, x_0);
return x_2;
}
}
obj* l_List_foldl___main___at_String_join___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_foldl___main___at_String_join___spec__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_String_join___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_join(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_String_singleton(uint32 x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = lean::string_push(x_1, x_0);
return x_2;
}
}
obj* l_String_singleton___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_String_singleton(x_1);
return x_2;
}
}
obj* l_List_map___main___at_String_intercalate___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_6 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = lean::string_data(x_2);
x_8 = l_List_map___main___at_String_intercalate___spec__1(x_4);
if (lean::is_scalar(x_6)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_6;
}
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_String_intercalate(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_data(x_0);
x_3 = l_List_map___main___at_String_intercalate___spec__1(x_1);
x_4 = l_List_intercalate___rarg(x_2, x_3);
x_5 = lean::string_mk(x_4);
return x_5;
}
}
obj* l_String_mkIterator(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(0ul);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_String_Iterator_toString___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* l_String_Iterator_toString___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_Iterator_toString___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_String_Iterator_toString(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_Iterator_toString___main(x_0);
return x_1;
}
}
obj* l_String_Iterator_toString___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_Iterator_toString(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_String_Iterator_remainingBytes___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::cnstr_get(x_0, 0);
x_2 = lean::cnstr_get(x_0, 1);
x_3 = lean::string_utf8_byte_size(x_1);
x_4 = lean::nat_sub(x_3, x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_String_Iterator_remainingBytes___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_Iterator_remainingBytes___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_String_Iterator_remainingBytes(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_Iterator_remainingBytes___main(x_0);
return x_1;
}
}
obj* l_String_Iterator_remainingBytes___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_Iterator_remainingBytes(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_String_Iterator_pos___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
return x_1;
}
}
obj* l_String_Iterator_pos___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_Iterator_pos___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_String_Iterator_pos(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_Iterator_pos___main(x_0);
return x_1;
}
}
obj* l_String_Iterator_pos___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_Iterator_pos(x_0);
lean::dec(x_0);
return x_1;
}
}
uint32 l_String_Iterator_curr___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint32 x_3; 
x_1 = lean::cnstr_get(x_0, 0);
x_2 = lean::cnstr_get(x_0, 1);
x_3 = lean::string_utf8_get(x_1, x_2);
return x_3;
}
}
obj* l_String_Iterator_curr___main___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = l_String_Iterator_curr___main(x_0);
x_2 = lean::box_uint32(x_1);
lean::dec(x_0);
return x_2;
}
}
uint32 l_String_Iterator_curr(obj* x_0) {
_start:
{
uint32 x_1; 
x_1 = l_String_Iterator_curr___main(x_0);
return x_1;
}
}
obj* l_String_Iterator_curr___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = l_String_Iterator_curr(x_0);
x_2 = lean::box_uint32(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_String_Iterator_next___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_1 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_5 = x_0;
} else {
 lean::inc(x_1);
 lean::inc(x_3);
 lean::dec(x_0);
 x_5 = lean::box(0);
}
x_6 = lean::string_utf8_next(x_1, x_3);
lean::dec(x_3);
if (lean::is_scalar(x_5)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_5;
}
lean::cnstr_set(x_8, 0, x_1);
lean::cnstr_set(x_8, 1, x_6);
return x_8;
}
}
obj* l_String_Iterator_next(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_Iterator_next___main(x_0);
return x_1;
}
}
obj* l_String_Iterator_prev___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_1 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_5 = x_0;
} else {
 lean::inc(x_1);
 lean::inc(x_3);
 lean::dec(x_0);
 x_5 = lean::box(0);
}
x_6 = lean::string_utf8_prev(x_1, x_3);
lean::dec(x_3);
if (lean::is_scalar(x_5)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_5;
}
lean::cnstr_set(x_8, 0, x_1);
lean::cnstr_set(x_8, 1, x_6);
return x_8;
}
}
obj* l_String_Iterator_prev(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_Iterator_prev___main(x_0);
return x_1;
}
}
uint8 l_String_Iterator_hasNext___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; uint8 x_4; 
x_1 = lean::cnstr_get(x_0, 0);
x_2 = lean::cnstr_get(x_0, 1);
x_3 = lean::string_utf8_byte_size(x_1);
x_4 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_String_Iterator_hasNext___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_String_Iterator_hasNext___main(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_String_Iterator_hasNext(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_String_Iterator_hasNext___main(x_0);
return x_1;
}
}
obj* l_String_Iterator_hasNext___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_String_Iterator_hasNext(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_String_Iterator_hasPrev___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = lean::cnstr_get(x_0, 1);
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::nat_dec_lt(x_2, x_1);
return x_3;
}
}
obj* l_String_Iterator_hasPrev___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_String_Iterator_hasPrev___main(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_String_Iterator_hasPrev(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_String_Iterator_hasPrev___main(x_0);
return x_1;
}
}
obj* l_String_Iterator_hasPrev___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_String_Iterator_hasPrev(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_String_Iterator_setCurr___main(obj* x_0, uint32 x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_6 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = lean::string_utf8_set(x_2, x_4, x_1);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
return x_8;
}
}
obj* l_String_Iterator_setCurr___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_String_Iterator_setCurr___main(x_0, x_2);
return x_3;
}
}
obj* l_String_Iterator_setCurr(obj* x_0, uint32 x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_setCurr___main(x_0, x_1);
return x_2;
}
}
obj* l_String_Iterator_setCurr___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_String_Iterator_setCurr(x_0, x_2);
return x_3;
}
}
obj* l_String_Iterator_toEnd___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 1);
 x_3 = x_0;
} else {
 lean::inc(x_1);
 lean::dec(x_0);
 x_3 = lean::box(0);
}
x_4 = lean::string_utf8_byte_size(x_1);
if (lean::is_scalar(x_3)) {
 x_5 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_5 = x_3;
}
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
}
obj* l_String_Iterator_toEnd(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_Iterator_toEnd___main(x_0);
return x_1;
}
}
obj* l_String_Iterator_extract___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::string_dec_eq(x_2, x_4);
if (x_6 == 0)
{
obj* x_7; 
x_7 = l_String_splitAux___main___closed__1;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::nat_dec_lt(x_5, x_3);
if (x_8 == 0)
{
obj* x_9; 
x_9 = lean::string_utf8_extract(x_2, x_3, x_5);
return x_9;
}
else
{
obj* x_10; 
x_10 = l_String_splitAux___main___closed__1;
return x_10;
}
}
}
}
obj* l_String_Iterator_extract___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_extract___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_String_Iterator_extract(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_extract___main(x_0, x_1);
return x_2;
}
}
obj* l_String_Iterator_extract___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_extract(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_String_Iterator_forward___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_7; 
x_4 = lean::mk_nat_obj(1ul);
x_5 = lean::nat_sub(x_1, x_4);
lean::dec(x_1);
x_7 = l_String_Iterator_next___main(x_0);
x_0 = x_7;
x_1 = x_5;
goto _start;
}
else
{
lean::dec(x_1);
return x_0;
}
}
}
obj* l_String_Iterator_forward(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_forward___main(x_0, x_1);
return x_2;
}
}
obj* l_String_Iterator_remainingToString___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::cnstr_get(x_0, 0);
x_2 = lean::cnstr_get(x_0, 1);
x_3 = lean::string_utf8_byte_size(x_1);
x_4 = lean::string_utf8_extract(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_String_Iterator_remainingToString___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_Iterator_remainingToString___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_String_Iterator_remainingToString(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_Iterator_remainingToString___main(x_0);
return x_1;
}
}
obj* l_String_Iterator_remainingToString___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_Iterator_remainingToString(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_String_Iterator_isPrefixOfRemaining___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; uint8 x_14; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::string_utf8_byte_size(x_2);
x_7 = lean::string_utf8_extract(x_2, x_3, x_6);
x_8 = lean::nat_sub(x_6, x_3);
lean::dec(x_6);
x_10 = lean::nat_add(x_5, x_8);
lean::dec(x_8);
x_12 = lean::string_utf8_extract(x_4, x_5, x_10);
lean::dec(x_10);
x_14 = lean::string_dec_eq(x_7, x_12);
lean::dec(x_12);
lean::dec(x_7);
return x_14;
}
}
obj* l_String_Iterator_isPrefixOfRemaining___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_String_Iterator_isPrefixOfRemaining___main(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_String_Iterator_isPrefixOfRemaining(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_String_Iterator_isPrefixOfRemaining___main(x_0, x_1);
return x_2;
}
}
obj* l_String_Iterator_isPrefixOfRemaining___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_String_Iterator_isPrefixOfRemaining(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_String_Iterator_nextn___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_7; 
x_4 = lean::mk_nat_obj(1ul);
x_5 = lean::nat_sub(x_1, x_4);
lean::dec(x_1);
x_7 = l_String_Iterator_next___main(x_0);
x_0 = x_7;
x_1 = x_5;
goto _start;
}
else
{
lean::dec(x_1);
return x_0;
}
}
}
obj* l_String_Iterator_nextn(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_nextn___main(x_0, x_1);
return x_2;
}
}
obj* l_String_Iterator_prevn___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_7; 
x_4 = lean::mk_nat_obj(1ul);
x_5 = lean::nat_sub(x_1, x_4);
lean::dec(x_1);
x_7 = l_String_Iterator_prev___main(x_0);
x_0 = x_7;
x_1 = x_5;
goto _start;
}
else
{
lean::dec(x_1);
return x_0;
}
}
}
obj* l_String_Iterator_prevn(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_prevn___main(x_0, x_1);
return x_2;
}
}
obj* l___private_init_data_string_basic_8__lineColumnAux___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_8; uint8 x_10; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
x_10 = lean::string_utf8_at_end(x_0, x_2);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; uint32 x_15; uint32 x_16; uint8 x_17; 
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_11 = x_3;
} else {
 lean::dec(x_3);
 x_11 = lean::box(0);
}
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_sub(x_1, x_12);
lean::dec(x_1);
x_15 = lean::string_utf8_get(x_0, x_2);
x_16 = 10;
x_17 = x_15 == x_16;
if (x_17 == 0)
{
obj* x_18; obj* x_20; obj* x_22; 
x_18 = lean::string_utf8_next(x_0, x_2);
lean::dec(x_2);
x_20 = lean::nat_add(x_8, x_12);
lean::dec(x_8);
if (lean::is_scalar(x_11)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_11;
}
lean::cnstr_set(x_22, 0, x_6);
lean::cnstr_set(x_22, 1, x_20);
x_1 = x_13;
x_2 = x_18;
x_3 = x_22;
goto _start;
}
else
{
obj* x_25; obj* x_27; obj* x_29; 
lean::dec(x_8);
x_25 = lean::string_utf8_next(x_0, x_2);
lean::dec(x_2);
x_27 = lean::nat_add(x_6, x_12);
lean::dec(x_6);
if (lean::is_scalar(x_11)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_11;
}
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_4);
x_1 = x_13;
x_2 = x_25;
x_3 = x_29;
goto _start;
}
}
else
{
lean::dec(x_8);
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
else
{
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
}
obj* l___private_init_data_string_basic_8__lineColumnAux___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_data_string_basic_8__lineColumnAux___main(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l___private_init_data_string_basic_8__lineColumnAux(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_data_string_basic_8__lineColumnAux___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_data_string_basic_8__lineColumnAux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_data_string_basic_8__lineColumnAux(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* _init_l_String_lineColumn___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(1ul);
x_1 = lean::mk_nat_obj(0ul);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_String_lineColumn(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::string_utf8_byte_size(x_0);
x_3 = lean::mk_nat_obj(1ul);
x_4 = lean::nat_add(x_2, x_3);
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0ul);
x_7 = l_String_lineColumn___closed__1;
x_8 = l___private_init_data_string_basic_8__lineColumnAux___main(x_0, x_4, x_6, x_7);
return x_8;
}
}
obj* l_String_lineColumn___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_lineColumn(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_String_offsetOfPosAux___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = lean::nat_dec_eq(x_3, x_1);
if (x_7 == 0)
{
uint8 x_8; 
x_8 = lean::string_utf8_at_end(x_0, x_3);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_12; obj* x_14; 
x_9 = lean::mk_nat_obj(1ul);
x_10 = lean::nat_sub(x_2, x_9);
lean::dec(x_2);
x_12 = lean::string_utf8_next(x_0, x_3);
lean::dec(x_3);
x_14 = lean::nat_add(x_4, x_9);
lean::dec(x_4);
x_2 = x_10;
x_3 = x_12;
x_4 = x_14;
goto _start;
}
else
{
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
else
{
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
else
{
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
}
obj* l_String_offsetOfPosAux___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_String_offsetOfPosAux___main(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_String_offsetOfPosAux(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_String_offsetOfPosAux___main(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_String_offsetOfPosAux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_String_offsetOfPosAux(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_String_offsetOfPos(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
x_2 = lean::string_utf8_byte_size(x_0);
x_3 = lean::mk_nat_obj(1ul);
x_4 = lean::nat_add(x_2, x_3);
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0ul);
x_7 = l_String_offsetOfPosAux___main(x_0, x_1, x_4, x_6, x_6);
return x_7;
}
}
obj* l_String_offsetOfPos___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_offsetOfPos(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_String_foldlAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0ul);
x_7 = lean::nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
uint8 x_8; 
x_8 = lean::nat_dec_eq(x_4, x_2);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_12; uint32 x_13; obj* x_15; obj* x_17; 
x_9 = lean::mk_nat_obj(1ul);
x_10 = lean::nat_sub(x_3, x_9);
lean::dec(x_3);
x_12 = lean::string_utf8_next(x_1, x_4);
x_13 = lean::string_utf8_get(x_1, x_4);
lean::dec(x_4);
x_15 = lean::box_uint32(x_13);
lean::inc(x_0);
x_17 = lean::apply_2(x_0, x_5, x_15);
x_3 = x_10;
x_4 = x_12;
x_5 = x_17;
goto _start;
}
else
{
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
return x_5;
}
}
else
{
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
return x_5;
}
}
}
obj* l_String_foldlAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_String_foldlAux___main___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_String_foldlAux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_String_foldlAux___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_String_foldlAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_foldlAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_String_foldlAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_String_foldlAux___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_String_foldlAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_String_foldlAux___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_String_foldlAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_String_foldlAux___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_String_foldlAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_foldlAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_String_foldl___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::string_utf8_byte_size(x_2);
x_4 = lean::mk_nat_obj(1ul);
x_5 = lean::nat_add(x_3, x_4);
x_6 = lean::mk_nat_obj(0ul);
x_7 = l_String_foldlAux___main___rarg(x_0, x_2, x_3, x_5, x_6, x_1);
lean::dec(x_3);
return x_7;
}
}
obj* l_String_foldl(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_String_foldl___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_String_foldl___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_String_foldl___rarg(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_String_foldl___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_foldl(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_String_foldrAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0ul);
x_7 = lean::nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
uint8 x_8; 
x_8 = lean::nat_dec_eq(x_5, x_3);
if (x_8 == 0)
{
obj* x_9; obj* x_10; uint32 x_11; obj* x_12; obj* x_14; obj* x_17; obj* x_18; 
x_9 = lean::mk_nat_obj(1ul);
x_10 = lean::nat_sub(x_4, x_9);
x_11 = lean::string_utf8_get(x_2, x_5);
x_12 = lean::string_utf8_next(x_2, x_5);
lean::inc(x_0);
x_14 = l_String_foldrAux___main___rarg(x_0, x_1, x_2, x_3, x_10, x_12);
lean::dec(x_12);
lean::dec(x_10);
x_17 = lean::box_uint32(x_11);
x_18 = lean::apply_2(x_0, x_17, x_14);
return x_18;
}
else
{
lean::dec(x_0);
lean::inc(x_1);
return x_1;
}
}
else
{
lean::dec(x_0);
lean::inc(x_1);
return x_1;
}
}
}
obj* l_String_foldrAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_String_foldrAux___main___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_String_foldrAux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_String_foldrAux___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
return x_6;
}
}
obj* l_String_foldrAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_foldrAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_String_foldrAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_String_foldrAux___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_String_foldrAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_String_foldrAux___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_String_foldrAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_String_foldrAux___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
return x_6;
}
}
obj* l_String_foldrAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_foldrAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_String_foldr___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::string_utf8_byte_size(x_2);
x_4 = lean::mk_nat_obj(1ul);
x_5 = lean::nat_add(x_3, x_4);
x_6 = lean::mk_nat_obj(0ul);
x_7 = l_String_foldrAux___main___rarg(x_0, x_1, x_2, x_3, x_5, x_6);
lean::dec(x_5);
lean::dec(x_3);
return x_7;
}
}
obj* l_String_foldr(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_String_foldr___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_String_foldr___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_String_foldr___rarg(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_String_foldr___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_foldr(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_String_anyAux___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = lean::nat_dec_eq(x_4, x_1);
if (x_7 == 0)
{
uint32 x_8; obj* x_9; obj* x_11; uint8 x_12; 
x_8 = lean::string_utf8_get(x_0, x_4);
x_9 = lean::box_uint32(x_8);
lean::inc(x_2);
x_11 = lean::apply_1(x_2, x_9);
x_12 = lean::unbox(x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_16; 
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_sub(x_3, x_13);
lean::dec(x_3);
x_16 = lean::string_utf8_next(x_0, x_4);
lean::dec(x_4);
x_3 = x_14;
x_4 = x_16;
goto _start;
}
else
{
uint8 x_22; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_22 = 1;
return x_22;
}
}
else
{
uint8 x_26; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_26 = 0;
return x_26;
}
}
else
{
uint8 x_30; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_30 = 0;
return x_30;
}
}
}
obj* l_String_anyAux___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_String_anyAux___main(x_0, x_1, x_2, x_3, x_4);
x_6 = lean::box(x_5);
lean::dec(x_0);
lean::dec(x_1);
return x_6;
}
}
uint8 l_String_anyAux(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = l_String_anyAux___main(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_String_anyAux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_String_anyAux(x_0, x_1, x_2, x_3, x_4);
x_6 = lean::box(x_5);
lean::dec(x_0);
lean::dec(x_1);
return x_6;
}
}
uint8 l_String_any(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_2 = lean::string_utf8_byte_size(x_0);
x_3 = lean::mk_nat_obj(1ul);
x_4 = lean::nat_add(x_2, x_3);
x_5 = lean::mk_nat_obj(0ul);
x_6 = l_String_anyAux___main(x_0, x_2, x_1, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_String_any___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_String_any(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
return x_3;
}
}
uint8 l_String_anyAux___main___at_String_all___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = lean::nat_dec_eq(x_4, x_2);
if (x_7 == 0)
{
uint32 x_8; obj* x_9; obj* x_11; uint8 x_12; 
x_8 = lean::string_utf8_get(x_1, x_4);
x_9 = lean::box_uint32(x_8);
lean::inc(x_0);
x_11 = lean::apply_1(x_0, x_9);
x_12 = lean::unbox(x_11);
if (x_12 == 0)
{
uint8 x_16; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_16 = 1;
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_20; 
x_17 = lean::mk_nat_obj(1ul);
x_18 = lean::nat_sub(x_3, x_17);
lean::dec(x_3);
x_20 = lean::string_utf8_next(x_1, x_4);
lean::dec(x_4);
x_3 = x_18;
x_4 = x_20;
goto _start;
}
}
else
{
uint8 x_26; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_26 = 0;
return x_26;
}
}
else
{
uint8 x_30; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_30 = 0;
return x_30;
}
}
}
uint8 l_String_all(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_2 = lean::string_utf8_byte_size(x_0);
x_3 = lean::mk_nat_obj(1ul);
x_4 = lean::nat_add(x_2, x_3);
x_5 = lean::mk_nat_obj(0ul);
x_6 = l_String_anyAux___main___at_String_all___spec__1(x_1, x_0, x_2, x_4, x_5);
lean::dec(x_2);
if (x_6 == 0)
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8 x_9; 
x_9 = 0;
return x_9;
}
}
}
obj* l_String_anyAux___main___at_String_all___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_String_anyAux___main___at_String_all___spec__1(x_0, x_1, x_2, x_3, x_4);
x_6 = lean::box(x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_String_all___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_String_all(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
return x_3;
}
}
uint8 l_String_anyAux___main___at_String_contains___spec__1(uint32 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = lean::nat_dec_eq(x_4, x_2);
if (x_7 == 0)
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_utf8_get(x_1, x_4);
x_9 = x_8 == x_0;
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; 
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_sub(x_3, x_10);
lean::dec(x_3);
x_13 = lean::string_utf8_next(x_1, x_4);
lean::dec(x_4);
x_3 = x_11;
x_4 = x_13;
goto _start;
}
else
{
uint8 x_18; 
lean::dec(x_4);
lean::dec(x_3);
x_18 = 1;
return x_18;
}
}
else
{
uint8 x_21; 
lean::dec(x_4);
lean::dec(x_3);
x_21 = 0;
return x_21;
}
}
else
{
uint8 x_24; 
lean::dec(x_4);
lean::dec(x_3);
x_24 = 0;
return x_24;
}
}
}
uint8 l_String_contains(obj* x_0, uint32 x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_2 = lean::string_utf8_byte_size(x_0);
x_3 = lean::mk_nat_obj(1ul);
x_4 = lean::nat_add(x_2, x_3);
x_5 = lean::mk_nat_obj(0ul);
x_6 = l_String_anyAux___main___at_String_contains___spec__1(x_1, x_0, x_2, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_String_anyAux___main___at_String_contains___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; uint8 x_6; obj* x_7; 
x_5 = lean::unbox_uint32(x_0);
x_6 = l_String_anyAux___main___at_String_contains___spec__1(x_5, x_1, x_2, x_3, x_4);
x_7 = lean::box(x_6);
lean::dec(x_1);
lean::dec(x_2);
return x_7;
}
}
obj* l_String_contains___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_String_contains(x_0, x_2);
x_4 = lean::box(x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_String_mapAux___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = lean::string_utf8_at_end(x_3, x_2);
if (x_6 == 0)
{
obj* x_7; obj* x_8; uint32 x_10; obj* x_11; obj* x_13; uint32 x_14; obj* x_15; obj* x_16; 
x_7 = lean::mk_nat_obj(1ul);
x_8 = lean::nat_sub(x_1, x_7);
lean::dec(x_1);
x_10 = lean::string_utf8_get(x_3, x_2);
x_11 = lean::box_uint32(x_10);
lean::inc(x_0);
x_13 = lean::apply_1(x_0, x_11);
x_14 = lean::unbox_uint32(x_13);
x_15 = lean::string_utf8_set(x_3, x_2, x_14);
x_16 = lean::string_utf8_next(x_15, x_2);
lean::dec(x_2);
x_1 = x_8;
x_2 = x_16;
x_3 = x_15;
goto _start;
}
else
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
}
else
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
}
}
obj* l_String_mapAux(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_String_mapAux___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_String_map(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
x_2 = lean::string_utf8_byte_size(x_1);
x_3 = lean::mk_nat_obj(1ul);
x_4 = lean::nat_add(x_2, x_3);
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0ul);
x_7 = l_String_mapAux___main(x_0, x_4, x_6, x_1);
return x_7;
}
}
obj* _init_l_String_foldlAux___main___at_String_toNat___spec__1___closed__1() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = 48;
x_1 = lean::uint32_to_nat(x_0);
return x_1;
}
}
obj* l_String_foldlAux___main___at_String_toNat___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = lean::nat_dec_eq(x_3, x_1);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_11; uint32 x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_21; 
x_8 = lean::mk_nat_obj(1ul);
x_9 = lean::nat_sub(x_2, x_8);
lean::dec(x_2);
x_11 = lean::string_utf8_next(x_0, x_3);
x_12 = lean::string_utf8_get(x_0, x_3);
lean::dec(x_3);
x_14 = lean::mk_nat_obj(10ul);
x_15 = lean::nat_mul(x_4, x_14);
lean::dec(x_4);
x_17 = lean::uint32_to_nat(x_12);
x_18 = l_String_foldlAux___main___at_String_toNat___spec__1___closed__1;
x_19 = lean::nat_sub(x_17, x_18);
lean::dec(x_17);
x_21 = lean::nat_add(x_15, x_19);
lean::dec(x_19);
lean::dec(x_15);
x_2 = x_9;
x_3 = x_11;
x_4 = x_21;
goto _start;
}
else
{
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
else
{
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
}
obj* l_String_toNat(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::string_utf8_byte_size(x_0);
x_2 = lean::mk_nat_obj(1ul);
x_3 = lean::nat_add(x_1, x_2);
x_4 = lean::mk_nat_obj(0ul);
x_5 = l_String_foldlAux___main___at_String_toNat___spec__1(x_0, x_1, x_3, x_4, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_String_foldlAux___main___at_String_toNat___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_String_foldlAux___main___at_String_toNat___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_String_toNat___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_toNat(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_String_anyAux___main___at_String_isNat___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = lean::nat_dec_eq(x_3, x_1);
if (x_6 == 0)
{
uint32 x_7; uint8 x_8; 
x_7 = lean::string_utf8_get(x_0, x_3);
x_8 = l_Char_isDigit(x_7);
if (x_8 == 0)
{
uint8 x_11; 
lean::dec(x_3);
lean::dec(x_2);
x_11 = 1;
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; 
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_sub(x_2, x_12);
lean::dec(x_2);
x_15 = lean::string_utf8_next(x_0, x_3);
lean::dec(x_3);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
else
{
uint8 x_20; 
lean::dec(x_3);
lean::dec(x_2);
x_20 = 0;
return x_20;
}
}
else
{
uint8 x_23; 
lean::dec(x_3);
lean::dec(x_2);
x_23 = 0;
return x_23;
}
}
}
uint8 l_String_isNat(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; uint8 x_5; 
x_1 = lean::string_utf8_byte_size(x_0);
x_2 = lean::mk_nat_obj(1ul);
x_3 = lean::nat_add(x_1, x_2);
x_4 = lean::mk_nat_obj(0ul);
x_5 = l_String_anyAux___main___at_String_isNat___spec__1(x_0, x_1, x_3, x_4);
lean::dec(x_1);
if (x_5 == 0)
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8 x_8; 
x_8 = 0;
return x_8;
}
}
}
obj* l_String_anyAux___main___at_String_isNat___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_String_anyAux___main___at_String_isNat___spec__1(x_0, x_1, x_2, x_3);
x_5 = lean::box(x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_String_isNat___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_String_isNat(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Substring_toString___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::cnstr_get(x_0, 0);
x_2 = lean::cnstr_get(x_0, 1);
x_3 = lean::cnstr_get(x_0, 2);
x_4 = lean::string_utf8_extract(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Substring_toString___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Substring_toString___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Substring_toString(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::cnstr_get(x_0, 0);
x_2 = lean::cnstr_get(x_0, 1);
x_3 = lean::cnstr_get(x_0, 2);
x_4 = lean::string_utf8_extract(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Substring_toString___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Substring_toString(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Substring_toIterator___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l_Substring_toIterator(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
uint32 l_Substring_get___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; uint32 x_5; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = lean::nat_add(x_3, x_1);
x_5 = lean::string_utf8_get(x_2, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Substring_get___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = l_Substring_get___main(x_0, x_1);
x_3 = lean::box_uint32(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint32 l_Substring_get(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; uint32 x_5; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = lean::nat_add(x_3, x_1);
x_5 = lean::string_utf8_get(x_2, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Substring_get___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = l_Substring_get(x_0, x_1);
x_3 = lean::box_uint32(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Substring_next___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_8; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = lean::cnstr_get(x_0, 2);
x_5 = lean::nat_add(x_3, x_1);
x_6 = lean::string_utf8_next(x_2, x_5);
lean::dec(x_5);
x_8 = lean::nat_dec_lt(x_4, x_6);
if (x_8 == 0)
{
obj* x_9; 
x_9 = lean::nat_sub(x_6, x_3);
lean::dec(x_6);
return x_9;
}
else
{
obj* x_12; 
lean::dec(x_6);
x_12 = lean::nat_sub(x_4, x_3);
return x_12;
}
}
}
obj* l_Substring_next___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Substring_next___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Substring_next(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_8; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = lean::cnstr_get(x_0, 2);
x_5 = lean::nat_add(x_3, x_1);
x_6 = lean::string_utf8_next(x_2, x_5);
lean::dec(x_5);
x_8 = lean::nat_dec_lt(x_4, x_6);
if (x_8 == 0)
{
obj* x_9; 
x_9 = lean::nat_sub(x_6, x_3);
lean::dec(x_6);
return x_9;
}
else
{
obj* x_12; 
lean::dec(x_6);
x_12 = lean::nat_sub(x_4, x_3);
return x_12;
}
}
}
obj* l_Substring_next___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Substring_next(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Substring_prev___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = lean::nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_8; 
x_5 = lean::nat_add(x_3, x_1);
x_6 = lean::string_utf8_prev(x_2, x_5);
lean::dec(x_5);
x_8 = lean::nat_sub(x_6, x_3);
lean::dec(x_6);
return x_8;
}
else
{
lean::inc(x_1);
return x_1;
}
}
}
obj* l_Substring_prev___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Substring_prev___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Substring_prev(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = lean::nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_8; 
x_5 = lean::nat_add(x_3, x_1);
x_6 = lean::string_utf8_prev(x_2, x_5);
lean::dec(x_5);
x_8 = lean::nat_sub(x_6, x_3);
lean::dec(x_6);
return x_8;
}
else
{
lean::inc(x_1);
return x_1;
}
}
}
obj* l_Substring_prev___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Substring_prev(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint32 l_Substring_front(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; uint32 x_5; 
x_1 = lean::cnstr_get(x_0, 0);
x_2 = lean::cnstr_get(x_0, 1);
x_3 = lean::mk_nat_obj(0ul);
x_4 = lean::nat_add(x_2, x_3);
x_5 = lean::string_utf8_get(x_1, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Substring_front___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = l_Substring_front(x_0);
x_2 = lean::box_uint32(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Substring_posOf(obj* x_0, uint32 x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_14; obj* x_17; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::string_utf8_byte_size(x_2);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_9, x_10);
lean::dec(x_9);
lean::inc(x_4);
x_14 = l_String_posOfAux___main(x_2, x_1, x_6, x_11, x_4);
lean::dec(x_6);
lean::dec(x_2);
x_17 = lean::nat_sub(x_14, x_4);
lean::dec(x_4);
lean::dec(x_14);
return x_17;
}
}
obj* l_Substring_posOf___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_Substring_posOf(x_0, x_2);
return x_3;
}
}
obj* _init_l_Substring_drop___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::mk_string("");
x_1 = lean::string_utf8_byte_size(x_0);
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
lean::cnstr_set(x_3, 2, x_1);
return x_3;
}
}
obj* l_Substring_drop___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_11; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_6 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 x_8 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_0);
 x_8 = lean::box(0);
}
x_9 = lean::nat_add(x_4, x_1);
lean::dec(x_4);
x_11 = lean::nat_dec_le(x_6, x_9);
if (x_11 == 0)
{
obj* x_12; 
if (lean::is_scalar(x_8)) {
 x_12 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_12 = x_8;
}
lean::cnstr_set(x_12, 0, x_2);
lean::cnstr_set(x_12, 1, x_9);
lean::cnstr_set(x_12, 2, x_6);
return x_12;
}
else
{
obj* x_17; 
lean::dec(x_8);
lean::dec(x_6);
lean::dec(x_9);
lean::dec(x_2);
x_17 = l_Substring_drop___main___closed__1;
return x_17;
}
}
}
obj* l_Substring_drop___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Substring_drop___main(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Substring_drop(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_11; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_6 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 x_8 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_0);
 x_8 = lean::box(0);
}
x_9 = lean::nat_add(x_4, x_1);
lean::dec(x_4);
x_11 = lean::nat_dec_le(x_6, x_9);
if (x_11 == 0)
{
obj* x_12; 
if (lean::is_scalar(x_8)) {
 x_12 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_12 = x_8;
}
lean::cnstr_set(x_12, 0, x_2);
lean::cnstr_set(x_12, 1, x_9);
lean::cnstr_set(x_12, 2, x_6);
return x_12;
}
else
{
obj* x_17; 
lean::dec(x_8);
lean::dec(x_6);
lean::dec(x_9);
lean::dec(x_2);
x_17 = l_Substring_drop___main___closed__1;
return x_17;
}
}
}
obj* l_Substring_drop___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Substring_drop(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Substring_dropRight___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_10; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_6 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 x_8 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_0);
 x_8 = lean::box(0);
}
x_9 = lean::nat_sub(x_6, x_1);
x_10 = lean::nat_dec_le(x_9, x_6);
lean::dec(x_6);
if (x_10 == 0)
{
obj* x_12; 
if (lean::is_scalar(x_8)) {
 x_12 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_12 = x_8;
}
lean::cnstr_set(x_12, 0, x_2);
lean::cnstr_set(x_12, 1, x_4);
lean::cnstr_set(x_12, 2, x_9);
return x_12;
}
else
{
obj* x_17; 
lean::dec(x_8);
lean::dec(x_9);
lean::dec(x_4);
lean::dec(x_2);
x_17 = l_Substring_drop___main___closed__1;
return x_17;
}
}
}
obj* l_Substring_dropRight___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Substring_dropRight___main(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Substring_dropRight(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_10; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_6 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 x_8 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_0);
 x_8 = lean::box(0);
}
x_9 = lean::nat_sub(x_6, x_1);
x_10 = lean::nat_dec_le(x_9, x_6);
lean::dec(x_6);
if (x_10 == 0)
{
obj* x_12; 
if (lean::is_scalar(x_8)) {
 x_12 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_12 = x_8;
}
lean::cnstr_set(x_12, 0, x_2);
lean::cnstr_set(x_12, 1, x_4);
lean::cnstr_set(x_12, 2, x_9);
return x_12;
}
else
{
obj* x_17; 
lean::dec(x_8);
lean::dec(x_9);
lean::dec(x_4);
lean::dec(x_2);
x_17 = l_Substring_drop___main___closed__1;
return x_17;
}
}
}
obj* l_Substring_dropRight___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Substring_dropRight(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Substring_take___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_10; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_6 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 x_8 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_0);
 x_8 = lean::box(0);
}
x_9 = lean::nat_add(x_4, x_1);
x_10 = lean::nat_dec_le(x_6, x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_6);
if (lean::is_scalar(x_8)) {
 x_12 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_12 = x_8;
}
lean::cnstr_set(x_12, 0, x_2);
lean::cnstr_set(x_12, 1, x_4);
lean::cnstr_set(x_12, 2, x_9);
return x_12;
}
else
{
obj* x_14; 
lean::dec(x_9);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_2);
lean::cnstr_set(x_14, 1, x_4);
lean::cnstr_set(x_14, 2, x_6);
return x_14;
}
}
}
obj* l_Substring_take___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Substring_take___main(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Substring_take(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_10; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_6 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 x_8 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_0);
 x_8 = lean::box(0);
}
x_9 = lean::nat_add(x_4, x_1);
x_10 = lean::nat_dec_le(x_6, x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_6);
if (lean::is_scalar(x_8)) {
 x_12 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_12 = x_8;
}
lean::cnstr_set(x_12, 0, x_2);
lean::cnstr_set(x_12, 1, x_4);
lean::cnstr_set(x_12, 2, x_9);
return x_12;
}
else
{
obj* x_14; 
lean::dec(x_9);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_2);
lean::cnstr_set(x_14, 1, x_4);
lean::cnstr_set(x_14, 2, x_6);
return x_14;
}
}
}
obj* l_Substring_take___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Substring_take(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Substring_takeRight___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_10; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_6 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 x_8 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_0);
 x_8 = lean::box(0);
}
x_9 = lean::nat_sub(x_6, x_1);
x_10 = lean::nat_dec_le(x_9, x_4);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_4);
if (lean::is_scalar(x_8)) {
 x_12 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_12 = x_8;
}
lean::cnstr_set(x_12, 0, x_2);
lean::cnstr_set(x_12, 1, x_9);
lean::cnstr_set(x_12, 2, x_6);
return x_12;
}
else
{
obj* x_14; 
lean::dec(x_9);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_2);
lean::cnstr_set(x_14, 1, x_4);
lean::cnstr_set(x_14, 2, x_6);
return x_14;
}
}
}
obj* l_Substring_takeRight___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Substring_takeRight___main(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Substring_takeRight(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_10; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_6 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 x_8 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_0);
 x_8 = lean::box(0);
}
x_9 = lean::nat_sub(x_6, x_1);
x_10 = lean::nat_dec_le(x_9, x_4);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_4);
if (lean::is_scalar(x_8)) {
 x_12 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_12 = x_8;
}
lean::cnstr_set(x_12, 0, x_2);
lean::cnstr_set(x_12, 1, x_9);
lean::cnstr_set(x_12, 2, x_6);
return x_12;
}
else
{
obj* x_14; 
lean::dec(x_9);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_2);
lean::cnstr_set(x_14, 1, x_4);
lean::cnstr_set(x_14, 2, x_6);
return x_14;
}
}
}
obj* l_Substring_takeRight___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Substring_takeRight(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
uint8 l_Substring_atEnd___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; uint8 x_5; 
x_2 = lean::cnstr_get(x_0, 1);
x_3 = lean::cnstr_get(x_0, 2);
x_4 = lean::nat_add(x_2, x_1);
x_5 = lean::nat_dec_eq(x_4, x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_Substring_atEnd___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Substring_atEnd___main(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Substring_atEnd(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; uint8 x_5; 
x_2 = lean::cnstr_get(x_0, 1);
x_3 = lean::cnstr_get(x_0, 2);
x_4 = lean::nat_add(x_2, x_1);
x_5 = lean::nat_dec_eq(x_4, x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_Substring_atEnd___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Substring_atEnd(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Substring_extract___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::mk_string("");
x_1 = lean::mk_nat_obj(0ul);
x_2 = lean::mk_nat_obj(1ul);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
return x_3;
}
}
obj* l_Substring_extract___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; uint8 x_8; 
x_3 = lean::cnstr_get(x_0, 0);
x_5 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_release(x_0, 2);
 x_7 = x_0;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_0);
 x_7 = lean::box(0);
}
x_8 = lean::nat_dec_le(x_2, x_1);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_12; 
x_9 = lean::nat_add(x_5, x_1);
x_10 = lean::nat_add(x_5, x_2);
lean::dec(x_5);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_3);
lean::cnstr_set(x_12, 1, x_9);
lean::cnstr_set(x_12, 2, x_10);
return x_12;
}
else
{
obj* x_16; 
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_3);
x_16 = l_Substring_extract___main___closed__1;
return x_16;
}
}
}
obj* l_Substring_extract___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Substring_extract___main(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Substring_extract(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; uint8 x_8; 
x_3 = lean::cnstr_get(x_0, 0);
x_5 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_release(x_0, 2);
 x_7 = x_0;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_0);
 x_7 = lean::box(0);
}
x_8 = lean::nat_dec_le(x_2, x_1);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_12; 
x_9 = lean::nat_add(x_5, x_1);
x_10 = lean::nat_add(x_5, x_2);
lean::dec(x_5);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_3);
lean::cnstr_set(x_12, 1, x_9);
lean::cnstr_set(x_12, 2, x_10);
return x_12;
}
else
{
obj* x_16; 
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_3);
x_16 = l_Substring_extract___main___closed__1;
return x_16;
}
}
}
obj* l_Substring_extract___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Substring_extract(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Substring_splitAux___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(0ul);
x_9 = lean::nat_dec_eq(x_3, x_8);
if (x_9 == 0)
{
uint8 x_10; 
x_10 = lean::nat_dec_eq(x_5, x_2);
if (x_10 == 0)
{
obj* x_11; obj* x_12; uint32 x_14; uint32 x_15; uint8 x_16; 
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_sub(x_3, x_11);
lean::dec(x_3);
x_14 = lean::string_utf8_get(x_0, x_5);
x_15 = lean::string_utf8_get(x_1, x_6);
x_16 = x_14 == x_15;
if (x_16 == 0)
{
obj* x_18; 
lean::dec(x_6);
x_18 = lean::string_utf8_next(x_0, x_5);
lean::dec(x_5);
x_3 = x_12;
x_5 = x_18;
x_6 = x_8;
goto _start;
}
else
{
obj* x_21; obj* x_23; uint8 x_25; 
x_21 = lean::string_utf8_next(x_0, x_5);
lean::dec(x_5);
x_23 = lean::string_utf8_next(x_1, x_6);
lean::dec(x_6);
x_25 = lean::string_utf8_at_end(x_1, x_23);
if (x_25 == 0)
{
x_3 = x_12;
x_5 = x_21;
x_6 = x_23;
goto _start;
}
else
{
obj* x_27; obj* x_30; obj* x_31; 
x_27 = lean::nat_sub(x_21, x_23);
lean::dec(x_23);
lean::inc(x_0);
x_30 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_30, 0, x_0);
lean::cnstr_set(x_30, 1, x_4);
lean::cnstr_set(x_30, 2, x_27);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_7);
lean::inc(x_21);
x_3 = x_12;
x_4 = x_21;
x_5 = x_21;
x_6 = x_8;
x_7 = x_31;
goto _start;
}
}
}
else
{
uint8 x_35; 
lean::dec(x_3);
x_35 = lean::string_utf8_at_end(x_1, x_6);
if (x_35 == 0)
{
obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_6);
x_37 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_37, 0, x_0);
lean::cnstr_set(x_37, 1, x_4);
lean::cnstr_set(x_37, 2, x_5);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_7);
x_39 = l_List_reverse___rarg(x_38);
return x_39;
}
else
{
obj* x_40; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_40 = lean::nat_sub(x_5, x_6);
lean::dec(x_6);
lean::dec(x_5);
x_43 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_43, 0, x_0);
lean::cnstr_set(x_43, 1, x_4);
lean::cnstr_set(x_43, 2, x_40);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_7);
x_45 = l_Substring_drop___main___closed__1;
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_44);
x_47 = l_List_reverse___rarg(x_46);
return x_47;
}
}
}
else
{
obj* x_54; 
lean::dec(x_5);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
x_54 = lean::box(0);
return x_54;
}
}
}
obj* l_Substring_splitAux___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Substring_splitAux___main(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_1);
lean::dec(x_2);
return x_8;
}
}
obj* l_Substring_splitAux(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Substring_splitAux___main(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
obj* l_Substring_splitAux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Substring_splitAux(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_1);
lean::dec(x_2);
return x_8;
}
}
obj* l_Substring_split(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean::string_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_18; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
x_8 = lean::string_utf8_byte_size(x_4);
x_9 = lean::mk_nat_obj(1ul);
x_10 = lean::nat_add(x_8, x_9);
lean::dec(x_8);
x_12 = lean::cnstr_get(x_0, 1);
lean::inc(x_12);
lean::dec(x_0);
x_15 = lean::box(0);
x_16 = lean::mk_nat_obj(0ul);
lean::inc(x_12);
x_18 = l_Substring_splitAux___main(x_4, x_1, x_6, x_10, x_12, x_12, x_16, x_15);
lean::dec(x_6);
return x_18;
}
else
{
obj* x_20; obj* x_21; 
x_20 = lean::box(0);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_0);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
}
obj* l_Substring_split___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Substring_split(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Substring_foldl___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_14; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 2);
lean::inc(x_7);
lean::dec(x_2);
x_10 = lean::string_utf8_byte_size(x_3);
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_add(x_10, x_11);
lean::dec(x_10);
x_14 = l_String_foldlAux___main___rarg(x_0, x_3, x_7, x_12, x_5, x_1);
lean::dec(x_7);
lean::dec(x_3);
return x_14;
}
}
obj* l_Substring_foldl(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Substring_foldl___rarg), 3, 0);
return x_1;
}
}
obj* l_Substring_foldl___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Substring_foldl(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Substring_foldr___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::cnstr_get(x_2, 2);
x_6 = lean::string_utf8_byte_size(x_3);
x_7 = lean::mk_nat_obj(1ul);
x_8 = lean::nat_add(x_6, x_7);
lean::dec(x_6);
x_10 = l_String_foldrAux___main___rarg(x_0, x_1, x_3, x_5, x_8, x_4);
lean::dec(x_8);
return x_10;
}
}
obj* l_Substring_foldr(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Substring_foldr___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_Substring_foldr___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Substring_foldr___rarg(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Substring_foldr___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Substring_foldr(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_Substring_any(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_9; obj* x_10; obj* x_11; uint8 x_13; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::string_utf8_byte_size(x_2);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_9, x_10);
lean::dec(x_9);
x_13 = l_String_anyAux___main(x_2, x_6, x_1, x_11, x_4);
lean::dec(x_6);
lean::dec(x_2);
return x_13;
}
}
obj* l_Substring_any___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Substring_any(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_String_anyAux___main___at_Substring_all___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = lean::nat_dec_eq(x_4, x_2);
if (x_7 == 0)
{
uint32 x_8; obj* x_9; obj* x_11; uint8 x_12; 
x_8 = lean::string_utf8_get(x_1, x_4);
x_9 = lean::box_uint32(x_8);
lean::inc(x_0);
x_11 = lean::apply_1(x_0, x_9);
x_12 = lean::unbox(x_11);
if (x_12 == 0)
{
uint8 x_16; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_16 = 1;
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_20; 
x_17 = lean::mk_nat_obj(1ul);
x_18 = lean::nat_sub(x_3, x_17);
lean::dec(x_3);
x_20 = lean::string_utf8_next(x_1, x_4);
lean::dec(x_4);
x_3 = x_18;
x_4 = x_20;
goto _start;
}
}
else
{
uint8 x_26; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_26 = 0;
return x_26;
}
}
else
{
uint8 x_30; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_30 = 0;
return x_30;
}
}
}
uint8 l_Substring_all(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_9; obj* x_10; obj* x_11; uint8 x_13; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::string_utf8_byte_size(x_2);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_9, x_10);
lean::dec(x_9);
x_13 = l_String_anyAux___main___at_Substring_all___spec__1(x_1, x_2, x_6, x_11, x_4);
lean::dec(x_6);
lean::dec(x_2);
if (x_13 == 0)
{
uint8 x_16; 
x_16 = 1;
return x_16;
}
else
{
uint8 x_17; 
x_17 = 0;
return x_17;
}
}
}
obj* l_String_anyAux___main___at_Substring_all___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_String_anyAux___main___at_Substring_all___spec__1(x_0, x_1, x_2, x_3, x_4);
x_6 = lean::box(x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Substring_all___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Substring_all(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_String_anyAux___main___at_Substring_contains___spec__1(uint32 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = lean::nat_dec_eq(x_4, x_2);
if (x_7 == 0)
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_utf8_get(x_1, x_4);
x_9 = x_8 == x_0;
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; 
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_sub(x_3, x_10);
lean::dec(x_3);
x_13 = lean::string_utf8_next(x_1, x_4);
lean::dec(x_4);
x_3 = x_11;
x_4 = x_13;
goto _start;
}
else
{
uint8 x_18; 
lean::dec(x_4);
lean::dec(x_3);
x_18 = 1;
return x_18;
}
}
else
{
uint8 x_21; 
lean::dec(x_4);
lean::dec(x_3);
x_21 = 0;
return x_21;
}
}
else
{
uint8 x_24; 
lean::dec(x_4);
lean::dec(x_3);
x_24 = 0;
return x_24;
}
}
}
uint8 l_Substring_contains(obj* x_0, uint32 x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_9; obj* x_10; obj* x_11; uint8 x_13; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::string_utf8_byte_size(x_2);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_9, x_10);
lean::dec(x_9);
x_13 = l_String_anyAux___main___at_Substring_contains___spec__1(x_1, x_2, x_6, x_11, x_4);
lean::dec(x_6);
lean::dec(x_2);
return x_13;
}
}
obj* l_String_anyAux___main___at_Substring_contains___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; uint8 x_6; obj* x_7; 
x_5 = lean::unbox_uint32(x_0);
x_6 = l_String_anyAux___main___at_Substring_contains___spec__1(x_5, x_1, x_2, x_3, x_4);
x_7 = lean::box(x_6);
lean::dec(x_1);
lean::dec(x_2);
return x_7;
}
}
obj* l_Substring_contains___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_Substring_contains(x_0, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Substring_takeWhileAux___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = lean::nat_dec_eq(x_4, x_1);
if (x_7 == 0)
{
uint32 x_8; obj* x_9; obj* x_11; uint8 x_12; 
x_8 = lean::string_utf8_get(x_0, x_4);
x_9 = lean::box_uint32(x_8);
lean::inc(x_2);
x_11 = lean::apply_1(x_2, x_9);
x_12 = lean::unbox(x_11);
if (x_12 == 0)
{
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
else
{
obj* x_15; obj* x_16; obj* x_18; 
x_15 = lean::mk_nat_obj(1ul);
x_16 = lean::nat_sub(x_3, x_15);
lean::dec(x_3);
x_18 = lean::string_utf8_next(x_0, x_4);
lean::dec(x_4);
x_3 = x_16;
x_4 = x_18;
goto _start;
}
}
else
{
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
else
{
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
}
obj* l_Substring_takeWhileAux___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Substring_takeWhileAux___main(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_Substring_takeWhileAux(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Substring_takeWhileAux___main(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Substring_takeWhileAux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Substring_takeWhileAux(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_Substring_takeWhile___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_14; obj* x_16; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_6 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_8 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_0);
 x_8 = lean::box(0);
}
x_9 = lean::string_utf8_byte_size(x_2);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_9, x_10);
lean::dec(x_9);
lean::inc(x_4);
x_14 = l_Substring_takeWhileAux___main(x_2, x_6, x_1, x_11, x_4);
lean::dec(x_6);
if (lean::is_scalar(x_8)) {
 x_16 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_16 = x_8;
}
lean::cnstr_set(x_16, 0, x_2);
lean::cnstr_set(x_16, 1, x_4);
lean::cnstr_set(x_16, 2, x_14);
return x_16;
}
}
obj* l_Substring_takeWhile(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_14; obj* x_16; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_6 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_8 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_0);
 x_8 = lean::box(0);
}
x_9 = lean::string_utf8_byte_size(x_2);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_9, x_10);
lean::dec(x_9);
lean::inc(x_4);
x_14 = l_Substring_takeWhileAux___main(x_2, x_6, x_1, x_11, x_4);
lean::dec(x_6);
if (lean::is_scalar(x_8)) {
 x_16 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_16 = x_8;
}
lean::cnstr_set(x_16, 0, x_2);
lean::cnstr_set(x_16, 1, x_4);
lean::cnstr_set(x_16, 2, x_14);
return x_16;
}
}
obj* l_Substring_dropWhile___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_6 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_8 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_0);
 x_8 = lean::box(0);
}
x_9 = lean::string_utf8_byte_size(x_2);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_9, x_10);
lean::dec(x_9);
x_13 = l_Substring_takeWhileAux___main(x_2, x_6, x_1, x_11, x_4);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_2);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set(x_14, 2, x_6);
return x_14;
}
}
obj* l_Substring_dropWhile(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_6 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_8 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_0);
 x_8 = lean::box(0);
}
x_9 = lean::string_utf8_byte_size(x_2);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_9, x_10);
lean::dec(x_9);
x_13 = l_Substring_takeWhileAux___main(x_2, x_6, x_1, x_11, x_4);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_2);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set(x_14, 2, x_6);
return x_14;
}
}
obj* l_Substring_takeRightWhileAux___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = lean::nat_dec_eq(x_4, x_1);
if (x_7 == 0)
{
obj* x_8; uint32 x_9; obj* x_10; obj* x_12; uint8 x_13; 
x_8 = lean::string_utf8_prev(x_0, x_4);
x_9 = lean::string_utf8_get(x_0, x_8);
x_10 = lean::box_uint32(x_9);
lean::inc(x_2);
x_12 = lean::apply_1(x_2, x_10);
x_13 = lean::unbox(x_12);
if (x_13 == 0)
{
lean::dec(x_8);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
else
{
obj* x_18; obj* x_19; 
lean::dec(x_4);
x_18 = lean::mk_nat_obj(1ul);
x_19 = lean::nat_sub(x_3, x_18);
lean::dec(x_3);
x_3 = x_19;
x_4 = x_8;
goto _start;
}
}
else
{
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
else
{
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::inc(x_1);
return x_1;
}
}
}
obj* l_Substring_takeRightWhileAux___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Substring_takeRightWhileAux___main(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_Substring_takeRightWhileAux(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Substring_takeRightWhileAux___main(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Substring_takeRightWhileAux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Substring_takeRightWhileAux(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_Substring_takeRightWhile___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_14; obj* x_16; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_6 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_8 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_0);
 x_8 = lean::box(0);
}
x_9 = lean::string_utf8_byte_size(x_2);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_9, x_10);
lean::dec(x_9);
lean::inc(x_6);
x_14 = l_Substring_takeRightWhileAux___main(x_2, x_4, x_1, x_11, x_6);
lean::dec(x_4);
if (lean::is_scalar(x_8)) {
 x_16 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_16 = x_8;
}
lean::cnstr_set(x_16, 0, x_2);
lean::cnstr_set(x_16, 1, x_14);
lean::cnstr_set(x_16, 2, x_6);
return x_16;
}
}
obj* l_Substring_takeRightWhile(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_14; obj* x_16; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_6 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_8 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_0);
 x_8 = lean::box(0);
}
x_9 = lean::string_utf8_byte_size(x_2);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_9, x_10);
lean::dec(x_9);
lean::inc(x_6);
x_14 = l_Substring_takeRightWhileAux___main(x_2, x_4, x_1, x_11, x_6);
lean::dec(x_4);
if (lean::is_scalar(x_8)) {
 x_16 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_16 = x_8;
}
lean::cnstr_set(x_16, 0, x_2);
lean::cnstr_set(x_16, 1, x_14);
lean::cnstr_set(x_16, 2, x_6);
return x_16;
}
}
obj* l_Substring_dropRightWhile___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_6 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_8 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_0);
 x_8 = lean::box(0);
}
x_9 = lean::string_utf8_byte_size(x_2);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_9, x_10);
lean::dec(x_9);
x_13 = l_Substring_takeRightWhileAux___main(x_2, x_4, x_1, x_11, x_6);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_2);
lean::cnstr_set(x_14, 1, x_4);
lean::cnstr_set(x_14, 2, x_13);
return x_14;
}
}
obj* l_Substring_dropRightWhile(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_6 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_8 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_0);
 x_8 = lean::box(0);
}
x_9 = lean::string_utf8_byte_size(x_2);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_9, x_10);
lean::dec(x_9);
x_13 = l_Substring_takeRightWhileAux___main(x_2, x_4, x_1, x_11, x_6);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_2);
lean::cnstr_set(x_14, 1, x_4);
lean::cnstr_set(x_14, 2, x_13);
return x_14;
}
}
obj* l_Substring_takeWhileAux___main___at_Substring_trimLeft___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = lean::nat_dec_eq(x_3, x_1);
if (x_6 == 0)
{
uint32 x_7; uint8 x_8; 
x_7 = lean::string_utf8_get(x_0, x_3);
x_8 = l_Char_isWhitespace(x_7);
if (x_8 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_10; obj* x_11; obj* x_13; 
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_sub(x_2, x_10);
lean::dec(x_2);
x_13 = lean::string_utf8_next(x_0, x_3);
lean::dec(x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
else
{
lean::dec(x_2);
return x_3;
}
}
else
{
lean::dec(x_2);
return x_3;
}
}
}
obj* l_Substring_trimLeft(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; 
x_1 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_7 = x_0;
} else {
 lean::inc(x_1);
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_0);
 x_7 = lean::box(0);
}
x_8 = lean::string_utf8_byte_size(x_1);
x_9 = lean::mk_nat_obj(1ul);
x_10 = lean::nat_add(x_8, x_9);
lean::dec(x_8);
x_12 = l_Substring_takeWhileAux___main___at_Substring_trimLeft___spec__1(x_1, x_5, x_10, x_3);
if (lean::is_scalar(x_7)) {
 x_13 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_13 = x_7;
}
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_12);
lean::cnstr_set(x_13, 2, x_5);
return x_13;
}
}
obj* l_Substring_takeWhileAux___main___at_Substring_trimLeft___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Substring_takeWhileAux___main___at_Substring_trimLeft___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Substring_takeRightWhileAux___main___at_Substring_trimRight___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = lean::nat_dec_eq(x_3, x_1);
if (x_6 == 0)
{
obj* x_7; uint32 x_8; uint8 x_9; 
x_7 = lean::string_utf8_prev(x_0, x_3);
x_8 = lean::string_utf8_get(x_0, x_7);
x_9 = l_Char_isWhitespace(x_8);
if (x_9 == 0)
{
lean::dec(x_7);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_13; obj* x_14; 
lean::dec(x_3);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_sub(x_2, x_13);
lean::dec(x_2);
x_2 = x_14;
x_3 = x_7;
goto _start;
}
}
else
{
lean::dec(x_2);
return x_3;
}
}
else
{
lean::dec(x_3);
lean::dec(x_2);
lean::inc(x_1);
return x_1;
}
}
}
obj* l_Substring_trimRight(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; 
x_1 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_7 = x_0;
} else {
 lean::inc(x_1);
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_0);
 x_7 = lean::box(0);
}
x_8 = lean::string_utf8_byte_size(x_1);
x_9 = lean::mk_nat_obj(1ul);
x_10 = lean::nat_add(x_8, x_9);
lean::dec(x_8);
x_12 = l_Substring_takeRightWhileAux___main___at_Substring_trimRight___spec__1(x_1, x_3, x_10, x_5);
if (lean::is_scalar(x_7)) {
 x_13 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_13 = x_7;
}
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_3);
lean::cnstr_set(x_13, 2, x_12);
return x_13;
}
}
obj* l_Substring_takeRightWhileAux___main___at_Substring_trimRight___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Substring_takeRightWhileAux___main___at_Substring_trimRight___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Substring_takeWhileAux___main___at_Substring_trim___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = lean::nat_dec_eq(x_3, x_1);
if (x_6 == 0)
{
uint32 x_7; uint8 x_8; 
x_7 = lean::string_utf8_get(x_0, x_3);
x_8 = l_Char_isWhitespace(x_7);
if (x_8 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_10; obj* x_11; obj* x_13; 
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_sub(x_2, x_10);
lean::dec(x_2);
x_13 = lean::string_utf8_next(x_0, x_3);
lean::dec(x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
else
{
lean::dec(x_2);
return x_3;
}
}
else
{
lean::dec(x_2);
return x_3;
}
}
}
obj* l_Substring_takeRightWhileAux___main___at_Substring_trim___main___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = lean::nat_dec_eq(x_3, x_1);
if (x_6 == 0)
{
obj* x_7; uint32 x_8; uint8 x_9; 
x_7 = lean::string_utf8_prev(x_0, x_3);
x_8 = lean::string_utf8_get(x_0, x_7);
x_9 = l_Char_isWhitespace(x_8);
if (x_9 == 0)
{
lean::dec(x_7);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_13; obj* x_14; 
lean::dec(x_3);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_sub(x_2, x_13);
lean::dec(x_2);
x_2 = x_14;
x_3 = x_7;
goto _start;
}
}
else
{
lean::dec(x_2);
return x_3;
}
}
else
{
lean::dec(x_3);
lean::dec(x_2);
lean::inc(x_1);
return x_1;
}
}
}
obj* l_Substring_trim___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; 
x_1 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_7 = x_0;
} else {
 lean::inc(x_1);
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_0);
 x_7 = lean::box(0);
}
x_8 = lean::string_utf8_byte_size(x_1);
x_9 = lean::mk_nat_obj(1ul);
x_10 = lean::nat_add(x_8, x_9);
lean::dec(x_8);
lean::inc(x_10);
x_13 = l_Substring_takeWhileAux___main___at_Substring_trim___main___spec__1(x_1, x_5, x_10, x_3);
x_14 = l_Substring_takeRightWhileAux___main___at_Substring_trim___main___spec__2(x_1, x_13, x_10, x_5);
if (lean::is_scalar(x_7)) {
 x_15 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_15 = x_7;
}
lean::cnstr_set(x_15, 0, x_1);
lean::cnstr_set(x_15, 1, x_13);
lean::cnstr_set(x_15, 2, x_14);
return x_15;
}
}
obj* l_Substring_takeWhileAux___main___at_Substring_trim___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Substring_takeWhileAux___main___at_Substring_trim___main___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Substring_takeRightWhileAux___main___at_Substring_trim___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Substring_takeRightWhileAux___main___at_Substring_trim___main___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Substring_takeWhileAux___main___at_Substring_trim___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = lean::nat_dec_eq(x_3, x_1);
if (x_6 == 0)
{
uint32 x_7; uint8 x_8; 
x_7 = lean::string_utf8_get(x_0, x_3);
x_8 = l_Char_isWhitespace(x_7);
if (x_8 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_10; obj* x_11; obj* x_13; 
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_sub(x_2, x_10);
lean::dec(x_2);
x_13 = lean::string_utf8_next(x_0, x_3);
lean::dec(x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
else
{
lean::dec(x_2);
return x_3;
}
}
else
{
lean::dec(x_2);
return x_3;
}
}
}
obj* l_Substring_takeRightWhileAux___main___at_Substring_trim___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = lean::nat_dec_eq(x_3, x_1);
if (x_6 == 0)
{
obj* x_7; uint32 x_8; uint8 x_9; 
x_7 = lean::string_utf8_prev(x_0, x_3);
x_8 = lean::string_utf8_get(x_0, x_7);
x_9 = l_Char_isWhitespace(x_8);
if (x_9 == 0)
{
lean::dec(x_7);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_13; obj* x_14; 
lean::dec(x_3);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_sub(x_2, x_13);
lean::dec(x_2);
x_2 = x_14;
x_3 = x_7;
goto _start;
}
}
else
{
lean::dec(x_2);
return x_3;
}
}
else
{
lean::dec(x_3);
lean::dec(x_2);
lean::inc(x_1);
return x_1;
}
}
}
obj* l_Substring_trim(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; 
x_1 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_7 = x_0;
} else {
 lean::inc(x_1);
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_0);
 x_7 = lean::box(0);
}
x_8 = lean::string_utf8_byte_size(x_1);
x_9 = lean::mk_nat_obj(1ul);
x_10 = lean::nat_add(x_8, x_9);
lean::dec(x_8);
lean::inc(x_10);
x_13 = l_Substring_takeWhileAux___main___at_Substring_trim___spec__1(x_1, x_5, x_10, x_3);
x_14 = l_Substring_takeRightWhileAux___main___at_Substring_trim___spec__2(x_1, x_13, x_10, x_5);
if (lean::is_scalar(x_7)) {
 x_15 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_15 = x_7;
}
lean::cnstr_set(x_15, 0, x_1);
lean::cnstr_set(x_15, 1, x_13);
lean::cnstr_set(x_15, 2, x_14);
return x_15;
}
}
obj* l_Substring_takeWhileAux___main___at_Substring_trim___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Substring_takeWhileAux___main___at_Substring_trim___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Substring_takeRightWhileAux___main___at_Substring_trim___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Substring_takeRightWhileAux___main___at_Substring_trim___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_String_foldlAux___main___at_Substring_toNat___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = lean::nat_dec_eq(x_3, x_1);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_11; uint32 x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_21; 
x_8 = lean::mk_nat_obj(1ul);
x_9 = lean::nat_sub(x_2, x_8);
lean::dec(x_2);
x_11 = lean::string_utf8_next(x_0, x_3);
x_12 = lean::string_utf8_get(x_0, x_3);
lean::dec(x_3);
x_14 = lean::mk_nat_obj(10ul);
x_15 = lean::nat_mul(x_4, x_14);
lean::dec(x_4);
x_17 = lean::uint32_to_nat(x_12);
x_18 = l_String_foldlAux___main___at_String_toNat___spec__1___closed__1;
x_19 = lean::nat_sub(x_17, x_18);
lean::dec(x_17);
x_21 = lean::nat_add(x_15, x_19);
lean::dec(x_19);
lean::dec(x_15);
x_2 = x_9;
x_3 = x_11;
x_4 = x_21;
goto _start;
}
else
{
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
else
{
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
}
obj* l_Substring_toNat(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::string_utf8_byte_size(x_1);
x_9 = lean::mk_nat_obj(1ul);
x_10 = lean::nat_add(x_8, x_9);
lean::dec(x_8);
x_12 = lean::mk_nat_obj(0ul);
x_13 = l_String_foldlAux___main___at_Substring_toNat___spec__1(x_1, x_5, x_10, x_3, x_12);
lean::dec(x_5);
lean::dec(x_1);
return x_13;
}
}
obj* l_String_foldlAux___main___at_Substring_toNat___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_String_foldlAux___main___at_Substring_toNat___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
uint8 l_String_anyAux___main___at_Substring_isNat___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = lean::nat_dec_eq(x_3, x_1);
if (x_6 == 0)
{
uint32 x_7; uint8 x_8; 
x_7 = lean::string_utf8_get(x_0, x_3);
x_8 = l_Char_isDigit(x_7);
if (x_8 == 0)
{
uint8 x_11; 
lean::dec(x_3);
lean::dec(x_2);
x_11 = 1;
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; 
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_sub(x_2, x_12);
lean::dec(x_2);
x_15 = lean::string_utf8_next(x_0, x_3);
lean::dec(x_3);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
else
{
uint8 x_20; 
lean::dec(x_3);
lean::dec(x_2);
x_20 = 0;
return x_20;
}
}
else
{
uint8 x_23; 
lean::dec(x_3);
lean::dec(x_2);
x_23 = 0;
return x_23;
}
}
}
uint8 l_Substring_isNat(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; uint8 x_12; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::string_utf8_byte_size(x_1);
x_9 = lean::mk_nat_obj(1ul);
x_10 = lean::nat_add(x_8, x_9);
lean::dec(x_8);
x_12 = l_String_anyAux___main___at_Substring_isNat___spec__1(x_1, x_5, x_10, x_3);
lean::dec(x_5);
lean::dec(x_1);
if (x_12 == 0)
{
uint8 x_15; 
x_15 = 1;
return x_15;
}
else
{
uint8 x_16; 
x_16 = 0;
return x_16;
}
}
}
obj* l_String_anyAux___main___at_Substring_isNat___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_String_anyAux___main___at_Substring_isNat___spec__1(x_0, x_1, x_2, x_3);
x_5 = lean::box(x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_Substring_isNat___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Substring_isNat(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* _init_l_String_drop___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::mk_string("");
x_1 = lean::string_utf8_byte_size(x_0);
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::string_utf8_extract(x_0, x_2, x_1);
lean::dec(x_1);
lean::dec(x_0);
return x_3;
}
}
obj* l_String_drop(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; uint8 x_5; 
x_2 = lean::string_utf8_byte_size(x_0);
x_3 = lean::mk_nat_obj(0ul);
x_4 = lean::nat_add(x_3, x_1);
x_5 = lean::nat_dec_le(x_2, x_4);
if (x_5 == 0)
{
obj* x_6; 
x_6 = lean::string_utf8_extract(x_0, x_4, x_2);
lean::dec(x_2);
lean::dec(x_4);
return x_6;
}
else
{
obj* x_11; 
lean::dec(x_4);
lean::dec(x_2);
x_11 = l_String_drop___closed__1;
return x_11;
}
}
}
obj* l_String_drop___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_drop(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_String_dropRight(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::string_utf8_byte_size(x_0);
x_3 = lean::nat_sub(x_2, x_1);
x_4 = lean::nat_dec_le(x_3, x_2);
lean::dec(x_2);
if (x_4 == 0)
{
obj* x_6; obj* x_7; 
x_6 = lean::mk_nat_obj(0ul);
x_7 = lean::string_utf8_extract(x_0, x_6, x_3);
lean::dec(x_3);
return x_7;
}
else
{
obj* x_10; 
lean::dec(x_3);
x_10 = l_String_drop___closed__1;
return x_10;
}
}
}
obj* l_String_dropRight___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_dropRight(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_String_take(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; uint8 x_5; 
x_2 = lean::string_utf8_byte_size(x_0);
x_3 = lean::mk_nat_obj(0ul);
x_4 = lean::nat_add(x_3, x_1);
x_5 = lean::nat_dec_le(x_2, x_4);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_2);
x_7 = lean::string_utf8_extract(x_0, x_3, x_4);
lean::dec(x_4);
return x_7;
}
else
{
obj* x_10; 
lean::dec(x_4);
x_10 = lean::string_utf8_extract(x_0, x_3, x_2);
lean::dec(x_2);
return x_10;
}
}
}
obj* l_String_take___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_take(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_String_takeRight(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; uint8 x_5; 
x_2 = lean::string_utf8_byte_size(x_0);
x_3 = lean::nat_sub(x_2, x_1);
x_4 = lean::mk_nat_obj(0ul);
x_5 = lean::nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
obj* x_6; 
x_6 = lean::string_utf8_extract(x_0, x_3, x_2);
lean::dec(x_2);
lean::dec(x_3);
return x_6;
}
else
{
obj* x_10; 
lean::dec(x_3);
x_10 = lean::string_utf8_extract(x_0, x_4, x_2);
lean::dec(x_2);
return x_10;
}
}
}
obj* l_String_takeRight___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_takeRight(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_String_takeWhile(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_8; 
x_2 = lean::string_utf8_byte_size(x_0);
x_3 = lean::mk_nat_obj(1ul);
x_4 = lean::nat_add(x_2, x_3);
x_5 = lean::mk_nat_obj(0ul);
x_6 = l_Substring_takeWhileAux___main(x_0, x_2, x_1, x_4, x_5);
lean::dec(x_2);
x_8 = lean::string_utf8_extract(x_0, x_5, x_6);
lean::dec(x_6);
return x_8;
}
}
obj* l_String_takeWhile___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_takeWhile(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_String_dropWhile(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::string_utf8_byte_size(x_0);
x_3 = lean::mk_nat_obj(1ul);
x_4 = lean::nat_add(x_2, x_3);
x_5 = lean::mk_nat_obj(0ul);
x_6 = l_Substring_takeWhileAux___main(x_0, x_2, x_1, x_4, x_5);
x_7 = lean::string_utf8_extract(x_0, x_6, x_2);
lean::dec(x_2);
lean::dec(x_6);
return x_7;
}
}
obj* l_String_dropWhile___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_dropWhile(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Substring_takeRightWhileAux___main___at_String_trimRight___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = lean::nat_dec_eq(x_3, x_1);
if (x_6 == 0)
{
obj* x_7; uint32 x_8; uint8 x_9; 
x_7 = lean::string_utf8_prev(x_0, x_3);
x_8 = lean::string_utf8_get(x_0, x_7);
x_9 = l_Char_isWhitespace(x_8);
if (x_9 == 0)
{
lean::dec(x_7);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_13; obj* x_14; 
lean::dec(x_3);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_sub(x_2, x_13);
lean::dec(x_2);
x_2 = x_14;
x_3 = x_7;
goto _start;
}
}
else
{
lean::dec(x_2);
return x_3;
}
}
else
{
lean::dec(x_3);
lean::dec(x_2);
lean::inc(x_1);
return x_1;
}
}
}
obj* l_String_trimRight(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::string_utf8_byte_size(x_0);
x_2 = lean::mk_nat_obj(1ul);
x_3 = lean::nat_add(x_1, x_2);
x_4 = lean::mk_nat_obj(0ul);
x_5 = l_Substring_takeRightWhileAux___main___at_String_trimRight___spec__1(x_0, x_4, x_3, x_1);
x_6 = lean::string_utf8_extract(x_0, x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l_Substring_takeRightWhileAux___main___at_String_trimRight___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Substring_takeRightWhileAux___main___at_String_trimRight___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_String_trimRight___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_trimRight(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Substring_takeWhileAux___main___at_String_trimLeft___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = lean::nat_dec_eq(x_3, x_1);
if (x_6 == 0)
{
uint32 x_7; uint8 x_8; 
x_7 = lean::string_utf8_get(x_0, x_3);
x_8 = l_Char_isWhitespace(x_7);
if (x_8 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_10; obj* x_11; obj* x_13; 
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_sub(x_2, x_10);
lean::dec(x_2);
x_13 = lean::string_utf8_next(x_0, x_3);
lean::dec(x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
else
{
lean::dec(x_2);
return x_3;
}
}
else
{
lean::dec(x_2);
return x_3;
}
}
}
obj* l_String_trimLeft(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::string_utf8_byte_size(x_0);
x_2 = lean::mk_nat_obj(1ul);
x_3 = lean::nat_add(x_1, x_2);
x_4 = lean::mk_nat_obj(0ul);
x_5 = l_Substring_takeWhileAux___main___at_String_trimLeft___spec__1(x_0, x_1, x_3, x_4);
x_6 = lean::string_utf8_extract(x_0, x_5, x_1);
lean::dec(x_1);
lean::dec(x_5);
return x_6;
}
}
obj* l_Substring_takeWhileAux___main___at_String_trimLeft___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Substring_takeWhileAux___main___at_String_trimLeft___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_String_trimLeft___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_trimLeft(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Substring_takeWhileAux___main___at_String_trim___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = lean::nat_dec_eq(x_3, x_1);
if (x_6 == 0)
{
uint32 x_7; uint8 x_8; 
x_7 = lean::string_utf8_get(x_0, x_3);
x_8 = l_Char_isWhitespace(x_7);
if (x_8 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_10; obj* x_11; obj* x_13; 
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_sub(x_2, x_10);
lean::dec(x_2);
x_13 = lean::string_utf8_next(x_0, x_3);
lean::dec(x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
else
{
lean::dec(x_2);
return x_3;
}
}
else
{
lean::dec(x_2);
return x_3;
}
}
}
obj* l_Substring_takeRightWhileAux___main___at_String_trim___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = lean::nat_dec_eq(x_3, x_1);
if (x_6 == 0)
{
obj* x_7; uint32 x_8; uint8 x_9; 
x_7 = lean::string_utf8_prev(x_0, x_3);
x_8 = lean::string_utf8_get(x_0, x_7);
x_9 = l_Char_isWhitespace(x_8);
if (x_9 == 0)
{
lean::dec(x_7);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_13; obj* x_14; 
lean::dec(x_3);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_sub(x_2, x_13);
lean::dec(x_2);
x_2 = x_14;
x_3 = x_7;
goto _start;
}
}
else
{
lean::dec(x_2);
return x_3;
}
}
else
{
lean::dec(x_3);
lean::dec(x_2);
lean::inc(x_1);
return x_1;
}
}
}
obj* l_String_trim(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
x_1 = lean::string_utf8_byte_size(x_0);
x_2 = lean::mk_nat_obj(1ul);
x_3 = lean::nat_add(x_1, x_2);
x_4 = lean::mk_nat_obj(0ul);
lean::inc(x_3);
x_6 = l_Substring_takeWhileAux___main___at_String_trim___spec__1(x_0, x_1, x_3, x_4);
x_7 = l_Substring_takeRightWhileAux___main___at_String_trim___spec__2(x_0, x_6, x_3, x_1);
x_8 = lean::string_utf8_extract(x_0, x_6, x_7);
lean::dec(x_7);
lean::dec(x_6);
return x_8;
}
}
obj* l_Substring_takeWhileAux___main___at_String_trim___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Substring_takeWhileAux___main___at_String_trim___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Substring_takeRightWhileAux___main___at_String_trim___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Substring_takeRightWhileAux___main___at_String_trim___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_String_trim___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_trim(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Char_toString(uint32 x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = lean::string_push(x_1, x_0);
return x_2;
}
}
obj* l_Char_toString___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_Char_toString(x_1);
return x_2;
}
}
obj* initialize_init_data_list_basic(obj*);
obj* initialize_init_data_char_basic(obj*);
obj* initialize_init_data_option_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_string_basic(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_list_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_char_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_option_basic(w);
 l_String_DecidableEq = _init_l_String_DecidableEq();
lean::mark_persistent(l_String_DecidableEq);
 l_String_HasLess = _init_l_String_HasLess();
lean::mark_persistent(l_String_HasLess);
 l_String_splitAux___main___closed__1 = _init_l_String_splitAux___main___closed__1();
lean::mark_persistent(l_String_splitAux___main___closed__1);
 l_String_Inhabited = _init_l_String_Inhabited();
lean::mark_persistent(l_String_Inhabited);
 l_String_HasSizeof = _init_l_String_HasSizeof();
lean::mark_persistent(l_String_HasSizeof);
 l_String_HasAppend = _init_l_String_HasAppend();
lean::mark_persistent(l_String_HasAppend);
 l_String_lineColumn___closed__1 = _init_l_String_lineColumn___closed__1();
lean::mark_persistent(l_String_lineColumn___closed__1);
 l_String_foldlAux___main___at_String_toNat___spec__1___closed__1 = _init_l_String_foldlAux___main___at_String_toNat___spec__1___closed__1();
lean::mark_persistent(l_String_foldlAux___main___at_String_toNat___spec__1___closed__1);
 l_Substring_drop___main___closed__1 = _init_l_Substring_drop___main___closed__1();
lean::mark_persistent(l_Substring_drop___main___closed__1);
 l_Substring_extract___main___closed__1 = _init_l_Substring_extract___main___closed__1();
lean::mark_persistent(l_Substring_extract___main___closed__1);
 l_String_drop___closed__1 = _init_l_String_drop___closed__1();
lean::mark_persistent(l_String_drop___closed__1);
return w;
}
