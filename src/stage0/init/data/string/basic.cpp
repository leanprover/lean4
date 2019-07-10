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
obj* l_String_posOfAux___main(obj*, uint32, obj*, obj*);
obj* l_String_prev___boxed(obj*, obj*);
obj* l_Substring_dropRight___boxed(obj*, obj*);
obj* l_String_mkIterator(obj*);
obj* l___private_init_data_string_basic_4__utf8SetAux(uint32, obj*, obj*, obj*);
obj* l_String_posOf___boxed(obj*, obj*);
obj* l_Substring_takeWhileAux(obj*, obj*, obj*, obj*);
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
obj* l_String_foldlAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_String_front___boxed(obj*);
obj* l_String_Iterator_prevn(obj*, obj*);
obj* l_String_Iterator_extract___main___boxed(obj*, obj*);
obj* l_String_join___boxed(obj*);
obj* l_String_takeRight(obj*, obj*);
obj* l_String_Iterator_remainingToString___main(obj*);
obj* l_Substring_extract___main(obj*, obj*, obj*);
obj* l_String_Iterator_setCurr___main___boxed(obj*, obj*);
obj* l_String_mapAux___main(obj*, obj*, obj*);
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
obj* l_Substring_next___main___boxed(obj*, obj*);
uint8 l_String_isEmpty(obj*);
obj* l_String_trim___boxed(obj*);
obj* l_String_foldrAux(obj*);
obj* l_String_intercalate(obj*, obj*);
obj* l___private_init_data_string_basic_8__lineColumnAux___boxed(obj*, obj*, obj*);
obj* l_String_lineColumn(obj*, obj*);
obj* l_Nat_repeatAux___main___at_String_pushn___spec__1(uint32, obj*, obj*);
obj* l_Substring_dropRight___main(obj*, obj*);
obj* l_Substring_prev(obj*, obj*);
obj* l_String_Iterator_hasPrev___boxed(obj*);
obj* l_Substring_isNat___boxed(obj*);
obj* l_String_Iterator_extract___main(obj*, obj*);
obj* l_Substring_any___boxed(obj*, obj*);
obj* l_String_Iterator_pos(obj*);
obj* l_Substring_takeWhile___main(obj*, obj*);
obj* l_String_drop___boxed(obj*, obj*);
obj* l_String_Iterator_toString___main___boxed(obj*);
obj* l_Substring_get___boxed(obj*, obj*);
uint8 l_String_Iterator_hasPrev___main(obj*);
obj* l_Char_toString___boxed(obj*);
obj* l_String_push___boxed(obj*, obj*);
obj* l_Substring_takeRightWhileAux___main___boxed(obj*, obj*, obj*, obj*);
uint8 l_String_isPrefixOf(obj*, obj*);
obj* l_String_isPrefixOfAux___main___boxed(obj*, obj*, obj*);
obj* l_String_foldrAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_String_dropRight___boxed(obj*, obj*);
obj* l___private_init_data_string_basic_4__utf8SetAux___main(uint32, obj*, obj*, obj*);
obj* l___private_init_data_string_basic_7__utf8ExtractAux_u2081(obj*, obj*, obj*, obj*);
obj* l___private_init_data_string_basic_6__utf8ExtractAux_u2082(obj*, obj*, obj*);
obj* l_String_split___boxed(obj*, obj*);
obj* l_Substring_dropWhile(obj*, obj*);
obj* l_List_reverse___rarg(obj*);
obj* l_String_Iterator_isPrefixOfRemaining___boxed(obj*, obj*);
obj* l_String_Iterator_remainingBytes___main(obj*);
obj* l_String_Iterator_pos___boxed(obj*);
uint8 l_String_anyAux___main___at_String_isNat___spec__1(obj*, obj*, obj*);
obj* l_Substring_takeRightWhileAux___main___at_Substring_trimRight___spec__1(obj*, obj*, obj*);
obj* l_String_foldl___rarg(obj*, obj*, obj*);
obj* l_String_pushn___boxed(obj*, obj*, obj*);
obj* l_String_get___boxed(obj*, obj*);
uint8 l_String_Iterator_hasNext(obj*);
obj* l_String_offsetOfPos(obj*, obj*);
obj* l_String_DecidableEq___closed__1;
obj* l_String_HasAppend;
obj* l_String_HasLess;
obj* l_Substring_contains___boxed(obj*, obj*);
obj* l_Substring_foldl___rarg(obj*, obj*, obj*);
obj* l_String_takeWhile(obj*, obj*);
uint8 l_String_contains(obj*, uint32);
obj* l_String_Iterator_prev___main(obj*);
obj* l_String_dropWhile___boxed(obj*, obj*);
obj* l_Substring_takeWhileAux___main(obj*, obj*, obj*, obj*);
obj* l_Substring_takeRight___main___boxed(obj*, obj*);
obj* l_String_Iterator_forward___main(obj*, obj*);
uint8 l_String_Iterator_isPrefixOfRemaining(obj*, obj*);
obj* l_String_splitAux(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Substring_takeRight(obj*, obj*);
obj* l_Substring_toString(obj*);
uint8 l_String_any(obj*, obj*);
obj* l_Substring_takeRightWhileAux___main___at_Substring_trimRight___spec__1___boxed(obj*, obj*, obj*);
obj* l_String_Inhabited;
obj* l___private_init_data_string_basic_8__lineColumnAux(obj*, obj*, obj*);
obj* l_Substring_next(obj*, obj*);
obj* l___private_init_data_string_basic_8__lineColumnAux___main(obj*, obj*, obj*);
obj* l_Substring_trimRight(obj*);
obj* l_Substring_toIterator___main(obj*);
obj* l_String_anyAux___main___at_Substring_contains___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Substring_extract(obj*, obj*, obj*);
obj* l___private_init_data_string_basic_1__csize(uint32);
obj* l_String_Iterator_prevn___main(obj*, obj*);
obj* l___private_init_data_string_basic_4__utf8SetAux___boxed(obj*, obj*, obj*, obj*);
obj* l_Substring_extract___main___closed__1;
obj* l_Substring_extract___main___boxed(obj*, obj*, obj*);
obj* l_String_back___boxed(obj*);
obj* l_String_foldlAux___main___at_String_toNat___spec__1(obj*, obj*, obj*, obj*);
obj* l_String_Iterator_hasNext___main___boxed(obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_Substring_take___boxed(obj*, obj*);
obj* l_String_takeRight___boxed(obj*, obj*);
obj* l_Substring_drop___main(obj*, obj*);
obj* l_String_Iterator_toString(obj*);
obj* l_Substring_drop(obj*, obj*);
obj* l_String_isPrefixOfAux___boxed(obj*, obj*, obj*);
obj* l___private_init_data_string_basic_6__utf8ExtractAux_u2082___main(obj*, obj*, obj*);
obj* l_Substring_trim___main(obj*);
obj* l_Char_toString(uint32);
obj* l_String_offsetOfPosAux___main(obj*, obj*, obj*, obj*);
obj* l_String_Iterator_next(obj*);
obj* l_Substring_splitAux___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_String_Iterator_hasNext___boxed(obj*);
obj* l_Substring_dropRight___main___boxed(obj*, obj*);
obj* l_String_foldlAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Substring_dropRightWhile___main(obj*, obj*);
obj* l_String_foldl(obj*);
obj* l_Nat_repeatAux___main___at_String_pushn___spec__1___boxed(obj*, obj*, obj*);
obj* l_String_any___boxed(obj*, obj*);
obj* l___private_init_data_string_basic_5__utf8PrevAux(obj*, obj*, obj*);
obj* l_String_contains___boxed(obj*, obj*);
obj* l___private_init_data_string_basic_5__utf8PrevAux___main(obj*, obj*, obj*);
obj* l_Substring_posOf(obj*, uint32);
uint8 l_String_anyAux___main___at_Substring_contains___spec__1(uint32, obj*, obj*, obj*);
obj* l_String_isPrefixOf___boxed(obj*, obj*);
obj* l_String_offsetOfPosAux___main___boxed(obj*, obj*, obj*, obj*);
obj* l_String_offsetOfPosAux(obj*, obj*, obj*, obj*);
obj* l_String_Iterator_next___main(obj*);
obj* l_Substring_takeRightWhileAux___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_data_string_basic_7__utf8ExtractAux_u2081___main(obj*, obj*, obj*, obj*);
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
obj* l_String_anyAux___main___at_String_contains___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_String_mk___boxed(obj*);
obj* l_String_Iterator_prev(obj*);
obj* l_String_foldrAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_String_offsetOfPosAux___boxed(obj*, obj*, obj*, obj*);
obj* l_String_toSubstring(obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_String_str(obj*, uint32);
obj* l_Substring_drop___main___boxed(obj*, obj*);
obj* l_Substring_split(obj*, obj*);
obj* l_String_drop(obj*, obj*);
obj* l_Substring_drop___main___closed__1;
obj* l_Substring_posOf___boxed(obj*, obj*);
obj* l_String_data___boxed(obj*);
obj* l_String_bsize(obj*);
obj* l_String_anyAux___main___at_Substring_all___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_String_Iterator_remainingToString___boxed(obj*);
obj* l_Substring_dropRight(obj*, obj*);
obj* l_String_Iterator_nextn(obj*, obj*);
obj* l_String_foldrAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_String_toNat___boxed(obj*);
obj* l_String_Iterator_curr___main___boxed(obj*);
obj* l_String_Iterator_toString___boxed(obj*);
uint8 l_String_anyAux___main___at_Substring_all___spec__1(obj*, obj*, obj*, obj*);
obj* l_String_foldlAux(obj*);
obj* l_String_set___boxed(obj*, obj*, obj*);
obj* l_String_Iterator_remainingToString___main___boxed(obj*);
obj* l_Substring_front___boxed(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_String_anyAux___boxed(obj*, obj*, obj*, obj*);
obj* l_Substring_takeRight___main(obj*, obj*);
obj* l_Substring_takeRightWhileAux___main(obj*, obj*, obj*, obj*);
obj* l_String_join(obj*);
obj* l_String_Iterator_remainingBytes___main___boxed(obj*);
uint8 l_String_isPrefixOfAux___main(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Substring_foldl(obj*);
obj* l_String_splitAux___main___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_String_append___boxed(obj*, obj*);
obj* l_Substring_takeRightWhile___main(obj*, obj*);
obj* l___private_init_data_string_basic_5__utf8PrevAux___boxed(obj*, obj*, obj*);
obj* l_String_Iterator_nextn___main(obj*, obj*);
obj* l_String_Iterator_pos___main___boxed(obj*);
obj* l_String_isEmpty___boxed(obj*);
obj* l_List_map___main___at_String_intercalate___spec__1(obj*);
obj* l_String_foldl___rarg___boxed(obj*, obj*, obj*);
obj* l_String_toList(obj*);
obj* l_Substring_takeWhileAux___boxed(obj*, obj*, obj*, obj*);
obj* l_String_atEnd___boxed(obj*, obj*);
obj* l_Substring_takeWhile(obj*, obj*);
namespace lean {
uint32 string_utf8_get(obj*, obj*);
}
obj* l_Substring_drop___boxed(obj*, obj*);
obj* l_String_trimRight___boxed(obj*);
obj* l_Substring_drop___main___closed__2;
obj* l_Substring_splitAux(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_String_singleton(uint32);
obj* l___private_init_data_string_basic_8__lineColumnAux___main___boxed(obj*, obj*, obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
uint8 l_UInt32_decEq(uint32, uint32);
obj* l_String_anyAux___main___at_String_all___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Substring_extract___boxed(obj*, obj*, obj*);
obj* l_Substring_splitAux___main(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_String_foldrAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Substring_dropRightWhile(obj*, obj*);
obj* l_Substring_takeWhileAux___main___boxed(obj*, obj*, obj*, obj*);
obj* l_Substring_toIterator(obj*);
uint8 l_Substring_atEnd(obj*, obj*);
obj* l_Substring_next___main(obj*, obj*);
obj* l_Substring_take___main(obj*, obj*);
obj* l_String_HasAppend___closed__1;
uint8 l_Char_isDigit(uint32);
obj* l_String_dropRight(obj*, obj*);
obj* l_Substring_all___boxed(obj*, obj*);
obj* l_Substring_takeWhileAux___main___at_Substring_trimLeft___spec__1(obj*, obj*, obj*);
obj* l_Substring_splitAux___main___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_String_Iterator_forward(obj*, obj*);
obj* l_Substring_atEnd___main___boxed(obj*, obj*);
obj* l_String_Iterator_isPrefixOfRemaining___main___boxed(obj*, obj*);
obj* l_Substring_takeWhileAux___main___at_Substring_trimLeft___spec__1___boxed(obj*, obj*, obj*);
obj* l_String_decLt___boxed(obj*, obj*);
obj* l_String_DecidableEq;
obj* l_String_trim(obj*);
obj* l___private_init_data_string_basic_6__utf8ExtractAux_u2082___boxed(obj*, obj*, obj*);
obj* l_String_foldr___rarg(obj*, obj*, obj*);
obj* l_Substring_toIterator___main___boxed(obj*);
obj* l_Substring_split___boxed(obj*, obj*);
obj* l_String_split(obj*, obj*);
obj* l_String_foldr(obj*);
obj* l_String_posOfAux___boxed(obj*, obj*, obj*, obj*);
obj* l_String_mapAux(obj*, obj*, obj*);
obj* l___private_init_data_string_basic_1__csize___boxed(obj*);
namespace lean {
obj* string_data(obj*);
}
obj* l_String_extract___boxed(obj*, obj*, obj*);
uint8 l_Substring_any(obj*, obj*);
obj* l_Substring_takeRightWhileAux(obj*, obj*, obj*, obj*);
uint8 l_String_isNat(obj*);
obj* l_String_Iterator_pos___main(obj*);
obj* l_Substring_trimLeft(obj*);
uint32 l_String_Iterator_curr(obj*);
obj* l_String_pushn(obj*, uint32, obj*);
obj* l_String_splitAux___main(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_data_string_basic_3__utf8GetAux___boxed(obj*, obj*, obj*);
uint8 l_Char_isWhitespace(uint32);
obj* l_String_Iterator_remainingBytes___boxed(obj*);
obj* l_String_posOfAux(obj*, uint32, obj*, obj*);
uint32 l___private_init_data_string_basic_3__utf8GetAux(obj*, obj*, obj*);
obj* l_Substring_toString___boxed(obj*);
obj* l_String_HasSizeof;
uint32 l_String_front(obj*);
uint8 l_String_anyAux___main___at_String_all___spec__1(obj*, obj*, obj*, obj*);
uint8 l_String_isPrefixOfAux(obj*, obj*, obj*);
obj* l_Substring_get___main___boxed(obj*, obj*);
obj* l_String_anyAux___main___boxed(obj*, obj*, obj*, obj*);
uint32 l___private_init_data_string_basic_3__utf8GetAux___main(obj*, obj*, obj*);
obj* l_Substring_prev___main___boxed(obj*, obj*);
obj* l_List_intercalate___rarg(obj*, obj*);
obj* l___private_init_data_string_basic_2__utf8ByteSizeAux___main(obj*, obj*);
obj* l___private_init_data_string_basic_6__utf8ExtractAux_u2082___main___boxed(obj*, obj*, obj*);
obj* l_Substring_dropWhile___main(obj*, obj*);
uint32 l_Char_utf8Size(uint32);
obj* l_String_Iterator_toEnd___main(obj*);
obj* l_Substring_toNat(obj*);
namespace lean {
obj* string_utf8_next(obj*, obj*);
}
obj* l_String_splitAux___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_data_string_basic_3__utf8GetAux___main___boxed(obj*, obj*, obj*);
obj* l_String_Iterator_extract___boxed(obj*, obj*);
uint8 l_Substring_atEnd___main(obj*, obj*);
obj* l___private_init_data_string_basic_7__utf8ExtractAux_u2081___main___boxed(obj*, obj*, obj*, obj*);
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
obj* l_String_Iterator_curr___boxed(obj*);
obj* l_Substring_toString___main___boxed(obj*);
obj* l_String_dropWhile(obj*, obj*);
namespace lean {
obj* string_utf8_byte_size(obj*);
}
obj* l_String_foldr___rarg___boxed(obj*, obj*, obj*);
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
uint8 l_String_Iterator_hasPrev(obj*);
obj* l_List_foldl___main___at_String_join___spec__1(obj*, obj*);
obj* l_Substring_toIterator___boxed(obj*);
obj* l_String_HasSizeof___closed__1;
uint8 l_Substring_isNat(obj*);
obj* l_String_Iterator_setCurr(obj*, uint32);
obj* l_String_foldlAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Substring_toString___main(obj*);
obj* l_String_Iterator_toEnd(obj*);
obj* l_String_bsize___boxed(obj*);
namespace lean {
obj* nat_mul(obj*, obj*);
}
uint8 l_String_Iterator_isPrefixOfRemaining___main(obj*, obj*);
obj* l_String_Iterator_setCurr___main(obj*, uint32);
obj* l___private_init_data_string_basic_7__utf8ExtractAux_u2081___boxed(obj*, obj*, obj*, obj*);
obj* l_String_posOfAux___main___boxed(obj*, obj*, obj*, obj*);
uint8 l_Substring_contains(obj*, uint32);
obj* l_String_str___boxed(obj*, obj*);
obj* l_String_takeWhile___boxed(obj*, obj*);
obj* l_String_foldlAux___main___at_String_toNat___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_String_next___boxed(obj*, obj*);
obj* l_String_trimLeft(obj*);
obj* l___private_init_data_string_basic_2__utf8ByteSizeAux(obj*, obj*);
uint8 l_String_anyAux___main___at_String_contains___spec__1(uint32, obj*, obj*, obj*);
obj* l_String_length___boxed(obj*);
obj* l_String_anyAux___main___at_String_isNat___spec__1___boxed(obj*, obj*, obj*);
uint8 l_String_anyAux(obj*, obj*, obj*, obj*);
obj* l_Substring_prev___boxed(obj*, obj*);
obj* l_Substring_take(obj*, obj*);
uint8 l_String_anyAux___main(obj*, obj*, obj*, obj*);
obj* l_Substring_foldr___rarg(obj*, obj*, obj*);
obj* l_String_lineColumn___closed__1;
obj* l_String_trimRight(obj*);
obj* l_Substring_takeRight___boxed(obj*, obj*);
uint32 l_String_back(obj*);
obj* l_String_Iterator_remainingBytes(obj*);
obj* l_String_foldlAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_String_Iterator_remainingToString(obj*);
obj* l_String_splitAux___main___closed__1;
namespace lean {
obj* string_utf8_set(obj*, obj*, uint32);
}
namespace lean {
obj* string_length(obj*);
}
obj* l_String_lineColumn___boxed(obj*, obj*);
obj* l_String_mk___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::string_mk(x_1);
return x_2;
}
}
obj* l_String_data___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::string_data(x_1);
return x_2;
}
}
obj* l_String_decEq___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::string_dec_eq(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* _init_l_String_DecidableEq___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_String_decEq___boxed), 2, 0);
return x_1;
}
}
obj* _init_l_String_DecidableEq() {
_start:
{
obj* x_1; 
x_1 = l_String_DecidableEq___closed__1;
return x_1;
}
}
obj* l_List_asString(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::string_mk(x_1);
return x_2;
}
}
obj* _init_l_String_HasLess() {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* l_String_decLt___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::string_dec_lt(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_String_length___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::string_length(x_1);
return x_2;
}
}
obj* l_String_push___boxed(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = lean::string_push(x_1, x_3);
return x_4;
}
}
obj* l_String_append___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::string_append(x_1, x_2);
return x_3;
}
}
obj* l_String_toList(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::string_data(x_1);
return x_2;
}
}
obj* l___private_init_data_string_basic_1__csize(uint32 x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = l_Char_utf8Size(x_1);
x_3 = lean::uint32_to_nat(x_2);
return x_3;
}
}
obj* l___private_init_data_string_basic_1__csize___boxed(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l___private_init_data_string_basic_1__csize(x_2);
return x_3;
}
}
obj* l___private_init_data_string_basic_2__utf8ByteSizeAux___main(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_2;
}
else
{
obj* x_3; obj* x_4; uint32 x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_6 = l___private_init_data_string_basic_1__csize(x_5);
x_7 = lean::nat_add(x_2, x_6);
lean::dec(x_6);
lean::dec(x_2);
x_1 = x_4;
x_2 = x_7;
goto _start;
}
}
}
obj* l___private_init_data_string_basic_2__utf8ByteSizeAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_data_string_basic_2__utf8ByteSizeAux___main(x_1, x_2);
return x_3;
}
}
obj* l_String_utf8ByteSize___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::string_utf8_byte_size(x_1);
return x_2;
}
}
obj* l_String_bsize(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::string_utf8_byte_size(x_1);
return x_2;
}
}
obj* l_String_bsize___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_bsize(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_String_toSubstring(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::string_utf8_byte_size(x_1);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
lean::cnstr_set(x_4, 2, x_2);
return x_4;
}
}
uint32 l___private_init_data_string_basic_3__utf8GetAux___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint32 x_4; 
lean::dec(x_2);
x_4 = 65;
return x_4;
}
else
{
obj* x_5; obj* x_6; uint8 x_7; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::nat_dec_eq(x_2, x_3);
if (x_7 == 0)
{
uint32 x_8; obj* x_9; obj* x_10; 
x_8 = lean::unbox_uint32(x_5);
lean::dec(x_5);
x_9 = l___private_init_data_string_basic_1__csize(x_8);
x_10 = lean::nat_add(x_2, x_9);
lean::dec(x_9);
lean::dec(x_2);
x_1 = x_6;
x_2 = x_10;
goto _start;
}
else
{
uint32 x_12; 
lean::dec(x_6);
lean::dec(x_2);
x_12 = lean::unbox_uint32(x_5);
lean::dec(x_5);
return x_12;
}
}
}
}
obj* l___private_init_data_string_basic_3__utf8GetAux___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = l___private_init_data_string_basic_3__utf8GetAux___main(x_1, x_2, x_3);
lean::dec(x_3);
x_5 = lean::box_uint32(x_4);
return x_5;
}
}
uint32 l___private_init_data_string_basic_3__utf8GetAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; 
x_4 = l___private_init_data_string_basic_3__utf8GetAux___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_data_string_basic_3__utf8GetAux___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = l___private_init_data_string_basic_3__utf8GetAux(x_1, x_2, x_3);
lean::dec(x_3);
x_5 = lean::box_uint32(x_4);
return x_5;
}
}
obj* l_String_get___boxed(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::string_utf8_get(x_1, x_2);
x_4 = lean::box_uint32(x_3);
return x_4;
}
}
obj* l___private_init_data_string_basic_4__utf8SetAux___main(uint32 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_2;
}
else
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_2);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
x_8 = lean::nat_dec_eq(x_3, x_4);
if (x_8 == 0)
{
uint32 x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = lean::unbox_uint32(x_6);
x_10 = l___private_init_data_string_basic_1__csize(x_9);
x_11 = lean::nat_add(x_3, x_10);
lean::dec(x_10);
x_12 = l___private_init_data_string_basic_4__utf8SetAux___main(x_1, x_7, x_11, x_4);
lean::dec(x_11);
lean::cnstr_set(x_2, 1, x_12);
return x_2;
}
else
{
obj* x_13; 
lean::dec(x_6);
x_13 = lean::box_uint32(x_1);
lean::cnstr_set(x_2, 0, x_13);
return x_2;
}
}
else
{
obj* x_14; obj* x_15; uint8 x_16; 
x_14 = lean::cnstr_get(x_2, 0);
x_15 = lean::cnstr_get(x_2, 1);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_2);
x_16 = lean::nat_dec_eq(x_3, x_4);
if (x_16 == 0)
{
uint32 x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_17 = lean::unbox_uint32(x_14);
x_18 = l___private_init_data_string_basic_1__csize(x_17);
x_19 = lean::nat_add(x_3, x_18);
lean::dec(x_18);
x_20 = l___private_init_data_string_basic_4__utf8SetAux___main(x_1, x_15, x_19, x_4);
lean::dec(x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_14);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
else
{
obj* x_22; obj* x_23; 
lean::dec(x_14);
x_22 = lean::box_uint32(x_1);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_15);
return x_23;
}
}
}
}
}
obj* l___private_init_data_string_basic_4__utf8SetAux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_6 = l___private_init_data_string_basic_4__utf8SetAux___main(x_5, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_6;
}
}
obj* l___private_init_data_string_basic_4__utf8SetAux(uint32 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_string_basic_4__utf8SetAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l___private_init_data_string_basic_4__utf8SetAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_6 = l___private_init_data_string_basic_4__utf8SetAux(x_5, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_6;
}
}
obj* l_String_set___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_3);
x_5 = lean::string_utf8_set(x_1, x_2, x_4);
return x_5;
}
}
obj* l_String_next___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::string_utf8_next(x_1, x_2);
return x_3;
}
}
obj* l___private_init_data_string_basic_5__utf8PrevAux___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::mk_nat_obj(0u);
return x_4;
}
else
{
obj* x_5; obj* x_6; uint32 x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::unbox_uint32(x_5);
lean::dec(x_5);
x_8 = l___private_init_data_string_basic_1__csize(x_7);
x_9 = lean::nat_add(x_2, x_8);
lean::dec(x_8);
x_10 = lean::nat_dec_eq(x_9, x_3);
if (x_10 == 0)
{
lean::dec(x_2);
x_1 = x_6;
x_2 = x_9;
goto _start;
}
else
{
lean::dec(x_9);
lean::dec(x_6);
return x_2;
}
}
}
}
obj* l___private_init_data_string_basic_5__utf8PrevAux___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_data_string_basic_5__utf8PrevAux___main(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l___private_init_data_string_basic_5__utf8PrevAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_data_string_basic_5__utf8PrevAux___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_data_string_basic_5__utf8PrevAux___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_data_string_basic_5__utf8PrevAux(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_String_prev___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::string_utf8_prev(x_1, x_2);
return x_3;
}
}
uint32 l_String_front(obj* x_1) {
_start:
{
obj* x_2; uint32 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::string_utf8_get(x_1, x_2);
return x_3;
}
}
obj* l_String_front___boxed(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = l_String_front(x_1);
lean::dec(x_1);
x_3 = lean::box_uint32(x_2);
return x_3;
}
}
uint32 l_String_back(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint32 x_4; 
x_2 = lean::string_utf8_byte_size(x_1);
x_3 = lean::string_utf8_prev(x_1, x_2);
lean::dec(x_2);
x_4 = lean::string_utf8_get(x_1, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_String_back___boxed(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = l_String_back(x_1);
lean::dec(x_1);
x_3 = lean::box_uint32(x_2);
return x_3;
}
}
obj* l_String_atEnd___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::string_utf8_at_end(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_String_posOfAux___main(obj* x_1, uint32 x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::nat_dec_eq(x_4, x_3);
if (x_5 == 0)
{
uint32 x_6; uint8 x_7; 
x_6 = lean::string_utf8_get(x_1, x_4);
x_7 = x_6 == x_2;
if (x_7 == 0)
{
obj* x_8; 
x_8 = lean::string_utf8_next(x_1, x_4);
lean::dec(x_4);
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
obj* l_String_posOfAux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_6 = l_String_posOfAux___main(x_1, x_5, x_3, x_4);
lean::dec(x_3);
lean::dec(x_1);
return x_6;
}
}
obj* l_String_posOfAux(obj* x_1, uint32 x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_String_posOfAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_String_posOfAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_6 = l_String_posOfAux(x_1, x_5, x_3, x_4);
lean::dec(x_3);
lean::dec(x_1);
return x_6;
}
}
obj* l_String_posOf(obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::string_utf8_byte_size(x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = l_String_posOfAux___main(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_String_posOf___boxed(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_4 = l_String_posOf(x_1, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_data_string_basic_6__utf8ExtractAux_u2082___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_1;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; uint8 x_7; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean::nat_dec_eq(x_2, x_3);
if (x_7 == 0)
{
uint32 x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::unbox_uint32(x_5);
x_9 = l___private_init_data_string_basic_1__csize(x_8);
x_10 = lean::nat_add(x_2, x_9);
lean::dec(x_9);
x_11 = l___private_init_data_string_basic_6__utf8ExtractAux_u2082___main(x_6, x_10, x_3);
lean::dec(x_10);
lean::cnstr_set(x_1, 1, x_11);
return x_1;
}
else
{
obj* x_12; 
lean::free_heap_obj(x_1);
lean::dec(x_6);
lean::dec(x_5);
x_12 = lean::box(0);
return x_12;
}
}
else
{
obj* x_13; obj* x_14; uint8 x_15; 
x_13 = lean::cnstr_get(x_1, 0);
x_14 = lean::cnstr_get(x_1, 1);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_1);
x_15 = lean::nat_dec_eq(x_2, x_3);
if (x_15 == 0)
{
uint32 x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_16 = lean::unbox_uint32(x_13);
x_17 = l___private_init_data_string_basic_1__csize(x_16);
x_18 = lean::nat_add(x_2, x_17);
lean::dec(x_17);
x_19 = l___private_init_data_string_basic_6__utf8ExtractAux_u2082___main(x_14, x_18, x_3);
lean::dec(x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_13);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
else
{
obj* x_21; 
lean::dec(x_14);
lean::dec(x_13);
x_21 = lean::box(0);
return x_21;
}
}
}
}
}
obj* l___private_init_data_string_basic_6__utf8ExtractAux_u2082___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_data_string_basic_6__utf8ExtractAux_u2082___main(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l___private_init_data_string_basic_6__utf8ExtractAux_u2082(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_data_string_basic_6__utf8ExtractAux_u2082___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_data_string_basic_6__utf8ExtractAux_u2082___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_data_string_basic_6__utf8ExtractAux_u2082(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l___private_init_data_string_basic_7__utf8ExtractAux_u2081___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_2);
return x_1;
}
else
{
obj* x_5; obj* x_6; uint8 x_7; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_7 = lean::nat_dec_eq(x_2, x_3);
if (x_7 == 0)
{
uint32 x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_8 = lean::unbox_uint32(x_5);
lean::dec(x_5);
x_9 = l___private_init_data_string_basic_1__csize(x_8);
x_10 = lean::nat_add(x_2, x_9);
lean::dec(x_9);
lean::dec(x_2);
x_1 = x_6;
x_2 = x_10;
goto _start;
}
else
{
obj* x_12; 
lean::dec(x_6);
lean::dec(x_5);
x_12 = l___private_init_data_string_basic_6__utf8ExtractAux_u2082___main(x_1, x_2, x_4);
lean::dec(x_2);
return x_12;
}
}
}
}
obj* l___private_init_data_string_basic_7__utf8ExtractAux_u2081___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_string_basic_7__utf8ExtractAux_u2081___main(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l___private_init_data_string_basic_7__utf8ExtractAux_u2081(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_string_basic_7__utf8ExtractAux_u2081___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l___private_init_data_string_basic_7__utf8ExtractAux_u2081___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_string_basic_7__utf8ExtractAux_u2081(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_String_extract___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::string_utf8_extract(x_1, x_2, x_3);
return x_4;
}
}
obj* _init_l_String_splitAux___main___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("");
return x_1;
}
}
obj* l_String_splitAux___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; 
x_7 = lean::string_utf8_at_end(x_1, x_4);
if (x_7 == 0)
{
uint32 x_8; uint32 x_9; uint8 x_10; 
x_8 = lean::string_utf8_get(x_1, x_4);
x_9 = lean::string_utf8_get(x_2, x_5);
x_10 = x_8 == x_9;
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
lean::dec(x_5);
x_11 = lean::string_utf8_next(x_1, x_4);
lean::dec(x_4);
x_12 = lean::mk_nat_obj(0u);
x_4 = x_11;
x_5 = x_12;
goto _start;
}
else
{
obj* x_14; obj* x_15; uint8 x_16; 
x_14 = lean::string_utf8_next(x_1, x_4);
lean::dec(x_4);
x_15 = lean::string_utf8_next(x_2, x_5);
lean::dec(x_5);
x_16 = lean::string_utf8_at_end(x_2, x_15);
if (x_16 == 0)
{
x_4 = x_14;
x_5 = x_15;
goto _start;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_18 = lean::nat_sub(x_14, x_15);
lean::dec(x_15);
x_19 = lean::string_utf8_extract(x_1, x_3, x_18);
lean::dec(x_18);
lean::dec(x_3);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_6);
x_21 = lean::mk_nat_obj(0u);
lean::inc(x_14);
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
uint8 x_23; 
x_23 = lean::string_utf8_at_end(x_2, x_5);
if (x_23 == 0)
{
obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_5);
x_24 = lean::string_utf8_extract(x_1, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_6);
x_26 = l_List_reverse___rarg(x_25);
return x_26;
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_27 = lean::nat_sub(x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
x_28 = lean::string_utf8_extract(x_1, x_3, x_27);
lean::dec(x_27);
lean::dec(x_3);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_6);
x_30 = l_String_splitAux___main___closed__1;
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_29);
x_32 = l_List_reverse___rarg(x_31);
return x_32;
}
}
}
}
obj* l_String_splitAux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_String_splitAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_String_splitAux(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_String_splitAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
obj* l_String_splitAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_String_splitAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_String_split(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = l_String_splitAux___main___closed__1;
x_4 = lean::string_dec_eq(x_2, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::box(0);
x_6 = lean::mk_nat_obj(0u);
x_7 = l_String_splitAux___main(x_1, x_2, x_6, x_6, x_6, x_5);
lean::dec(x_1);
return x_7;
}
else
{
obj* x_8; obj* x_9; 
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_String_split___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_String_split(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_String_Inhabited() {
_start:
{
obj* x_1; 
x_1 = l_String_splitAux___main___closed__1;
return x_1;
}
}
obj* _init_l_String_HasSizeof___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_String_length___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_String_HasSizeof() {
_start:
{
obj* x_1; 
x_1 = l_String_HasSizeof___closed__1;
return x_1;
}
}
obj* _init_l_String_HasAppend___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_String_append___boxed), 2, 0);
return x_1;
}
}
obj* _init_l_String_HasAppend() {
_start:
{
obj* x_1; 
x_1 = l_String_HasAppend___closed__1;
return x_1;
}
}
obj* l_String_str(obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; 
x_3 = lean::string_push(x_1, x_2);
return x_3;
}
}
obj* l_String_str___boxed(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_4 = l_String_str(x_1, x_3);
return x_4;
}
}
obj* l_Nat_repeatAux___main___at_String_pushn___spec__1(uint32 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_2, x_6);
lean::dec(x_2);
x_8 = lean::string_push(x_3, x_1);
x_2 = x_7;
x_3 = x_8;
goto _start;
}
else
{
lean::dec(x_2);
return x_3;
}
}
}
obj* l_String_pushn(obj* x_1, uint32 x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Nat_repeatAux___main___at_String_pushn___spec__1(x_2, x_3, x_1);
return x_4;
}
}
obj* l_Nat_repeatAux___main___at_String_pushn___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_5 = l_Nat_repeatAux___main___at_String_pushn___spec__1(x_4, x_2, x_3);
return x_5;
}
}
obj* l_String_pushn___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_5 = l_String_pushn(x_1, x_4, x_3);
return x_5;
}
}
uint8 l_String_isEmpty(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::string_utf8_byte_size(x_1);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_String_isEmpty___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_String_isEmpty(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_List_foldl___main___at_String_join___spec__1(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::string_append(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
obj* l_String_join(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_String_splitAux___main___closed__1;
x_3 = l_List_foldl___main___at_String_join___spec__1(x_2, x_1);
return x_3;
}
}
obj* l_List_foldl___main___at_String_join___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_foldl___main___at_String_join___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_String_join___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_join(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_String_singleton(uint32 x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean::string_push(x_2, x_1);
return x_3;
}
}
obj* l_String_singleton___boxed(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_String_singleton(x_2);
return x_3;
}
}
obj* l_List_map___main___at_String_intercalate___spec__1(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::string_data(x_4);
x_7 = l_List_map___main___at_String_intercalate___spec__1(x_5);
lean::cnstr_set(x_1, 1, x_7);
lean::cnstr_set(x_1, 0, x_6);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_10 = lean::string_data(x_8);
x_11 = l_List_map___main___at_String_intercalate___spec__1(x_9);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
}
}
obj* l_String_intercalate(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::string_data(x_1);
x_4 = l_List_map___main___at_String_intercalate___spec__1(x_2);
x_5 = l_List_intercalate___rarg(x_3, x_4);
x_6 = lean::string_mk(x_5);
return x_6;
}
}
obj* l_String_mkIterator(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_String_Iterator_toString___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
return x_2;
}
}
obj* l_String_Iterator_toString___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_toString___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_String_Iterator_toString(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_toString___main(x_1);
return x_2;
}
}
obj* l_String_Iterator_toString___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_toString(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_String_Iterator_remainingBytes___main(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::string_utf8_byte_size(x_2);
x_5 = lean::nat_sub(x_4, x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_String_Iterator_remainingBytes___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_remainingBytes___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_String_Iterator_remainingBytes(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_remainingBytes___main(x_1);
return x_2;
}
}
obj* l_String_Iterator_remainingBytes___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_remainingBytes(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_String_Iterator_pos___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
return x_2;
}
}
obj* l_String_Iterator_pos___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_pos___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_String_Iterator_pos(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_pos___main(x_1);
return x_2;
}
}
obj* l_String_Iterator_pos___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_pos(x_1);
lean::dec(x_1);
return x_2;
}
}
uint32 l_String_Iterator_curr___main(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint32 x_4; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::string_utf8_get(x_2, x_3);
return x_4;
}
}
obj* l_String_Iterator_curr___main___boxed(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = l_String_Iterator_curr___main(x_1);
lean::dec(x_1);
x_3 = lean::box_uint32(x_2);
return x_3;
}
}
uint32 l_String_Iterator_curr(obj* x_1) {
_start:
{
uint32 x_2; 
x_2 = l_String_Iterator_curr___main(x_1);
return x_2;
}
}
obj* l_String_Iterator_curr___boxed(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = l_String_Iterator_curr(x_1);
lean::dec(x_1);
x_3 = lean::box_uint32(x_2);
return x_3;
}
}
obj* l_String_Iterator_next___main(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::string_utf8_next(x_3, x_4);
lean::dec(x_4);
lean::cnstr_set(x_1, 1, x_5);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::inc(x_6);
lean::dec(x_1);
x_8 = lean::string_utf8_next(x_6, x_7);
lean::dec(x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_String_Iterator_next(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_next___main(x_1);
return x_2;
}
}
obj* l_String_Iterator_prev___main(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::string_utf8_prev(x_3, x_4);
lean::dec(x_4);
lean::cnstr_set(x_1, 1, x_5);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::inc(x_6);
lean::dec(x_1);
x_8 = lean::string_utf8_prev(x_6, x_7);
lean::dec(x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_String_Iterator_prev(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_prev___main(x_1);
return x_2;
}
}
uint8 l_String_Iterator_hasNext___main(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; uint8 x_5; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::string_utf8_byte_size(x_2);
x_5 = lean::nat_dec_lt(x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_String_Iterator_hasNext___main___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_String_Iterator_hasNext___main(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_String_Iterator_hasNext(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_String_Iterator_hasNext___main(x_1);
return x_2;
}
}
obj* l_String_Iterator_hasNext___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_String_Iterator_hasNext(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_String_Iterator_hasPrev___main(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::cnstr_get(x_1, 1);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_lt(x_3, x_2);
return x_4;
}
}
obj* l_String_Iterator_hasPrev___main___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_String_Iterator_hasPrev___main(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_String_Iterator_hasPrev(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_String_Iterator_hasPrev___main(x_1);
return x_2;
}
}
obj* l_String_Iterator_hasPrev___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_String_Iterator_hasPrev(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_String_Iterator_setCurr___main(obj* x_1, uint32 x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::string_utf8_set(x_4, x_5, x_2);
lean::cnstr_set(x_1, 0, x_6);
return x_1;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_1, 0);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::inc(x_7);
lean::dec(x_1);
x_9 = lean::string_utf8_set(x_7, x_8, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
return x_10;
}
}
}
obj* l_String_Iterator_setCurr___main___boxed(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_4 = l_String_Iterator_setCurr___main(x_1, x_3);
return x_4;
}
}
obj* l_String_Iterator_setCurr(obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; 
x_3 = l_String_Iterator_setCurr___main(x_1, x_2);
return x_3;
}
}
obj* l_String_Iterator_setCurr___boxed(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_4 = l_String_Iterator_setCurr(x_1, x_3);
return x_4;
}
}
obj* l_String_Iterator_toEnd___main(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
lean::dec(x_4);
x_5 = lean::string_utf8_byte_size(x_3);
lean::cnstr_set(x_1, 1, x_5);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::string_utf8_byte_size(x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
}
obj* l_String_Iterator_toEnd(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_toEnd___main(x_1);
return x_2;
}
}
obj* l_String_Iterator_extract___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
x_7 = lean::string_dec_eq(x_3, x_5);
if (x_7 == 0)
{
obj* x_8; 
x_8 = l_String_splitAux___main___closed__1;
return x_8;
}
else
{
uint8 x_9; 
x_9 = lean::nat_dec_lt(x_6, x_4);
if (x_9 == 0)
{
obj* x_10; 
x_10 = lean::string_utf8_extract(x_3, x_4, x_6);
return x_10;
}
else
{
obj* x_11; 
x_11 = l_String_splitAux___main___closed__1;
return x_11;
}
}
}
}
obj* l_String_Iterator_extract___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_String_Iterator_extract___main(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_String_Iterator_extract(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_String_Iterator_extract___main(x_1, x_2);
return x_3;
}
}
obj* l_String_Iterator_extract___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_String_Iterator_extract(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_String_Iterator_forward___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_2, x_5);
lean::dec(x_2);
x_7 = l_String_Iterator_next___main(x_1);
x_1 = x_7;
x_2 = x_6;
goto _start;
}
else
{
lean::dec(x_2);
return x_1;
}
}
}
obj* l_String_Iterator_forward(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_String_Iterator_forward___main(x_1, x_2);
return x_3;
}
}
obj* l_String_Iterator_remainingToString___main(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::string_utf8_byte_size(x_2);
x_5 = lean::string_utf8_extract(x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_String_Iterator_remainingToString___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_remainingToString___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_String_Iterator_remainingToString(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_remainingToString___main(x_1);
return x_2;
}
}
obj* l_String_Iterator_remainingToString___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_Iterator_remainingToString(x_1);
lean::dec(x_1);
return x_2;
}
}
uint8 l_String_Iterator_isPrefixOfRemaining___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
x_7 = lean::string_utf8_byte_size(x_3);
x_8 = lean::string_utf8_extract(x_3, x_4, x_7);
x_9 = lean::nat_sub(x_7, x_4);
lean::dec(x_7);
x_10 = lean::nat_add(x_6, x_9);
lean::dec(x_9);
x_11 = lean::string_utf8_extract(x_5, x_6, x_10);
lean::dec(x_10);
x_12 = lean::string_dec_eq(x_8, x_11);
lean::dec(x_11);
lean::dec(x_8);
return x_12;
}
}
obj* l_String_Iterator_isPrefixOfRemaining___main___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_String_Iterator_isPrefixOfRemaining___main(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_String_Iterator_isPrefixOfRemaining(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_String_Iterator_isPrefixOfRemaining___main(x_1, x_2);
return x_3;
}
}
obj* l_String_Iterator_isPrefixOfRemaining___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_String_Iterator_isPrefixOfRemaining(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_String_Iterator_nextn___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_2, x_5);
lean::dec(x_2);
x_7 = l_String_Iterator_next___main(x_1);
x_1 = x_7;
x_2 = x_6;
goto _start;
}
else
{
lean::dec(x_2);
return x_1;
}
}
}
obj* l_String_Iterator_nextn(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_String_Iterator_nextn___main(x_1, x_2);
return x_3;
}
}
obj* l_String_Iterator_prevn___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_2, x_5);
lean::dec(x_2);
x_7 = l_String_Iterator_prev___main(x_1);
x_1 = x_7;
x_2 = x_6;
goto _start;
}
else
{
lean::dec(x_2);
return x_1;
}
}
}
obj* l_String_Iterator_prevn(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_String_Iterator_prevn___main(x_1, x_2);
return x_3;
}
}
obj* l___private_init_data_string_basic_8__lineColumnAux___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_6 = lean::string_utf8_at_end(x_1, x_2);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_3);
if (x_7 == 0)
{
obj* x_8; obj* x_9; uint32 x_10; uint32 x_11; uint8 x_12; 
x_8 = lean::cnstr_get(x_3, 1);
lean::dec(x_8);
x_9 = lean::cnstr_get(x_3, 0);
lean::dec(x_9);
x_10 = lean::string_utf8_get(x_1, x_2);
x_11 = 10;
x_12 = x_10 == x_11;
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; 
x_13 = lean::string_utf8_next(x_1, x_2);
lean::dec(x_2);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_5, x_14);
lean::dec(x_5);
lean::cnstr_set(x_3, 1, x_15);
x_2 = x_13;
goto _start;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_5);
x_17 = lean::string_utf8_next(x_1, x_2);
lean::dec(x_2);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean::nat_add(x_4, x_18);
lean::dec(x_4);
x_20 = lean::mk_nat_obj(0u);
lean::cnstr_set(x_3, 1, x_20);
lean::cnstr_set(x_3, 0, x_19);
x_2 = x_17;
goto _start;
}
}
else
{
uint32 x_22; uint32 x_23; uint8 x_24; 
lean::dec(x_3);
x_22 = lean::string_utf8_get(x_1, x_2);
x_23 = 10;
x_24 = x_22 == x_23;
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_25 = lean::string_utf8_next(x_1, x_2);
lean::dec(x_2);
x_26 = lean::mk_nat_obj(1u);
x_27 = lean::nat_add(x_5, x_26);
lean::dec(x_5);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_4);
lean::cnstr_set(x_28, 1, x_27);
x_2 = x_25;
x_3 = x_28;
goto _start;
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_5);
x_30 = lean::string_utf8_next(x_1, x_2);
lean::dec(x_2);
x_31 = lean::mk_nat_obj(1u);
x_32 = lean::nat_add(x_4, x_31);
lean::dec(x_4);
x_33 = lean::mk_nat_obj(0u);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_33);
x_2 = x_30;
x_3 = x_34;
goto _start;
}
}
}
else
{
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_2);
return x_3;
}
}
}
obj* l___private_init_data_string_basic_8__lineColumnAux___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_data_string_basic_8__lineColumnAux___main(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_data_string_basic_8__lineColumnAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_data_string_basic_8__lineColumnAux___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_data_string_basic_8__lineColumnAux___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_data_string_basic_8__lineColumnAux(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_String_lineColumn___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(1u);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_String_lineColumn(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_String_lineColumn___closed__1;
x_5 = l___private_init_data_string_basic_8__lineColumnAux___main(x_1, x_3, x_4);
return x_5;
}
}
obj* l_String_lineColumn___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_String_lineColumn(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_String_offsetOfPosAux___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::nat_dec_eq(x_3, x_2);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = lean::string_utf8_at_end(x_1, x_3);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::string_utf8_next(x_1, x_3);
lean::dec(x_3);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_4, x_8);
lean::dec(x_4);
x_3 = x_7;
x_4 = x_9;
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
}
obj* l_String_offsetOfPosAux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_String_offsetOfPosAux___main(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_String_offsetOfPosAux(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_String_offsetOfPosAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_String_offsetOfPosAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_String_offsetOfPosAux(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_String_offsetOfPos(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_String_offsetOfPosAux___main(x_1, x_2, x_3, x_3);
return x_4;
}
}
obj* l_String_offsetOfPos___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_String_offsetOfPos(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_String_foldlAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = lean::nat_dec_eq(x_4, x_3);
if (x_6 == 0)
{
obj* x_7; uint32 x_8; obj* x_9; obj* x_10; 
x_7 = lean::string_utf8_next(x_2, x_4);
x_8 = lean::string_utf8_get(x_2, x_4);
lean::dec(x_4);
x_9 = lean::box_uint32(x_8);
lean::inc(x_1);
x_10 = lean::apply_2(x_1, x_5, x_9);
x_4 = x_7;
x_5 = x_10;
goto _start;
}
else
{
lean::dec(x_4);
lean::dec(x_1);
return x_5;
}
}
}
obj* l_String_foldlAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_String_foldlAux___main___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_String_foldlAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_String_foldlAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_String_foldlAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_String_foldlAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_String_foldlAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_String_foldlAux___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_String_foldlAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_String_foldlAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_String_foldl___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::string_utf8_byte_size(x_3);
x_5 = lean::mk_nat_obj(0u);
x_6 = l_String_foldlAux___main___rarg(x_1, x_3, x_4, x_5, x_2);
lean::dec(x_4);
return x_6;
}
}
obj* l_String_foldl(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_String_foldl___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_String_foldl___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_String_foldl___rarg(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_String_foldrAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = lean::nat_dec_eq(x_5, x_4);
if (x_6 == 0)
{
uint32 x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::string_utf8_get(x_3, x_5);
x_8 = lean::string_utf8_next(x_3, x_5);
lean::inc(x_1);
x_9 = l_String_foldrAux___main___rarg(x_1, x_2, x_3, x_4, x_8);
lean::dec(x_8);
x_10 = lean::box_uint32(x_7);
x_11 = lean::apply_2(x_1, x_10, x_9);
return x_11;
}
else
{
lean::dec(x_1);
lean::inc(x_2);
return x_2;
}
}
}
obj* l_String_foldrAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_String_foldrAux___main___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_String_foldrAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_String_foldrAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_String_foldrAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_String_foldrAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_String_foldrAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_String_foldrAux___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_String_foldrAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_String_foldrAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_String_foldr___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::string_utf8_byte_size(x_3);
x_5 = lean::mk_nat_obj(0u);
x_6 = l_String_foldrAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
return x_6;
}
}
obj* l_String_foldr(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_String_foldr___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_String_foldr___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_String_foldr___rarg(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
uint8 l_String_anyAux___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::nat_dec_eq(x_4, x_2);
if (x_5 == 0)
{
uint32 x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_6 = lean::string_utf8_get(x_1, x_4);
x_7 = lean::box_uint32(x_6);
lean::inc(x_3);
x_8 = lean::apply_1(x_3, x_7);
x_9 = lean::unbox(x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; 
x_10 = lean::string_utf8_next(x_1, x_4);
lean::dec(x_4);
x_4 = x_10;
goto _start;
}
else
{
uint8 x_12; 
lean::dec(x_4);
lean::dec(x_3);
x_12 = 1;
return x_12;
}
}
else
{
uint8 x_13; 
lean::dec(x_4);
lean::dec(x_3);
x_13 = 0;
return x_13;
}
}
}
obj* l_String_anyAux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_String_anyAux___main(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
x_6 = lean::box(x_5);
return x_6;
}
}
uint8 l_String_anyAux(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = l_String_anyAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_String_anyAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_String_anyAux(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
x_6 = lean::box(x_5);
return x_6;
}
}
uint8 l_String_any(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::string_utf8_byte_size(x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = l_String_anyAux___main(x_1, x_3, x_2, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_String_any___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_String_any(x_1, x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_String_anyAux___main___at_String_all___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::nat_dec_eq(x_4, x_3);
if (x_5 == 0)
{
uint32 x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_6 = lean::string_utf8_get(x_2, x_4);
x_7 = lean::box_uint32(x_6);
lean::inc(x_1);
x_8 = lean::apply_1(x_1, x_7);
x_9 = lean::unbox(x_8);
lean::dec(x_8);
if (x_9 == 0)
{
uint8 x_10; 
lean::dec(x_4);
lean::dec(x_1);
x_10 = 1;
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::string_utf8_next(x_2, x_4);
lean::dec(x_4);
x_4 = x_11;
goto _start;
}
}
else
{
uint8 x_13; 
lean::dec(x_4);
lean::dec(x_1);
x_13 = 0;
return x_13;
}
}
}
uint8 l_String_all(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::string_utf8_byte_size(x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = l_String_anyAux___main___at_String_all___spec__1(x_2, x_1, x_3, x_4);
lean::dec(x_3);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
}
}
obj* l_String_anyAux___main___at_String_all___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_String_anyAux___main___at_String_all___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
x_6 = lean::box(x_5);
return x_6;
}
}
obj* l_String_all___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_String_all(x_1, x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_String_anyAux___main___at_String_contains___spec__1(uint32 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::nat_dec_eq(x_4, x_3);
if (x_5 == 0)
{
uint32 x_6; uint8 x_7; 
x_6 = lean::string_utf8_get(x_2, x_4);
x_7 = x_6 == x_1;
if (x_7 == 0)
{
obj* x_8; 
x_8 = lean::string_utf8_next(x_2, x_4);
lean::dec(x_4);
x_4 = x_8;
goto _start;
}
else
{
uint8 x_10; 
lean::dec(x_4);
x_10 = 1;
return x_10;
}
}
else
{
uint8 x_11; 
lean::dec(x_4);
x_11 = 0;
return x_11;
}
}
}
uint8 l_String_contains(obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::string_utf8_byte_size(x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = l_String_anyAux___main___at_String_contains___spec__1(x_2, x_1, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_String_anyAux___main___at_String_contains___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; uint8 x_6; obj* x_7; 
x_5 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_6 = l_String_anyAux___main___at_String_contains___spec__1(x_5, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
x_7 = lean::box(x_6);
return x_7;
}
}
obj* l_String_contains___boxed(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; uint8 x_4; obj* x_5; 
x_3 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_4 = l_String_contains(x_1, x_3);
lean::dec(x_1);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_String_mapAux___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::string_utf8_at_end(x_3, x_2);
if (x_4 == 0)
{
uint32 x_5; obj* x_6; obj* x_7; uint32 x_8; obj* x_9; obj* x_10; 
x_5 = lean::string_utf8_get(x_3, x_2);
x_6 = lean::box_uint32(x_5);
lean::inc(x_1);
x_7 = lean::apply_1(x_1, x_6);
x_8 = lean::unbox_uint32(x_7);
lean::dec(x_7);
x_9 = lean::string_utf8_set(x_3, x_2, x_8);
x_10 = lean::string_utf8_next(x_9, x_2);
lean::dec(x_2);
x_2 = x_10;
x_3 = x_9;
goto _start;
}
else
{
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
}
obj* l_String_mapAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_String_mapAux___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_String_map(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_String_mapAux___main(x_1, x_3, x_2);
return x_4;
}
}
obj* l_String_foldlAux___main___at_String_toNat___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::nat_dec_eq(x_3, x_2);
if (x_5 == 0)
{
obj* x_6; uint32 x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::string_utf8_next(x_1, x_3);
x_7 = lean::string_utf8_get(x_1, x_3);
lean::dec(x_3);
x_8 = lean::mk_nat_obj(10u);
x_9 = lean::nat_mul(x_4, x_8);
lean::dec(x_4);
x_10 = lean::uint32_to_nat(x_7);
x_11 = lean::mk_nat_obj(48u);
x_12 = lean::nat_sub(x_10, x_11);
lean::dec(x_10);
x_13 = lean::nat_add(x_9, x_12);
lean::dec(x_12);
lean::dec(x_9);
x_3 = x_6;
x_4 = x_13;
goto _start;
}
else
{
lean::dec(x_3);
return x_4;
}
}
}
obj* l_String_toNat(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::string_utf8_byte_size(x_1);
x_3 = lean::mk_nat_obj(0u);
x_4 = l_String_foldlAux___main___at_String_toNat___spec__1(x_1, x_2, x_3, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_String_foldlAux___main___at_String_toNat___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_String_foldlAux___main___at_String_toNat___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_String_toNat___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_toNat(x_1);
lean::dec(x_1);
return x_2;
}
}
uint8 l_String_anyAux___main___at_String_isNat___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::nat_dec_eq(x_3, x_2);
if (x_4 == 0)
{
uint32 x_5; uint8 x_6; 
x_5 = lean::string_utf8_get(x_1, x_3);
x_6 = l_Char_isDigit(x_5);
if (x_6 == 0)
{
uint8 x_7; 
lean::dec(x_3);
x_7 = 1;
return x_7;
}
else
{
obj* x_8; 
x_8 = lean::string_utf8_next(x_1, x_3);
lean::dec(x_3);
x_3 = x_8;
goto _start;
}
}
else
{
uint8 x_10; 
lean::dec(x_3);
x_10 = 0;
return x_10;
}
}
}
uint8 l_String_isNat(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::string_utf8_byte_size(x_1);
x_3 = lean::mk_nat_obj(0u);
x_4 = l_String_anyAux___main___at_String_isNat___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
}
}
obj* l_String_anyAux___main___at_String_isNat___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_String_anyAux___main___at_String_isNat___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_String_isNat___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_String_isNat(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_String_isPrefixOfAux___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::string_utf8_at_end(x_1, x_3);
if (x_4 == 0)
{
uint32 x_5; uint32 x_6; uint8 x_7; 
x_5 = lean::string_utf8_get(x_1, x_3);
x_6 = lean::string_utf8_get(x_2, x_3);
x_7 = x_5 == x_6;
if (x_7 == 0)
{
uint8 x_8; 
lean::dec(x_3);
x_8 = 0;
return x_8;
}
else
{
obj* x_9; 
x_9 = lean::string_utf8_next(x_2, x_3);
lean::dec(x_3);
x_3 = x_9;
goto _start;
}
}
else
{
uint8 x_11; 
lean::dec(x_3);
x_11 = 1;
return x_11;
}
}
}
obj* l_String_isPrefixOfAux___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_String_isPrefixOfAux___main(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_String_isPrefixOfAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_String_isPrefixOfAux___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_String_isPrefixOfAux___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_String_isPrefixOfAux(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_String_isPrefixOf(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::string_length(x_1);
x_4 = lean::string_length(x_2);
x_5 = lean::nat_dec_le(x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
else
{
obj* x_7; uint8 x_8; 
x_7 = lean::mk_nat_obj(0u);
x_8 = l_String_isPrefixOfAux___main(x_1, x_2, x_7);
return x_8;
}
}
}
obj* l_String_isPrefixOf___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_String_isPrefixOf(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Substring_toString___main(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_1, 2);
x_5 = lean::string_utf8_extract(x_2, x_3, x_4);
return x_5;
}
}
obj* l_Substring_toString___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Substring_toString___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Substring_toString(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_1, 2);
x_5 = lean::string_utf8_extract(x_2, x_3, x_4);
return x_5;
}
}
obj* l_Substring_toString___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Substring_toString(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Substring_toIterator___main(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::inc(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_Substring_toIterator___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Substring_toIterator___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Substring_toIterator(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::inc(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_Substring_toIterator___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Substring_toIterator(x_1);
lean::dec(x_1);
return x_2;
}
}
uint32 l_Substring_get___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; uint32 x_6; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::nat_add(x_4, x_2);
x_6 = lean::string_utf8_get(x_3, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l_Substring_get___main___boxed(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = l_Substring_get___main(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box_uint32(x_3);
return x_4;
}
}
uint32 l_Substring_get(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; uint32 x_6; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::nat_add(x_4, x_2);
x_6 = lean::string_utf8_get(x_3, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l_Substring_get___boxed(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = l_Substring_get(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box_uint32(x_3);
return x_4;
}
}
obj* l_Substring_next___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_1, 2);
x_6 = lean::nat_add(x_4, x_2);
x_7 = lean::string_utf8_next(x_3, x_6);
lean::dec(x_6);
x_8 = lean::nat_dec_lt(x_5, x_7);
if (x_8 == 0)
{
obj* x_9; 
x_9 = lean::nat_sub(x_7, x_4);
lean::dec(x_7);
return x_9;
}
else
{
obj* x_10; 
lean::dec(x_7);
x_10 = lean::nat_sub(x_5, x_4);
return x_10;
}
}
}
obj* l_Substring_next___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Substring_next___main(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Substring_next(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_1, 2);
x_6 = lean::nat_add(x_4, x_2);
x_7 = lean::string_utf8_next(x_3, x_6);
lean::dec(x_6);
x_8 = lean::nat_dec_lt(x_5, x_7);
if (x_8 == 0)
{
obj* x_9; 
x_9 = lean::nat_sub(x_7, x_4);
lean::dec(x_7);
return x_9;
}
else
{
obj* x_10; 
lean::dec(x_7);
x_10 = lean::nat_sub(x_5, x_4);
return x_10;
}
}
}
obj* l_Substring_next___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Substring_next(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Substring_prev___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::nat_add(x_4, x_2);
x_7 = lean::string_utf8_prev(x_3, x_6);
lean::dec(x_6);
x_8 = lean::nat_sub(x_7, x_4);
lean::dec(x_7);
return x_8;
}
else
{
lean::inc(x_2);
return x_2;
}
}
}
obj* l_Substring_prev___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Substring_prev___main(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Substring_prev(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::nat_add(x_4, x_2);
x_7 = lean::string_utf8_prev(x_3, x_6);
lean::dec(x_6);
x_8 = lean::nat_sub(x_7, x_4);
lean::dec(x_7);
return x_8;
}
else
{
lean::inc(x_2);
return x_2;
}
}
}
obj* l_Substring_prev___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Substring_prev(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
uint32 l_Substring_front(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; uint32 x_6; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_add(x_3, x_4);
x_6 = lean::string_utf8_get(x_2, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l_Substring_front___boxed(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = l_Substring_front(x_1);
lean::dec(x_1);
x_3 = lean::box_uint32(x_2);
return x_3;
}
}
obj* l_Substring_posOf(obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 2);
lean::inc(x_5);
lean::dec(x_1);
lean::inc(x_4);
x_6 = l_String_posOfAux___main(x_3, x_2, x_5, x_4);
lean::dec(x_5);
lean::dec(x_3);
x_7 = lean::nat_sub(x_6, x_4);
lean::dec(x_4);
lean::dec(x_6);
return x_7;
}
}
obj* l_Substring_posOf___boxed(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_4 = l_Substring_posOf(x_1, x_3);
return x_4;
}
}
obj* _init_l_Substring_drop___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = lean::string_utf8_byte_size(x_1);
return x_2;
}
}
obj* _init_l_Substring_drop___main___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Substring_drop___main___closed__1;
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 2, x_3);
return x_4;
}
}
obj* l_Substring_drop___main(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::nat_add(x_5, x_2);
lean::dec(x_5);
x_8 = lean::nat_dec_le(x_6, x_7);
if (x_8 == 0)
{
lean::cnstr_set(x_1, 1, x_7);
return x_1;
}
else
{
obj* x_9; 
lean::dec(x_7);
lean::free_heap_obj(x_1);
lean::dec(x_6);
lean::dec(x_4);
x_9 = l_Substring_drop___main___closed__2;
return x_9;
}
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_10 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_1);
x_13 = lean::nat_add(x_11, x_2);
lean::dec(x_11);
x_14 = lean::nat_dec_le(x_12, x_13);
if (x_14 == 0)
{
obj* x_15; 
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_13);
lean::cnstr_set(x_15, 2, x_12);
return x_15;
}
else
{
obj* x_16; 
lean::dec(x_13);
lean::dec(x_12);
lean::dec(x_10);
x_16 = l_Substring_drop___main___closed__2;
return x_16;
}
}
}
}
obj* l_Substring_drop___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Substring_drop___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Substring_drop(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::nat_add(x_5, x_2);
lean::dec(x_5);
x_8 = lean::nat_dec_le(x_6, x_7);
if (x_8 == 0)
{
lean::cnstr_set(x_1, 1, x_7);
return x_1;
}
else
{
obj* x_9; 
lean::dec(x_7);
lean::free_heap_obj(x_1);
lean::dec(x_6);
lean::dec(x_4);
x_9 = l_Substring_drop___main___closed__2;
return x_9;
}
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_10 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_1);
x_13 = lean::nat_add(x_11, x_2);
lean::dec(x_11);
x_14 = lean::nat_dec_le(x_12, x_13);
if (x_14 == 0)
{
obj* x_15; 
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_13);
lean::cnstr_set(x_15, 2, x_12);
return x_15;
}
else
{
obj* x_16; 
lean::dec(x_13);
lean::dec(x_12);
lean::dec(x_10);
x_16 = l_Substring_drop___main___closed__2;
return x_16;
}
}
}
}
obj* l_Substring_drop___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Substring_drop(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Substring_dropRight___main(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::nat_sub(x_6, x_2);
x_8 = lean::nat_dec_le(x_7, x_6);
lean::dec(x_6);
if (x_8 == 0)
{
lean::cnstr_set(x_1, 2, x_7);
return x_1;
}
else
{
obj* x_9; 
lean::dec(x_7);
lean::free_heap_obj(x_1);
lean::dec(x_5);
lean::dec(x_4);
x_9 = l_Substring_drop___main___closed__2;
return x_9;
}
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_10 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_1);
x_13 = lean::nat_sub(x_12, x_2);
x_14 = lean::nat_dec_le(x_13, x_12);
lean::dec(x_12);
if (x_14 == 0)
{
obj* x_15; 
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_11);
lean::cnstr_set(x_15, 2, x_13);
return x_15;
}
else
{
obj* x_16; 
lean::dec(x_13);
lean::dec(x_11);
lean::dec(x_10);
x_16 = l_Substring_drop___main___closed__2;
return x_16;
}
}
}
}
obj* l_Substring_dropRight___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Substring_dropRight___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Substring_dropRight(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::nat_sub(x_6, x_2);
x_8 = lean::nat_dec_le(x_7, x_6);
lean::dec(x_6);
if (x_8 == 0)
{
lean::cnstr_set(x_1, 2, x_7);
return x_1;
}
else
{
obj* x_9; 
lean::dec(x_7);
lean::free_heap_obj(x_1);
lean::dec(x_5);
lean::dec(x_4);
x_9 = l_Substring_drop___main___closed__2;
return x_9;
}
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_10 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_1);
x_13 = lean::nat_sub(x_12, x_2);
x_14 = lean::nat_dec_le(x_13, x_12);
lean::dec(x_12);
if (x_14 == 0)
{
obj* x_15; 
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_11);
lean::cnstr_set(x_15, 2, x_13);
return x_15;
}
else
{
obj* x_16; 
lean::dec(x_13);
lean::dec(x_11);
lean::dec(x_10);
x_16 = l_Substring_drop___main___closed__2;
return x_16;
}
}
}
}
obj* l_Substring_dropRight___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Substring_dropRight(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Substring_take___main(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_1, 2);
x_6 = lean::nat_add(x_4, x_2);
x_7 = lean::nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean::dec(x_5);
lean::cnstr_set(x_1, 2, x_6);
return x_1;
}
else
{
lean::dec(x_6);
return x_1;
}
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::nat_add(x_9, x_2);
x_12 = lean::nat_dec_le(x_10, x_11);
if (x_12 == 0)
{
obj* x_13; 
lean::dec(x_10);
x_13 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_13, 0, x_8);
lean::cnstr_set(x_13, 1, x_9);
lean::cnstr_set(x_13, 2, x_11);
return x_13;
}
else
{
obj* x_14; 
lean::dec(x_11);
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_8);
lean::cnstr_set(x_14, 1, x_9);
lean::cnstr_set(x_14, 2, x_10);
return x_14;
}
}
}
}
obj* l_Substring_take___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Substring_take___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Substring_take(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_1, 2);
x_6 = lean::nat_add(x_4, x_2);
x_7 = lean::nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean::dec(x_5);
lean::cnstr_set(x_1, 2, x_6);
return x_1;
}
else
{
lean::dec(x_6);
return x_1;
}
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::nat_add(x_9, x_2);
x_12 = lean::nat_dec_le(x_10, x_11);
if (x_12 == 0)
{
obj* x_13; 
lean::dec(x_10);
x_13 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_13, 0, x_8);
lean::cnstr_set(x_13, 1, x_9);
lean::cnstr_set(x_13, 2, x_11);
return x_13;
}
else
{
obj* x_14; 
lean::dec(x_11);
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_8);
lean::cnstr_set(x_14, 1, x_9);
lean::cnstr_set(x_14, 2, x_10);
return x_14;
}
}
}
}
obj* l_Substring_take___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Substring_take(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Substring_takeRight___main(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_1, 2);
x_6 = lean::nat_sub(x_5, x_2);
x_7 = lean::nat_dec_le(x_6, x_4);
if (x_7 == 0)
{
lean::dec(x_4);
lean::cnstr_set(x_1, 1, x_6);
return x_1;
}
else
{
lean::dec(x_6);
return x_1;
}
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::nat_sub(x_10, x_2);
x_12 = lean::nat_dec_le(x_11, x_9);
if (x_12 == 0)
{
obj* x_13; 
lean::dec(x_9);
x_13 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_13, 0, x_8);
lean::cnstr_set(x_13, 1, x_11);
lean::cnstr_set(x_13, 2, x_10);
return x_13;
}
else
{
obj* x_14; 
lean::dec(x_11);
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_8);
lean::cnstr_set(x_14, 1, x_9);
lean::cnstr_set(x_14, 2, x_10);
return x_14;
}
}
}
}
obj* l_Substring_takeRight___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Substring_takeRight___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Substring_takeRight(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_1, 2);
x_6 = lean::nat_sub(x_5, x_2);
x_7 = lean::nat_dec_le(x_6, x_4);
if (x_7 == 0)
{
lean::dec(x_4);
lean::cnstr_set(x_1, 1, x_6);
return x_1;
}
else
{
lean::dec(x_6);
return x_1;
}
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::nat_sub(x_10, x_2);
x_12 = lean::nat_dec_le(x_11, x_9);
if (x_12 == 0)
{
obj* x_13; 
lean::dec(x_9);
x_13 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_13, 0, x_8);
lean::cnstr_set(x_13, 1, x_11);
lean::cnstr_set(x_13, 2, x_10);
return x_13;
}
else
{
obj* x_14; 
lean::dec(x_11);
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_8);
lean::cnstr_set(x_14, 1, x_9);
lean::cnstr_set(x_14, 2, x_10);
return x_14;
}
}
}
}
obj* l_Substring_takeRight___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Substring_takeRight(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
uint8 l_Substring_atEnd___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_1, 2);
x_5 = lean::nat_add(x_3, x_2);
x_6 = lean::nat_dec_eq(x_5, x_4);
lean::dec(x_5);
return x_6;
}
}
obj* l_Substring_atEnd___main___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Substring_atEnd___main(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Substring_atEnd(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_1, 2);
x_5 = lean::nat_add(x_3, x_2);
x_6 = lean::nat_dec_eq(x_5, x_4);
lean::dec(x_5);
return x_6;
}
}
obj* l_Substring_atEnd___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Substring_atEnd(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* _init_l_Substring_extract___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::mk_nat_obj(1u);
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 2, x_3);
return x_4;
}
}
obj* l_Substring_extract___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean::cnstr_get(x_1, 2);
lean::dec(x_7);
x_8 = lean::nat_dec_le(x_3, x_2);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::nat_add(x_6, x_2);
x_10 = lean::nat_add(x_6, x_3);
lean::dec(x_6);
lean::cnstr_set(x_1, 2, x_10);
lean::cnstr_set(x_1, 1, x_9);
return x_1;
}
else
{
obj* x_11; 
lean::free_heap_obj(x_1);
lean::dec(x_6);
lean::dec(x_5);
x_11 = l_Substring_extract___main___closed__1;
return x_11;
}
}
else
{
obj* x_12; obj* x_13; uint8 x_14; 
x_12 = lean::cnstr_get(x_1, 0);
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_1);
x_14 = lean::nat_dec_le(x_3, x_2);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::nat_add(x_13, x_2);
x_16 = lean::nat_add(x_13, x_3);
lean::dec(x_13);
x_17 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_17, 0, x_12);
lean::cnstr_set(x_17, 1, x_15);
lean::cnstr_set(x_17, 2, x_16);
return x_17;
}
else
{
obj* x_18; 
lean::dec(x_13);
lean::dec(x_12);
x_18 = l_Substring_extract___main___closed__1;
return x_18;
}
}
}
}
obj* l_Substring_extract___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Substring_extract___main(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Substring_extract(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean::cnstr_get(x_1, 2);
lean::dec(x_7);
x_8 = lean::nat_dec_le(x_3, x_2);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::nat_add(x_6, x_2);
x_10 = lean::nat_add(x_6, x_3);
lean::dec(x_6);
lean::cnstr_set(x_1, 2, x_10);
lean::cnstr_set(x_1, 1, x_9);
return x_1;
}
else
{
obj* x_11; 
lean::free_heap_obj(x_1);
lean::dec(x_6);
lean::dec(x_5);
x_11 = l_Substring_extract___main___closed__1;
return x_11;
}
}
else
{
obj* x_12; obj* x_13; uint8 x_14; 
x_12 = lean::cnstr_get(x_1, 0);
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_1);
x_14 = lean::nat_dec_le(x_3, x_2);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::nat_add(x_13, x_2);
x_16 = lean::nat_add(x_13, x_3);
lean::dec(x_13);
x_17 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_17, 0, x_12);
lean::cnstr_set(x_17, 1, x_15);
lean::cnstr_set(x_17, 2, x_16);
return x_17;
}
else
{
obj* x_18; 
lean::dec(x_13);
lean::dec(x_12);
x_18 = l_Substring_extract___main___closed__1;
return x_18;
}
}
}
}
obj* l_Substring_extract___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Substring_extract(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Substring_splitAux___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; 
x_8 = lean::nat_dec_eq(x_5, x_3);
if (x_8 == 0)
{
uint32 x_9; uint32 x_10; uint8 x_11; 
x_9 = lean::string_utf8_get(x_1, x_5);
x_10 = lean::string_utf8_get(x_2, x_6);
x_11 = x_9 == x_10;
if (x_11 == 0)
{
obj* x_12; obj* x_13; 
lean::dec(x_6);
x_12 = lean::string_utf8_next(x_1, x_5);
lean::dec(x_5);
x_13 = lean::mk_nat_obj(0u);
x_5 = x_12;
x_6 = x_13;
goto _start;
}
else
{
obj* x_15; obj* x_16; uint8 x_17; 
x_15 = lean::string_utf8_next(x_1, x_5);
lean::dec(x_5);
x_16 = lean::string_utf8_next(x_2, x_6);
lean::dec(x_6);
x_17 = lean::string_utf8_at_end(x_2, x_16);
if (x_17 == 0)
{
x_5 = x_15;
x_6 = x_16;
goto _start;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_19 = lean::nat_sub(x_15, x_16);
lean::dec(x_16);
lean::inc(x_1);
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_1);
lean::cnstr_set(x_20, 1, x_4);
lean::cnstr_set(x_20, 2, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_7);
x_22 = lean::mk_nat_obj(0u);
lean::inc(x_15);
x_4 = x_15;
x_5 = x_15;
x_6 = x_22;
x_7 = x_21;
goto _start;
}
}
}
else
{
uint8 x_24; 
x_24 = lean::string_utf8_at_end(x_2, x_6);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_6);
x_25 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_25, 0, x_1);
lean::cnstr_set(x_25, 1, x_4);
lean::cnstr_set(x_25, 2, x_5);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_7);
x_27 = l_List_reverse___rarg(x_26);
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_28 = lean::nat_sub(x_5, x_6);
lean::dec(x_6);
lean::dec(x_5);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_1);
lean::cnstr_set(x_29, 1, x_4);
lean::cnstr_set(x_29, 2, x_28);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_7);
x_31 = l_Substring_drop___main___closed__2;
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_30);
x_33 = l_List_reverse___rarg(x_32);
return x_33;
}
}
}
}
obj* l_Substring_splitAux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Substring_splitAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_3);
lean::dec(x_2);
return x_8;
}
}
obj* l_Substring_splitAux(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Substring_splitAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
obj* l_Substring_splitAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Substring_splitAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_3);
lean::dec(x_2);
return x_8;
}
}
obj* l_Substring_split(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = l_String_splitAux___main___closed__1;
x_4 = lean::string_dec_eq(x_2, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::box(0);
x_9 = lean::mk_nat_obj(0u);
lean::inc(x_7);
x_10 = l_Substring_splitAux___main(x_5, x_2, x_6, x_7, x_7, x_9, x_8);
lean::dec(x_6);
return x_10;
}
else
{
obj* x_11; obj* x_12; 
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_1);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
}
obj* l_Substring_split___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Substring_split(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Substring_foldl___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 2);
lean::inc(x_6);
lean::dec(x_3);
x_7 = l_String_foldlAux___main___rarg(x_1, x_4, x_6, x_5, x_2);
lean::dec(x_6);
lean::dec(x_4);
return x_7;
}
}
obj* l_Substring_foldl(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Substring_foldl___rarg), 3, 0);
return x_2;
}
}
obj* l_Substring_foldr___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_3, 0);
x_5 = lean::cnstr_get(x_3, 1);
x_6 = lean::cnstr_get(x_3, 2);
x_7 = l_String_foldrAux___main___rarg(x_1, x_2, x_4, x_6, x_5);
return x_7;
}
}
obj* l_Substring_foldr(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Substring_foldr___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Substring_foldr___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Substring_foldr___rarg(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
uint8 l_Substring_any(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 2);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_String_anyAux___main(x_3, x_5, x_2, x_4);
lean::dec(x_5);
lean::dec(x_3);
return x_6;
}
}
obj* l_Substring_any___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Substring_any(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_String_anyAux___main___at_Substring_all___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::nat_dec_eq(x_4, x_3);
if (x_5 == 0)
{
uint32 x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_6 = lean::string_utf8_get(x_2, x_4);
x_7 = lean::box_uint32(x_6);
lean::inc(x_1);
x_8 = lean::apply_1(x_1, x_7);
x_9 = lean::unbox(x_8);
lean::dec(x_8);
if (x_9 == 0)
{
uint8 x_10; 
lean::dec(x_4);
lean::dec(x_1);
x_10 = 1;
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::string_utf8_next(x_2, x_4);
lean::dec(x_4);
x_4 = x_11;
goto _start;
}
}
else
{
uint8 x_13; 
lean::dec(x_4);
lean::dec(x_1);
x_13 = 0;
return x_13;
}
}
}
uint8 l_Substring_all(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 2);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_String_anyAux___main___at_Substring_all___spec__1(x_2, x_3, x_5, x_4);
lean::dec(x_5);
lean::dec(x_3);
if (x_6 == 0)
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
obj* l_String_anyAux___main___at_Substring_all___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_String_anyAux___main___at_Substring_all___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
x_6 = lean::box(x_5);
return x_6;
}
}
obj* l_Substring_all___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Substring_all(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_String_anyAux___main___at_Substring_contains___spec__1(uint32 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::nat_dec_eq(x_4, x_3);
if (x_5 == 0)
{
uint32 x_6; uint8 x_7; 
x_6 = lean::string_utf8_get(x_2, x_4);
x_7 = x_6 == x_1;
if (x_7 == 0)
{
obj* x_8; 
x_8 = lean::string_utf8_next(x_2, x_4);
lean::dec(x_4);
x_4 = x_8;
goto _start;
}
else
{
uint8 x_10; 
lean::dec(x_4);
x_10 = 1;
return x_10;
}
}
else
{
uint8 x_11; 
lean::dec(x_4);
x_11 = 0;
return x_11;
}
}
}
uint8 l_Substring_contains(obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 2);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_String_anyAux___main___at_Substring_contains___spec__1(x_2, x_3, x_5, x_4);
lean::dec(x_5);
lean::dec(x_3);
return x_6;
}
}
obj* l_String_anyAux___main___at_Substring_contains___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; uint8 x_6; obj* x_7; 
x_5 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_6 = l_String_anyAux___main___at_Substring_contains___spec__1(x_5, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
x_7 = lean::box(x_6);
return x_7;
}
}
obj* l_Substring_contains___boxed(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; uint8 x_4; obj* x_5; 
x_3 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_4 = l_Substring_contains(x_1, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_Substring_takeWhileAux___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::nat_dec_eq(x_4, x_2);
if (x_5 == 0)
{
uint32 x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_6 = lean::string_utf8_get(x_1, x_4);
x_7 = lean::box_uint32(x_6);
lean::inc(x_3);
x_8 = lean::apply_1(x_3, x_7);
x_9 = lean::unbox(x_8);
lean::dec(x_8);
if (x_9 == 0)
{
lean::dec(x_3);
return x_4;
}
else
{
obj* x_10; 
x_10 = lean::string_utf8_next(x_1, x_4);
lean::dec(x_4);
x_4 = x_10;
goto _start;
}
}
else
{
lean::dec(x_3);
return x_4;
}
}
}
obj* l_Substring_takeWhileAux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Substring_takeWhileAux___main(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Substring_takeWhileAux(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Substring_takeWhileAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Substring_takeWhileAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Substring_takeWhileAux(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Substring_takeWhile___main(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_5);
x_7 = l_Substring_takeWhileAux___main(x_4, x_6, x_2, x_5);
lean::dec(x_6);
lean::cnstr_set(x_1, 2, x_7);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_9);
x_11 = l_Substring_takeWhileAux___main(x_8, x_10, x_2, x_9);
lean::dec(x_10);
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_9);
lean::cnstr_set(x_12, 2, x_11);
return x_12;
}
}
}
obj* l_Substring_takeWhile(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_5);
x_7 = l_Substring_takeWhileAux___main(x_4, x_6, x_2, x_5);
lean::dec(x_6);
lean::cnstr_set(x_1, 2, x_7);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_9);
x_11 = l_Substring_takeWhileAux___main(x_8, x_10, x_2, x_9);
lean::dec(x_10);
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_9);
lean::cnstr_set(x_12, 2, x_11);
return x_12;
}
}
}
obj* l_Substring_dropWhile___main(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = l_Substring_takeWhileAux___main(x_4, x_6, x_2, x_5);
lean::cnstr_set(x_1, 1, x_7);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_11 = l_Substring_takeWhileAux___main(x_8, x_10, x_2, x_9);
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_11);
lean::cnstr_set(x_12, 2, x_10);
return x_12;
}
}
}
obj* l_Substring_dropWhile(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = l_Substring_takeWhileAux___main(x_4, x_6, x_2, x_5);
lean::cnstr_set(x_1, 1, x_7);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_11 = l_Substring_takeWhileAux___main(x_8, x_10, x_2, x_9);
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_11);
lean::cnstr_set(x_12, 2, x_10);
return x_12;
}
}
}
obj* l_Substring_takeRightWhileAux___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::nat_dec_eq(x_4, x_2);
if (x_5 == 0)
{
obj* x_6; uint32 x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_6 = lean::string_utf8_prev(x_1, x_4);
x_7 = lean::string_utf8_get(x_1, x_6);
x_8 = lean::box_uint32(x_7);
lean::inc(x_3);
x_9 = lean::apply_1(x_3, x_8);
x_10 = lean::unbox(x_9);
lean::dec(x_9);
if (x_10 == 0)
{
lean::dec(x_6);
lean::dec(x_3);
return x_4;
}
else
{
lean::dec(x_4);
x_4 = x_6;
goto _start;
}
}
else
{
lean::dec(x_3);
return x_4;
}
}
}
obj* l_Substring_takeRightWhileAux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Substring_takeRightWhileAux___main(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Substring_takeRightWhileAux(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Substring_takeRightWhileAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Substring_takeRightWhileAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Substring_takeRightWhileAux(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Substring_takeRightWhile___main(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_7 = l_Substring_takeRightWhileAux___main(x_4, x_5, x_2, x_6);
lean::dec(x_5);
lean::cnstr_set(x_1, 1, x_7);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_10);
x_11 = l_Substring_takeRightWhileAux___main(x_8, x_9, x_2, x_10);
lean::dec(x_9);
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_11);
lean::cnstr_set(x_12, 2, x_10);
return x_12;
}
}
}
obj* l_Substring_takeRightWhile(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_7 = l_Substring_takeRightWhileAux___main(x_4, x_5, x_2, x_6);
lean::dec(x_5);
lean::cnstr_set(x_1, 1, x_7);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_10);
x_11 = l_Substring_takeRightWhileAux___main(x_8, x_9, x_2, x_10);
lean::dec(x_9);
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_11);
lean::cnstr_set(x_12, 2, x_10);
return x_12;
}
}
}
obj* l_Substring_dropRightWhile___main(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = l_Substring_takeRightWhileAux___main(x_4, x_5, x_2, x_6);
lean::cnstr_set(x_1, 2, x_7);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_11 = l_Substring_takeRightWhileAux___main(x_8, x_9, x_2, x_10);
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_9);
lean::cnstr_set(x_12, 2, x_11);
return x_12;
}
}
}
obj* l_Substring_dropRightWhile(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = l_Substring_takeRightWhileAux___main(x_4, x_5, x_2, x_6);
lean::cnstr_set(x_1, 2, x_7);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_11 = l_Substring_takeRightWhileAux___main(x_8, x_9, x_2, x_10);
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_9);
lean::cnstr_set(x_12, 2, x_11);
return x_12;
}
}
}
obj* l_Substring_takeWhileAux___main___at_Substring_trimLeft___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::nat_dec_eq(x_3, x_2);
if (x_4 == 0)
{
uint32 x_5; uint8 x_6; 
x_5 = lean::string_utf8_get(x_1, x_3);
x_6 = l_Char_isWhitespace(x_5);
if (x_6 == 0)
{
return x_3;
}
else
{
obj* x_7; 
x_7 = lean::string_utf8_next(x_1, x_3);
lean::dec(x_3);
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
obj* l_Substring_trimLeft(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_1, 2);
x_6 = l_Substring_takeWhileAux___main___at_Substring_trimLeft___spec__1(x_3, x_5, x_4);
lean::cnstr_set(x_1, 1, x_6);
return x_1;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_1, 0);
x_8 = lean::cnstr_get(x_1, 1);
x_9 = lean::cnstr_get(x_1, 2);
lean::inc(x_9);
lean::inc(x_8);
lean::inc(x_7);
lean::dec(x_1);
x_10 = l_Substring_takeWhileAux___main___at_Substring_trimLeft___spec__1(x_7, x_9, x_8);
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_7);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set(x_11, 2, x_9);
return x_11;
}
}
}
obj* l_Substring_takeWhileAux___main___at_Substring_trimLeft___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Substring_takeWhileAux___main___at_Substring_trimLeft___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Substring_takeRightWhileAux___main___at_Substring_trimRight___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::nat_dec_eq(x_3, x_2);
if (x_4 == 0)
{
obj* x_5; uint32 x_6; uint8 x_7; 
x_5 = lean::string_utf8_prev(x_1, x_3);
x_6 = lean::string_utf8_get(x_1, x_5);
x_7 = l_Char_isWhitespace(x_6);
if (x_7 == 0)
{
lean::dec(x_5);
return x_3;
}
else
{
lean::dec(x_3);
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
obj* l_Substring_trimRight(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_1, 2);
x_6 = l_Substring_takeRightWhileAux___main___at_Substring_trimRight___spec__1(x_3, x_4, x_5);
lean::cnstr_set(x_1, 2, x_6);
return x_1;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_1, 0);
x_8 = lean::cnstr_get(x_1, 1);
x_9 = lean::cnstr_get(x_1, 2);
lean::inc(x_9);
lean::inc(x_8);
lean::inc(x_7);
lean::dec(x_1);
x_10 = l_Substring_takeRightWhileAux___main___at_Substring_trimRight___spec__1(x_7, x_8, x_9);
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_7);
lean::cnstr_set(x_11, 1, x_8);
lean::cnstr_set(x_11, 2, x_10);
return x_11;
}
}
}
obj* l_Substring_takeRightWhileAux___main___at_Substring_trimRight___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Substring_takeRightWhileAux___main___at_Substring_trimRight___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Substring_trim___main(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_1, 2);
x_6 = l_Substring_takeWhileAux___main___at_Substring_trimLeft___spec__1(x_3, x_5, x_4);
x_7 = l_Substring_takeRightWhileAux___main___at_Substring_trimRight___spec__1(x_3, x_6, x_5);
lean::cnstr_set(x_1, 2, x_7);
lean::cnstr_set(x_1, 1, x_6);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_11 = l_Substring_takeWhileAux___main___at_Substring_trimLeft___spec__1(x_8, x_10, x_9);
x_12 = l_Substring_takeRightWhileAux___main___at_Substring_trimRight___spec__1(x_8, x_11, x_10);
x_13 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_13, 0, x_8);
lean::cnstr_set(x_13, 1, x_11);
lean::cnstr_set(x_13, 2, x_12);
return x_13;
}
}
}
obj* l_Substring_trim(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_1, 2);
x_6 = l_Substring_takeWhileAux___main___at_Substring_trimLeft___spec__1(x_3, x_5, x_4);
x_7 = l_Substring_takeRightWhileAux___main___at_Substring_trimRight___spec__1(x_3, x_6, x_5);
lean::cnstr_set(x_1, 2, x_7);
lean::cnstr_set(x_1, 1, x_6);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_11 = l_Substring_takeWhileAux___main___at_Substring_trimLeft___spec__1(x_8, x_10, x_9);
x_12 = l_Substring_takeRightWhileAux___main___at_Substring_trimRight___spec__1(x_8, x_11, x_10);
x_13 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_13, 0, x_8);
lean::cnstr_set(x_13, 1, x_11);
lean::cnstr_set(x_13, 2, x_12);
return x_13;
}
}
}
obj* l_Substring_toNat(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::mk_nat_obj(0u);
x_6 = l_String_foldlAux___main___at_String_toNat___spec__1(x_2, x_4, x_3, x_5);
lean::dec(x_4);
lean::dec(x_2);
return x_6;
}
}
uint8 l_Substring_isNat(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; uint8 x_5; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
lean::dec(x_1);
x_5 = l_String_anyAux___main___at_String_isNat___spec__1(x_2, x_4, x_3);
lean::dec(x_4);
lean::dec(x_2);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
}
}
obj* l_Substring_isNat___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Substring_isNat(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _init_l_String_drop___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Substring_drop___main___closed__1;
x_4 = lean::string_utf8_extract(x_1, x_2, x_3);
return x_4;
}
}
obj* l_String_drop(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::string_utf8_byte_size(x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_add(x_4, x_2);
x_6 = lean::nat_dec_le(x_3, x_5);
if (x_6 == 0)
{
obj* x_7; 
x_7 = lean::string_utf8_extract(x_1, x_5, x_3);
lean::dec(x_3);
lean::dec(x_5);
return x_7;
}
else
{
obj* x_8; 
lean::dec(x_5);
lean::dec(x_3);
x_8 = l_String_drop___closed__1;
return x_8;
}
}
}
obj* l_String_drop___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_String_drop(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_String_dropRight(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::string_utf8_byte_size(x_1);
x_4 = lean::nat_sub(x_3, x_2);
x_5 = lean::nat_dec_le(x_4, x_3);
lean::dec(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::string_utf8_extract(x_1, x_6, x_4);
lean::dec(x_4);
return x_7;
}
else
{
obj* x_8; 
lean::dec(x_4);
x_8 = l_String_drop___closed__1;
return x_8;
}
}
}
obj* l_String_dropRight___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_String_dropRight(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_String_take(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::string_utf8_byte_size(x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_add(x_4, x_2);
x_6 = lean::nat_dec_le(x_3, x_5);
if (x_6 == 0)
{
obj* x_7; 
lean::dec(x_3);
x_7 = lean::string_utf8_extract(x_1, x_4, x_5);
lean::dec(x_5);
return x_7;
}
else
{
obj* x_8; 
lean::dec(x_5);
x_8 = lean::string_utf8_extract(x_1, x_4, x_3);
lean::dec(x_3);
return x_8;
}
}
}
obj* l_String_take___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_String_take(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_String_takeRight(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::string_utf8_byte_size(x_1);
x_4 = lean::nat_sub(x_3, x_2);
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_le(x_4, x_5);
if (x_6 == 0)
{
obj* x_7; 
x_7 = lean::string_utf8_extract(x_1, x_4, x_3);
lean::dec(x_3);
lean::dec(x_4);
return x_7;
}
else
{
obj* x_8; 
lean::dec(x_4);
x_8 = lean::string_utf8_extract(x_1, x_5, x_3);
lean::dec(x_3);
return x_8;
}
}
}
obj* l_String_takeRight___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_String_takeRight(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_String_takeWhile(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::string_utf8_byte_size(x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Substring_takeWhileAux___main(x_1, x_3, x_2, x_4);
lean::dec(x_3);
x_6 = lean::string_utf8_extract(x_1, x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l_String_takeWhile___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_String_takeWhile(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_String_dropWhile(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::string_utf8_byte_size(x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Substring_takeWhileAux___main(x_1, x_3, x_2, x_4);
x_6 = lean::string_utf8_extract(x_1, x_5, x_3);
lean::dec(x_3);
lean::dec(x_5);
return x_6;
}
}
obj* l_String_dropWhile___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_String_dropWhile(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_String_trimRight(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_utf8_byte_size(x_1);
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Substring_takeRightWhileAux___main___at_Substring_trimRight___spec__1(x_1, x_3, x_2);
x_5 = lean::string_utf8_extract(x_1, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_String_trimRight___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_trimRight(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_String_trimLeft(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_utf8_byte_size(x_1);
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Substring_takeWhileAux___main___at_Substring_trimLeft___spec__1(x_1, x_2, x_3);
x_5 = lean::string_utf8_extract(x_1, x_4, x_2);
lean::dec(x_2);
lean::dec(x_4);
return x_5;
}
}
obj* l_String_trimLeft___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_trimLeft(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_String_trim(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::string_utf8_byte_size(x_1);
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Substring_takeWhileAux___main___at_Substring_trimLeft___spec__1(x_1, x_2, x_3);
x_5 = l_Substring_takeRightWhileAux___main___at_Substring_trimRight___spec__1(x_1, x_4, x_2);
x_6 = lean::string_utf8_extract(x_1, x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
return x_6;
}
}
obj* l_String_trim___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Char_toString(uint32 x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean::string_push(x_2, x_1);
return x_3;
}
}
obj* l_Char_toString___boxed(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_3 = l_Char_toString(x_2);
return x_3;
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
if (io_result_is_error(w)) return w;
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "mk"), 1, l_String_mk___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "data"), 1, l_String_data___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "decEq"), 2, l_String_decEq___boxed);
l_String_DecidableEq___closed__1 = _init_l_String_DecidableEq___closed__1();
lean::mark_persistent(l_String_DecidableEq___closed__1);
l_String_DecidableEq = _init_l_String_DecidableEq();
lean::mark_persistent(l_String_DecidableEq);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("String"), "DecidableEq"), l_String_DecidableEq);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("List"), "asString"), 1, l_List_asString);
l_String_HasLess = _init_l_String_HasLess();
lean::mark_persistent(l_String_HasLess);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("String"), "HasLess"), l_String_HasLess);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "decLt"), 2, l_String_decLt___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "length"), 1, l_String_length___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "push"), 2, l_String_push___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "append"), 2, l_String_append___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "toList"), 1, l_String_toList);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "utf8ByteSize"), 1, l_String_utf8ByteSize___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "bsize"), 1, l_String_bsize___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "toSubstring"), 1, l_String_toSubstring);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "get"), 2, l_String_get___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "set"), 3, l_String_set___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "next"), 2, l_String_next___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "prev"), 2, l_String_prev___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "front"), 1, l_String_front___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "back"), 1, l_String_back___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "atEnd"), 2, l_String_atEnd___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "posOfAux"), 4, l_String_posOfAux___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "posOf"), 2, l_String_posOf___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "extract"), 3, l_String_extract___boxed);
l_String_splitAux___main___closed__1 = _init_l_String_splitAux___main___closed__1();
lean::mark_persistent(l_String_splitAux___main___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "splitAux"), 6, l_String_splitAux___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "split"), 2, l_String_split___boxed);
l_String_Inhabited = _init_l_String_Inhabited();
lean::mark_persistent(l_String_Inhabited);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("String"), "Inhabited"), l_String_Inhabited);
l_String_HasSizeof___closed__1 = _init_l_String_HasSizeof___closed__1();
lean::mark_persistent(l_String_HasSizeof___closed__1);
l_String_HasSizeof = _init_l_String_HasSizeof();
lean::mark_persistent(l_String_HasSizeof);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("String"), "HasSizeof"), l_String_HasSizeof);
l_String_HasAppend___closed__1 = _init_l_String_HasAppend___closed__1();
lean::mark_persistent(l_String_HasAppend___closed__1);
l_String_HasAppend = _init_l_String_HasAppend();
lean::mark_persistent(l_String_HasAppend);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("String"), "HasAppend"), l_String_HasAppend);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "str"), 2, l_String_str___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "pushn"), 3, l_String_pushn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "isEmpty"), 1, l_String_isEmpty___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "join"), 1, l_String_join___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "singleton"), 1, l_String_singleton___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "intercalate"), 2, l_String_intercalate);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "mkIterator"), 1, l_String_mkIterator);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("String"), "Iterator"), "toString"), 1, l_String_Iterator_toString___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("String"), "Iterator"), "remainingBytes"), 1, l_String_Iterator_remainingBytes___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("String"), "Iterator"), "pos"), 1, l_String_Iterator_pos___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("String"), "Iterator"), "curr"), 1, l_String_Iterator_curr___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("String"), "Iterator"), "next"), 1, l_String_Iterator_next);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("String"), "Iterator"), "prev"), 1, l_String_Iterator_prev);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("String"), "Iterator"), "hasNext"), 1, l_String_Iterator_hasNext___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("String"), "Iterator"), "hasPrev"), 1, l_String_Iterator_hasPrev___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("String"), "Iterator"), "setCurr"), 2, l_String_Iterator_setCurr___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("String"), "Iterator"), "toEnd"), 1, l_String_Iterator_toEnd);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("String"), "Iterator"), "extract"), 2, l_String_Iterator_extract___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("String"), "Iterator"), "forward"), 2, l_String_Iterator_forward);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("String"), "Iterator"), "remainingToString"), 1, l_String_Iterator_remainingToString___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("String"), "Iterator"), "isPrefixOfRemaining"), 2, l_String_Iterator_isPrefixOfRemaining___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("String"), "Iterator"), "nextn"), 2, l_String_Iterator_nextn);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("String"), "Iterator"), "prevn"), 2, l_String_Iterator_prevn);
l_String_lineColumn___closed__1 = _init_l_String_lineColumn___closed__1();
lean::mark_persistent(l_String_lineColumn___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "lineColumn"), 2, l_String_lineColumn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "offsetOfPosAux"), 4, l_String_offsetOfPosAux___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "offsetOfPos"), 2, l_String_offsetOfPos___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "foldlAux"), 1, l_String_foldlAux);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "foldl"), 1, l_String_foldl);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "foldrAux"), 1, l_String_foldrAux);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "foldr"), 1, l_String_foldr);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "anyAux"), 4, l_String_anyAux___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "any"), 2, l_String_any___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "all"), 2, l_String_all___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "contains"), 2, l_String_contains___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "mapAux"), 3, l_String_mapAux);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "map"), 2, l_String_map);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "toNat"), 1, l_String_toNat___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "isNat"), 1, l_String_isNat___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "isPrefixOfAux"), 3, l_String_isPrefixOfAux___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "isPrefixOf"), 2, l_String_isPrefixOf___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "toString"), 1, l_Substring_toString___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "toIterator"), 1, l_Substring_toIterator___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "get"), 2, l_Substring_get___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "next"), 2, l_Substring_next___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "prev"), 2, l_Substring_prev___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "front"), 1, l_Substring_front___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "posOf"), 2, l_Substring_posOf___boxed);
l_Substring_drop___main___closed__1 = _init_l_Substring_drop___main___closed__1();
lean::mark_persistent(l_Substring_drop___main___closed__1);
l_Substring_drop___main___closed__2 = _init_l_Substring_drop___main___closed__2();
lean::mark_persistent(l_Substring_drop___main___closed__2);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "drop"), 2, l_Substring_drop___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "dropRight"), 2, l_Substring_dropRight___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "take"), 2, l_Substring_take___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "takeRight"), 2, l_Substring_takeRight___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "atEnd"), 2, l_Substring_atEnd___boxed);
l_Substring_extract___main___closed__1 = _init_l_Substring_extract___main___closed__1();
lean::mark_persistent(l_Substring_extract___main___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "extract"), 3, l_Substring_extract___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "splitAux"), 7, l_Substring_splitAux___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "split"), 2, l_Substring_split___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "foldl"), 1, l_Substring_foldl);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "foldr"), 1, l_Substring_foldr);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "any"), 2, l_Substring_any___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "all"), 2, l_Substring_all___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "contains"), 2, l_Substring_contains___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "takeWhileAux"), 4, l_Substring_takeWhileAux___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "takeWhile"), 2, l_Substring_takeWhile);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "dropWhile"), 2, l_Substring_dropWhile);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "takeRightWhileAux"), 4, l_Substring_takeRightWhileAux___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "takeRightWhile"), 2, l_Substring_takeRightWhile);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "dropRightWhile"), 2, l_Substring_dropRightWhile);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "trimLeft"), 1, l_Substring_trimLeft);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "trimRight"), 1, l_Substring_trimRight);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "trim"), 1, l_Substring_trim);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "toNat"), 1, l_Substring_toNat);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Substring"), "isNat"), 1, l_Substring_isNat___boxed);
l_String_drop___closed__1 = _init_l_String_drop___closed__1();
lean::mark_persistent(l_String_drop___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "drop"), 2, l_String_drop___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "dropRight"), 2, l_String_dropRight___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "take"), 2, l_String_take___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "takeRight"), 2, l_String_takeRight___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "takeWhile"), 2, l_String_takeWhile___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "dropWhile"), 2, l_String_dropWhile___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "trimRight"), 1, l_String_trimRight___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "trimLeft"), 1, l_String_trimLeft___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("String"), "trim"), 1, l_String_trim___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Char"), "toString"), 1, l_Char_toString___boxed);
return w;
}
