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
obj* l_String_utf8ByteSize___boxed(obj*);
uint32 l_String_Iterator_curr___main(obj*);
obj* l_String_Iterator_extract(obj*, obj*);
obj* l_String_utf8AtEnd___boxed(obj*, obj*);
obj* l_String_mkIterator(obj*);
obj* l___private_init_data_string_basic_2__utf8ByteSizeAux___main___boxed(obj*, obj*);
obj* l___private_init_data_string_basic_4__utf8SetAux(uint32, obj*, usize, usize);
obj* l_String_Iterator_hasPrev___main___boxed(obj*);
obj* l_List_asString(obj*);
usize l_String_trimRightAux(obj*, obj*, usize);
obj* l_List_foldl___main___at_String_join___spec__1___boxed(obj*, obj*);
obj* l___private_init_data_string_basic_4__utf8SetAux___main___boxed(obj*, obj*, obj*, obj*);
obj* l_String_singleton___boxed(obj*);
obj* l_String_front___boxed(obj*);
obj* l___private_init_data_string_basic_9__toNatCore(obj*, obj*, obj*);
obj* l_String_Iterator_prevn(obj*, obj*);
obj* l_String_Iterator_extract___main___boxed(obj*, obj*);
obj* l___private_init_data_string_basic_9__toNatCore___main___closed__1;
obj* l_String_join___boxed(obj*);
obj* l_String_Iterator_remainingToString___main(obj*);
obj* l_String_Iterator_setCurr___main___boxed(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_String_toNat(obj*);
namespace lean {
uint32 string_utf8_get(obj*, usize);
}
obj* l_String_utf8Set___boxed(obj*, obj*, obj*);
obj* l_String_trimRightAux___main___boxed(obj*, obj*, obj*);
uint8 l_String_isEmpty(obj*);
obj* l_String_trim___boxed(obj*);
namespace lean {
usize string_utf8_prev(obj*, usize);
}
obj* l_String_intercalate(obj*, obj*);
obj* l_String_lineColumn(obj*, obj*);
obj* l_String_Iterator_hasPrev___boxed(obj*);
usize l_String_utf8Begin;
obj* l_String_Iterator_extract___main(obj*, obj*);
obj* l_String_trimRightAux___boxed(obj*, obj*, obj*);
obj* l___private_init_data_string_basic_9__toNatCore___main(obj*, obj*, obj*);
obj* l_String_Iterator_toString___main___boxed(obj*);
uint8 l_String_Iterator_hasPrev___main(obj*);
obj* l_Char_toString___boxed(obj*);
obj* l_String_push___boxed(obj*, obj*);
obj* l_String_utf8Get___boxed(obj*, obj*);
obj* l_String_Iterator_remaining___main___boxed(obj*);
obj* l___private_init_data_string_basic_4__utf8SetAux___main(uint32, obj*, usize, usize);
obj* l___private_init_data_string_basic_7__utf8ExtractAux_u_2081(obj*, usize, usize, usize);
obj* l___private_init_data_string_basic_6__utf8ExtractAux_u_2082(obj*, usize, usize);
obj* l_String_Iterator_isPrefixOfRemaining___boxed(obj*, obj*);
usize l_String_Iterator_remainingBytes___main(obj*);
obj* l_String_trimLeftAux___boxed(obj*, obj*, obj*);
obj* l_String_pushn___boxed(obj*, obj*, obj*);
obj* l___private_init_data_string_basic_2__utf8ByteSizeAux___boxed(obj*, obj*);
uint8 l_String_Iterator_hasNext(obj*);
obj* l_String_HasAppend;
obj* l_String_Iterator_prev___main(obj*);
obj* l_String_Iterator_forward___main(obj*, obj*);
uint8 l_String_Iterator_isPrefixOfRemaining(obj*, obj*);
obj* l_String_Inhabited;
obj* l___private_init_data_string_basic_8__lineColumnAux(obj*, obj*, obj*);
obj* l___private_init_data_string_basic_8__lineColumnAux___main(obj*, obj*, obj*);
usize l___private_init_data_string_basic_1__csize(uint32);
obj* l_String_Iterator_prevn___main(obj*, obj*);
obj* l___private_init_data_string_basic_4__utf8SetAux___boxed(obj*, obj*, obj*, obj*);
obj* l_String_back___boxed(obj*);
obj* l_String_Iterator_hasNext___main___boxed(obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_String_Iterator_toString(obj*);
obj* l___private_init_data_string_basic_6__utf8ExtractAux_u_2082___main(obj*, usize, usize);
obj* l_Char_toString(uint32);
obj* l_String_Iterator_remaining___main(obj*);
obj* l_String_Iterator_next(obj*);
obj* l_String_Iterator_hasNext___boxed(obj*);
usize l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1;
usize l___private_init_data_string_basic_5__utf8PrevAux(obj*, usize, usize);
usize l___private_init_data_string_basic_5__utf8PrevAux___main(obj*, usize, usize);
obj* l_String_Iterator_next___main(obj*);
obj* l___private_init_data_string_basic_7__utf8ExtractAux_u_2081___main(obj*, usize, usize, usize);
namespace lean {
obj* string_append(obj*, obj*);
}
namespace lean {
uint8 string_dec_lt(obj*, obj*);
}
obj* l_String_Iterator_setCurr___boxed(obj*, obj*);
obj* l_String_decEq___boxed(obj*, obj*);
obj* l_String_Iterator_prev(obj*);
obj* l_String_str(obj*, uint32);
usize l_String_bsize(obj*);
obj* l_String_Iterator_remainingToString___boxed(obj*);
obj* l_String_Iterator_nextn(obj*, obj*);
obj* l_String_Iterator_curr___main___boxed(obj*);
obj* l_String_Iterator_toString___boxed(obj*);
obj* l_String_trimLeftAux___main___boxed(obj*, obj*, obj*);
obj* l_String_Iterator_remainingToString___main___boxed(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_String_join(obj*);
obj* l_String_Iterator_remainingBytes___main___boxed(obj*);
obj* l_String_HasLt;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_String_append___boxed(obj*, obj*);
namespace lean {
uint8 string_utf8_at_end(obj*, usize);
}
obj* l___private_init_data_string_basic_5__utf8PrevAux___boxed(obj*, obj*, obj*);
obj* l_String_Iterator_nextn___main(obj*, obj*);
obj* l_String_isEmpty___boxed(obj*);
obj* l_Nat_repeatCore___main___at_String_pushn___spec__1(uint32, obj*, obj*, obj*);
obj* l_List_map___main___at_String_intercalate___spec__1(obj*);
obj* l_String_toList(obj*);
obj* l_String_utf8Begin___boxed;
obj* l_String_trimRight___boxed(obj*);
obj* l_String_singleton(uint32);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
usize l_String_trimRightAux___main(obj*, obj*, usize);
obj* l_String_Iterator_remaining___boxed(obj*);
obj* l_String_Iterator_forward(obj*, obj*);
obj* l_String_Iterator_isPrefixOfRemaining___main___boxed(obj*, obj*);
obj* l_String_decLt___boxed(obj*, obj*);
obj* l_String_DecidableEq;
obj* l_String_trim(obj*);
obj* l___private_init_data_string_basic_6__utf8ExtractAux_u_2082___boxed(obj*, obj*, obj*);
obj* l_String_utf8Next___boxed(obj*, obj*);
obj* l___private_init_data_string_basic_1__csize___boxed(obj*);
namespace lean {
obj* string_data(obj*);
}
obj* l_String_extract___boxed(obj*, obj*, obj*);
uint32 l_String_Iterator_curr(obj*);
obj* l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1___boxed;
obj* l_String_pushn(obj*, uint32, obj*);
obj* l_String_utf8Prev___boxed(obj*, obj*);
obj* l___private_init_data_string_basic_3__utf8GetAux___boxed(obj*, obj*, obj*);
uint8 l_Char_isWhitespace(uint32);
obj* l_String_Iterator_remainingBytes___boxed(obj*);
uint32 l___private_init_data_string_basic_3__utf8GetAux(obj*, usize, usize);
obj* l_String_HasSizeof;
uint32 l_String_front(obj*);
uint32 l___private_init_data_string_basic_3__utf8GetAux___main(obj*, usize, usize);
obj* l_List_intercalate___rarg(obj*, obj*);
usize l___private_init_data_string_basic_2__utf8ByteSizeAux___main(obj*, usize);
obj* l___private_init_data_string_basic_6__utf8ExtractAux_u_2082___main___boxed(obj*, obj*, obj*);
uint32 l_Char_utf8Size(uint32);
obj* l_String_Iterator_toEnd___main(obj*);
obj* l_String_Iterator_remaining(obj*);
obj* l___private_init_data_string_basic_3__utf8GetAux___main___boxed(obj*, obj*, obj*);
obj* l_String_Iterator_extract___boxed(obj*, obj*);
obj* l___private_init_data_string_basic_7__utf8ExtractAux_u_2081___main___boxed(obj*, obj*, obj*, obj*);
namespace lean {
uint32 uint32_of_nat(obj*);
}
uint8 l_String_Iterator_hasNext___main(obj*);
namespace lean {
obj* string_utf8_extract(obj*, usize, usize);
}
namespace lean {
usize usize_of_nat(obj*);
}
namespace lean {
obj* string_mk(obj*);
}
obj* l_String_Iterator_curr___boxed(obj*);
namespace lean {
usize string_utf8_byte_size(obj*);
}
usize l_String_trimLeftAux(obj*, obj*, usize);
obj* l_String_Iterator_toString___main(obj*);
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l___private_init_data_string_basic_5__utf8PrevAux___main___boxed(obj*, obj*, obj*);
obj* l_String_trimLeft___boxed(obj*);
namespace lean {
usize string_utf8_next(obj*, usize);
}
uint8 l_String_Iterator_hasPrev(obj*);
namespace lean {
obj* string_utf8_set(obj*, usize, uint32);
}
obj* l_List_foldl___main___at_String_join___spec__1(obj*, obj*);
usize l_String_trimLeftAux___main(obj*, obj*, usize);
obj* l_String_Iterator_setCurr(obj*, uint32);
obj* l_Nat_repeatCore___main___at_String_pushn___spec__1___boxed(obj*, obj*, obj*, obj*);
namespace lean {
obj* usize_to_nat(usize);
}
obj* l_String_Iterator_toEnd(obj*);
obj* l_String_bsize___boxed(obj*);
namespace lean {
obj* nat_mul(obj*, obj*);
}
uint8 l_String_Iterator_isPrefixOfRemaining___main(obj*, obj*);
obj* l_String_Iterator_setCurr___main(obj*, uint32);
obj* l___private_init_data_string_basic_7__utf8ExtractAux_u_2081___boxed(obj*, obj*, obj*, obj*);
obj* l_String_str___boxed(obj*, obj*);
obj* l_String_trimLeft(obj*);
usize l___private_init_data_string_basic_2__utf8ByteSizeAux(obj*, usize);
obj* l_String_Iterator_extract___main___closed__1;
obj* l_String_length___boxed(obj*);
obj* l_String_lineColumn___closed__1;
obj* l_String_trimRight(obj*);
uint32 l_String_back(obj*);
usize l_String_Iterator_remainingBytes(obj*);
obj* l_String_Iterator_remainingToString(obj*);
namespace lean {
obj* string_length(obj*);
}
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
obj* _init_l_String_HasLt() {
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
usize l___private_init_data_string_basic_1__csize(uint32 x_0) {
_start:
{
uint32 x_1; usize x_2; 
x_1 = l_Char_utf8Size(x_0);
x_2 = x_1;
return x_2;
}
}
obj* l___private_init_data_string_basic_1__csize___boxed(obj* x_0) {
_start:
{
uint32 x_1; usize x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l___private_init_data_string_basic_1__csize(x_1);
x_3 = lean::box_size_t(x_2);
return x_3;
}
}
usize l___private_init_data_string_basic_2__utf8ByteSizeAux___main(obj* x_0, usize x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
return x_1;
}
else
{
obj* x_2; obj* x_3; uint32 x_4; usize x_5; usize x_6; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = lean::unbox_uint32(x_2);
x_5 = l___private_init_data_string_basic_1__csize(x_4);
x_6 = x_1 + x_5;
x_0 = x_3;
x_1 = x_6;
goto _start;
}
}
}
obj* l___private_init_data_string_basic_2__utf8ByteSizeAux___main___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_1);
x_3 = l___private_init_data_string_basic_2__utf8ByteSizeAux___main(x_0, x_2);
x_4 = lean::box_size_t(x_3);
lean::dec(x_0);
return x_4;
}
}
usize l___private_init_data_string_basic_2__utf8ByteSizeAux(obj* x_0, usize x_1) {
_start:
{
usize x_2; 
x_2 = l___private_init_data_string_basic_2__utf8ByteSizeAux___main(x_0, x_1);
return x_2;
}
}
obj* l___private_init_data_string_basic_2__utf8ByteSizeAux___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_1);
x_3 = l___private_init_data_string_basic_2__utf8ByteSizeAux(x_0, x_2);
x_4 = lean::box_size_t(x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_String_utf8ByteSize___boxed(obj* x_0) {
_start:
{
usize x_1; obj* x_2; 
x_1 = lean::string_utf8_byte_size(x_0);
x_2 = lean::box_size_t(x_1);
lean::dec(x_0);
return x_2;
}
}
usize l_String_bsize(obj* x_0) {
_start:
{
usize x_1; 
x_1 = lean::string_utf8_byte_size(x_0);
return x_1;
}
}
obj* l_String_bsize___boxed(obj* x_0) {
_start:
{
usize x_1; obj* x_2; 
x_1 = l_String_bsize(x_0);
x_2 = lean::box_size_t(x_1);
lean::dec(x_0);
return x_2;
}
}
usize _init_l_String_utf8Begin() {
_start:
{
obj* x_0; usize x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::usize_of_nat(x_0);
return x_1;
}
}
obj* _init_l_String_utf8Begin___boxed() {
_start:
{
usize x_0; obj* x_1; 
x_0 = l_String_utf8Begin;
x_1 = lean::box_size_t(x_0);
return x_1;
}
}
uint32 l___private_init_data_string_basic_3__utf8GetAux___main(obj* x_0, usize x_1, usize x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint32 x_3; 
x_3 = 65;
return x_3;
}
else
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_0, 0);
x_5 = lean::cnstr_get(x_0, 1);
x_6 = x_1 == x_2;
if (x_6 == 0)
{
uint32 x_7; usize x_8; usize x_9; 
x_7 = lean::unbox_uint32(x_4);
x_8 = l___private_init_data_string_basic_1__csize(x_7);
x_9 = x_1 + x_8;
x_0 = x_5;
x_1 = x_9;
goto _start;
}
else
{
uint32 x_11; 
x_11 = lean::unbox_uint32(x_4);
return x_11;
}
}
}
}
obj* l___private_init_data_string_basic_3__utf8GetAux___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; uint32 x_5; obj* x_6; 
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::unbox_size_t(x_2);
x_5 = l___private_init_data_string_basic_3__utf8GetAux___main(x_0, x_3, x_4);
x_6 = lean::box_uint32(x_5);
lean::dec(x_0);
return x_6;
}
}
uint32 l___private_init_data_string_basic_3__utf8GetAux(obj* x_0, usize x_1, usize x_2) {
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
usize x_3; usize x_4; uint32 x_5; obj* x_6; 
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::unbox_size_t(x_2);
x_5 = l___private_init_data_string_basic_3__utf8GetAux(x_0, x_3, x_4);
x_6 = lean::box_uint32(x_5);
lean::dec(x_0);
return x_6;
}
}
obj* l_String_utf8Get___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; uint32 x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_1);
x_3 = lean::string_utf8_get(x_0, x_2);
x_4 = lean::box_uint32(x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l___private_init_data_string_basic_4__utf8SetAux___main(uint32 x_0, obj* x_1, usize x_2, usize x_3) {
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
x_9 = x_2 == x_3;
if (x_9 == 0)
{
uint32 x_10; usize x_11; usize x_12; obj* x_13; obj* x_14; 
x_10 = lean::unbox_uint32(x_4);
x_11 = l___private_init_data_string_basic_1__csize(x_10);
x_12 = x_2 + x_11;
x_13 = l___private_init_data_string_basic_4__utf8SetAux___main(x_0, x_6, x_12, x_3);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_4);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
else
{
obj* x_16; obj* x_17; 
lean::dec(x_4);
x_16 = lean::box_uint32(x_0);
if (lean::is_scalar(x_8)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_8;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_6);
return x_17;
}
}
}
}
obj* l___private_init_data_string_basic_4__utf8SetAux___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; usize x_5; usize x_6; obj* x_7; 
x_4 = lean::unbox_uint32(x_0);
x_5 = lean::unbox_size_t(x_2);
x_6 = lean::unbox_size_t(x_3);
x_7 = l___private_init_data_string_basic_4__utf8SetAux___main(x_4, x_1, x_5, x_6);
return x_7;
}
}
obj* l___private_init_data_string_basic_4__utf8SetAux(uint32 x_0, obj* x_1, usize x_2, usize x_3) {
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
uint32 x_4; usize x_5; usize x_6; obj* x_7; 
x_4 = lean::unbox_uint32(x_0);
x_5 = lean::unbox_size_t(x_2);
x_6 = lean::unbox_size_t(x_3);
x_7 = l___private_init_data_string_basic_4__utf8SetAux(x_4, x_1, x_5, x_6);
return x_7;
}
}
obj* l_String_utf8Set___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; uint32 x_4; obj* x_5; 
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::unbox_uint32(x_2);
x_5 = lean::string_utf8_set(x_0, x_3, x_4);
return x_5;
}
}
obj* l_String_utf8Next___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_1);
x_3 = lean::string_utf8_next(x_0, x_2);
x_4 = lean::box_size_t(x_3);
lean::dec(x_0);
return x_4;
}
}
usize _init_l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1() {
_start:
{
obj* x_0; usize x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::usize_of_nat(x_0);
return x_1;
}
}
usize l___private_init_data_string_basic_5__utf8PrevAux___main(obj* x_0, usize x_1, usize x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
usize x_3; 
x_3 = l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1;
return x_3;
}
else
{
obj* x_4; obj* x_5; uint32 x_6; usize x_7; usize x_8; uint8 x_9; 
x_4 = lean::cnstr_get(x_0, 0);
x_5 = lean::cnstr_get(x_0, 1);
x_6 = lean::unbox_uint32(x_4);
x_7 = l___private_init_data_string_basic_1__csize(x_6);
x_8 = x_1 + x_7;
x_9 = x_8 == x_2;
if (x_9 == 0)
{
x_0 = x_5;
x_1 = x_8;
goto _start;
}
else
{
return x_1;
}
}
}
}
obj* _init_l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1___boxed() {
_start:
{
usize x_0; obj* x_1; 
x_0 = l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1;
x_1 = lean::box_size_t(x_0);
return x_1;
}
}
obj* l___private_init_data_string_basic_5__utf8PrevAux___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; usize x_5; obj* x_6; 
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::unbox_size_t(x_2);
x_5 = l___private_init_data_string_basic_5__utf8PrevAux___main(x_0, x_3, x_4);
x_6 = lean::box_size_t(x_5);
lean::dec(x_0);
return x_6;
}
}
usize l___private_init_data_string_basic_5__utf8PrevAux(obj* x_0, usize x_1, usize x_2) {
_start:
{
usize x_3; 
x_3 = l___private_init_data_string_basic_5__utf8PrevAux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_init_data_string_basic_5__utf8PrevAux___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; usize x_5; obj* x_6; 
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::unbox_size_t(x_2);
x_5 = l___private_init_data_string_basic_5__utf8PrevAux(x_0, x_3, x_4);
x_6 = lean::box_size_t(x_5);
lean::dec(x_0);
return x_6;
}
}
obj* l_String_utf8Prev___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_1);
x_3 = lean::string_utf8_prev(x_0, x_2);
x_4 = lean::box_size_t(x_3);
lean::dec(x_0);
return x_4;
}
}
uint32 l_String_front(obj* x_0) {
_start:
{
usize x_1; uint32 x_2; 
x_1 = l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1;
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
usize x_1; usize x_2; uint32 x_3; 
x_1 = lean::string_utf8_byte_size(x_0);
x_2 = lean::string_utf8_prev(x_0, x_1);
x_3 = lean::string_utf8_get(x_0, x_2);
return x_3;
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
obj* l_String_utf8AtEnd___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_1);
x_3 = lean::string_utf8_at_end(x_0, x_2);
x_4 = lean::box(x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l___private_init_data_string_basic_6__utf8ExtractAux_u_2082___main(obj* x_0, usize x_1, usize x_2) {
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
x_8 = x_1 == x_2;
if (x_8 == 0)
{
uint32 x_9; usize x_10; usize x_11; obj* x_12; obj* x_13; 
x_9 = lean::unbox_uint32(x_3);
x_10 = l___private_init_data_string_basic_1__csize(x_9);
x_11 = x_1 + x_10;
x_12 = l___private_init_data_string_basic_6__utf8ExtractAux_u_2082___main(x_5, x_11, x_2);
if (lean::is_scalar(x_7)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_7;
}
lean::cnstr_set(x_13, 0, x_3);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
else
{
obj* x_17; 
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_3);
x_17 = lean::box(0);
return x_17;
}
}
}
}
obj* l___private_init_data_string_basic_6__utf8ExtractAux_u_2082___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; obj* x_5; 
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::unbox_size_t(x_2);
x_5 = l___private_init_data_string_basic_6__utf8ExtractAux_u_2082___main(x_0, x_3, x_4);
return x_5;
}
}
obj* l___private_init_data_string_basic_6__utf8ExtractAux_u_2082(obj* x_0, usize x_1, usize x_2) {
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
usize x_3; usize x_4; obj* x_5; 
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::unbox_size_t(x_2);
x_5 = l___private_init_data_string_basic_6__utf8ExtractAux_u_2082(x_0, x_3, x_4);
return x_5;
}
}
obj* l___private_init_data_string_basic_7__utf8ExtractAux_u_2081___main(obj* x_0, usize x_1, usize x_2, usize x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
return x_0;
}
else
{
obj* x_4; obj* x_6; uint8 x_8; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = x_1 == x_2;
if (x_8 == 0)
{
uint32 x_10; usize x_11; usize x_12; 
lean::dec(x_0);
x_10 = lean::unbox_uint32(x_4);
x_11 = l___private_init_data_string_basic_1__csize(x_10);
x_12 = x_1 + x_11;
x_0 = x_6;
x_1 = x_12;
goto _start;
}
else
{
obj* x_16; 
lean::dec(x_6);
lean::dec(x_4);
x_16 = l___private_init_data_string_basic_6__utf8ExtractAux_u_2082___main(x_0, x_1, x_3);
return x_16;
}
}
}
}
obj* l___private_init_data_string_basic_7__utf8ExtractAux_u_2081___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
usize x_4; usize x_5; usize x_6; obj* x_7; 
x_4 = lean::unbox_size_t(x_1);
x_5 = lean::unbox_size_t(x_2);
x_6 = lean::unbox_size_t(x_3);
x_7 = l___private_init_data_string_basic_7__utf8ExtractAux_u_2081___main(x_0, x_4, x_5, x_6);
return x_7;
}
}
obj* l___private_init_data_string_basic_7__utf8ExtractAux_u_2081(obj* x_0, usize x_1, usize x_2, usize x_3) {
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
usize x_4; usize x_5; usize x_6; obj* x_7; 
x_4 = lean::unbox_size_t(x_1);
x_5 = lean::unbox_size_t(x_2);
x_6 = lean::unbox_size_t(x_3);
x_7 = l___private_init_data_string_basic_7__utf8ExtractAux_u_2081(x_0, x_4, x_5, x_6);
return x_7;
}
}
obj* l_String_extract___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; obj* x_5; 
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::unbox_size_t(x_2);
x_5 = lean::string_utf8_extract(x_0, x_3, x_4);
lean::dec(x_0);
return x_5;
}
}
usize l_String_trimLeftAux___main(obj* x_0, obj* x_1, usize x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
usize x_5; uint8 x_6; 
x_5 = lean::string_utf8_byte_size(x_0);
x_6 = x_5 <= x_2;
if (x_6 == 0)
{
uint32 x_7; uint8 x_8; 
x_7 = lean::string_utf8_get(x_0, x_2);
x_8 = l_Char_isWhitespace(x_7);
if (x_8 == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_10; obj* x_11; usize x_13; usize x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_1, x_10);
lean::dec(x_1);
x_13 = l___private_init_data_string_basic_1__csize(x_7);
x_14 = x_2 + x_13;
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
else
{
lean::dec(x_1);
return x_2;
}
}
else
{
lean::dec(x_1);
return x_2;
}
}
}
obj* l_String_trimLeftAux___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; obj* x_5; 
x_3 = lean::unbox_size_t(x_2);
x_4 = l_String_trimLeftAux___main(x_0, x_1, x_3);
x_5 = lean::box_size_t(x_4);
lean::dec(x_0);
return x_5;
}
}
usize l_String_trimLeftAux(obj* x_0, obj* x_1, usize x_2) {
_start:
{
usize x_3; 
x_3 = l_String_trimLeftAux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_String_trimLeftAux___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; obj* x_5; 
x_3 = lean::unbox_size_t(x_2);
x_4 = l_String_trimLeftAux(x_0, x_1, x_3);
x_5 = lean::box_size_t(x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l_String_trimLeft(obj* x_0) {
_start:
{
usize x_1; obj* x_2; usize x_3; usize x_4; uint8 x_5; 
x_1 = lean::string_utf8_byte_size(x_0);
x_2 = lean::usize_to_nat(x_1);
x_3 = l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1;
x_4 = l_String_trimLeftAux___main(x_0, x_2, x_3);
x_5 = x_4 == x_3;
if (x_5 == 0)
{
obj* x_6; 
x_6 = lean::string_utf8_extract(x_0, x_4, x_1);
return x_6;
}
else
{
lean::inc(x_0);
return x_0;
}
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
usize l_String_trimRightAux___main(obj* x_0, obj* x_1, usize x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
usize x_5; uint8 x_6; 
x_5 = l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1;
x_6 = x_2 == x_5;
if (x_6 == 0)
{
usize x_7; uint32 x_8; uint8 x_9; 
x_7 = lean::string_utf8_prev(x_0, x_2);
x_8 = lean::string_utf8_get(x_0, x_7);
x_9 = l_Char_isWhitespace(x_8);
if (x_9 == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_11; obj* x_12; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_1, x_11);
lean::dec(x_1);
x_1 = x_12;
x_2 = x_7;
goto _start;
}
}
else
{
lean::dec(x_1);
return x_2;
}
}
else
{
lean::dec(x_1);
return x_2;
}
}
}
obj* l_String_trimRightAux___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; obj* x_5; 
x_3 = lean::unbox_size_t(x_2);
x_4 = l_String_trimRightAux___main(x_0, x_1, x_3);
x_5 = lean::box_size_t(x_4);
lean::dec(x_0);
return x_5;
}
}
usize l_String_trimRightAux(obj* x_0, obj* x_1, usize x_2) {
_start:
{
usize x_3; 
x_3 = l_String_trimRightAux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_String_trimRightAux___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; obj* x_5; 
x_3 = lean::unbox_size_t(x_2);
x_4 = l_String_trimRightAux(x_0, x_1, x_3);
x_5 = lean::box_size_t(x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l_String_trimRight(obj* x_0) {
_start:
{
usize x_1; obj* x_2; usize x_3; uint8 x_4; 
x_1 = lean::string_utf8_byte_size(x_0);
x_2 = lean::usize_to_nat(x_1);
x_3 = l_String_trimRightAux___main(x_0, x_2, x_1);
x_4 = x_3 == x_1;
if (x_4 == 0)
{
usize x_5; obj* x_6; 
x_5 = l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1;
x_6 = lean::string_utf8_extract(x_0, x_5, x_3);
return x_6;
}
else
{
lean::inc(x_0);
return x_0;
}
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
obj* l_String_trim(obj* x_0) {
_start:
{
usize x_1; obj* x_2; usize x_3; usize x_5; usize x_6; uint8 x_7; 
x_1 = lean::string_utf8_byte_size(x_0);
x_2 = lean::usize_to_nat(x_1);
x_3 = l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1;
lean::inc(x_2);
x_5 = l_String_trimLeftAux___main(x_0, x_2, x_3);
x_6 = l_String_trimRightAux___main(x_0, x_2, x_1);
x_7 = x_5 == x_3;
if (x_7 == 0)
{
obj* x_8; 
x_8 = lean::string_utf8_extract(x_0, x_5, x_6);
return x_8;
}
else
{
uint8 x_9; 
x_9 = x_6 == x_1;
if (x_9 == 0)
{
obj* x_10; 
x_10 = lean::string_utf8_extract(x_0, x_5, x_6);
return x_10;
}
else
{
lean::inc(x_0);
return x_0;
}
}
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
obj* l_String_mkIterator(obj* x_0) {
_start:
{
obj* x_1; usize x_2; obj* x_3; obj* x_4; 
x_1 = lean::mk_nat_obj(0u);
x_2 = l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1;
x_3 = lean::alloc_cnstr(0, 2, sizeof(size_t)*1);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set_scalar(x_3, sizeof(void*)*2, x_2);
x_4 = x_3;
return x_4;
}
}
obj* l_String_Iterator_remaining___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::cnstr_get(x_0, 0);
x_2 = lean::cnstr_get(x_0, 1);
x_3 = lean::string_length(x_1);
x_4 = lean::nat_sub(x_3, x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_String_Iterator_remaining___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_Iterator_remaining___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_String_Iterator_remaining(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_Iterator_remaining___main(x_0);
return x_1;
}
}
obj* l_String_Iterator_remaining___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_String_Iterator_remaining(x_0);
lean::dec(x_0);
return x_1;
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
usize l_String_Iterator_remainingBytes___main(obj* x_0) {
_start:
{
obj* x_1; usize x_2; usize x_3; usize x_4; 
x_1 = lean::cnstr_get(x_0, 0);
x_2 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*2);
x_3 = lean::string_utf8_byte_size(x_1);
x_4 = x_3 - x_2;
return x_4;
}
}
obj* l_String_Iterator_remainingBytes___main___boxed(obj* x_0) {
_start:
{
usize x_1; obj* x_2; 
x_1 = l_String_Iterator_remainingBytes___main(x_0);
x_2 = lean::box_size_t(x_1);
lean::dec(x_0);
return x_2;
}
}
usize l_String_Iterator_remainingBytes(obj* x_0) {
_start:
{
usize x_1; 
x_1 = l_String_Iterator_remainingBytes___main(x_0);
return x_1;
}
}
obj* l_String_Iterator_remainingBytes___boxed(obj* x_0) {
_start:
{
usize x_1; obj* x_2; 
x_1 = l_String_Iterator_remainingBytes(x_0);
x_2 = lean::box_size_t(x_1);
lean::dec(x_0);
return x_2;
}
}
uint32 l_String_Iterator_curr___main(obj* x_0) {
_start:
{
obj* x_1; usize x_2; uint32 x_3; 
x_1 = lean::cnstr_get(x_0, 0);
x_2 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*2);
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
obj* x_1; obj* x_3; usize x_5; obj* x_6; obj* x_7; obj* x_8; usize x_10; obj* x_11; obj* x_12; 
x_1 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*2);
if (lean::is_exclusive(x_0)) {
 x_6 = x_0;
} else {
 lean::inc(x_1);
 lean::inc(x_3);
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_add(x_3, x_7);
lean::dec(x_3);
x_10 = lean::string_utf8_next(x_1, x_5);
if (lean::is_scalar(x_6)) {
 x_11 = lean::alloc_cnstr(0, 2, sizeof(size_t)*1);
} else {
 x_11 = x_6;
}
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_8);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_10);
x_12 = x_11;
return x_12;
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
obj* x_1; obj* x_3; usize x_5; obj* x_6; obj* x_7; obj* x_8; usize x_10; obj* x_11; obj* x_12; 
x_1 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*2);
if (lean::is_exclusive(x_0)) {
 x_6 = x_0;
} else {
 lean::inc(x_1);
 lean::inc(x_3);
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_3, x_7);
lean::dec(x_3);
x_10 = lean::string_utf8_prev(x_1, x_5);
if (lean::is_scalar(x_6)) {
 x_11 = lean::alloc_cnstr(0, 2, sizeof(size_t)*1);
} else {
 x_11 = x_6;
}
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_8);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_10);
x_12 = x_11;
return x_12;
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
obj* x_1; usize x_2; usize x_3; uint8 x_4; 
x_1 = lean::cnstr_get(x_0, 0);
x_2 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*2);
x_3 = lean::string_utf8_byte_size(x_1);
x_4 = x_2 < x_3;
if (x_4 == 0)
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
usize x_1; usize x_2; uint8 x_3; 
x_1 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*2);
x_2 = l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1;
x_3 = x_2 < x_1;
if (x_3 == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8 x_5; 
x_5 = 1;
return x_5;
}
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
obj* x_2; obj* x_4; usize x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_6 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*2);
if (lean::is_exclusive(x_0)) {
 x_7 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::dec(x_0);
 x_7 = lean::box(0);
}
x_8 = lean::string_utf8_set(x_2, x_6, x_1);
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(0, 2, sizeof(size_t)*1);
} else {
 x_9 = x_7;
}
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_4);
lean::cnstr_set_scalar(x_9, sizeof(void*)*2, x_6);
x_10 = x_9;
return x_10;
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
obj* x_1; obj* x_3; obj* x_4; usize x_5; obj* x_6; obj* x_7; 
x_1 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 1);
 x_3 = x_0;
} else {
 lean::inc(x_1);
 lean::dec(x_0);
 x_3 = lean::box(0);
}
x_4 = lean::string_length(x_1);
x_5 = lean::string_utf8_byte_size(x_1);
if (lean::is_scalar(x_3)) {
 x_6 = lean::alloc_cnstr(0, 2, sizeof(size_t)*1);
} else {
 x_6 = x_3;
}
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_4);
lean::cnstr_set_scalar(x_6, sizeof(void*)*2, x_5);
x_7 = x_6;
return x_7;
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
obj* _init_l_String_Iterator_extract___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("");
return x_0;
}
}
obj* l_String_Iterator_extract___main(obj* x_0, obj* x_1) {
_start:
{
usize x_2; obj* x_3; obj* x_4; usize x_5; uint8 x_6; 
x_2 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*2);
x_3 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get_scalar<usize>(x_1, sizeof(void*)*2);
x_6 = lean::string_dec_eq(x_3, x_4);
if (x_6 == 0)
{
obj* x_7; 
x_7 = l_String_Iterator_extract___main___closed__1;
return x_7;
}
else
{
uint8 x_8; 
x_8 = x_5 < x_2;
if (x_8 == 0)
{
obj* x_9; 
x_9 = lean::string_utf8_extract(x_3, x_2, x_5);
return x_9;
}
else
{
obj* x_10; 
x_10 = l_String_Iterator_extract___main___closed__1;
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
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_7; 
x_4 = lean::mk_nat_obj(1u);
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
obj* x_1; usize x_2; usize x_3; obj* x_4; 
x_1 = lean::cnstr_get(x_0, 0);
x_2 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*2);
x_3 = lean::string_utf8_byte_size(x_1);
x_4 = lean::string_utf8_extract(x_1, x_2, x_3);
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
usize x_2; obj* x_3; obj* x_4; usize x_5; usize x_6; obj* x_7; usize x_8; usize x_9; obj* x_10; uint8 x_11; 
x_2 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*2);
x_3 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get_scalar<usize>(x_1, sizeof(void*)*2);
x_6 = lean::string_utf8_byte_size(x_3);
x_7 = lean::string_utf8_extract(x_3, x_2, x_6);
x_8 = x_6 - x_2;
x_9 = x_5 + x_8;
x_10 = lean::string_utf8_extract(x_4, x_5, x_9);
x_11 = lean::string_dec_eq(x_7, x_10);
lean::dec(x_10);
lean::dec(x_7);
if (x_11 == 0)
{
uint8 x_14; 
x_14 = 0;
return x_14;
}
else
{
uint8 x_15; 
x_15 = 1;
return x_15;
}
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
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_9; 
x_6 = lean::mk_nat_obj(1u);
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
x_1 = lean::string_length(x_0);
x_2 = lean::mk_nat_obj(0u);
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
x_1 = l_String_Iterator_extract___main___closed__1;
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
x_1 = l_String_Iterator_extract___main___closed__1;
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
obj* l_String_Iterator_nextn___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_7; 
x_4 = lean::mk_nat_obj(1u);
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
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_7; 
x_4 = lean::mk_nat_obj(1u);
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
obj* l___private_init_data_string_basic_8__lineColumnAux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_7; uint8 x_9; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
x_9 = l_String_Iterator_hasNext___main(x_1);
if (x_9 == 0)
{
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_14; obj* x_15; obj* x_16; uint32 x_18; uint32 x_19; uint8 x_20; 
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_14 = x_2;
} else {
 lean::dec(x_2);
 x_14 = lean::box(0);
}
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_sub(x_0, x_15);
lean::dec(x_0);
x_18 = l_String_Iterator_curr___main(x_1);
x_19 = 10;
x_20 = x_18 == x_19;
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_24; 
x_21 = l_String_Iterator_next___main(x_1);
x_22 = lean::nat_add(x_7, x_15);
lean::dec(x_7);
if (lean::is_scalar(x_14)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_14;
}
lean::cnstr_set(x_24, 0, x_5);
lean::cnstr_set(x_24, 1, x_22);
x_0 = x_16;
x_1 = x_21;
x_2 = x_24;
goto _start;
}
else
{
obj* x_27; obj* x_28; obj* x_30; 
lean::dec(x_7);
x_27 = l_String_Iterator_next___main(x_1);
x_28 = lean::nat_add(x_5, x_15);
lean::dec(x_5);
if (lean::is_scalar(x_14)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_14;
}
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_3);
x_0 = x_16;
x_1 = x_27;
x_2 = x_30;
goto _start;
}
}
}
else
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
}
}
obj* l___private_init_data_string_basic_8__lineColumnAux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_data_string_basic_8__lineColumnAux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* _init_l_String_lineColumn___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_String_lineColumn(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; usize x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::mk_nat_obj(0u);
x_3 = l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1;
x_4 = lean::alloc_cnstr(0, 2, sizeof(size_t)*1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_3);
x_5 = x_4;
x_6 = l_String_lineColumn___closed__1;
x_7 = l___private_init_data_string_basic_8__lineColumnAux___main(x_1, x_5, x_6);
return x_7;
}
}
obj* l_Char_toString(uint32 x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_String_Iterator_extract___main___closed__1;
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
obj* _init_l___private_init_data_string_basic_9__toNatCore___main___closed__1() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = 48;
x_1 = lean::uint32_to_nat(x_0);
return x_1;
}
}
obj* l___private_init_data_string_basic_9__toNatCore___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; uint32 x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_19; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_1, x_5);
lean::dec(x_1);
x_8 = l_String_Iterator_curr___main(x_0);
x_9 = lean::mk_nat_obj(10u);
x_10 = lean::nat_mul(x_2, x_9);
lean::dec(x_2);
x_12 = lean::uint32_to_nat(x_8);
x_13 = lean::nat_add(x_10, x_12);
lean::dec(x_12);
lean::dec(x_10);
x_16 = l___private_init_data_string_basic_9__toNatCore___main___closed__1;
x_17 = lean::nat_sub(x_13, x_16);
lean::dec(x_13);
x_19 = l_String_Iterator_next___main(x_0);
x_0 = x_19;
x_1 = x_6;
x_2 = x_17;
goto _start;
}
else
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
}
}
obj* l___private_init_data_string_basic_9__toNatCore(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_data_string_basic_9__toNatCore___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_String_toNat(obj* x_0) {
_start:
{
obj* x_1; usize x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_8; 
x_1 = lean::mk_nat_obj(0u);
x_2 = l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1;
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, sizeof(size_t)*1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_2);
x_5 = x_4;
x_6 = lean::string_length(x_0);
lean::dec(x_0);
x_8 = l___private_init_data_string_basic_9__toNatCore___main(x_5, x_6, x_1);
return x_8;
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
 l_String_HasLt = _init_l_String_HasLt();
lean::mark_persistent(l_String_HasLt);
 l_String_utf8Begin = _init_l_String_utf8Begin();
 l_String_utf8Begin___boxed = _init_l_String_utf8Begin___boxed();
lean::mark_persistent(l_String_utf8Begin___boxed);
 l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1 = _init_l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1();
 l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1___boxed = _init_l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1___boxed();
lean::mark_persistent(l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1___boxed);
 l_String_Iterator_extract___main___closed__1 = _init_l_String_Iterator_extract___main___closed__1();
lean::mark_persistent(l_String_Iterator_extract___main___closed__1);
 l_String_Inhabited = _init_l_String_Inhabited();
lean::mark_persistent(l_String_Inhabited);
 l_String_HasSizeof = _init_l_String_HasSizeof();
lean::mark_persistent(l_String_HasSizeof);
 l_String_HasAppend = _init_l_String_HasAppend();
lean::mark_persistent(l_String_HasAppend);
 l_String_lineColumn___closed__1 = _init_l_String_lineColumn___closed__1();
lean::mark_persistent(l_String_lineColumn___closed__1);
 l___private_init_data_string_basic_9__toNatCore___main___closed__1 = _init_l___private_init_data_string_basic_9__toNatCore___main___closed__1();
lean::mark_persistent(l___private_init_data_string_basic_9__toNatCore___main___closed__1);
return w;
}
