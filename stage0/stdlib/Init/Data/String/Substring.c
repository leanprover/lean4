// Lean compiler output
// Module: Init.Data.String.Substring
// Imports: public import Init.Data.String.Basic
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
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_isEmptyImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_String_foldrAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_atEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_Raw_all___lam__0(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Substring_Raw_commonPrefix(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_String_foldlAux___at___00Substring_Raw_toNat_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_posOf(lean_object*, uint32_t);
LEAN_EXPORT uint8_t l_Substring_Raw_isNat(lean_object*);
static lean_object* l_Substring_Raw_hasBeq___closed__0;
LEAN_EXPORT lean_object* l_Substring_Raw_extract___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_Raw_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhile(lean_object*, lean_object*);
LEAN_EXPORT uint32_t lean_substring_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_beqImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_atEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_dropPrefix_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_substring_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_splitOn___boxed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_contains___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT uint8_t l_Substring_Raw_all(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_substring_isempty(lean_object*);
LEAN_EXPORT lean_object* l_Substring_next(lean_object*, lean_object*);
static lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0;
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Substring_Raw_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_hasBeq;
LEAN_EXPORT lean_object* l_Substring_Raw_foldr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_String_anyAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_commonSuffix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_sameAs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_drop(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Substring_Raw_toNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_toString___boxed(lean_object*);
LEAN_EXPORT uint8_t l_String_anyAux___at___00Substring_Raw_toNat_x3f_spec__1(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_nextn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_next___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at___00Substring_Raw_Internal_allImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_contains___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_allImpl___boxed(lean_object*, lean_object*);
lean_object* l_Char_isWhitespace___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_anyAux___at___00Substring_Raw_Internal_allImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_isEmpty(lean_object*);
lean_object* l_String_posOfAux(lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_trimLeft(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_trimRight(lean_object*);
static lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1;
LEAN_EXPORT lean_object* l_Substring_Raw_toString(lean_object*);
LEAN_EXPORT uint8_t l_Substring_Raw_sameAs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_trim(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_prevn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___at___00Substring_Raw_toNat_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_prev___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_Raw_contains(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_getImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_Raw_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_dropSuffix_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_Raw_contains___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Substring_Raw_dropWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_repair(lean_object*);
lean_object* l_String_foldlAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_dropRightWhile(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_frontImpl___boxed(lean_object*);
LEAN_EXPORT uint32_t lean_substring_front(lean_object*);
static lean_object* l_Substring_Raw_trimLeft___closed__0;
LEAN_EXPORT lean_object* lean_substring_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_Raw_atEnd(lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_front___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Substring_bsize(lean_object*);
LEAN_EXPORT lean_object* lean_substring_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_all___lam__0___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_all___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_bsize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeRight(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Substring_toString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_prevn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at___00Substring_Raw_toNat_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_dropRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_prev___boxed(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Substring_Raw_front(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_posOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_substring_tostring(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_any___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_atEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_foldl(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Substring_Raw_extract___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_get_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_splitOn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_next___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_substring_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_next(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_substring_all(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_get_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_substring_takewhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_isEmpty___boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_Raw_isNat___lam__0(uint8_t, uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_toString(lean_object*);
uint8_t l_String_Pos_Raw_substrEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_Raw_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_nextn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Substring_Raw_extract___closed__1;
LEAN_EXPORT uint8_t l_Substring_Raw_isEmpty(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Substring_Raw_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Substring_Raw_isEmpty(x_1);
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
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_isEmptyImpl___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_substring_isempty(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toString(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Substring_Raw_toString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Substring_Raw_toString(x_1);
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
LEAN_EXPORT uint32_t l_Substring_Raw_get(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Substring_Raw_get___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = l_Substring_Raw_get(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_getImpl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_substring_get(x_1, x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_next(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Substring_Raw_next___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Substring_Raw_next(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_get_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_get_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Substring_0__Substring_Raw_get_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_prev(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Substring_Raw_prev___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Substring_Raw_prev(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Substring_Raw_nextn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Substring_Raw_nextn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_Raw_nextn(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_prevn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Substring_Raw_prevn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_Raw_prevn(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT uint32_t l_Substring_Raw_front(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint32_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_string_utf8_get(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_front___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Substring_Raw_front(x_1);
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
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_frontImpl___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_substring_front(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_posOf(lean_object* x_1, uint32_t x_2) {
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
LEAN_EXPORT lean_object* l_Substring_Raw_posOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_Substring_Raw_posOf(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_drop(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Substring_Raw_nextn(x_1, x_2, x_6);
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
x_7 = l_Substring_Raw_nextn(x_1, x_2, x_6);
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
LEAN_EXPORT lean_object* l_Substring_Raw_dropRight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_nat_sub(x_5, x_4);
x_7 = l_Substring_Raw_prevn(x_1, x_2, x_6);
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
LEAN_EXPORT lean_object* l_Substring_Raw_take(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Substring_Raw_nextn(x_1, x_2, x_5);
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
LEAN_EXPORT lean_object* l_Substring_Raw_takeRight(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Substring_Raw_prevn(x_1, x_2, x_6);
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
LEAN_EXPORT uint8_t l_Substring_Raw_atEnd(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Substring_Raw_atEnd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Substring_Raw_atEnd(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Substring_Raw_extract___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Substring_Raw_extract___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Substring_Raw_extract___closed__0;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_extract(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_17 = l_Substring_Raw_extract___closed__1;
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
LEAN_EXPORT lean_object* l_Substring_Raw_extract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_Raw_extract(x_1, x_2, x_3);
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
x_17 = l_Substring_Raw_extract___closed__1;
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
static lean_object* _init_l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Substring_Raw_extract___closed__0;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Substring_Raw_extract___closed__0;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_57 = l_Substring_Raw_extract___closed__1;
x_7 = x_57;
goto block_10;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_64; lean_object* x_65; uint8_t x_71; 
x_58 = l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1;
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
x_74 = l_Substring_Raw_extract___closed__1;
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
lean_inc(x_16);
x_3 = x_16;
x_4 = x_16;
x_5 = x_15;
x_6 = x_18;
goto _start;
}
block_32:
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_nat_add(x_22, x_25);
lean_dec(x_25);
x_29 = lean_nat_dec_le(x_23, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_inc_ref(x_21);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_28);
x_15 = x_24;
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
x_15 = x_24;
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
x_24 = x_37;
x_25 = x_38;
x_26 = x_33;
x_27 = x_40;
goto block_32;
}
else
{
lean_dec(x_40);
lean_inc(x_23);
x_24 = x_37;
x_25 = x_38;
x_26 = x_33;
x_27 = x_23;
goto block_32;
}
}
else
{
lean_object* x_42; 
lean_dec(x_38);
lean_dec(x_3);
x_42 = l_Substring_Raw_extract___closed__1;
x_15 = x_37;
x_16 = x_33;
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_splitOn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Substring_Raw_extract___closed__0;
x_4 = lean_string_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(x_1, x_2, x_5, x_5, x_5, x_6);
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
LEAN_EXPORT lean_object* l_Substring_Raw_splitOn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Substring_Raw_splitOn(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Substring_Raw_foldl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Substring_Raw_foldr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT uint8_t l_Substring_Raw_any(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Substring_Raw_any___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Substring_Raw_any(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_all___lam__0(lean_object* x_1, uint32_t x_2) {
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
LEAN_EXPORT uint8_t l_Substring_Raw_all(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_alloc_closure((void*)(l_Substring_Raw_all___lam__0___boxed), 2, 1);
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
LEAN_EXPORT lean_object* l_Substring_Raw_all___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_Substring_Raw_all___lam__0(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_all___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Substring_Raw_all(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at___00Substring_Raw_Internal_allImpl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_6 = l_String_anyAux___at___00Substring_Raw_Internal_allImpl_spec__0(x_2, x_3, x_5, x_4);
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
LEAN_EXPORT lean_object* l_String_anyAux___at___00Substring_Raw_Internal_allImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_String_anyAux___at___00Substring_Raw_Internal_allImpl_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_allImpl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_substring_all(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_contains___lam__0(uint32_t x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint32_dec_eq(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_contains(lean_object* x_1, uint32_t x_2) {
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
x_7 = lean_alloc_closure((void*)(l_Substring_Raw_contains___lam__0___boxed), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = l_String_anyAux(x_3, x_5, x_7, x_4);
lean_dec(x_5);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_contains___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Substring_Raw_contains___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_Substring_Raw_contains(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Substring_Raw_takeWhileAux(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhile(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Substring_Raw_takeWhileAux(x_4, x_6, x_2, x_5);
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
x_11 = l_Substring_Raw_takeWhileAux(x_8, x_10, x_2, x_9);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_7 = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(x_2, x_4, x_6, x_5);
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
x_11 = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(x_2, x_8, x_10, x_9);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropWhile(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Substring_Raw_takeWhileAux(x_4, x_6, x_2, x_5);
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
x_11 = l_Substring_Raw_takeWhileAux(x_8, x_10, x_2, x_9);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Substring_Raw_takeRightWhileAux(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhile(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Substring_Raw_takeRightWhileAux(x_4, x_5, x_2, x_6);
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
x_11 = l_Substring_Raw_takeRightWhileAux(x_8, x_9, x_2, x_10);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropRightWhile(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Substring_Raw_takeRightWhileAux(x_4, x_5, x_2, x_6);
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
x_11 = l_Substring_Raw_takeRightWhileAux(x_8, x_9, x_2, x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Substring_Raw_trimLeft___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Char_isWhitespace___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trimLeft(lean_object* x_1) {
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
x_6 = l_Substring_Raw_trimLeft___closed__0;
x_7 = l_Substring_Raw_takeWhileAux(x_3, x_5, x_6, x_4);
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
x_11 = l_Substring_Raw_trimLeft___closed__0;
x_12 = l_Substring_Raw_takeWhileAux(x_8, x_10, x_11, x_9);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trimRight(lean_object* x_1) {
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
x_6 = l_Substring_Raw_trimLeft___closed__0;
x_7 = l_Substring_Raw_takeRightWhileAux(x_3, x_4, x_6, x_5);
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
x_11 = l_Substring_Raw_trimLeft___closed__0;
x_12 = l_Substring_Raw_takeRightWhileAux(x_8, x_9, x_11, x_10);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trim(lean_object* x_1) {
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
x_6 = l_Substring_Raw_trimLeft___closed__0;
x_7 = l_Substring_Raw_takeWhileAux(x_3, x_5, x_6, x_4);
x_8 = l_Substring_Raw_takeRightWhileAux(x_3, x_7, x_6, x_5);
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
x_12 = l_Substring_Raw_trimLeft___closed__0;
x_13 = l_Substring_Raw_takeWhileAux(x_9, x_11, x_12, x_10);
x_14 = l_Substring_Raw_takeRightWhileAux(x_9, x_13, x_12, x_11);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_isNat___lam__0(uint8_t x_1, uint32_t x_2) {
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
LEAN_EXPORT uint8_t l_Substring_Raw_isNat(lean_object* x_1) {
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
x_9 = lean_alloc_closure((void*)(l_Substring_Raw_isNat___lam__0___boxed), 2, 1);
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
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Substring_Raw_isNat___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Substring_Raw_isNat(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at___00Substring_Raw_toNat_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT uint8_t l_String_anyAux___at___00Substring_Raw_toNat_x3f_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Substring_Raw_toNat_x3f(lean_object* x_1) {
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
x_12 = l_String_anyAux___at___00Substring_Raw_toNat_x3f_spec__1(x_11, x_2, x_4, x_3);
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
x_6 = l_String_foldlAux___at___00Substring_Raw_toNat_x3f_spec__0(x_2, x_4, x_3, x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at___00Substring_Raw_toNat_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_foldlAux___at___00Substring_Raw_toNat_x3f_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at___00Substring_Raw_toNat_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
x_6 = l_String_anyAux___at___00Substring_Raw_toNat_x3f_spec__1(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_repair(lean_object* x_1) {
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
LEAN_EXPORT uint8_t l_Substring_Raw_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_3 = l_Substring_Raw_repair(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = l_Substring_Raw_repair(x_2);
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
x_14 = l_String_Pos_Raw_substrEq(x_4, x_5, x_8, x_9, x_11);
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Substring_Raw_beq(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lean_substring_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Substring_Raw_beq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_beqImpl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_substring_beq(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Substring_Raw_hasBeq___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Substring_Raw_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Substring_Raw_hasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Substring_Raw_hasBeq___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_sameAs(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Substring_Raw_beq(x_1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_sameAs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Substring_Raw_sameAs(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonPrefix(lean_object* x_1, lean_object* x_2) {
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
x_6 = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(x_1, x_2, x_4, x_5);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonSuffix(lean_object* x_1, lean_object* x_2) {
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
x_6 = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(x_1, x_2, x_4, x_5);
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
LEAN_EXPORT lean_object* l_Substring_Raw_dropPrefix_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_3 = l_Substring_Raw_commonPrefix(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Substring_Raw_dropSuffix_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_3 = l_Substring_Raw_commonSuffix(x_1, x_2);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Substring_bsize(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_nat_sub(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_bsize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Substring_bsize(x_1);
lean_dec_ref(x_1);
return x_2;
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
LEAN_EXPORT uint8_t l_Substring_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Substring_Raw_beq(x_1, x_2);
return x_3;
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
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Substring(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Substring_Raw_extract___closed__0 = _init_l_Substring_Raw_extract___closed__0();
lean_mark_persistent(l_Substring_Raw_extract___closed__0);
l_Substring_Raw_extract___closed__1 = _init_l_Substring_Raw_extract___closed__1();
lean_mark_persistent(l_Substring_Raw_extract___closed__1);
l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0 = _init_l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0();
lean_mark_persistent(l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0);
l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1 = _init_l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1();
lean_mark_persistent(l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1);
l_Substring_Raw_trimLeft___closed__0 = _init_l_Substring_Raw_trimLeft___closed__0();
lean_mark_persistent(l_Substring_Raw_trimLeft___closed__0);
l_Substring_Raw_hasBeq___closed__0 = _init_l_Substring_Raw_hasBeq___closed__0();
lean_mark_persistent(l_Substring_Raw_hasBeq___closed__0);
l_Substring_Raw_hasBeq = _init_l_Substring_Raw_hasBeq();
lean_mark_persistent(l_Substring_Raw_hasBeq);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
