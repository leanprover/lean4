// Lean compiler output
// Module: Init.Data.String.TakeDrop
// Imports: public import Init.Data.String.Slice public import Init.Data.String.Substring
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
LEAN_EXPORT lean_object* l_String_startsWith___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_endsWith(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_endsWith___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_stripSuffix(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_startsWith___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropEndWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_dropRightWhile_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_trimLeft_spec__0(lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultDropSuffix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___at___00String_takeRightWhile_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_trimLeft_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultDropSuffix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___at___00String_takeRightWhile_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_trim(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
LEAN_EXPORT lean_object* l_String_isPrefixOf___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevAux_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Pos_Raw_nextUntil___lam__0(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_dropEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_stripPrefix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_trimAsciiStart(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_String_dropRightWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix___redArg(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_trimLeft_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextWhile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_String_trimAsciiEnd___closed__0;
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00String_stripSuffix_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropRight(lean_object*, lean_object*);
extern lean_object* l_String_Slice_Pattern_ForwardCharPredSearcher_instForwardPatternForallCharBool;
LEAN_EXPORT lean_object* lean_string_nextwhile(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_utf8ByteSize(lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_Slice_Pattern_BackwardCharPredSearcher_instBackwardPatternForallCharBool;
lean_object* l_Char_isWhitespace___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_dropEndWhile___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_startsWith(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_startsWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeEndWhile(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_dropSuffix___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_trim(lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_Substring_Raw_takeWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_next___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00String_stripPrefix_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeRightWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeEndWhile___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_nextUntil(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_endsWith___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_trimRight_spec__0___boxed(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_String_Slice_dropPrefix___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_trimLeft_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_trimAscii(lean_object*);
LEAN_EXPORT uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_trimRight_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_nextWhile(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultDropSuffix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_trimRight_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_nextUntil___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_dropright(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_endsWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeEnd(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_string_isprefixof(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_trimAsciiEnd(lean_object*);
LEAN_EXPORT lean_object* l_String_trimRight(lean_object*);
lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeWhile_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultDropSuffix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_trimRight_spec__0_spec__0(lean_object*);
lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_trimLeft(lean_object*);
LEAN_EXPORT lean_object* l_String_dropWhile___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_drop(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_nextWhile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_dropRightWhile_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_isPrefixOfImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___at___00String_takeRightWhile_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_slice_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextWhile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeWhile___redArg(lean_object*, lean_object*, lean_object*);
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
x_6 = l_String_Slice_Pos_nextn(x_5, x_3, x_2);
lean_dec_ref(x_5);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_4);
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
x_6 = l_String_Slice_Pos_nextn(x_5, x_3, x_2);
lean_dec_ref(x_5);
x_7 = lean_string_utf8_extract(x_1, x_6, x_4);
lean_dec(x_4);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_dropEnd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_utf8ByteSize(x_5);
x_7 = l_String_Slice_Pos_prevn(x_5, x_6, x_2);
lean_dec_ref(x_5);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_dropRight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_utf8ByteSize(x_5);
x_7 = l_String_Slice_Pos_prevn(x_5, x_6, x_2);
lean_dec_ref(x_5);
x_8 = lean_string_utf8_extract(x_1, x_3, x_7);
lean_dec(x_7);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* lean_string_dropright(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_utf8ByteSize(x_5);
x_7 = l_String_Slice_Pos_prevn(x_5, x_6, x_2);
lean_dec_ref(x_5);
x_8 = lean_string_utf8_extract(x_1, x_3, x_7);
lean_dec(x_7);
lean_dec_ref(x_1);
return x_8;
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
x_6 = l_String_Slice_Pos_nextn(x_5, x_3, x_2);
lean_dec_ref(x_5);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_takeEnd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc(x_4);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_utf8ByteSize(x_5);
x_7 = l_String_Slice_Pos_prevn(x_5, x_6, x_2);
lean_dec_ref(x_5);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_takeRight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc(x_4);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_utf8ByteSize(x_5);
x_7 = l_String_Slice_Pos_prevn(x_5, x_6, x_2);
lean_dec_ref(x_5);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_4);
x_9 = l_String_Slice_toString(x_8);
lean_dec_ref(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_takeWhile___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_string_utf8_byte_size(x_2);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = l___private_Init_Data_String_Slice_0__String_Slice_takeWhile_go(lean_box(0), x_1, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_takeWhile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_3);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = l___private_Init_Data_String_Slice_0__String_Slice_takeWhile_go(lean_box(0), x_2, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_dropWhile___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_string_utf8_byte_size(x_2);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(lean_box(0), x_1, x_6, x_3, x_4);
lean_dec_ref(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_dropWhile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_3);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(lean_box(0), x_2, x_7, x_4, x_5);
lean_dec_ref(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_takeEndWhile___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_string_utf8_byte_size(x_2);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = l_String_Slice_utf8ByteSize(x_6);
x_8 = l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go(lean_box(0), x_1, x_6, x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_takeEndWhile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_3);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_String_Slice_utf8ByteSize(x_7);
x_9 = l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go(lean_box(0), x_2, x_7, x_4, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultDropSuffix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___at___00String_takeRightWhile_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_String_Slice_utf8ByteSize(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint32_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_10 = l_String_Slice_Pos_prevAux_go___redArg(x_2, x_9);
x_11 = lean_nat_add(x_7, x_10);
x_12 = lean_string_utf8_get_fast(x_6, x_11);
lean_dec(x_11);
x_13 = lean_box_uint32(x_12);
x_14 = lean_apply_1(x_1, x_13);
x_15 = lean_unbox(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_10);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_10);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_18 = lean_box(0);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___at___00String_takeRightWhile_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_add(x_5, x_3);
lean_inc(x_7);
lean_inc(x_5);
lean_inc_ref(x_4);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
lean_inc_ref(x_1);
x_9 = l_String_Slice_Pattern_ToBackwardSearcher_defaultDropSuffix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___at___00String_takeRightWhile_spec__0_spec__0(x_1, x_8);
lean_dec_ref(x_8);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_nat_dec_lt(x_10, x_3);
lean_dec(x_3);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_10);
lean_inc(x_6);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_2, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_2, 0);
lean_dec(x_15);
lean_ctor_set(x_2, 1, x_7);
return x_2;
}
else
{
lean_object* x_16; 
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_7);
lean_ctor_set(x_16, 2, x_6);
return x_16;
}
}
else
{
lean_dec(x_7);
x_3 = x_10;
goto _start;
}
}
else
{
uint8_t x_18; 
lean_dec(x_9);
lean_inc(x_6);
lean_inc_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_2, 2);
lean_dec(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_2, 0);
lean_dec(x_21);
lean_ctor_set(x_2, 1, x_7);
return x_2;
}
else
{
lean_object* x_22; 
lean_dec(x_2);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_7);
lean_ctor_set(x_22, 2, x_6);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_String_takeRightWhile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_utf8ByteSize(x_5);
x_7 = l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___at___00String_takeRightWhile_spec__0(x_2, x_5, x_6);
x_8 = l_String_Slice_toString(x_7);
lean_dec_ref(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultDropSuffix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___at___00String_takeRightWhile_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pattern_ToBackwardSearcher_defaultDropSuffix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___at___00String_takeRightWhile_spec__0_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_dropEndWhile___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_string_utf8_byte_size(x_2);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = l_String_Slice_utf8ByteSize(x_6);
x_8 = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go(lean_box(0), x_1, x_6, x_3, x_7);
lean_dec_ref(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_dropEndWhile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_3);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_String_Slice_utf8ByteSize(x_7);
x_9 = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go(lean_box(0), x_2, x_7, x_4, x_8);
lean_dec_ref(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_dropRightWhile_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_nat_add(x_5, x_3);
lean_inc(x_5);
lean_inc_ref(x_4);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
lean_inc_ref(x_1);
x_8 = l_String_Slice_Pattern_ToBackwardSearcher_defaultDropSuffix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___at___00String_takeRightWhile_spec__0_spec__0(x_1, x_7);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_nat_dec_lt(x_9, x_3);
lean_dec(x_3);
if (x_10 == 0)
{
lean_dec(x_9);
lean_dec_ref(x_1);
return x_7;
}
else
{
lean_dec_ref(x_7);
x_3 = x_9;
goto _start;
}
}
else
{
lean_dec(x_8);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_String_dropRightWhile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_utf8ByteSize(x_5);
x_7 = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_dropRightWhile_spec__0(x_2, x_5, x_6);
lean_dec_ref(x_5);
x_8 = l_String_Slice_toString(x_7);
lean_dec_ref(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_dropRightWhile_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_dropRightWhile_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_startsWith___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_apply_2(x_4, x_7, x_3);
x_9 = lean_unbox(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l_String_startsWith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_string_utf8_byte_size(x_3);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_apply_2(x_5, x_8, x_4);
x_10 = lean_unbox(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_String_startsWith___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_startsWith___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_startsWith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_String_startsWith(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_String_isPrefixOf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_string_utf8_byte_size(x_1);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_String_Slice_utf8ByteSize(x_7);
x_9 = l_String_Slice_utf8ByteSize(x_5);
x_10 = lean_nat_dec_le(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_slice_memcmp(x_5, x_7, x_3, x_3, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_String_isPrefixOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_isPrefixOf(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lean_string_isprefixof(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_string_utf8_byte_size(x_1);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_String_Slice_utf8ByteSize(x_7);
x_9 = l_String_Slice_utf8ByteSize(x_5);
x_10 = lean_nat_dec_le(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_slice_memcmp(x_5, x_7, x_3, x_3, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
return x_11;
}
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
LEAN_EXPORT uint8_t l_String_endsWith___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_apply_2(x_4, x_7, x_3);
x_9 = lean_unbox(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l_String_endsWith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_string_utf8_byte_size(x_3);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_apply_2(x_5, x_8, x_4);
x_10 = lean_unbox(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_String_endsWith___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_endsWith___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_endsWith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_String_endsWith(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_String_trimAsciiEnd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Char_isWhitespace___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_trimAsciiEnd(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = l_String_Slice_Pattern_BackwardCharPredSearcher_instBackwardPatternForallCharBool;
x_6 = l_String_trimAsciiEnd___closed__0;
x_7 = l_String_Slice_utf8ByteSize(x_4);
x_8 = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go(lean_box(0), x_5, x_4, x_6, x_7);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultDropSuffix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_trimRight_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_String_Slice_utf8ByteSize(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_14; uint32_t x_15; uint8_t x_16; uint32_t x_23; uint8_t x_24; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
lean_dec(x_2);
x_9 = l_String_Slice_Pos_prevAux_go___redArg(x_1, x_8);
x_14 = lean_nat_add(x_6, x_9);
x_15 = lean_string_utf8_get_fast(x_5, x_14);
lean_dec(x_14);
x_23 = 32;
x_24 = lean_uint32_dec_eq(x_15, x_23);
if (x_24 == 0)
{
uint32_t x_25; uint8_t x_26; 
x_25 = 9;
x_26 = lean_uint32_dec_eq(x_15, x_25);
x_16 = x_26;
goto block_22;
}
else
{
x_16 = x_24;
goto block_22;
}
block_13:
{
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_9);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
}
block_22:
{
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = 13;
x_18 = lean_uint32_dec_eq(x_15, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 10;
x_20 = lean_uint32_dec_eq(x_15, x_19);
x_10 = x_20;
goto block_13;
}
else
{
x_10 = x_18;
goto block_13;
}
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_9);
return x_21;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_2);
x_27 = lean_box(0);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_trimRight_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_nat_add(x_4, x_2);
lean_inc(x_4);
lean_inc_ref(x_3);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = l_String_Slice_Pattern_ToBackwardSearcher_defaultDropSuffix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_trimRight_spec__0_spec__0(x_6);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_nat_dec_lt(x_8, x_2);
lean_dec(x_2);
if (x_9 == 0)
{
lean_dec(x_8);
return x_6;
}
else
{
lean_dec_ref(x_6);
x_2 = x_8;
goto _start;
}
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_String_trimRight(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = l_String_Slice_utf8ByteSize(x_4);
x_6 = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_trimRight_spec__0(x_4, x_5);
lean_dec_ref(x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = lean_string_utf8_extract(x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ToBackwardSearcher_defaultDropSuffix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_trimRight_spec__0_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_Pattern_ToBackwardSearcher_defaultDropSuffix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_trimRight_spec__0_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_trimRight_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_trimRight_spec__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_trimAsciiStart(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = l_String_Slice_Pattern_ForwardCharPredSearcher_instForwardPatternForallCharBool;
x_6 = l_String_trimAsciiEnd___closed__0;
x_7 = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(lean_box(0), x_5, x_4, x_6, x_2);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_trimLeft_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_String_Slice_utf8ByteSize(x_1);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint32_t x_12; uint8_t x_13; uint32_t x_20; uint8_t x_21; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_String_Slice_Pos_next___redArg(x_1, x_2);
x_12 = lean_string_utf8_get_fast(x_5, x_6);
x_20 = 32;
x_21 = lean_uint32_dec_eq(x_12, x_20);
if (x_21 == 0)
{
uint32_t x_22; uint8_t x_23; 
x_22 = 9;
x_23 = lean_uint32_dec_eq(x_12, x_22);
x_13 = x_23;
goto block_19;
}
else
{
x_13 = x_21;
goto block_19;
}
block_11:
{
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_7);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
}
block_19:
{
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 13;
x_15 = lean_uint32_dec_eq(x_12, x_14);
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; 
x_16 = 10;
x_17 = lean_uint32_dec_eq(x_12, x_16);
x_8 = x_17;
goto block_11;
}
else
{
x_8 = x_15;
goto block_11;
}
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_7);
return x_18;
}
}
}
else
{
lean_object* x_24; 
x_24 = lean_box(0);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_trimLeft_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_nat_add(x_4, x_2);
lean_inc(x_5);
lean_inc_ref(x_3);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_5);
x_8 = l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_trimLeft_spec__0_spec__0(x_7);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_9);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_2);
if (x_11 == 0)
{
lean_dec(x_10);
return x_7;
}
else
{
lean_dec_ref(x_7);
x_2 = x_10;
goto _start;
}
}
else
{
lean_dec(x_8);
lean_dec(x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_String_trimLeft(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_trimLeft_spec__0(x_4, x_2);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = lean_string_utf8_extract(x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_trimLeft_spec__0_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_trimLeft_spec__0_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_trimLeft_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_trimLeft_spec__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_trimAscii(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = l_String_Slice_trimAscii(x_4);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_trim(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = l_String_Slice_trimAscii(x_4);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = lean_string_utf8_extract(x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* lean_string_trim(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = l_String_Slice_trimAscii(x_4);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = lean_string_utf8_extract(x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextWhile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l_Substring_Raw_takeWhileAux(x_1, x_4, x_2, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextWhile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Pos_Raw_nextWhile(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_nextWhile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l_Substring_Raw_takeWhileAux(x_1, x_4, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* lean_string_nextwhile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(x_2, x_1, x_4, x_3);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_nextUntil___lam__0(lean_object* x_1, uint32_t x_2) {
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
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_String_Pos_Raw_nextUntil___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = l_Substring_Raw_takeWhileAux(x_1, x_5, x_4, x_3);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_String_Pos_Raw_nextUntil___lam__0(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Pos_Raw_nextUntil(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_10; 
x_10 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
else
{
lean_dec_ref(x_1);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_String_nextUntil(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(x_2, x_1, x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
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
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_2);
lean_inc(x_6);
lean_inc_ref(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_apply_2(x_4, x_7, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_2);
x_9 = lean_box(0);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_6);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_6);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_dropPrefix_x3f___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_2);
lean_inc_ref(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_apply_2(x_4, x_7, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec_ref(x_2);
x_9 = lean_box(0);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_5);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_dropSuffix_x3f___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_string_utf8_byte_size(x_2);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = l_String_Slice_dropPrefix___redArg(x_1, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_dropPrefix___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_utf8ByteSize(x_5);
x_7 = l_String_Slice_utf8ByteSize(x_2);
x_8 = lean_nat_dec_le(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
return x_2;
}
else
{
uint8_t x_9; 
x_9 = lean_slice_memcmp(x_2, x_5, x_3, x_3, x_6);
lean_dec_ref(x_5);
if (x_9 == 0)
{
lean_dec(x_6);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
x_13 = l_String_Slice_pos_x21(x_2, x_6);
lean_dec(x_6);
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_2, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_2, 0);
lean_dec(x_17);
x_18 = lean_nat_add(x_11, x_13);
lean_dec(x_13);
lean_dec(x_11);
lean_ctor_set(x_2, 1, x_18);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_19 = lean_nat_add(x_11, x_13);
lean_dec(x_13);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_12);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00String_stripPrefix_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_stripPrefix(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_String_dropPrefix___at___00String_stripPrefix_spec__0(x_1, x_2);
x_4 = l_String_Slice_toString(x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_string_utf8_byte_size(x_2);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = l_String_Slice_dropSuffix___redArg(x_1, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_dropSuffix___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_utf8ByteSize(x_5);
x_7 = l_String_Slice_utf8ByteSize(x_2);
x_8 = lean_nat_dec_le(x_6, x_7);
if (x_8 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_2;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_nat_sub(x_7, x_6);
lean_dec(x_7);
x_10 = lean_slice_memcmp(x_2, x_5, x_9, x_3, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
if (x_10 == 0)
{
lean_dec(x_9);
return x_2;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = l_String_Slice_pos_x21(x_2, x_9);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_2, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_2, 0);
lean_dec(x_17);
x_18 = lean_nat_add(x_12, x_13);
lean_dec(x_13);
lean_ctor_set(x_2, 2, x_18);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_19 = lean_nat_add(x_12, x_13);
lean_dec(x_13);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_12);
lean_ctor_set(x_20, 2, x_19);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00String_stripSuffix_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_stripSuffix(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_String_dropSuffix___at___00String_stripSuffix_spec__0(x_1, x_2);
x_4 = l_String_Slice_toString(x_3);
lean_dec_ref(x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Substring(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Substring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_trimAsciiEnd___closed__0 = _init_l_String_trimAsciiEnd___closed__0();
lean_mark_persistent(l_String_trimAsciiEnd___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
