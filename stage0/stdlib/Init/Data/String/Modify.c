// Lean compiler output
// Module: Init.Data.String.Modify
// Imports: public import Init.Data.String.Basic public import Init.Data.String.Termination import Init.Data.ByteArray.Lemmas import Init.Data.Char.Lemmas
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
LEAN_EXPORT lean_object* l_String_Pos_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_set___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_Pos_pastModify___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_appendRight___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_set___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_pastModify___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_pastModify(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
static lean_object* l_String_toLower___closed__0;
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_modify___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_decapitalize(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
static lean_object* l_String_toUpper___closed__0;
LEAN_EXPORT lean_object* l_String_Pos_appendRight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_pastSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_pastModify___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Char_toLower___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_pastSet___redArg(lean_object*, uint32_t);
lean_object* l_Char_toUpper___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_modify___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_modify(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_toUpper(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toSetOfLE___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_modify(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_pastSet___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toSetOfLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_pastSet(lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* lean_string_capitalize(lean_object*);
LEAN_EXPORT lean_object* l_String_toLower(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toSetOfLE___redArg___boxed(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_appendRight___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_modify(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_map(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_modify___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_Pos_appendRight___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toSetOfLE(lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_capitalize(lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_set___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_6 = lean_string_utf8_set(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSetOfLE___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSetOfLE___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Pos_toSetOfLE___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSetOfLE(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint32_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toSetOfLE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_8 = l_String_Pos_toSetOfLE(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastSet___redArg(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Char_utf8Size(x_2);
x_4 = lean_nat_add(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastSet___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_String_Pos_pastSet___redArg(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastSet(lean_object* x_1, lean_object* x_2, uint32_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Char_utf8Size(x_3);
x_6 = lean_nat_add(x_2, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_6 = l_String_Pos_pastSet(x_1, x_2, x_5, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Pos_appendRight___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_Pos_appendRight___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Pos_appendRight___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Pos_appendRight(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Pos_appendRight___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Pos_appendRight(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Pos_modify___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; 
x_4 = lean_string_utf8_get_fast(x_1, x_2);
x_5 = lean_box_uint32(x_4);
x_6 = lean_apply_1(x_3, x_5);
x_7 = lean_unbox_uint32(x_6);
lean_dec(x_6);
x_8 = lean_string_utf8_set(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_Pos_modify(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; 
x_5 = lean_string_utf8_get_fast(x_1, x_2);
x_6 = lean_box_uint32(x_5);
x_7 = lean_apply_1(x_3, x_6);
x_8 = lean_unbox_uint32(x_7);
lean_dec(x_7);
x_9 = lean_string_utf8_set(x_1, x_2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Pos_toModifyOfLE___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Pos_toModifyOfLE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_String_Pos_toModifyOfLE(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastModify___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_string_utf8_get_fast(x_1, x_2);
x_5 = lean_box_uint32(x_4);
x_6 = lean_apply_1(x_3, x_5);
x_7 = lean_unbox_uint32(x_6);
lean_dec(x_6);
x_8 = l_Char_utf8Size(x_7);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastModify___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Pos_pastModify___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastModify(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_string_utf8_get_fast(x_1, x_2);
x_6 = lean_box_uint32(x_5);
x_7 = lean_apply_1(x_3, x_6);
x_8 = lean_unbox_uint32(x_7);
lean_dec(x_7);
x_9 = l_Char_utf8Size(x_8);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_String_Pos_pastModify___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_Pos_pastModify(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
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
LEAN_EXPORT lean_object* l_String_Pos_Raw_modify(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_String_Pos_Raw_modify___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Pos_Raw_modify(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
LEAN_EXPORT lean_object* l_String_mapAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint32_t x_6; lean_object* x_7; lean_object* x_8; uint32_t x_9; lean_object* x_10; uint32_t x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_string_utf8_get_fast(x_2, x_3);
x_7 = lean_box_uint32(x_6);
lean_inc_ref(x_1);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_unbox_uint32(x_8);
lean_inc(x_3);
x_10 = lean_string_utf8_set(x_2, x_3, x_9);
x_11 = lean_unbox_uint32(x_8);
lean_dec(x_8);
x_12 = l_Char_utf8Size(x_11);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_12);
lean_dec(x_3);
x_2 = x_10;
x_3 = x_13;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_String_map(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_mapAux(x_1, x_2, x_3);
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
x_4 = l_String_mapAux(x_2, x_1, x_3);
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
x_4 = l_String_mapAux(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_capitalize(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = 97;
x_5 = lean_uint32_dec_le(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_string_utf8_set(x_1, x_2, x_3);
return x_6;
}
else
{
uint32_t x_7; uint8_t x_8; 
x_7 = 122;
x_8 = lean_uint32_dec_le(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_string_utf8_set(x_1, x_2, x_3);
return x_9;
}
else
{
uint32_t x_10; uint32_t x_11; lean_object* x_12; 
x_10 = 4294967264;
x_11 = lean_uint32_add(x_3, x_10);
x_12 = lean_string_utf8_set(x_1, x_2, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* lean_string_capitalize(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = 97;
x_5 = lean_uint32_dec_le(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_string_utf8_set(x_1, x_2, x_3);
return x_6;
}
else
{
uint32_t x_7; uint8_t x_8; 
x_7 = 122;
x_8 = lean_uint32_dec_le(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_string_utf8_set(x_1, x_2, x_3);
return x_9;
}
else
{
uint32_t x_10; uint32_t x_11; lean_object* x_12; 
x_10 = 4294967264;
x_11 = lean_uint32_add(x_3, x_10);
x_12 = lean_string_utf8_set(x_1, x_2, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_String_decapitalize(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = 65;
x_5 = lean_uint32_dec_le(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_string_utf8_set(x_1, x_2, x_3);
return x_6;
}
else
{
uint32_t x_7; uint8_t x_8; 
x_7 = 90;
x_8 = lean_uint32_dec_le(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_string_utf8_set(x_1, x_2, x_3);
return x_9;
}
else
{
uint32_t x_10; uint32_t x_11; lean_object* x_12; 
x_10 = 32;
x_11 = lean_uint32_add(x_3, x_10);
x_12 = lean_string_utf8_set(x_1, x_2, x_11);
return x_12;
}
}
}
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Modify(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_toUpper___closed__0 = _init_l_String_toUpper___closed__0();
lean_mark_persistent(l_String_toUpper___closed__0);
l_String_toLower___closed__0 = _init_l_String_toLower___closed__0();
lean_mark_persistent(l_String_toLower___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
