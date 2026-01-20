// Lean compiler output
// Module: Init.Data.String.Bootstrap
// Imports: public import Init.Data.Char.Basic public import Init.Data.ByteArray.Bootstrap
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
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_append___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_asString(lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_pushn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_contains___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_intercalate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_nextWhile___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_posof(lean_object*, uint32_t);
lean_object* lean_substring_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_trim(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_all___boxed(lean_object*, lean_object*);
uint32_t lean_substring_front(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_string_isprefixof(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_trim___boxed(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_Internal_length___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_next___boxed(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_isEmpty___boxed(lean_object*);
lean_object* lean_string_foldl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_isPrefixOf___boxed(lean_object*, lean_object*);
uint8_t lean_string_contains(lean_object*, uint32_t);
lean_object* lean_substring_takewhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_drop___boxed(lean_object*, lean_object*);
uint8_t lean_substring_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_any___boxed(lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_Internal_min___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_prev___boxed(lean_object*, lean_object*);
lean_object* lean_string_offsetofpos(lean_object*, lean_object*);
uint8_t lean_substring_isempty(lean_object*);
lean_object* lean_substring_drop(lean_object*, lean_object*);
lean_object* lean_substring_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instInhabited;
LEAN_EXPORT lean_object* l_String_Internal_offsetOfPos___boxed(lean_object*, lean_object*);
lean_object* lean_string_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_singleton___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Char_toString(uint32_t);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_capitalize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_push___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_beq___boxed(lean_object*, lean_object*);
lean_object* lean_substring_tostring(lean_object*);
uint8_t lean_substring_all(lean_object*, lean_object*);
lean_object* lean_string_pos_min(lean_object*, lean_object*);
lean_object* lean_string_pushn(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Char_toString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_extract___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_atEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_dropRight___boxed(lean_object*, lean_object*);
lean_object* lean_string_nextwhile(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instOfNatRaw;
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_takeWhile___boxed(lean_object*, lean_object*);
uint32_t lean_string_front(lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_posOf___boxed(lean_object*, lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_foldl___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_isempty(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_toString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_singleton(uint32_t);
LEAN_EXPORT lean_object* l_String_mk___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_drop___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_Internal_sub___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_front___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_extract___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_dropright(lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
static lean_object* l_String_instInhabited___closed__0;
LEAN_EXPORT lean_object* l_String_Internal_getUTF8Byte___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_front___boxed(lean_object*);
uint8_t lean_string_any(lean_object*, lean_object*);
lean_object* lean_string_pos_sub(lean_object*, lean_object*);
uint32_t lean_substring_get(lean_object*, lean_object*);
lean_object* lean_string_capitalize(lean_object*);
static lean_object* _init_l_String_instOfNatRaw() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_String_instInhabited___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_String_instInhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_String_instInhabited___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_push___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = lean_string_push(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_singleton(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_String_instInhabited___closed__0;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_singleton___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_String_singleton(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Internal_posOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = lean_string_posof(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Internal_offsetOfPos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_offsetofpos(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Internal_extract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_String_Internal_length___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_length(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Internal_pushn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_string_pushn(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Internal_append___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_append(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Internal_next___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Internal_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_string_isempty(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Internal_foldl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_string_foldl(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Internal_isPrefixOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_string_isprefixof(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Internal_any___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_string_any(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Internal_contains___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_String_Internal_get___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_String_Internal_capitalize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_capitalize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Internal_atEnd___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_String_Internal_nextWhile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_string_nextwhile(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Internal_trim___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_trim(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Internal_intercalate___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_intercalate(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Internal_front___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_string_front(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Internal_drop___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_drop(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Internal_dropRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_dropright(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Internal_getUTF8Byte___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_string_get_byte_fast(x_1, x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_mk___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_asString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_toString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_substring_tostring(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_drop___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_substring_drop(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_front___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_substring_front(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_takeWhile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_substring_takewhile(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_extract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_substring_extract(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_all___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_substring_all(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_substring_beq(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_substring_isempty(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_get___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_substring_get(x_1, x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_prev___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_substring_prev(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_Internal_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_pos_sub(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_Internal_min___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_pos_min(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Char_toString(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_String_instInhabited___closed__0;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Char_toString___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_toString(x_2);
return x_3;
}
}
lean_object* initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray_Bootstrap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Bootstrap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_instOfNatRaw = _init_l_String_instOfNatRaw();
lean_mark_persistent(l_String_instOfNatRaw);
l_String_instInhabited___closed__0 = _init_l_String_instInhabited___closed__0();
lean_mark_persistent(l_String_instInhabited___closed__0);
l_String_instInhabited = _init_l_String_instInhabited();
lean_mark_persistent(l_String_instInhabited);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
