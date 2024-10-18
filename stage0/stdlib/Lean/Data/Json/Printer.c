// Lean compiler output
// Module: Lean.Data.Json.Printer
// Imports: Lean.Data.Format Lean.Data.Json.Basic Init.Data.List.Impl
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
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_compress(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lean_Json_compress_go___closed__1;
lean_object* l_Lean_JsonNumber_toString(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Json_compress_go___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__3;
static lean_object* l_Lean_Json_render___closed__9;
static lean_object* l_Lean_Json_render___closed__19;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Json_renderString___closed__1;
static lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__2;
static lean_object* l_Lean_Json_render___closed__12;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l_Lean_Json_render___closed__20;
static lean_object* l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
static lean_object* l_Lean_Json_render___closed__6;
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Json_render___closed__14;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_escape(lean_object*, lean_object*);
uint32_t l_Nat_digitChar(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Json_compress_go___spec__2(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__1;
static lean_object* l_Lean_Json_render___closed__17;
static lean_object* l_Lean_Json_render___closed__4;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Json_compress_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Json_render___closed__11;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Json_compress_go___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_Json_render___closed__16;
static lean_object* l_Lean_Json_render___closed__13;
LEAN_EXPORT lean_object* l_Lean_Json_renderString___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Json_instToFormat___closed__1;
static lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Json_render___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Json_render___closed__5;
static lean_object* l_Lean_Json_render___closed__7;
static lean_object* l_Lean_Json_render___closed__15;
static lean_object* l_Lean_Json_render___closed__3;
static lean_object* l_Lean_Json_render___closed__10;
LEAN_EXPORT lean_object* l_String_foldlAux___at_Lean_Json_escape___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Json_render___closed__1;
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Json_compress_go___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_instToString(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Json_render___spec__1(size_t, size_t, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Json_compress_go___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep___at_Prod_repr___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___at_Lean_Json_escape___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_renderString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_compress_go(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__4;
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Json_render___closed__18;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_escape___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Json_render___closed__8;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_render(lean_object*);
static lean_object* l_Lean_Json_render___closed__2;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2;
static lean_object* l_Lean_Json_render___closed__21;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Json_render___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_instToFormat;
LEAN_EXPORT lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(lean_object*, uint32_t);
static lean_object* l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__3;
static lean_object* _init_l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\\u", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\\r", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\\n", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\\\\", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\\\"", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; uint32_t x_25; uint8_t x_26; 
x_25 = 34;
x_26 = lean_uint32_dec_eq(x_2, x_25);
if (x_26 == 0)
{
uint32_t x_27; uint8_t x_28; 
x_27 = 92;
x_28 = lean_uint32_dec_eq(x_2, x_27);
if (x_28 == 0)
{
uint32_t x_29; uint8_t x_30; 
x_29 = 10;
x_30 = lean_uint32_dec_eq(x_2, x_29);
if (x_30 == 0)
{
uint32_t x_31; uint8_t x_32; 
x_31 = 13;
x_32 = lean_uint32_dec_eq(x_2, x_31);
if (x_32 == 0)
{
uint32_t x_33; uint8_t x_34; 
x_33 = 32;
x_34 = lean_uint32_dec_le(x_33, x_2);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_box(0);
x_3 = x_35;
goto block_24;
}
else
{
uint32_t x_36; uint8_t x_37; 
x_36 = 1114111;
x_37 = lean_uint32_dec_le(x_2, x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_box(0);
x_3 = x_38;
goto block_24;
}
else
{
lean_object* x_39; 
x_39 = lean_string_push(x_1, x_2);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__2;
x_41 = lean_string_append(x_1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__3;
x_43 = lean_string_append(x_1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__4;
x_45 = lean_string_append(x_1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__5;
x_47 = lean_string_append(x_1, x_46);
return x_47;
}
block_24:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; lean_object* x_16; uint32_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_3);
x_4 = lean_uint32_to_nat(x_2);
x_5 = lean_unsigned_to_nat(4096u);
x_6 = lean_nat_div(x_4, x_5);
x_7 = l_Nat_digitChar(x_6);
lean_dec(x_6);
x_8 = lean_nat_mod(x_4, x_5);
x_9 = lean_unsigned_to_nat(256u);
x_10 = lean_nat_div(x_8, x_9);
lean_dec(x_8);
x_11 = l_Nat_digitChar(x_10);
lean_dec(x_10);
x_12 = lean_nat_mod(x_4, x_9);
x_13 = lean_unsigned_to_nat(16u);
x_14 = lean_nat_div(x_12, x_13);
lean_dec(x_12);
x_15 = l_Nat_digitChar(x_14);
lean_dec(x_14);
x_16 = lean_nat_mod(x_4, x_13);
lean_dec(x_4);
x_17 = l_Nat_digitChar(x_16);
lean_dec(x_16);
x_18 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__1;
x_19 = lean_string_append(x_1, x_18);
x_20 = lean_string_push(x_19, x_7);
x_21 = lean_string_push(x_20, x_11);
x_22 = lean_string_push(x_21, x_15);
x_23 = lean_string_push(x_22, x_17);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at_Lean_Json_escape___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_6; uint32_t x_7; lean_object* x_8; 
x_6 = lean_string_utf8_next(x_1, x_3);
x_7 = lean_string_utf8_get(x_1, x_3);
lean_dec(x_3);
x_8 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(x_4, x_7);
x_3 = x_6;
x_4 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_escape(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_String_foldlAux___at_Lean_Json_escape___spec__1(x_1, x_3, x_4, x_2);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at_Lean_Json_escape___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_foldlAux___at_Lean_Json_escape___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_escape___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_escape(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Json_renderString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_renderString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Json_renderString___closed__1;
x_4 = lean_string_append(x_2, x_3);
x_5 = l_Lean_Json_escape(x_1, x_4);
x_6 = lean_string_append(x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_renderString___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_renderString(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Json_render___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Json_render(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
static lean_object* _init_l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Json_render___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2(x_1, x_3);
x_8 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_9 = l_Lean_Json_renderString(x_4, x_8);
lean_dec(x_4);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__3;
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Json_render(x_5);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = 0;
x_18 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
x_1 = x_19;
x_2 = x_6;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Json_render___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_render___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_render___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_render___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_render___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_render___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_render___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_render___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_render___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_render___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_render___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_render___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_render___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Json_render___closed__8;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Json_render___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_render___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_render___closed__10;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_render___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_render___closed__11;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_render___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_render___closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_render___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_render___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_render___closed__14;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_render___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_render___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_render___closed__16;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_render___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_render___closed__17;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_render___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_render___closed__16;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_render___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("}", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_render___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_render___closed__20;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_render(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Json_render___closed__2;
return x_2;
}
case 1:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, 0);
lean_dec(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Json_render___closed__4;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_Json_render___closed__6;
return x_5;
}
}
case 2:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = l_Lean_JsonNumber_toString(x_7);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_JsonNumber_toString(x_9);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
case 3:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_15 = l_Lean_Json_renderString(x_13, x_14);
lean_dec(x_13);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_18 = l_Lean_Json_renderString(x_16, x_17);
lean_dec(x_16);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
case 4:
{
lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_array_size(x_20);
x_22 = 0;
x_23 = l_Array_mapMUnsafe_map___at_Lean_Json_render___spec__1(x_21, x_22, x_20);
x_24 = lean_array_to_list(x_23);
x_25 = l_Lean_Json_render___closed__9;
x_26 = l_Std_Format_joinSep___at_Prod_repr___spec__1(x_24, x_25);
x_27 = l_Lean_Json_render___closed__13;
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Json_render___closed__15;
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Json_render___closed__12;
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = 0;
x_34 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
return x_34;
}
default: 
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_box(0);
x_37 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2(x_36, x_35);
x_38 = l_Lean_Json_render___closed__9;
x_39 = l_Std_Format_joinSep___at_Prod_repr___spec__1(x_37, x_38);
x_40 = l_Lean_Json_render___closed__19;
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Json_render___closed__21;
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Json_render___closed__18;
x_45 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = 0;
x_47 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Json_render___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Json_render___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_pretty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Json_render(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_format_pretty(x_3, x_2, x_4, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Json_compress_go___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Json_compress_go___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget(x_1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
x_2 = x_7;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Json_compress_go___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = l_Lean_RBNode_fold___at_Lean_Json_compress_go___spec__3(x_1, x_3);
lean_inc(x_5);
lean_inc(x_4);
x_8 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Json_compress_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(4);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_compress_go(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Json_render___closed__1;
x_7 = lean_string_append(x_1, x_6);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
case 1:
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_4, 0);
lean_dec(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_Json_render___closed__3;
x_12 = lean_string_append(x_1, x_11);
x_1 = x_12;
x_2 = x_10;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_Json_render___closed__5;
x_16 = lean_string_append(x_1, x_15);
x_1 = x_16;
x_2 = x_14;
goto _start;
}
}
case 2:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
lean_dec(x_4);
x_20 = l_Lean_JsonNumber_toString(x_19);
x_21 = lean_string_append(x_1, x_20);
lean_dec(x_20);
x_1 = x_21;
x_2 = x_18;
goto _start;
}
case 3:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
lean_dec(x_4);
x_25 = l_Lean_Json_renderString(x_24, x_1);
lean_dec(x_24);
x_1 = x_25;
x_2 = x_23;
goto _start;
}
case 4:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_28 = lean_ctor_get(x_2, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_4, 0);
lean_inc(x_29);
lean_dec(x_4);
x_30 = l_Lean_Json_render___closed__10;
x_31 = lean_string_append(x_1, x_30);
x_32 = lean_array_size(x_29);
x_33 = 0;
x_34 = l_Array_mapMUnsafe_map___at_Lean_Json_compress_go___spec__1(x_32, x_33, x_29);
x_35 = lean_box(2);
lean_ctor_set(x_2, 0, x_35);
x_36 = lean_array_get_size(x_34);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_dec_lt(x_37, x_36);
if (x_38 == 0)
{
lean_dec(x_36);
lean_dec(x_34);
x_1 = x_31;
goto _start;
}
else
{
size_t x_40; lean_object* x_41; 
x_40 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_41 = l_Array_foldrMUnsafe_fold___at_Lean_Json_compress_go___spec__2(x_34, x_40, x_33, x_2);
lean_dec(x_34);
x_1 = x_31;
x_2 = x_41;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
lean_dec(x_2);
x_44 = lean_ctor_get(x_4, 0);
lean_inc(x_44);
lean_dec(x_4);
x_45 = l_Lean_Json_render___closed__10;
x_46 = lean_string_append(x_1, x_45);
x_47 = lean_array_size(x_44);
x_48 = 0;
x_49 = l_Array_mapMUnsafe_map___at_Lean_Json_compress_go___spec__1(x_47, x_48, x_44);
x_50 = lean_box(2);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_43);
x_52 = lean_array_get_size(x_49);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_nat_dec_lt(x_53, x_52);
if (x_54 == 0)
{
lean_dec(x_52);
lean_dec(x_49);
x_1 = x_46;
x_2 = x_51;
goto _start;
}
else
{
size_t x_56; lean_object* x_57; 
x_56 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_57 = l_Array_foldrMUnsafe_fold___at_Lean_Json_compress_go___spec__2(x_49, x_56, x_48, x_51);
lean_dec(x_49);
x_1 = x_46;
x_2 = x_57;
goto _start;
}
}
}
default: 
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_2, 1);
lean_inc(x_59);
lean_dec(x_2);
x_60 = lean_ctor_get(x_4, 0);
lean_inc(x_60);
lean_dec(x_4);
x_61 = l_Lean_Json_render___closed__16;
x_62 = lean_string_append(x_1, x_61);
x_63 = lean_box(0);
x_64 = l_Lean_RBNode_fold___at_Lean_Json_compress_go___spec__3(x_63, x_60);
lean_dec(x_60);
x_65 = l_Lean_Json_compress_go___closed__1;
x_66 = l_List_appendTR___rarg(x_64, x_65);
x_67 = l_List_appendTR___rarg(x_66, x_59);
x_1 = x_62;
x_2 = x_67;
goto _start;
}
}
}
case 1:
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_2);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_2, 1);
x_71 = lean_ctor_get(x_2, 0);
lean_dec(x_71);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_3);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_ctor_set_tag(x_3, 0);
x_73 = lean_box(5);
lean_ctor_set(x_2, 0, x_73);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_3);
lean_ctor_set(x_74, 1, x_2);
x_2 = x_74;
goto _start;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_3, 0);
lean_inc(x_76);
lean_dec(x_3);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_box(5);
lean_ctor_set(x_2, 0, x_78);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_2);
x_2 = x_79;
goto _start;
}
}
else
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_70, 0);
lean_inc(x_81);
switch (lean_obj_tag(x_81)) {
case 0:
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_81, 0);
lean_dec(x_83);
x_84 = lean_ctor_get(x_3, 0);
lean_inc(x_84);
lean_dec(x_3);
lean_ctor_set(x_81, 0, x_84);
x_85 = lean_box(5);
lean_ctor_set(x_2, 0, x_85);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_2);
x_2 = x_86;
goto _start;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_81);
x_88 = lean_ctor_get(x_3, 0);
lean_inc(x_88);
lean_dec(x_3);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_box(5);
lean_ctor_set(x_2, 0, x_90);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_2);
x_2 = x_91;
goto _start;
}
}
case 1:
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_81);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_81, 0);
lean_dec(x_94);
x_95 = lean_ctor_get(x_3, 0);
lean_inc(x_95);
lean_dec(x_3);
lean_ctor_set_tag(x_81, 0);
lean_ctor_set(x_81, 0, x_95);
x_96 = lean_box(5);
lean_ctor_set(x_2, 0, x_96);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_81);
lean_ctor_set(x_97, 1, x_2);
x_2 = x_97;
goto _start;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_81);
x_99 = lean_ctor_get(x_3, 0);
lean_inc(x_99);
lean_dec(x_3);
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = lean_box(5);
lean_ctor_set(x_2, 0, x_101);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_2);
x_2 = x_102;
goto _start;
}
}
case 2:
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_3);
if (x_104 == 0)
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_70);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_70, 0);
lean_dec(x_106);
lean_ctor_set_tag(x_3, 0);
x_107 = lean_box(2);
lean_ctor_set(x_70, 0, x_107);
goto _start;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_70, 1);
lean_inc(x_109);
lean_dec(x_70);
lean_ctor_set_tag(x_3, 0);
x_110 = lean_box(2);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
lean_ctor_set(x_2, 1, x_111);
goto _start;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_3, 0);
lean_inc(x_113);
lean_dec(x_3);
x_114 = lean_ctor_get(x_70, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_115 = x_70;
} else {
 lean_dec_ref(x_70);
 x_115 = lean_box(0);
}
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_113);
x_117 = lean_box(2);
if (lean_is_scalar(x_115)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_115;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_114);
lean_ctor_set(x_2, 1, x_118);
lean_ctor_set(x_2, 0, x_116);
goto _start;
}
}
default: 
{
uint8_t x_120; 
lean_dec(x_81);
x_120 = !lean_is_exclusive(x_3);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
lean_ctor_set_tag(x_3, 0);
x_121 = lean_box(5);
lean_ctor_set(x_2, 0, x_121);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_3);
lean_ctor_set(x_122, 1, x_2);
x_2 = x_122;
goto _start;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_3, 0);
lean_inc(x_124);
lean_dec(x_3);
x_125 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_125, 0, x_124);
x_126 = lean_box(5);
lean_ctor_set(x_2, 0, x_126);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_2);
x_2 = x_127;
goto _start;
}
}
}
}
}
else
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_2, 1);
lean_inc(x_129);
lean_dec(x_2);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_3, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_131 = x_3;
} else {
 lean_dec_ref(x_3);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 1, 0);
} else {
 x_132 = x_131;
 lean_ctor_set_tag(x_132, 0);
}
lean_ctor_set(x_132, 0, x_130);
x_133 = lean_box(5);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_129);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_134);
x_2 = x_135;
goto _start;
}
else
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_129, 0);
lean_inc(x_137);
switch (lean_obj_tag(x_137)) {
case 0:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_138 = x_137;
} else {
 lean_dec_ref(x_137);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_3, 0);
lean_inc(x_139);
lean_dec(x_3);
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(0, 1, 0);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_139);
x_141 = lean_box(5);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_129);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_142);
x_2 = x_143;
goto _start;
}
case 1:
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_145 = x_137;
} else {
 lean_dec_ref(x_137);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_3, 0);
lean_inc(x_146);
lean_dec(x_3);
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(0, 1, 0);
} else {
 x_147 = x_145;
 lean_ctor_set_tag(x_147, 0);
}
lean_ctor_set(x_147, 0, x_146);
x_148 = lean_box(5);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_129);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_149);
x_2 = x_150;
goto _start;
}
case 2:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_152 = lean_ctor_get(x_3, 0);
lean_inc(x_152);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_153 = x_3;
} else {
 lean_dec_ref(x_3);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_129, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_155 = x_129;
} else {
 lean_dec_ref(x_129);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_156 = lean_alloc_ctor(0, 1, 0);
} else {
 x_156 = x_153;
 lean_ctor_set_tag(x_156, 0);
}
lean_ctor_set(x_156, 0, x_152);
x_157 = lean_box(2);
if (lean_is_scalar(x_155)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_155;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_154);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_158);
x_2 = x_159;
goto _start;
}
default: 
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_137);
x_161 = lean_ctor_get(x_3, 0);
lean_inc(x_161);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_162 = x_3;
} else {
 lean_dec_ref(x_3);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(0, 1, 0);
} else {
 x_163 = x_162;
 lean_ctor_set_tag(x_163, 0);
}
lean_ctor_set(x_163, 0, x_161);
x_164 = lean_box(5);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_129);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_165);
x_2 = x_166;
goto _start;
}
}
}
}
}
case 2:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_2, 1);
lean_inc(x_168);
lean_dec(x_2);
x_169 = l_Lean_Json_render___closed__14;
x_170 = lean_string_append(x_1, x_169);
x_1 = x_170;
x_2 = x_168;
goto _start;
}
case 3:
{
uint8_t x_172; 
x_172 = !lean_is_exclusive(x_2);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_2, 1);
x_174 = lean_ctor_get(x_2, 0);
lean_dec(x_174);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_175 = lean_ctor_get(x_3, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_3, 1);
lean_inc(x_176);
lean_dec(x_3);
x_177 = l_Lean_Json_renderString(x_175, x_1);
lean_dec(x_175);
x_178 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2;
x_179 = lean_string_append(x_177, x_178);
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_176);
x_181 = lean_box(5);
lean_ctor_set(x_2, 0, x_181);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_2);
x_1 = x_179;
x_2 = x_182;
goto _start;
}
else
{
lean_object* x_184; 
x_184 = lean_ctor_get(x_173, 0);
lean_inc(x_184);
switch (lean_obj_tag(x_184)) {
case 0:
{
uint8_t x_185; 
x_185 = !lean_is_exclusive(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_186 = lean_ctor_get(x_184, 0);
lean_dec(x_186);
x_187 = lean_ctor_get(x_3, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_3, 1);
lean_inc(x_188);
lean_dec(x_3);
x_189 = l_Lean_Json_renderString(x_187, x_1);
lean_dec(x_187);
x_190 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2;
x_191 = lean_string_append(x_189, x_190);
lean_ctor_set(x_184, 0, x_188);
x_192 = lean_box(5);
lean_ctor_set(x_2, 0, x_192);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_184);
lean_ctor_set(x_193, 1, x_2);
x_1 = x_191;
x_2 = x_193;
goto _start;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_184);
x_195 = lean_ctor_get(x_3, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_3, 1);
lean_inc(x_196);
lean_dec(x_3);
x_197 = l_Lean_Json_renderString(x_195, x_1);
lean_dec(x_195);
x_198 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2;
x_199 = lean_string_append(x_197, x_198);
x_200 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_200, 0, x_196);
x_201 = lean_box(5);
lean_ctor_set(x_2, 0, x_201);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_2);
x_1 = x_199;
x_2 = x_202;
goto _start;
}
}
case 1:
{
uint8_t x_204; 
x_204 = !lean_is_exclusive(x_184);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_205 = lean_ctor_get(x_184, 0);
lean_dec(x_205);
x_206 = lean_ctor_get(x_3, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_3, 1);
lean_inc(x_207);
lean_dec(x_3);
x_208 = l_Lean_Json_renderString(x_206, x_1);
lean_dec(x_206);
x_209 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2;
x_210 = lean_string_append(x_208, x_209);
lean_ctor_set_tag(x_184, 0);
lean_ctor_set(x_184, 0, x_207);
x_211 = lean_box(5);
lean_ctor_set(x_2, 0, x_211);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_184);
lean_ctor_set(x_212, 1, x_2);
x_1 = x_210;
x_2 = x_212;
goto _start;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_184);
x_214 = lean_ctor_get(x_3, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_3, 1);
lean_inc(x_215);
lean_dec(x_3);
x_216 = l_Lean_Json_renderString(x_214, x_1);
lean_dec(x_214);
x_217 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2;
x_218 = lean_string_append(x_216, x_217);
x_219 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_219, 0, x_215);
x_220 = lean_box(5);
lean_ctor_set(x_2, 0, x_220);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_2);
x_1 = x_218;
x_2 = x_221;
goto _start;
}
}
case 4:
{
lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_223 = lean_ctor_get(x_3, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_3, 1);
lean_inc(x_224);
lean_dec(x_3);
x_225 = !lean_is_exclusive(x_173);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_226 = lean_ctor_get(x_173, 0);
lean_dec(x_226);
x_227 = l_Lean_Json_renderString(x_223, x_1);
lean_dec(x_223);
x_228 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2;
x_229 = lean_string_append(x_227, x_228);
x_230 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_230, 0, x_224);
x_231 = lean_box(4);
lean_ctor_set(x_173, 0, x_231);
lean_ctor_set(x_2, 0, x_230);
x_1 = x_229;
goto _start;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_233 = lean_ctor_get(x_173, 1);
lean_inc(x_233);
lean_dec(x_173);
x_234 = l_Lean_Json_renderString(x_223, x_1);
lean_dec(x_223);
x_235 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2;
x_236 = lean_string_append(x_234, x_235);
x_237 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_237, 0, x_224);
x_238 = lean_box(4);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_233);
lean_ctor_set(x_2, 1, x_239);
lean_ctor_set(x_2, 0, x_237);
x_1 = x_236;
goto _start;
}
}
default: 
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_184);
x_241 = lean_ctor_get(x_3, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_3, 1);
lean_inc(x_242);
lean_dec(x_3);
x_243 = l_Lean_Json_renderString(x_241, x_1);
lean_dec(x_241);
x_244 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2;
x_245 = lean_string_append(x_243, x_244);
x_246 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_246, 0, x_242);
x_247 = lean_box(5);
lean_ctor_set(x_2, 0, x_247);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_2);
x_1 = x_245;
x_2 = x_248;
goto _start;
}
}
}
}
else
{
lean_object* x_250; 
x_250 = lean_ctor_get(x_2, 1);
lean_inc(x_250);
lean_dec(x_2);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_251 = lean_ctor_get(x_3, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_3, 1);
lean_inc(x_252);
lean_dec(x_3);
x_253 = l_Lean_Json_renderString(x_251, x_1);
lean_dec(x_251);
x_254 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2;
x_255 = lean_string_append(x_253, x_254);
x_256 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_256, 0, x_252);
x_257 = lean_box(5);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_250);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_258);
x_1 = x_255;
x_2 = x_259;
goto _start;
}
else
{
lean_object* x_261; 
x_261 = lean_ctor_get(x_250, 0);
lean_inc(x_261);
switch (lean_obj_tag(x_261)) {
case 0:
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 x_262 = x_261;
} else {
 lean_dec_ref(x_261);
 x_262 = lean_box(0);
}
x_263 = lean_ctor_get(x_3, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_3, 1);
lean_inc(x_264);
lean_dec(x_3);
x_265 = l_Lean_Json_renderString(x_263, x_1);
lean_dec(x_263);
x_266 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2;
x_267 = lean_string_append(x_265, x_266);
if (lean_is_scalar(x_262)) {
 x_268 = lean_alloc_ctor(0, 1, 0);
} else {
 x_268 = x_262;
}
lean_ctor_set(x_268, 0, x_264);
x_269 = lean_box(5);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_250);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_270);
x_1 = x_267;
x_2 = x_271;
goto _start;
}
case 1:
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 x_273 = x_261;
} else {
 lean_dec_ref(x_261);
 x_273 = lean_box(0);
}
x_274 = lean_ctor_get(x_3, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_3, 1);
lean_inc(x_275);
lean_dec(x_3);
x_276 = l_Lean_Json_renderString(x_274, x_1);
lean_dec(x_274);
x_277 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2;
x_278 = lean_string_append(x_276, x_277);
if (lean_is_scalar(x_273)) {
 x_279 = lean_alloc_ctor(0, 1, 0);
} else {
 x_279 = x_273;
 lean_ctor_set_tag(x_279, 0);
}
lean_ctor_set(x_279, 0, x_275);
x_280 = lean_box(5);
x_281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_250);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_281);
x_1 = x_278;
x_2 = x_282;
goto _start;
}
case 4:
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_284 = lean_ctor_get(x_3, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_3, 1);
lean_inc(x_285);
lean_dec(x_3);
x_286 = lean_ctor_get(x_250, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_287 = x_250;
} else {
 lean_dec_ref(x_250);
 x_287 = lean_box(0);
}
x_288 = l_Lean_Json_renderString(x_284, x_1);
lean_dec(x_284);
x_289 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2;
x_290 = lean_string_append(x_288, x_289);
x_291 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_291, 0, x_285);
x_292 = lean_box(4);
if (lean_is_scalar(x_287)) {
 x_293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_293 = x_287;
}
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_286);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_293);
x_1 = x_290;
x_2 = x_294;
goto _start;
}
default: 
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_261);
x_296 = lean_ctor_get(x_3, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_3, 1);
lean_inc(x_297);
lean_dec(x_3);
x_298 = l_Lean_Json_renderString(x_296, x_1);
lean_dec(x_296);
x_299 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2;
x_300 = lean_string_append(x_298, x_299);
x_301 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_301, 0, x_297);
x_302 = lean_box(5);
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_250);
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_301);
lean_ctor_set(x_304, 1, x_303);
x_1 = x_300;
x_2 = x_304;
goto _start;
}
}
}
}
}
case 4:
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_2, 1);
lean_inc(x_306);
lean_dec(x_2);
x_307 = l_Lean_Json_render___closed__20;
x_308 = lean_string_append(x_1, x_307);
x_1 = x_308;
x_2 = x_306;
goto _start;
}
default: 
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_2, 1);
lean_inc(x_310);
lean_dec(x_2);
x_311 = l_Lean_Json_render___closed__7;
x_312 = lean_string_append(x_1, x_311);
x_1 = x_312;
x_2 = x_310;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Json_compress_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Json_compress_go___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Json_compress_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at_Lean_Json_compress_go___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Json_compress_go___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_fold___at_Lean_Json_compress_go___spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_compress(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_6 = l_Lean_Json_compress_go(x_5, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Json_instToFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_render), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_instToFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Json_instToFormat___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(80u);
x_3 = l_Lean_Json_pretty(x_1, x_2);
return x_3;
}
}
lean_object* initialize_Lean_Data_Format(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Json_Printer(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Format(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Impl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__1 = _init_l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__1();
lean_mark_persistent(l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__1);
l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__2 = _init_l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__2();
lean_mark_persistent(l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__2);
l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__3 = _init_l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__3();
lean_mark_persistent(l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__3);
l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__4 = _init_l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__4();
lean_mark_persistent(l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__4);
l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__5 = _init_l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__5();
lean_mark_persistent(l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__5);
l_Lean_Json_renderString___closed__1 = _init_l_Lean_Json_renderString___closed__1();
lean_mark_persistent(l_Lean_Json_renderString___closed__1);
l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1 = _init_l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1();
lean_mark_persistent(l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1);
l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2 = _init_l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2();
lean_mark_persistent(l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2);
l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__3 = _init_l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__3();
lean_mark_persistent(l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__3);
l_Lean_Json_render___closed__1 = _init_l_Lean_Json_render___closed__1();
lean_mark_persistent(l_Lean_Json_render___closed__1);
l_Lean_Json_render___closed__2 = _init_l_Lean_Json_render___closed__2();
lean_mark_persistent(l_Lean_Json_render___closed__2);
l_Lean_Json_render___closed__3 = _init_l_Lean_Json_render___closed__3();
lean_mark_persistent(l_Lean_Json_render___closed__3);
l_Lean_Json_render___closed__4 = _init_l_Lean_Json_render___closed__4();
lean_mark_persistent(l_Lean_Json_render___closed__4);
l_Lean_Json_render___closed__5 = _init_l_Lean_Json_render___closed__5();
lean_mark_persistent(l_Lean_Json_render___closed__5);
l_Lean_Json_render___closed__6 = _init_l_Lean_Json_render___closed__6();
lean_mark_persistent(l_Lean_Json_render___closed__6);
l_Lean_Json_render___closed__7 = _init_l_Lean_Json_render___closed__7();
lean_mark_persistent(l_Lean_Json_render___closed__7);
l_Lean_Json_render___closed__8 = _init_l_Lean_Json_render___closed__8();
lean_mark_persistent(l_Lean_Json_render___closed__8);
l_Lean_Json_render___closed__9 = _init_l_Lean_Json_render___closed__9();
lean_mark_persistent(l_Lean_Json_render___closed__9);
l_Lean_Json_render___closed__10 = _init_l_Lean_Json_render___closed__10();
lean_mark_persistent(l_Lean_Json_render___closed__10);
l_Lean_Json_render___closed__11 = _init_l_Lean_Json_render___closed__11();
lean_mark_persistent(l_Lean_Json_render___closed__11);
l_Lean_Json_render___closed__12 = _init_l_Lean_Json_render___closed__12();
lean_mark_persistent(l_Lean_Json_render___closed__12);
l_Lean_Json_render___closed__13 = _init_l_Lean_Json_render___closed__13();
lean_mark_persistent(l_Lean_Json_render___closed__13);
l_Lean_Json_render___closed__14 = _init_l_Lean_Json_render___closed__14();
lean_mark_persistent(l_Lean_Json_render___closed__14);
l_Lean_Json_render___closed__15 = _init_l_Lean_Json_render___closed__15();
lean_mark_persistent(l_Lean_Json_render___closed__15);
l_Lean_Json_render___closed__16 = _init_l_Lean_Json_render___closed__16();
lean_mark_persistent(l_Lean_Json_render___closed__16);
l_Lean_Json_render___closed__17 = _init_l_Lean_Json_render___closed__17();
lean_mark_persistent(l_Lean_Json_render___closed__17);
l_Lean_Json_render___closed__18 = _init_l_Lean_Json_render___closed__18();
lean_mark_persistent(l_Lean_Json_render___closed__18);
l_Lean_Json_render___closed__19 = _init_l_Lean_Json_render___closed__19();
lean_mark_persistent(l_Lean_Json_render___closed__19);
l_Lean_Json_render___closed__20 = _init_l_Lean_Json_render___closed__20();
lean_mark_persistent(l_Lean_Json_render___closed__20);
l_Lean_Json_render___closed__21 = _init_l_Lean_Json_render___closed__21();
lean_mark_persistent(l_Lean_Json_render___closed__21);
l_Lean_Json_compress_go___closed__1 = _init_l_Lean_Json_compress_go___closed__1();
lean_mark_persistent(l_Lean_Json_compress_go___closed__1);
l_Lean_Json_instToFormat___closed__1 = _init_l_Lean_Json_instToFormat___closed__1();
lean_mark_persistent(l_Lean_Json_instToFormat___closed__1);
l_Lean_Json_instToFormat = _init_l_Lean_Json_instToFormat();
lean_mark_persistent(l_Lean_Json_instToFormat);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
