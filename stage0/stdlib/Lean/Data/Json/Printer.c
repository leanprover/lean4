// Lean compiler output
// Module: Lean.Data.Json.Printer
// Imports: Lean.Data.Format Lean.Data.Json.Basic
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__3;
static lean_object* l_Lean_Json_render___closed__9;
static lean_object* l_Lean_Json_render___closed__19;
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
LEAN_EXPORT lean_object* l_Lean_Json_escape(lean_object*);
uint32_t l_Nat_digitChar(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__1;
static lean_object* l_Lean_Json_render___closed__17;
static lean_object* l_Lean_Json_render___closed__4;
lean_object* lean_string_mk(lean_object*);
static lean_object* l_Lean_Json_render___closed__11;
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Lean_Json_render___closed__16;
static lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__6;
static lean_object* l_Lean_Json_render___closed__13;
LEAN_EXPORT lean_object* l_Lean_Json_renderString___boxed(lean_object*);
static lean_object* l_Lean_Json_instToFormat___closed__1;
static lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Json_render___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Json_render___closed__5;
static lean_object* l_Lean_Json_render___closed__7;
static lean_object* l_Lean_Json_render___closed__15;
static lean_object* l_Lean_Json_render___closed__3;
static lean_object* l_Lean_Json_render___closed__10;
LEAN_EXPORT lean_object* l_String_foldlAux___at_Lean_Json_escape___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Json_compress_go___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Json_render___closed__1;
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_instToString(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Json_render___spec__1(size_t, size_t, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Json_compress_go___spec__2(lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep___at_Prod_repr___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___at_Lean_Json_escape___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_renderString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_compress_go(lean_object*, lean_object*);
static lean_object* l_Lean_Json_compress_go___closed__2;
static lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__4;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Json_render___closed__18;
LEAN_EXPORT lean_object* l_List_map___at_Lean_Json_compress_go___spec__1(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Json_escape___boxed(lean_object*);
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
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\\r", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\\n", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\\\\", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__6() {
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
lean_object* x_3; uint32_t x_32; uint8_t x_33; 
x_32 = 34;
x_33 = lean_uint32_dec_eq(x_2, x_32);
if (x_33 == 0)
{
uint32_t x_34; uint8_t x_35; 
x_34 = 92;
x_35 = lean_uint32_dec_eq(x_2, x_34);
if (x_35 == 0)
{
uint32_t x_36; uint8_t x_37; 
x_36 = 10;
x_37 = lean_uint32_dec_eq(x_2, x_36);
if (x_37 == 0)
{
uint32_t x_38; uint8_t x_39; 
x_38 = 13;
x_39 = lean_uint32_dec_eq(x_2, x_38);
if (x_39 == 0)
{
uint32_t x_40; uint8_t x_41; 
x_40 = 32;
x_41 = lean_uint32_dec_le(x_40, x_2);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_box(0);
x_3 = x_42;
goto block_31;
}
else
{
uint32_t x_43; uint8_t x_44; 
x_43 = 1114111;
x_44 = lean_uint32_dec_le(x_2, x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_box(0);
x_3 = x_45;
goto block_31;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__2;
x_47 = lean_string_push(x_46, x_2);
x_48 = lean_string_append(x_1, x_47);
lean_dec(x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__3;
x_50 = lean_string_append(x_1, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__4;
x_52 = lean_string_append(x_1, x_51);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__5;
x_54 = lean_string_append(x_1, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__6;
x_56 = lean_string_append(x_1, x_55);
return x_56;
}
block_31:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint32_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint32_t x_17; lean_object* x_18; uint32_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_3);
x_4 = lean_uint32_to_nat(x_2);
x_5 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__1;
x_6 = lean_string_append(x_1, x_5);
x_7 = lean_unsigned_to_nat(4096u);
x_8 = lean_nat_div(x_4, x_7);
x_9 = l_Nat_digitChar(x_8);
lean_dec(x_8);
x_10 = lean_nat_mod(x_4, x_7);
x_11 = lean_unsigned_to_nat(256u);
x_12 = lean_nat_div(x_10, x_11);
lean_dec(x_10);
x_13 = l_Nat_digitChar(x_12);
lean_dec(x_12);
x_14 = lean_nat_mod(x_4, x_11);
x_15 = lean_unsigned_to_nat(16u);
x_16 = lean_nat_div(x_14, x_15);
lean_dec(x_14);
x_17 = l_Nat_digitChar(x_16);
lean_dec(x_16);
x_18 = lean_nat_mod(x_4, x_15);
lean_dec(x_4);
x_19 = l_Nat_digitChar(x_18);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_box_uint32(x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_box_uint32(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_box_uint32(x_13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_box_uint32(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_string_mk(x_28);
x_30 = lean_string_append(x_6, x_29);
lean_dec(x_29);
return x_30;
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
LEAN_EXPORT lean_object* l_Lean_Json_escape(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__2;
x_5 = l_String_foldlAux___at_Lean_Json_escape___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Json_escape___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_escape(x_1);
lean_dec(x_1);
return x_2;
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
LEAN_EXPORT lean_object* l_Lean_Json_renderString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Json_escape(x_1);
x_3 = l_Lean_Json_renderString___closed__1;
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
x_5 = lean_string_append(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_renderString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_renderString(x_1);
lean_dec(x_1);
return x_2;
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
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
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
x_8 = l_Lean_Json_renderString(x_4);
lean_dec(x_4);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2;
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Json_render(x_5);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = 0;
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
x_1 = x_18;
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
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = l_Lean_Json_renderString(x_13);
lean_dec(x_13);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_Json_renderString(x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
case 4:
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_array_get_size(x_18);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = 0;
x_22 = l_Array_mapMUnsafe_map___at_Lean_Json_render___spec__1(x_20, x_21, x_18);
x_23 = lean_array_to_list(lean_box(0), x_22);
x_24 = l_Lean_Json_render___closed__9;
x_25 = l_Std_Format_joinSep___at_Prod_repr___spec__1(x_23, x_24);
x_26 = l_Lean_Json_render___closed__13;
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_Json_render___closed__15;
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Json_render___closed__12;
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = 0;
x_33 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
return x_33;
}
default: 
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_box(0);
x_36 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2(x_35, x_34);
x_37 = l_Lean_Json_render___closed__9;
x_38 = l_Std_Format_joinSep___at_Prod_repr___spec__1(x_36, x_37);
x_39 = l_Lean_Json_render___closed__19;
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lean_Json_render___closed__21;
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Json_render___closed__18;
x_44 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = 0;
x_46 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_45);
return x_46;
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
LEAN_EXPORT lean_object* l_List_map___at_Lean_Json_compress_go___spec__1(lean_object* x_1) {
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
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = l_List_map___at_Lean_Json_compress_go___spec__1(x_5);
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
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_List_map___at_Lean_Json_compress_go___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Json_compress_go___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_RBNode_fold___at_Lean_Json_compress_go___spec__2(x_1, x_3);
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
x_2 = lean_box(2);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Json_compress_go___closed__2() {
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
lean_dec(x_4);
x_25 = l_Lean_Json_renderString(x_24);
lean_dec(x_24);
x_26 = lean_string_append(x_1, x_25);
lean_dec(x_25);
x_1 = x_26;
x_2 = x_23;
goto _start;
}
case 4:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
lean_dec(x_2);
x_29 = lean_ctor_get(x_4, 0);
lean_inc(x_29);
lean_dec(x_4);
x_30 = l_Lean_Json_render___closed__10;
x_31 = lean_string_append(x_1, x_30);
x_32 = lean_array_to_list(lean_box(0), x_29);
x_33 = l_List_map___at_Lean_Json_compress_go___spec__1(x_32);
x_34 = l_Lean_Json_compress_go___closed__1;
x_35 = l_List_appendTR___rarg(x_33, x_34);
x_36 = l_List_appendTR___rarg(x_35, x_28);
x_1 = x_31;
x_2 = x_36;
goto _start;
}
default: 
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
lean_dec(x_2);
x_39 = lean_ctor_get(x_4, 0);
lean_inc(x_39);
lean_dec(x_4);
x_40 = l_Lean_Json_render___closed__16;
x_41 = lean_string_append(x_1, x_40);
x_42 = lean_box(0);
x_43 = l_Lean_RBNode_fold___at_Lean_Json_compress_go___spec__2(x_42, x_39);
lean_dec(x_39);
x_44 = l_Lean_Json_compress_go___closed__2;
x_45 = l_List_appendTR___rarg(x_43, x_44);
x_46 = l_List_appendTR___rarg(x_45, x_38);
x_1 = x_41;
x_2 = x_46;
goto _start;
}
}
}
case 1:
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_2);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_2, 1);
x_50 = lean_ctor_get(x_2, 0);
lean_dec(x_50);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_3);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_ctor_set_tag(x_3, 0);
x_52 = lean_box(5);
lean_ctor_set(x_2, 0, x_52);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_3);
lean_ctor_set(x_53, 1, x_2);
x_2 = x_53;
goto _start;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_3, 0);
lean_inc(x_55);
lean_dec(x_3);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_box(5);
lean_ctor_set(x_2, 0, x_57);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_2);
x_2 = x_58;
goto _start;
}
}
else
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_49, 0);
lean_inc(x_60);
switch (lean_obj_tag(x_60)) {
case 0:
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
x_63 = lean_ctor_get(x_3, 0);
lean_inc(x_63);
lean_dec(x_3);
lean_ctor_set(x_60, 0, x_63);
x_64 = lean_box(5);
lean_ctor_set(x_2, 0, x_64);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_2);
x_2 = x_65;
goto _start;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_60);
x_67 = lean_ctor_get(x_3, 0);
lean_inc(x_67);
lean_dec(x_3);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_box(5);
lean_ctor_set(x_2, 0, x_69);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_2);
x_2 = x_70;
goto _start;
}
}
case 1:
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_60);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_60, 0);
lean_dec(x_73);
x_74 = lean_ctor_get(x_3, 0);
lean_inc(x_74);
lean_dec(x_3);
lean_ctor_set_tag(x_60, 0);
lean_ctor_set(x_60, 0, x_74);
x_75 = lean_box(5);
lean_ctor_set(x_2, 0, x_75);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_60);
lean_ctor_set(x_76, 1, x_2);
x_2 = x_76;
goto _start;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_60);
x_78 = lean_ctor_get(x_3, 0);
lean_inc(x_78);
lean_dec(x_3);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_box(5);
lean_ctor_set(x_2, 0, x_80);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_2);
x_2 = x_81;
goto _start;
}
}
case 2:
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_3);
if (x_83 == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_49);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_49, 0);
lean_dec(x_85);
lean_ctor_set_tag(x_3, 0);
x_86 = lean_box(2);
lean_ctor_set(x_49, 0, x_86);
goto _start;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_49, 1);
lean_inc(x_88);
lean_dec(x_49);
lean_ctor_set_tag(x_3, 0);
x_89 = lean_box(2);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
lean_ctor_set(x_2, 1, x_90);
goto _start;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_ctor_get(x_3, 0);
lean_inc(x_92);
lean_dec(x_3);
x_93 = lean_ctor_get(x_49, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_94 = x_49;
} else {
 lean_dec_ref(x_49);
 x_94 = lean_box(0);
}
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_92);
x_96 = lean_box(2);
if (lean_is_scalar(x_94)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_94;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_93);
lean_ctor_set(x_2, 1, x_97);
lean_ctor_set(x_2, 0, x_95);
goto _start;
}
}
default: 
{
uint8_t x_99; 
lean_dec(x_60);
x_99 = !lean_is_exclusive(x_3);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
lean_ctor_set_tag(x_3, 0);
x_100 = lean_box(5);
lean_ctor_set(x_2, 0, x_100);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_3);
lean_ctor_set(x_101, 1, x_2);
x_2 = x_101;
goto _start;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_3, 0);
lean_inc(x_103);
lean_dec(x_3);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = lean_box(5);
lean_ctor_set(x_2, 0, x_105);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_2);
x_2 = x_106;
goto _start;
}
}
}
}
}
else
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_2, 1);
lean_inc(x_108);
lean_dec(x_2);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_3, 0);
lean_inc(x_109);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_110 = x_3;
} else {
 lean_dec_ref(x_3);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 1, 0);
} else {
 x_111 = x_110;
 lean_ctor_set_tag(x_111, 0);
}
lean_ctor_set(x_111, 0, x_109);
x_112 = lean_box(5);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_108);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_113);
x_2 = x_114;
goto _start;
}
else
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_108, 0);
lean_inc(x_116);
switch (lean_obj_tag(x_116)) {
case 0:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_117 = x_116;
} else {
 lean_dec_ref(x_116);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get(x_3, 0);
lean_inc(x_118);
lean_dec(x_3);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 1, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_118);
x_120 = lean_box(5);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_108);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_121);
x_2 = x_122;
goto _start;
}
case 1:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_124 = x_116;
} else {
 lean_dec_ref(x_116);
 x_124 = lean_box(0);
}
x_125 = lean_ctor_get(x_3, 0);
lean_inc(x_125);
lean_dec(x_3);
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(0, 1, 0);
} else {
 x_126 = x_124;
 lean_ctor_set_tag(x_126, 0);
}
lean_ctor_set(x_126, 0, x_125);
x_127 = lean_box(5);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_108);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_128);
x_2 = x_129;
goto _start;
}
case 2:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_131 = lean_ctor_get(x_3, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_132 = x_3;
} else {
 lean_dec_ref(x_3);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_108, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_134 = x_108;
} else {
 lean_dec_ref(x_108);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_135 = lean_alloc_ctor(0, 1, 0);
} else {
 x_135 = x_132;
 lean_ctor_set_tag(x_135, 0);
}
lean_ctor_set(x_135, 0, x_131);
x_136 = lean_box(2);
if (lean_is_scalar(x_134)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_134;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_133);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_137);
x_2 = x_138;
goto _start;
}
default: 
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_116);
x_140 = lean_ctor_get(x_3, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_141 = x_3;
} else {
 lean_dec_ref(x_3);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(0, 1, 0);
} else {
 x_142 = x_141;
 lean_ctor_set_tag(x_142, 0);
}
lean_ctor_set(x_142, 0, x_140);
x_143 = lean_box(5);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_108);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_144);
x_2 = x_145;
goto _start;
}
}
}
}
}
case 2:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_2, 1);
lean_inc(x_147);
lean_dec(x_2);
x_148 = l_Lean_Json_render___closed__14;
x_149 = lean_string_append(x_1, x_148);
x_1 = x_149;
x_2 = x_147;
goto _start;
}
case 3:
{
uint8_t x_151; 
x_151 = !lean_is_exclusive(x_2);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_2, 1);
x_153 = lean_ctor_get(x_2, 0);
lean_dec(x_153);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_154 = lean_ctor_get(x_3, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_3, 1);
lean_inc(x_155);
lean_dec(x_3);
x_156 = l_Lean_Json_renderString(x_154);
lean_dec(x_154);
x_157 = lean_string_append(x_1, x_156);
lean_dec(x_156);
x_158 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_159 = lean_string_append(x_157, x_158);
x_160 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_160, 0, x_155);
x_161 = lean_box(5);
lean_ctor_set(x_2, 0, x_161);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_2);
x_1 = x_159;
x_2 = x_162;
goto _start;
}
else
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_152, 0);
lean_inc(x_164);
switch (lean_obj_tag(x_164)) {
case 0:
{
uint8_t x_165; 
x_165 = !lean_is_exclusive(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_166 = lean_ctor_get(x_164, 0);
lean_dec(x_166);
x_167 = lean_ctor_get(x_3, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_3, 1);
lean_inc(x_168);
lean_dec(x_3);
x_169 = l_Lean_Json_renderString(x_167);
lean_dec(x_167);
x_170 = lean_string_append(x_1, x_169);
lean_dec(x_169);
x_171 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_172 = lean_string_append(x_170, x_171);
lean_ctor_set(x_164, 0, x_168);
x_173 = lean_box(5);
lean_ctor_set(x_2, 0, x_173);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_164);
lean_ctor_set(x_174, 1, x_2);
x_1 = x_172;
x_2 = x_174;
goto _start;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_164);
x_176 = lean_ctor_get(x_3, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_3, 1);
lean_inc(x_177);
lean_dec(x_3);
x_178 = l_Lean_Json_renderString(x_176);
lean_dec(x_176);
x_179 = lean_string_append(x_1, x_178);
lean_dec(x_178);
x_180 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_181 = lean_string_append(x_179, x_180);
x_182 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_182, 0, x_177);
x_183 = lean_box(5);
lean_ctor_set(x_2, 0, x_183);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_2);
x_1 = x_181;
x_2 = x_184;
goto _start;
}
}
case 1:
{
uint8_t x_186; 
x_186 = !lean_is_exclusive(x_164);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_187 = lean_ctor_get(x_164, 0);
lean_dec(x_187);
x_188 = lean_ctor_get(x_3, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_3, 1);
lean_inc(x_189);
lean_dec(x_3);
x_190 = l_Lean_Json_renderString(x_188);
lean_dec(x_188);
x_191 = lean_string_append(x_1, x_190);
lean_dec(x_190);
x_192 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_193 = lean_string_append(x_191, x_192);
lean_ctor_set_tag(x_164, 0);
lean_ctor_set(x_164, 0, x_189);
x_194 = lean_box(5);
lean_ctor_set(x_2, 0, x_194);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_164);
lean_ctor_set(x_195, 1, x_2);
x_1 = x_193;
x_2 = x_195;
goto _start;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_164);
x_197 = lean_ctor_get(x_3, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_3, 1);
lean_inc(x_198);
lean_dec(x_3);
x_199 = l_Lean_Json_renderString(x_197);
lean_dec(x_197);
x_200 = lean_string_append(x_1, x_199);
lean_dec(x_199);
x_201 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_202 = lean_string_append(x_200, x_201);
x_203 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_203, 0, x_198);
x_204 = lean_box(5);
lean_ctor_set(x_2, 0, x_204);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_2);
x_1 = x_202;
x_2 = x_205;
goto _start;
}
}
case 4:
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_207 = lean_ctor_get(x_3, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_3, 1);
lean_inc(x_208);
lean_dec(x_3);
x_209 = !lean_is_exclusive(x_152);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_210 = lean_ctor_get(x_152, 0);
lean_dec(x_210);
x_211 = l_Lean_Json_renderString(x_207);
lean_dec(x_207);
x_212 = lean_string_append(x_1, x_211);
lean_dec(x_211);
x_213 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_214 = lean_string_append(x_212, x_213);
x_215 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_215, 0, x_208);
x_216 = lean_box(4);
lean_ctor_set(x_152, 0, x_216);
lean_ctor_set(x_2, 0, x_215);
x_1 = x_214;
goto _start;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_218 = lean_ctor_get(x_152, 1);
lean_inc(x_218);
lean_dec(x_152);
x_219 = l_Lean_Json_renderString(x_207);
lean_dec(x_207);
x_220 = lean_string_append(x_1, x_219);
lean_dec(x_219);
x_221 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_222 = lean_string_append(x_220, x_221);
x_223 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_223, 0, x_208);
x_224 = lean_box(4);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_218);
lean_ctor_set(x_2, 1, x_225);
lean_ctor_set(x_2, 0, x_223);
x_1 = x_222;
goto _start;
}
}
default: 
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_164);
x_227 = lean_ctor_get(x_3, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_3, 1);
lean_inc(x_228);
lean_dec(x_3);
x_229 = l_Lean_Json_renderString(x_227);
lean_dec(x_227);
x_230 = lean_string_append(x_1, x_229);
lean_dec(x_229);
x_231 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_232 = lean_string_append(x_230, x_231);
x_233 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_233, 0, x_228);
x_234 = lean_box(5);
lean_ctor_set(x_2, 0, x_234);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_2);
x_1 = x_232;
x_2 = x_235;
goto _start;
}
}
}
}
else
{
lean_object* x_237; 
x_237 = lean_ctor_get(x_2, 1);
lean_inc(x_237);
lean_dec(x_2);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_238 = lean_ctor_get(x_3, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_3, 1);
lean_inc(x_239);
lean_dec(x_3);
x_240 = l_Lean_Json_renderString(x_238);
lean_dec(x_238);
x_241 = lean_string_append(x_1, x_240);
lean_dec(x_240);
x_242 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_243 = lean_string_append(x_241, x_242);
x_244 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_244, 0, x_239);
x_245 = lean_box(5);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_237);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_246);
x_1 = x_243;
x_2 = x_247;
goto _start;
}
else
{
lean_object* x_249; 
x_249 = lean_ctor_get(x_237, 0);
lean_inc(x_249);
switch (lean_obj_tag(x_249)) {
case 0:
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 x_250 = x_249;
} else {
 lean_dec_ref(x_249);
 x_250 = lean_box(0);
}
x_251 = lean_ctor_get(x_3, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_3, 1);
lean_inc(x_252);
lean_dec(x_3);
x_253 = l_Lean_Json_renderString(x_251);
lean_dec(x_251);
x_254 = lean_string_append(x_1, x_253);
lean_dec(x_253);
x_255 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_256 = lean_string_append(x_254, x_255);
if (lean_is_scalar(x_250)) {
 x_257 = lean_alloc_ctor(0, 1, 0);
} else {
 x_257 = x_250;
}
lean_ctor_set(x_257, 0, x_252);
x_258 = lean_box(5);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_237);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_259);
x_1 = x_256;
x_2 = x_260;
goto _start;
}
case 1:
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 x_262 = x_249;
} else {
 lean_dec_ref(x_249);
 x_262 = lean_box(0);
}
x_263 = lean_ctor_get(x_3, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_3, 1);
lean_inc(x_264);
lean_dec(x_3);
x_265 = l_Lean_Json_renderString(x_263);
lean_dec(x_263);
x_266 = lean_string_append(x_1, x_265);
lean_dec(x_265);
x_267 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_268 = lean_string_append(x_266, x_267);
if (lean_is_scalar(x_262)) {
 x_269 = lean_alloc_ctor(0, 1, 0);
} else {
 x_269 = x_262;
 lean_ctor_set_tag(x_269, 0);
}
lean_ctor_set(x_269, 0, x_264);
x_270 = lean_box(5);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_237);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_269);
lean_ctor_set(x_272, 1, x_271);
x_1 = x_268;
x_2 = x_272;
goto _start;
}
case 4:
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_274 = lean_ctor_get(x_3, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_3, 1);
lean_inc(x_275);
lean_dec(x_3);
x_276 = lean_ctor_get(x_237, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_277 = x_237;
} else {
 lean_dec_ref(x_237);
 x_277 = lean_box(0);
}
x_278 = l_Lean_Json_renderString(x_274);
lean_dec(x_274);
x_279 = lean_string_append(x_1, x_278);
lean_dec(x_278);
x_280 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_281 = lean_string_append(x_279, x_280);
x_282 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_282, 0, x_275);
x_283 = lean_box(4);
if (lean_is_scalar(x_277)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_277;
}
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_276);
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_282);
lean_ctor_set(x_285, 1, x_284);
x_1 = x_281;
x_2 = x_285;
goto _start;
}
default: 
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_249);
x_287 = lean_ctor_get(x_3, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_3, 1);
lean_inc(x_288);
lean_dec(x_3);
x_289 = l_Lean_Json_renderString(x_287);
lean_dec(x_287);
x_290 = lean_string_append(x_1, x_289);
lean_dec(x_289);
x_291 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_292 = lean_string_append(x_290, x_291);
x_293 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_293, 0, x_288);
x_294 = lean_box(5);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_237);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_293);
lean_ctor_set(x_296, 1, x_295);
x_1 = x_292;
x_2 = x_296;
goto _start;
}
}
}
}
}
case 4:
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_2, 1);
lean_inc(x_298);
lean_dec(x_2);
x_299 = l_Lean_Json_render___closed__20;
x_300 = lean_string_append(x_1, x_299);
x_1 = x_300;
x_2 = x_298;
goto _start;
}
default: 
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_2, 1);
lean_inc(x_302);
lean_dec(x_2);
x_303 = l_Lean_Json_render___closed__7;
x_304 = lean_string_append(x_1, x_303);
x_1 = x_304;
x_2 = x_302;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Json_compress_go___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_fold___at_Lean_Json_compress_go___spec__2(x_1, x_2);
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
x_5 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__2;
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
l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__6 = _init_l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__6();
lean_mark_persistent(l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__6);
l_Lean_Json_renderString___closed__1 = _init_l_Lean_Json_renderString___closed__1();
lean_mark_persistent(l_Lean_Json_renderString___closed__1);
l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1 = _init_l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1();
lean_mark_persistent(l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1);
l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2 = _init_l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2();
lean_mark_persistent(l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2);
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
l_Lean_Json_compress_go___closed__2 = _init_l_Lean_Json_compress_go___closed__2();
lean_mark_persistent(l_Lean_Json_compress_go___closed__2);
l_Lean_Json_instToFormat___closed__1 = _init_l_Lean_Json_instToFormat___closed__1();
lean_mark_persistent(l_Lean_Json_instToFormat___closed__1);
l_Lean_Json_instToFormat = _init_l_Lean_Json_instToFormat();
lean_mark_persistent(l_Lean_Json_instToFormat);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
