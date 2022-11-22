// Lean compiler output
// Module: Lean.Data.Json.Printer
// Imports: Init Lean.Data.Format Lean.Data.Json.Basic
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
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__1;
lean_object* lean_string_push(lean_object*, uint32_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_escape(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Json_compress_go___spec__2(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__2;
static lean_object* l_Lean_Json_render___closed__14;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_JsonNumber_toString(lean_object*);
lean_object* l_Std_Format_joinSep___at_Prod_repr___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Json_compress_go___closed__1;
static lean_object* l_Lean_Json_render___closed__13;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Json_render___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_Json_instToFormatJson___closed__1;
static lean_object* l_Lean_Json_compress_go___closed__2;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Json_render___closed__6;
static lean_object* l_Lean_Json_escape___closed__1;
LEAN_EXPORT lean_object* l_Lean_Json_escape___boxed(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Json_render___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Json_render___closed__17;
static lean_object* l_Lean_Json_render___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(lean_object*, uint32_t);
static lean_object* l_Lean_Json_render___closed__1;
static lean_object* l_Lean_Json_render___closed__2;
LEAN_EXPORT lean_object* l_Lean_Json_compress(lean_object*);
static lean_object* l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2;
static lean_object* l_Lean_Json_render___closed__19;
static lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__4;
lean_object* lean_format_pretty(lean_object*, lean_object*);
static lean_object* l_Lean_Json_render___closed__9;
LEAN_EXPORT lean_object* l_Lean_Json_renderString(lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Lean_Json_renderString___closed__1;
LEAN_EXPORT lean_object* l_Lean_Json_renderString___boxed(lean_object*);
uint32_t l_Nat_digitChar(lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Json_render___closed__11;
LEAN_EXPORT lean_object* l_Lean_Json_compress_go(lean_object*, lean_object*);
static lean_object* l_Lean_Json_render___closed__18;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Json_compress_go___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Json_render___closed__5;
static lean_object* l_Lean_Json_render___closed__3;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
lean_object* l_String_foldlAux_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_instToFormatJson;
static lean_object* l_Lean_Json_render___closed__4;
static lean_object* l_Lean_Json_render___closed__12;
LEAN_EXPORT lean_object* l_Lean_Json_instToStringJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_render(lean_object*);
static lean_object* l_Lean_Json_render___closed__10;
static lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__6;
static lean_object* l_Lean_Json_render___closed__15;
static lean_object* l_Lean_Json_render___closed__20;
lean_object* lean_string_length(lean_object*);
static lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__5;
static lean_object* l_Lean_Json_render___closed__21;
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
static lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__3;
lean_object* lean_uint32_to_nat(uint32_t);
static lean_object* l_Lean_Json_render___closed__7;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Json_render___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
static lean_object* l_Lean_Json_render___closed__16;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Json_compress_go___spec__1(lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\\u", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\\r", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\\n", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\\\\", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\\\"", 2);
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
static lean_object* _init_l_Lean_Json_escape___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_escape(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = l_Lean_Json_escape___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__2;
x_6 = l_String_foldlAux_loop___rarg(x_3, x_1, x_2, x_4, x_5);
lean_dec(x_2);
return x_6;
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
x_1 = lean_mk_string_from_bytes("\"", 1);
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
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
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
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__2;
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Json_render(x_5);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = 0;
x_17 = lean_alloc_ctor(5, 1, 1);
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
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_render___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_render___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_render___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("false", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_render___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_render___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_render___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("true", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_render___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_render___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_render___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(",", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_render___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_render___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
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
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Json_render___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[", 1);
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
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_render___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("]", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_render___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_render___closed__14;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_render___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("{", 1);
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
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_render___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("}", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_render___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_render___closed__20;
x_2 = lean_alloc_ctor(2, 1, 0);
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_JsonNumber_toString(x_6);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
case 3:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Json_renderString(x_9);
lean_dec(x_9);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
case 4:
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_array_get_size(x_12);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = 0;
x_16 = l_Array_mapMUnsafe_map___at_Lean_Json_render___spec__1(x_14, x_15, x_12);
x_17 = lean_array_to_list(lean_box(0), x_16);
x_18 = l_Lean_Json_render___closed__9;
x_19 = l_Std_Format_joinSep___at_Prod_repr___spec__1(x_17, x_18);
lean_dec(x_17);
x_20 = l_Lean_Json_render___closed__13;
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Json_render___closed__15;
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Json_render___closed__12;
x_25 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = 0;
x_27 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
return x_27;
}
default: 
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_box(0);
x_30 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2(x_29, x_28);
x_31 = l_Lean_Json_render___closed__9;
x_32 = l_Std_Format_joinSep___at_Prod_repr___spec__1(x_30, x_31);
lean_dec(x_30);
x_33 = l_Lean_Json_render___closed__19;
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_Json_render___closed__21;
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Json_render___closed__18;
x_38 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = 0;
x_40 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
return x_40;
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
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_render(x_1);
x_4 = lean_format_pretty(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Json_compress_go___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
lean_dec(x_2);
x_29 = lean_ctor_get(x_4, 0);
lean_inc(x_29);
lean_dec(x_4);
x_30 = l_Lean_Json_render___closed__10;
x_31 = lean_string_append(x_1, x_30);
x_32 = lean_array_to_list(lean_box(0), x_29);
x_33 = lean_box(0);
x_34 = l_List_mapTR_loop___at_Lean_Json_compress_go___spec__1(x_32, x_33);
x_35 = l_Lean_Json_compress_go___closed__1;
x_36 = l_List_appendTR___rarg(x_34, x_35);
x_37 = l_List_appendTR___rarg(x_36, x_28);
x_1 = x_31;
x_2 = x_37;
goto _start;
}
default: 
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
lean_dec(x_2);
x_40 = lean_ctor_get(x_4, 0);
lean_inc(x_40);
lean_dec(x_4);
x_41 = l_Lean_Json_render___closed__16;
x_42 = lean_string_append(x_1, x_41);
x_43 = lean_box(0);
x_44 = l_Lean_RBNode_fold___at_Lean_Json_compress_go___spec__2(x_43, x_40);
lean_dec(x_40);
x_45 = l_Lean_Json_compress_go___closed__2;
x_46 = l_List_appendTR___rarg(x_44, x_45);
x_47 = l_List_appendTR___rarg(x_46, x_39);
x_1 = x_42;
x_2 = x_47;
goto _start;
}
}
}
case 1:
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_2);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_2, 1);
x_51 = lean_ctor_get(x_2, 0);
lean_dec(x_51);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_3);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_ctor_set_tag(x_3, 0);
x_53 = lean_box(5);
lean_ctor_set(x_2, 0, x_53);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_3);
lean_ctor_set(x_54, 1, x_2);
x_2 = x_54;
goto _start;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_3, 0);
lean_inc(x_56);
lean_dec(x_3);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_box(5);
lean_ctor_set(x_2, 0, x_58);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_2);
x_2 = x_59;
goto _start;
}
}
else
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_50, 0);
lean_inc(x_61);
switch (lean_obj_tag(x_61)) {
case 0:
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
x_64 = lean_ctor_get(x_3, 0);
lean_inc(x_64);
lean_dec(x_3);
lean_ctor_set(x_61, 0, x_64);
x_65 = lean_box(5);
lean_ctor_set(x_2, 0, x_65);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_61);
lean_ctor_set(x_66, 1, x_2);
x_2 = x_66;
goto _start;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_61);
x_68 = lean_ctor_get(x_3, 0);
lean_inc(x_68);
lean_dec(x_3);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_box(5);
lean_ctor_set(x_2, 0, x_70);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_2);
x_2 = x_71;
goto _start;
}
}
case 1:
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_61);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_61, 0);
lean_dec(x_74);
x_75 = lean_ctor_get(x_3, 0);
lean_inc(x_75);
lean_dec(x_3);
lean_ctor_set_tag(x_61, 0);
lean_ctor_set(x_61, 0, x_75);
x_76 = lean_box(5);
lean_ctor_set(x_2, 0, x_76);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_61);
lean_ctor_set(x_77, 1, x_2);
x_2 = x_77;
goto _start;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_61);
x_79 = lean_ctor_get(x_3, 0);
lean_inc(x_79);
lean_dec(x_3);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_box(5);
lean_ctor_set(x_2, 0, x_81);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_2);
x_2 = x_82;
goto _start;
}
}
case 2:
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_3);
if (x_84 == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_50);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_50, 0);
lean_dec(x_86);
lean_ctor_set_tag(x_3, 0);
x_87 = lean_box(2);
lean_ctor_set(x_50, 0, x_87);
goto _start;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_50, 1);
lean_inc(x_89);
lean_dec(x_50);
lean_ctor_set_tag(x_3, 0);
x_90 = lean_box(2);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
lean_ctor_set(x_2, 1, x_91);
goto _start;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_3, 0);
lean_inc(x_93);
lean_dec(x_3);
x_94 = lean_ctor_get(x_50, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_95 = x_50;
} else {
 lean_dec_ref(x_50);
 x_95 = lean_box(0);
}
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_93);
x_97 = lean_box(2);
if (lean_is_scalar(x_95)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_95;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_94);
lean_ctor_set(x_2, 1, x_98);
lean_ctor_set(x_2, 0, x_96);
goto _start;
}
}
default: 
{
uint8_t x_100; 
lean_dec(x_61);
x_100 = !lean_is_exclusive(x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_ctor_set_tag(x_3, 0);
x_101 = lean_box(5);
lean_ctor_set(x_2, 0, x_101);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_3);
lean_ctor_set(x_102, 1, x_2);
x_2 = x_102;
goto _start;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_3, 0);
lean_inc(x_104);
lean_dec(x_3);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = lean_box(5);
lean_ctor_set(x_2, 0, x_106);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_2);
x_2 = x_107;
goto _start;
}
}
}
}
}
else
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_2, 1);
lean_inc(x_109);
lean_dec(x_2);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_110 = lean_ctor_get(x_3, 0);
lean_inc(x_110);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_111 = x_3;
} else {
 lean_dec_ref(x_3);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 1, 0);
} else {
 x_112 = x_111;
 lean_ctor_set_tag(x_112, 0);
}
lean_ctor_set(x_112, 0, x_110);
x_113 = lean_box(5);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_109);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
x_2 = x_115;
goto _start;
}
else
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_109, 0);
lean_inc(x_117);
switch (lean_obj_tag(x_117)) {
case 0:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_118 = x_117;
} else {
 lean_dec_ref(x_117);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_3, 0);
lean_inc(x_119);
lean_dec(x_3);
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(0, 1, 0);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_119);
x_121 = lean_box(5);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_109);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_122);
x_2 = x_123;
goto _start;
}
case 1:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_125 = x_117;
} else {
 lean_dec_ref(x_117);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_3, 0);
lean_inc(x_126);
lean_dec(x_3);
if (lean_is_scalar(x_125)) {
 x_127 = lean_alloc_ctor(0, 1, 0);
} else {
 x_127 = x_125;
 lean_ctor_set_tag(x_127, 0);
}
lean_ctor_set(x_127, 0, x_126);
x_128 = lean_box(5);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_109);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_129);
x_2 = x_130;
goto _start;
}
case 2:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_132 = lean_ctor_get(x_3, 0);
lean_inc(x_132);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_133 = x_3;
} else {
 lean_dec_ref(x_3);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_109, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_135 = x_109;
} else {
 lean_dec_ref(x_109);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_136 = lean_alloc_ctor(0, 1, 0);
} else {
 x_136 = x_133;
 lean_ctor_set_tag(x_136, 0);
}
lean_ctor_set(x_136, 0, x_132);
x_137 = lean_box(2);
if (lean_is_scalar(x_135)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_135;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_134);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_138);
x_2 = x_139;
goto _start;
}
default: 
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_117);
x_141 = lean_ctor_get(x_3, 0);
lean_inc(x_141);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_142 = x_3;
} else {
 lean_dec_ref(x_3);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(0, 1, 0);
} else {
 x_143 = x_142;
 lean_ctor_set_tag(x_143, 0);
}
lean_ctor_set(x_143, 0, x_141);
x_144 = lean_box(5);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_109);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_145);
x_2 = x_146;
goto _start;
}
}
}
}
}
case 2:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_2, 1);
lean_inc(x_148);
lean_dec(x_2);
x_149 = l_Lean_Json_render___closed__14;
x_150 = lean_string_append(x_1, x_149);
x_1 = x_150;
x_2 = x_148;
goto _start;
}
case 3:
{
uint8_t x_152; 
x_152 = !lean_is_exclusive(x_2);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_2, 1);
x_154 = lean_ctor_get(x_2, 0);
lean_dec(x_154);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_155 = lean_ctor_get(x_3, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_3, 1);
lean_inc(x_156);
lean_dec(x_3);
x_157 = l_Lean_Json_renderString(x_155);
lean_dec(x_155);
x_158 = lean_string_append(x_1, x_157);
lean_dec(x_157);
x_159 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_160 = lean_string_append(x_158, x_159);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_156);
x_162 = lean_box(5);
lean_ctor_set(x_2, 0, x_162);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_2);
x_1 = x_160;
x_2 = x_163;
goto _start;
}
else
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_153, 0);
lean_inc(x_165);
switch (lean_obj_tag(x_165)) {
case 0:
{
uint8_t x_166; 
x_166 = !lean_is_exclusive(x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_167 = lean_ctor_get(x_165, 0);
lean_dec(x_167);
x_168 = lean_ctor_get(x_3, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_3, 1);
lean_inc(x_169);
lean_dec(x_3);
x_170 = l_Lean_Json_renderString(x_168);
lean_dec(x_168);
x_171 = lean_string_append(x_1, x_170);
lean_dec(x_170);
x_172 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_173 = lean_string_append(x_171, x_172);
lean_ctor_set(x_165, 0, x_169);
x_174 = lean_box(5);
lean_ctor_set(x_2, 0, x_174);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_165);
lean_ctor_set(x_175, 1, x_2);
x_1 = x_173;
x_2 = x_175;
goto _start;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_165);
x_177 = lean_ctor_get(x_3, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_3, 1);
lean_inc(x_178);
lean_dec(x_3);
x_179 = l_Lean_Json_renderString(x_177);
lean_dec(x_177);
x_180 = lean_string_append(x_1, x_179);
lean_dec(x_179);
x_181 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_182 = lean_string_append(x_180, x_181);
x_183 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_183, 0, x_178);
x_184 = lean_box(5);
lean_ctor_set(x_2, 0, x_184);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_2);
x_1 = x_182;
x_2 = x_185;
goto _start;
}
}
case 1:
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_165);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_188 = lean_ctor_get(x_165, 0);
lean_dec(x_188);
x_189 = lean_ctor_get(x_3, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_3, 1);
lean_inc(x_190);
lean_dec(x_3);
x_191 = l_Lean_Json_renderString(x_189);
lean_dec(x_189);
x_192 = lean_string_append(x_1, x_191);
lean_dec(x_191);
x_193 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_194 = lean_string_append(x_192, x_193);
lean_ctor_set_tag(x_165, 0);
lean_ctor_set(x_165, 0, x_190);
x_195 = lean_box(5);
lean_ctor_set(x_2, 0, x_195);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_165);
lean_ctor_set(x_196, 1, x_2);
x_1 = x_194;
x_2 = x_196;
goto _start;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_165);
x_198 = lean_ctor_get(x_3, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_3, 1);
lean_inc(x_199);
lean_dec(x_3);
x_200 = l_Lean_Json_renderString(x_198);
lean_dec(x_198);
x_201 = lean_string_append(x_1, x_200);
lean_dec(x_200);
x_202 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_203 = lean_string_append(x_201, x_202);
x_204 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_204, 0, x_199);
x_205 = lean_box(5);
lean_ctor_set(x_2, 0, x_205);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_2);
x_1 = x_203;
x_2 = x_206;
goto _start;
}
}
case 4:
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_208 = lean_ctor_get(x_3, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_3, 1);
lean_inc(x_209);
lean_dec(x_3);
x_210 = !lean_is_exclusive(x_153);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_211 = lean_ctor_get(x_153, 0);
lean_dec(x_211);
x_212 = l_Lean_Json_renderString(x_208);
lean_dec(x_208);
x_213 = lean_string_append(x_1, x_212);
lean_dec(x_212);
x_214 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_215 = lean_string_append(x_213, x_214);
x_216 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_216, 0, x_209);
x_217 = lean_box(4);
lean_ctor_set(x_153, 0, x_217);
lean_ctor_set(x_2, 0, x_216);
x_1 = x_215;
goto _start;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_219 = lean_ctor_get(x_153, 1);
lean_inc(x_219);
lean_dec(x_153);
x_220 = l_Lean_Json_renderString(x_208);
lean_dec(x_208);
x_221 = lean_string_append(x_1, x_220);
lean_dec(x_220);
x_222 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_223 = lean_string_append(x_221, x_222);
x_224 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_224, 0, x_209);
x_225 = lean_box(4);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_219);
lean_ctor_set(x_2, 1, x_226);
lean_ctor_set(x_2, 0, x_224);
x_1 = x_223;
goto _start;
}
}
default: 
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_165);
x_228 = lean_ctor_get(x_3, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_3, 1);
lean_inc(x_229);
lean_dec(x_3);
x_230 = l_Lean_Json_renderString(x_228);
lean_dec(x_228);
x_231 = lean_string_append(x_1, x_230);
lean_dec(x_230);
x_232 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_233 = lean_string_append(x_231, x_232);
x_234 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_234, 0, x_229);
x_235 = lean_box(5);
lean_ctor_set(x_2, 0, x_235);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_2);
x_1 = x_233;
x_2 = x_236;
goto _start;
}
}
}
}
else
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_2, 1);
lean_inc(x_238);
lean_dec(x_2);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_239 = lean_ctor_get(x_3, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_3, 1);
lean_inc(x_240);
lean_dec(x_3);
x_241 = l_Lean_Json_renderString(x_239);
lean_dec(x_239);
x_242 = lean_string_append(x_1, x_241);
lean_dec(x_241);
x_243 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_244 = lean_string_append(x_242, x_243);
x_245 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_245, 0, x_240);
x_246 = lean_box(5);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_238);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_247);
x_1 = x_244;
x_2 = x_248;
goto _start;
}
else
{
lean_object* x_250; 
x_250 = lean_ctor_get(x_238, 0);
lean_inc(x_250);
switch (lean_obj_tag(x_250)) {
case 0:
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 x_251 = x_250;
} else {
 lean_dec_ref(x_250);
 x_251 = lean_box(0);
}
x_252 = lean_ctor_get(x_3, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_3, 1);
lean_inc(x_253);
lean_dec(x_3);
x_254 = l_Lean_Json_renderString(x_252);
lean_dec(x_252);
x_255 = lean_string_append(x_1, x_254);
lean_dec(x_254);
x_256 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_257 = lean_string_append(x_255, x_256);
if (lean_is_scalar(x_251)) {
 x_258 = lean_alloc_ctor(0, 1, 0);
} else {
 x_258 = x_251;
}
lean_ctor_set(x_258, 0, x_253);
x_259 = lean_box(5);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_238);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_260);
x_1 = x_257;
x_2 = x_261;
goto _start;
}
case 1:
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 x_263 = x_250;
} else {
 lean_dec_ref(x_250);
 x_263 = lean_box(0);
}
x_264 = lean_ctor_get(x_3, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_3, 1);
lean_inc(x_265);
lean_dec(x_3);
x_266 = l_Lean_Json_renderString(x_264);
lean_dec(x_264);
x_267 = lean_string_append(x_1, x_266);
lean_dec(x_266);
x_268 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_269 = lean_string_append(x_267, x_268);
if (lean_is_scalar(x_263)) {
 x_270 = lean_alloc_ctor(0, 1, 0);
} else {
 x_270 = x_263;
 lean_ctor_set_tag(x_270, 0);
}
lean_ctor_set(x_270, 0, x_265);
x_271 = lean_box(5);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_238);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_270);
lean_ctor_set(x_273, 1, x_272);
x_1 = x_269;
x_2 = x_273;
goto _start;
}
case 4:
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_275 = lean_ctor_get(x_3, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_3, 1);
lean_inc(x_276);
lean_dec(x_3);
x_277 = lean_ctor_get(x_238, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_278 = x_238;
} else {
 lean_dec_ref(x_238);
 x_278 = lean_box(0);
}
x_279 = l_Lean_Json_renderString(x_275);
lean_dec(x_275);
x_280 = lean_string_append(x_1, x_279);
lean_dec(x_279);
x_281 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_282 = lean_string_append(x_280, x_281);
x_283 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_283, 0, x_276);
x_284 = lean_box(4);
if (lean_is_scalar(x_278)) {
 x_285 = lean_alloc_ctor(1, 2, 0);
} else {
 x_285 = x_278;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_277);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set(x_286, 1, x_285);
x_1 = x_282;
x_2 = x_286;
goto _start;
}
default: 
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_250);
x_288 = lean_ctor_get(x_3, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_3, 1);
lean_inc(x_289);
lean_dec(x_3);
x_290 = l_Lean_Json_renderString(x_288);
lean_dec(x_288);
x_291 = lean_string_append(x_1, x_290);
lean_dec(x_290);
x_292 = l_Lean_RBNode_fold___at_Lean_Json_render___spec__2___closed__1;
x_293 = lean_string_append(x_291, x_292);
x_294 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_294, 0, x_289);
x_295 = lean_box(5);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_238);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_294);
lean_ctor_set(x_297, 1, x_296);
x_1 = x_293;
x_2 = x_297;
goto _start;
}
}
}
}
}
case 4:
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_2, 1);
lean_inc(x_299);
lean_dec(x_2);
x_300 = l_Lean_Json_render___closed__20;
x_301 = lean_string_append(x_1, x_300);
x_1 = x_301;
x_2 = x_299;
goto _start;
}
default: 
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_2, 1);
lean_inc(x_303);
lean_dec(x_2);
x_304 = l_Lean_Json_render___closed__7;
x_305 = lean_string_append(x_1, x_304);
x_1 = x_305;
x_2 = x_303;
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
static lean_object* _init_l_Lean_Json_instToFormatJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_render), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_instToFormatJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Json_instToFormatJson___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instToStringJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(80u);
x_3 = l_Lean_Json_pretty(x_1, x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Format(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Json_Printer(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l_Lean_Json_escape___closed__1 = _init_l_Lean_Json_escape___closed__1();
lean_mark_persistent(l_Lean_Json_escape___closed__1);
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
l_Lean_Json_instToFormatJson___closed__1 = _init_l_Lean_Json_instToFormatJson___closed__1();
lean_mark_persistent(l_Lean_Json_instToFormatJson___closed__1);
l_Lean_Json_instToFormatJson = _init_l_Lean_Json_instToFormatJson();
lean_mark_persistent(l_Lean_Json_instToFormatJson);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
