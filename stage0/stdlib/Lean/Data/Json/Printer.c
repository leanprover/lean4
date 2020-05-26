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
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Json_escape(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Json_jsonHasFormat___closed__1;
lean_object* l_Lean_Json_render___main___closed__4;
lean_object* l_Lean_Json_render___main___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_toString(lean_object*);
lean_object* l_Lean_Json_render___main___closed__6;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Json_render___main(lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
extern lean_object* l_String_quote___closed__1;
extern lean_object* l_Id_monad;
lean_object* l_Lean_Json_escape___boxed(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Json_jsonHasFormat;
extern lean_object* l_Lean_Format_sbracket___closed__2;
lean_object* l_Lean_Json_render___main___lambda__2___closed__1;
lean_object* l_Lean_Json_jsonHasToString(lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
extern lean_object* l_Char_quoteCore___closed__2;
extern lean_object* l_Lean_Format_repr___main___closed__13;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_foldrAux___main___at_Lean_Json_escape___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_render___main___lambda__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_JsonNumber_jsonNumberHasRepr___closed__1;
lean_object* l_Lean_Json_render___main___closed__7;
lean_object* l_Lean_Json_render___main___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Json_renderString(lean_object*);
lean_object* l_Lean_Json_renderString___boxed(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint32_t l_Nat_digitChar(lean_object*);
lean_object* l_Lean_Format_joinSep___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_fold___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_render___main___closed__5;
extern lean_object* l_Lean_nullKind___closed__1;
extern lean_object* l_Lean_Format_sbracket___closed__3;
extern lean_object* l_Char_quoteCore___closed__3;
lean_object* l_Array_umapMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
extern lean_object* l_Lean_formatHasFormat;
lean_object* l_String_foldrAux___main___at_Lean_Json_escape___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_render___main___closed__3;
extern lean_object* l_Lean_Format_sbracket___closed__1;
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* lean_format_group(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Json_render(lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Json_render___main___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
extern lean_object* l_Char_quoteCore___closed__5;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_render___main___closed__1;
lean_object* l_Lean_Json_render___main___closed__2;
uint8_t l_UInt32_decLe(uint32_t, uint32_t);
lean_object* l___private_Lean_Data_Json_Printer_1__escapeAux___closed__2;
extern lean_object* l_Lean_Format_repr___main___closed__16;
lean_object* l_Lean_Json_render___main___closed__9;
lean_object* l___private_Lean_Data_Json_Printer_1__escapeAux___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Json_Printer_1__escapeAux___closed__1;
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_string_mk(lean_object*);
extern lean_object* l_addParenHeuristic___closed__1;
lean_object* l___private_Lean_Data_Json_Printer_1__escapeAux(uint32_t, lean_object*);
lean_object* l_Lean_Json_render___main___closed__8;
lean_object* _init_l___private_Lean_Data_Json_Printer_1__escapeAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\\u");
return x_1;
}
}
lean_object* _init_l___private_Lean_Data_Json_Printer_1__escapeAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\\r");
return x_1;
}
}
lean_object* l___private_Lean_Data_Json_Printer_1__escapeAux(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_32; uint8_t x_33; 
x_32 = 34;
x_33 = x_1 == x_32;
if (x_33 == 0)
{
uint32_t x_34; uint8_t x_35; 
x_34 = 92;
x_35 = x_1 == x_34;
if (x_35 == 0)
{
uint32_t x_36; uint8_t x_37; 
x_36 = 10;
x_37 = x_1 == x_36;
if (x_37 == 0)
{
uint32_t x_38; uint8_t x_39; 
x_38 = 13;
x_39 = x_1 == x_38;
if (x_39 == 0)
{
uint32_t x_40; uint8_t x_41; 
x_40 = 32;
x_41 = x_40 <= x_1;
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
x_44 = x_1 <= x_43;
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
x_46 = l_String_splitAux___main___closed__1;
x_47 = lean_string_push(x_46, x_1);
x_48 = lean_string_append(x_47, x_2);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = l___private_Lean_Data_Json_Printer_1__escapeAux___closed__2;
x_50 = lean_string_append(x_49, x_2);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = l_Char_quoteCore___closed__5;
x_52 = lean_string_append(x_51, x_2);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = l_Char_quoteCore___closed__3;
x_54 = lean_string_append(x_53, x_2);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = l_Char_quoteCore___closed__2;
x_56 = lean_string_append(x_55, x_2);
return x_56;
}
block_31:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; lean_object* x_16; uint32_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_3);
x_4 = lean_uint32_to_nat(x_1);
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
x_18 = lean_box(0);
x_19 = lean_box_uint32(x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_box_uint32(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_box_uint32(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_box_uint32(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_string_mk(x_26);
x_28 = l___private_Lean_Data_Json_Printer_1__escapeAux___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = lean_string_append(x_29, x_2);
return x_30;
}
}
}
lean_object* l___private_Lean_Data_Json_Printer_1__escapeAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Data_Json_Printer_1__escapeAux(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_String_foldrAux___main___at_Lean_Json_escape___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_4, x_3);
if (x_5 == 0)
{
uint32_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_string_utf8_get(x_2, x_4);
x_7 = lean_string_utf8_next(x_2, x_4);
x_8 = l_String_foldrAux___main___at_Lean_Json_escape___spec__1(x_1, x_2, x_3, x_7);
lean_dec(x_7);
x_9 = l___private_Lean_Data_Json_Printer_1__escapeAux(x_6, x_8);
lean_dec(x_8);
return x_9;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
lean_object* l_Lean_Json_escape(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = l_String_splitAux___main___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_String_foldrAux___main___at_Lean_Json_escape___spec__1(x_3, x_1, x_2, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_String_foldrAux___main___at_Lean_Json_escape___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_foldrAux___main___at_Lean_Json_escape___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Json_escape___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_escape(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Json_renderString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Json_escape(x_1);
x_3 = l_String_quote___closed__1;
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
x_5 = lean_string_append(x_4, x_3);
return x_5;
}
}
lean_object* l_Lean_Json_renderString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_renderString(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Json_render___main___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_render___main(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Json_render___main___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Util_1__mkPanicMessage___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Json_render___main___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = l_Lean_Json_renderString(x_2);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = 0;
x_7 = l_Lean_Json_render___main___lambda__2___closed__1;
x_8 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_6);
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_6);
x_11 = l_Lean_Json_render___main(x_3);
x_12 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_6);
x_13 = lean_format_group(x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
return x_14;
}
}
lean_object* _init_l_Lean_Json_render___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_nullKind___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Json_render___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_render___main___lambda__1___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Json_render___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonNumber_jsonNumberHasRepr___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Json_render___main___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Json_render___main___closed__3;
x_3 = lean_box(1);
x_4 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Json_render___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_render___main___lambda__2___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Json_render___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_addParenHeuristic___closed__1;
x_2 = lean_string_length(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Json_render___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_addParenHeuristic___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Json_render___main___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("}");
return x_1;
}
}
lean_object* _init_l_Lean_Json_render___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_render___main___closed__8;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Json_render___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Json_render___main___closed__1;
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
x_4 = l_Lean_Format_repr___main___closed__13;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_Format_repr___main___closed__16;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = x_12;
x_14 = l_Id_monad;
x_15 = l_Lean_Json_render___main___closed__2;
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_umapMAux___main___rarg(x_14, lean_box(0), x_15, x_16, x_13);
x_18 = x_17;
x_19 = l_Array_toList___rarg(x_18);
lean_dec(x_18);
x_20 = l_Lean_formatHasFormat;
x_21 = l_Lean_Json_render___main___closed__4;
x_22 = l_Lean_Format_joinSep___main___rarg(x_20, x_19, x_21);
x_23 = 0;
x_24 = l_Lean_Format_sbracket___closed__2;
x_25 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_23);
x_26 = l_Lean_Format_sbracket___closed__3;
x_27 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_23);
x_28 = l_Lean_Format_sbracket___closed__1;
x_29 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_format_group(x_29);
return x_30;
}
default: 
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_box(0);
x_33 = l_Lean_Json_render___main___closed__5;
x_34 = l_RBNode_fold___main___rarg(x_33, x_32, x_31);
x_35 = l_Lean_formatHasFormat;
x_36 = l_Lean_Json_render___main___closed__4;
x_37 = l_Lean_Format_joinSep___main___rarg(x_35, x_34, x_36);
x_38 = 0;
x_39 = l_Lean_Json_render___main___closed__7;
x_40 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_38);
x_41 = l_Lean_Json_render___main___closed__9;
x_42 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_38);
x_43 = l_Lean_Json_render___main___closed__6;
x_44 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_format_group(x_44);
return x_45;
}
}
}
}
lean_object* l_Lean_Json_render___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_render___main___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Json_render___main___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Json_render___main___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Json_render(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_render___main(x_1);
return x_2;
}
}
lean_object* l_Lean_Json_pretty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_render___main(x_1);
x_4 = lean_format_pretty(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Json_jsonHasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_render), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Json_jsonHasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Json_jsonHasFormat___closed__1;
return x_1;
}
}
lean_object* l_Lean_Json_jsonHasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(80u);
x_3 = l_Lean_Json_pretty(x_1, x_2);
return x_3;
}
}
lean_object* initialize_Lean_Data_Format(lean_object*);
lean_object* initialize_Lean_Data_Json_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Data_Json_Printer(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Format(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Data_Json_Printer_1__escapeAux___closed__1 = _init_l___private_Lean_Data_Json_Printer_1__escapeAux___closed__1();
lean_mark_persistent(l___private_Lean_Data_Json_Printer_1__escapeAux___closed__1);
l___private_Lean_Data_Json_Printer_1__escapeAux___closed__2 = _init_l___private_Lean_Data_Json_Printer_1__escapeAux___closed__2();
lean_mark_persistent(l___private_Lean_Data_Json_Printer_1__escapeAux___closed__2);
l_Lean_Json_render___main___lambda__2___closed__1 = _init_l_Lean_Json_render___main___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Json_render___main___lambda__2___closed__1);
l_Lean_Json_render___main___closed__1 = _init_l_Lean_Json_render___main___closed__1();
lean_mark_persistent(l_Lean_Json_render___main___closed__1);
l_Lean_Json_render___main___closed__2 = _init_l_Lean_Json_render___main___closed__2();
lean_mark_persistent(l_Lean_Json_render___main___closed__2);
l_Lean_Json_render___main___closed__3 = _init_l_Lean_Json_render___main___closed__3();
lean_mark_persistent(l_Lean_Json_render___main___closed__3);
l_Lean_Json_render___main___closed__4 = _init_l_Lean_Json_render___main___closed__4();
lean_mark_persistent(l_Lean_Json_render___main___closed__4);
l_Lean_Json_render___main___closed__5 = _init_l_Lean_Json_render___main___closed__5();
lean_mark_persistent(l_Lean_Json_render___main___closed__5);
l_Lean_Json_render___main___closed__6 = _init_l_Lean_Json_render___main___closed__6();
lean_mark_persistent(l_Lean_Json_render___main___closed__6);
l_Lean_Json_render___main___closed__7 = _init_l_Lean_Json_render___main___closed__7();
lean_mark_persistent(l_Lean_Json_render___main___closed__7);
l_Lean_Json_render___main___closed__8 = _init_l_Lean_Json_render___main___closed__8();
lean_mark_persistent(l_Lean_Json_render___main___closed__8);
l_Lean_Json_render___main___closed__9 = _init_l_Lean_Json_render___main___closed__9();
lean_mark_persistent(l_Lean_Json_render___main___closed__9);
l_Lean_Json_jsonHasFormat___closed__1 = _init_l_Lean_Json_jsonHasFormat___closed__1();
lean_mark_persistent(l_Lean_Json_jsonHasFormat___closed__1);
l_Lean_Json_jsonHasFormat = _init_l_Lean_Json_jsonHasFormat();
lean_mark_persistent(l_Lean_Json_jsonHasFormat);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
