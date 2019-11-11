// Lean compiler output
// Module: Init.Lean.Meta.Exception
// Imports: Init.Lean.Environment Init.Lean.MetavarContext
#include "runtime/lean.h"
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
lean_object* l_List_toString___at_Lean_Meta_Exception_toStr___spec__1(lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Exception_toStr___closed__5;
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l_Lean_Meta_Exception_toStr___closed__1;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Level_format(lean_object*);
lean_object* l_Lean_Meta_Exception_HasToString;
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_List_toStringAux___main___at_Lean_Meta_Exception_toStr___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Exception_toStr___closed__8;
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_Meta_Exception_toStr___closed__4;
lean_object* l_Lean_Meta_Exception_Inhabited;
lean_object* l_Lean_Meta_Exception_toStr___closed__3;
lean_object* l_Lean_Meta_Exception_HasToString___closed__1;
lean_object* l_Lean_Meta_Exception_toStr(lean_object*);
lean_object* l_Lean_Meta_Exception_toStr___closed__9;
lean_object* l_Lean_Meta_Exception_toStr___closed__2;
lean_object* l_Lean_Meta_Exception_toStr___closed__10;
lean_object* l_Lean_Meta_Exception_toStr___closed__11;
lean_object* l_Lean_Meta_Exception_toStr___closed__6;
lean_object* l_Lean_Meta_Exception_toStr___closed__7;
lean_object* l_Lean_Meta_Exception_Inhabited___closed__1;
lean_object* l_List_toStringAux___main___at_Lean_Meta_Exception_toStr___spec__2(uint8_t, lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Meta_Exception_toStr___closed__12;
extern lean_object* l_List_repr___rarg___closed__1;
lean_object* l_Lean_Meta_Exception_toStr___closed__13;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* _init_l_Lean_Meta_Exception_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Exception_Inhabited___closed__1;
return x_1;
}
}
lean_object* l_List_toStringAux___main___at_Lean_Meta_Exception_toStr___spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_String_splitAux___main___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Level_format(x_4);
x_7 = l_Lean_Options_empty;
x_8 = l_Lean_Format_pretty(x_6, x_7);
x_9 = l_List_reprAux___main___rarg___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_List_toStringAux___main___at_Lean_Meta_Exception_toStr___spec__2(x_1, x_5);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
return x_12;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
x_13 = l_String_splitAux___main___closed__1;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_Lean_Level_format(x_14);
x_17 = l_Lean_Options_empty;
x_18 = l_Lean_Format_pretty(x_16, x_17);
x_19 = 0;
x_20 = l_List_toStringAux___main___at_Lean_Meta_Exception_toStr___spec__2(x_19, x_15);
x_21 = lean_string_append(x_18, x_20);
lean_dec(x_20);
return x_21;
}
}
}
}
lean_object* l_List_toString___at_Lean_Meta_Exception_toStr___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_repr___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = 1;
x_4 = l_List_toStringAux___main___at_Lean_Meta_Exception_toStr___spec__2(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
lean_object* _init_l_Lean_Meta_Exception_toStr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown constant '");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toStr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown free variable '");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toStr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown metavariable '");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toStr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown universe level metavariable '");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toStr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected loose bound variable #");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toStr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("function expected");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toStr___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("type expected");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toStr___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("incorrect number of universe levels for '");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toStr___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toStr___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toStr___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("revert failure");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toStr___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("try to assign read only metavariable");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toStr___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("bug");
return x_1;
}
}
lean_object* l_Lean_Meta_Exception_toStr(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_Name_toString___closed__1;
x_4 = l_Lean_Name_toStringWithSep___main(x_3, x_2);
x_5 = l_Lean_Meta_Exception_toStr___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_Char_HasRepr___closed__1;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Name_toString___closed__1;
x_11 = l_Lean_Name_toStringWithSep___main(x_10, x_9);
x_12 = l_Lean_Meta_Exception_toStr___closed__2;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Char_HasRepr___closed__1;
x_15 = lean_string_append(x_13, x_14);
return x_15;
}
case 2:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_Name_toString___closed__1;
x_18 = l_Lean_Name_toStringWithSep___main(x_17, x_16);
x_19 = l_Lean_Meta_Exception_toStr___closed__3;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Char_HasRepr___closed__1;
x_22 = lean_string_append(x_20, x_21);
return x_22;
}
case 3:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = l_Lean_Name_toString___closed__1;
x_25 = l_Lean_Name_toStringWithSep___main(x_24, x_23);
x_26 = l_Lean_Meta_Exception_toStr___closed__4;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l_Char_HasRepr___closed__1;
x_29 = lean_string_append(x_27, x_28);
return x_29;
}
case 4:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = l_Nat_repr(x_30);
x_32 = l_Lean_Meta_Exception_toStr___closed__5;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
return x_33;
}
case 5:
{
lean_object* x_34; 
lean_dec(x_1);
x_34 = l_Lean_Meta_Exception_toStr___closed__6;
return x_34;
}
case 6:
{
lean_object* x_35; 
lean_dec(x_1);
x_35 = l_Lean_Meta_Exception_toStr___closed__7;
return x_35;
}
case 7:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec(x_1);
x_38 = l_Lean_Name_toString___closed__1;
x_39 = l_Lean_Name_toStringWithSep___main(x_38, x_36);
x_40 = l_Lean_Meta_Exception_toStr___closed__8;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = l_Lean_Meta_Exception_toStr___closed__9;
x_43 = lean_string_append(x_41, x_42);
x_44 = l_List_toString___at_Lean_Meta_Exception_toStr___spec__1(x_37);
x_45 = lean_string_append(x_43, x_44);
lean_dec(x_44);
return x_45;
}
case 8:
{
lean_object* x_46; 
lean_dec(x_1);
x_46 = l_Lean_Meta_Exception_toStr___closed__10;
return x_46;
}
case 9:
{
lean_object* x_47; 
lean_dec(x_1);
x_47 = l_Lean_Meta_Exception_toStr___closed__11;
return x_47;
}
case 10:
{
lean_object* x_48; 
lean_dec(x_1);
x_48 = l_Lean_Meta_Exception_toStr___closed__12;
return x_48;
}
case 11:
{
lean_object* x_49; 
lean_dec(x_1);
x_49 = l_Lean_Meta_Exception_toStr___closed__13;
return x_49;
}
default: 
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
lean_dec(x_1);
return x_50;
}
}
}
}
lean_object* l_List_toStringAux___main___at_Lean_Meta_Exception_toStr___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___main___at_Lean_Meta_Exception_toStr___spec__2(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_Exception_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Exception_toStr), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_HasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Exception_HasToString___closed__1;
return x_1;
}
}
lean_object* initialize_Init_Lean_Environment(lean_object*);
lean_object* initialize_Init_Lean_MetavarContext(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_Exception(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_MetavarContext(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Exception_Inhabited___closed__1 = _init_l_Lean_Meta_Exception_Inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_Exception_Inhabited___closed__1);
l_Lean_Meta_Exception_Inhabited = _init_l_Lean_Meta_Exception_Inhabited();
lean_mark_persistent(l_Lean_Meta_Exception_Inhabited);
l_Lean_Meta_Exception_toStr___closed__1 = _init_l_Lean_Meta_Exception_toStr___closed__1();
lean_mark_persistent(l_Lean_Meta_Exception_toStr___closed__1);
l_Lean_Meta_Exception_toStr___closed__2 = _init_l_Lean_Meta_Exception_toStr___closed__2();
lean_mark_persistent(l_Lean_Meta_Exception_toStr___closed__2);
l_Lean_Meta_Exception_toStr___closed__3 = _init_l_Lean_Meta_Exception_toStr___closed__3();
lean_mark_persistent(l_Lean_Meta_Exception_toStr___closed__3);
l_Lean_Meta_Exception_toStr___closed__4 = _init_l_Lean_Meta_Exception_toStr___closed__4();
lean_mark_persistent(l_Lean_Meta_Exception_toStr___closed__4);
l_Lean_Meta_Exception_toStr___closed__5 = _init_l_Lean_Meta_Exception_toStr___closed__5();
lean_mark_persistent(l_Lean_Meta_Exception_toStr___closed__5);
l_Lean_Meta_Exception_toStr___closed__6 = _init_l_Lean_Meta_Exception_toStr___closed__6();
lean_mark_persistent(l_Lean_Meta_Exception_toStr___closed__6);
l_Lean_Meta_Exception_toStr___closed__7 = _init_l_Lean_Meta_Exception_toStr___closed__7();
lean_mark_persistent(l_Lean_Meta_Exception_toStr___closed__7);
l_Lean_Meta_Exception_toStr___closed__8 = _init_l_Lean_Meta_Exception_toStr___closed__8();
lean_mark_persistent(l_Lean_Meta_Exception_toStr___closed__8);
l_Lean_Meta_Exception_toStr___closed__9 = _init_l_Lean_Meta_Exception_toStr___closed__9();
lean_mark_persistent(l_Lean_Meta_Exception_toStr___closed__9);
l_Lean_Meta_Exception_toStr___closed__10 = _init_l_Lean_Meta_Exception_toStr___closed__10();
lean_mark_persistent(l_Lean_Meta_Exception_toStr___closed__10);
l_Lean_Meta_Exception_toStr___closed__11 = _init_l_Lean_Meta_Exception_toStr___closed__11();
lean_mark_persistent(l_Lean_Meta_Exception_toStr___closed__11);
l_Lean_Meta_Exception_toStr___closed__12 = _init_l_Lean_Meta_Exception_toStr___closed__12();
lean_mark_persistent(l_Lean_Meta_Exception_toStr___closed__12);
l_Lean_Meta_Exception_toStr___closed__13 = _init_l_Lean_Meta_Exception_toStr___closed__13();
lean_mark_persistent(l_Lean_Meta_Exception_toStr___closed__13);
l_Lean_Meta_Exception_HasToString___closed__1 = _init_l_Lean_Meta_Exception_HasToString___closed__1();
lean_mark_persistent(l_Lean_Meta_Exception_HasToString___closed__1);
l_Lean_Meta_Exception_HasToString = _init_l_Lean_Meta_Exception_HasToString();
lean_mark_persistent(l_Lean_Meta_Exception_HasToString);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
