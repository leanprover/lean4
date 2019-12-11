// Lean compiler output
// Module: Init.Lean.Meta.Exception
// Imports: Init.Lean.Environment Init.Lean.MetavarContext Init.Lean.Util.Message
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
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__51;
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__19;
lean_object* l_Lean_Meta_Exception_toStr___closed__4;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__35;
lean_object* l_Lean_Meta_Exception_toStr___closed__9;
lean_object* l_Lean_Meta_Exception_toStr___closed__8;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__45;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__40;
lean_object* l_Lean_Meta_Exception_toStr___closed__17;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__36;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__65;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__39;
extern lean_object* l_List_repr___rarg___closed__1;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__59;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__31;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__70;
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__11;
extern lean_object* l_Lean_Format_flatten___main___closed__1;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__54;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__69;
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Exception_toStr___closed__13;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Exception_toStr___closed__1;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__52;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__50;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Meta_Exception_Inhabited___closed__1;
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__29;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__25;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__62;
lean_object* l_Lean_Meta_Exception_toStr___closed__2;
lean_object* l_Lean_Meta_Exception_Inhabited;
lean_object* l_Lean_Meta_Exception_toStr___closed__12;
lean_object* l_Lean_Meta_Exception_HasToString;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__68;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__73;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__32;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__10;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__20;
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__57;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__17;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__43;
lean_object* l_Lean_Meta_Exception_toStr___closed__19;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__44;
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
extern lean_object* l_Lean_MessageData_coeOfArrayExpr___closed__2;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__9;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__67;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__8;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_Lean_Meta_Exception_toStr___closed__11;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__27;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__4;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__71;
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__63;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__3;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__37;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__7;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__24;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__55;
lean_object* l_Lean_Meta_Exception_toStr___closed__16;
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__53;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__22;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__42;
lean_object* l_Lean_mkLevelMVar(lean_object*);
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__15;
lean_object* l_Lean_Meta_Exception_toStr___closed__7;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__18;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__30;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__76;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__75;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__26;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__58;
lean_object* l_List_toStringAux___main___at_Lean_Meta_Exception_toStr___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__14;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__28;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__33;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__5;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__78;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__61;
lean_object* l_Lean_Meta_Exception_toStr___closed__10;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__12;
lean_object* l_List_toStringAux___main___at_Lean_Meta_Exception_toStr___spec__2(uint8_t, lean_object*);
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__72;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__23;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__6;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__46;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__34;
lean_object* l_Lean_Meta_Exception_toStr(lean_object*);
lean_object* l_Lean_Meta_Exception_HasToString___closed__1;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__2;
lean_object* l_Lean_Meta_Exception_mkCtx(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__48;
lean_object* l_Lean_Meta_Exception_mkCtx___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Exception_toStr___closed__6;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__13;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__41;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__38;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__21;
lean_object* l_Lean_Meta_Exception_toTraceMessageData(lean_object*);
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__16;
lean_object* l_Lean_Meta_Exception_toStr___closed__18;
lean_object* l_Lean_Meta_Exception_toStr___closed__15;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__74;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__60;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__47;
lean_object* l_Lean_Meta_Exception_toStr___closed__5;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__64;
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_Meta_Exception_toStr___closed__3;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__1;
lean_object* l_Lean_Level_format(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__66;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__56;
lean_object* l_Lean_Meta_Exception_toStr___closed__14;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__77;
lean_object* l_List_toString___at_Lean_Meta_Exception_toStr___spec__1(lean_object*);
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__49;
lean_object* _init_l_Lean_Meta_Exception_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = lean_alloc_ctor(19, 1, 0);
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
x_1 = lean_mk_string("isDefEq is stuck");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toStr___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("type mismatch at let-expression");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toStr___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("application type mismatch");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toStr___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("type class instance expected");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toStr___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("application builder failure");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toStr___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("type class instance synthesis failed");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toStr___closed__19() {
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
case 13:
{
lean_object* x_49; 
lean_dec(x_1);
x_49 = l_Lean_Meta_Exception_toStr___closed__14;
return x_49;
}
case 14:
{
lean_object* x_50; 
lean_dec(x_1);
x_50 = l_Lean_Meta_Exception_toStr___closed__15;
return x_50;
}
case 15:
{
lean_object* x_51; 
lean_dec(x_1);
x_51 = l_Lean_Meta_Exception_toStr___closed__16;
return x_51;
}
case 16:
{
lean_object* x_52; 
lean_dec(x_1);
x_52 = l_Lean_Meta_Exception_toStr___closed__17;
return x_52;
}
case 17:
{
lean_object* x_53; 
lean_dec(x_1);
x_53 = l_Lean_Meta_Exception_toStr___closed__18;
return x_53;
}
case 18:
{
lean_object* x_54; 
lean_dec(x_1);
x_54 = l_Lean_Meta_Exception_toStr___closed__19;
return x_54;
}
case 19:
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
lean_dec(x_1);
return x_55;
}
default: 
{
lean_object* x_56; 
lean_dec(x_1);
x_56 = l_Lean_Meta_Exception_toStr___closed__13;
return x_56;
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
lean_object* l_Lean_Meta_Exception_mkCtx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(5, 4, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
lean_ctor_set(x_6, 3, x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_Exception_mkCtx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Exception_mkCtx(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknownConst");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__2;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_flatten___main___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__3;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknownFVar");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__7;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__8;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknownExprMVar");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__11;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__12;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknownLevelMVar");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__14;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__15;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__16;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpectedBVar");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__18;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__19;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__20;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("functionExpected");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__22;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__23;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__24;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("typeExpected");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__26;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__27;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__28;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("incorrectNumOfLevels");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__30;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__31;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__32;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalidProjection");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__34;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__35;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__36;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("revertFailure");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__38;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__39;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__41() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("readOnlyMVar");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__41;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__42;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__43;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__45() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isLevelDefEqStuck");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__45;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__46;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__47;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__49() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" =?= ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__49;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__50;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__52() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isExprDefEqStuck");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__52;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__53;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__54;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__56() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("letTypeMismatch");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__56;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__57;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__58;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__60() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("appTypeMismatch");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__60;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__62() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__61;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__62;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__64() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("notInstance");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__65() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__64;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__66() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__65;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__67() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__66;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__68() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("appBuilder");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__69() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__68;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__70() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__69;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__71() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__70;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__72() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("synthInstance");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__73() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__72;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__74() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__73;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__75() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__74;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__76() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("internal bug");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__77() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__76;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__78() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__77;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Exception_toTraceMessageData(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l_Lean_Meta_Exception_toTraceMessageData___closed__5;
x_6 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_Lean_Meta_Exception_mkCtx(x_3, x_6);
lean_dec(x_3);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_Lean_Meta_Exception_toTraceMessageData___closed__9;
x_12 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Meta_Exception_mkCtx(x_9, x_12);
lean_dec(x_9);
return x_13;
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_mkMVar(x_14);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_Meta_Exception_toTraceMessageData___closed__13;
x_19 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Meta_Exception_mkCtx(x_15, x_19);
lean_dec(x_15);
return x_20;
}
case 3:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_23 = l_Lean_mkLevelMVar(x_21);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_Meta_Exception_toTraceMessageData___closed__17;
x_26 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Meta_Exception_mkCtx(x_22, x_26);
lean_dec(x_22);
return x_27;
}
case 4:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l_Lean_mkBVar(x_28);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lean_Meta_Exception_toTraceMessageData___closed__21;
x_32 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
case 5:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
lean_dec(x_1);
x_36 = l_Lean_mkApp(x_33, x_34);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_Meta_Exception_toTraceMessageData___closed__25;
x_39 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_Meta_Exception_mkCtx(x_35, x_39);
lean_dec(x_35);
return x_40;
}
case 6:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_41);
x_44 = l_Lean_Meta_Exception_toTraceMessageData___closed__29;
x_45 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_Meta_Exception_mkCtx(x_42, x_45);
lean_dec(x_42);
return x_46;
}
case 7:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_1, 2);
lean_inc(x_49);
lean_dec(x_1);
x_50 = l_Lean_mkConst(x_47, x_48);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l_Lean_Meta_Exception_toTraceMessageData___closed__33;
x_53 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_Meta_Exception_mkCtx(x_49, x_53);
lean_dec(x_49);
return x_54;
}
case 8:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_1, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_1, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_1, 3);
lean_inc(x_58);
lean_dec(x_1);
x_59 = l_Lean_mkProj(x_55, x_56, x_57);
x_60 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = l_Lean_Meta_Exception_toTraceMessageData___closed__37;
x_62 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l_Lean_Meta_Exception_mkCtx(x_58, x_62);
lean_dec(x_58);
return x_63;
}
case 9:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_1, 2);
lean_inc(x_64);
lean_dec(x_1);
x_65 = l_Lean_Meta_Exception_toTraceMessageData___closed__40;
x_66 = l_Lean_Meta_Exception_mkCtx(x_64, x_65);
lean_dec(x_64);
return x_66;
}
case 10:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_1, 1);
lean_inc(x_68);
lean_dec(x_1);
x_69 = l_Lean_mkMVar(x_67);
x_70 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = l_Lean_Meta_Exception_toTraceMessageData___closed__44;
x_72 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_Meta_Exception_mkCtx(x_68, x_72);
lean_dec(x_68);
return x_73;
}
case 11:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_1, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_1, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_1, 2);
lean_inc(x_76);
lean_dec(x_1);
x_77 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_77, 0, x_74);
x_78 = l_Lean_Meta_Exception_toTraceMessageData___closed__48;
x_79 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_Lean_Meta_Exception_toTraceMessageData___closed__51;
x_81 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_82, 0, x_75);
x_83 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_Meta_Exception_mkCtx(x_76, x_83);
lean_dec(x_76);
return x_84;
}
case 12:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_85 = lean_ctor_get(x_1, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_1, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_1, 2);
lean_inc(x_87);
lean_dec(x_1);
x_88 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_88, 0, x_85);
x_89 = l_Lean_Meta_Exception_toTraceMessageData___closed__55;
x_90 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = l_Lean_Meta_Exception_toTraceMessageData___closed__51;
x_92 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_93, 0, x_86);
x_94 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_Meta_Exception_mkCtx(x_87, x_94);
lean_dec(x_87);
return x_95;
}
case 13:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_ctor_get(x_1, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_1, 1);
lean_inc(x_97);
lean_dec(x_1);
x_98 = l_Lean_mkFVar(x_96);
x_99 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = l_Lean_Meta_Exception_toTraceMessageData___closed__59;
x_101 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = l_Lean_Meta_Exception_mkCtx(x_97, x_101);
lean_dec(x_97);
return x_102;
}
case 14:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_103 = lean_ctor_get(x_1, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_1, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_1, 2);
lean_inc(x_105);
lean_dec(x_1);
x_106 = l_Lean_mkApp(x_103, x_104);
x_107 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = l_Lean_Meta_Exception_toTraceMessageData___closed__63;
x_109 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = l_Lean_Meta_Exception_mkCtx(x_105, x_109);
lean_dec(x_105);
return x_110;
}
case 15:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_1, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_1, 1);
lean_inc(x_112);
lean_dec(x_1);
x_113 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_113, 0, x_111);
x_114 = l_Lean_Meta_Exception_toTraceMessageData___closed__67;
x_115 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = l_Lean_Meta_Exception_mkCtx(x_112, x_115);
lean_dec(x_112);
return x_116;
}
case 16:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_117 = lean_ctor_get(x_1, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_1, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_1, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_1, 3);
lean_inc(x_120);
lean_dec(x_1);
x_121 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_121, 0, x_117);
x_122 = l_Lean_Meta_Exception_toTraceMessageData___closed__71;
x_123 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_125 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_unsigned_to_nat(0u);
x_127 = l_Lean_MessageData_coeOfArrayExpr___closed__2;
x_128 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_119, x_126, x_127);
lean_dec(x_119);
x_129 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_129, 0, x_125);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_124);
x_131 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_131, 0, x_118);
x_132 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_133 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_Meta_Exception_mkCtx(x_120, x_133);
lean_dec(x_120);
return x_134;
}
case 17:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_135 = lean_ctor_get(x_1, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_1, 1);
lean_inc(x_136);
lean_dec(x_1);
x_137 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_137, 0, x_135);
x_138 = l_Lean_Meta_Exception_toTraceMessageData___closed__75;
x_139 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
x_140 = l_Lean_Meta_Exception_mkCtx(x_136, x_139);
lean_dec(x_136);
return x_140;
}
case 18:
{
lean_object* x_141; 
lean_dec(x_1);
x_141 = l_Lean_Meta_Exception_toTraceMessageData___closed__78;
return x_141;
}
default: 
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_1, 0);
lean_inc(x_142);
lean_dec(x_1);
x_143 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_144 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_144, 0, x_143);
return x_144;
}
}
}
}
lean_object* initialize_Init_Lean_Environment(lean_object*);
lean_object* initialize_Init_Lean_MetavarContext(lean_object*);
lean_object* initialize_Init_Lean_Util_Message(lean_object*);
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
res = initialize_Init_Lean_Util_Message(lean_io_mk_world());
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
l_Lean_Meta_Exception_toStr___closed__14 = _init_l_Lean_Meta_Exception_toStr___closed__14();
lean_mark_persistent(l_Lean_Meta_Exception_toStr___closed__14);
l_Lean_Meta_Exception_toStr___closed__15 = _init_l_Lean_Meta_Exception_toStr___closed__15();
lean_mark_persistent(l_Lean_Meta_Exception_toStr___closed__15);
l_Lean_Meta_Exception_toStr___closed__16 = _init_l_Lean_Meta_Exception_toStr___closed__16();
lean_mark_persistent(l_Lean_Meta_Exception_toStr___closed__16);
l_Lean_Meta_Exception_toStr___closed__17 = _init_l_Lean_Meta_Exception_toStr___closed__17();
lean_mark_persistent(l_Lean_Meta_Exception_toStr___closed__17);
l_Lean_Meta_Exception_toStr___closed__18 = _init_l_Lean_Meta_Exception_toStr___closed__18();
lean_mark_persistent(l_Lean_Meta_Exception_toStr___closed__18);
l_Lean_Meta_Exception_toStr___closed__19 = _init_l_Lean_Meta_Exception_toStr___closed__19();
lean_mark_persistent(l_Lean_Meta_Exception_toStr___closed__19);
l_Lean_Meta_Exception_HasToString___closed__1 = _init_l_Lean_Meta_Exception_HasToString___closed__1();
lean_mark_persistent(l_Lean_Meta_Exception_HasToString___closed__1);
l_Lean_Meta_Exception_HasToString = _init_l_Lean_Meta_Exception_HasToString();
lean_mark_persistent(l_Lean_Meta_Exception_HasToString);
l_Lean_Meta_Exception_toTraceMessageData___closed__1 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__1();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__1);
l_Lean_Meta_Exception_toTraceMessageData___closed__2 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__2();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__2);
l_Lean_Meta_Exception_toTraceMessageData___closed__3 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__3();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__3);
l_Lean_Meta_Exception_toTraceMessageData___closed__4 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__4();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__4);
l_Lean_Meta_Exception_toTraceMessageData___closed__5 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__5();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__5);
l_Lean_Meta_Exception_toTraceMessageData___closed__6 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__6();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__6);
l_Lean_Meta_Exception_toTraceMessageData___closed__7 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__7();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__7);
l_Lean_Meta_Exception_toTraceMessageData___closed__8 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__8();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__8);
l_Lean_Meta_Exception_toTraceMessageData___closed__9 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__9();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__9);
l_Lean_Meta_Exception_toTraceMessageData___closed__10 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__10();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__10);
l_Lean_Meta_Exception_toTraceMessageData___closed__11 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__11();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__11);
l_Lean_Meta_Exception_toTraceMessageData___closed__12 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__12();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__12);
l_Lean_Meta_Exception_toTraceMessageData___closed__13 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__13();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__13);
l_Lean_Meta_Exception_toTraceMessageData___closed__14 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__14();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__14);
l_Lean_Meta_Exception_toTraceMessageData___closed__15 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__15();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__15);
l_Lean_Meta_Exception_toTraceMessageData___closed__16 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__16();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__16);
l_Lean_Meta_Exception_toTraceMessageData___closed__17 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__17();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__17);
l_Lean_Meta_Exception_toTraceMessageData___closed__18 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__18();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__18);
l_Lean_Meta_Exception_toTraceMessageData___closed__19 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__19();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__19);
l_Lean_Meta_Exception_toTraceMessageData___closed__20 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__20();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__20);
l_Lean_Meta_Exception_toTraceMessageData___closed__21 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__21();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__21);
l_Lean_Meta_Exception_toTraceMessageData___closed__22 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__22();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__22);
l_Lean_Meta_Exception_toTraceMessageData___closed__23 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__23();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__23);
l_Lean_Meta_Exception_toTraceMessageData___closed__24 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__24();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__24);
l_Lean_Meta_Exception_toTraceMessageData___closed__25 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__25();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__25);
l_Lean_Meta_Exception_toTraceMessageData___closed__26 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__26();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__26);
l_Lean_Meta_Exception_toTraceMessageData___closed__27 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__27();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__27);
l_Lean_Meta_Exception_toTraceMessageData___closed__28 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__28();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__28);
l_Lean_Meta_Exception_toTraceMessageData___closed__29 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__29();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__29);
l_Lean_Meta_Exception_toTraceMessageData___closed__30 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__30();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__30);
l_Lean_Meta_Exception_toTraceMessageData___closed__31 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__31();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__31);
l_Lean_Meta_Exception_toTraceMessageData___closed__32 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__32();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__32);
l_Lean_Meta_Exception_toTraceMessageData___closed__33 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__33();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__33);
l_Lean_Meta_Exception_toTraceMessageData___closed__34 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__34();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__34);
l_Lean_Meta_Exception_toTraceMessageData___closed__35 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__35();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__35);
l_Lean_Meta_Exception_toTraceMessageData___closed__36 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__36();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__36);
l_Lean_Meta_Exception_toTraceMessageData___closed__37 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__37();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__37);
l_Lean_Meta_Exception_toTraceMessageData___closed__38 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__38();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__38);
l_Lean_Meta_Exception_toTraceMessageData___closed__39 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__39();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__39);
l_Lean_Meta_Exception_toTraceMessageData___closed__40 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__40();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__40);
l_Lean_Meta_Exception_toTraceMessageData___closed__41 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__41();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__41);
l_Lean_Meta_Exception_toTraceMessageData___closed__42 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__42();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__42);
l_Lean_Meta_Exception_toTraceMessageData___closed__43 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__43();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__43);
l_Lean_Meta_Exception_toTraceMessageData___closed__44 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__44();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__44);
l_Lean_Meta_Exception_toTraceMessageData___closed__45 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__45();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__45);
l_Lean_Meta_Exception_toTraceMessageData___closed__46 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__46();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__46);
l_Lean_Meta_Exception_toTraceMessageData___closed__47 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__47();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__47);
l_Lean_Meta_Exception_toTraceMessageData___closed__48 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__48();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__48);
l_Lean_Meta_Exception_toTraceMessageData___closed__49 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__49();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__49);
l_Lean_Meta_Exception_toTraceMessageData___closed__50 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__50();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__50);
l_Lean_Meta_Exception_toTraceMessageData___closed__51 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__51();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__51);
l_Lean_Meta_Exception_toTraceMessageData___closed__52 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__52();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__52);
l_Lean_Meta_Exception_toTraceMessageData___closed__53 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__53();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__53);
l_Lean_Meta_Exception_toTraceMessageData___closed__54 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__54();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__54);
l_Lean_Meta_Exception_toTraceMessageData___closed__55 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__55();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__55);
l_Lean_Meta_Exception_toTraceMessageData___closed__56 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__56();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__56);
l_Lean_Meta_Exception_toTraceMessageData___closed__57 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__57();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__57);
l_Lean_Meta_Exception_toTraceMessageData___closed__58 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__58();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__58);
l_Lean_Meta_Exception_toTraceMessageData___closed__59 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__59();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__59);
l_Lean_Meta_Exception_toTraceMessageData___closed__60 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__60();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__60);
l_Lean_Meta_Exception_toTraceMessageData___closed__61 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__61();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__61);
l_Lean_Meta_Exception_toTraceMessageData___closed__62 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__62();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__62);
l_Lean_Meta_Exception_toTraceMessageData___closed__63 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__63();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__63);
l_Lean_Meta_Exception_toTraceMessageData___closed__64 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__64();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__64);
l_Lean_Meta_Exception_toTraceMessageData___closed__65 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__65();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__65);
l_Lean_Meta_Exception_toTraceMessageData___closed__66 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__66();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__66);
l_Lean_Meta_Exception_toTraceMessageData___closed__67 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__67();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__67);
l_Lean_Meta_Exception_toTraceMessageData___closed__68 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__68();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__68);
l_Lean_Meta_Exception_toTraceMessageData___closed__69 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__69();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__69);
l_Lean_Meta_Exception_toTraceMessageData___closed__70 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__70();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__70);
l_Lean_Meta_Exception_toTraceMessageData___closed__71 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__71();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__71);
l_Lean_Meta_Exception_toTraceMessageData___closed__72 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__72();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__72);
l_Lean_Meta_Exception_toTraceMessageData___closed__73 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__73();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__73);
l_Lean_Meta_Exception_toTraceMessageData___closed__74 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__74();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__74);
l_Lean_Meta_Exception_toTraceMessageData___closed__75 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__75();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__75);
l_Lean_Meta_Exception_toTraceMessageData___closed__76 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__76();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__76);
l_Lean_Meta_Exception_toTraceMessageData___closed__77 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__77();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__77);
l_Lean_Meta_Exception_toTraceMessageData___closed__78 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__78();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__78);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
