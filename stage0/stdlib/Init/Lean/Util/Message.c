// Lean compiler output
// Module: Init.Lean.Util.Message
// Imports: Init.Data.ToString Init.Lean.Data.Position Init.Lean.Syntax Init.Lean.MetavarContext Init.Lean.Environment
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
lean_object* l_List_reverse___rarg(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
extern lean_object* l_addParenHeuristic___closed__2;
lean_object* l_Lean_MetavarContext_instantiateMVars(lean_object*, lean_object*);
lean_object* l_Lean_Message_toString___closed__3;
lean_object* l_Lean_MessageLog_Inhabited;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object*);
extern lean_object* l_Lean_Format_flatten___main___closed__1;
lean_object* l_Lean_MessageData_coeOfLevel(lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1;
lean_object* l_Lean_MessageData_Lean_HasFormat(lean_object*);
lean_object* l_Lean_MessageData_coeOfFormat(lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_formatAux___main(lean_object*, lean_object*);
extern lean_object* l_Lean_formatKVMap___closed__1;
extern lean_object* l_String_splitAux___main___closed__1;
uint8_t l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1(uint8_t, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__2;
extern lean_object* l_EStateM_Result_toString___rarg___closed__2;
lean_object* l_Lean_MessageLog_toList(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_coeOfName(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_Inhabited;
lean_object* l_Lean_fmt___at_Lean_MessageData_formatAux___main___spec__1(lean_object*);
lean_object* l_Lean_Message_Inhabited;
lean_object* l_Lean_Message_HasToString;
lean_object* l_Lean_MessageLog_HasAppend;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_MessageData_coeOfArrayExpr___closed__2;
lean_object* l_Lean_Message_toString___closed__4;
lean_object* l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Message_toString___closed__1;
lean_object* l_Lean_Message_toString___closed__2;
extern lean_object* l_Lean_Options_empty;
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_MessageData_coeOfArrayExpr(lean_object*);
extern lean_object* l_String_Iterator_HasRepr___closed__2;
lean_object* l_Lean_Message_HasToString___closed__1;
lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_HasAppend___closed__1;
extern lean_object* l_Lean_Format_sbracket___closed__3;
lean_object* l_Lean_fmt___at_Lean_Message_toString___spec__1(lean_object*);
lean_object* l_Lean_MessageLog_empty;
lean_object* l_Lean_mkErrorStringWithPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_coeOfArrayExpr___closed__1;
extern lean_object* l_Lean_Format_sbracket___closed__1;
lean_object* l_Lean_MessageData_HasAppend(lean_object*, lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* lean_format_group(lean_object*);
lean_object* l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx___main(lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
lean_object* l_Lean_Message_Inhabited___closed__1;
lean_object* l_Lean_Message_Inhabited___closed__2;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Message_toString___closed__5;
uint8_t l_Lean_MessageLog_isEmpty(lean_object*);
lean_object* l_Lean_MessageData_coeOfExpr(lean_object*);
lean_object* l_Lean_Message_toString(lean_object*);
lean_object* l_Lean_MessageData_formatAux(lean_object*, lean_object*);
lean_object* l_Lean_Level_format(lean_object*);
lean_object* l_Lean_MessageData_Inhabited___closed__1;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_isEmpty___boxed(lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_coeOfArrayExpr___boxed(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_mkErrorStringWithPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = l___private_Init_Util_1__mkPanicMessage___closed__2;
x_6 = lean_string_append(x_1, x_5);
x_7 = l_Nat_repr(x_2);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_9 = lean_string_append(x_8, x_5);
x_10 = l_Nat_repr(x_3);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
x_12 = l_String_Iterator_HasRepr___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_string_append(x_13, x_4);
return x_14;
}
}
lean_object* l_Lean_mkErrorStringWithPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkErrorStringWithPos(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* _init_l_Lean_MessageData_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_MessageData_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageData_Inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_fmt___at_Lean_MessageData_formatAux___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_format(x_1);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = 0;
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_9);
lean_inc(x_1);
x_12 = l_Lean_MessageData_formatAux___main(x_1, x_8);
x_13 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_9);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_4 = x_15;
x_5 = x_13;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = 0;
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_9);
lean_inc(x_1);
x_12 = l_Lean_MessageData_formatAux___main(x_1, x_8);
x_13 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_9);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_4 = x_15;
x_5 = x_13;
goto _start;
}
}
}
lean_object* l_Lean_MessageData_formatAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Syntax_formatStx___main(x_4);
return x_5;
}
case 2:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
case 3:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_Level_format(x_9);
return x_10;
}
case 4:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(x_11);
return x_12;
}
case 5:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 3);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_1 = x_19;
x_2 = x_16;
goto _start;
}
case 6:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = l_Lean_MessageData_formatAux___main(x_1, x_22);
x_24 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
case 7:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
lean_dec(x_2);
x_26 = l_Lean_MessageData_formatAux___main(x_1, x_25);
x_27 = lean_format_group(x_26);
return x_27;
}
case 8:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
lean_dec(x_2);
x_30 = l_Lean_MessageData_formatAux___main(x_1, x_28);
x_31 = l_Lean_MessageData_formatAux___main(x_1, x_29);
x_32 = 0;
x_33 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_32);
return x_33;
}
case 9:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_dec(x_2);
x_36 = l_Lean_Name_toString___closed__1;
x_37 = l_Lean_Name_toStringWithSep___main(x_36, x_34);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = 0;
x_40 = l_Lean_Format_sbracket___closed__2;
x_41 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*2, x_39);
x_42 = l_Lean_Format_sbracket___closed__3;
x_43 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*2, x_39);
x_44 = l_Lean_Format_sbracket___closed__1;
x_45 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_format_group(x_45);
x_47 = l_Lean_Format_flatten___main___closed__1;
x_48 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_39);
x_49 = l_Lean_MessageData_formatAux___main(x_1, x_35);
x_50 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_39);
return x_50;
}
default: 
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_2, 0);
lean_inc(x_51);
lean_dec(x_2);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_box(0);
x_54 = l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__2(x_1, x_51, x_51, x_52, x_53);
lean_dec(x_51);
x_55 = lean_unsigned_to_nat(2u);
x_56 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_57, 1);
x_60 = lean_ctor_get(x_57, 0);
lean_dec(x_60);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_61; 
lean_free_object(x_57);
lean_dec(x_59);
lean_dec(x_1);
x_61 = lean_ctor_get(x_2, 0);
lean_inc(x_61);
lean_dec(x_2);
return x_61;
}
case 1:
{
lean_object* x_62; lean_object* x_63; 
lean_free_object(x_57);
lean_dec(x_59);
lean_dec(x_1);
x_62 = lean_ctor_get(x_2, 0);
lean_inc(x_62);
lean_dec(x_2);
x_63 = l_Lean_Syntax_formatStx___main(x_62);
return x_63;
}
case 2:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_free_object(x_57);
lean_dec(x_1);
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
lean_dec(x_59);
x_65 = lean_ctor_get(x_2, 0);
lean_inc(x_65);
lean_dec(x_2);
x_66 = l_Lean_MetavarContext_instantiateMVars(x_64, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_expr_dbg_to_string(x_67);
lean_dec(x_67);
x_69 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
case 3:
{
lean_object* x_70; lean_object* x_71; 
lean_free_object(x_57);
lean_dec(x_59);
lean_dec(x_1);
x_70 = lean_ctor_get(x_2, 0);
lean_inc(x_70);
lean_dec(x_2);
x_71 = l_Lean_Level_format(x_70);
return x_71;
}
case 4:
{
lean_object* x_72; lean_object* x_73; 
lean_free_object(x_57);
lean_dec(x_59);
lean_dec(x_1);
x_72 = lean_ctor_get(x_2, 0);
lean_inc(x_72);
lean_dec(x_2);
x_73 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(x_72);
return x_73;
}
case 5:
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_1);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_1, 0);
lean_dec(x_75);
x_76 = !lean_is_exclusive(x_59);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_59, 1);
lean_dec(x_77);
x_78 = lean_ctor_get(x_59, 0);
lean_dec(x_78);
x_79 = lean_ctor_get(x_2, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_2, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_2, 3);
lean_inc(x_82);
lean_dec(x_2);
lean_ctor_set(x_59, 1, x_81);
lean_ctor_set(x_59, 0, x_80);
lean_ctor_set(x_57, 0, x_79);
x_2 = x_82;
goto _start;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_59);
x_84 = lean_ctor_get(x_2, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_2, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_2, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_2, 3);
lean_inc(x_87);
lean_dec(x_2);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
lean_ctor_set(x_57, 1, x_88);
lean_ctor_set(x_57, 0, x_84);
x_2 = x_87;
goto _start;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_1);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_90 = x_59;
} else {
 lean_dec_ref(x_59);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_2, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_2, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_2, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_2, 3);
lean_inc(x_94);
lean_dec(x_2);
if (lean_is_scalar(x_90)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_90;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set(x_57, 1, x_95);
lean_ctor_set(x_57, 0, x_91);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_57);
x_1 = x_96;
x_2 = x_94;
goto _start;
}
}
case 6:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_free_object(x_57);
lean_dec(x_59);
x_98 = lean_ctor_get(x_2, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_2, 1);
lean_inc(x_99);
lean_dec(x_2);
x_100 = l_Lean_MessageData_formatAux___main(x_1, x_99);
x_101 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
case 7:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_free_object(x_57);
lean_dec(x_59);
x_102 = lean_ctor_get(x_2, 0);
lean_inc(x_102);
lean_dec(x_2);
x_103 = l_Lean_MessageData_formatAux___main(x_1, x_102);
x_104 = lean_format_group(x_103);
return x_104;
}
case 8:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; 
lean_free_object(x_57);
lean_dec(x_59);
x_105 = lean_ctor_get(x_2, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_2, 1);
lean_inc(x_106);
lean_dec(x_2);
lean_inc(x_1);
x_107 = l_Lean_MessageData_formatAux___main(x_1, x_105);
x_108 = l_Lean_MessageData_formatAux___main(x_1, x_106);
x_109 = 0;
x_110 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*2, x_109);
return x_110;
}
case 9:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_free_object(x_57);
lean_dec(x_59);
x_111 = lean_ctor_get(x_2, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_2, 1);
lean_inc(x_112);
lean_dec(x_2);
x_113 = l_Lean_Name_toString___closed__1;
x_114 = l_Lean_Name_toStringWithSep___main(x_113, x_111);
x_115 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = 0;
x_117 = l_Lean_Format_sbracket___closed__2;
x_118 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_115);
lean_ctor_set_uint8(x_118, sizeof(void*)*2, x_116);
x_119 = l_Lean_Format_sbracket___closed__3;
x_120 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set_uint8(x_120, sizeof(void*)*2, x_116);
x_121 = l_Lean_Format_sbracket___closed__1;
x_122 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
x_123 = lean_format_group(x_122);
x_124 = l_Lean_Format_flatten___main___closed__1;
x_125 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
lean_ctor_set_uint8(x_125, sizeof(void*)*2, x_116);
x_126 = l_Lean_MessageData_formatAux___main(x_1, x_112);
x_127 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set_uint8(x_127, sizeof(void*)*2, x_116);
return x_127;
}
default: 
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_free_object(x_57);
lean_dec(x_59);
x_128 = lean_ctor_get(x_2, 0);
lean_inc(x_128);
lean_dec(x_2);
x_129 = lean_unsigned_to_nat(0u);
x_130 = lean_box(0);
x_131 = l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__3(x_1, x_128, x_128, x_129, x_130);
lean_dec(x_128);
x_132 = lean_unsigned_to_nat(2u);
x_133 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
}
else
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_57, 1);
lean_inc(x_134);
lean_dec(x_57);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_135; 
lean_dec(x_134);
lean_dec(x_1);
x_135 = lean_ctor_get(x_2, 0);
lean_inc(x_135);
lean_dec(x_2);
return x_135;
}
case 1:
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_134);
lean_dec(x_1);
x_136 = lean_ctor_get(x_2, 0);
lean_inc(x_136);
lean_dec(x_2);
x_137 = l_Lean_Syntax_formatStx___main(x_136);
return x_137;
}
case 2:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_1);
x_138 = lean_ctor_get(x_134, 0);
lean_inc(x_138);
lean_dec(x_134);
x_139 = lean_ctor_get(x_2, 0);
lean_inc(x_139);
lean_dec(x_2);
x_140 = l_Lean_MetavarContext_instantiateMVars(x_138, x_139);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec(x_140);
x_142 = lean_expr_dbg_to_string(x_141);
lean_dec(x_141);
x_143 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_143, 0, x_142);
return x_143;
}
case 3:
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_134);
lean_dec(x_1);
x_144 = lean_ctor_get(x_2, 0);
lean_inc(x_144);
lean_dec(x_2);
x_145 = l_Lean_Level_format(x_144);
return x_145;
}
case 4:
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_134);
lean_dec(x_1);
x_146 = lean_ctor_get(x_2, 0);
lean_inc(x_146);
lean_dec(x_2);
x_147 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(x_146);
return x_147;
}
case 5:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_148 = x_1;
} else {
 lean_dec_ref(x_1);
 x_148 = lean_box(0);
}
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_149 = x_134;
} else {
 lean_dec_ref(x_134);
 x_149 = lean_box(0);
}
x_150 = lean_ctor_get(x_2, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_2, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_2, 2);
lean_inc(x_152);
x_153 = lean_ctor_get(x_2, 3);
lean_inc(x_153);
lean_dec(x_2);
if (lean_is_scalar(x_149)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_149;
}
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_152);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_150);
lean_ctor_set(x_155, 1, x_154);
if (lean_is_scalar(x_148)) {
 x_156 = lean_alloc_ctor(1, 1, 0);
} else {
 x_156 = x_148;
}
lean_ctor_set(x_156, 0, x_155);
x_1 = x_156;
x_2 = x_153;
goto _start;
}
case 6:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_134);
x_158 = lean_ctor_get(x_2, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_2, 1);
lean_inc(x_159);
lean_dec(x_2);
x_160 = l_Lean_MessageData_formatAux___main(x_1, x_159);
x_161 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
case 7:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_134);
x_162 = lean_ctor_get(x_2, 0);
lean_inc(x_162);
lean_dec(x_2);
x_163 = l_Lean_MessageData_formatAux___main(x_1, x_162);
x_164 = lean_format_group(x_163);
return x_164;
}
case 8:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; 
lean_dec(x_134);
x_165 = lean_ctor_get(x_2, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_2, 1);
lean_inc(x_166);
lean_dec(x_2);
lean_inc(x_1);
x_167 = l_Lean_MessageData_formatAux___main(x_1, x_165);
x_168 = l_Lean_MessageData_formatAux___main(x_1, x_166);
x_169 = 0;
x_170 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
lean_ctor_set_uint8(x_170, sizeof(void*)*2, x_169);
return x_170;
}
case 9:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_134);
x_171 = lean_ctor_get(x_2, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_2, 1);
lean_inc(x_172);
lean_dec(x_2);
x_173 = l_Lean_Name_toString___closed__1;
x_174 = l_Lean_Name_toStringWithSep___main(x_173, x_171);
x_175 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_175, 0, x_174);
x_176 = 0;
x_177 = l_Lean_Format_sbracket___closed__2;
x_178 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_175);
lean_ctor_set_uint8(x_178, sizeof(void*)*2, x_176);
x_179 = l_Lean_Format_sbracket___closed__3;
x_180 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
lean_ctor_set_uint8(x_180, sizeof(void*)*2, x_176);
x_181 = l_Lean_Format_sbracket___closed__1;
x_182 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_180);
x_183 = lean_format_group(x_182);
x_184 = l_Lean_Format_flatten___main___closed__1;
x_185 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
lean_ctor_set_uint8(x_185, sizeof(void*)*2, x_176);
x_186 = l_Lean_MessageData_formatAux___main(x_1, x_172);
x_187 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
lean_ctor_set_uint8(x_187, sizeof(void*)*2, x_176);
return x_187;
}
default: 
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_134);
x_188 = lean_ctor_get(x_2, 0);
lean_inc(x_188);
lean_dec(x_2);
x_189 = lean_unsigned_to_nat(0u);
x_190 = lean_box(0);
x_191 = l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__3(x_1, x_188, x_188, x_189, x_190);
lean_dec(x_188);
x_192 = lean_unsigned_to_nat(2u);
x_193 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_MessageData_formatAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_formatAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_MessageData_HasAppend(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_MessageData_Lean_HasFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_MessageData_formatAux___main(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_MessageData_coeOfFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_coeOfLevel(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_coeOfExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_coeOfName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_sbracket___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_formatKVMap___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1;
x_7 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_1, x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_2, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_2, x_11);
lean_dec(x_2);
if (x_10 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_14 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_8);
x_16 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_2 = x_12;
x_3 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_8);
x_19 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_18);
x_2 = x_12;
x_3 = x_19;
goto _start;
}
}
}
}
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MessageData_arrayExpr_toMessageData(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_MessageData_coeOfArrayExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_addParenHeuristic___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_MessageData_coeOfArrayExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_coeOfArrayExpr___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_coeOfArrayExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_MessageData_coeOfArrayExpr___closed__2;
x_4 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_MessageData_coeOfArrayExpr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_coeOfArrayExpr(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_fmt___at_Lean_Message_toString___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_MessageData_formatAux___main(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Message_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":\n");
return x_1;
}
}
lean_object* _init_l_Lean_Message_toString___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = lean_string_append(x_1, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Message_toString___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("warning: ");
return x_1;
}
}
lean_object* _init_l_Lean_Message_toString___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Message_toString___closed__3;
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Message_toString___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_EStateM_Result_toString___rarg___closed__2;
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Message_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = l_String_splitAux___main___closed__1;
x_9 = lean_string_dec_eq(x_7, x_8);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_10);
x_12 = l_Lean_Options_empty;
x_13 = l_Lean_Format_pretty(x_11, x_12);
switch (x_6) {
case 0:
{
if (x_9 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_Message_toString___closed__1;
x_15 = lean_string_append(x_7, x_14);
x_16 = lean_string_append(x_8, x_15);
lean_dec(x_15);
x_17 = lean_string_append(x_16, x_13);
lean_dec(x_13);
x_18 = l_Lean_mkErrorStringWithPos(x_2, x_4, x_5, x_17);
lean_dec(x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_19 = l_Lean_Message_toString___closed__2;
x_20 = lean_string_append(x_19, x_13);
lean_dec(x_13);
x_21 = l_Lean_mkErrorStringWithPos(x_2, x_4, x_5, x_20);
lean_dec(x_20);
return x_21;
}
}
case 1:
{
if (x_9 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = l_Lean_Message_toString___closed__1;
x_23 = lean_string_append(x_7, x_22);
x_24 = l_Lean_Message_toString___closed__3;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = lean_string_append(x_25, x_13);
lean_dec(x_13);
x_27 = l_Lean_mkErrorStringWithPos(x_2, x_4, x_5, x_26);
lean_dec(x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_7);
x_28 = l_Lean_Message_toString___closed__4;
x_29 = lean_string_append(x_28, x_13);
lean_dec(x_13);
x_30 = l_Lean_mkErrorStringWithPos(x_2, x_4, x_5, x_29);
lean_dec(x_29);
return x_30;
}
}
default: 
{
if (x_9 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = l_Lean_Message_toString___closed__1;
x_32 = lean_string_append(x_7, x_31);
x_33 = l_EStateM_Result_toString___rarg___closed__2;
x_34 = lean_string_append(x_33, x_32);
lean_dec(x_32);
x_35 = lean_string_append(x_34, x_13);
lean_dec(x_13);
x_36 = l_Lean_mkErrorStringWithPos(x_2, x_4, x_5, x_35);
lean_dec(x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_7);
x_37 = l_Lean_Message_toString___closed__5;
x_38 = lean_string_append(x_37, x_13);
lean_dec(x_13);
x_39 = l_Lean_mkErrorStringWithPos(x_2, x_4, x_5, x_38);
lean_dec(x_38);
return x_39;
}
}
}
}
}
lean_object* _init_l_Lean_Message_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Message_Inhabited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_String_splitAux___main___closed__1;
x_3 = l_Lean_Message_Inhabited___closed__1;
x_4 = 2;
x_5 = l_Lean_MessageData_Inhabited___closed__1;
x_6 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*5, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Message_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Message_Inhabited___closed__2;
return x_1;
}
}
lean_object* _init_l_Lean_Message_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Message_toString), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Message_HasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Message_HasToString___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_MessageLog_empty() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
uint8_t l_Lean_MessageLog_isEmpty(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_List_isEmpty___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_MessageLog_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageLog_isEmpty(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_MessageLog_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_Lean_MessageLog_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_MessageLog_append(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_append___rarg(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_MessageLog_HasAppend___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageLog_append), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_MessageLog_HasAppend() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageLog_HasAppend___closed__1;
return x_1;
}
}
uint8_t l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1(x_1, x_4);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*5);
x_7 = lean_box(x_6);
if (lean_obj_tag(x_7) == 2)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
lean_dec(x_7);
return x_5;
}
}
}
}
uint8_t l_Lean_MessageLog_hasErrors(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = 0;
x_3 = l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageLog_hasErrors(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_MessageLog_toList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_reverse___rarg(x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_ToString(lean_object*);
lean_object* initialize_Init_Lean_Data_Position(lean_object*);
lean_object* initialize_Init_Lean_Syntax(lean_object*);
lean_object* initialize_Init_Lean_MetavarContext(lean_object*);
lean_object* initialize_Init_Lean_Environment(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Util_Message(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Data_Position(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Syntax(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_MetavarContext(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_MessageData_Inhabited___closed__1 = _init_l_Lean_MessageData_Inhabited___closed__1();
lean_mark_persistent(l_Lean_MessageData_Inhabited___closed__1);
l_Lean_MessageData_Inhabited = _init_l_Lean_MessageData_Inhabited();
lean_mark_persistent(l_Lean_MessageData_Inhabited);
l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1 = _init_l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1();
lean_mark_persistent(l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1);
l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2 = _init_l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2();
lean_mark_persistent(l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2);
l_Lean_MessageData_coeOfArrayExpr___closed__1 = _init_l_Lean_MessageData_coeOfArrayExpr___closed__1();
lean_mark_persistent(l_Lean_MessageData_coeOfArrayExpr___closed__1);
l_Lean_MessageData_coeOfArrayExpr___closed__2 = _init_l_Lean_MessageData_coeOfArrayExpr___closed__2();
lean_mark_persistent(l_Lean_MessageData_coeOfArrayExpr___closed__2);
l_Lean_Message_toString___closed__1 = _init_l_Lean_Message_toString___closed__1();
lean_mark_persistent(l_Lean_Message_toString___closed__1);
l_Lean_Message_toString___closed__2 = _init_l_Lean_Message_toString___closed__2();
lean_mark_persistent(l_Lean_Message_toString___closed__2);
l_Lean_Message_toString___closed__3 = _init_l_Lean_Message_toString___closed__3();
lean_mark_persistent(l_Lean_Message_toString___closed__3);
l_Lean_Message_toString___closed__4 = _init_l_Lean_Message_toString___closed__4();
lean_mark_persistent(l_Lean_Message_toString___closed__4);
l_Lean_Message_toString___closed__5 = _init_l_Lean_Message_toString___closed__5();
lean_mark_persistent(l_Lean_Message_toString___closed__5);
l_Lean_Message_Inhabited___closed__1 = _init_l_Lean_Message_Inhabited___closed__1();
lean_mark_persistent(l_Lean_Message_Inhabited___closed__1);
l_Lean_Message_Inhabited___closed__2 = _init_l_Lean_Message_Inhabited___closed__2();
lean_mark_persistent(l_Lean_Message_Inhabited___closed__2);
l_Lean_Message_Inhabited = _init_l_Lean_Message_Inhabited();
lean_mark_persistent(l_Lean_Message_Inhabited);
l_Lean_Message_HasToString___closed__1 = _init_l_Lean_Message_HasToString___closed__1();
lean_mark_persistent(l_Lean_Message_HasToString___closed__1);
l_Lean_Message_HasToString = _init_l_Lean_Message_HasToString();
lean_mark_persistent(l_Lean_Message_HasToString);
l_Lean_MessageLog_empty = _init_l_Lean_MessageLog_empty();
lean_mark_persistent(l_Lean_MessageLog_empty);
l_Lean_MessageLog_Inhabited = _init_l_Lean_MessageLog_Inhabited();
lean_mark_persistent(l_Lean_MessageLog_Inhabited);
l_Lean_MessageLog_HasAppend___closed__1 = _init_l_Lean_MessageLog_HasAppend___closed__1();
lean_mark_persistent(l_Lean_MessageLog_HasAppend___closed__1);
l_Lean_MessageLog_HasAppend = _init_l_Lean_MessageLog_HasAppend();
lean_mark_persistent(l_Lean_MessageLog_HasAppend);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
