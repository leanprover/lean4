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
lean_object* l_PersistentArray_forM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_addParenHeuristic___closed__2;
lean_object* l_Lean_MetavarContext_instantiateMVars(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlM___at_Lean_MessageLog_toList___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Lean_MessageData_ofArray___boxed(lean_object*);
lean_object* l_Lean_Message_toString___closed__3;
lean_object* l_Lean_MessageLog_Inhabited;
lean_object* l_Lean_MessageData_stxMaxDepthOption___closed__2;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_stxMaxDepthOption___closed__4;
lean_object* l_Lean_MessageData_sbracket(lean_object*);
lean_object* l_Lean_MessageData_coeOfSyntax(lean_object*);
extern lean_object* l_Lean_List_format___rarg___closed__1;
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
extern lean_object* l_Lean_verboseOption___closed__3;
extern lean_object* l_Lean_Format_flatten___main___closed__1;
lean_object* l_Lean_MessageData_coeOfLevel(lean_object*);
uint8_t l_PersistentArray_anyMAux___main___at_Lean_MessageLog_hasErrors___spec__2(lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1;
lean_object* l_Lean_MessageData_stxMaxDepthOption___closed__3;
lean_object* l_Lean_MessageData_Lean_HasFormat(lean_object*);
lean_object* l_Lean_MessageData_coeOfFormat(lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_formatAux___main(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
extern lean_object* l_Lean_formatKVMap___closed__1;
lean_object* l_PersistentArray_push___rarg(lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_MessageData_stxMaxDepthOption(lean_object*);
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__2;
lean_object* lean_message_string(lean_object*);
extern lean_object* l_EStateM_Result_toString___rarg___closed__2;
lean_object* l_Lean_MessageLog_toList(lean_object*);
lean_object* l_PersistentArray_foldlMAux___main___at_Lean_MessageLog_toList___spec__2(lean_object*, lean_object*);
lean_object* l_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1___boxed(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Option_format___rarg___closed__1;
lean_object* l_Lean_MessageData_coeOfName(lean_object*);
lean_object* l_Lean_MessageData_coeOfOptExpr(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_Inhabited;
lean_object* l_Lean_fmt___at_Lean_MessageData_formatAux___main___spec__1(lean_object*);
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_stxMaxDepthOption___closed__1;
lean_object* l_Lean_MessageLog_ppOldOption___closed__1;
lean_object* l_PersistentArray_foldlM___at_Lean_MessageLog_toList___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Message_Inhabited;
lean_object* l_Lean_Message_HasToString;
lean_object* l_Lean_MessageLog_ppOldOption___closed__2;
lean_object* l_Lean_MessageLog_HasAppend;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_MessageData_coeOfArrayExpr___closed__2;
lean_object* l_Lean_Message_toString___closed__4;
lean_object* l_PersistentArray_anyMAux___main___at_Lean_MessageLog_hasErrors___spec__2___boxed(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
extern lean_object* l_PersistentArray_empty___closed__3;
lean_object* l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Message_toString___closed__1;
lean_object* l_Lean_Message_toString___closed__2;
extern lean_object* l_Lean_Options_empty;
lean_object* lean_expr_dbg_to_string(lean_object*);
uint8_t l_PersistentArray_isEmpty___rarg(lean_object*);
lean_object* l_Lean_MessageData_getSyntaxMaxDepth___boxed(lean_object*);
lean_object* l_Lean_MessageData_coeOfArrayExpr(lean_object*);
lean_object* l_Lean_MessageLog_ppOldOption(lean_object*);
lean_object* l_Lean_MessageData_formatAux___main___closed__1;
extern lean_object* l_String_Iterator_HasRepr___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList___closed__2;
lean_object* l_Lean_Message_HasToString___closed__1;
lean_object* l_Lean_MessageData_ofList___boxed(lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep___main(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_getNat(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ppOld___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_toList___boxed(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_message_severity(lean_object*);
lean_object* l_Lean_MessageLog_HasAppend___closed__1;
lean_object* l_Lean_MessageData_ofArray(lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__3;
lean_object* l_Lean_MessageLog_forM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_formatAux___main___closed__2;
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l_Lean_MessageData_getSyntaxMaxDepth(lean_object*);
lean_object* l_Lean_fmt___at_Lean_Message_toString___spec__1(lean_object*);
lean_object* l_Lean_MessageLog_empty;
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkErrorStringWithPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_coeOfArrayExpr___closed__1;
extern lean_object* l_Lean_Format_sbracket___closed__1;
lean_object* l_Lean_MessageData_HasAppend(lean_object*, lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList___closed__4;
lean_object* l_Lean_MessageData_bracket(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_forM___boxed(lean_object*);
lean_object* lean_format_group(lean_object*);
lean_object* l_Lean_MessageData_joinSep___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep___main___boxed(lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
lean_object* l_Lean_MessageLog_forM(lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Message_Inhabited___closed__1;
extern lean_object* l_Lean_List_format___rarg___closed__3;
lean_object* l_Lean_Message_Inhabited___closed__2;
lean_object* l_Lean_MessageData_coeOfOptExpr___boxed(lean_object*);
lean_object* l_Lean_MessageData_coeOfOptExpr___closed__1;
lean_object* l_PersistentArray_foldlMAux___main___at_Lean_MessageLog_toList___spec__2___boxed(lean_object*, lean_object*);
uint8_t l_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Message_toString___closed__5;
lean_object* l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_message_pos(lean_object*);
uint8_t l_Lean_MessageLog_isEmpty(lean_object*);
lean_object* l_Lean_MessageData_coeOfExpr(lean_object*);
lean_object* l_Lean_Message_getSeverityEx___boxed(lean_object*);
lean_object* l_Lean_MessageLog_append___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Message_toString(lean_object*);
lean_object* l_Lean_MessageData_formatAux(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_paren(lean_object*);
lean_object* l_Lean_Level_format(lean_object*);
lean_object* l_Lean_MessageData_Inhabited___closed__1;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_stxMaxDepthOption___closed__5;
lean_object* l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_pp_expr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList___closed__1;
lean_object* l_Lean_MessageLog_isEmpty___boxed(lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_coeOfArrayExpr___boxed(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* _init_l_Lean_MessageData_stxMaxDepthOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("syntaxMaxDepth");
return x_1;
}
}
lean_object* _init_l_Lean_MessageData_stxMaxDepthOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MessageData_stxMaxDepthOption___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_MessageData_stxMaxDepthOption___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_MessageData_stxMaxDepthOption___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maximum depth when displaying syntax objects in messages");
return x_1;
}
}
lean_object* _init_l_Lean_MessageData_stxMaxDepthOption___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_MessageData_stxMaxDepthOption___closed__3;
x_2 = l_String_splitAux___main___closed__1;
x_3 = l_Lean_MessageData_stxMaxDepthOption___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_MessageData_stxMaxDepthOption(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_MessageData_stxMaxDepthOption___closed__2;
x_3 = l_Lean_MessageData_stxMaxDepthOption___closed__5;
x_4 = lean_register_option(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_MessageData_getSyntaxMaxDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_MessageData_stxMaxDepthOption___closed__2;
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_KVMap_getNat(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_MessageData_getSyntaxMaxDepth___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_getSyntaxMaxDepth(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_ppOld___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_pp_expr(x_1, x_2, x_3, x_4, x_5);
return x_6;
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
lean_object* _init_l_Lean_MessageData_formatAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ppOld");
return x_1;
}
}
lean_object* _init_l_Lean_MessageData_formatAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MessageData_formatAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_formatStxAux___main(x_5, x_6, x_4);
return x_7;
}
case 2:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_expr_dbg_to_string(x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
case 3:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lean_Level_format(x_11);
return x_12;
}
case 4:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(x_13);
return x_14;
}
case 5:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_15);
x_1 = x_17;
x_2 = x_16;
goto _start;
}
case 6:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
x_21 = l_Lean_MessageData_formatAux___main(x_1, x_20);
x_22 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
case 7:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_dec(x_2);
x_24 = l_Lean_MessageData_formatAux___main(x_1, x_23);
x_25 = lean_format_group(x_24);
return x_25;
}
case 8:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec(x_2);
x_28 = l_Lean_MessageData_formatAux___main(x_1, x_26);
x_29 = l_Lean_MessageData_formatAux___main(x_1, x_27);
x_30 = 0;
x_31 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_30);
return x_31;
}
case 9:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
lean_dec(x_2);
x_34 = l_Lean_Name_toString___closed__1;
x_35 = l_Lean_Name_toStringWithSep___main(x_34, x_32);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = 0;
x_38 = l_Lean_Format_sbracket___closed__2;
x_39 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*2, x_37);
x_40 = l_Lean_Format_sbracket___closed__3;
x_41 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*2, x_37);
x_42 = l_Lean_Format_sbracket___closed__1;
x_43 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_format_group(x_43);
x_45 = l_Lean_Format_flatten___main___closed__1;
x_46 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_37);
x_47 = l_Lean_MessageData_formatAux___main(x_1, x_33);
x_48 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_37);
return x_48;
}
default: 
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_2, 0);
lean_inc(x_49);
lean_dec(x_2);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_box(0);
x_52 = l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__2(x_1, x_49, x_49, x_50, x_51);
lean_dec(x_49);
x_53 = lean_unsigned_to_nat(2u);
x_54 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_55; 
lean_dec(x_1);
x_55 = lean_ctor_get(x_2, 0);
lean_inc(x_55);
lean_dec(x_2);
return x_55;
}
case 1:
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_1);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_1, 0);
x_58 = lean_ctor_get(x_2, 0);
lean_inc(x_58);
lean_dec(x_2);
x_59 = lean_ctor_get(x_57, 3);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_MessageData_getSyntaxMaxDepth(x_59);
lean_dec(x_59);
lean_ctor_set(x_1, 0, x_60);
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Lean_Syntax_formatStxAux___main(x_1, x_61, x_58);
lean_dec(x_1);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
lean_dec(x_1);
x_64 = lean_ctor_get(x_2, 0);
lean_inc(x_64);
lean_dec(x_2);
x_65 = lean_ctor_get(x_63, 3);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_MessageData_getSyntaxMaxDepth(x_65);
lean_dec(x_65);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_unsigned_to_nat(0u);
x_69 = l_Lean_Syntax_formatStxAux___main(x_67, x_68, x_64);
lean_dec(x_67);
return x_69;
}
}
case 2:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_78; 
x_70 = lean_ctor_get(x_1, 0);
lean_inc(x_70);
lean_dec(x_1);
x_71 = lean_ctor_get(x_2, 0);
lean_inc(x_71);
lean_dec(x_2);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_inc(x_72);
x_73 = l_Lean_MetavarContext_instantiateMVars(x_72, x_71);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_ctor_get(x_70, 3);
lean_inc(x_75);
x_76 = l_Lean_MessageData_formatAux___main___closed__2;
x_77 = 1;
x_78 = l_Lean_KVMap_getBool(x_75, x_76, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_75);
lean_dec(x_72);
lean_dec(x_70);
x_79 = lean_expr_dbg_to_string(x_74);
lean_dec(x_74);
x_80 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_70, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_70, 2);
lean_inc(x_82);
lean_dec(x_70);
x_83 = lean_pp_expr(x_81, x_72, x_82, x_75, x_74);
return x_83;
}
}
case 3:
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_1);
x_84 = lean_ctor_get(x_2, 0);
lean_inc(x_84);
lean_dec(x_2);
x_85 = l_Lean_Level_format(x_84);
return x_85;
}
case 4:
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_1);
x_86 = lean_ctor_get(x_2, 0);
lean_inc(x_86);
lean_dec(x_2);
x_87 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(x_86);
return x_87;
}
case 5:
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_1);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_1, 0);
lean_dec(x_89);
x_90 = lean_ctor_get(x_2, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_2, 1);
lean_inc(x_91);
lean_dec(x_2);
lean_ctor_set(x_1, 0, x_90);
x_2 = x_91;
goto _start;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_1);
x_93 = lean_ctor_get(x_2, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_2, 1);
lean_inc(x_94);
lean_dec(x_2);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_93);
x_1 = x_95;
x_2 = x_94;
goto _start;
}
}
case 6:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_2, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_2, 1);
lean_inc(x_98);
lean_dec(x_2);
x_99 = l_Lean_MessageData_formatAux___main(x_1, x_98);
x_100 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
case 7:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_2, 0);
lean_inc(x_101);
lean_dec(x_2);
x_102 = l_Lean_MessageData_formatAux___main(x_1, x_101);
x_103 = lean_format_group(x_102);
return x_103;
}
case 8:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_2, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_2, 1);
lean_inc(x_105);
lean_dec(x_2);
lean_inc(x_1);
x_106 = l_Lean_MessageData_formatAux___main(x_1, x_104);
x_107 = l_Lean_MessageData_formatAux___main(x_1, x_105);
x_108 = 0;
x_109 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*2, x_108);
return x_109;
}
case 9:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_110 = lean_ctor_get(x_2, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_2, 1);
lean_inc(x_111);
lean_dec(x_2);
x_112 = l_Lean_Name_toString___closed__1;
x_113 = l_Lean_Name_toStringWithSep___main(x_112, x_110);
x_114 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = 0;
x_116 = l_Lean_Format_sbracket___closed__2;
x_117 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_114);
lean_ctor_set_uint8(x_117, sizeof(void*)*2, x_115);
x_118 = l_Lean_Format_sbracket___closed__3;
x_119 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set_uint8(x_119, sizeof(void*)*2, x_115);
x_120 = l_Lean_Format_sbracket___closed__1;
x_121 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = lean_format_group(x_121);
x_123 = l_Lean_Format_flatten___main___closed__1;
x_124 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
lean_ctor_set_uint8(x_124, sizeof(void*)*2, x_115);
x_125 = l_Lean_MessageData_formatAux___main(x_1, x_111);
x_126 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set_uint8(x_126, sizeof(void*)*2, x_115);
return x_126;
}
default: 
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_127 = lean_ctor_get(x_2, 0);
lean_inc(x_127);
lean_dec(x_2);
x_128 = lean_unsigned_to_nat(0u);
x_129 = lean_box(0);
x_130 = l_Array_iterateMAux___main___at_Lean_MessageData_formatAux___main___spec__3(x_1, x_127, x_127, x_128, x_129);
lean_dec(x_127);
x_131 = lean_unsigned_to_nat(2u);
x_132 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
return x_132;
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
lean_object* l_Lean_MessageData_coeOfSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_MessageData_coeOfOptExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Option_format___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_coeOfOptExpr(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_coeOfOptExpr___closed__1;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
}
lean_object* l_Lean_MessageData_coeOfOptExpr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_coeOfOptExpr(x_1);
lean_dec(x_1);
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
lean_object* l_Lean_MessageData_bracket(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_string_length(x_1);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
lean_object* l_Lean_MessageData_paren(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Prod_HasRepr___rarg___closed__1;
x_3 = l_Option_HasRepr___rarg___closed__3;
x_4 = l_Lean_MessageData_bracket(x_2, x_1, x_3);
return x_4;
}
}
lean_object* l_Lean_MessageData_sbracket(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_List_repr___rarg___closed__2;
x_3 = l_List_repr___rarg___closed__3;
x_4 = l_Lean_MessageData_bracket(x_2, x_1, x_3);
return x_4;
}
}
lean_object* l_Lean_MessageData_joinSep___main(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = l_Lean_MessageData_Inhabited___closed__1;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_inc(x_6);
x_7 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = l_Lean_MessageData_joinSep___main(x_4, x_2);
x_9 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
}
lean_object* l_Lean_MessageData_joinSep___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_joinSep___main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_MessageData_joinSep(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_joinSep___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_MessageData_joinSep___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_joinSep(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l_Lean_MessageData_ofList___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_List_format___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_MessageData_ofList___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_List_format___rarg___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_MessageData_ofList___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_MessageData_ofList___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MessageData_ofList___closed__2;
x_2 = l_Lean_MessageData_ofList___closed__3;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_MessageData_ofList(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_ofList___closed__1;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_MessageData_ofList___closed__4;
x_4 = l_Lean_MessageData_joinSep___main(x_1, x_3);
x_5 = l_List_repr___rarg___closed__2;
x_6 = l_List_repr___rarg___closed__3;
x_7 = l_Lean_MessageData_bracket(x_5, x_4, x_6);
return x_7;
}
}
}
lean_object* l_Lean_MessageData_ofList___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_ofList(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_ofArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_toList___rarg(x_1);
x_3 = l_Lean_MessageData_ofList(x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_MessageData_ofArray___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_ofArray(x_1);
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
lean_object* lean_message_pos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
return x_2;
}
}
uint8_t lean_message_severity(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Message_getSeverityEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_message_severity(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* lean_message_string(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_2);
x_4 = l_Lean_Options_empty;
x_5 = l_Lean_Format_pretty(x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_MessageLog_empty() {
_start:
{
lean_object* x_1; 
x_1 = l_PersistentArray_empty___closed__3;
return x_1;
}
}
uint8_t l_Lean_MessageLog_isEmpty(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_PersistentArray_isEmpty___rarg(x_1);
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
x_1 = l_PersistentArray_empty___closed__3;
return x_1;
}
}
lean_object* l_Lean_MessageLog_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_push___rarg(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_MessageLog_append(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_append___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_MessageLog_append___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageLog_append(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_MessageLog_HasAppend___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageLog_append___boxed), 2, 0);
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
uint8_t l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = l_PersistentArray_anyMAux___main___at_Lean_MessageLog_hasErrors___spec__2(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_4);
return x_8;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*5);
lean_dec(x_7);
x_9 = lean_box(x_8);
if (lean_obj_tag(x_9) == 2)
{
uint8_t x_10; 
lean_dec(x_4);
x_10 = 1;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_4 = x_12;
goto _start;
}
}
}
}
uint8_t l_PersistentArray_anyMAux___main___at_Lean_MessageLog_hasErrors___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__3(x_2, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__4(x_6, x_6, x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*5);
lean_dec(x_7);
x_9 = lean_box(x_8);
if (lean_obj_tag(x_9) == 2)
{
uint8_t x_10; 
lean_dec(x_4);
x_10 = 1;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_4 = x_12;
goto _start;
}
}
}
}
uint8_t l_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_PersistentArray_anyMAux___main___at_Lean_MessageLog_hasErrors___spec__2(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__5(x_1, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
else
{
return x_3;
}
}
}
uint8_t l_Lean_MessageLog_hasErrors(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_1);
return x_2;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_PersistentArray_anyMAux___main___at_Lean_MessageLog_hasErrors___spec__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_PersistentArray_anyMAux___main___at_Lean_MessageLog_hasErrors___spec__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_MessageLog_hasErrors___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
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
lean_object* l_Lean_MessageLog_forM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentArray_forM___rarg(x_1, lean_box(0), x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_MessageLog_forM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageLog_forM___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_MessageLog_forM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageLog_forM(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_PersistentArray_foldlMAux___main___at_Lean_MessageLog_toList___spec__2(x_7, x_4);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_PersistentArray_foldlMAux___main___at_Lean_MessageLog_toList___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__3(x_3, x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__4(x_6, x_6, x_7, x_2);
return x_8;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_PersistentArray_foldlM___at_Lean_MessageLog_toList___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_PersistentArray_foldlMAux___main___at_Lean_MessageLog_toList___spec__2(x_3, x_2);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__5(x_1, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Lean_MessageLog_toList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_PersistentArray_foldlM___at_Lean_MessageLog_toList___spec__1(x_1, x_2);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_PersistentArray_foldlMAux___main___at_Lean_MessageLog_toList___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_foldlMAux___main___at_Lean_MessageLog_toList___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_MessageLog_toList___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_PersistentArray_foldlM___at_Lean_MessageLog_toList___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_foldlM___at_Lean_MessageLog_toList___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_MessageLog_toList___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageLog_toList(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_MessageLog_ppOldOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("disable/enable old pretty printer");
return x_1;
}
}
lean_object* _init_l_Lean_MessageLog_ppOldOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_verboseOption___closed__3;
x_2 = l_String_splitAux___main___closed__1;
x_3 = l_Lean_MessageLog_ppOldOption___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_MessageLog_ppOldOption(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_MessageData_formatAux___main___closed__2;
x_3 = l_Lean_MessageLog_ppOldOption___closed__2;
x_4 = lean_register_option(x_2, x_3, x_1);
return x_4;
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
l_Lean_MessageData_stxMaxDepthOption___closed__1 = _init_l_Lean_MessageData_stxMaxDepthOption___closed__1();
lean_mark_persistent(l_Lean_MessageData_stxMaxDepthOption___closed__1);
l_Lean_MessageData_stxMaxDepthOption___closed__2 = _init_l_Lean_MessageData_stxMaxDepthOption___closed__2();
lean_mark_persistent(l_Lean_MessageData_stxMaxDepthOption___closed__2);
l_Lean_MessageData_stxMaxDepthOption___closed__3 = _init_l_Lean_MessageData_stxMaxDepthOption___closed__3();
lean_mark_persistent(l_Lean_MessageData_stxMaxDepthOption___closed__3);
l_Lean_MessageData_stxMaxDepthOption___closed__4 = _init_l_Lean_MessageData_stxMaxDepthOption___closed__4();
lean_mark_persistent(l_Lean_MessageData_stxMaxDepthOption___closed__4);
l_Lean_MessageData_stxMaxDepthOption___closed__5 = _init_l_Lean_MessageData_stxMaxDepthOption___closed__5();
lean_mark_persistent(l_Lean_MessageData_stxMaxDepthOption___closed__5);
res = l_Lean_MessageData_stxMaxDepthOption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_MessageData_formatAux___main___closed__1 = _init_l_Lean_MessageData_formatAux___main___closed__1();
lean_mark_persistent(l_Lean_MessageData_formatAux___main___closed__1);
l_Lean_MessageData_formatAux___main___closed__2 = _init_l_Lean_MessageData_formatAux___main___closed__2();
lean_mark_persistent(l_Lean_MessageData_formatAux___main___closed__2);
l_Lean_MessageData_coeOfOptExpr___closed__1 = _init_l_Lean_MessageData_coeOfOptExpr___closed__1();
lean_mark_persistent(l_Lean_MessageData_coeOfOptExpr___closed__1);
l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1 = _init_l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1();
lean_mark_persistent(l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1);
l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2 = _init_l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2();
lean_mark_persistent(l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2);
l_Lean_MessageData_coeOfArrayExpr___closed__1 = _init_l_Lean_MessageData_coeOfArrayExpr___closed__1();
lean_mark_persistent(l_Lean_MessageData_coeOfArrayExpr___closed__1);
l_Lean_MessageData_coeOfArrayExpr___closed__2 = _init_l_Lean_MessageData_coeOfArrayExpr___closed__2();
lean_mark_persistent(l_Lean_MessageData_coeOfArrayExpr___closed__2);
l_Lean_MessageData_ofList___closed__1 = _init_l_Lean_MessageData_ofList___closed__1();
lean_mark_persistent(l_Lean_MessageData_ofList___closed__1);
l_Lean_MessageData_ofList___closed__2 = _init_l_Lean_MessageData_ofList___closed__2();
lean_mark_persistent(l_Lean_MessageData_ofList___closed__2);
l_Lean_MessageData_ofList___closed__3 = _init_l_Lean_MessageData_ofList___closed__3();
lean_mark_persistent(l_Lean_MessageData_ofList___closed__3);
l_Lean_MessageData_ofList___closed__4 = _init_l_Lean_MessageData_ofList___closed__4();
lean_mark_persistent(l_Lean_MessageData_ofList___closed__4);
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
l_Lean_MessageLog_ppOldOption___closed__1 = _init_l_Lean_MessageLog_ppOldOption___closed__1();
lean_mark_persistent(l_Lean_MessageLog_ppOldOption___closed__1);
l_Lean_MessageLog_ppOldOption___closed__2 = _init_l_Lean_MessageLog_ppOldOption___closed__2();
lean_mark_persistent(l_Lean_MessageLog_ppOldOption___closed__2);
res = l_Lean_MessageLog_ppOldOption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
