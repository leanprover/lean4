// Lean compiler output
// Module: Init.Lean.Parser.Module
// Imports: Init.Lean.Message Init.Lean.Parser.Command
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
lean_object* l_Lean_Parser_mkParserContextCore(lean_object*, lean_object*, lean_object*);
extern uint8_t l_String_anyAux___main___at_String_all___spec__1___closed__1;
lean_object* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__7;
extern lean_object* l_Lean_Parser_manyAux___main___closed__1;
lean_object* l_Lean_Parser_Module_import___elambda__1___rarg___closed__7;
lean_object* l_IO_print___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__4(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___closed__8;
lean_object* lean_io_timeit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___closed__4;
extern lean_object* l_Lean_nullKind;
lean_object* l_IO_readTextFile___at_Lean_Parser_parseFile___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_io_prim_put_str(lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ModuleParserState_inhabited___closed__1;
lean_object* l_Lean_Parser_testModuleParser___closed__2;
extern uint8_t l_String_Iterator_extract___closed__1;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Module_2__mkEOI___closed__2;
lean_object* l___private_Init_Lean_Parser_Module_2__mkEOI___closed__1;
lean_object* l_Lean_Parser_Module_prelude;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_Parser_Module_import;
lean_object* l_Lean_Parser_ParserAttribute_runParser(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_header___closed__4;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Parser_Module_prelude___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_Module_import___elambda__1___rarg___closed__5;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_isExitCommand___boxed(lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l___private_Init_Lean_Parser_Module_4__testModuleParserAux___main(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseFile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1(uint8_t, lean_object*);
lean_object* l_Lean_Parser_testModuleParser___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_ident___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Module_2__mkEOI(lean_object*);
lean_object* l_Lean_Parser_Module_prelude___closed__4;
lean_object* l_IO_readTextFile___at_Lean_Parser_parseFile___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_header___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___elambda__1___rarg___closed__6;
lean_object* l_Lean_Parser_Module_header___elambda__1___closed__1;
lean_object* l___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initCacheForInput(lean_object*);
extern lean_object* l_Lean_Parser_Trie_HasEmptyc___closed__1;
lean_object* l_Lean_Syntax_updateLeading___rarg(lean_object*);
extern lean_object* l_Lean_mkOptionalNode___rarg___closed__1;
lean_object* l_Lean_Parser_Module_header___elambda__1___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_testModuleParser___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___elambda__1___rarg___closed__3;
lean_object* l_Lean_Parser_parseFileAux___main___closed__1;
lean_object* l_Lean_Parser_Module_header___closed__2;
lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Module_4__testModuleParserAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object*);
lean_object* l_Lean_Parser_Module_header___closed__1;
lean_object* l_Lean_Parser_whitespace___main(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__5;
lean_object* l_Lean_Parser_optionaInfo(lean_object*);
lean_object* l___private_Init_Lean_Parser_Module_1__mkErrorMessage(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*, lean_object*);
lean_object* l_Lean_Parser_testModuleParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseCommand___main(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_Parser_Module_import___elambda__1___rarg___closed__2;
lean_object* l_IO_print___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_header___closed__6;
lean_object* l_Lean_Parser_testModuleParser___closed__1;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_IO_println___rarg___closed__1;
lean_object* l_Lean_Parser_Module_import___elambda__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Parser_Module_import___elambda__1___rarg___closed__8;
lean_object* l_Lean_Parser_Module_import___closed__1;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___elambda__1___rarg___closed__1;
lean_object* l_Lean_Parser_parseFileAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___elambda__1___rarg___closed__4;
lean_object* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__2;
lean_object* l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(lean_object*);
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4;
lean_object* l_Lean_Parser_Module_header;
lean_object* l_List_forM___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_prelude___elambda__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_exit___elambda__1___rarg___closed__2;
lean_object* l_Lean_Parser_Module_import___closed__6;
lean_object* l_Lean_Parser_Module_header___closed__5;
lean_object* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__8;
lean_object* l_Lean_Parser_Module_import___elambda__1___rarg___closed__9;
lean_object* l_Lean_Parser_Module_import___closed__2;
lean_object* l_Lean_Parser_ModuleParserState_inhabited;
lean_object* l_IO_println___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__1(lean_object*, lean_object*);
extern lean_object* l_Substring_drop___closed__2;
lean_object* l_Lean_Parser_Error_toString(lean_object*);
lean_object* l_Lean_Parser_Module_import___elambda__1___rarg___closed__11;
uint8_t l_Lean_Parser_isExitCommand(lean_object*);
lean_object* l_Lean_Parser_Module_updateTokens(lean_object*);
lean_object* l_Lean_Parser_Module_prelude___closed__3;
lean_object* l_Lean_Parser_Module_import___closed__3;
lean_object* l_Lean_Parser_Module_prelude___closed__1;
lean_object* l_Lean_Parser_Module_import___closed__7;
lean_object* l___private_Init_Lean_Parser_Module_4__testModuleParserAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolInfo(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_commandParserAttribute;
lean_object* l_Lean_Parser_Module_prelude___closed__2;
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_header___closed__3;
lean_object* l_String_trim(lean_object*);
lean_object* l___private_Init_Lean_Parser_Module_3__consumeInput(lean_object*, lean_object*);
lean_object* lean_io_prim_read_text_file(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___closed__5;
lean_object* l_Lean_Parser_Module_prelude___elambda__1(lean_object*);
lean_object* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__3;
lean_object* l_IO_println___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__3(lean_object*, lean_object*);
uint8_t l_Lean_Parser_isEOI(lean_object*);
lean_object* l_Lean_Parser_Module_import___elambda__1___rarg___closed__12;
lean_object* l_Lean_Parser_identFn___rarg(lean_object*, lean_object*);
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Syntax_formatStx___main___rarg(lean_object*);
lean_object* l___private_Init_Lean_Parser_Module_1__mkErrorMessage___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*);
lean_object* l_EStateM_pure___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Message_toString(lean_object*);
lean_object* l_Lean_Parser_parseFileAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__1;
lean_object* lean_test_module_parser(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_parseCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__6;
lean_object* l_Lean_Parser_Module_import___elambda__1(lean_object*);
lean_object* l_Lean_Parser_isEOI___boxed(lean_object*);
lean_object* l_Lean_Parser_Module_header___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___elambda__1___rarg___closed__10;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Module");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_2 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("prelude");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__6;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_Module_prelude___elambda__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = l_Lean_Parser_tokenFn(x_1, x_2);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 2)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__5;
x_13 = lean_string_dec_eq(x_11, x_12);
lean_dec(x_11);
x_14 = 1;
x_15 = l_Bool_DecidableEq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__8;
x_17 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_16, x_5);
x_18 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4;
x_19 = l_Lean_Parser_ParserState_mkNode(x_17, x_18, x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
x_20 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4;
x_21 = l_Lean_Parser_ParserState_mkNode(x_6, x_20, x_4);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_10);
x_22 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__8;
x_23 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_22, x_5);
x_24 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4;
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_24, x_4);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__8;
x_27 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_26, x_5);
x_28 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4;
x_29 = l_Lean_Parser_ParserState_mkNode(x_27, x_28, x_4);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_7);
x_30 = l_String_Iterator_extract___closed__1;
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_6, 0);
lean_inc(x_31);
x_32 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_31);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 2)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__5;
x_35 = lean_string_dec_eq(x_33, x_34);
lean_dec(x_33);
x_36 = 1;
x_37 = l_Bool_DecidableEq(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__8;
x_39 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_38, x_5);
x_40 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4;
x_41 = l_Lean_Parser_ParserState_mkNode(x_39, x_40, x_4);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_5);
x_42 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4;
x_43 = l_Lean_Parser_ParserState_mkNode(x_6, x_42, x_4);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_32);
x_44 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__8;
x_45 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_44, x_5);
x_46 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4;
x_47 = l_Lean_Parser_ParserState_mkNode(x_45, x_46, x_4);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__8;
x_49 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_48, x_5);
x_50 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4;
x_51 = l_Lean_Parser_ParserState_mkNode(x_49, x_50, x_4);
return x_51;
}
}
}
}
lean_object* l_Lean_Parser_Module_prelude___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude___elambda__1___rarg), 2, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__5;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4;
x_2 = l_Lean_Parser_Module_prelude___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude___elambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___closed__2;
x_2 = l_Lean_Parser_Module_prelude___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Module_prelude___closed__4;
return x_1;
}
}
lean_object* l_Lean_Parser_Module_prelude___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Module_prelude___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("import");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("import ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("runtime");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__7;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__10;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_Module_import___elambda__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_20; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_124 = lean_ctor_get(x_2, 1);
lean_inc(x_124);
lean_inc(x_1);
x_125 = l_Lean_Parser_tokenFn(x_1, x_2);
x_126 = lean_ctor_get(x_125, 3);
lean_inc(x_126);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_127; 
x_127 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_125, 0);
lean_inc(x_128);
x_129 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_128);
lean_dec(x_128);
if (lean_obj_tag(x_129) == 2)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; 
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_131 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__4;
x_132 = lean_string_dec_eq(x_130, x_131);
lean_dec(x_130);
x_133 = 1;
x_134 = l_Bool_DecidableEq(x_132, x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__12;
x_136 = l_Lean_Parser_ParserState_mkErrorsAt(x_125, x_135, x_124);
x_20 = x_136;
goto block_123;
}
else
{
lean_dec(x_124);
x_20 = x_125;
goto block_123;
}
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_129);
x_137 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__12;
x_138 = l_Lean_Parser_ParserState_mkErrorsAt(x_125, x_137, x_124);
x_20 = x_138;
goto block_123;
}
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__12;
x_140 = l_Lean_Parser_ParserState_mkErrorsAt(x_125, x_139, x_124);
x_20 = x_140;
goto block_123;
}
}
else
{
uint8_t x_141; 
lean_dec(x_126);
x_141 = l_String_Iterator_extract___closed__1;
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_125, 0);
lean_inc(x_142);
x_143 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_142);
lean_dec(x_142);
if (lean_obj_tag(x_143) == 2)
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; uint8_t x_147; uint8_t x_148; 
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
lean_dec(x_143);
x_145 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__4;
x_146 = lean_string_dec_eq(x_144, x_145);
lean_dec(x_144);
x_147 = 1;
x_148 = l_Bool_DecidableEq(x_146, x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__12;
x_150 = l_Lean_Parser_ParserState_mkErrorsAt(x_125, x_149, x_124);
x_20 = x_150;
goto block_123;
}
else
{
lean_dec(x_124);
x_20 = x_125;
goto block_123;
}
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_143);
x_151 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__12;
x_152 = l_Lean_Parser_ParserState_mkErrorsAt(x_125, x_151, x_124);
x_20 = x_152;
goto block_123;
}
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__12;
x_154 = l_Lean_Parser_ParserState_mkErrorsAt(x_125, x_153, x_124);
x_20 = x_154;
goto block_123;
}
}
block_19:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Parser_identFn___rarg(x_1, x_5);
x_9 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__2;
x_10 = l_Lean_Parser_ParserState_mkNode(x_8, x_9, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__2;
x_12 = l_Lean_Parser_ParserState_mkNode(x_5, x_11, x_4);
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = l_String_Iterator_extract___closed__1;
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Parser_identFn___rarg(x_1, x_5);
x_15 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__2;
x_16 = l_Lean_Parser_ParserState_mkNode(x_14, x_15, x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_5, x_17, x_4);
return x_18;
}
}
}
block_123:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_43; lean_object* x_44; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_array_get_size(x_23);
lean_dec(x_23);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_1);
x_43 = l_Lean_Parser_tokenFn(x_1, x_20);
x_44 = lean_ctor_get(x_43, 3);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_45);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 2)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__6;
x_49 = lean_string_dec_eq(x_47, x_48);
lean_dec(x_47);
x_50 = 1;
x_51 = l_Bool_DecidableEq(x_49, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__9;
lean_inc(x_25);
x_53 = l_Lean_Parser_ParserState_mkErrorsAt(x_43, x_52, x_25);
x_26 = x_53;
goto block_42;
}
else
{
x_26 = x_43;
goto block_42;
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_46);
x_54 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__9;
lean_inc(x_25);
x_55 = l_Lean_Parser_ParserState_mkErrorsAt(x_43, x_54, x_25);
x_26 = x_55;
goto block_42;
}
}
else
{
uint8_t x_56; 
lean_dec(x_44);
x_56 = l_String_Iterator_extract___closed__1;
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_43, 0);
lean_inc(x_57);
x_58 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_57);
lean_dec(x_57);
if (lean_obj_tag(x_58) == 2)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__6;
x_61 = lean_string_dec_eq(x_59, x_60);
lean_dec(x_59);
x_62 = 1;
x_63 = l_Bool_DecidableEq(x_61, x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__9;
lean_inc(x_25);
x_65 = l_Lean_Parser_ParserState_mkErrorsAt(x_43, x_64, x_25);
x_26 = x_65;
goto block_42;
}
else
{
x_26 = x_43;
goto block_42;
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_58);
x_66 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__9;
lean_inc(x_25);
x_67 = l_Lean_Parser_ParserState_mkErrorsAt(x_43, x_66, x_25);
x_26 = x_67;
goto block_42;
}
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__9;
lean_inc(x_25);
x_69 = l_Lean_Parser_ParserState_mkErrorsAt(x_43, x_68, x_25);
x_26 = x_69;
goto block_42;
}
}
block_42:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 3);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
if (x_22 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
x_28 = l_Lean_nullKind;
x_29 = l_Lean_Parser_ParserState_mkNode(x_26, x_28, x_24);
x_5 = x_29;
goto block_19;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Lean_Parser_ParserState_restore(x_26, x_24, x_25);
x_31 = l_Lean_nullKind;
x_32 = l_Lean_Parser_ParserState_mkNode(x_30, x_31, x_24);
x_5 = x_32;
goto block_19;
}
}
else
{
lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; 
lean_dec(x_27);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
x_34 = lean_nat_dec_eq(x_33, x_25);
lean_dec(x_33);
x_35 = 1;
x_36 = l_Bool_DecidableEq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_25);
x_37 = l_Lean_nullKind;
x_38 = l_Lean_Parser_ParserState_mkNode(x_26, x_37, x_24);
x_5 = x_38;
goto block_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = l_Lean_Parser_ParserState_restore(x_26, x_24, x_25);
x_40 = l_Lean_nullKind;
x_41 = l_Lean_Parser_ParserState_mkNode(x_39, x_40, x_24);
x_5 = x_41;
goto block_19;
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_1);
x_70 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__2;
x_71 = l_Lean_Parser_ParserState_mkNode(x_20, x_70, x_4);
return x_71;
}
}
else
{
uint8_t x_72; 
lean_dec(x_21);
x_72 = l_String_Iterator_extract___closed__1;
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_94; lean_object* x_95; 
x_73 = lean_ctor_get(x_20, 0);
lean_inc(x_73);
x_74 = lean_array_get_size(x_73);
lean_dec(x_73);
x_75 = lean_ctor_get(x_20, 1);
lean_inc(x_75);
lean_inc(x_1);
x_94 = l_Lean_Parser_tokenFn(x_1, x_20);
x_95 = lean_ctor_get(x_94, 3);
lean_inc(x_95);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
x_96 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_94, 0);
lean_inc(x_97);
x_98 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_97);
lean_dec(x_97);
if (lean_obj_tag(x_98) == 2)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__6;
x_101 = lean_string_dec_eq(x_99, x_100);
lean_dec(x_99);
x_102 = 1;
x_103 = l_Bool_DecidableEq(x_101, x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__9;
lean_inc(x_75);
x_105 = l_Lean_Parser_ParserState_mkErrorsAt(x_94, x_104, x_75);
x_76 = x_105;
goto block_93;
}
else
{
x_76 = x_94;
goto block_93;
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_98);
x_106 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__9;
lean_inc(x_75);
x_107 = l_Lean_Parser_ParserState_mkErrorsAt(x_94, x_106, x_75);
x_76 = x_107;
goto block_93;
}
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__9;
lean_inc(x_75);
x_109 = l_Lean_Parser_ParserState_mkErrorsAt(x_94, x_108, x_75);
x_76 = x_109;
goto block_93;
}
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_95);
x_110 = lean_ctor_get(x_94, 0);
lean_inc(x_110);
x_111 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_110);
lean_dec(x_110);
if (lean_obj_tag(x_111) == 2)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__6;
x_114 = lean_string_dec_eq(x_112, x_113);
lean_dec(x_112);
x_115 = 1;
x_116 = l_Bool_DecidableEq(x_114, x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__9;
lean_inc(x_75);
x_118 = l_Lean_Parser_ParserState_mkErrorsAt(x_94, x_117, x_75);
x_76 = x_118;
goto block_93;
}
else
{
x_76 = x_94;
goto block_93;
}
}
else
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_111);
x_119 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__9;
lean_inc(x_75);
x_120 = l_Lean_Parser_ParserState_mkErrorsAt(x_94, x_119, x_75);
x_76 = x_120;
goto block_93;
}
}
block_93:
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_76, 3);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_75);
x_79 = l_Lean_nullKind;
x_80 = l_Lean_Parser_ParserState_mkNode(x_76, x_79, x_74);
x_5 = x_80;
goto block_19;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = l_Lean_Parser_ParserState_restore(x_76, x_74, x_75);
x_82 = l_Lean_nullKind;
x_83 = l_Lean_Parser_ParserState_mkNode(x_81, x_82, x_74);
x_5 = x_83;
goto block_19;
}
}
else
{
lean_object* x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; 
lean_dec(x_77);
x_84 = lean_ctor_get(x_76, 1);
lean_inc(x_84);
x_85 = lean_nat_dec_eq(x_84, x_75);
lean_dec(x_84);
x_86 = 1;
x_87 = l_Bool_DecidableEq(x_85, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_75);
x_88 = l_Lean_nullKind;
x_89 = l_Lean_Parser_ParserState_mkNode(x_76, x_88, x_74);
x_5 = x_89;
goto block_19;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = l_Lean_Parser_ParserState_restore(x_76, x_74, x_75);
x_91 = l_Lean_nullKind;
x_92 = l_Lean_Parser_ParserState_mkNode(x_90, x_91, x_74);
x_5 = x_92;
goto block_19;
}
}
}
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_1);
x_121 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__2;
x_122 = l_Lean_Parser_ParserState_mkNode(x_20, x_121, x_4);
return x_122;
}
}
}
}
}
lean_object* l_Lean_Parser_Module_import___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Module_import___elambda__1___rarg), 2, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Module_import___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__4;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__6;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_import___closed__2;
x_2 = l_Lean_Parser_optionaInfo(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Module_import___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___closed__3;
x_2 = l_Lean_Parser_ident___closed__1;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___closed__1;
x_2 = l_Lean_Parser_Module_import___closed__4;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Module_import___closed__5;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_import___elambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Module_import___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___closed__6;
x_2 = l_Lean_Parser_Module_import___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Module_import___closed__8;
return x_1;
}
}
lean_object* l_Lean_Parser_Module_import___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Module_import___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_array_get_size(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_3);
x_8 = l_Lean_Parser_Module_import___elambda__1___rarg(x_3, x_4);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; 
lean_dec(x_6);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
x_12 = lean_nat_dec_eq(x_7, x_11);
lean_dec(x_11);
lean_dec(x_7);
x_13 = 1;
x_14 = l_Bool_DecidableEq(x_12, x_13);
if (x_14 == 0)
{
x_4 = x_8;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
x_16 = l_Lean_Parser_manyAux___main___closed__1;
x_17 = l_Lean_Parser_ParserState_mkUnexpectedError(x_8, x_16);
return x_17;
}
}
else
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; 
lean_dec(x_3);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
x_19 = lean_nat_dec_eq(x_7, x_18);
lean_dec(x_18);
x_20 = 1;
x_21 = l_Bool_DecidableEq(x_19, x_20);
if (x_21 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_22; 
x_22 = l_Lean_Parser_ParserState_restore(x_8, x_6, x_7);
lean_dec(x_6);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_9);
x_23 = l_String_Iterator_extract___closed__1;
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; 
lean_dec(x_6);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
x_25 = lean_nat_dec_eq(x_7, x_24);
lean_dec(x_24);
lean_dec(x_7);
x_26 = 1;
x_27 = l_Bool_DecidableEq(x_25, x_26);
if (x_27 == 0)
{
x_4 = x_8;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_3);
x_29 = l_Lean_Parser_manyAux___main___closed__1;
x_30 = l_Lean_Parser_ParserState_mkUnexpectedError(x_8, x_29);
return x_30;
}
}
else
{
lean_object* x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; 
lean_dec(x_3);
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
x_32 = lean_nat_dec_eq(x_7, x_31);
lean_dec(x_31);
x_33 = 1;
x_34 = l_Bool_DecidableEq(x_32, x_33);
if (x_34 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_35; 
x_35 = l_Lean_Parser_ParserState_restore(x_8, x_6, x_7);
lean_dec(x_6);
return x_35;
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Module_header___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("header");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Module_header___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Module_header___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Module_header___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
lean_inc(x_2);
x_32 = l_Lean_Parser_Module_prelude___elambda__1___rarg(x_2, x_3);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
x_35 = l_Lean_nullKind;
lean_inc(x_5);
x_36 = l_Lean_Parser_ParserState_mkNode(x_32, x_35, x_5);
x_6 = x_36;
goto block_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = l_Lean_Parser_ParserState_restore(x_32, x_5, x_31);
x_38 = l_Lean_nullKind;
lean_inc(x_5);
x_39 = l_Lean_Parser_ParserState_mkNode(x_37, x_38, x_5);
x_6 = x_39;
goto block_30;
}
}
else
{
lean_object* x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; 
lean_dec(x_33);
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
x_41 = lean_nat_dec_eq(x_40, x_31);
lean_dec(x_40);
x_42 = 1;
x_43 = l_Bool_DecidableEq(x_41, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
x_44 = l_Lean_nullKind;
lean_inc(x_5);
x_45 = l_Lean_Parser_ParserState_mkNode(x_32, x_44, x_5);
x_6 = x_45;
goto block_30;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = l_Lean_Parser_ParserState_restore(x_32, x_5, x_31);
x_47 = l_Lean_nullKind;
lean_inc(x_5);
x_48 = l_Lean_Parser_ParserState_mkNode(x_46, x_47, x_5);
x_6 = x_48;
goto block_30;
}
}
block_30:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_array_get_size(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_11, x_1, x_2, x_6);
x_13 = l_Lean_nullKind;
x_14 = l_Lean_Parser_ParserState_mkNode(x_12, x_13, x_10);
x_15 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_16 = l_Lean_Parser_ParserState_mkNode(x_14, x_15, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_17 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_6, x_17, x_5);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_7);
x_19 = l_String_Iterator_extract___closed__1;
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_6, 0);
lean_inc(x_20);
x_21 = lean_array_get_size(x_20);
lean_dec(x_20);
x_22 = 0;
x_23 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_22, x_1, x_2, x_6);
x_24 = l_Lean_nullKind;
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_24, x_21);
x_26 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_27 = l_Lean_Parser_ParserState_mkNode(x_25, x_26, x_5);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
x_28 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_29 = l_Lean_Parser_ParserState_mkNode(x_6, x_28, x_5);
return x_29;
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Module_header___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_optionaInfo(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_header___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_noFirstTokenInfo(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_header___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header___closed__1;
x_2 = l_Lean_Parser_Module_header___closed__2;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_header___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_2 = l_Lean_Parser_Module_header___closed__3;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_header___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_header___elambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Module_header___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header___closed__4;
x_2 = l_Lean_Parser_Module_header___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_header() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Module_header___closed__6;
return x_1;
}
}
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_5, x_2, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Parser_Module_header___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Module_header___elambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_Module_updateTokens(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 3);
x_6 = l_Lean_Parser_Module_header;
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_1(x_8, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_9);
x_10 = l_Lean_Parser_Trie_HasEmptyc___closed__1;
lean_ctor_set(x_3, 3, x_10);
return x_1;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_ctor_set(x_3, 3, x_11);
return x_1;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_ctor_get(x_3, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_16 = l_Lean_Parser_Module_header;
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_apply_1(x_18, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_19);
x_20 = l_Lean_Parser_Trie_HasEmptyc___closed__1;
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_14);
lean_ctor_set(x_21, 3, x_20);
lean_ctor_set(x_1, 0, x_21);
return x_1;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_13);
lean_ctor_set(x_23, 2, x_14);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 3);
lean_inc(x_29);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 lean_ctor_release(x_24, 3);
 x_30 = x_24;
} else {
 lean_dec_ref(x_24);
 x_30 = lean_box(0);
}
x_31 = l_Lean_Parser_Module_header;
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_apply_1(x_33, x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_34);
x_35 = l_Lean_Parser_Trie_HasEmptyc___closed__1;
if (lean_is_scalar(x_30)) {
 x_36 = lean_alloc_ctor(0, 4, 0);
} else {
 x_36 = x_30;
}
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_27);
lean_ctor_set(x_36, 2, x_28);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_25);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
lean_dec(x_34);
if (lean_is_scalar(x_30)) {
 x_39 = lean_alloc_ctor(0, 4, 0);
} else {
 x_39 = x_30;
}
lean_ctor_set(x_39, 0, x_26);
lean_ctor_set(x_39, 1, x_27);
lean_ctor_set(x_39, 2, x_28);
lean_ctor_set(x_39, 3, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_25);
return x_40;
}
}
}
}
lean_object* _init_l_Lean_Parser_ModuleParserState_inhabited___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_ModuleParserState_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_ModuleParserState_inhabited___closed__1;
return x_1;
}
}
lean_object* l___private_Init_Lean_Parser_Module_1__mkErrorMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 2);
x_6 = l_Lean_FileMap_toPosition(x_5, x_2);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_3);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = 2;
x_12 = l_String_splitAux___main___closed__1;
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_6);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set(x_13, 3, x_12);
lean_ctor_set(x_13, 4, x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*5, x_11);
return x_13;
}
}
lean_object* l___private_Init_Lean_Parser_Module_1__mkErrorMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Parser_Module_1__mkErrorMessage(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_parseHeader(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
x_4 = l_Lean_Parser_Module_updateTokens(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Parser_mkParserState(x_6);
lean_dec(x_6);
x_8 = l_Lean_Parser_whitespace___main(x_4, x_7);
x_9 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_10 = l_Lean_Parser_Module_header___elambda__1(x_9, x_4, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_11);
lean_dec(x_11);
x_13 = lean_ctor_get(x_10, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = 0;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = l_Lean_Parser_Error_toString(x_20);
x_23 = l___private_Init_Lean_Parser_Module_1__mkErrorMessage(x_4, x_21, x_22);
lean_dec(x_4);
x_24 = 1;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
lean_object* _init_l___private_Init_Lean_Parser_Module_2__mkEOI___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("eoi");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Parser_Module_2__mkEOI___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__2;
x_2 = l___private_Init_Lean_Parser_Module_2__mkEOI___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Parser_Module_2__mkEOI(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = l_Substring_drop___closed__2;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_String_splitAux___main___closed__1;
x_6 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_mkOptionalNode___rarg___closed__1;
x_8 = lean_array_push(x_7, x_6);
x_9 = l___private_Init_Lean_Parser_Module_2__mkEOI___closed__2;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
uint8_t l_Lean_Parser_isEOI(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l___private_Init_Lean_Parser_Module_2__mkEOI___closed__2;
x_3 = l_Lean_Syntax_isOfKind___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_isEOI___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_isEOI(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Parser_isExitCommand(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Parser_Command_exit___elambda__1___rarg___closed__2;
x_3 = l_Lean_Syntax_isOfKind___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_isExitCommand___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_isExitCommand(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Parser_Module_3__consumeInput(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Parser_initCacheForInput(x_4);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = l_Array_empty___closed__1;
lean_inc(x_2);
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_6);
x_9 = l_Lean_Parser_tokenFn(x_1, x_8);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
lean_dec(x_2);
return x_13;
}
}
}
lean_object* l_Lean_Parser_parseCommand___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_string_utf8_at_end(x_7, x_5);
x_9 = 1;
x_10 = l_Bool_DecidableEq(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
lean_inc(x_1);
lean_inc(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_1);
x_14 = l_Lean_Parser_initCacheForInput(x_7);
lean_dec(x_7);
x_15 = lean_box(0);
x_16 = l_Array_empty___closed__1;
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
lean_ctor_set(x_17, 2, x_14);
lean_ctor_set(x_17, 3, x_15);
x_18 = l_Lean_Parser_commandParserAttribute;
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_13);
x_20 = l_Lean_Parser_ParserAttribute_runParser(x_18, x_19, x_13, x_17);
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_22);
lean_dec(x_22);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = 0;
lean_ctor_set(x_3, 0, x_24);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_4);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
x_29 = l_Bool_DecidableEq(x_6, x_9);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_dec(x_20);
x_31 = l_Lean_Parser_Error_toString(x_28);
x_32 = l___private_Init_Lean_Parser_Module_1__mkErrorMessage(x_13, x_30, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_4);
x_34 = l___private_Init_Lean_Parser_Module_3__consumeInput(x_13, x_30);
lean_ctor_set(x_3, 0, x_34);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_9);
x_4 = x_33;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_28);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_dec(x_20);
x_37 = l___private_Init_Lean_Parser_Module_3__consumeInput(x_13, x_36);
lean_ctor_set(x_3, 0, x_37);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_9);
goto _start;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_2);
lean_ctor_set(x_39, 1, x_1);
x_40 = l_Lean_Parser_initCacheForInput(x_7);
lean_dec(x_7);
x_41 = lean_box(0);
x_42 = l_Array_empty___closed__1;
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_5);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_41);
x_44 = l_Lean_Parser_commandParserAttribute;
x_45 = lean_unsigned_to_nat(0u);
lean_inc(x_39);
x_46 = l_Lean_Parser_ParserAttribute_runParser(x_44, x_45, x_39, x_43);
x_47 = lean_ctor_get(x_46, 3);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_39);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_48);
lean_dec(x_48);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = 0;
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_4);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
lean_dec(x_47);
x_56 = l_Bool_DecidableEq(x_6, x_9);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_46, 1);
lean_inc(x_57);
lean_dec(x_46);
x_58 = l_Lean_Parser_Error_toString(x_55);
x_59 = l___private_Init_Lean_Parser_Module_1__mkErrorMessage(x_39, x_57, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_4);
x_61 = l___private_Init_Lean_Parser_Module_3__consumeInput(x_39, x_57);
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_9);
x_3 = x_62;
x_4 = x_60;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_55);
x_64 = lean_ctor_get(x_46, 1);
lean_inc(x_64);
lean_dec(x_46);
x_65 = l___private_Init_Lean_Parser_Module_3__consumeInput(x_39, x_64);
x_66 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_9);
x_3 = x_66;
goto _start;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_68 = l___private_Init_Lean_Parser_Module_2__mkEOI(x_5);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_3);
lean_ctor_set(x_69, 1, x_4);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
lean_object* l_Lean_Parser_parseCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_parseCommand___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_IO_print___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Syntax_formatStx___main___rarg(x_1);
x_4 = l_Lean_Options_empty;
x_5 = l_Lean_Format_pretty(x_3, x_4);
x_6 = lean_io_prim_put_str(x_5, x_2);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_IO_println___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_print___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__2(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_IO_println___rarg___closed__1;
x_6 = lean_io_prim_put_str(x_5, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
lean_object* l_IO_print___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Message_toString(x_1);
x_4 = lean_io_prim_put_str(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_IO_println___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_print___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__4(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_IO_println___rarg___closed__1;
x_6 = lean_io_prim_put_str(x_5, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
lean_object* l_List_forM___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_IO_println___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__3(x_5, x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_1 = x_6;
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
lean_dec(x_6);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
}
lean_object* l___private_Init_Lean_Parser_Module_4__testModuleParserAux___main(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_44; 
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Parser_parseCommand___main(x_1, x_2, x_4, x_5);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_44 = l_Lean_Parser_isEOI(x_9);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = l_Lean_Parser_isExitCommand(x_9);
x_12 = x_45;
goto block_43;
}
else
{
uint8_t x_46; 
x_46 = 1;
x_12 = x_46;
goto block_43;
}
block_43:
{
uint8_t x_13; uint8_t x_14; 
x_13 = 1;
x_14 = l_Bool_DecidableEq(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Bool_DecidableEq(x_3, x_13);
if (x_15 == 0)
{
lean_dec(x_9);
x_4 = x_10;
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = l_IO_println___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__1(x_9, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_4 = x_10;
x_5 = x_11;
x_6 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_11);
x_24 = l_List_reverse___rarg(x_11);
x_25 = l_List_forM___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__5(x_24, x_6);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = 0;
x_29 = l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1(x_28, x_11);
lean_dec(x_11);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_box(x_13);
lean_ctor_set(x_25, 0, x_30);
return x_25;
}
else
{
lean_object* x_31; 
x_31 = lean_box(x_28);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
}
else
{
lean_object* x_32; uint8_t x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_33 = 0;
x_34 = l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1(x_33, x_11);
lean_dec(x_11);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_box(x_13);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(x_33);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_32);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_11);
x_39 = !lean_is_exclusive(x_25);
if (x_39 == 0)
{
return x_25;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_25, 0);
x_41 = lean_ctor_get(x_25, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_25);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Lean_Parser_Module_4__testModuleParserAux___main(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l___private_Init_Lean_Parser_Module_4__testModuleParserAux(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Parser_Module_4__testModuleParserAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Init_Lean_Parser_Module_4__testModuleParserAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Lean_Parser_Module_4__testModuleParserAux(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_Parser_testModuleParser___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Parser_Module_4__testModuleParserAux___main(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
lean_object* _init_l_Lean_Parser_testModuleParser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" parser");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_testModuleParser___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* lean_test_module_parser(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_6 = l_Lean_Parser_testModuleParser___closed__1;
lean_inc(x_3);
x_7 = lean_string_append(x_3, x_6);
x_8 = l_Lean_Parser_mkParserContextCore(x_1, x_2, x_3);
lean_inc(x_8);
lean_inc(x_1);
x_9 = l_Lean_Parser_parseHeader(x_1, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = 1;
x_15 = l_Bool_DecidableEq(x_4, x_14);
x_16 = lean_box(x_4);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_testModuleParser___lambda__1___boxed), 7, 5);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_8);
lean_closure_set(x_17, 2, x_16);
lean_closure_set(x_17, 3, x_12);
lean_closure_set(x_17, 4, x_13);
if (x_15 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
x_18 = l_Lean_Parser_testModuleParser___closed__2;
x_19 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_17);
x_20 = lean_io_timeit(x_7, x_19, x_5);
lean_dec(x_7);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_alloc_closure((void*)(l_IO_println___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__1), 2, 1);
lean_closure_set(x_21, 0, x_11);
x_22 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_17);
x_23 = lean_io_timeit(x_7, x_22, x_5);
lean_dec(x_7);
return x_23;
}
}
}
lean_object* l_Lean_Parser_testModuleParser___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Lean_Parser_testModuleParser___lambda__1(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_9;
}
}
lean_object* l_Lean_Parser_testModuleParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = lean_test_module_parser(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
lean_object* _init_l_Lean_Parser_parseFileAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to parse file");
return x_1;
}
}
lean_object* l_Lean_Parser_parseFileAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; 
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Parser_parseCommand___main(x_1, x_2, x_3, x_4);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_Parser_isEOI(x_9);
x_13 = 1;
x_14 = l_Bool_DecidableEq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_array_push(x_5, x_9);
x_3 = x_10;
x_4 = x_11;
x_5 = x_15;
goto _start;
}
else
{
uint8_t x_17; uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_List_isEmpty___rarg(x_11);
x_18 = l_Bool_DecidableEq(x_17, x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
x_19 = l_List_reverse___rarg(x_11);
x_20 = l_List_forM___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__5(x_19, x_6);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = l_Lean_Parser_parseFileAux___main___closed__1;
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_Lean_Parser_parseFileAux___main___closed__1;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_11);
x_31 = l_Lean_nullKind;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_5);
x_33 = l_Lean_Syntax_updateLeading___rarg(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_6);
return x_34;
}
}
}
}
lean_object* l_Lean_Parser_parseFileAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_parseFileAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_IO_readTextFile___at_Lean_Parser_parseFile___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_read_text_file(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_parseFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_realpath(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_io_prim_read_text_file(x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Parser_mkParserContextCore(x_1, x_8, x_5);
lean_inc(x_10);
lean_inc(x_1);
x_11 = l_Lean_Parser_parseHeader(x_1, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_mkOptionalNode___rarg___closed__1;
x_17 = lean_array_push(x_16, x_13);
x_18 = l_Lean_Parser_parseFileAux___main(x_1, x_10, x_14, x_15, x_17, x_9);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_4);
if (x_23 == 0)
{
return x_4;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_4, 0);
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_4);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_IO_readTextFile___at_Lean_Parser_parseFile___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_readTextFile___at_Lean_Parser_parseFile___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_Lean_Message(lean_object*);
lean_object* initialize_Init_Lean_Parser_Command(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Parser_Module(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Message(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Parser_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__1);
l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__2);
l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__3);
l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4 = _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4);
l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__5 = _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__5);
l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__6 = _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__6);
l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__7 = _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__7);
l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__8 = _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__8();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__8);
l_Lean_Parser_Module_prelude___closed__1 = _init_l_Lean_Parser_Module_prelude___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_prelude___closed__1);
l_Lean_Parser_Module_prelude___closed__2 = _init_l_Lean_Parser_Module_prelude___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_prelude___closed__2);
l_Lean_Parser_Module_prelude___closed__3 = _init_l_Lean_Parser_Module_prelude___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_prelude___closed__3);
l_Lean_Parser_Module_prelude___closed__4 = _init_l_Lean_Parser_Module_prelude___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_prelude___closed__4);
l_Lean_Parser_Module_prelude = _init_l_Lean_Parser_Module_prelude();
lean_mark_persistent(l_Lean_Parser_Module_prelude);
l_Lean_Parser_Module_import___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___rarg___closed__1);
l_Lean_Parser_Module_import___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___rarg___closed__2);
l_Lean_Parser_Module_import___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___rarg___closed__3);
l_Lean_Parser_Module_import___elambda__1___rarg___closed__4 = _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___rarg___closed__4);
l_Lean_Parser_Module_import___elambda__1___rarg___closed__5 = _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___rarg___closed__5);
l_Lean_Parser_Module_import___elambda__1___rarg___closed__6 = _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___rarg___closed__6);
l_Lean_Parser_Module_import___elambda__1___rarg___closed__7 = _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___rarg___closed__7);
l_Lean_Parser_Module_import___elambda__1___rarg___closed__8 = _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__8();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___rarg___closed__8);
l_Lean_Parser_Module_import___elambda__1___rarg___closed__9 = _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__9();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___rarg___closed__9);
l_Lean_Parser_Module_import___elambda__1___rarg___closed__10 = _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__10();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___rarg___closed__10);
l_Lean_Parser_Module_import___elambda__1___rarg___closed__11 = _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__11();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___rarg___closed__11);
l_Lean_Parser_Module_import___elambda__1___rarg___closed__12 = _init_l_Lean_Parser_Module_import___elambda__1___rarg___closed__12();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___rarg___closed__12);
l_Lean_Parser_Module_import___closed__1 = _init_l_Lean_Parser_Module_import___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__1);
l_Lean_Parser_Module_import___closed__2 = _init_l_Lean_Parser_Module_import___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__2);
l_Lean_Parser_Module_import___closed__3 = _init_l_Lean_Parser_Module_import___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__3);
l_Lean_Parser_Module_import___closed__4 = _init_l_Lean_Parser_Module_import___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__4);
l_Lean_Parser_Module_import___closed__5 = _init_l_Lean_Parser_Module_import___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__5);
l_Lean_Parser_Module_import___closed__6 = _init_l_Lean_Parser_Module_import___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__6);
l_Lean_Parser_Module_import___closed__7 = _init_l_Lean_Parser_Module_import___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__7);
l_Lean_Parser_Module_import___closed__8 = _init_l_Lean_Parser_Module_import___closed__8();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__8);
l_Lean_Parser_Module_import = _init_l_Lean_Parser_Module_import();
lean_mark_persistent(l_Lean_Parser_Module_import);
l_Lean_Parser_Module_header___elambda__1___closed__1 = _init_l_Lean_Parser_Module_header___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__1);
l_Lean_Parser_Module_header___elambda__1___closed__2 = _init_l_Lean_Parser_Module_header___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__2);
l_Lean_Parser_Module_header___closed__1 = _init_l_Lean_Parser_Module_header___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__1);
l_Lean_Parser_Module_header___closed__2 = _init_l_Lean_Parser_Module_header___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__2);
l_Lean_Parser_Module_header___closed__3 = _init_l_Lean_Parser_Module_header___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__3);
l_Lean_Parser_Module_header___closed__4 = _init_l_Lean_Parser_Module_header___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__4);
l_Lean_Parser_Module_header___closed__5 = _init_l_Lean_Parser_Module_header___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__5);
l_Lean_Parser_Module_header___closed__6 = _init_l_Lean_Parser_Module_header___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__6);
l_Lean_Parser_Module_header = _init_l_Lean_Parser_Module_header();
lean_mark_persistent(l_Lean_Parser_Module_header);
l_Lean_Parser_ModuleParserState_inhabited___closed__1 = _init_l_Lean_Parser_ModuleParserState_inhabited___closed__1();
lean_mark_persistent(l_Lean_Parser_ModuleParserState_inhabited___closed__1);
l_Lean_Parser_ModuleParserState_inhabited = _init_l_Lean_Parser_ModuleParserState_inhabited();
lean_mark_persistent(l_Lean_Parser_ModuleParserState_inhabited);
l___private_Init_Lean_Parser_Module_2__mkEOI___closed__1 = _init_l___private_Init_Lean_Parser_Module_2__mkEOI___closed__1();
lean_mark_persistent(l___private_Init_Lean_Parser_Module_2__mkEOI___closed__1);
l___private_Init_Lean_Parser_Module_2__mkEOI___closed__2 = _init_l___private_Init_Lean_Parser_Module_2__mkEOI___closed__2();
lean_mark_persistent(l___private_Init_Lean_Parser_Module_2__mkEOI___closed__2);
l_Lean_Parser_testModuleParser___closed__1 = _init_l_Lean_Parser_testModuleParser___closed__1();
lean_mark_persistent(l_Lean_Parser_testModuleParser___closed__1);
l_Lean_Parser_testModuleParser___closed__2 = _init_l_Lean_Parser_testModuleParser___closed__2();
lean_mark_persistent(l_Lean_Parser_testModuleParser___closed__2);
l_Lean_Parser_parseFileAux___main___closed__1 = _init_l_Lean_Parser_parseFileAux___main___closed__1();
lean_mark_persistent(l_Lean_Parser_parseFileAux___main___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
